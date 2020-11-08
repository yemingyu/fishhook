// Copyright (c) 2013, Facebook, Inc.
// All rights reserved.
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//   * Redistributions of source code must retain the above copyright notice,
//     this list of conditions and the following disclaimer.
//   * Redistributions in binary form must reproduce the above copyright notice,
//     this list of conditions and the following disclaimer in the documentation
//     and/or other materials provided with the distribution.
//   * Neither the name Facebook nor the names of its contributors may be used to
//     endorse or promote products derived from this software without specific
//     prior written permission.
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include "fishhook.h"

#include <dlfcn.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <mach/mach.h>
#include <mach/vm_map.h>
#include <mach/vm_region.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>

#ifdef __LP64__
typedef struct mach_header_64 mach_header_t;
typedef struct segment_command_64 segment_command_t;
typedef struct section_64 section_t;
typedef struct nlist_64 nlist_t;
#define LC_SEGMENT_ARCH_DEPENDENT LC_SEGMENT_64
#else
typedef struct mach_header mach_header_t;
typedef struct segment_command segment_command_t;
typedef struct section section_t;
typedef struct nlist nlist_t;
#define LC_SEGMENT_ARCH_DEPENDENT LC_SEGMENT
#endif

#ifndef SEG_DATA_CONST
#define SEG_DATA_CONST  "__DATA_CONST"
#endif

struct rebindings_entry {
  struct rebinding *rebindings;
  size_t rebindings_nel;
  struct rebindings_entry *next;
};

static struct rebindings_entry *_rebindings_head;   // 开发者输入的 hook 相关参数转化成的结构体数据，是一个递归结构可以用来遍历多个重绑定符号

static int prepend_rebindings(struct rebindings_entry **rebindings_head,
                              struct rebinding rebindings[],
                              size_t nel) {
  struct rebindings_entry *new_entry = (struct rebindings_entry *) malloc(sizeof(struct rebindings_entry));
  if (!new_entry) {
    return -1;
  }
  new_entry->rebindings = (struct rebinding *) malloc(sizeof(struct rebinding) * nel);
  if (!new_entry->rebindings) {
    free(new_entry);
    return -1;
  }
  memcpy(new_entry->rebindings, rebindings, sizeof(struct rebinding) * nel);
  new_entry->rebindings_nel = nel;
  new_entry->next = *rebindings_head;
  *rebindings_head = new_entry;
  return 0;
}

static vm_prot_t get_protection(void *sectionStart) {
  mach_port_t task = mach_task_self();
  vm_size_t size = 0;
  vm_address_t address = (vm_address_t)sectionStart;
  memory_object_name_t object;
#if __LP64__
  mach_msg_type_number_t count = VM_REGION_BASIC_INFO_COUNT_64;
  vm_region_basic_info_data_64_t info;
  kern_return_t info_ret = vm_region_64(
      task, &address, &size, VM_REGION_BASIC_INFO_64, (vm_region_info_64_t)&info, &count, &object);
#else
  mach_msg_type_number_t count = VM_REGION_BASIC_INFO_COUNT;
  vm_region_basic_info_data_t info;
  kern_return_t info_ret = vm_region(task, &address, &size, VM_REGION_BASIC_INFO, (vm_region_info_t)&info, &count, &object);
#endif
  if (info_ret == KERN_SUCCESS) {
    return info.protection;
  } else {
    return VM_PROT_READ;
  }
}
static void perform_rebinding_with_section(struct rebindings_entry *rebindings,
                                           section_t *section,
                                           intptr_t slide,
                                           nlist_t *symtab,
                                           char *strtab,
                                           uint32_t *indirect_symtab) {
  const bool isDataConst = strcmp(section->segname, SEG_DATA_CONST) == 0;   // non-lazy 对应 __DATA_CONST
  uint32_t *indirect_symbol_indices = indirect_symtab + section->reserved1; // lazy 或 nonlazy 的指针对应到 indirect Symbols 中的起始位置，便于后续遍历
  void **indirect_symbol_bindings = (void **)((uintptr_t)slide + section->addr);    // slide 是 ASLR，获取 lazy 或 nonlazy 表中位置，后续替换的就是 lazy、nonlazy 表中符号对应的地址
  vm_prot_t oldProtection = VM_PROT_READ;
  if (isDataConst) {    // 老的 __DATA_CONST 需要的内存保护相关
    oldProtection = get_protection(rebindings);
    mprotect(indirect_symbol_bindings, section->size, PROT_READ | PROT_WRITE);
  }
  for (uint i = 0; i < section->size / sizeof(void *); i++) {   // 目标符号与 lazy 或 nonlazy 表中逐个进行对比
    uint32_t symtab_index = indirect_symbol_indices[i];
    if (symtab_index == INDIRECT_SYMBOL_ABS || symtab_index == INDIRECT_SYMBOL_LOCAL ||
        symtab_index == (INDIRECT_SYMBOL_LOCAL   | INDIRECT_SYMBOL_ABS)) {  // 过滤无用部分
      continue;
    }
    uint32_t strtab_offset = symtab[symtab_index].n_un.n_strx;  // 根据 symbol table 找到 string table 对应位置
    char *symbol_name = strtab + strtab_offset; // string table 中获取符号名，为了后续进行目标函数名匹配
    bool symbol_name_longer_than_1 = symbol_name[0] && symbol_name[1];  // 长度超过 1 才有效
    struct rebindings_entry *cur = rebindings;
    while (cur) {
      for (uint j = 0; j < cur->rebindings_nel; j++) {
        if (symbol_name_longer_than_1 &&
            strcmp(&symbol_name[1], cur->rebindings[j].name) == 0) {
          if (cur->rebindings[j].replaced != NULL &&
              indirect_symbol_bindings[i] != cur->rebindings[j].replacement) {
            *(cur->rebindings[j].replaced) = indirect_symbol_bindings[i];   // replaced 值为 null，所以要用存放 replaced 变量的地址，然后让这个地址的内容为 hook 前的原函数地址，nl 表中符号对应的值 MachOView 上显示 00000，但实际读取内存是有值的，应该是 image 加载时 dyld 进行的处理
          }
          indirect_symbol_bindings[i] = cur->rebindings[j].replacement; // 调整内存中 lazy、nonlazy 表中符号对应的地址值，如果是调用 lazy 绑定函数，hook 前调用时会走到原有 lazy symbol pointer 里面的汇编代码，进而走到 stub 然后获取 bind 地址，hook 后就直接调用到 hook 替换的地址，需要调用原有函数时，就走前面说的流程；按照以前的分析 lazy binding 后会调整 lazy 表中符号对应的地址，这里替换后再走到 lazy binding 看起来不会覆盖内存中已经 hook 了的 lazy symbol pointer 里的汇编值；实践中多以 hook lazy 居多，nl 如 _mach_task_self_ 实测会成功
          goto symbol_loop;
        }
      }
      cur = cur->next;
    }
  symbol_loop:;
  }
  if (isDataConst) {
    int protection = 0;
    if (oldProtection & VM_PROT_READ) {
      protection |= PROT_READ;
    }
    if (oldProtection & VM_PROT_WRITE) {
      protection |= PROT_WRITE;
    }
    if (oldProtection & VM_PROT_EXECUTE) {
      protection |= PROT_EXEC;
    }
    mprotect(indirect_symbol_bindings, section->size, protection);
  }
}

static void rebind_symbols_for_image(struct rebindings_entry *rebindings,
                                     const struct mach_header *header,
                                     intptr_t slide) {
  Dl_info info;
  if (dladdr(header, &info) == 0) { // dladdr 会返回 mach_header 和 image 的名字
    return;
  }

  segment_command_t *cur_seg_cmd;
  segment_command_t *linkedit_segment = NULL;
  struct symtab_command* symtab_cmd = NULL;
  struct dysymtab_command* dysymtab_cmd = NULL;

  uintptr_t cur = (uintptr_t)header + sizeof(mach_header_t);
  for (uint i = 0; i < header->ncmds; i++, cur += cur_seg_cmd->cmdsize) {
    cur_seg_cmd = (segment_command_t *)cur;
    if (cur_seg_cmd->cmd == LC_SEGMENT_ARCH_DEPENDENT) {
      if (strcmp(cur_seg_cmd->segname, SEG_LINKEDIT) == 0) {
        linkedit_segment = cur_seg_cmd; // 遍历 Segment 类型 Load Command 找到 linkedit segment 对应的 LC
      }
    } else if (cur_seg_cmd->cmd == LC_SYMTAB) {
      symtab_cmd = (struct symtab_command*)cur_seg_cmd; // 遍历 Load Command 找到 LC_SYMTAB
    } else if (cur_seg_cmd->cmd == LC_DYSYMTAB) {
      dysymtab_cmd = (struct dysymtab_command*)cur_seg_cmd; // 遍历 Load Command 找到 LC_DYSYMTAB
    }
  }

  if (!symtab_cmd || !dysymtab_cmd || !linkedit_segment ||
      !dysymtab_cmd->nindirectsyms) {
    return;
  }

  // Find base symbol/string table addresses
  uintptr_t linkedit_base = (uintptr_t)slide + linkedit_segment->vmaddr - linkedit_segment->fileoff;    // 根据 ASLR 偏移和 linkedit segment 虚拟地址等，获取二进制在内存中的基址
  nlist_t *symtab = (nlist_t *)(linkedit_base + symtab_cmd->symoff);    // 获取内存中符号表的起始地址
  char *strtab = (char *)(linkedit_base + symtab_cmd->stroff);  // 获取内存中字符串表的起始地址

  // Get indirect symbol table (array of uint32_t indices into symbol table)
  uint32_t *indirect_symtab = (uint32_t *)(linkedit_base + dysymtab_cmd->indirectsymoff);   // 获取内存中 Indirect Symbols 其实地址

  cur = (uintptr_t)header + sizeof(mach_header_t);
  for (uint i = 0; i < header->ncmds; i++, cur += cur_seg_cmd->cmdsize) {
    cur_seg_cmd = (segment_command_t *)cur;
    if (cur_seg_cmd->cmd == LC_SEGMENT_ARCH_DEPENDENT) {
      if (strcmp(cur_seg_cmd->segname, SEG_DATA) != 0 &&
          strcmp(cur_seg_cmd->segname, SEG_DATA_CONST) != 0) {  // lazy 表位于 __DATA 中，non-lazy 位于 __DATA_CONST 中
        continue;
      }
      for (uint j = 0; j < cur_seg_cmd->nsects; j++) {
        section_t *sect =
          (section_t *)(cur + sizeof(segment_command_t)) + j;
        if ((sect->flags & SECTION_TYPE) == S_LAZY_SYMBOL_POINTERS) {   // 尝试匹配 lazy 表
          perform_rebinding_with_section(rebindings, sect, slide, symtab, strtab, indirect_symtab);
        }
        if ((sect->flags & SECTION_TYPE) == S_NON_LAZY_SYMBOL_POINTERS) {   // 尝试匹配 non-lazy 表
          perform_rebinding_with_section(rebindings, sect, slide, symtab, strtab, indirect_symtab);
        }
      }
    }
  }
}

static void _rebind_symbols_for_image(const struct mach_header *header,
                                      intptr_t slide) { // header 为 image 对应 mach_header，slide 为 ASLR 偏移
    rebind_symbols_for_image(_rebindings_head, header, slide);
}

int rebind_symbols_image(void *header,
                         intptr_t slide,
                         struct rebinding rebindings[],
                         size_t rebindings_nel) {
    struct rebindings_entry *rebindings_head = NULL;
    int retval = prepend_rebindings(&rebindings_head, rebindings, rebindings_nel);
    rebind_symbols_for_image(rebindings_head, (const struct mach_header *) header, slide);
    if (rebindings_head) {
      free(rebindings_head->rebindings);
    }
    free(rebindings_head);
    return retval;
}

int rebind_symbols(struct rebinding rebindings[], size_t rebindings_nel) {
  int retval = prepend_rebindings(&_rebindings_head, rebindings, rebindings_nel);   // 将开发者输入的 hook 相关参数转成递归结构体结构
  if (retval < 0) {
    return retval;
  }
  // If this was the first call, register callback for image additions (which is also invoked for
  // existing images, otherwise, just run on existing images
  if (!_rebindings_head->next) {
    _dyld_register_func_for_add_image(_rebind_symbols_for_image);   // 首次调用 rebind_symbols 走这个逻辑，当前存在的所有 image 都会触发此回调，后续每个新的 image 被加载绑定时也会触发回调，每个 image 都需要走一遍重绑定
  } else {
    uint32_t c = _dyld_image_count();
    for (uint32_t i = 0; i < c; i++) {
      _rebind_symbols_for_image(_dyld_get_image_header(i), _dyld_get_image_vmaddr_slide(i));    // 再次调用 rebind_symbols 走这个逻辑，对当前存在的所有 image 进行重新绑定符号处理，后续每个新的 image 被加载绑定时就不会触发回调了，所以尽量在首次把需要配置的 hook 配置完成
    }
  }
  return retval;
}
