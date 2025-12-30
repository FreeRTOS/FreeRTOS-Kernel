/* x86_64 
 * 
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */

#ifndef _X86_64_H_
#define _X86_64_H_
#include "FreeRTOS.h"
#include "task.h"
#include <memory.h>

#if defined(__x86_64__)
// Max number of heap regions
#define MAX_HEAP_REGIONS 64

// Multiboot tages that we are interested in
#define MULTIBOOT_TAG_TYPE_MODULE 3
#define MULTIBOOT_TAG_TYPE_MEMORY 6
#define MULTIBOOT_TAG_TYPE_END 0

// Regions - Read Only or Read-Write
#define REGION_RO 0
#define REGION_RW 1

struct multiboot_tag {
    uint32_t type;
    uint32_t size;
};
struct multiboot_tag_mmap {
    uint32_t type;
    uint32_t size;
    uint32_t entry_size;
    uint32_t entry_version;
    struct multiboot_mmap_entry {
        uint64_t base_addr;
        uint64_t length;
        uint32_t type;
        uint32_t reserved;
    } entries[];
};

struct multiboot_info {
    uint32_t total_size;
    uint32_t reserved;
    struct multiboot_tag tags[];
};

#define PAGE_SIZE_1GB  (1ULL << 30)
#define PAGE_SIZE_4K   (1ULL << 12)
#define PGD_INDEX(addr)   (((addr) >> 39) & 0x1FF)
#define PUD_INDEX(addr)   (((addr) >> 30) & 0x1FF)
#define PMD_INDEX(addr)   (((addr) >> 21) & 0x1FF)
#define PT_INDEX(addr)    (((addr) >> 12) & 0x1FF)

#define USER_VA_START 0xFFFF800000000000ULL

#define PAGE_TABLE_SIZE 512


// Extern variable defined in linker script and assembly code
extern uint64_t pml4;
extern uint64_t pud;
extern uint8_t end;


/* Setup Identity Mapping for Kernel */
void vSetupKernelPageMapping(void);

/* Parse user modules loaded as part of boot. Return
*  end address of user modules
*/
void vInitMemoryAllocator(uint64_t);
void vx86_64Init(uint64_t multiboot_info_addr);
uint32_t xInitiRegionForRestrictedTask(MemoryRegion_t *regions);
void vMapPages(uint64_t start_addr,uint64_t end_addr, uint64_t *pgd, uint32_t mode);
void vFreeAllPages(uint64_t *pgd);
uint64_t *pMallocPageTable(void);
#endif
#endif
