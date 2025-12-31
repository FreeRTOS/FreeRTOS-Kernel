/* x86_64_init 
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

#include "FreeRTOS.h"
#include "x86_64.h"
#include "task.h"
#include "stdio.h"
#include "stdio.h"
#include "trap.h"
#include "xen/memory.h"
#include "e820.h"
#include "hypervisor.h"
#include "xen/hvm/params.h"
#include <xen/arch-x86/hvm/start_info.h>

HeapRegion_t xHeapRegions[MAX_HEAP_REGIONS];

// DEBUG variables for testing purpose
uint64_t pml4_w_user=0;

// Extern variable defined in linker script and assembly code
extern uint64_t pml4;
extern uint64_t pud;
extern uint8_t end;
extern char __system_calls_start;
extern char __system_calls_end;
extern char __apis_start;
extern char __apis_end;
extern char __rodata_start;
extern char __rodata_end;

/*
*   Method to setup regions for restricted tasks.
*   A restricted task has access to following
*   user mode
*   user data
*   system calls
*   utilities apis like strlen
*   its process stack 
*/
uint32_t xInitiRegionForRestrictedTask(MemoryRegion_t *regions) ;
void vInitMemoryAllocator(uint64_t multiboot_info_addr);
void vx86_64Init(uint64_t multiboot_info_addr) ;
void vSetupKernelPageMapping(void) ;
uint32_t xInitiRegionForRestrictedTask(MemoryRegion_t *regions) {

     uint32_t num_region_used = 0;
     regions[num_region_used].pvBaseAddress = &__system_calls_start;
     regions[num_region_used].ulLengthInBytes = (uint32_t) (&__system_calls_end - &__system_calls_start);
     regions[num_region_used].ulParameters = REGION_RO;
     num_region_used++;

     regions[num_region_used].pvBaseAddress = &__apis_start;
     regions[num_region_used].ulLengthInBytes = (uint32_t) (&__apis_end - &__apis_start);
     regions[num_region_used].ulParameters = REGION_RO;
     num_region_used++;

     regions[num_region_used].pvBaseAddress = &__rodata_start;
     regions[num_region_used].ulLengthInBytes = (uint32_t) (&__rodata_end - &__rodata_start);
     regions[num_region_used].ulParameters = REGION_RO;
     num_region_used++;

     return num_region_used;
}

#define PAGE_SIZE_1GB  (1ULL << 30)
#define PML4_INDEX(va) (((va) >> 39) & 0x1FF)
#define PDPT_INDEX(va) (((va) >> 30) & 0x1FF)

/* Setup Mapping for Kernel */
void vSetupKernelPageMapping() {
    uint64_t *page_table_l4_addr = &pml4;
    uint64_t *page_table_l3_addr = &pud;
    uint64_t addr = 0;
    for (int i=0;i<256;i++) {
        page_table_l4_addr[i] = (uint64_t) &page_table_l3_addr[i*512];
        page_table_l4_addr[i] |= 0x03;
        for (int j=0;j<512;j++) {
            page_table_l3_addr[i*(int)512+j]=addr|(uint64_t)0x83;
            addr += 0x40000000ULL;
        }
    }
    addr = 0;
    for (int i=256;i<512;i++) {
        page_table_l4_addr[i] = (uint64_t) &page_table_l3_addr[i*512];
        page_table_l4_addr[i] |= 0x03;
        for (int j=0;j<512;j++) {
            page_table_l3_addr[i*(int)512+j]=addr|(uint64_t)0x83;
            addr += 0x40000000ULL;
        }
    }
}


void vInitMemoryAllocator(uint64_t multiboot_info_addr)
{
    // Find the end address where kernel is loaded.
    // Free Memory can started only from that address
    uint64_t last_used_addr = (uint64_t) &end;
    int heap_region_count = 0;
    printf("kernel end: %p\n",last_used_addr);
    if (multiboot_info_addr != (uint64_t)0) {
        uint64_t* val = (uint64_t*) multiboot_info_addr;
	uint32_t magic = *((uint64_t *)val);
        
	if (magic != XEN_HVM_START_MAGIC_VALUE) {
            struct multiboot_tag *tag = (struct multiboot_tag *)(multiboot_info_addr + (uint64_t)8); // Skip total size and reserved field
    
            while (tag->type != (uint32_t)0) { // 0 indicates end tag
            if (tag->type == (uint32_t)MULTIBOOT_TAG_TYPE_MEMORY) {
                    struct multiboot_tag_mmap *mmap_tag = (struct multiboot_tag_mmap *)tag;
                    for (uint32_t i = 0; i < (mmap_tag->size - 16) / mmap_tag->entry_size; i++) {
                        struct multiboot_mmap_entry *entry = &mmap_tag->entries[i];
                        if (entry->type == 1) {
                            uint64_t start_addr =  entry->base_addr;
                            uint64_t end_addr = start_addr + entry->length;
                            if (start_addr > last_used_addr) {
                                xHeapRegions[heap_region_count].pucStartAddress = (uint8_t *) start_addr;
                                xHeapRegions[heap_region_count].xSizeInBytes = entry->length;
                                heap_region_count++;
                            } else if (end_addr > last_used_addr) {
                                xHeapRegions[heap_region_count].pucStartAddress = (uint8_t *)last_used_addr;
                                xHeapRegions[heap_region_count].xSizeInBytes = end_addr - last_used_addr;
                                heap_region_count++;
                            }
                        }
                    }
                }
                tag = (struct multiboot_tag *)((uint8_t *)tag + ((tag->size + 7) & ~7)); // Align tag size to 8
            }
	} else {
	    struct hvm_start_info *hsi = (struct hvm_start_info *)val;
            long ret;
            struct xen_memory_map memmap;
            memmap.nr_entries = E820_MAX;
            set_xen_guest_handle(memmap.buffer, e820_map);
            ret = HYPERVISOR_memory_op(XENMEM_memory_map, &memmap);
            unsigned long end, start;
            struct e820entry  *entry = (struct e820entry *)e820_map;
            for ( int i = 0; i < memmap.nr_entries; i++ )
            {
                if (entry[i].type == XEN_HVM_MEMMAP_TYPE_RAM) {
                    uint64_t start_addr =  entry[i].addr;
                    uint64_t end_addr = entry[i].addr+entry[i].size;
                    if (start_addr > last_used_addr) {
                        xHeapRegions[heap_region_count].pucStartAddress = (uint8_t *) start_addr;
                        xHeapRegions[heap_region_count].xSizeInBytes = entry[i].size;
                        heap_region_count++;
                    } else if (end_addr > last_used_addr) {
                        xHeapRegions[heap_region_count].pucStartAddress = (uint8_t *)last_used_addr;
                        xHeapRegions[heap_region_count].xSizeInBytes = end_addr - last_used_addr;
                        heap_region_count++;
                    }
		}
            }
	}
    }
    xHeapRegions[heap_region_count].pucStartAddress = 0;
    xHeapRegions[heap_region_count].xSizeInBytes = 0;
    vPortDefineHeapRegions( xHeapRegions );  
    return;
}

void vx86_64Init(uint64_t multiboot_info_addr) {
    vIDTInit();
    vSetupKernelPageMapping();
    vInitMemoryAllocator(multiboot_info_addr);
}
