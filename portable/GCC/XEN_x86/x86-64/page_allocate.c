
/* page_allocate 
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

#include "stdint.h"
#include "x86_64.h"
#include "stdio.h"
#include "stdlib.h"
#include "string.h"
#include <memory.h>

void vAlignedFree(void *aligned_ptr) ;
void vFreeAllPages(uint64_t *pgd) ;
uint64_t *pMallocPageTable(void) ;
void vMapPages(uint64_t start_addr,uint64_t end_addr, uint64_t *pgd, uint32_t mode) ;

void vAlignedFree(void *aligned_ptr) {
    if (aligned_ptr != NULL) {
        void *original_ptr = ((void **)aligned_ptr)[-1];
        vPortFree(original_ptr);
    }
}

void vFreeAllPages(uint64_t *pgd) {
    if (pgd !=NULL) {
        for (int pgd_index=256;pgd_index<512;pgd_index++) {
            uint64_t *pud = (uint64_t *)(pgd[pgd_index]&0xfffffffff000ULL);
            if (pud !=NULL) {
                for (int pud_index=0;pud_index<512;pud_index++) {
                    uint64_t *pmd = (uint64_t *)(pud[pud_index]&0xfffffffff000ULL);
                    if (pmd !=NULL) {
                        for (int pmd_index=0;pmd_index<512;pmd_index++) {
                             uint64_t *pt = (uint64_t *)(pmd[pmd_index]&0xfffffffff000ULL);
                             if (pt!=NULL) {
                                 vAlignedFree(pt);
                             }
                        }
                        vAlignedFree(pmd);
                    }
                }
                vAlignedFree(pud);
            }
        }
        vAlignedFree(pgd);
    }
}
uint64_t *pMallocPageTable(void) {
    uint64_t *page_table=(uint64_t *)pvAlignedMalloc((uint64_t)512 * sizeof(uint64_t),4096);
    memset(page_table,0,(uint64_t)512*sizeof(uint64_t));
    return page_table;
}
void vMapPages(uint64_t start_addr,uint64_t end_addr, uint64_t *pgd, uint32_t mode) {
    uint32_t pgd_index = 0;
    uint32_t pud_index = 0;
    uint32_t pmd_index = 0;
    uint32_t pt_index = 0;
    uint64_t addr = start_addr;
    uint64_t target_address = USER_VA_START + start_addr;

    while (addr < end_addr) {
        pgd_index = PGD_INDEX(target_address);
        pud_index = PUD_INDEX(target_address);
        pmd_index = PMD_INDEX(target_address);
        pt_index = PT_INDEX(target_address);
        uint64_t *pud = (uint64_t *)(pgd[pgd_index]&0xfffffffff000ULL);
        if (pud == (void *)0) {
            pud = pMallocPageTable();
            pgd[pgd_index] = (uint64_t) pud;
            pgd[pgd_index] |= 0x07;
        } 
        uint64_t *pmd = (uint64_t *)(pud[pud_index]&0xfffffffff000ULL);
        if (pmd == (void *)0) {
            pmd = pMallocPageTable();
            pud[pud_index]  = (uint64_t) pmd;
            pud[pud_index] |= 0x07;
        } 
        uint64_t *pt = (uint64_t *)(pmd[pmd_index]&0xfffffffff000ULL);
        if (pt == (void *)0) {
            pt = pMallocPageTable();
            pmd[pmd_index]  = (uint64_t) pt;
            pmd[pmd_index] |= 0x07;
        } 
        pt[pt_index] = addr | (uint64_t)0x07;
        if (mode != REGION_RW)
            pt[pt_index] &= ~0x2;
        addr += PAGE_SIZE_4K;
        target_address += PAGE_SIZE_4K;
    }
}
