/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*
 * mte_port.c — MTE heap wrapper and stack tagging for FreeRTOS Armv9 port.
 *
 * Uses ARM ACLE intrinsics (arm_acle.h) for MISRA C:2012 compliance.
 *
 * configARMV9_MTE_HEAP: wraps pvPortMalloc/vPortFree with IRG/STG tagging
 * configARMV9_MTE_STACK: tags task stack memory on creation
 */

#define PORTMEMORY_IMPLEMENTATION    1

#include "FreeRTOS.h"
#include "task.h"
#include <stdint.h>
#include <arm_acle.h>

#if ( configARMV9_MTE_HEAP == 1 )

void * pvPortMallocTagged( size_t xSize )
{
    /* MISRA Ref 11.5.1 [Void pointer assignment] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/MISRA.md#rule-115 */
    void * pv = pvPortMalloc( xSize );

    if( pv == NULL )
    {
        return NULL;
    }

    /* Generate random tag (excludes tag 0 via GCR_EL1) */
    pv = __arm_mte_create_random_tag( pv, 0 );

    /* Tag all 16-byte granules in the allocation */
    size_t xRounded = ( xSize + 15U ) & ~15U;

    /* MISRA Ref 11.5.1 [Void pointer assignment] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/MISRA.md#rule-115 */
    uint8_t * pucTagPtr = ( uint8_t * ) pv;

    for( size_t i = 0; i < xRounded; i += 16U )
    {
        __arm_mte_set_tag( &pucTagPtr[ i ] );
    }

    return pv;
}

void vPortFreeTagged( void * pv )
{
    if( pv == NULL )
    {
        return;
    }

    /* Strip tag (top byte) to recover the canonical address for the allocator */
    /* MISRA Ref 11.6.1 [Pointer to integer conversion] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/MISRA.md#rule-116 */
    uintptr_t xAddr = ( uintptr_t ) pv & 0x00FFFFFFFFFFFFFFULL;
    void * pvUntagged = ( void * ) xAddr;

    /* Re-tag freed region with tag 0 (use-after-free detection).
     * Tag the first 64 bytes (covers most small allocations). */
    /* MISRA Ref 11.5.1 [Void pointer assignment] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/MISRA.md#rule-115 */
    uint8_t * pucPtr = ( uint8_t * ) pvUntagged;

    for( size_t i = 0; i < 64U; i += 16U )
    {
        __arm_mte_set_tag( &pucPtr[ i ] );
    }

    vPortFree( pvUntagged );
}

#endif /* configARMV9_MTE_HEAP */

#if ( configARMV9_MTE_STACK == 1 )

void vPortMteTagStack( StackType_t * pxStack, uint32_t ulStackDepth )
{
    /* MISRA Ref 11.5.1 [Void pointer assignment] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Kernel/blob/main/MISRA.md#rule-115 */
    void * pvAddr = ( void * ) pxStack;
    size_t xBytes = ( size_t ) ulStackDepth * sizeof( StackType_t );

    /* Generate a random tag for this task's stack */
    pvAddr = __arm_mte_create_random_tag( pvAddr, 0 );

    /* Tag all granules */
    uint8_t * pucPtr = ( uint8_t * ) pvAddr;

    for( size_t i = 0; i < xBytes; i += 16U )
    {
        __arm_mte_set_tag( &pucPtr[ i ] );
    }
}

#endif /* configARMV9_MTE_STACK */
