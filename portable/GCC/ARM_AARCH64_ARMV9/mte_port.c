/*
 * mte_port.c — MTE heap wrapper and stack tagging for FreeRTOS Armv9 port.
 *
 * Uses ARM ACLE intrinsics (arm_acle.h) for MISRA C:2012 compliance.
 * No pointer-to-integer casts required.
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
