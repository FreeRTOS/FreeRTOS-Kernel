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

#ifndef PORTMACRO_H
#define PORTMACRO_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/*-----------------------------------------------------------
 * Port specific definitions.
 *
 * The settings in this file configure FreeRTOS correctly for the given hardware
 * and compiler.
 *
 * These settings should not be altered.
 *-----------------------------------------------------------
 */

/* Type definitions. */
#define portCHAR          char
#define portFLOAT         float
#define portDOUBLE        double
#define portLONG          long
#define portSHORT         short
#define portSTACK_TYPE    uint64_t
#define portBASE_TYPE     long
#define portPOINTER_SIZE_TYPE uint64_t

typedef portSTACK_TYPE   StackType_t;
typedef long             BaseType_t;
typedef unsigned long    UBaseType_t;

typedef BaseType_t       TickType_t;
#define portMAX_DELAY    ( ( TickType_t ) 0xffffffffUL )

/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define portSTACK_GROWTH      ( -1 )
#define portTICK_PERIOD_MS    ( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT    32

/*-----------------------------------------------------------*/

/* Task utilities. */

/* The interrupt priority (for vectors 16 to 255) is determined using vector/16.
 * The quotient is rounded to the nearest integer with 1 being the lowest priority
 * and 15 is the highest.  Therefore the following two interrupts are at the lowest
 * priority.  *NOTE 1* If the yield vector is changed then it must also be changed
 * in the portYIELD_INTERRUPT definition immediately below. */
#define portAPIC_TIMER_INT_VECTOR        ( 0x20 )
#define portAPIC_DEBUG_SERIAL_INT_VECTOR ( 0x24 )
#define portAPIC_YIELD_INT_VECTOR        ( 0x21 )

/* Build yield interrupt instruction. */
#define portYIELD_INTERRUPT             "int $0x21"

/* APIC register addresses. */
#define portAPIC_EOI                    ( *( ( volatile uint32_t * ) 0xFEE000B0UL ) )

/* APIC bit definitions. */
#define portAPIC_ENABLE_BIT             ( 1UL << 8UL )
#define portAPIC_TIMER_PERIODIC         ( 1UL << 17UL )
#define portAPIC_DISABLE                ( 1UL << 16UL )
#define portAPIC_NMI                    ( 4 << 8 )
#define portAPIC_DIV_16                 ( 0x03 )

/* Define local APIC register addresses. */
#define configAPIC_BASE    0xFEE00000UL
#define portAPIC_ID_REGISTER            ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x20UL ) ) )
#define portAPIC_SPURIOUS_INT           ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0xF0UL ) ) )
#define portAPIC_LVT_TIMER              ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x320UL ) ) )
#define portAPIC_TIMER_INITIAL_COUNT    ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x380UL ) ) )
#define portAPIC_TIMER_CURRENT_COUNT    ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x390UL ) ) )
#define portAPIC_TASK_PRIORITY          ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x80UL ) ) )
#define portAPIC_LVT_ERROR              ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x370UL ) ) )
#define portAPIC_ERROR_STATUS           ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x280UL ) ) )
#define portAPIC_LDR                    ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0xD0UL ) ) )
#define portAPIC_TMRDIV                 ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x3E0UL ) ) )
#define portAPIC_LVT_PERF               ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x340UL ) ) )
#define portAPIC_LVT_LINT0              ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x350UL ) ) )
#define portAPIC_LVT_LINT1              ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0x360UL ) ) )

/* Don't yield if inside a critical section - instead hold the yield pending
 * so it is performed when the critical section is exited. */
#define portYIELD()                                  \
    {                                                \
        extern volatile uint32_t ulCriticalNesting;  \
        extern volatile uint32_t ulPortYieldPending; \
        if( ulCriticalNesting != 0 )                 \
        {                                            \
            ulPortYieldPending = pdTRUE;             \
        }                                            \
        else                                         \
        {                                            \
            __asm volatile ( portYIELD_INTERRUPT );  \
        }                                            \
    };



/* Called at the end of an ISR that can cause a context switch - pend a yield if
 * xSwitchRequired is not false. */
#define portEND_SWITCHING_ISR( xSwitchRequired )     \
    {                                                \
        extern volatile uint32_t ulPortYieldPending; \
        if( xSwitchRequired != pdFALSE )             \
        {                                            \
            ulPortYieldPending = 1;                  \
        }                                            \
    }

/* Same as portEND_SWITCHING_ISR() - take your pick which name to use. */
#define portYIELD_FROM_ISR( x )    portEND_SWITCHING_ISR( x )

/*-----------------------------------------------------------
* Critical section control
*----------------------------------------------------------*/

/* Critical sections for use in interrupts. */
#define portSET_INTERRUPT_MASK_FROM_ISR()         ulPortSetInterruptMask()
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( x )    vPortClearInterruptMask( x )

extern int vPortIsPrivileged(void);
extern void vPortEnterCritical( void );
extern void vPortExitCritical( void );
extern uint32_t ulPortSetInterruptMask( void );
extern void vPortClearInterruptMask( uint32_t ulNewMaskValue );

/* These macros do not globally disable/enable interrupts.  They do mask off
 * interrupts that have a priority below configMAX_API_CALL_INTERRUPT_PRIORITY. */
#define portENTER_CRITICAL()        vPortEnterCritical()
#define portEXIT_CRITICAL()         vPortExitCritical()
#define portDISABLE_INTERRUPTS()    __asm volatile ( "cli" )
#define portENABLE_INTERRUPTS()     __asm volatile ( "sti" )

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site.  These are
 * not required for this port but included in case common demo code that uses these
 * macros is used. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters )    void vFunction( void * pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters )          void vFunction( void * pvParameters )

/* Architecture specific optimisations. */
#if configUSE_PORT_OPTIMISED_TASK_SELECTION == 1

/* Store/clear the ready priorities in a bit map. */
    #define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities ) \
    __asm volatile ( "bsr %1, %0\n\t"                                    \
                     : "=r" ( uxTopPriority ) : "rm" ( uxReadyPriorities ) : "cc" )

    #define portRECORD_READY_PRIORITY( uxPriority, uxReadyPriorities )    ( uxReadyPriorities ) |= ( 1UL << ( uxPriority ) )
    #define portRESET_READY_PRIORITY( uxPriority, uxReadyPriorities )     ( uxReadyPriorities ) &= ~( 1UL << ( uxPriority ) )

#endif /* configUSE_PORT_OPTIMISED_TASK_SELECTION */

#define portNOP()    __asm volatile ( "NOP" )

/*-----------------------------------------------------------
* Misc
*----------------------------------------------------------*/

#define portNUM_VECTORS     256
#define portMAX_PRIORITY    15

#ifndef configUSE_PORT_OPTIMISED_TASK_SELECTION

/* The FreeRTOS scheduling algorithm selects the task that will enter the
 * Running state.  configUSE_PORT_OPTIMISED_TASK_SELECTION is used to set how
 * that is done.
 *
 * If configUSE_PORT_OPTIMISED_TASK_SELECTION is set to 0 then the task to
 * enter the Running state is selected using a portable algorithm written in
 * C.  This is the slowest method, but the algorithm does not restrict the
 * maximum number of unique RTOS task priorities that are available.
 *
 * If configUSE_PORT_OPTIMISED_TASK_SELECTION is set to 1 then the task to
 * enter the Running state is selected using a single assembly instruction.
 * This is the fastest method, but restricts the maximum number of unique RTOS
 * task priorities to 32 (the same task priority can be assigned to any number
 * of RTOS tasks). */
    #warning configUSE_PORT_OPTIMISED_TASK_SELECTION was not defined in FreeRTOSConfig.h and has been defaulted to 1
    #define configUSE_PORT_OPTIMISED_TASK_SELECTION    1
#endif

/* The value written to the task priority register to raise the interrupt mask
 * to the maximum from which FreeRTOS API calls can be made. */
#define portAPIC_PRIORITY_SHIFT        ( 4UL )
#define portAPIC_MAX_SUB_PRIORITY      ( 0x0fUL )
#define portMAX_API_CALL_PRIORITY      ( ( configMAX_API_CALL_INTERRUPT_PRIORITY << portAPIC_PRIORITY_SHIFT ) | portAPIC_MAX_SUB_PRIORITY )

/* Asserts if interrupt safe FreeRTOS functions are called from a priority
 * above the max system call interrupt priority. */
#define portAPIC_PROCESSOR_PRIORITY    ( *( ( volatile uint32_t * ) ( configAPIC_BASE + 0xA0UL ) ) )
#define portASSERT_IF_INTERRUPT_PRIORITY_INVALID()    configASSERT( ( portAPIC_PROCESSOR_PRIORITY ) <= ( portMAX_API_CALL_PRIORITY ) )

/* Support for Restricted Tasks */
#define portUSING_MPU_WRAPPERS 1

/* 
*  The following two setting are saved for each task
*  FreeRTOS saves this information in Task Control Block
*  and these are used during context switch.
*/
typedef struct {
    uint64_t pgd;
    StackType_t *kernel_stack;
} xMPU_SETTINGS;

/* Allow upto 16 memory regions to be defined.*/
#define portNUM_CONFIGURABLE_REGIONS    16
#define portPRIVILEGE_BIT               0x80000000UL
#define portIS_PRIVILEGED()             vPortIsPrivileged()


/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* PORTMACRO_H */
