/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * Copyright 2025 Arm Limited and/or its affiliates
 * <open-source-office@arm.com>
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
#define portSTACK_TYPE    size_t
#define portBASE_TYPE     long

#if !defined(__ASSEMBLER__)
    typedef portSTACK_TYPE   StackType_t;
    typedef portBASE_TYPE    BaseType_t;
    typedef uint64_t         UBaseType_t;

    typedef uint64_t         TickType_t;
    #define portMAX_DELAY    ( ( TickType_t ) 0xffffffffffffffff )
#endif /* if !defined(__ASSEMBLER__) */

/* 64-bit tick type on a 64-bit architecture, so reads of the tick count do
 * not need to be guarded with a critical section. */
#define portTICK_TYPE_IS_ATOMIC    1

/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define portSTACK_GROWTH         ( -1 )
#define portTICK_PERIOD_MS       ( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT       16
#define portPOINTER_SIZE_TYPE    uint64_t

/*-----------------------------------------------------------*/

/* Task utilities. */

#if !defined(__ASSEMBLER__)
    /* Called at the end of an ISR that can cause a context switch. */
    #if ( configNUMBER_OF_CORES == 1 )
        #define portEND_SWITCHING_ISR( xSwitchRequired ) \
        {                                                \
            extern uint64_t ullPortYieldRequired;        \
                                                        \
            if( xSwitchRequired != pdFALSE )             \
            {                                            \
                ullPortYieldRequired = pdTRUE;           \
            }                                            \
        }
    #else
        #define portEND_SWITCHING_ISR( xSwitchRequired )                   \
        {                                                                  \
            extern uint64_t ullPortYieldRequired[ configNUMBER_OF_CORES ]; \
                                                                        \
            if( xSwitchRequired != pdFALSE )                               \
            {                                                              \
                ullPortYieldRequired[ portGET_CORE_ID() ] = pdTRUE;        \
            }                                                              \
        }
    #endif /* if ( configNUMBER_OF_CORES == 1 ) */
#endif /* if !defined(__ASSEMBLER__) */

/**
 * @brief SVC numbers.
 */
#define portSVC_YIELD                      105
#define portSVC_START_FIRST_TASK           106
#define portSVC_DISABLE_INTERRUPTS         107
#define portSVC_ENABLE_INTERRUPTS          108
#define portSVC_GET_CORE_ID                109
#define portSVC_MASK_ALL_INTERRUPTS        110
#define portSVC_UNMASK_ALL_INTERRUPTS      111
#define portSVC_UNMASK_INTERRUPTS          112

#define portYIELD_FROM_ISR( x )    portEND_SWITCHING_ISR( x )
#define portYIELD()                __asm volatile ( "SVC %0" : : "i" ( portSVC_YIELD ) : "memory" )

/*-----------------------------------------------------------
* Critical section control
*----------------------------------------------------------*/

#if !defined(__ASSEMBLER__)
    extern UBaseType_t vTaskEnterCriticalFromISR( void );
    extern void vTaskExitCriticalFromISR( UBaseType_t uxSavedInterruptStatus );
    extern UBaseType_t uxPortSetInterruptMask( void );
    extern UBaseType_t uxPortSetInterruptMaskFromISR( void );
    extern void vPortClearInterruptMask( UBaseType_t uxNewMaskValue );
    extern void vPortClearInterruptMaskFromISR( UBaseType_t uxNewMaskValue );
    extern void vInterruptCore( uint32_t ulInterruptID, uint32_t ulCoreID );
#endif /* if !defined(__ASSEMBLER__) */

/* Use SVC so this is safe from EL0. EL1 sites in the port use direct MSR. */\
#define portDISABLE_INTERRUPTS() __asm volatile ( "SVC %0" : : "i" ( portSVC_DISABLE_INTERRUPTS ) : "memory" )

#define portENABLE_INTERRUPTS()  __asm volatile ( "SVC %0" : : "i" ( portSVC_ENABLE_INTERRUPTS ) : "memory" )


/* In all GICs 255 can be written to the priority mask register to unmask all
 * (but the lowest) interrupt priority. */
#define portUNMASK_VALUE           ( 0xFFUL )

#if !defined(__ASSEMBLER__)
    /* These macros do not globally disable/enable interrupts.  They do mask off
    * interrupts that have a priority below configMAX_API_CALL_INTERRUPT_PRIORITY. */
    #if  ( configNUMBER_OF_CORES == 1 )
        extern void vPortEnterCritical( void );
        extern void vPortExitCritical( void );
        #define portENTER_CRITICAL()                  vPortEnterCritical()
        #define portEXIT_CRITICAL()                   vPortExitCritical()
    #else
        #define portENTER_CRITICAL()                  vTaskEnterCritical()
        #define portEXIT_CRITICAL()                   vTaskExitCritical()
    #endif
    #define portSET_INTERRUPT_MASK_FROM_ISR()         uxPortSetInterruptMaskFromISR()
    #define portCLEAR_INTERRUPT_MASK_FROM_ISR( x )    vPortClearInterruptMaskFromISR( x )
    #define portENTER_CRITICAL_FROM_ISR()             vTaskEnterCriticalFromISR()
    #define portEXIT_CRITICAL_FROM_ISR( x )           vTaskExitCriticalFromISR( x )
#endif /* if !defined(__ASSEMBLER__) */

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site.  These are
 * not required for this port but included in case common demo code that uses these
 * macros is used. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters )    void vFunction( void * pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters )          void vFunction( void * pvParameters )

#if !defined(__ASSEMBLER__)
    /* Prototype of the FreeRTOS tick handler.  This must be installed as the
    * handler for whichever peripheral is used to generate the RTOS tick. */
    void FreeRTOS_Tick_Handler( void );
#endif /* if !defined(__ASSEMBLER__) */

#define portTASK_NO_FPU_CONTEXT_BY_DEFAULT     ( 1U )
#define portTASK_HAVE_FPU_CONTEXT_BY_DEFAULT   ( 2U )

/* If configUSE_TASK_FPU_SUPPORT is set to portTASK_NO_FPU_CONTEXT_BY_DEFAULT (1U)
 * (or left undefined) then tasks are created without an FPU context and
 * must call vPortTaskUsesFPU() to give themselves an FPU context before
 * using any FPU instructions.  If configUSE_TASK_FPU_SUPPORT is set to
 * portTASK_HAVE_FPU_CONTEXT_BY_DEFAULT (2U) then all tasks will have an FPU context
 * by default. */
#if ( configUSE_TASK_FPU_SUPPORT == portTASK_NO_FPU_CONTEXT_BY_DEFAULT )
    void vPortTaskUsesFPU( void );
#else
/* Each task has an FPU context already, so define this function away to
 * nothing to prevent it from being called accidentally. */
    #define vPortTaskUsesFPU()
#endif
#define portTASK_USES_FLOATING_POINT()    vPortTaskUsesFPU()

#define portLOWEST_INTERRUPT_PRIORITY           ( ( ( uint32_t ) configUNIQUE_INTERRUPT_PRIORITIES ) - 1UL )
#define portLOWEST_USABLE_INTERRUPT_PRIORITY    ( portLOWEST_INTERRUPT_PRIORITY - 1UL )

/* Architecture specific optimisations. */
#ifndef configUSE_PORT_OPTIMISED_TASK_SELECTION
    #define configUSE_PORT_OPTIMISED_TASK_SELECTION    1
#endif

#if configUSE_PORT_OPTIMISED_TASK_SELECTION == 1

/* Store/clear the ready priorities in a bit map. */
    #define portRECORD_READY_PRIORITY( uxPriority, uxReadyPriorities )    ( uxReadyPriorities ) |= ( 1UL << ( uxPriority ) )
    #define portRESET_READY_PRIORITY( uxPriority, uxReadyPriorities )     ( uxReadyPriorities ) &= ~( 1UL << ( uxPriority ) )

/*-----------------------------------------------------------*/

    #define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities )    uxTopPriority = ( 31 - __builtin_clz( uxReadyPriorities ) )

#endif /* configUSE_PORT_OPTIMISED_TASK_SELECTION */

#if ( configASSERT_DEFINED == 1 )
    void vPortValidateInterruptPriority( void );
    #define portASSERT_IF_INTERRUPT_PRIORITY_INVALID()    vPortValidateInterruptPriority()
#endif /* configASSERT */

#define portNOP()                                         __asm volatile ( "NOP" )
#define portINLINE    __inline

/* The number of bits to shift for an interrupt priority is dependent on the
 * number of bits implemented by the interrupt controller. */
#if configUNIQUE_INTERRUPT_PRIORITIES == 16
    #define portPRIORITY_SHIFT            4
    #define portMAX_BINARY_POINT_VALUE    3
#elif configUNIQUE_INTERRUPT_PRIORITIES == 32
    #define portPRIORITY_SHIFT            3
    #define portMAX_BINARY_POINT_VALUE    2
#elif configUNIQUE_INTERRUPT_PRIORITIES == 64
    #define portPRIORITY_SHIFT            2
    #define portMAX_BINARY_POINT_VALUE    1
#elif configUNIQUE_INTERRUPT_PRIORITIES == 128
    #define portPRIORITY_SHIFT            1
    #define portMAX_BINARY_POINT_VALUE    0
#elif configUNIQUE_INTERRUPT_PRIORITIES == 256
    #define portPRIORITY_SHIFT            0
    #define portMAX_BINARY_POINT_VALUE    0
#else /* if configUNIQUE_INTERRUPT_PRIORITIES == 16 */
    #error Invalid configUNIQUE_INTERRUPT_PRIORITIES setting.  configUNIQUE_INTERRUPT_PRIORITIES must be set to the number of unique priorities implemented by the target hardware
#endif /* if configUNIQUE_INTERRUPT_PRIORITIES == 16 */

#define portINTERRUPT_PRIORITY_REGISTER_OFFSET    ( 0x400U )
#define portYIELD_CORE_INT_ID                     ( 0x0U )

#if ( configNUMBER_OF_CORES > 1 )

    #if !defined(__ASSEMBLER__)
        typedef enum
        {
            eIsrLock = 0,
            eTaskLock,
            eLockCount
        } ePortRTOSLock;

        extern volatile uint64_t ullCriticalNestings[ configNUMBER_OF_CORES ];
        extern void vPortRecursiveLock( BaseType_t xCoreID,
                                        ePortRTOSLock eLockNum,
                                        BaseType_t uxAcquire );
        extern BaseType_t xPortGetCoreID( void );
    #endif /* if !defined(__ASSEMBLER__) */

    #define portSET_INTERRUPT_MASK()         uxPortSetInterruptMask()
    #define portCLEAR_INTERRUPT_MASK( x )    vPortClearInterruptMask( x )

    #define portMAX_CORE_COUNT      configNUMBER_OF_CORES
    #define portGET_CORE_ID()       xPortGetCoreID()

/* Use SGI 0 as the yield core interrupt. */
    #define portYIELD_CORE( xCoreID )   vInterruptCore( portYIELD_CORE_INT_ID, ( uint32_t ) xCoreID )

    #define portRELEASE_ISR_LOCK( xCoreID )                    vPortRecursiveLock( ( xCoreID ), eIsrLock, pdFALSE )
    #define portGET_ISR_LOCK( xCoreID )                        vPortRecursiveLock( ( xCoreID ), eIsrLock, pdTRUE )

    #define portRELEASE_TASK_LOCK( xCoreID )                   vPortRecursiveLock( ( xCoreID ), eTaskLock, pdFALSE )
    #define portGET_TASK_LOCK( xCoreID )                       vPortRecursiveLock( ( xCoreID ), eTaskLock, pdTRUE )

    #define portGET_CRITICAL_NESTING_COUNT( xCoreID )          ( ullCriticalNestings[ ( xCoreID ) ] )
    #define portSET_CRITICAL_NESTING_COUNT( xCoreID, x )       ( ullCriticalNestings[ ( xCoreID ) ] = ( x ) )
    #define portINCREMENT_CRITICAL_NESTING_COUNT( xCoreID )    ( ullCriticalNestings[ ( xCoreID ) ]++ )
    #define portDECREMENT_CRITICAL_NESTING_COUNT( xCoreID )    ( ullCriticalNestings[ ( xCoreID ) ]-- )

#endif /* configNUMBER_OF_CORES > 1 */

#define portMEMORY_BARRIER()    __asm volatile ( "" ::: "memory" )

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* PORTMACRO_H */
