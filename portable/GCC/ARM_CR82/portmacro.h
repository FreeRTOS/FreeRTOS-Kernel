/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * Copyright 2025-2026 Arm Limited and/or its affiliates
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

#define portSVC_SYSTEM_CALL_EXIT                    104
#define portSVC_YIELD                               105
#define portSVC_START_FIRST_TASK                    106
#define portSVC_DISABLE_INTERRUPTS                  107
#define portSVC_ENABLE_INTERRUPTS                   108
#define portSVC_GET_CORE_ID                         109
#define portSVC_MASK_ALL_INTERRUPTS                 110
#define portSVC_UNMASK_ALL_INTERRUPTS               111
#define portSVC_UNMASK_INTERRUPTS                   112
#define portSVC_CHECK_PRIVILEGE                     113
#define portSVC_SAVE_TASK_CONTEXT                   114
#define portSVC_RESTORE_CONTEXT                     115
#define portSVC_DELETE_CURRENT_TASK                 116
#define portSVC_INTERRUPT_CORE                      117

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
#define portMAX_API_PRIORITY_MASK                 ( configMAX_API_CALL_INTERRUPT_PRIORITY << portPRIORITY_SHIFT )

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
        extern uint8_t ucPortGetCoreID( void );
        extern uint8_t ucPortGetCoreIDFromIsr( void );
    #endif /* if !defined(__ASSEMBLER__) */

    #define portSET_INTERRUPT_MASK()         uxPortSetInterruptMask()
    #define portCLEAR_INTERRUPT_MASK( x )    vPortClearInterruptMask( x )

    #define portMAX_CORE_COUNT               configNUMBER_OF_CORES
    #define portGET_CORE_ID()                ucPortGetCoreID()
    #define portGET_CORE_ID_FROM_ISR()       ucPortGetCoreIDFromIsr()

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

/**
 * @brief MPU specific constants.
 */
#if ( configENABLE_MPU == 1 )

    #if !defined(__ASSEMBLER__)
        extern BaseType_t xPortIsTaskPrivileged( void );
    #endif /* if !defined(__ASSEMBLER__) */

    /* Device memory attributes used in MAIR_EL1 registers.
     *
     * 8-bit values encoded as follows:
     *  Bit[7:4] - 0000 - Device Memory
     *  Bit[3:2] - 00 --> Device-nGnRnE
     *             01 --> Device-nGnRE
     *             10 --> Device-nGRE
     *             11 --> Device-GRE
     *  Bit[1:0] - 00.
     */
    #define portMPU_DEVICE_MEMORY_nGnRnE                 ( 0x00 )
    #define portMPU_DEVICE_MEMORY_nGnRE                  ( 0x04 )
    #define portMPU_DEVICE_MEMORY_nGRE                   ( 0x08 )
    #define portMPU_DEVICE_MEMORY_GRE                    ( 0x0C )

    /* MPU settings that can be overridden in FreeRTOSConfig.h. */
    #ifndef configTOTAL_MPU_REGIONS
        #define configTOTAL_MPU_REGIONS                  ( 16UL )
    #endif

    #define portPRIVILEGED_FLASH_REGION                  ( 0ULL )                                /* Privileged flash region number. */
    #define portUNPRIVILEGED_FLASH_REGION                ( 1ULL )                                /* Unprivileged flash region number. */
    #define portUNPRIVILEGED_SYSCALLS_REGION             ( 2ULL )                                /* Unprivileged syscalls region number. */
    #define portPRIVILEGED_RAM_REGION                    ( 3ULL )                                /* Privileged RAM region number. */
    #define portSTACK_REGION                             ( 4ULL )                                /* Stack region number. */
    #define portSTACK_REGION_INDEX                       ( 0ULL )                                /* Stack region index in the xRegionSettings array. */
    #define portFIRST_CONFIGURABLE_REGION                ( 5ULL )                                /* First user configurable region number. */
    #define portLAST_CONFIGURABLE_REGION                 ( configTOTAL_MPU_REGIONS - 1UL )
    #define portNUM_CONFIGURABLE_REGIONS                 ( ( portLAST_CONFIGURABLE_REGION - portFIRST_CONFIGURABLE_REGION ) + 1 )
    #define portTOTAL_NUM_REGIONS                        ( portNUM_CONFIGURABLE_REGIONS + 1 )    /* Plus one to make space for the stack region. */

    #if ( configENABLE_ACCESS_CONTROL_LIST == 1 )
        #define portACL_ENTRY_SIZE_BITS ( 32UL )
    #endif /* configENABLE_ACCESS_CONTROL_LIST == 1 */

    #if !defined(__ASSEMBLER__)
        /**
         * @brief Settings to define an MPU region.
         */
        typedef struct MPURegionSettings
        {
            uint64_t ullPrbarEl1; /**< PRBAR_EL1 for the region. */
            uint64_t ullPrlarEl1; /**< PRLAR_EL1 for the region. */
        } MPURegionSettings_t;

        #ifndef configSYSTEM_CALL_STACK_SIZE
            #define configSYSTEM_CALL_STACK_SIZE 128  /* must be defined to the desired size of the system call stack in words for using MPU wrappers v2. */
        #endif

        /**
         * @brief System call info.
         */
        typedef struct SYSTEM_CALL_INFO
        {
            /* Used to save both the user-mode stack pointer (SP_EL0) and link register (X30)
             * at system call entry so they can be restored or referenced safely even if the task
             * switches out while executing the system call.
             */
            uint64_t ullLinkRegisterAtSystemCallEntry;
            uint64_t ullUserSPAtSystemCallEntry;
        } xSYSTEM_CALL_INFO;
    #endif /* if !defined(__ASSEMBLER__) */

    /**
     * @brief Task context as stored in the TCB.
     */
    #if ( configENABLE_FPU == 1 )
        /*
         * +-----------+------------+--------------------------------+-------------+------------------+
         * |  Q0-Q31   | FPSR, FPCR |  CRITICAL_NESTING, FPU_CONTEXT | X0-X30, XZR | INIT_PSTATE, PC  |
         * +-----------+------------+--------------------------------+-------------+------------------+
         *
         * <-----------><-----------><-------------------------------><------------><----------------->
         *      64            2                      2                      32               2
         */
        #define MAX_CONTEXT_SIZE    102

    #else /* #if ( configENABLE_FPU == 1 ) */
        /*
         * +--------------------------------+-------------+------------------+
         * |  CRITICAL_NESTING, FPU_CONTEXT | X0-X30, XZR | INIT_PSTATE, PC  |
         * +--------------------------------+-------------+------------------+
         * <-------------------------------><------------><------------------>
         *                 2                      32               2
         */
        #define MAX_CONTEXT_SIZE    36
    #endif /* #if ( configENABLE_FPU == 1 ) */

    #if !defined(__ASSEMBLER__)
        typedef struct MPU_SETTINGS
        {
            uint64_t ullTaskUnprivilegedSP;                                              /* Task's unprivileged user stack pointer. */
            uint64_t ullMairEl1;                                                         /* MAIR_EL1 for the task containing attributes. */
            MPURegionSettings_t xRegionsSettings[ portTOTAL_NUM_REGIONS ];               /* Settings for tasks' regions. */
            uint64_t ullContext[ MAX_CONTEXT_SIZE + configSYSTEM_CALL_STACK_SIZE ];      /* Task's saved context. */
            uint64_t ullTaskFlags;

            xSYSTEM_CALL_INFO xSystemCallInfo;

            #if ( configENABLE_ACCESS_CONTROL_LIST == 1 )
                uint32_t ulAccessControlList[ ( configPROTECTED_KERNEL_OBJECT_POOL_SIZE / portACL_ENTRY_SIZE_BITS ) + 1 ];
            #endif /* configENABLE_ACCESS_CONTROL_LIST */
        } xMPU_SETTINGS;
    #endif /* if !defined(__ASSEMBLER__) */

    #define portUSING_MPU_WRAPPERS                        ( 1 )
    #define portPRIVILEGE_BIT                             ( 0x80000000UL )

    /* Normal memory attributes used in MAIR_EL1 registers. */
    #define portMPU_NORMAL_MEMORY_NON_CACHEABLE           ( 0x44 )       /* Non-cacheable. */
    #define portMPU_NORMAL_MEMORY_BUFFERABLE_CACHEABLE    ( 0xFF )       /* Non-Transient, Write-back, Read-Allocate and Write-Allocate. */

    #define portMPU_MAIR_EL1_ATTR0_POS                    ( 0UL )
    #define portMPU_MAIR_EL1_ATTR0_MASK                   ( 0x00000000000000ffULL )

    #define portMPU_MAIR_EL1_ATTR1_POS                    ( 8UL )
    #define portMPU_MAIR_EL1_ATTR1_MASK                   ( 0x000000000000ff00ULL )

    #define portMPU_MAIR_EL1_ATTR2_POS                    ( 16UL )
    #define portMPU_MAIR_EL1_ATTR2_MASK                   ( 0x0000000000ff0000ULL )

    #define portMPU_MAIR_EL1_ATTR3_POS                    ( 24UL )
    #define portMPU_MAIR_EL1_ATTR3_MASK                   ( 0x00000000ff000000ULL )

    #define portMPU_MAIR_EL1_ATTR4_POS                    ( 32UL )
    #define portMPU_MAIR_EL1_ATTR4_MASK                   ( 0x000000ff00000000ULL )

    #define portMPU_MAIR_EL1_ATTR5_POS                    ( 40UL )
    #define portMPU_MAIR_EL1_ATTR5_MASK                   ( 0x0000ff0000000000ULL )

    #define portMPU_MAIR_EL1_ATTR6_POS                    ( 48UL )
    #define portMPU_MAIR_EL1_ATTR6_MASK                   ( 0x00ff000000000000ULL )

    #define portMPU_MAIR_EL1_ATTR7_POS                    ( 56UL )
    #define portMPU_MAIR_EL1_ATTR7_MASK                   ( 0xff00000000000000ULL )

    #define portMPU_PRBAR_EL1_ADDRESS_MASK                ( 0x0000FFFFFFFFFFC0ULL )
    #define portMPU_PRLAR_EL1_ADDRESS_MASK                ( 0x0000FFFFFFFFFFC0ULL )
    #define portMPU_PRBAR_EL1_ACCESS_PERMISSIONS_MASK     ( 3ULL<< 2ULL )

    #define portMPU_REGION_NON_SHAREABLE                  ( 0ULL << 4ULL )
    #define portMPU_REGION_OUTER_SHAREABLE                ( 2ULL << 4ULL )
    #define portMPU_REGION_INNER_SHAREABLE                ( 3ULL << 4ULL )

    #define portMPU_REGION_PRIVILEGED_READ_WRITE          ( 0ULL << 2ULL )
    #define portMPU_REGION_READ_WRITE                     ( 1ULL << 2ULL )
    #define portMPU_REGION_PRIVILEGED_READ_ONLY           ( 2ULL << 2ULL )
    #define portMPU_REGION_READ_ONLY                      ( 3ULL << 2ULL )

    #define portMPU_REGION_EXECUTE_NEVER                  ( 1ULL << 1ULL )

    #define portMPU_PRLAR_EL1_ATTR_INDEX0                 ( 0ULL << 1ULL )
    #define portMPU_PRLAR_EL1_ATTR_INDEX1                 ( 1ULL << 1ULL )
    #define portMPU_PRLAR_EL1_ATTR_INDEX2                 ( 2ULL << 1ULL )
    #define portMPU_PRLAR_EL1_ATTR_INDEX3                 ( 3ULL << 1ULL )
    #define portMPU_PRLAR_EL1_ATTR_INDEX4                 ( 4ULL << 1ULL )
    #define portMPU_PRLAR_EL1_ATTR_INDEX5                 ( 5ULL << 1ULL )
    #define portMPU_PRLAR_EL1_ATTR_INDEX6                 ( 6ULL << 1ULL )
    #define portMPU_PRLAR_EL1_ATTR_INDEX7                 ( 7ULL << 1ULL )

    #define portMPU_PRLAR_EL1_REGION_ENABLE               ( 1ULL )

    #define portMPU_ENABLE_BIT                            ( 1ULL << 0ULL )
    #define portMPU_PRIV_BACKGROUND_ENABLE_BIT            ( 1ULL << 17ULL )

    /* Max value that fits in a uint64_t type. */
    #define portUINT64_MAX                                ( ~( ( uint64_t ) 0 ) )
    #define portADD_UINT64_WILL_OVERFLOW( a, b )          ( ( a ) > ( portUINT64_MAX - ( b ) ) )

    /* Extract first address of the MPU region as encoded in the
     * PRBAR_EL1 register value. */
    #define portEXTRACT_FIRST_ADDRESS_FROM_PRBAR_EL1( prbar_el1 ) \
        ( ( prbar_el1 ) & portMPU_PRBAR_EL1_ADDRESS_MASK )

    /* Extract last address of the MPU region as encoded in the
     * PRLAR_EL1 register value. */
    #define portEXTRACT_LAST_ADDRESS_FROM_PRLAR_EL1( prlar_el1 ) \
        ( ( ( prlar_el1 ) & portMPU_PRLAR_EL1_ADDRESS_MASK ) | ~portMPU_PRLAR_EL1_ADDRESS_MASK )

    /* Does addr lies within [start, end] address range? */
    #define portIS_ADDRESS_WITHIN_RANGE( addr, start, end ) \
        ( ( ( addr ) >= ( start ) ) && ( ( addr ) <= ( end ) ) )

    /* Is the access request satisfied by the available permissions? */
    #define portIS_AUTHORIZED( accessRequest, permissions ) \
        ( ( ( permissions ) & ( accessRequest ) ) == accessRequest )

    /**
     * @brief Offsets in the task's stack (context).
     */
    #if ( configUSE_TASK_FPU_SUPPORT == portTASK_HAVE_FPU_CONTEXT_BY_DEFAULT )
        #define portOFFSET_TO_PC     ( 68 )
        #define portOFFSET_TO_LR     ( 70 )
        #define portOFFSET_TO_X0     ( 100 )
        #define portOFFSET_TO_X1     ( 101 )
        #define portOFFSET_TO_X2     ( 98 )
        #define portOFFSET_TO_X3     ( 99 )
    #else
        #define portOFFSET_TO_PC     ( 2 )
        #define portOFFSET_TO_LR     ( 4 )
        #define portOFFSET_TO_X0     ( 34 )
        #define portOFFSET_TO_X1     ( 35 )
        #define portOFFSET_TO_X2     ( 32 )
        #define portOFFSET_TO_X3     ( 33 )
    #endif

    /**
     * @brief Flag used to mark that a Task is privileged.
     *
     * @ingroup Port Privilege
     */
    #define portTASK_IS_PRIVILEGED_FLAG   ( 1UL << 1UL )

    /**
     * @brief Checks whether or not the calling task is privileged.
     *
     * @return pdTRUE if the calling task is privileged, pdFALSE otherwise.
     */
    #define portIS_TASK_PRIVILEGED() xPortIsTaskPrivileged()

#else

    #define portPRIVILEGE_BIT        ( 0x0UL )

#endif /* #if ( configENABLE_MPU == 1 ) */

#define portPSTATE_I_BIT             ( 0x7 )

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* PORTMACRO_H */
