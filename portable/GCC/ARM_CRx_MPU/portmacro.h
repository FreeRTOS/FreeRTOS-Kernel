/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/**
 * @brief Functions, Defines, and Structs for use in the ARM_CRx_MPU FreeRTOS-Port
 * @file portmacro.h
 * @note The settings in this file configure FreeRTOS correctly for the given
 *  hardware and compiler. These settings should not be altered.
 */

/**
 * @brief APIs and Variables used to control the onboard MPU.
 * @defgroup MPU Control
 */

#ifdef __cplusplus
extern "C" {
#endif

/* Include stdint for integer types of specific bit widths */
#include <stdint.h>

/* ------------------------------ FreeRTOS Config Check ------------------------------ */

/* Include the FreeRTOS Config file first to get the includes being used */
#include "FreeRTOSConfig.h"

#ifndef configENABLE_MPU
    #define configENABLE_MPU 1
#elif( configENABLE_MPU != 1 )
    #error "This port is only usable with configENABLE_MPU set to 1"
#endif /* configENABLE_MPU */

#ifndef configENABLE_ACCESS_CONTROL_LIST
    #define configENABLE_ACCESS_CONTROL_LIST 1
#endif /* configENABLE_ACCESS_CONTROL_LIST */

#ifndef configPROTECTED_KERNEL_OBJECT_POOL_SIZE
    #error "Set configPROTECTED_KERNEL_OBJECT_POOL_SIZE to at least the " \
            "number of FreeRTOS-Kernel Objects to be created"
#endif /* configPROTECTED_KERNEL_OBJECT_POOL_SIZE */

/**
 * @brief The size in Bytes that the Privileged System Call Stack should be.
 *
 * @ingroup MPU Privilege
 *
 * @note A Stack of this length, in bytes, is used by FreeRTOS APIs when called
 * by an unprivileged task.
 */
#ifndef configSYSTEM_CALL_STACK_SIZE
    #error "Define configSYSTEM_CALL_STACK_SIZE to a length, in bytes, " \
            "to use when an unprivileged task makes a FreeRTOS Kernel call. "
#endif /* configSYSTEM_CALL_STACK_SIZE */

/* ------------------------------ FreeRTOS Config Check ------------------------------ */

#if( configUSE_PORT_OPTIMISED_TASK_SELECTION == 1 )
    /* Check the configuration. */
    #if( configMAX_PRIORITIES > 32 )
        #error "configUSE_PORT_OPTIMISED_TASK_SELECTION can only be set to 1 when " \
                "configMAX_PRIORITIES is less than or equal to 32. " \
                "It is very rare that a system requires more than 10 to 15 difference " \
                "priorities as tasks that share a priority will time slice."
    #endif /* ( configMAX_PRIORITIES > 32 ) */

    /**
     * @brief Mark that a task of the current priority is ready for execution.
     *
     * @ingroup Scheduler
     *
     * @param[in] uxPriority Priority of task that can enter the ready state
     * @param[out] uxTopReadyPriority Bitmap of tasks that are in the ready state
     */
    #define portRECORD_READY_PRIORITY( uxPriority, uxTopReadyPriority ) \
        ( uxTopReadyPriority ) |= ( 1UL << ( uxPriority ) )

    /**
     * @brief Mark that a task of the current priority has left the ready state.
     *
     * @ingroup Scheduler
     *
     * @param[in] uxPriority Priority of task that is leaving the ready state
     * @param[out] uxTopReadyPriority Bitmap of tasks that are in the ready state
     */
    #define portRESET_READY_PRIORITY( uxPriority, uxTopReadyPriority ) \
        ( uxTopReadyPriority ) &= ~( 1UL << ( uxPriority ) )

    /**
     * @brief Determine what the highest priority ready task is.
     *
     * @ingroup Scheduler
     *
     * @param[out] uxTopReadyPriority Bitmap of tasks that are in the ready state
     * @param[out] uxTopPriority The highest priority ready task's priority value.
     */
    #define portGET_HIGHEST_PRIORITY( uxTopPriority, uxTopReadyPriority ) \
        uxTopPriority = ( 31UL - ulPortCountLeadingZeros( ( uxTopReadyPriority ) ) )

#endif /* configUSE_PORT_OPTIMISED_TASK_SELECTION */

#ifndef configSETUP_TICK_INTERRUPT
    #error "configSETUP_TICK_INTERRUPT() must be defined in FreeRTOSConfig.h " \
            "to call the function that sets up the tick interrupt."
#endif /* configSETUP_TICK_INTERRUPT */

#if( configUSE_TICKLESS_IDLE != 0 )
    #error This port does not support tickless idle
#endif /* ( configUSE_TICKLESS_IDLE != 0 ) */

/* ------------------------------ Port Type Definitions ------------------------------ */

#include "portmacro_asm.h"

/**
 * @brief Critical section nesting value to mark the end of a critical section.
 *
 * @ingroup Critical Sections
 *
 * @note
 * A critical section is exited when the critical section nesting count reaches
 * this value. When exiting a critical section IRQs are re-enabled.
 */
#define portNO_CRITICAL_NESTING ( ( uint32_t ) 0x0 )

/**
 * @brief Bit value used to mark if the CPU is currently executing in Thumb Mode.
 * @ingroup Task Context
 */
#define portTHUMB_MODE_BIT      ( ( StackType_t ) 0x20 )

/**
 * @brief Value used to check if a task's function is a Thumb function.
 * @ingroup Task Context
 */
#define portTHUMB_MODE_ADDRESS  ( 0x01UL )

/**
 * @brief Unsigned Data type equal to the data word operating size of the CPU.
 *
 * @ingroup Port Interface Specifications
 *
 * @note
 * The FreeRTOS-Kernel needs to be able to use an unsigned type that is
 * the most efficient, natural type for the targeted architecture.
 */
typedef uint32_t StackType_t;

/**
 * @brief Signed Data type equal to the data word operating size of the CPU.
 *
 * @ingroup Port Interface Specifications
 *
 * @note
 * The FreeRTOS-Kernel needs to be able to use a signed type that is
 * the most efficient, natural type for the targeted architecture.
 */
typedef int32_t BaseType_t;

/**
 * @brief Unsigned Data type equal to the data word operating size of the CPU.
 *
 * @ingroup Port Interface Specifications
 *
 * @note
 * The FreeRTOS-Kernel needs to be able to use an unsigned type that is
 * the most efficient, natural type for the targeted architecture.
 */
typedef uint32_t UBaseType_t;

/**
 * @brief Integer type used for the Tick Counter.
 *
 * @note
 * Use a 32-bit tick type on a 32-bit architecture, so reads of the tick count
 * do not need to be guarded with a critical section.
 */
typedef uint32_t TickType_t;

/**
 * @brief Marks the direction the stack grows on the targeted CPU.
 *
 * @ingroup Port Interface Specifications
 *
 */
#define portSTACK_GROWTH   ( -1 )

/**
 * @brief Specifies at what number of bytes a stack pointer shall be aligned.
 *
 * @ingroup Port Interface Specifications
 *
 */
#define portBYTE_ALIGNMENT 8U

/**
 * @brief Task function prototype macro as described on FreeRTOS.org.
 *
 * @ingroup Port Interface Specifications
 *
 * @note
 * These are not required for this port but included in case common demo code
 * that uses these macros is used.
 */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) \
    void vFunction( void * pvParameters )

/**
 * @brief Task function prototype macro as described on FreeRTOS.org.
 *
 * @ingroup Port Interface Specifications
 *
 * @note
 * These are not required for this port but included in case common demo code
 * that uses these macros is used.
 */
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void * pvParameters )

/**
 * @brief Wrapper for the no-op ARM Assembly Instruction.
 * @ingroup Port Interface Specifications
 */
#define portNOP()                                    __asm volatile( "NOP" )

/**
 * @brief Wrapper for the Inline GCC Label.
 * @ingroup Port Interface Specifications
 */
#define portINLINE                                   __inline

/**
 * @brief Wrapper for the ARM Memory Sync Assembly Instruction.
 * @ingroup Port Interface Specifications
 */
#define portMEMORY_BARRIER()                         __asm volatile( "" ::: "memory" )

/**
 * @brief Defines if the system tick count can be accessed atomically.
 *
 * @ingroup System Clock
 */
#define portTICK_TYPE_IS_ATOMIC                      1

/**
 * @brief Define the number of miliseconds between system ticks.
 *
 * @ingroup System Clock
 */
#define portTICK_PERIOD_MS                           ( ( TickType_t ) 1000UL / configTICK_RATE_HZ )

/**
 * @brief Define the larges possible delay value for a task.
 *
 * @ingroup System Clock
 */
#define portMAX_DELAY                                ( TickType_t ) 0xFFFFFFFFUL

/* ----------------------------- Port Assembly Functions ----------------------------- */

/** @brief Assembly FreeRTOS Supervisor Call Handler.  */
void FreeRTOS_SVC_Handler( void );

/** @brief Assembly FreeRTOS Interrupt Handler */
void FreeRTOS_IRQ_Handler( void );

/**
 * @brief Make a Supervisor Call to swap the currently running task out.
 *
 * @ingroup Scheduler
 * @note The FreeRTOS-Kernel needs a method to swap the current task that is
 * running. The FreeRTOS-Port needs to ensure that when this happens any
 * hardware specific values related to the current task’s context are properly
 * saved. A properly saved context can be restored to allow execution of the
 * task as if it was not interrupted.
 */
void vPortYield( void );

/** @brief Raise a Supervisor Call to swap the currently running task out. */
#define portYIELD() vPortYield()

/**
 * @brief Disable IRQs then increment the critical nesting count.
 * @ingroup Critical Section
 */
void vPortEnterCritical( void );

/** @brief Enter a Critical Section inside of the FreeRTOS-Kernel */
#define portENTER_CRITICAL() vPortEnterCritical()

/**
 * @brief Enable IRQs and decrement the critical nesting count.
 * @ingroup Critical Section
 */
void vPortExitCritical( void );

/**
 * @brief Exit a Critical Section inside of the FreeRTOS-Kernel.
 * @ingroup Critical Section
 */
#define portEXIT_CRITICAL() vPortExitCritical()

/**
 * @brief Set the IRQ bit of the CPSR high, enabling IRQs.
 * @ingroup Interrupt Management
 */
void vPortEnableInterrupts( void );

/**
 * @brief Enable Interrupts by setting the IRQ allowed flag on the CPU
 * @ingroup Interrupt Management
 */
#define portENABLE_INTERRUPTS() vPortEnableInterrupts()

/**
 * @brief Set the IRQ bit of the CPSR low, disabling IRQs.
 * @ingroup Interrupt Management
 */
void vPortDisableInterrupts( void );

/**
 * @brief Enable Interrupts by lowering the IRQ allowed flag on the CPU.
 * @ingroup Interrupt Management
 */
#define portDISABLE_INTERRUPTS() vPortDisableInterrupts()

/**
 * @brief Exit the FreeRTOS-Kernel, restoring the task's settings.
 *
 * @ingroup Port Privilege
 *
 * @return void
 */
void vPortSystemCallExit( void );

/**
 * @brief Load the context of the first task.
 *
 * @ingroup Scheduler
 *
 * @note This is an assembly function implemented in portASM.s, it loads the
 * context of the first task from pxCurrentTCB.
 */
void vPortStartFirstTask( void );

/**
 * @brief Enable the onboard MPU.
 *
 * @ingroup MPU Control
 *
 * @return void
 */
void vMPUEnable( void );

/**
 * @brief Disable the onboard MPU.
 *
 * @ingroup MPU Control
 *
 * @return VOID
 */
void vMPUDisable( void );

/**
 * @brief Enable the MPU Background Region.
 *
 * @ingroup MPU Control
 *
 * @return void
 */
void vMPUEnableBackgroundRegion( void );

/**
 * @brief Disable the MPU Background Region
 *
 * @ingroup MPU Control
 *
 * @return void
 */
void vMPUDisableBackgroundRegion( void );
/**
 * @brief Assembly routine to set permissions for an MPU Region.
 *
 * @ingroup MPU Control
 *
 * @param[in] ulRegionNumber The MPU Region Number to change permissions for
 * @param[in] ulBaseAddress The base address of the MPU Region
 * @param[in] ulRegionSize The number of bytes to make the MPU Region
 * @param[in] ulRegionPermissions The permissions to assign to the MPU Region
 *
 * @note This is an Assembly Function implemented in portASM.S.
 * This is meant as a purely internal function that performs a raw write of the
 * provided values to the relevant MPU Registers. The inputs to this function
 * are checked internally before it is called in the port.c file.
 */
void vMPUSetRegion( uint32_t ulRegionNumber,
                    uint32_t ulBaseAddress,
                    uint32_t ulRegionSize,
                    uint32_t ulRegionPermissions );

/* ------------------------------- Port.c Declarations ------------------------------- */

/**
 * @brief Checks whether or not the processor is privileged.
 *
 * @ingroup Port Privilege
 *
 * @note
 * The Privilege level is determined by checking if bits [4:0] of
 * the callers Current Program Status Register are in USER_MODE, 0x10
 *
 * @return
 * 0 If the CPSR Mode Bits are set to 0x10
 * 1 If the CPSR Mode Bits are set to 0x11-0x11F
 *
 */
BaseType_t xPortIsPrivileged( void );

/**
 * @brief Check if the CPU is currently in a privileged operating mode.
 *
 * @ingroup Port Privilege
 *
 * @return
 * 1 If the processor is privileged
 * 0 If the processor is not privileged
 *
 */
#define portIS_PRIVILEGED() xPortIsPrivileged()

/**
 * @brief Check if ulTaskFlags has portTASK_IS_PRIVILEGED_FLAG.
 *
 * @ingroup Port Privilege
 *
 * @note
 * As this loads pxCurrentTCB to determine if the task's ulTaskFlags is privileged
 * or not, this function can return a different value than xPortIsPrivileged.
 *
 * @return
 * 0 If pxCurrentTCB's !( ulTaskFlags && portTASK_IS_PRIVILEGED_FLAG )
 * 1 If pxCurrentTCB's ( ulTaskFlags && portTASK_IS_PRIVILEGED_FLAG )
 */
BaseType_t xPortIsTaskPrivileged( void );

/**
 * @brief Checks whether or not the currently running task is privileged.
 *
 * @ingroup Port Privilege
 *
 * @return
 * pdTRUE if the calling task is privileged
 * pdFALSE if the calling task is not privileged
 */
#define portIS_TASK_PRIVILEGED() xPortIsTaskPrivileged()

/**
 * @brief Default return address for tasks, it is not meant to be called.
 *
 * @ingroup Task Context
 * @note This function is used as the default Link Register address if
 * configTASK_RETURN_ADDRESS is not defined in FreeRTOSConfig.h
 *
 */
void prvTaskExitError( void );

/**
 * @brief User provided task return function.
 *
 * @ingroup Task Context
 *
 * @note Let the user override the pre-loading of the initial LR with
 * the address of prvTaskExitError() in case it messes up unwinding of
 * the stack in the debugger.
 */
#ifdef configTASK_RETURN_ADDRESS
    #define portTASK_RETURN_ADDRESS configTASK_RETURN_ADDRESS
#else
    #define configTASK_RETURN_ADDRESS prvTaskExitError
#endif /* configTASK_RETURN_ADDRESS */

/**
 * @brief Function a task should execute if it exits its assigned function.
 *
 * @ingroup Task Context
 *
 * @note If configTASK_RETURN_ADDRESS is not defined this value shall be set to
 * prvTaskExitError().
 */
#define portTASK_RETURN_ADDRESS configTASK_RETURN_ADDRESS

/**
 * @brief Returns the number of leading zeros in a 32 bit variable.
 *
 * @param[in] ulBitmap 32 Bit long number to count zeros of.
 *
 * @return The number of leading zeros ulBitmap has.
 */
UBaseType_t ulPortCountLeadingZeros( UBaseType_t ulBitmap );

/**
 * @brief Function meant to end the FreeRTOS Scheduler, not implemented on this port.
 * @ingroup Scheduler
 */
void vPortEndScheduler( void );

/* --------------------------------- MPU Definitions --------------------------------- */

/**
 * @brief Mark that this port utilizes the onboard ARM MPU.
 *
 * @ingroup MPU Control
 *
 * @note The structures and methods of manipulating the MPU are contained
 * within the port layer. Fills the xMPUSettings structure with the memory
 * region information contained in xRegions.
 *
 */
#define portUSING_MPU_WRAPPERS     1

/**
 * @brief Used to mark if a task should be created as a privileged task.
 *
 * @ingroup Task Context
 * @ingroup MPU Control
 *
 * @note This is done by performing a bitwise OR of this value and the task priority.
 * For example, to create a privileged task at priority 2 the uxPriority
 * parameter should be set to ( 2 | portPRIVILEGE_BIT ).
 */
#define portPRIVILEGE_BIT          ( 0x80000000UL )

/** @brief Size of the System Call Buffer in the TCB. */

#define portSYSTEM_CALL_STACK_SIZE configSYSTEM_CALL_STACK_SIZE

/** @brief Size of an Access Control List (ACL) entry in bits. */
#define portACL_ENTRY_SIZE_BITS    ( 32UL )

/**
 * @brief Structure to hold the MPU Register Values.
 * @struct xMPU_REGION_REGISTERS
 *
 * @ingroup MPU Control
 *
 * NOTE: Do not modify this structure. The ordering of this struct MUST
 * line up with the ordering explained in portRESTORE_CONTEXT.
 */
typedef struct MPU_REGION_REGISTERS
{
    /**
     * @brief Member used to hold the MPU register value for the Region Size.
     * @struct xMPU_REGION_REGISTERS
     * @ingroup MPU Control
     */
    uint32_t ulRegionSize;

    /**
     * @brief Member used to hold the MPU register value for the Region Attributes.
     * @struct xMPU_REGION_REGISTERS
     * @ingroup MPU Control
     */
    uint32_t ulRegionAttribute;

    /**
     * @brief Member used to hold the MPU register value for the Region Base Address.
     * @struct xMPU_REGION_REGISTERS
     * @ingroup MPU Control
     */
    uint32_t ulRegionBaseAddress;
} xMPU_REGION_REGISTERS;

/**
 * @brief Structure to hold per-task System Call Stack information.
 * @struct xSYSTEM_CALL_STACK_INFO
 *
 * @ingroup Port Privilege
 *
 * NOTE: Do not modify this structure. The ordering of this structure is expected
 * to be this way in the assembly code of the port.
 */
typedef struct SYSTEM_CALL_STACK_INFO
{
    /**
     * @brief Stack Pointer of the task when it made a FreeRTOS System Call.
     * @struct xSYSTEM_CALL_STACK_INFO
     */
    uint32_t * pulTaskStackPointer;

    /**
     * @brief Link Register of the task when it made a FreeRTOS System Call.
     * @struct xSYSTEM_CALL_STACK_INFO
     */
    uint32_t * pulLinkRegisterAtSystemCallEntry;

    /**
     * @brief Pre-Set Stack Pointer to use when making a FreeRTOS System Call.
     * @struct xSYSTEM_CALL_STACK_INFO
     * @note This will point to the start of ulSystemCallStackBuffer[]
     */
    uint32_t * pulSystemCallStackPointer;

    /**
     * @brief Pre-Set Link Register to exit a FreeRTOS System Call.
     * @struct xSYSTEM_CALL_STACK_INFO
     * @note This value is set in pxPortInitialiseStack() to ensure after making
     * a FreeRTOS System Call that the last LR jump is to vPortSystemCallExit()
     */
    void * pulSystemCallLinkRegister;

    /**
     * @brief Buffer to be used when performing a FreeRTOS System Call.
     * @struct xSYSTEM_CALL_STACK_INFO
     */
    uint32_t ulSystemCallStackBuffer[ configSYSTEM_CALL_STACK_SIZE ];
} xSYSTEM_CALL_STACK_INFO;

/**
 * @brief Per-Task MPU Settings structure stored in the TCB
 * @struct xMPU_SETTINGS
 *
 * @ingroup MPU Control
 * @ingroup Task Context
 * @ingroup Port Privilege
 *
 * NOTE: Do not modify this structure. The ordering of this structure is expected to be
 * this way in the assembly code of the port.
 */
typedef struct MPU_SETTINGS
{
    /**
     * @brief Array of Per-Task MPU Register Values. Loaded on Task Context Restore.
     * @struct xMPU_SETTINGS
     */
    xMPU_REGION_REGISTERS xRegion[ portTOTAL_NUM_REGIONS_IN_TCB ];

    /**
     * @brief Buffer that holds a Task's Context when being swapped out.
     * @struct xMPU_SETTINGS
     */
    uint32_t ulContext[ MAX_CONTEXT_SIZE ];

    /**
     * @brief Variable to hold FreeRTOS Privilege Settings.
     * @struct xMPU_SETTINGS
     */
    uint32_t ulTaskFlags;

    /**
     * @brief System Call Info structure that is stored in the TCB.
     * @struct xMPU_SETTINGS
     */
    xSYSTEM_CALL_STACK_INFO xSystemCallStackInfo;

#if( configENABLE_ACCESS_CONTROL_LIST == 1 )
    uint32_t ulAccessControlList[ ( configPROTECTED_KERNEL_OBJECT_POOL_SIZE
                                    / portACL_ENTRY_SIZE_BITS )
                                  + 1UL ];
#endif
} xMPU_SETTINGS;

#ifdef __cplusplus
} /* extern C */
#endif

#endif /* PORTMACRO_H */
