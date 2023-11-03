/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*******************************************************************************
 * This file provides an example FreeRTOSConfig.h header file, inclusive of an
 * abbreviated explanation of each configuration item.  Online and reference
 * documentation provides more information.
 * https://www.freertos.org/a00110.html
 *
 * Constant values enclosed in square brackets ('[' and ']') must be completed
 * before this file will build.
 *
 * Use the FreeRTOSConfig.h supplied with the RTOS port in use rather than this
 * generic file, if one is available.
 ******************************************************************************/

#ifndef __FREERTOS_CONFIG_H__
#define __FREERTOS_CONFIG_H__

/******************************************************************************/
/* Hardware description related definitions. **********************************/
/******************************************************************************/

/* In most cases, configCPU_CLOCK_HZ must be set to the frequency of the clock
 * that drives the peripheral used to generate the kernels periodic tick interrupt.
 * The default value is set to 20MHz and matches the QEMU demo settings.  Your
 * application will certainly need a different value so set this correctly.
 * This is very often, but not always, equal to the main system clock frequency. */
#define configCPU_CLOCK_HZ    ( ( unsigned long ) 20000000 )

/* configSYSTICK_CLOCK_HZ is an optional parameter for ARM Cortex-M ports only.
 *
 * By default ARM Cortex-M ports generate the RTOS tick interrupt from the
 * Cortex-M SysTick timer. Most Cortex-M MCUs run the SysTick timer at the same
 * frequency as the MCU itself - when that is the case configSYSTICK_CLOCK_HZ is
 * not needed and should be left undefined. If the SysTick timer is clocked at a
 * different frequency to the MCU core then set configCPU_CLOCK_HZ to the MCU clock
 * frequency, as normal, and configSYSTICK_CLOCK_HZ to the SysTick clock
 * frequency.  Not used if left undefined.
 * The default value is undefined (commented out).  If you need this value bring it
 * back and set it to a suitable value */

/*
 #define configSYSTICK_CLOCK_HZ                  [Platform specific]
 */

/******************************************************************************/
/* Scheduling behaviour related definitions. **********************************/
/******************************************************************************/

/* configTICK_RATE_HZ sets frequency of the tick interrupt in Hz, normally
 * calculated from the configCPU_CLOCK_HZ value. */
#define configTICK_RATE_HZ                         100

/* Set configUSE_PREEMPTION to 1 to use pre-emptive scheduling.  Set
 * configUSE_PREEMPTION to 0 to use co-operative scheduling.
 * See https://www.freertos.org/single-core-amp-smp-rtos-scheduling.html */
#define configUSE_PREEMPTION                       1

/* Set configUSE_TIME_SLICING to 1 to have the scheduler switch between Ready
 * state tasks of equal priority on every tick interrupt.  Set
 * configUSE_TIME_SLICING to 0 to prevent the scheduler switching between Ready
 * state tasks just because there was a tick interrupt.  See
 * https://freertos.org/single-core-amp-smp-rtos-scheduling.html */
#define configUSE_TIME_SLICING                     0

/* Set configUSE_PORT_OPTIMISED_TASK_SELECTION to 1 to select the next task to
 * run using an algorithm optimised to the instruction set of the target hardware -
 * normally using a count leading zeros assembly instruction.  Set to 0 to select
 * the next task to run using a generic C algorithm that works for all FreeRTOS
 * ports.  Not all FreeRTOS ports have this option.  Defaults to 0 if left
 * undefined. */
#define configUSE_PORT_OPTIMISED_TASK_SELECTION    0

/* Set configUSE_TICKLESS_IDLE to 1 to use the low power tickless mode.  Set to
 * 0 to keep the tick interrupt running at all times.  Not all FreeRTOS ports
 * support tickless mode. See https://www.freertos.org/low-power-tickless-rtos.html
 * Defaults to 0 if left undefined. */
#define configUSE_TICKLESS_IDLE                    0

/* configMAX_PRIORITIES Sets the number of available task priorities.  Tasks can
 * be assigned priorities of 0 to (configMAX_PRIORITIES - 1).  Zero is the lowest
 * priority. */
#define configMAX_PRIORITIES                       5

/* configMINIMAL_STACK_SIZE defines the size of the stack used by the Idle task
 * (in words, not in bytes!).  The kernel does not use this constant for any other
 * purpose.  Demo applications use the constant to make the demos somewhat portable
 * across hardware architectures. */
#define configMINIMAL_STACK_SIZE                   128

/* configMAX_TASK_NAME_LEN sets the maximum length (in characters) of a task's
 * human readable name.  Includes the NULL terminator. */
#define configMAX_TASK_NAME_LEN                    16

/* Time is measured in 'ticks' - which is the number of times the tick interrupt
 * has executed since the RTOS kernel was started.
 * The tick count is held in a variable of type TickType_t.
 *
 * configTICK_TYPE_WIDTH_IN_BITS controls the type (and therefore bit-width) of TickType_t:
 *
 * Defining configTICK_TYPE_WIDTH_IN_BITS as TICK_TYPE_WIDTH_16_BITS causes
 * TickType_t to be defined (typedef'ed) as an unsigned 16-bit type.
 *
 * Defining configTICK_TYPE_WIDTH_IN_BITS as TICK_TYPE_WIDTH_32_BITS causes
 * TickType_t to be defined (typedef'ed) as an unsigned 32-bit type.
 *
 * Defining configTICK_TYPE_WIDTH_IN_BITS as TICK_TYPE_WIDTH_64_BITS causes
 * TickType_t to be defined (typedef'ed) as an unsigned 64-bit type. */
#define configTICK_TYPE_WIDTH_IN_BITS              TICK_TYPE_WIDTH_64_BITS

/* Set configIDLE_SHOULD_YIELD to 1 to have the Idle task yield to an
 * application task if there is an Idle priority (priority 0) application task that
 * can run.  Set to 0 to have the Idle task use all of its timeslice.  Default to 1
 * if left undefined. */
#define configIDLE_SHOULD_YIELD                    1

/* Each task has an array of task notifications.
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the array.
 * See https://www.freertos.org/RTOS-task-notifications.html  Defaults to 1 if
 * left undefined. */
#define configTASK_NOTIFICATION_ARRAY_ENTRIES      1

/* configQUEUE_REGISTRY_SIZE sets the maximum number of queues and semaphores
 * that can be referenced from the queue registry.  Only required when using a
 * kernel aware debugger.  Defaults to 0 if left undefined. */
#define configQUEUE_REGISTRY_SIZE                  0

/* Set configENABLE_BACKWARD_COMPATIBILITY to 1 to map function names and
 * datatypes from old version of FreeRTOS to their latest equivalent.  Defaults to
 * 1 if left undefined. */
#define configENABLE_BACKWARD_COMPATIBILITY        0

/* Each task has its own array of pointers that can be used as thread local
 * storage.  configNUM_THREAD_LOCAL_STORAGE_POINTERS set the number of indexes in
 * the array.  See https://www.freertos.org/thread-local-storage-pointers.html
 * Defaults to 0 if left undefined. */
#define configNUM_THREAD_LOCAL_STORAGE_POINTERS    0

/* Sets the type used by the parameter to xTaskCreate() that specifies the stack
 * size of the task being created.  The same type is used to return information
 * about stack usage in various other API calls.  Defaults to size_t if left
 * undefined. */
#define configSTACK_DEPTH_TYPE                     size_t

/* configMESSAGE_BUFFER_LENGTH_TYPE sets the type used to store the length of
 *  each message written to a FreeRTOS message buffer (the length is also written to
 *  the message buffer.  Defaults to size_t if left undefined - but that may waste
 *  space if messages never go above a length that could be held in a uint8_t. */
#define configMESSAGE_BUFFER_LENGTH_TYPE           size_t

/* Set configUSE_NEWLIB_REENTRANT to 1 to have a newlib reent structure
 * allocated for each task.  Set to 0 to not support newlib reent structures.
 * Default to 0 if left undefined.
 *
 * Note Newlib support has been included by popular demand, but is not used or
 * tested by the FreeRTOS maintainers themselves. FreeRTOS is not responsible for
 * resulting newlib operation. User must be familiar with newlib and must provide
 * system-wide implementations of the necessary stubs. Note that (at the time of
 * writing) the current newlib design implements a system-wide malloc() that must
 * be provided with locks. */
#define configUSE_NEWLIB_REENTRANT                 0

/******************************************************************************/
/* Software timer related definitions. ****************************************/
/******************************************************************************/

/* Set configUSE_TIMERS to 1 to include software timer functionality in the
 * build.  Set to 0 to exclude software timer functionality from the build.  The
 * FreeRTOS/source/timers.c source file must be included in the build if
 * configUSE_TIMERS is set to 1.  Default to 0 if left undefined.  See
 * https://www.freertos.org/RTOS-software-timer.html */
#define configUSE_TIMERS                1

/* configTIMER_TASK_PRIORITY sets the priority used by the timer task.  Only
 * used if configUSE_TIMERS is set to 1.  The timer task is a standard FreeRTOS
 * task, so its priority is set like any other task.  See
 * https://www.freertos.org/RTOS-software-timer-service-daemon-task.html  Only used
 * if configUSE_TIMERS is set to 1. */
#define configTIMER_TASK_PRIORITY       ( configMAX_PRIORITIES - 1 )

/* configTIMER_TASK_STACK_DEPTH sets the size of the stack allocated to the
 * timer task (in words, not in bytes!).  The timer task is a standard FreeRTOS
 * task.  See https://www.freertos.org/RTOS-software-timer-service-daemon-task.html
 * Only used if configUSE_TIMERS is set to 1. */
#define configTIMER_TASK_STACK_DEPTH    configMINIMAL_STACK_SIZE

/* configTIMER_QUEUE_LENGTH sets the length of the queue (the number of discrete
 * items the queue can hold) used to send commands to the timer task.  See
 * https://www.freertos.org/RTOS-software-timer-service-daemon-task.html  Only used
 * if configUSE_TIMERS is set to 1. */
#define configTIMER_QUEUE_LENGTH        10

/******************************************************************************/
/* Memory allocation related definitions. *************************************/
/******************************************************************************/

/* Set configSUPPORT_STATIC_ALLOCATION to 1 to include FreeRTOS API functions
 * that create FreeRTOS objects (tasks, queues, etc.) using statically allocated
 * memory in the build.  Set to 0 to exclude the ability to create statically
 * allocated objects from the build.  Defaults to 0 if left undefined.  See
 * https://www.freertos.org/Static_Vs_Dynamic_Memory_Allocation.html */
#define configSUPPORT_STATIC_ALLOCATION              1

/* Set configSUPPORT_DYNAMIC_ALLOCATION to 1 to include FreeRTOS API functions
 * that create FreeRTOS objects (tasks, queues, etc.) using dynamically allocated
 * memory in the build.  Set to 0 to exclude the ability to create dynamically
 * allocated objects from the build.  Defaults to 1 if left undefined.  See
 * https://www.freertos.org/Static_Vs_Dynamic_Memory_Allocation.html */
#define configSUPPORT_DYNAMIC_ALLOCATION             1

/* Sets the total size of the FreeRTOS heap, in bytes, when heap_1.c, heap_2.c
 * or heap_4.c are included in the build.  This value is defaulted to 4096 bytes but
 * it must be tailored to each application.  Note the heap will appear in the .bss
 * section.  See https://www.freertos.org/a00111.html */
#define configTOTAL_HEAP_SIZE                        4096

/* Set configAPPLICATION_ALLOCATED_HEAP to 1 to have the application allocate
 * the array used as the FreeRTOS heap.  Set to 0 to have the linker allocate the
 * array used as the FreeRTOS heap.  Defaults to 0 if left undefined. */
#define configAPPLICATION_ALLOCATED_HEAP             0

/* Set configSTACK_ALLOCATION_FROM_SEPARATE_HEAP to 1 to have task stacks
 * allocated from somewhere other than the FreeRTOS heap.  This is useful if you
 * want to ensure stacks are held in fast memory.  Set to 0 to have task stacks
 * come from the standard FreeRTOS heap.  The application writer must provide
 * implementations for pvPortMallocStack() and vPortFreeStack() if set to 1.
 * Defaults to 0 if left undefined. */
#define configSTACK_ALLOCATION_FROM_SEPARATE_HEAP    0

/******************************************************************************/
/* Interrupt nesting behaviour configuration. *********************************/
/******************************************************************************/

/* configKERNEL_INTERRUPT_PRIORITY sets the priority of the tick and context
 * switch performing interrupts.  The default value is set to the highest interrupt
 * priority (0).  Not supported by all FreeRTOS ports.  See
 * https://www.freertos.org/RTOS-Cortex-M3-M4.html for information specific to ARM
 * Cortex-M devices. */
#define configKERNEL_INTERRUPT_PRIORITY          0

/* configMAX_SYSCALL_INTERRUPT_PRIORITY sets the interrupt priority above which
 * FreeRTOS API calls must not be made.  Interrupts above this priority are never
 * disabled, so never delayed by RTOS activity.  The default value is set to the
 * highest interrupt priority (0).  Not supported by all FreeRTOS ports.
 * See https://www.freertos.org/RTOS-Cortex-M3-M4.html for information specific to
 * ARM Cortex-M devices. */
#define configMAX_SYSCALL_INTERRUPT_PRIORITY     0

/* Another name for configMAX_SYSCALL_INTERRUPT_PRIORITY - the name used depends
 * on the FreeRTOS port. */
#define configMAX_API_CALL_INTERRUPT_PRIORITY    0

/******************************************************************************/
/* Hook and callback function related definitions. ****************************/
/******************************************************************************/

/* Set the following configUSE_* constants to 1 to include the named hook
 * functionality in the build.  Set to 0 to exclude the hook functionality from the
 * build.  The application writer is responsible for providing the hook function
 * for any set to 1.  See https://www.freertos.org/a00016.html */
#define configUSE_IDLE_HOOK                   0
#define configUSE_TICK_HOOK                   0
#define configUSE_MALLOC_FAILED_HOOK          0
#define configUSE_DAEMON_TASK_STARTUP_HOOK    0

/* Set configCHECK_FOR_STACK_OVERFLOW to 1 or 2 for FreeRTOS to check for a
 * stack overflow at the time of a context switch.  Set to 0 to not look for a
 * stack overflow.  If configCHECK_FOR_STACK_OVERFLOW is 1 then the check only
 * looks for the stack pointer being out of bounds when a task's context is saved
 * to its stack - this is fast but somewhat ineffective.  If
 * configCHECK_FOR_STACK_OVERFLOW is 2 then the check looks for a pattern written
 * to the end of a task's stack having been overwritten.  This is slower, but will
 * catch most (but not all) stack overflows.  The application writer must provide
 * the stack overflow callback when configCHECK_FOR_STACK_OVERFLOW is set to 1.
 * See https://www.freertos.org/Stacks-and-stack-overflow-checking.html  Defaults
 * to 0 if left undefined. */
#define configCHECK_FOR_STACK_OVERFLOW        2

/******************************************************************************/
/* Run time and task stats gathering related definitions. *********************/
/******************************************************************************/

/* Set configGENERATE_RUN_TIME_STATS to 1 to have FreeRTOS collect data on the
* processing time used by each task.  Set to 0 to not collect the data.  The
* application writer needs to provide a clock source if set to 1.  Defaults to 0
* if left undefined.  See https://www.freertos.org/rtos-run-time-stats.html */
#define configGENERATE_RUN_TIME_STATS           0

/* Set configUSE_TRACE_FACILITY to include additional task structure members
 * are used by trace and visualisation functions and tools.  Set to 0 to exclude
 * the additional information from the structures.  Defaults to 0 if left
 * undefined. */
#define configUSE_TRACE_FACILITY                0

/* Set to 1 to include the vTaskList() and vTaskGetRunTimeStats() functions in
 * the build.  Set to 0 to exclude these functions from the build.  These two
 * functions introduce a dependency on string formatting functions that would
 * otherwise not exist - hence they are kept separate.  Defaults to 0 if left
 * undefined. */
#define configUSE_STATS_FORMATTING_FUNCTIONS    0

/******************************************************************************/
/* Debugging assistance. ******************************************************/
/******************************************************************************/

/* configASSERT() has the same semantics as the standard C assert().  It can
 * either be defined to take an action when the assertion fails, or not defined
 * at all (i.e. comment out or delete the definitions) to completely remove
 * assertions.  configASSERT() can be defined to anything you want, for example
 * you can call a function if an assert fails that passes the filename and line
 * number of the failing assert (for example, "vAssertCalled( __FILE__, __LINE__ )"
 * or it can simple disable interrupts and sit in a loop to halt all execution
 * on the failing line for viewing in a debugger. */
#define configASSERT( x )         \
    if( ( x ) == 0 )              \
    {                             \
        taskDISABLE_INTERRUPTS(); \
        for( ; ; )                \
        ;                         \
    }

/******************************************************************************/
/* Cortex-M MPU specific definitions. *****************************************/
/******************************************************************************/

/* If configINCLUDE_APPLICATION_DEFINED_PRIVILEGED_FUNCTIONS is set to 1 then
 * the application writer can provide functions that execute in privileged mode.
 * See: https://www.freertos.org/a00110.html#configINCLUDE_APPLICATION_DEFINED_PRIVILEGED_FUNCTIONS
 * Defaults to 0 if left undefined.  Only used by the FreeRTOS Cortex-M MPU ports,
 * not the standard ARMv7-M Cortex-M port. */
#define configINCLUDE_APPLICATION_DEFINED_PRIVILEGED_FUNCTIONS    0

/* Set configTOTAL_MPU_REGIONS to the number of MPU regions implemented on your
 * target hardware.  Normally 8 or 16.  Only used by the FreeRTOS Cortex-M MPU
 * ports, not the standard ARMv7-M Cortex-M port.  Defaults to 8 if left
 * undefined. */
#define configTOTAL_MPU_REGIONS                                   8

/* configTEX_S_C_B_FLASH allows application writers to override the default
 * values for the for TEX, Shareable (S), Cacheable (C) and Bufferable (B) bits for
 * the MPU region covering Flash.  Defaults to 0x07UL (which means TEX=000, S=1,
 * C=1, B=1) if left undefined.  Only used by the FreeRTOS Cortex-M MPU ports, not
 * the standard ARMv7-M Cortex-M port. */
#define configTEX_S_C_B_FLASH                                     0x07UL

/* configTEX_S_C_B_SRAM allows application writers to override the default
 * values for the for TEX, Shareable (S), Cacheable (C) and Bufferable (B) bits for
 * the MPU region covering RAM. Defaults to 0x07UL (which means TEX=000, S=1, C=1,
 * B=1) if left undefined.  Only used by the FreeRTOS Cortex-M MPU ports, not
 * the standard ARMv7-M Cortex-M port. */
#define configTEX_S_C_B_SRAM                                      0x07UL

/* Set configENFORCE_SYSTEM_CALLS_FROM_KERNEL_ONLY to 0 to prevent any privilege
 * escalations originating from outside of the kernel code itself.  Set to 1 to
 * allow application tasks to raise privilege.  Defaults to 1 if left undefined.
 * Only used by the FreeRTOS Cortex-M MPU ports, not the standard ARMv7-M Cortex-M
 * port.*/
#define configENFORCE_SYSTEM_CALLS_FROM_KERNEL_ONLY               1

/* Set configALLOW_UNPRIVILEGED_CRITICAL_SECTIONS to 1 to allow unprivileged
 * tasks enter critical sections (effectively mask interrupts).  Set to 0 to
 * prevent unprivileged tasks entering critical sections.  Defaults to 1 if left
 * undefined.  Only used by the FreeRTOS Cortex-M MPU ports, not the standard
 * ARMv7-M Cortex-M port.*/
#define configALLOW_UNPRIVILEGED_CRITICAL_SECTIONS                0

/******************************************************************************/
/* ARMv8-M secure side port related definitions. ******************************/
/******************************************************************************/

/* secureconfigMAX_SECURE_CONTEXTS define the maximum number of tasks that can
 *  call into the secure side of an ARMv8-M chip.  Not used by any other ports. */
#define secureconfigMAX_SECURE_CONTEXTS        5

/* Defines the kernel provided implementation of
 * vApplicationGetIdleTaskMemory() and vApplicationGetTimerTaskMemory()
 * to provide the memory that is used by the Idle task and Timer task respectively.
 * The application can provide it's own implementation of
 * vApplicationGetIdleTaskMemory() and vApplicationGetTimerTaskMemory() by
 * setting configKERNEL_PROVIDED_STATIC_MEMORY to 0 or leaving it undefined. */
#define configKERNEL_PROVIDED_STATIC_MEMORY    1

/******************************************************************************/
/* Definitions that include or exclude functionality. *************************/
/******************************************************************************/

/* Set the following configUSE_* constants to 1 to include the named feature in
 * the build, or 0 to exclude the named feature from the build. */
#define configUSE_TASK_NOTIFICATIONS           1
#define configUSE_MUTEXES                      1
#define configUSE_RECURSIVE_MUTEXES            1
#define configUSE_COUNTING_SEMAPHORES          1
#define configUSE_QUEUE_SETS                   0
#define configUSE_APPLICATION_TASK_TAG         0

/* Set the following INCLUDE_* constants to 1 to incldue the named API function,
 * or 0 to exclude the named API function.  Most linkers will remove unused
 * functions even when the constant is 1. */
#define INCLUDE_vTaskPrioritySet               1
#define INCLUDE_uxTaskPriorityGet              1
#define INCLUDE_vTaskDelete                    1
#define INCLUDE_vTaskSuspend                   1
#define INCLUDE_xResumeFromISR                 1
#define INCLUDE_vTaskDelayUntil                1
#define INCLUDE_vTaskDelay                     1
#define INCLUDE_xTaskGetSchedulerState         1
#define INCLUDE_xTaskGetCurrentTaskHandle      1
#define INCLUDE_uxTaskGetStackHighWaterMark    0
#define INCLUDE_xTaskGetIdleTaskHandle         0
#define INCLUDE_eTaskGetState                  0
#define INCLUDE_xEventGroupSetBitFromISR       1
#define INCLUDE_xTimerPendFunctionCall         0
#define INCLUDE_xTaskAbortDelay                0
#define INCLUDE_xTaskGetHandle                 0
#define INCLUDE_xTaskResumeFromISR             1

#endif /* __FREERTOS_CONFIG_H__ */
