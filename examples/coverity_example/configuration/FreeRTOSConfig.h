/*
 * FreeRTOS <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 */


#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

#define mtCOVERAGE_TEST_MARKER()    /* _asm will be reported by coverity */

#define configRUN_TIME_COUNTER_TYPE    uint32_t

/*-----------------------------------------------------------
* Application specific definitions.
*
* These definitions should be adjusted for your particular hardware and
* application requirements.
*
* THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
* FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.  See
* http://www.freertos.org/a00110.html
*----------------------------------------------------------*/

#define configNUMBER_OF_CORES                                     1U
#define configUSE_MUTEXES                                         1
#define configUSE_PASSIVE_IDLE_HOOK                               0
#define configUSE_PREEMPTION                                      1
#define configUSE_PORT_OPTIMISED_TASK_SELECTION                   0
#define configUSE_TRACE_FACILITY                                  1
#define configGENERATE_RUN_TIME_STATS                             0
#define configSUPPORT_DYNAMIC_ALLOCATION                          1
#define configSUPPORT_STATIC_ALLOCATION                           1
#define configUSE_TASK_PREEMPTION_DISABLE                         0
#define INCLUDE_vTaskDelete                                       1
#define INCLUDE_xTaskDelayUntil                                   1
#define INCLUDE_eTaskGetState                                     1
#define INCLUDE_xTaskAbortDelay                                   1
#define INCLUDE_vTaskPrioritySet                                  1
#define INCLUDE_vTaskSuspend                                      1
#define INCLUDE_xTaskGetCurrentTaskHandle                         1
#define INCLUDE_xTaskGetIdleTaskHandle                            1
#define configUSE_TIME_SLICING                                    1
#define configRUN_MULTIPLE_PRIORITIES                             0

#define configUSE_TICKLESS_IDLE                                   1
#define configCPU_CLOCK_HZ                                        60000000
#define configSYSTICK_CLOCK_HZ                                    1000000
#define configTICK_RATE_HZ                                        ( 1000U )
#define configMAX_PRIORITIES                                      ( 7U )
#define configMINIMAL_STACK_SIZE                                  ( ( configSTACK_DEPTH_TYPE ) 70U )
#define configMAX_TASK_NAME_LEN                                   ( 5U )
#define configUSE_16_BIT_TICKS                                    0
#define configIDLE_SHOULD_YIELD                                   1
#define configUSE_TASK_NOTIFICATIONS                              1
#define configTASK_NOTIFICATION_ARRAY_ENTRIES                     3
#define configUSE_RECURSIVE_MUTEXES                               1
#define configUSE_COUNTING_SEMAPHORES                             1
#define configUSE_ALTERNATIVE_API                                 0
#define configQUEUE_REGISTRY_SIZE                                 20
#define configUSE_QUEUE_SETS                                      1
#define configUSE_NEWLIB_REENTRANT                                0
#define configENABLE_BACKWARD_COMPATIBILITY                       1
#define configNUM_THREAD_LOCAL_STORAGE_POINTERS                   5
#define configUSE_MINI_LIST_ITEM                                  0
#define configSTACK_DEPTH_TYPE                                    uint16_t
#define configMESSAGE_BUFFER_LENGTH_TYPE                          size_t
#define configHEAP_CLEAR_MEMORY_ON_FREE                           1
#define configINITIAL_TICK_COUNT                                  ( ( TickType_t ) 0 )
#define configEXPECTED_IDLE_TIME_BEFORE_SLEEP                     2U

/* Memory allocation related definitions. */
#define configTOTAL_HEAP_SIZE                                     ( ( size_t ) ( 52 * 1024 ) )
#define configAPPLICATION_ALLOCATED_HEAP                          0
#define configSTACK_ALLOCATION_FROM_SEPARATE_HEAP                 0

/* Hook function related definitions. */
#define configUSE_IDLE_HOOK                                       0
#define configUSE_TICK_HOOK                                       0
#define configCHECK_FOR_STACK_OVERFLOW                            0
#define configUSE_MALLOC_FAILED_HOOK                              0
#define configUSE_DAEMON_TASK_STARTUP_HOOK                        0
#define configUSE_SB_COMPLETED_CALLBACK                           1

/* Run time and task stats gathering related definitions. */
#define configUSE_STATS_FORMATTING_FUNCTIONS                      1

/* Software timer related definitions. */
#define configUSE_TIMERS                                          1
#define configTIMER_TASK_PRIORITY                                 ( 6U )
#define configTIMER_QUEUE_LENGTH                                  20
#define configTIMER_TASK_STACK_DEPTH                              ( configMINIMAL_STACK_SIZE * 2U )

/* Interrupt nesting behaviour configuration. */
#define configKERNEL_INTERRUPT_PRIORITY                           ( configMAX_PRIORITIES - 1U )
#define configMAX_SYSCALL_INTERRUPT_PRIORITY                      ( configMAX_PRIORITIES - 1U )
#define configMAX_API_CALL_INTERRUPT_PRIORITY                     ( configMAX_PRIORITIES - 1U )

/* FreeRTOS MPU specific definitions. */
#define configINCLUDE_APPLICATION_DEFINED_PRIVILEGED_FUNCTIONS    0
#define configTOTAL_MPU_REGIONS                                   8      /* Default value. */
#define configTEX_S_C_B_FLASH                                     0x07UL /* Default value. */
#define configTEX_S_C_B_SRAM                                      0x07UL /* Default value. */
#define configENFORCE_SYSTEM_CALLS_FROM_KERNEL_ONLY               1
#define configALLOW_UNPRIVILEGED_CRITICAL_SECTIONS                1
#define configENABLE_ERRATA_837070_WORKAROUND                     1

/* ARMv8-M secure side port related definitions. */
#define secureconfigMAX_SECURE_CONTEXTS                           5

/* Optional functions - most linkers will remove unused functions anyway. */
#define INCLUDE_uxTaskPriorityGet                                 1
#define INCLUDE_xResumeFromISR                                    1
#define INCLUDE_vTaskDelay                                        1
#define INCLUDE_xTaskGetSchedulerState                            1
#define INCLUDE_uxTaskGetStackHighWaterMark                       1
#define INCLUDE_uxTaskGetStackHighWaterMark2                      1
#define INCLUDE_xEventGroupSetBitFromISR                          1
#define INCLUDE_xTimerPendFunctionCall                            1
#define INCLUDE_xTaskGetHandle                                    1
#define INCLUDE_xTaskResumeFromISR                                1
#define INCLUDE_vTaskCleanUpResources                             1
#define INCLUDE_xTimerGetTimerDaemonTaskHandle                    1
#define INCLUDE_xSemaphoreGetMutexHolder                          1

/* Run time stats gathering configuration options. */
#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS()

#define configKERNEL_PROVIDED_STATIC_MEMORY    1

#endif /* FREERTOS_CONFIG_H */
