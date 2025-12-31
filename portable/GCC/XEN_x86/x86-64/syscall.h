/* syscall
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

#ifndef _SYSCALL_H_
#define _SYSCALL_H_
#include "FreeRTOS.h"
#include "event_groups.h"
#include "stream_buffer.h"
#include "task.h"
#include "queue.h"
#include "timers.h"


void syscall_writec(char val);
BaseType_t syscall_xTaskGetTickCount(void);
BaseType_t syscall_xTaskDelayUntil( TickType_t * const pxPreviousWakeTime,
                                TickType_t xTimeIncrement);
BaseType_t syscall_xQueueGenericSend( QueueHandle_t xQueue,
                                  const void * const pvItemToQueue,
                                  TickType_t xTicksToWait,
                                  BaseType_t xCopyPosition );
BaseType_t syscall_xQueueReceive( QueueHandle_t pxQueue,
                              void * const pvBuffer,
                              TickType_t xTicksToWait );
BaseType_t syscall_xTimerGenericCommandFromTask( TimerHandle_t xTimer,
                                             const BaseType_t xCommandID,
                                             const TickType_t xOptionalValue,
                                             BaseType_t * const pxHigherPriorityTaskWoken,
                                             const TickType_t xTicksToWait );
QueueHandle_t syscall_xQueueGenericCreate( UBaseType_t uxQueueLength,
                                       UBaseType_t uxItemSize,
                                       uint8_t ucQueueType );
BaseType_t syscall_xTaskCreate( TaskFunction_t pvTaskCode,
                            const char * const pcName,
                            const configSTACK_DEPTH_TYPE uxStackDepth,
                            void * pvParameters,
                            UBaseType_t uxPriority,
                            TaskHandle_t * pxCreatedTask );
void syscall_vTaskDelete( TaskHandle_t pxTaskToDelete );
void syscall_vTaskDelay( TickType_t xTicksToDelay );
UBaseType_t syscall_uxTaskPriorityGet( const TaskHandle_t pxTask );
void syscall_vTaskPrioritySet( TaskHandle_t pxTask,
                           UBaseType_t uxNewPriority );
eTaskState syscall_eTaskGetState( TaskHandle_t pxTask );
void syscall_vTaskGetInfo( TaskHandle_t xTask,
                       TaskStatus_t * pxTaskStatus,
                       BaseType_t xGetFreeStackSpace,
                       eTaskState eState );
void syscall_vTaskSuspend( TaskHandle_t pxTaskToSuspend );
void syscall_vTaskResume( TaskHandle_t pxTaskToResume );
UBaseType_t syscall_uxTaskGetNumberOfTasks( void );
UBaseType_t syscall_uxTaskGetSystemState( TaskStatus_t * pxTaskStatusArray,
                                      UBaseType_t uxArraySize,
                                      configRUN_TIME_COUNTER_TYPE * pulTotalRunTime );
TaskHandle_t syscall_xTaskGetCurrentTaskHandle( void );
BaseType_t syscall_xTaskGetSchedulerState( void );
void syscall_vTaskSetTimeOutState( TimeOut_t * const pxTimeOut );
BaseType_t syscall_xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut,
                             TickType_t * const pxTicksToWait );
BaseType_t syscall_xTaskGenericNotify( TaskHandle_t xTaskToNotify,
                                   UBaseType_t uxIndexToNotify,
                                   uint32_t ulValue,
                                   eNotifyAction eAction,
                                   uint32_t * pulPreviousNotificationValue );
BaseType_t syscall_xTaskGenericNotifyWait( UBaseType_t uxIndexToWaitOn,
                                       uint32_t ulBitsToClearOnEntry,
                                       uint32_t ulBitsToClearOnExit,
                                       uint32_t * pulNotificationValue,
                                       TickType_t xTicksToWait );
uint32_t syscall_ulTaskGenericNotifyTake( UBaseType_t uxIndexToWaitOn,
                                      BaseType_t xClearCountOnExit,
                                      TickType_t xTicksToWait );
BaseType_t syscall_xTaskGenericNotifyStateClear( TaskHandle_t xTask,
                                             UBaseType_t uxIndexToClear );
uint32_t syscall_ulTaskGenericNotifyValueClear( TaskHandle_t xTask,
                                            UBaseType_t uxIndexToClear,
                                            uint32_t ulBitsToClear );
BaseType_t syscall_xQueueGenericReset( QueueHandle_t pxQueue,
                               BaseType_t xNewQueue );
UBaseType_t syscall_uxQueueMessagesWaiting( const QueueHandle_t pxQueue );
UBaseType_t syscall_uxQueueSpacesAvailable( const QueueHandle_t xQueue );
BaseType_t syscall_xQueuePeek( QueueHandle_t xQueue,
                       void * const pvBuffer,
                       TickType_t xTicksToWait );
BaseType_t syscall_xQueueSemaphoreTake( QueueHandle_t xQueue,
                                    TickType_t xTicksToWait );
QueueHandle_t syscall_xQueueCreateMutex( const uint8_t ucQueueType );
QueueHandle_t syscall_xQueueCreateCountingSemaphore( UBaseType_t uxCountValue,
                                                 UBaseType_t uxInitialCount );
BaseType_t syscall_xQueueTakeMutexRecursive( QueueHandle_t xMutex,
                                         TickType_t xBlockTime );
BaseType_t syscall_xQueueGiveMutexRecursive( QueueHandle_t xMutex );
QueueSetHandle_t syscall_xQueueCreateSet( UBaseType_t uxEventQueueLength );
QueueSetMemberHandle_t syscall_xQueueSelectFromSet( QueueSetHandle_t xQueueSet,
                                                TickType_t xBlockTimeTicks );
BaseType_t syscall_xQueueAddToSet( QueueSetMemberHandle_t xQueueOrSemaphore,
                               QueueSetHandle_t xQueueSet );
BaseType_t syscall_xQueueRemoveFromSet( QueueSetMemberHandle_t xQueueOrSemaphore,
                                    QueueSetHandle_t xQueueSet );
void syscall_vQueueAddToRegistry( QueueHandle_t xQueue,
                              const char * pcName );
void syscall_vQueueUnregisterQueue( QueueHandle_t xQueue );
const char * syscall_pcQueueGetName( QueueHandle_t xQueue );
void syscall_vQueueDelete( QueueHandle_t xQueue );
void * syscall_pvTimerGetTimerID( const TimerHandle_t xTimer );
void syscall_vTimerSetTimerID( TimerHandle_t xTimer,
                           void * pvNewID );
BaseType_t syscall_xTimerIsTimerActive( TimerHandle_t xTimer );
TaskHandle_t syscall_xTimerGetTimerDaemonTaskHandle( void );
void syscall_vTimerSetReloadMode( TimerHandle_t xTimer,
                              const BaseType_t uxAutoReload );
UBaseType_t syscall_uxTimerGetReloadMode( TimerHandle_t xTimer );
const char * syscall_pcTimerGetName( TimerHandle_t xTimer );
TickType_t syscall_xTimerGetPeriod( TimerHandle_t xTimer );
TickType_t syscall_xTimerGetExpiryTime( TimerHandle_t xTimer );
void syscall_vTaskListTasks( char * pcWriteBuffer,
                         size_t uxBufferLength );
void syscall_vTaskSuspendAll( void );
BaseType_t syscall_xTaskResumeAll( void );
BaseType_t syscall_xTaskAbortDelay( TaskHandle_t xTask );TaskHandle_t syscall_xTaskGetHandle( const char * pcNameToQuery ); 
TaskHandle_t syscall_xTaskGetHandle( const char * pcNameToQuery ); 
EventGroupHandle_t syscall_xEventGroupCreate( void ); /* FREERTOS_SYSTEM_CALL */
 EventBits_t syscall_xEventGroupWaitBits( EventGroupHandle_t xEventGroup,
                                             const EventBits_t uxBitsToWaitFor,
                                             const BaseType_t xClearOnExit,
                                             const BaseType_t xWaitForAllBits,
                                             TickType_t xTicksToWait ); /* FREERTOS_SYSTEM_CALL */
 void syscall_vEventGroupDelete( EventGroupHandle_t xEventGroup ); /* FREERTOS_SYSTEM_CALL */
StreamBufferHandle_t syscall_xStreamBufferGenericCreate( size_t xBufferSizeBytes,
                                                             size_t xTriggerLevelBytes,
                                                             BaseType_t xStreamBufferType,
                                                             StreamBufferCallbackFunction_t pxSendCompletedCallback,
                                                             StreamBufferCallbackFunction_t pxReceiveCompletedCallback ); /* FREERTOS_SYSTEM_CALL */
size_t syscall_xStreamBufferReceive( StreamBufferHandle_t xStreamBuffer,
                                         void * pvRxData,
                                         size_t xBufferLengthBytes,
                                         TickType_t xTicksToWait ); /* FREERTOS_SYSTEM_CALL */
void syscall_vStreamBufferDelete( StreamBufferHandle_t xStreamBuffer ); /* FREERTOS_SYSTEM_CALL */
TaskHandle_t syscall_xQueueGetMutexHolder( QueueHandle_t xSemaphore ); /* FREERTOS_SYSTEM_CALL */
EventBits_t syscall_xEventGroupSync( EventGroupHandle_t xEventGroup,
                                         const EventBits_t uxBitsToSet,
                                         const EventBits_t uxBitsToWaitFor,
                                         TickType_t xTicksToWait ); /* FREERTOS_SYSTEM_CALL */
EventBits_t syscall_xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                            const EventBits_t uxBitsToSet ); /* FREERTOS_SYSTEM_CALL */
EventBits_t syscall_xEventGroupClearBits( EventGroupHandle_t xEventGroup,
                                              const EventBits_t uxBitsToClear ); /* FREERTOS_SYSTEM_CALL */
size_t syscall_xStreamBufferSend( StreamBufferHandle_t xStreamBuffer,
                                      const void * pvTxData,
                                      size_t xDataLengthBytes,
                                      TickType_t xTicksToWait ); /* FREERTOS_SYSTEM_CALL */
BaseType_t syscall_xStreamBufferIsEmpty( StreamBufferHandle_t xStreamBuffer ); /* FREERTOS_SYSTEM_CALL */
size_t syscall_xStreamBufferNextMessageLengthBytes( StreamBufferHandle_t xStreamBuffer ); /* FREERTOS_SYSTEM_CALL */
BaseType_t syscall_xStreamBufferIsFull( StreamBufferHandle_t xStreamBuffer ); /* FREERTOS_SYSTEM_CALL */
 size_t syscall_xStreamBufferSpacesAvailable( StreamBufferHandle_t xStreamBuffer ); /* FREERTOS_SYSTEM_CALL */
 BaseType_t syscall_xStreamBufferReset( StreamBufferHandle_t xStreamBuffer ); /* FREERTOS_SYSTEM_CALL */
size_t syscall_xStreamBufferBytesAvailable( StreamBufferHandle_t xStreamBuffer ); /* FREERTOS_SYSTEM_CALL */


#endif
