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

#ifndef MPU_PROTOTYPES_H
#define MPU_PROTOTYPES_H

#include <stddef.h>

/** Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from
 * redefining all the API functions to use the MPU wrappers. That should only
 *  be done when task.h is included from an application file. */
#ifndef MPU_WRAPPERS_INCLUDED_FROM_API_FILE
    #define MPU_WRAPPERS_INCLUDED_FROM_API_FILE
#endif /* MPU_WRAPPERS_INCLUDED_FROM_API_FILE */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"
#include "event_groups.h"
#include "stream_buffer.h"
#include "mpu_prototypes.h"
#include "mpu_syscall_numbers.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

typedef struct xTaskGenericNotifyParams
{
    TaskHandle_t xTaskToNotify;
    UBaseType_t uxIndexToNotify;
    uint32_t ulValue;
    eNotifyAction eAction;
    uint32_t * pulPreviousNotificationValue;
} xTaskGenericNotifyParams_t;

typedef struct xTaskGenericNotifyWaitParams
{
    UBaseType_t uxIndexToWaitOn;
    uint32_t ulBitsToClearOnEntry;
    uint32_t ulBitsToClearOnExit;
    uint32_t * pulNotificationValue;
    TickType_t xTicksToWait;
} xTaskGenericNotifyWaitParams_t;

typedef struct xTimerGenericCommandParams
{
    TimerHandle_t xTimer;
    BaseType_t xCommandID;
    TickType_t xOptionalValue;
    BaseType_t * pxHigherPriorityTaskWoken;
    TickType_t xTicksToWait;
} xTimerGenericCommandParams_t;

typedef struct xEventGroupWaitBitsParams
{
    EventGroupHandle_t xEventGroup;
    EventBits_t uxBitsToWaitFor;
    BaseType_t xClearOnExit;
    BaseType_t xWaitForAllBits;
    TickType_t xTicksToWait;
} xEventGroupWaitBitsParams_t;

/*-----------------------------------------------------------*/

extern TickType_t MPU_xTaskGetTickCount( void ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

UBaseType_t MPU_uxTaskGetNumberOfTasks( void ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

char * MPU_pcTaskGetName( TaskHandle_t xTaskToQuery ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

void MPU_vTaskSetTimeOutState( TimeOut_t * const pxTimeOut ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

BaseType_t MPU_xTaskCheckForTimeOut(
    TimeOut_t * const pxTimeOut,
    TickType_t * const pxTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

BaseType_t MPU_xQueueGenericSend(
    QueueHandle_t xQueue,
    const void * const pvItemToQueue,
    TickType_t xTicksToWait,
    const BaseType_t xCopyPosition
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

UBaseType_t MPU_uxQueueMessagesWaiting( const QueueHandle_t xQueue
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

UBaseType_t MPU_uxQueueSpacesAvailable( const QueueHandle_t xQueue
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

BaseType_t MPU_xQueueReceive(
    QueueHandle_t xQueue,
    void * const pvBuffer,
    TickType_t xTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;
/*-----------------------------------------------------------*/

BaseType_t MPU_xQueuePeek(
    QueueHandle_t xQueue,
    void * const pvBuffer,
    TickType_t xTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

BaseType_t MPU_xQueueSemaphoreTake( QueueHandle_t xQueue, TickType_t xTicksToWait )
    __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

size_t MPU_xStreamBufferSend(
    StreamBufferHandle_t xStreamBuffer,
    const void * pvTxData,
    size_t xDataLengthBytes,
    TickType_t xTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

size_t MPU_xStreamBufferReceive(
    StreamBufferHandle_t xStreamBuffer,
    void * pvRxData,
    size_t xBufferLengthBytes,
    TickType_t xTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

BaseType_t MPU_xStreamBufferIsFull( StreamBufferHandle_t xStreamBuffer
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

BaseType_t MPU_xStreamBufferIsEmpty( StreamBufferHandle_t xStreamBuffer
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

size_t MPU_xStreamBufferSpacesAvailable( StreamBufferHandle_t xStreamBuffer
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

size_t MPU_xStreamBufferBytesAvailable( StreamBufferHandle_t xStreamBuffer
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

BaseType_t MPU_xStreamBufferSetTriggerLevel(
    StreamBufferHandle_t xStreamBuffer,
    size_t xTriggerLevel
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

size_t MPU_xStreamBufferNextMessageLengthBytes( StreamBufferHandle_t xStreamBuffer
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

EventBits_t MPU_xEventGroupWaitBits(
    EventGroupHandle_t xEventGroup,
    const EventBits_t uxBitsToWaitFor,
    const BaseType_t xClearOnExit,
    const BaseType_t xWaitForAllBits,
    TickType_t xTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;
/*-----------------------------------------------------------*/

EventBits_t MPU_xEventGroupClearBits(
    EventGroupHandle_t xEventGroup,
    const EventBits_t uxBitsToClear
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

EventBits_t MPU_xEventGroupSetBits(
    EventGroupHandle_t xEventGroup,
    const EventBits_t uxBitsToSet
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

EventBits_t MPU_xEventGroupSync(
    EventGroupHandle_t xEventGroup,
    const EventBits_t uxBitsToSet,
    const EventBits_t uxBitsToWaitFor,
    TickType_t xTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

/*-----------------------------------------------------------*/

#if( INCLUDE_xTaskDelayUntil == 1 )

BaseType_t MPU_xTaskDelayUntil(
    TickType_t * const pxPreviousWakeTime,
    const TickType_t xTimeIncrement
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_xTaskDelayUntil == 1 ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_xTaskAbortDelay == 1 )

BaseType_t MPU_xTaskAbortDelay( TaskHandle_t xTask ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_xTaskAbortDelay == 1 ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_vTaskDelay == 1 )

void MPU_vTaskDelay( const TickType_t xTicksToDelay ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_vTaskDelay == 1 ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_uxTaskPriorityGet == 1 )

UBaseType_t MPU_uxTaskPriorityGet( const TaskHandle_t xTask ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_uxTaskPriorityGet == 1 ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_eTaskGetState == 1 )

eTaskState MPU_eTaskGetState( TaskHandle_t xTask ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_eTaskGetState == 1 ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_xTaskGetIdleTaskHandle == 1 )

TaskHandle_t MPU_xTaskGetIdleTaskHandle( void ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_xTaskGetIdleTaskHandle == 1 ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_vTaskSuspend == 1 )

void MPU_vTaskSuspend( TaskHandle_t xTaskToSuspend ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

void MPU_vTaskResume( TaskHandle_t xTaskToResume ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_vTaskSuspend == 1 ) */
/*-----------------------------------------------------------*/

#if( configGENERATE_RUN_TIME_STATS == 1 )
configRUN_TIME_COUNTER_TYPE MPU_ulTaskGetRunTimeCounter( const TaskHandle_t xTask
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

configRUN_TIME_COUNTER_TYPE MPU_ulTaskGetRunTimePercent( const TaskHandle_t xTask
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

    #if( INCLUDE_xTaskGetIdleTaskHandle == 1 ) )
configRUN_TIME_COUNTER_TYPE MPU_ulTaskGetIdleRunTimePercent( void
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;
configRUN_TIME_COUNTER_TYPE MPU_ulTaskGetIdleRunTimeCounter( void
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;
    #endif /*  ( INCLUDE_xTaskGetIdleTaskHandle == 1 ) */

#endif /* if ( ( configGENERATE_RUN_TIME_STATS == 1 ) */
/*-----------------------------------------------------------*/

#if( configUSE_APPLICATION_TASK_TAG == 1 )

void MPU_vTaskSetApplicationTaskTag(
    TaskHandle_t xTask,
    TaskHookFunction_t pxHookFunction
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

TaskHookFunction_t MPU_xTaskGetApplicationTaskTag( TaskHandle_t xTask
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

#endif /* if ( configUSE_APPLICATION_TASK_TAG == 1 ) */
/*-----------------------------------------------------------*/

#if( configNUM_THREAD_LOCAL_STORAGE_POINTERS != 0 )

void MPU_vTaskSetThreadLocalStoragePointer(
    TaskHandle_t xTaskToSet,
    BaseType_t xIndex,
    void * pvValue
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

void * MPU_pvTaskGetThreadLocalStoragePointer(
    TaskHandle_t xTaskToQuery,
    BaseType_t xIndex
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

#endif /* if ( configNUM_THREAD_LOCAL_STORAGE_POINTERS != 0 ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_uxTaskGetStackHighWaterMark == 1 )

UBaseType_t MPU_uxTaskGetStackHighWaterMark( TaskHandle_t xTask ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_uxTaskGetStackHighWaterMark == 1 ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_uxTaskGetStackHighWaterMark2 == 1 )

configSTACK_DEPTH_TYPE MPU_uxTaskGetStackHighWaterMark2( TaskHandle_t xTask
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_uxTaskGetStackHighWaterMark2 == 1 ) */
/*-----------------------------------------------------------*/

#if( ( INCLUDE_xTaskGetCurrentTaskHandle == 1 ) || ( configUSE_MUTEXES == 1 ) )

TaskHandle_t MPU_xTaskGetCurrentTaskHandle( void ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( ( INCLUDE_xTaskGetCurrentTaskHandle == 1 ) || ( configUSE_MUTEXES == 1 ) \
          ) */
/*-----------------------------------------------------------*/

#if( INCLUDE_xTaskGetSchedulerState == 1 )

BaseType_t MPU_xTaskGetSchedulerState( void ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( INCLUDE_xTaskGetSchedulerState == 1 ) */
/*-----------------------------------------------------------*/

#if( configUSE_TRACE_FACILITY == 1 )

void MPU_vTaskGetInfo(
    TaskHandle_t xTask,
    TaskStatus_t * pxTaskStatus,
    BaseType_t xGetFreeStackSpace,
    eTaskState eState
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

UBaseType_t MPU_uxTaskGetSystemState(
    TaskStatus_t * const pxTaskStatusArray,
    const UBaseType_t uxArraySize,
    configRUN_TIME_COUNTER_TYPE * const pulTotalRunTime
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

UBaseType_t MPU_uxEventGroupGetNumber( void * xEventGroup ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

void MPU_vEventGroupSetNumber( void * xEventGroup, UBaseType_t uxEventGroupNumber )
    __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

#endif /*( configUSE_TRACE_FACILITY == 1 )*/
/*-----------------------------------------------------------*/

#if( configUSE_TASK_NOTIFICATIONS == 1 )

BaseType_t MPU_xTaskGenericNotifyEntry( const xTaskGenericNotifyParams_t * pxParams
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

BaseType_t MPU_xTaskGenericNotifyWaitEntry( const xTaskGenericNotifyWaitParams_t * pxParams
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

uint32_t MPU_ulTaskGenericNotifyTake(
    UBaseType_t uxIndexToWaitOn,
    BaseType_t xClearCountOnExit,
    TickType_t xTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

BaseType_t MPU_xTaskGenericNotifyStateClear(
    TaskHandle_t xTask,
    UBaseType_t uxIndexToClear
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

uint32_t MPU_ulTaskGenericNotifyValueClear(
    TaskHandle_t xTask,
    UBaseType_t uxIndexToClear,
    uint32_t ulBitsToClear
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

#endif /* if ( configUSE_TASK_NOTIFICATIONS == 1 ) */
/*-----------------------------------------------------------*/

#if( configUSE_RECURSIVE_MUTEXES == 1 )

BaseType_t MPU_xQueueTakeMutexRecursive( QueueHandle_t xMutex, TickType_t xTicksToWait )
    __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

BaseType_t MPU_xQueueGiveMutexRecursive( QueueHandle_t pxMutex ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

    #if( INCLUDE_xSemaphoreGetMutexHolder == 1 )

TaskHandle_t MPU_xQueueGetMutexHolder( QueueHandle_t xSemaphore ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

    #endif /* ( INCLUDE_xSemaphoreGetMutexHolder == 1 ) ) */

#endif /* if ( configUSE_RECURSIVE_MUTEXES == 1 ) */
/*-----------------------------------------------------------*/

#if( configUSE_QUEUE_SETS == 1 )

QueueSetMemberHandle_t MPU_xQueueSelectFromSet(
    QueueSetHandle_t xQueueSet,
    const TickType_t xTicksToWait
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

BaseType_t MPU_xQueueAddToSet(
    QueueSetMemberHandle_t xQueueOrSemaphore,
    QueueSetHandle_t xQueueSet
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

#endif /* if ( configUSE_QUEUE_SETS == 1 ) */
/*-----------------------------------------------------------*/

#if( configQUEUE_REGISTRY_SIZE > 0 )

void MPU_vQueueAddToRegistry( QueueHandle_t xQueue, const char * pcName )
    __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

void MPU_vQueueUnregisterQueue( QueueHandle_t xQueue ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

const char * MPU_pcQueueGetName( QueueHandle_t xQueue ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( configQUEUE_REGISTRY_SIZE > 0 ) */
/*-----------------------------------------------------------*/

#if( configUSE_TIMERS == 1 )

void * MPU_pvTimerGetTimerID( const TimerHandle_t xTimer ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

void MPU_vTimerSetTimerID( TimerHandle_t xTimer, void * pvNewID ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

BaseType_t MPU_xTimerIsTimerActive( TimerHandle_t xTimer ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

TaskHandle_t MPU_xTimerGetTimerDaemonTaskHandle( void ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

BaseType_t MPU_xTimerGenericCommandEntry( const xTimerGenericCommandParams_t * pxParams
) __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

const char * MPU_pcTimerGetName( TimerHandle_t xTimer ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

void MPU_vTimerSetReloadMode( TimerHandle_t xTimer, const BaseType_t uxAutoReload )
    __attribute__( ( naked ) ) FREERTOS_SYSTEM_CALL;

BaseType_t MPU_xTimerGetReloadMode( TimerHandle_t xTimer ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

UBaseType_t MPU_uxTimerGetReloadMode( TimerHandle_t xTimer ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

TickType_t MPU_xTimerGetPeriod( TimerHandle_t xTimer ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

TickType_t MPU_xTimerGetExpiryTime( TimerHandle_t xTimer ) __attribute__( ( naked )
) FREERTOS_SYSTEM_CALL;

#endif /* if ( configUSE_TIMERS == 1 ) */
/*-----------------------------------------------------------*/

#endif /* MPU_PROTOTYPES_H */
