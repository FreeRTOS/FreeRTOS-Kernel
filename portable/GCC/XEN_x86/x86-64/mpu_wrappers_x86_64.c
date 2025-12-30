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
 * Implementation of the wrapper functions used to raise the processor privilege
 * before calling a standard FreeRTOS API function.
 */
/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
 * all the API functions to use the MPU wrappers.  That should only be done when
 * task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE
/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"
#include "event_groups.h"
#include "stream_buffer.h"
#include "mpu_prototypes.h"
#include "syscall.h"
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskGetTickCount( void )
{
    TickType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTaskGetTickCount();
    }
    else
    {
        xReturn = xTaskGetTickCount();
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskDelayUntil( TickType_t * const pxPreviousWakeTime,
                                TickType_t xTimeIncrement )
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_xTaskDelayUntil(pxPreviousWakeTime, xTimeIncrement);
    }
    else
    {
        xReturn = xTaskDelayUntil( pxPreviousWakeTime, xTimeIncrement );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueueGenericSend( QueueHandle_t xQueue,
                                  const void * const pvItemToQueue,
                                  TickType_t xTicksToWait,
                                  BaseType_t xCopyPosition )
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueueGenericSend( xQueue, pvItemToQueue, xTicksToWait, xCopyPosition );
    }
    else
    {
        xReturn = xQueueGenericSend( xQueue, pvItemToQueue, xTicksToWait, xCopyPosition );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueueReceive( QueueHandle_t pxQueue,
                              void * const pvBuffer,
                              TickType_t xTicksToWait )
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueueReceive( pxQueue, pvBuffer, xTicksToWait );
    }
    else
    {
        xReturn = xQueueReceive( pxQueue, pvBuffer, xTicksToWait );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTimerGenericCommandFromTask( TimerHandle_t xTimer,
                                             const BaseType_t xCommandID,
                                             const TickType_t xOptionalValue,
                                             BaseType_t * const pxHigherPriorityTaskWoken,
                                             const TickType_t xTicksToWait )
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTimerGenericCommandFromTask( xTimer, xCommandID, xOptionalValue, pxHigherPriorityTaskWoken, xTicksToWait );
    }
    else
    {
        xReturn = xTimerGenericCommandFromTask( xTimer, xCommandID, xOptionalValue, pxHigherPriorityTaskWoken, xTicksToWait );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
QueueHandle_t MPU_xQueueGenericCreate( UBaseType_t uxQueueLength,
                                       UBaseType_t uxItemSize,
                                       uint8_t ucQueueType )
{
    return xQueueGenericCreate( uxQueueLength, uxItemSize, ucQueueType );
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskCreate( TaskFunction_t pvTaskCode,
                            const char * const pcName,
                            const configSTACK_DEPTH_TYPE uxStackDepth,
                            void * pvParameters,
                            UBaseType_t uxPriority,
                            TaskHandle_t * pxCreatedTask )
{
    /* This API can only be used to create priviledged tasks */
    return xTaskCreate( pvTaskCode, pcName, uxStackDepth, pvParameters, uxPriority|portPRIVILEGE_BIT, pxCreatedTask );
}
/*-----------------------------------------------------------*/
void MPU_vTaskDelete( TaskHandle_t pxTaskToDelete )
{
    vTaskDelete( pxTaskToDelete );
}
/*-----------------------------------------------------------*/
void MPU_vTaskDelay( TickType_t xTicksToDelay ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vTaskDelay( xTicksToDelay );
    }
    else
    {
        vTaskDelay( xTicksToDelay );
    }
}
/*-----------------------------------------------------------*/
UBaseType_t MPU_uxTaskPriorityGet( const TaskHandle_t pxTask ) 
{
    UBaseType_t uxReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        uxReturn = syscall_uxTaskPriorityGet( pxTask );
    }
    else
    {
        uxReturn = uxTaskPriorityGet( pxTask );
    }
    return uxReturn;
}
/*-----------------------------------------------------------*/
void MPU_vTaskPrioritySet( TaskHandle_t pxTask,
                           UBaseType_t uxNewPriority ) 
{
     vTaskPrioritySet( pxTask, uxNewPriority );
}
/*-----------------------------------------------------------*/
eTaskState MPU_eTaskGetState( TaskHandle_t pxTask ) 
{
    eTaskState eReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        eReturn = syscall_eTaskGetState( pxTask );
    }
    else
    {
        eReturn = eTaskGetState( pxTask );
    }
    return eReturn;
}
/*-----------------------------------------------------------*/
void MPU_vTaskGetInfo( TaskHandle_t xTask,
                       TaskStatus_t * pxTaskStatus,
                       BaseType_t xGetFreeStackSpace,
                       eTaskState eState ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vTaskGetInfo( xTask, pxTaskStatus, xGetFreeStackSpace, eState );
    }
    else
    {
        vTaskGetInfo( xTask, pxTaskStatus, xGetFreeStackSpace, eState );
    }
}
/*-----------------------------------------------------------*/
void MPU_vTaskSuspend( TaskHandle_t pxTaskToSuspend ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vTaskSuspend( pxTaskToSuspend );
    }
    else
    {
        vTaskSuspend( pxTaskToSuspend );
    }
}
/*-----------------------------------------------------------*/
void MPU_vTaskResume( TaskHandle_t pxTaskToResume ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vTaskResume( pxTaskToResume );
    }
    else
    {
        vTaskResume( pxTaskToResume );
    }
}
/*-----------------------------------------------------------*/
UBaseType_t MPU_uxTaskGetNumberOfTasks( void ) 
{
    UBaseType_t uxReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        uxReturn = syscall_uxTaskGetNumberOfTasks();
    }
    else
    {
        uxReturn = uxTaskGetNumberOfTasks();
    }
    return uxReturn;
}
/*-----------------------------------------------------------*/
UBaseType_t MPU_uxTaskGetSystemState( TaskStatus_t * pxTaskStatusArray,
                                      UBaseType_t uxArraySize,
                                      configRUN_TIME_COUNTER_TYPE * pulTotalRunTime ) 
{
    UBaseType_t uxReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        uxReturn = syscall_uxTaskGetSystemState( pxTaskStatusArray, uxArraySize, pulTotalRunTime );
    }
    else
    {
        uxReturn = uxTaskGetSystemState( pxTaskStatusArray, uxArraySize, pulTotalRunTime );
    }
    return uxReturn;
}
/*-----------------------------------------------------------*/
TaskHandle_t MPU_xTaskGetCurrentTaskHandle( void ) 
{
    TaskHandle_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTaskGetCurrentTaskHandle();
    }
    else
    {
        xReturn = xTaskGetCurrentTaskHandle();
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskGetSchedulerState( void ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTaskGetSchedulerState();
    }
    else
    {
        xReturn = xTaskGetSchedulerState();
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
void MPU_vTaskSetTimeOutState( TimeOut_t * const pxTimeOut ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vTaskSetTimeOutState( pxTimeOut );
    }
    else
    {
        vTaskSetTimeOutState( pxTimeOut );
    }
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskCheckForTimeOut( TimeOut_t * const pxTimeOut,
                             TickType_t * const pxTicksToWait ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTaskCheckForTimeOut( pxTimeOut, pxTicksToWait );
    }
    else
    {
        xReturn = xTaskCheckForTimeOut( pxTimeOut, pxTicksToWait );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskGenericNotify( TaskHandle_t xTaskToNotify,
                                   UBaseType_t uxIndexToNotify,
                                   uint32_t ulValue,
                                   eNotifyAction eAction,
                                   uint32_t * pulPreviousNotificationValue ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTaskGenericNotify( xTaskToNotify, uxIndexToNotify, ulValue, eAction, pulPreviousNotificationValue );
    }
    else
    {
        xReturn = xTaskGenericNotify( xTaskToNotify, uxIndexToNotify, ulValue, eAction, pulPreviousNotificationValue );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskGenericNotifyWait( UBaseType_t uxIndexToWaitOn,
                                       uint32_t ulBitsToClearOnEntry,
                                       uint32_t ulBitsToClearOnExit,
                                       uint32_t * pulNotificationValue,
                                       TickType_t xTicksToWait ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTaskGenericNotifyWait( uxIndexToWaitOn, ulBitsToClearOnEntry, ulBitsToClearOnExit, pulNotificationValue, xTicksToWait );
    }
    else
    {
        xReturn = xTaskGenericNotifyWait( uxIndexToWaitOn, ulBitsToClearOnEntry, ulBitsToClearOnExit, pulNotificationValue, xTicksToWait );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
uint32_t MPU_ulTaskGenericNotifyTake( UBaseType_t uxIndexToWaitOn,
                                      BaseType_t xClearCountOnExit,
                                      TickType_t xTicksToWait ) 
{
    uint32_t ulReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        ulReturn = syscall_ulTaskGenericNotifyTake( uxIndexToWaitOn, xClearCountOnExit, xTicksToWait );
    }
    else
    {
        ulReturn = ulTaskGenericNotifyTake( uxIndexToWaitOn, xClearCountOnExit, xTicksToWait );
    }
    return ulReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskGenericNotifyStateClear( TaskHandle_t xTask,
                                             UBaseType_t uxIndexToClear ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTaskGenericNotifyStateClear( xTask, uxIndexToClear );
    }
    else
    {
        xReturn = xTaskGenericNotifyStateClear( xTask, uxIndexToClear );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
uint32_t MPU_ulTaskGenericNotifyValueClear( TaskHandle_t xTask,
                                            UBaseType_t uxIndexToClear,
                                            uint32_t ulBitsToClear ) 
{
    uint32_t ulReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        ulReturn = syscall_ulTaskGenericNotifyValueClear( xTask, uxIndexToClear, ulBitsToClear );
    }
    else
    {
        ulReturn = ulTaskGenericNotifyValueClear( xTask, uxIndexToClear, ulBitsToClear );
    }
    return ulReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueueGenericReset( QueueHandle_t pxQueue,
                               BaseType_t xNewQueue ) 
{
    return xQueueGenericReset( pxQueue, xNewQueue );
}
/*-----------------------------------------------------------*/
UBaseType_t MPU_uxQueueMessagesWaiting( const QueueHandle_t pxQueue ) 
{
    uint32_t uxReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        uxReturn = syscall_uxQueueMessagesWaiting( pxQueue );
    }
    else
    {
        uxReturn = uxQueueMessagesWaiting( pxQueue );
    }
    return uxReturn;
}
/*-----------------------------------------------------------*/
UBaseType_t MPU_uxQueueSpacesAvailable( const QueueHandle_t xQueue ) 
{
    UBaseType_t uxReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        uxReturn = syscall_uxQueueSpacesAvailable( xQueue );
    }
    else
    {
        uxReturn = uxQueueSpacesAvailable( xQueue );
    }

    return uxReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueuePeek( QueueHandle_t xQueue,
                       void * const pvBuffer,
                       TickType_t xTicksToWait ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueuePeek( xQueue, pvBuffer, xTicksToWait );
    }
    else
    {
        xReturn = xQueuePeek( xQueue, pvBuffer, xTicksToWait );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueueSemaphoreTake( QueueHandle_t xQueue,
                                    TickType_t xTicksToWait ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueueSemaphoreTake( xQueue, xTicksToWait );
    }
    else
    {
        xReturn = xQueueSemaphoreTake( xQueue, xTicksToWait );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
QueueHandle_t MPU_xQueueCreateMutex( const uint8_t ucQueueType ) 
{
    return xQueueCreateMutex( ucQueueType );
}
/*-----------------------------------------------------------*/
QueueHandle_t MPU_xQueueCreateCountingSemaphore( UBaseType_t uxCountValue,
                                                 UBaseType_t uxInitialCount ) 
{
    return xQueueCreateCountingSemaphore( uxCountValue, uxInitialCount );
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueueTakeMutexRecursive( QueueHandle_t xMutex,
                                         TickType_t xBlockTime ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueueTakeMutexRecursive( xMutex, xBlockTime );
    }
    else
    {
        xReturn = xQueueTakeMutexRecursive( xMutex, xBlockTime );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueueGiveMutexRecursive( QueueHandle_t xMutex ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueueGiveMutexRecursive( xMutex );
    }
    else
    {
        xReturn = xQueueGiveMutexRecursive( xMutex );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
QueueSetHandle_t MPU_xQueueCreateSet( UBaseType_t uxEventQueueLength ) 
{
    return xQueueCreateSet( uxEventQueueLength );
}
/*-----------------------------------------------------------*/
QueueSetMemberHandle_t MPU_xQueueSelectFromSet( QueueSetHandle_t xQueueSet,
                                                TickType_t xBlockTimeTicks ) 
{
    QueueSetMemberHandle_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueueSelectFromSet( xQueueSet, xBlockTimeTicks );
    }
    else
    {
        xReturn = xQueueSelectFromSet( xQueueSet, xBlockTimeTicks );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueueAddToSet( QueueSetMemberHandle_t xQueueOrSemaphore,
                               QueueSetHandle_t xQueueSet ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueueAddToSet( xQueueOrSemaphore, xQueueSet );
    }
    else
    {
        xReturn = xQueueAddToSet( xQueueOrSemaphore, xQueueSet );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xQueueRemoveFromSet( QueueSetMemberHandle_t xQueueOrSemaphore,
                                    QueueSetHandle_t xQueueSet ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xQueueRemoveFromSet( xQueueOrSemaphore, xQueueSet );
    }
    else
    {
        xReturn = xQueueRemoveFromSet( xQueueOrSemaphore, xQueueSet );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
void MPU_vQueueAddToRegistry( QueueHandle_t xQueue,
                              const char * pcName ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vQueueAddToRegistry( xQueue, pcName );
    }
    else
    {
        vQueueAddToRegistry( xQueue, pcName );
    }
}
/*-----------------------------------------------------------*/
void MPU_vQueueUnregisterQueue( QueueHandle_t xQueue ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vQueueUnregisterQueue( xQueue );
    }
    else
    {
        vQueueUnregisterQueue( xQueue );
    }
}
/*-----------------------------------------------------------*/
const char * MPU_pcQueueGetName( QueueHandle_t xQueue ) 
{
    const char * pcReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        pcReturn = syscall_pcQueueGetName( xQueue );
    }
    else
    {
        pcReturn = pcQueueGetName( xQueue );
    }
    return pcReturn;
}
/*-----------------------------------------------------------*/
void MPU_vQueueDelete( QueueHandle_t xQueue ) 
{
    vQueueDelete( xQueue );
}
/*-----------------------------------------------------------*/
void * MPU_pvTimerGetTimerID( const TimerHandle_t xTimer ) 
{
    void * pvReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        pvReturn = syscall_pvTimerGetTimerID( xTimer );
    }
    else
    {
        pvReturn = pvTimerGetTimerID( xTimer );
    }
    return pvReturn;
}
/*-----------------------------------------------------------*/
void MPU_vTimerSetTimerID( TimerHandle_t xTimer,
                           void * pvNewID ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vTimerSetTimerID( xTimer, pvNewID );
    }
    else
    {
        vTimerSetTimerID( xTimer, pvNewID );
    }
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTimerIsTimerActive( TimerHandle_t xTimer ) 
{
    BaseType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTimerIsTimerActive( xTimer );
    }
    else
    {
        xReturn = xTimerIsTimerActive( xTimer );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
TaskHandle_t MPU_xTimerGetTimerDaemonTaskHandle( void ) 
{
    TaskHandle_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTimerGetTimerDaemonTaskHandle();
    }
    else
    {
        xReturn = xTimerGetTimerDaemonTaskHandle();
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
void MPU_vTimerSetReloadMode( TimerHandle_t xTimer,
                              const BaseType_t uxAutoReload ) 
{
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        syscall_vTimerSetReloadMode( xTimer, uxAutoReload );
    }
    else
    {
        vTimerSetReloadMode( xTimer, uxAutoReload );
    }
}
/*-----------------------------------------------------------*/
UBaseType_t MPU_uxTimerGetReloadMode( TimerHandle_t xTimer )
{
    UBaseType_t uxReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        uxReturn = syscall_uxTimerGetReloadMode( xTimer );
    }
    else
    {
        uxReturn = uxTimerGetReloadMode( xTimer );
    }
    return uxReturn;
}
/*-----------------------------------------------------------*/
const char * MPU_pcTimerGetName( TimerHandle_t xTimer ) 
{
    const char * pcReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        pcReturn = syscall_pcTimerGetName( xTimer );
    }
    else
    {
        pcReturn = pcTimerGetName( xTimer );
    }
    return pcReturn;
}
/*-----------------------------------------------------------*/
TickType_t MPU_xTimerGetPeriod( TimerHandle_t xTimer ) 
{
    TickType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTimerGetPeriod( xTimer );
    }
    else
    {
        xReturn = xTimerGetPeriod( xTimer );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
TickType_t MPU_xTimerGetExpiryTime( TimerHandle_t xTimer ) 
{
    TickType_t xReturn;
    if( portIS_PRIVILEGED() == pdFALSE )
    {
        xReturn = syscall_xTimerGetExpiryTime( xTimer );
    }
    else
    {
        xReturn = xTimerGetExpiryTime( xTimer );
    }
    return xReturn;
}
/*-----------------------------------------------------------*/
void MPU_vTaskListTasks( char * pcWriteBuffer,
                         size_t uxBufferLength ) 
{
    vTaskListTasks( pcWriteBuffer, uxBufferLength );
}
/*-----------------------------------------------------------*/
void MPU_vTaskSuspendAll( void ) 
{
    vTaskSuspendAll();
}
/*-----------------------------------------------------------*/
BaseType_t MPU_xTaskResumeAll( void ) 
{
    return xTaskResumeAll();
}
/*-----------------------------------------------------------*/
#if defined (INCLUDE_xTaskAbortDelay)
    #if ( INCLUDE_xTaskAbortDelay == 1 )
        BaseType_t MPU_xTaskAbortDelay( TaskHandle_t xTask ) /* FREERTOS_SYSTEM_CALL */
        {
            BaseType_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
              xReturn = syscall_xTaskAbortDelay( xTask );
            }
            else
            {
                xReturn = xTaskAbortDelay( xTask );
            }

            return xReturn;
        }
    #endif /* if ( INCLUDE_xTaskAbortDelay == 1 ) */
#endif /* #if defined (INCLUDE_xTaskAbortDelay) */

#if defined (INCLUDE_xTaskGetHandle)
    #if ( INCLUDE_xTaskGetHandle == 1 )
        TaskHandle_t MPU_xTaskGetHandle( const char * pcNameToQuery ) /* FREERTOS_SYSTEM_CALL */
        {
            TaskHandle_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
               xReturn = syscall_xTaskGetHandle( pcNameToQuery );
            }
            else
            {
                xReturn = xTaskGetHandle( pcNameToQuery );
            }

            return xReturn;
        }
    #endif /* if ( INCLUDE_xTaskGetHandle == 1 ) */
#endif /* #if defined (INCLUDE_xTaskGetHandle)  */

#if defined (configSUPPORT_DYNAMIC_ALLOCATION) && defined (configUSE_EVENT_GROUPS)
    #if ( ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) && ( configUSE_EVENT_GROUPS == 1 ) )
	    EventGroupHandle_t MPU_xEventGroupCreate( void ) /* FREERTOS_SYSTEM_CALL */
        {
	        EventGroupHandle_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                xReturn = syscall_xEventGroupCreate();
            }
            else
            {
                xReturn = xEventGroupCreate();
            }
                return xReturn;
         }
    #endif /* #if ( ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) && ( configUSE_EVENT_GROUPS == 1 ) ) */
#endif /* #if defined  (configUSE_EVENT_GROUPS)  #if defined (configSUPPORT_DYNAMIC_ALLOCATION)  */
/*-----------------------------------------------------------*/

#if defined (configUSE_EVENT_GROUPS)
    #if ( configUSE_EVENT_GROUPS == 1 )
        EventBits_t MPU_xEventGroupWaitBits( EventGroupHandle_t xEventGroup,
                                             const EventBits_t uxBitsToWaitFor,
                                             const BaseType_t xClearOnExit,
                                             const BaseType_t xWaitForAllBits,
                                             TickType_t xTicksToWait ) /* FREERTOS_SYSTEM_CALL */
        {
            EventBits_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                xReturn = syscall_xEventGroupWaitBits( xEventGroup, uxBitsToWaitFor, xClearOnExit, xWaitForAllBits, xTicksToWait );
            }
            else
            {
                xReturn = xEventGroupWaitBits( xEventGroup, uxBitsToWaitFor, xClearOnExit, xWaitForAllBits, xTicksToWait );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_EVENT_GROUPS == 1 ) */
#endif /* #if defined (configUSE_EVENT_GROUPS) */

#if defined (configUSE_EVENT_GROUPS)
    #if ( configUSE_EVENT_GROUPS == 1 )
        void MPU_vEventGroupDelete( EventGroupHandle_t xEventGroup ) /* FREERTOS_SYSTEM_CALL */
        {
            if( portIS_PRIVILEGED() == pdFALSE )
            {
              syscall_vEventGroupDelete( xEventGroup );
            }
            else
            {
                vEventGroupDelete( xEventGroup );
            }
        }
    #endif /* #if ( configUSE_EVENT_GROUPS == 1 ) */
#endif /* #if defined (configUSE_EVENT_GROUPS) */

#if defined (configSUPPORT_DYNAMIC_ALLOCATION)
    #if  defined (configUSE_STREAM_BUFFERS) 
        #if ( ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) && ( configUSE_STREAM_BUFFERS == 1 ) )
	        StreamBufferHandle_t MPU_xStreamBufferGenericCreate( size_t xBufferSizeBytes,
																 size_t xTriggerLevelBytes,
																 BaseType_t xStreamBufferType,
																 StreamBufferCallbackFunction_t pxSendCompletedCallback,
																 StreamBufferCallbackFunction_t pxReceiveCompletedCallback ) /* FREERTOS_SYSTEM_CALL */
			{
                StreamBufferHandle_t xReturn;

				/**
				 * Stream buffer application level callback functionality is disabled for MPU
				 * enabled ports.
				 */
				configASSERT( ( pxSendCompletedCallback == NULL ) &&
							  ( pxReceiveCompletedCallback == NULL ) );

				if( ( pxSendCompletedCallback == NULL ) &&
					( pxReceiveCompletedCallback == NULL ) )
				{
					if( portIS_PRIVILEGED() == pdFALSE )
					{
						xReturn = syscall_xStreamBufferGenericCreate( xBufferSizeBytes,
															  xTriggerLevelBytes,
															  xStreamBufferType,
															  NULL,
															  NULL );

					}
			        else
					{
						xReturn = xStreamBufferGenericCreate( xBufferSizeBytes,
															  xTriggerLevelBytes,
															  xStreamBufferType,
															  NULL,
															  NULL );
					}
				}
				else
				{
					traceSTREAM_BUFFER_CREATE_FAILED( xStreamBufferType );
					xReturn = NULL;
				}

				return xReturn;
            }
        #endif /* #if ( ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) && ( configUSE_STREAM_BUFFERS == 1 ) ) */
    #endif /* #if defined (configUSE_STREAM_BUFFERS) */
#endif /* #if defined (configSUPPORT_DYNAMIC_ALLOCATION) */

#if defined (configUSE_STREAM_BUFFERS)
    #if ( configUSE_STREAM_BUFFERS == 1 )
        size_t MPU_xStreamBufferReceive( StreamBufferHandle_t xStreamBuffer,
                                         void * pvRxData,
                                         size_t xBufferLengthBytes,
                                         TickType_t xTicksToWait ) /* FREERTOS_SYSTEM_CALL */
        {
            size_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                xReturn = syscall_xStreamBufferReceive( xStreamBuffer, pvRxData, xBufferLengthBytes, xTicksToWait );
            }
            else
            {
                
                xReturn = xStreamBufferReceive( xStreamBuffer, pvRxData, xBufferLengthBytes, xTicksToWait );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */
#endif /* #if defined (configUSE_STREAM_BUFFERS)*/

#if defined (configUSE_STREAM_BUFFERS)
    #if ( configUSE_STREAM_BUFFERS == 1 )
        void MPU_vStreamBufferDelete( StreamBufferHandle_t xStreamBuffer ) /* FREERTOS_SYSTEM_CALL */
        {
            if( portIS_PRIVILEGED() == pdFALSE )
            {  
               syscall_vStreamBufferDelete( xStreamBuffer );
            }
            else
            {
                vStreamBufferDelete( xStreamBuffer );
            }
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */
#endif /* #if defined (configUSE_STREAM_BUFFERS)*/

#if defined (configUSE_MUTEXES) &&  defined ( INCLUDE_xSemaphoreGetMutexHolder)
    #if ( ( configUSE_MUTEXES == 1 ) && ( INCLUDE_xSemaphoreGetMutexHolder == 1 ) )
        TaskHandle_t MPU_xQueueGetMutexHolder( QueueHandle_t xSemaphore ) /* FREERTOS_SYSTEM_CALL */
        {
            void * xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                xReturn = syscall_xQueueGetMutexHolder( xSemaphore );
            }
            else
            {
                xReturn = xQueueGetMutexHolder( xSemaphore );
            }

            return xReturn;
        }
    #endif /* if ( ( configUSE_MUTEXES == 1 ) && ( INCLUDE_xSemaphoreGetMutexHolder == 1 ) ) */
#endif /* #if defined (configUSE_MUTEXES) &&  defined ( INCLUDE_xSemaphoreGetMutexHolder) */

#if defined (configUSE_EVENT_GROUPS)
    #if ( configUSE_EVENT_GROUPS == 1 )
        EventBits_t MPU_xEventGroupSync( EventGroupHandle_t xEventGroup,
                                         const EventBits_t uxBitsToSet,
                                         const EventBits_t uxBitsToWaitFor,
                                         TickType_t xTicksToWait ) /* FREERTOS_SYSTEM_CALL */
        {
            EventBits_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                xReturn = syscall_xEventGroupSync( xEventGroup, uxBitsToSet, uxBitsToWaitFor, xTicksToWait );
            }
            else
            {
                xReturn = xEventGroupSync( xEventGroup, uxBitsToSet, uxBitsToWaitFor, xTicksToWait );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_EVENT_GROUPS == 1 ) */
#endif /* #if defined (configUSE_EVENT_GROUPS) */

#if defined (configUSE_EVENT_GROUPS)
    #if ( configUSE_EVENT_GROUPS == 1 )
        EventBits_t MPU_xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                            const EventBits_t uxBitsToSet ) /* FREERTOS_SYSTEM_CALL */
        {
            EventBits_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                 xReturn = syscall_xEventGroupSetBits( xEventGroup, uxBitsToSet ); 
            }
            else
            {
                xReturn = xEventGroupSetBits( xEventGroup, uxBitsToSet );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_EVENT_GROUPS == 1 ) */
#endif /* #if defined (configUSE_EVENT_GROUPS) */

#if defined (configUSE_EVENT_GROUPS)
    #if ( configUSE_EVENT_GROUPS == 1 )
        EventBits_t MPU_xEventGroupClearBits( EventGroupHandle_t xEventGroup,
                                              const EventBits_t uxBitsToClear ) /* FREERTOS_SYSTEM_CALL */
        {
            EventBits_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
              xReturn = syscall_xEventGroupClearBits( xEventGroup, uxBitsToClear );
            }
            else
            {
                xReturn = xEventGroupClearBits( xEventGroup, uxBitsToClear );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_EVENT_GROUPS == 1 ) */
#endif /* #if defined (configUSE_EVENT_GROUPS) */

#if defined (configUSE_STREAM_BUFFERS)
    #if ( configUSE_STREAM_BUFFERS == 1 )
        size_t MPU_xStreamBufferSend( StreamBufferHandle_t xStreamBuffer,
                                      const void * pvTxData,
                                      size_t xDataLengthBytes,
                                      TickType_t xTicksToWait ) /* FREERTOS_SYSTEM_CALL */
        {
            size_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {

                xReturn = syscall_xStreamBufferSend( xStreamBuffer, pvTxData, xDataLengthBytes, xTicksToWait );
            }
            else
            {
                xReturn = xStreamBufferSend( xStreamBuffer, pvTxData, xDataLengthBytes, xTicksToWait );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */

    #if ( configUSE_STREAM_BUFFERS == 1 )
        BaseType_t MPU_xStreamBufferIsEmpty( StreamBufferHandle_t xStreamBuffer ) /* FREERTOS_SYSTEM_CALL */
        {
            BaseType_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                xReturn = syscall_xStreamBufferIsEmpty( xStreamBuffer );
            }
            else
            {
                xReturn = xStreamBufferIsEmpty( xStreamBuffer );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */

    #if ( configUSE_STREAM_BUFFERS == 1 )
        size_t MPU_xStreamBufferNextMessageLengthBytes( StreamBufferHandle_t xStreamBuffer ) /* FREERTOS_SYSTEM_CALL */
        {
            size_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
              xReturn = syscall_xStreamBufferNextMessageLengthBytes( xStreamBuffer );
            }
            else
            {
                xReturn = xStreamBufferNextMessageLengthBytes( xStreamBuffer );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */

    #if ( configUSE_STREAM_BUFFERS == 1 )
        BaseType_t MPU_xStreamBufferIsFull( StreamBufferHandle_t xStreamBuffer ) /* FREERTOS_SYSTEM_CALL */
        {
            BaseType_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
               xReturn = syscall_xStreamBufferIsFull( xStreamBuffer );
            }
            else
            {
                xReturn = xStreamBufferIsFull( xStreamBuffer );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */

    #if ( configUSE_STREAM_BUFFERS == 1 )
        size_t MPU_xStreamBufferSpacesAvailable( StreamBufferHandle_t xStreamBuffer ) /* FREERTOS_SYSTEM_CALL */
        {
            size_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                xReturn = syscall_xStreamBufferSpacesAvailable ( xStreamBuffer );
            }
            else
            {
                xReturn = xStreamBufferSpacesAvailable( xStreamBuffer );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */

    #if ( configUSE_STREAM_BUFFERS == 1 )
        BaseType_t MPU_xStreamBufferReset( StreamBufferHandle_t xStreamBuffer ) /* FREERTOS_SYSTEM_CALL */
        {
            BaseType_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
               xReturn = syscall_xStreamBufferReset( xStreamBuffer );
            }
            else
            {
                xReturn = xStreamBufferReset( xStreamBuffer );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */
/*-----------------------------------------------------------*/
    #if ( configUSE_STREAM_BUFFERS == 1 )
        size_t MPU_xStreamBufferBytesAvailable( StreamBufferHandle_t xStreamBuffer ) /* FREERTOS_SYSTEM_CALL */
        {
            size_t xReturn;

            if( portIS_PRIVILEGED() == pdFALSE )
            {
                xReturn = syscall_xStreamBufferBytesAvailable( xStreamBuffer );
            }
            else
            {
                xReturn = xStreamBufferBytesAvailable( xStreamBuffer );
            }

            return xReturn;
        }
    #endif /* #if ( configUSE_STREAM_BUFFERS == 1 ) */
/*-----------------------------------------------------------*/
#endif /* #if defined (configUSE_STREAM_BUFFERS)*/
