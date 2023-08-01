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

/* Including FreeRTOSConfig.h here will cause build errors if the header file
 * contains code not understood by the assembler - for example the 'extern' keyword.
 * To avoid errors place any such code inside a #ifdef __ICCARM__/#endif block so
 * the code is included in C files but excluded by the preprocessor in assembly
 * files (__ICCARM__ is defined by the IAR C compiler but not by the IAR assembler. */
#include "FreeRTOSConfig.h"

    SECTION freertos_system_calls:CODE:NOROOT(2)
    THUMB
/*-----------------------------------------------------------*/

#ifndef configUSE_MPU_WRAPPERS_V1
    #define configUSE_MPU_WRAPPERS_V1 0
#endif

/* These must be in sync with portmacro.h. */
#define portSVC_SYSTEM_CALL_ENTER   3 /* System calls with upto 4 parameters. */
#define portSVC_SYSTEM_CALL_ENTER_1 4 /* System calls with 5 parameters. */
#define portSVC_SYSTEM_CALL_EXIT    5
/*-----------------------------------------------------------*/

#if ( configUSE_MPU_WRAPPERS_V1 == 0 )

    PUBLIC MPU_xTaskDelayUntil
MPU_xTaskDelayUntil:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskDelayUntil_Unpriv
    MPU_xTaskDelayUntil_Priv:
        pop {r0}
        b MPU_xTaskDelayUntilImpl
    MPU_xTaskDelayUntil_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskDelayUntilImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskAbortDelay
MPU_xTaskAbortDelay:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskAbortDelay_Unpriv
    MPU_xTaskAbortDelay_Priv:
        pop {r0}
        b MPU_xTaskAbortDelayImpl
    MPU_xTaskAbortDelay_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskAbortDelayImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTaskDelay
MPU_vTaskDelay:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTaskDelay_Unpriv
    MPU_vTaskDelay_Priv:
        pop {r0}
        b MPU_vTaskDelayImpl
    MPU_vTaskDelay_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTaskDelayImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxTaskPriorityGet
MPU_uxTaskPriorityGet:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxTaskPriorityGet_Unpriv
    MPU_uxTaskPriorityGet_Priv:
        pop {r0}
        b MPU_uxTaskPriorityGetImpl
    MPU_uxTaskPriorityGet_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxTaskPriorityGetImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_eTaskGetState
MPU_eTaskGetState:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_eTaskGetState_Unpriv
    MPU_eTaskGetState_Priv:
        pop {r0}
        b MPU_eTaskGetStateImpl
    MPU_eTaskGetState_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_eTaskGetStateImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTaskGetInfo
MPU_vTaskGetInfo:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTaskGetInfo_Unpriv
    MPU_vTaskGetInfo_Priv:
        pop {r0}
        b MPU_vTaskGetInfoImpl
    MPU_vTaskGetInfo_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTaskGetInfoImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskGetIdleTaskHandle
MPU_xTaskGetIdleTaskHandle:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskGetIdleTaskHandle_Unpriv
    MPU_xTaskGetIdleTaskHandle_Priv:
        pop {r0}
        b MPU_xTaskGetIdleTaskHandleImpl
    MPU_xTaskGetIdleTaskHandle_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskGetIdleTaskHandleImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTaskSuspend
MPU_vTaskSuspend:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTaskSuspend_Unpriv
    MPU_vTaskSuspend_Priv:
        pop {r0}
        b MPU_vTaskSuspendImpl
    MPU_vTaskSuspend_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTaskSuspendImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTaskResume
MPU_vTaskResume:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTaskResume_Unpriv
    MPU_vTaskResume_Priv:
        pop {r0}
        b MPU_vTaskResumeImpl
    MPU_vTaskResume_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTaskResumeImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskGetTickCount
MPU_xTaskGetTickCount:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskGetTickCount_Unpriv
    MPU_xTaskGetTickCount_Priv:
        pop {r0}
        b MPU_xTaskGetTickCountImpl
    MPU_xTaskGetTickCount_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskGetTickCountImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxTaskGetNumberOfTasks
MPU_uxTaskGetNumberOfTasks:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxTaskGetNumberOfTasks_Unpriv
    MPU_uxTaskGetNumberOfTasks_Priv:
        pop {r0}
        b MPU_uxTaskGetNumberOfTasksImpl
    MPU_uxTaskGetNumberOfTasks_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxTaskGetNumberOfTasksImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_pcTaskGetName
MPU_pcTaskGetName:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_pcTaskGetName_Unpriv
    MPU_pcTaskGetName_Priv:
        pop {r0}
        b MPU_pcTaskGetNameImpl
    MPU_pcTaskGetName_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_pcTaskGetNameImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_ulTaskGetRunTimeCounter
MPU_ulTaskGetRunTimeCounter:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_ulTaskGetRunTimeCounter_Unpriv
    MPU_ulTaskGetRunTimeCounter_Priv:
        pop {r0}
        b MPU_ulTaskGetRunTimeCounterImpl
    MPU_ulTaskGetRunTimeCounter_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_ulTaskGetRunTimeCounterImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_ulTaskGetRunTimePercent
MPU_ulTaskGetRunTimePercent:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_ulTaskGetRunTimePercent_Unpriv
    MPU_ulTaskGetRunTimePercent_Priv:
        pop {r0}
        b MPU_ulTaskGetRunTimePercentImpl
    MPU_ulTaskGetRunTimePercent_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_ulTaskGetRunTimePercentImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_ulTaskGetIdleRunTimePercent
MPU_ulTaskGetIdleRunTimePercent:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_ulTaskGetIdleRunTimePercent_Unpriv
    MPU_ulTaskGetIdleRunTimePercent_Priv:
        pop {r0}
        b MPU_ulTaskGetIdleRunTimePercentImpl
    MPU_ulTaskGetIdleRunTimePercent_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_ulTaskGetIdleRunTimePercentImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_ulTaskGetIdleRunTimeCounter
MPU_ulTaskGetIdleRunTimeCounter:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_ulTaskGetIdleRunTimeCounter_Unpriv
    MPU_ulTaskGetIdleRunTimeCounter_Priv:
        pop {r0}
        b MPU_ulTaskGetIdleRunTimeCounterImpl
    MPU_ulTaskGetIdleRunTimeCounter_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_ulTaskGetIdleRunTimeCounterImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTaskSetApplicationTaskTag
MPU_vTaskSetApplicationTaskTag:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTaskSetApplicationTaskTag_Unpriv
    MPU_vTaskSetApplicationTaskTag_Priv:
        pop {r0}
        b MPU_vTaskSetApplicationTaskTagImpl
    MPU_vTaskSetApplicationTaskTag_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTaskSetApplicationTaskTagImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskGetApplicationTaskTag
MPU_xTaskGetApplicationTaskTag:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskGetApplicationTaskTag_Unpriv
    MPU_xTaskGetApplicationTaskTag_Priv:
        pop {r0}
        b MPU_xTaskGetApplicationTaskTagImpl
    MPU_xTaskGetApplicationTaskTag_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskGetApplicationTaskTagImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTaskSetThreadLocalStoragePointer
MPU_vTaskSetThreadLocalStoragePointer:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTaskSetThreadLocalStoragePointer_Unpriv
    MPU_vTaskSetThreadLocalStoragePointer_Priv:
        pop {r0}
        b MPU_vTaskSetThreadLocalStoragePointerImpl
    MPU_vTaskSetThreadLocalStoragePointer_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTaskSetThreadLocalStoragePointerImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_pvTaskGetThreadLocalStoragePointer
MPU_pvTaskGetThreadLocalStoragePointer:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_pvTaskGetThreadLocalStoragePointer_Unpriv
    MPU_pvTaskGetThreadLocalStoragePointer_Priv:
        pop {r0}
        b MPU_pvTaskGetThreadLocalStoragePointerImpl
    MPU_pvTaskGetThreadLocalStoragePointer_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_pvTaskGetThreadLocalStoragePointerImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxTaskGetSystemState
MPU_uxTaskGetSystemState:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxTaskGetSystemState_Unpriv
    MPU_uxTaskGetSystemState_Priv:
        pop {r0}
        b MPU_uxTaskGetSystemStateImpl
    MPU_uxTaskGetSystemState_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxTaskGetSystemStateImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxTaskGetStackHighWaterMark
MPU_uxTaskGetStackHighWaterMark:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxTaskGetStackHighWaterMark_Unpriv
    MPU_uxTaskGetStackHighWaterMark_Priv:
        pop {r0}
        b MPU_uxTaskGetStackHighWaterMarkImpl
    MPU_uxTaskGetStackHighWaterMark_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxTaskGetStackHighWaterMarkImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxTaskGetStackHighWaterMark2
MPU_uxTaskGetStackHighWaterMark2:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxTaskGetStackHighWaterMark2_Unpriv
    MPU_uxTaskGetStackHighWaterMark2_Priv:
        pop {r0}
        b MPU_uxTaskGetStackHighWaterMark2Impl
    MPU_uxTaskGetStackHighWaterMark2_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxTaskGetStackHighWaterMark2Impl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskGetCurrentTaskHandle
MPU_xTaskGetCurrentTaskHandle:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskGetCurrentTaskHandle_Unpriv
    MPU_xTaskGetCurrentTaskHandle_Priv:
        pop {r0}
        b MPU_xTaskGetCurrentTaskHandleImpl
    MPU_xTaskGetCurrentTaskHandle_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskGetCurrentTaskHandleImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskGetSchedulerState
MPU_xTaskGetSchedulerState:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskGetSchedulerState_Unpriv
    MPU_xTaskGetSchedulerState_Priv:
        pop {r0}
        b MPU_xTaskGetSchedulerStateImpl
    MPU_xTaskGetSchedulerState_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskGetSchedulerStateImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTaskSetTimeOutState
MPU_vTaskSetTimeOutState:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTaskSetTimeOutState_Unpriv
    MPU_vTaskSetTimeOutState_Priv:
        pop {r0}
        b MPU_vTaskSetTimeOutStateImpl
    MPU_vTaskSetTimeOutState_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTaskSetTimeOutStateImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskCheckForTimeOut
MPU_xTaskCheckForTimeOut:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskCheckForTimeOut_Unpriv
    MPU_xTaskCheckForTimeOut_Priv:
        pop {r0}
        b MPU_xTaskCheckForTimeOutImpl
    MPU_xTaskCheckForTimeOut_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskCheckForTimeOutImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskGenericNotify
MPU_xTaskGenericNotify:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskGenericNotify_Unpriv
    MPU_xTaskGenericNotify_Priv:
        pop {r0}
        b MPU_xTaskGenericNotifyImpl
    MPU_xTaskGenericNotify_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER_1
        bl MPU_xTaskGenericNotifyImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskGenericNotifyWait
MPU_xTaskGenericNotifyWait:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskGenericNotifyWait_Unpriv
    MPU_xTaskGenericNotifyWait_Priv:
        pop {r0}
        b MPU_xTaskGenericNotifyWaitImpl
    MPU_xTaskGenericNotifyWait_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER_1
        bl MPU_xTaskGenericNotifyWaitImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_ulTaskGenericNotifyTake
MPU_ulTaskGenericNotifyTake:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_ulTaskGenericNotifyTake_Unpriv
    MPU_ulTaskGenericNotifyTake_Priv:
        pop {r0}
        b MPU_ulTaskGenericNotifyTakeImpl
    MPU_ulTaskGenericNotifyTake_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_ulTaskGenericNotifyTakeImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTaskGenericNotifyStateClear
MPU_xTaskGenericNotifyStateClear:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTaskGenericNotifyStateClear_Unpriv
    MPU_xTaskGenericNotifyStateClear_Priv:
        pop {r0}
        b MPU_xTaskGenericNotifyStateClearImpl
    MPU_xTaskGenericNotifyStateClear_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTaskGenericNotifyStateClearImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_ulTaskGenericNotifyValueClear
MPU_ulTaskGenericNotifyValueClear:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_ulTaskGenericNotifyValueClear_Unpriv
    MPU_ulTaskGenericNotifyValueClear_Priv:
        pop {r0}
        b MPU_ulTaskGenericNotifyValueClearImpl
    MPU_ulTaskGenericNotifyValueClear_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_ulTaskGenericNotifyValueClearImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueueGenericSend
MPU_xQueueGenericSend:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueueGenericSend_Unpriv
    MPU_xQueueGenericSend_Priv:
        pop {r0}
        b MPU_xQueueGenericSendImpl
    MPU_xQueueGenericSend_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueueGenericSendImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxQueueMessagesWaiting
MPU_uxQueueMessagesWaiting:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxQueueMessagesWaiting_Unpriv
    MPU_uxQueueMessagesWaiting_Priv:
        pop {r0}
        b MPU_uxQueueMessagesWaitingImpl
    MPU_uxQueueMessagesWaiting_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxQueueMessagesWaitingImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxQueueSpacesAvailable
MPU_uxQueueSpacesAvailable:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxQueueSpacesAvailable_Unpriv
    MPU_uxQueueSpacesAvailable_Priv:
        pop {r0}
        b MPU_uxQueueSpacesAvailableImpl
    MPU_uxQueueSpacesAvailable_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxQueueSpacesAvailableImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueueReceive
MPU_xQueueReceive:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueueReceive_Unpriv
    MPU_xQueueReceive_Priv:
        pop {r0}
        b MPU_xQueueReceiveImpl
    MPU_xQueueReceive_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueueReceiveImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueuePeek
MPU_xQueuePeek:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueuePeek_Unpriv
    MPU_xQueuePeek_Priv:
        pop {r0}
        b MPU_xQueuePeekImpl
    MPU_xQueuePeek_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueuePeekImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueueSemaphoreTake
MPU_xQueueSemaphoreTake:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueueSemaphoreTake_Unpriv
    MPU_xQueueSemaphoreTake_Priv:
        pop {r0}
        b MPU_xQueueSemaphoreTakeImpl
    MPU_xQueueSemaphoreTake_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueueSemaphoreTakeImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueueGetMutexHolder
MPU_xQueueGetMutexHolder:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueueGetMutexHolder_Unpriv
    MPU_xQueueGetMutexHolder_Priv:
        pop {r0}
        b MPU_xQueueGetMutexHolderImpl
    MPU_xQueueGetMutexHolder_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueueGetMutexHolderImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueueTakeMutexRecursive
MPU_xQueueTakeMutexRecursive:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueueTakeMutexRecursive_Unpriv
    MPU_xQueueTakeMutexRecursive_Priv:
        pop {r0}
        b MPU_xQueueTakeMutexRecursiveImpl
    MPU_xQueueTakeMutexRecursive_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueueTakeMutexRecursiveImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueueGiveMutexRecursive
MPU_xQueueGiveMutexRecursive:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueueGiveMutexRecursive_Unpriv
    MPU_xQueueGiveMutexRecursive_Priv:
        pop {r0}
        b MPU_xQueueGiveMutexRecursiveImpl
    MPU_xQueueGiveMutexRecursive_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueueGiveMutexRecursiveImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueueSelectFromSet
MPU_xQueueSelectFromSet:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueueSelectFromSet_Unpriv
    MPU_xQueueSelectFromSet_Priv:
        pop {r0}
        b MPU_xQueueSelectFromSetImpl
    MPU_xQueueSelectFromSet_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueueSelectFromSetImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xQueueAddToSet
MPU_xQueueAddToSet:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xQueueAddToSet_Unpriv
    MPU_xQueueAddToSet_Priv:
        pop {r0}
        b MPU_xQueueAddToSetImpl
    MPU_xQueueAddToSet_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xQueueAddToSetImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vQueueAddToRegistry
MPU_vQueueAddToRegistry:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vQueueAddToRegistry_Unpriv
    MPU_vQueueAddToRegistry_Priv:
        pop {r0}
        b MPU_vQueueAddToRegistryImpl
    MPU_vQueueAddToRegistry_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vQueueAddToRegistryImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vQueueUnregisterQueue
MPU_vQueueUnregisterQueue:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vQueueUnregisterQueue_Unpriv
    MPU_vQueueUnregisterQueue_Priv:
        pop {r0}
        b MPU_vQueueUnregisterQueueImpl
    MPU_vQueueUnregisterQueue_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vQueueUnregisterQueueImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_pcQueueGetName
MPU_pcQueueGetName:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_pcQueueGetName_Unpriv
    MPU_pcQueueGetName_Priv:
        pop {r0}
        b MPU_pcQueueGetNameImpl
    MPU_pcQueueGetName_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_pcQueueGetNameImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_pvTimerGetTimerID
MPU_pvTimerGetTimerID:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_pvTimerGetTimerID_Unpriv
    MPU_pvTimerGetTimerID_Priv:
        pop {r0}
        b MPU_pvTimerGetTimerIDImpl
    MPU_pvTimerGetTimerID_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_pvTimerGetTimerIDImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTimerSetTimerID
MPU_vTimerSetTimerID:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTimerSetTimerID_Unpriv
    MPU_vTimerSetTimerID_Priv:
        pop {r0}
        b MPU_vTimerSetTimerIDImpl
    MPU_vTimerSetTimerID_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTimerSetTimerIDImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTimerIsTimerActive
MPU_xTimerIsTimerActive:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTimerIsTimerActive_Unpriv
    MPU_xTimerIsTimerActive_Priv:
        pop {r0}
        b MPU_xTimerIsTimerActiveImpl
    MPU_xTimerIsTimerActive_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTimerIsTimerActiveImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTimerGetTimerDaemonTaskHandle
MPU_xTimerGetTimerDaemonTaskHandle:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTimerGetTimerDaemonTaskHandle_Unpriv
    MPU_xTimerGetTimerDaemonTaskHandle_Priv:
        pop {r0}
        b MPU_xTimerGetTimerDaemonTaskHandleImpl
    MPU_xTimerGetTimerDaemonTaskHandle_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTimerGetTimerDaemonTaskHandleImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTimerGenericCommandFromTask
MPU_xTimerGenericCommandFromTask:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTimerGenericCommandFromTask_Unpriv
    MPU_xTimerGenericCommandFromTask_Priv:
        pop {r0}
        b MPU_xTimerGenericCommandFromTaskImpl
    MPU_xTimerGenericCommandFromTask_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER_1
        bl MPU_xTimerGenericCommandFromTaskImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_pcTimerGetName
MPU_pcTimerGetName:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_pcTimerGetName_Unpriv
    MPU_pcTimerGetName_Priv:
        pop {r0}
        b MPU_pcTimerGetNameImpl
    MPU_pcTimerGetName_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_pcTimerGetNameImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vTimerSetReloadMode
MPU_vTimerSetReloadMode:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vTimerSetReloadMode_Unpriv
    MPU_vTimerSetReloadMode_Priv:
        pop {r0}
        b MPU_vTimerSetReloadModeImpl
    MPU_vTimerSetReloadMode_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vTimerSetReloadModeImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTimerGetReloadMode
MPU_xTimerGetReloadMode:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTimerGetReloadMode_Unpriv
    MPU_xTimerGetReloadMode_Priv:
        pop {r0}
        b MPU_xTimerGetReloadModeImpl
    MPU_xTimerGetReloadMode_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTimerGetReloadModeImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxTimerGetReloadMode
MPU_uxTimerGetReloadMode:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxTimerGetReloadMode_Unpriv
    MPU_uxTimerGetReloadMode_Priv:
        pop {r0}
        b MPU_uxTimerGetReloadModeImpl
    MPU_uxTimerGetReloadMode_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxTimerGetReloadModeImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTimerGetPeriod
MPU_xTimerGetPeriod:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTimerGetPeriod_Unpriv
    MPU_xTimerGetPeriod_Priv:
        pop {r0}
        b MPU_xTimerGetPeriodImpl
    MPU_xTimerGetPeriod_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTimerGetPeriodImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xTimerGetExpiryTime
MPU_xTimerGetExpiryTime:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xTimerGetExpiryTime_Unpriv
    MPU_xTimerGetExpiryTime_Priv:
        pop {r0}
        b MPU_xTimerGetExpiryTimeImpl
    MPU_xTimerGetExpiryTime_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xTimerGetExpiryTimeImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xEventGroupWaitBits
MPU_xEventGroupWaitBits:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xEventGroupWaitBits_Unpriv
    MPU_xEventGroupWaitBits_Priv:
        pop {r0}
        b MPU_xEventGroupWaitBitsImpl
    MPU_xEventGroupWaitBits_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER_1
        bl MPU_xEventGroupWaitBitsImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xEventGroupClearBits
MPU_xEventGroupClearBits:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xEventGroupClearBits_Unpriv
    MPU_xEventGroupClearBits_Priv:
        pop {r0}
        b MPU_xEventGroupClearBitsImpl
    MPU_xEventGroupClearBits_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xEventGroupClearBitsImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xEventGroupSetBits
MPU_xEventGroupSetBits:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xEventGroupSetBits_Unpriv
    MPU_xEventGroupSetBits_Priv:
        pop {r0}
        b MPU_xEventGroupSetBitsImpl
    MPU_xEventGroupSetBits_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xEventGroupSetBitsImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xEventGroupSync
MPU_xEventGroupSync:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xEventGroupSync_Unpriv
    MPU_xEventGroupSync_Priv:
        pop {r0}
        b MPU_xEventGroupSyncImpl
    MPU_xEventGroupSync_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xEventGroupSyncImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_uxEventGroupGetNumber
MPU_uxEventGroupGetNumber:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_uxEventGroupGetNumber_Unpriv
    MPU_uxEventGroupGetNumber_Priv:
        pop {r0}
        b MPU_uxEventGroupGetNumberImpl
    MPU_uxEventGroupGetNumber_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_uxEventGroupGetNumberImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_vEventGroupSetNumber
MPU_vEventGroupSetNumber:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_vEventGroupSetNumber_Unpriv
    MPU_vEventGroupSetNumber_Priv:
        pop {r0}
        b MPU_vEventGroupSetNumberImpl
    MPU_vEventGroupSetNumber_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_vEventGroupSetNumberImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xStreamBufferSend
MPU_xStreamBufferSend:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xStreamBufferSend_Unpriv
    MPU_xStreamBufferSend_Priv:
        pop {r0}
        b MPU_xStreamBufferSendImpl
    MPU_xStreamBufferSend_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xStreamBufferSendImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xStreamBufferReceive
MPU_xStreamBufferReceive:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xStreamBufferReceive_Unpriv
    MPU_xStreamBufferReceive_Priv:
        pop {r0}
        b MPU_xStreamBufferReceiveImpl
    MPU_xStreamBufferReceive_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xStreamBufferReceiveImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xStreamBufferIsFull
MPU_xStreamBufferIsFull:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xStreamBufferIsFull_Unpriv
    MPU_xStreamBufferIsFull_Priv:
        pop {r0}
        b MPU_xStreamBufferIsFullImpl
    MPU_xStreamBufferIsFull_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xStreamBufferIsFullImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xStreamBufferIsEmpty
MPU_xStreamBufferIsEmpty:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xStreamBufferIsEmpty_Unpriv
    MPU_xStreamBufferIsEmpty_Priv:
        pop {r0}
        b MPU_xStreamBufferIsEmptyImpl
    MPU_xStreamBufferIsEmpty_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xStreamBufferIsEmptyImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xStreamBufferSpacesAvailable
MPU_xStreamBufferSpacesAvailable:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xStreamBufferSpacesAvailable_Unpriv
    MPU_xStreamBufferSpacesAvailable_Priv:
        pop {r0}
        b MPU_xStreamBufferSpacesAvailableImpl
    MPU_xStreamBufferSpacesAvailable_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xStreamBufferSpacesAvailableImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xStreamBufferBytesAvailable
MPU_xStreamBufferBytesAvailable:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xStreamBufferBytesAvailable_Unpriv
    MPU_xStreamBufferBytesAvailable_Priv:
        pop {r0}
        b MPU_xStreamBufferBytesAvailableImpl
    MPU_xStreamBufferBytesAvailable_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xStreamBufferBytesAvailableImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xStreamBufferSetTriggerLevel
MPU_xStreamBufferSetTriggerLevel:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xStreamBufferSetTriggerLevel_Unpriv
    MPU_xStreamBufferSetTriggerLevel_Priv:
        pop {r0}
        b MPU_xStreamBufferSetTriggerLevelImpl
    MPU_xStreamBufferSetTriggerLevel_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xStreamBufferSetTriggerLevelImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

    PUBLIC MPU_xStreamBufferNextMessageLengthBytes
MPU_xStreamBufferNextMessageLengthBytes:
    push {r0}
    mrs r0, control
    tst r0, #1
    bne MPU_xStreamBufferNextMessageLengthBytes_Unpriv
    MPU_xStreamBufferNextMessageLengthBytes_Priv:
        pop {r0}
        b MPU_xStreamBufferNextMessageLengthBytesImpl
    MPU_xStreamBufferNextMessageLengthBytes_Unpriv:
        pop {r0}
        svc #portSVC_SYSTEM_CALL_ENTER
        bl MPU_xStreamBufferNextMessageLengthBytesImpl
        svc #portSVC_SYSTEM_CALL_EXIT
        bx lr
/*-----------------------------------------------------------*/

/* Default weak implementations in case one is not available from
 * mpu_wrappers because of config options. */

    PUBWEAK MPU_xTaskDelayUntilImpl
MPU_xTaskDelayUntilImpl:
    b MPU_xTaskDelayUntilImpl

    PUBWEAK MPU_xTaskAbortDelayImpl
MPU_xTaskAbortDelayImpl:
    b MPU_xTaskAbortDelayImpl

    PUBWEAK MPU_vTaskDelayImpl
MPU_vTaskDelayImpl:
    b MPU_vTaskDelayImpl

    PUBWEAK MPU_uxTaskPriorityGetImpl
MPU_uxTaskPriorityGetImpl:
    b MPU_uxTaskPriorityGetImpl

    PUBWEAK MPU_eTaskGetStateImpl
MPU_eTaskGetStateImpl:
    b MPU_eTaskGetStateImpl

    PUBWEAK MPU_vTaskGetInfoImpl
MPU_vTaskGetInfoImpl:
    b MPU_vTaskGetInfoImpl

    PUBWEAK MPU_xTaskGetIdleTaskHandleImpl
MPU_xTaskGetIdleTaskHandleImpl:
    b MPU_xTaskGetIdleTaskHandleImpl

    PUBWEAK MPU_vTaskSuspendImpl
MPU_vTaskSuspendImpl:
    b MPU_vTaskSuspendImpl

    PUBWEAK MPU_vTaskResumeImpl
MPU_vTaskResumeImpl:
    b MPU_vTaskResumeImpl

    PUBWEAK MPU_xTaskGetTickCountImpl
MPU_xTaskGetTickCountImpl:
    b MPU_xTaskGetTickCountImpl

    PUBWEAK MPU_uxTaskGetNumberOfTasksImpl
MPU_uxTaskGetNumberOfTasksImpl:
    b MPU_uxTaskGetNumberOfTasksImpl

    PUBWEAK MPU_pcTaskGetNameImpl
MPU_pcTaskGetNameImpl:
    b MPU_pcTaskGetNameImpl

    PUBWEAK MPU_ulTaskGetRunTimeCounterImpl
MPU_ulTaskGetRunTimeCounterImpl:
    b MPU_ulTaskGetRunTimeCounterImpl

    PUBWEAK MPU_ulTaskGetRunTimePercentImpl
MPU_ulTaskGetRunTimePercentImpl:
    b MPU_ulTaskGetRunTimePercentImpl

    PUBWEAK MPU_ulTaskGetIdleRunTimePercentImpl
MPU_ulTaskGetIdleRunTimePercentImpl:
    b MPU_ulTaskGetIdleRunTimePercentImpl

    PUBWEAK MPU_ulTaskGetIdleRunTimeCounterImpl
MPU_ulTaskGetIdleRunTimeCounterImpl:
    b MPU_ulTaskGetIdleRunTimeCounterImpl

    PUBWEAK MPU_vTaskSetApplicationTaskTagImpl
MPU_vTaskSetApplicationTaskTagImpl:
    b MPU_vTaskSetApplicationTaskTagImpl

    PUBWEAK MPU_xTaskGetApplicationTaskTagImpl
MPU_xTaskGetApplicationTaskTagImpl:
    b MPU_xTaskGetApplicationTaskTagImpl

    PUBWEAK MPU_vTaskSetThreadLocalStoragePointerImpl
MPU_vTaskSetThreadLocalStoragePointerImpl:
    b MPU_vTaskSetThreadLocalStoragePointerImpl

    PUBWEAK MPU_pvTaskGetThreadLocalStoragePointerImpl
MPU_pvTaskGetThreadLocalStoragePointerImpl:
    b MPU_pvTaskGetThreadLocalStoragePointerImpl

    PUBWEAK MPU_uxTaskGetSystemStateImpl
MPU_uxTaskGetSystemStateImpl:
    b MPU_uxTaskGetSystemStateImpl

    PUBWEAK MPU_uxTaskGetStackHighWaterMarkImpl
MPU_uxTaskGetStackHighWaterMarkImpl:
    b MPU_uxTaskGetStackHighWaterMarkImpl

    PUBWEAK MPU_uxTaskGetStackHighWaterMark2Impl
MPU_uxTaskGetStackHighWaterMark2Impl:
    b MPU_uxTaskGetStackHighWaterMark2Impl

    PUBWEAK MPU_xTaskGetCurrentTaskHandleImpl
MPU_xTaskGetCurrentTaskHandleImpl:
    b MPU_xTaskGetCurrentTaskHandleImpl

    PUBWEAK MPU_xTaskGetSchedulerStateImpl
MPU_xTaskGetSchedulerStateImpl:
    b MPU_xTaskGetSchedulerStateImpl

    PUBWEAK MPU_vTaskSetTimeOutStateImpl
MPU_vTaskSetTimeOutStateImpl:
    b MPU_vTaskSetTimeOutStateImpl

    PUBWEAK MPU_xTaskCheckForTimeOutImpl
MPU_xTaskCheckForTimeOutImpl:
    b MPU_xTaskCheckForTimeOutImpl

    PUBWEAK MPU_xTaskGenericNotifyImpl
MPU_xTaskGenericNotifyImpl:
    b MPU_xTaskGenericNotifyImpl

    PUBWEAK MPU_xTaskGenericNotifyWaitImpl
MPU_xTaskGenericNotifyWaitImpl:
    b MPU_xTaskGenericNotifyWaitImpl

    PUBWEAK MPU_ulTaskGenericNotifyTakeImpl
MPU_ulTaskGenericNotifyTakeImpl:
    b MPU_ulTaskGenericNotifyTakeImpl

    PUBWEAK MPU_xTaskGenericNotifyStateClearImpl
MPU_xTaskGenericNotifyStateClearImpl:
    b MPU_xTaskGenericNotifyStateClearImpl

    PUBWEAK MPU_ulTaskGenericNotifyValueClearImpl
MPU_ulTaskGenericNotifyValueClearImpl:
    b MPU_ulTaskGenericNotifyValueClearImpl

    PUBWEAK MPU_xQueueGenericSendImpl
MPU_xQueueGenericSendImpl:
    b MPU_xQueueGenericSendImpl

    PUBWEAK MPU_uxQueueMessagesWaitingImpl
MPU_uxQueueMessagesWaitingImpl:
    b MPU_uxQueueMessagesWaitingImpl

    PUBWEAK MPU_uxQueueSpacesAvailableImpl
MPU_uxQueueSpacesAvailableImpl:
    b MPU_uxQueueSpacesAvailableImpl

    PUBWEAK MPU_xQueueReceiveImpl
MPU_xQueueReceiveImpl:
    b MPU_xQueueReceiveImpl

    PUBWEAK MPU_xQueuePeekImpl
MPU_xQueuePeekImpl:
    b MPU_xQueuePeekImpl

    PUBWEAK MPU_xQueueSemaphoreTakeImpl
MPU_xQueueSemaphoreTakeImpl:
    b MPU_xQueueSemaphoreTakeImpl

    PUBWEAK MPU_xQueueGetMutexHolderImpl
MPU_xQueueGetMutexHolderImpl:
    b MPU_xQueueGetMutexHolderImpl

    PUBWEAK MPU_xQueueTakeMutexRecursiveImpl
MPU_xQueueTakeMutexRecursiveImpl:
    b MPU_xQueueTakeMutexRecursiveImpl

    PUBWEAK MPU_xQueueGiveMutexRecursiveImpl
MPU_xQueueGiveMutexRecursiveImpl:
    b MPU_xQueueGiveMutexRecursiveImpl

    PUBWEAK MPU_xQueueSelectFromSetImpl
MPU_xQueueSelectFromSetImpl:
    b MPU_xQueueSelectFromSetImpl

    PUBWEAK MPU_xQueueAddToSetImpl
MPU_xQueueAddToSetImpl:
    b MPU_xQueueAddToSetImpl

    PUBWEAK MPU_vQueueAddToRegistryImpl
MPU_vQueueAddToRegistryImpl:
    b MPU_vQueueAddToRegistryImpl

    PUBWEAK MPU_vQueueUnregisterQueueImpl
MPU_vQueueUnregisterQueueImpl:
    b MPU_vQueueUnregisterQueueImpl

    PUBWEAK MPU_pcQueueGetNameImpl
MPU_pcQueueGetNameImpl:
    b MPU_pcQueueGetNameImpl

    PUBWEAK MPU_pvTimerGetTimerIDImpl
MPU_pvTimerGetTimerIDImpl:
    b MPU_pvTimerGetTimerIDImpl

    PUBWEAK MPU_vTimerSetTimerIDImpl
MPU_vTimerSetTimerIDImpl:
    b MPU_vTimerSetTimerIDImpl

    PUBWEAK MPU_xTimerIsTimerActiveImpl
MPU_xTimerIsTimerActiveImpl:
    b MPU_xTimerIsTimerActiveImpl

    PUBWEAK MPU_xTimerGetTimerDaemonTaskHandleImpl
MPU_xTimerGetTimerDaemonTaskHandleImpl:
    b MPU_xTimerGetTimerDaemonTaskHandleImpl

    PUBWEAK MPU_xTimerGenericCommandFromTaskImpl
MPU_xTimerGenericCommandFromTaskImpl:
    b MPU_xTimerGenericCommandFromTaskImpl

    PUBWEAK MPU_pcTimerGetNameImpl
MPU_pcTimerGetNameImpl:
    b MPU_pcTimerGetNameImpl

    PUBWEAK MPU_vTimerSetReloadModeImpl
MPU_vTimerSetReloadModeImpl:
    b MPU_vTimerSetReloadModeImpl

    PUBWEAK MPU_xTimerGetReloadModeImpl
MPU_xTimerGetReloadModeImpl:
    b MPU_xTimerGetReloadModeImpl

    PUBWEAK MPU_uxTimerGetReloadModeImpl
MPU_uxTimerGetReloadModeImpl:
    b MPU_uxTimerGetReloadModeImpl

    PUBWEAK MPU_xTimerGetPeriodImpl
MPU_xTimerGetPeriodImpl:
    b MPU_xTimerGetPeriodImpl

    PUBWEAK MPU_xTimerGetExpiryTimeImpl
MPU_xTimerGetExpiryTimeImpl:
    b MPU_xTimerGetExpiryTimeImpl

    PUBWEAK MPU_xEventGroupWaitBitsImpl
MPU_xEventGroupWaitBitsImpl:
    b MPU_xEventGroupWaitBitsImpl

    PUBWEAK MPU_xEventGroupClearBitsImpl
MPU_xEventGroupClearBitsImpl:
    b MPU_xEventGroupClearBitsImpl

    PUBWEAK MPU_xEventGroupSetBitsImpl
MPU_xEventGroupSetBitsImpl:
    b MPU_xEventGroupSetBitsImpl

    PUBWEAK MPU_xEventGroupSyncImpl
MPU_xEventGroupSyncImpl:
    b MPU_xEventGroupSyncImpl

    PUBWEAK MPU_uxEventGroupGetNumberImpl
MPU_uxEventGroupGetNumberImpl:
    b MPU_uxEventGroupGetNumberImpl

    PUBWEAK MPU_vEventGroupSetNumberImpl
MPU_vEventGroupSetNumberImpl:
    b MPU_vEventGroupSetNumberImpl

    PUBWEAK MPU_xStreamBufferSendImpl
MPU_xStreamBufferSendImpl:
    b MPU_xStreamBufferSendImpl

    PUBWEAK MPU_xStreamBufferReceiveImpl
MPU_xStreamBufferReceiveImpl:
    b MPU_xStreamBufferReceiveImpl

    PUBWEAK MPU_xStreamBufferIsFullImpl
MPU_xStreamBufferIsFullImpl:
    b MPU_xStreamBufferIsFullImpl

    PUBWEAK MPU_xStreamBufferIsEmptyImpl
MPU_xStreamBufferIsEmptyImpl:
    b MPU_xStreamBufferIsEmptyImpl

    PUBWEAK MPU_xStreamBufferSpacesAvailableImpl
MPU_xStreamBufferSpacesAvailableImpl:
    b MPU_xStreamBufferSpacesAvailableImpl

    PUBWEAK MPU_xStreamBufferBytesAvailableImpl
MPU_xStreamBufferBytesAvailableImpl:
    b MPU_xStreamBufferBytesAvailableImpl

    PUBWEAK MPU_xStreamBufferSetTriggerLevelImpl
MPU_xStreamBufferSetTriggerLevelImpl:
    b MPU_xStreamBufferSetTriggerLevelImpl

    PUBWEAK MPU_xStreamBufferNextMessageLengthBytesImpl
MPU_xStreamBufferNextMessageLengthBytesImpl:
    b MPU_xStreamBufferNextMessageLengthBytesImpl

/*-----------------------------------------------------------*/

#endif /* #if ( configUSE_MPU_WRAPPERS_V1 == 0 ) */

    END
