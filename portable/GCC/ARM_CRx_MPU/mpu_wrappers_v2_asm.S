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

/*---------------------------------------------------------------------------*/

    .arm
    .syntax unified
    .section freertos_system_calls
#define FREERTOS_ASSEMBLY
    #include "FreeRTOSConfig.h"
    #include "portmacro_asm.h"
    #include "mpu_syscall_numbers.h"
#undef FREERTOS_ASSEMBLY

/* ------------------ Start of Port Specific System Calls ------------------ */

/**
 * Function: void vPortYield
 * Inputs:      VOID
*/
.align 4
.global vPortYield
.type vPortYield, %function
vPortYield:
    /* Make the SVC to swap tasks */
    SVC     #portSVC_YIELD
    /* After yielding to another task, resume executing the calling task */
    BX  LR

/*-------------------------------------------------------------------------------*/
/* vPortSystemCallExit */
.align 4
.global vPortSystemCallExit
.type vPortSystemCallExit, %function
vPortSystemCallExit:
    /* Make the SVC to exit a system call */
    SVC     #portSVC_SYSTEM_CALL_EXIT
    /* After performing the requested FreeRTOS API, return to the calling task */
    BX      LR

/*-------------------------------------------------------------------------------*/
/**
 * Function: BaseType_t xPortIsPrivileged
 * Inputs:      VOID
*/
.align 4
.weak xPortIsPrivileged
.type xPortIsPrivileged, %function
xPortIsPrivileged:
    /* Load value of SPSR into R0 */
    MRS     R0, CPSR
    /* Get the relevant mode bits */
    AND     R0, R0, #0x1F
    /* Check if we're in user mode */
    CMP     R0, #USER_MODE
    /* If we are in user mode set R0 to 0 for the return */
    MOVEQ   R0, #0x0
    /* Otherwise set R0 to 1 for the return */
    MOVNE   R0, #0x01
    BLX      LR

/*-------------------------------------------------------------------------------*/
/**
 * Function: UBaseType_t ulPortCountLeadingZeros
 * Inputs:      UBaseType_t ulBitmap
*/
.align 4
.weak ulPortCountLeadingZeros
.type ulPortCountLeadingZeros, %function
ulPortCountLeadingZeros:
    /* Count the leading zeros and return in R0 */
    CLZ     R0, R0
    BX      LR

/* ------------------- End of Port Specific System Calls ------------------- */

.macro processorInUserMode
    /* Push R0 before using it */
    PUSH    {R0}
    /* Load value of SPSR into R0 */
    MRS     R0, CPSR
    /* Get the relevant mode bits */
    AND     R0, R0, #0x1F
    /* Determine if the CPU is in user mode */
    CMP     R0, #USER_MODE
    /* Restore the pushed register */
    POP     {R0}
.endm

/*---------------------------------------------------------------------------*/

.extern MPU_xTaskGetTickCountImpl
/**
 * Function: TickType_t MPU_xTaskGetTickCount
 * Inputs:     void - No Inputs
*/
.align 4
.global MPU_xTaskGetTickCount
.type MPU_xTaskGetTickCount, function
MPU_xTaskGetTickCount:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xTaskGetTickCount
    B       MPU_xTaskGetTickCountImpl

/*---------------------------------------------------------------------------*/

.extern MPU_uxTaskGetNumberOfTasksImpl
/**
 * Function: UBaseType_t MPU_uxTaskGetNumberOfTasks
 * Inputs:     void - No Inputs
*/
.align 4
.global MPU_uxTaskGetNumberOfTasks
.type MPU_uxTaskGetNumberOfTasks, function
MPU_uxTaskGetNumberOfTasks:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_uxTaskGetNumberOfTasks
    B      MPU_uxTaskGetNumberOfTasksImpl

/*---------------------------------------------------------------------------*/

.extern MPU_vTaskSetTimeOutStateImpl
/**
 * Function: void MPU_vTaskSetTimeOutState
 * Inputs:     TimeOut_t * const pxTimeOut
*/
.align 4
.global MPU_vTaskSetTimeOutState
.type MPU_vTaskSetTimeOutState, function
MPU_vTaskSetTimeOutState:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_vTaskSetTimeOutState
    B       MPU_vTaskSetTimeOutStateImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xTaskCheckForTimeOutImpl
/**
 * Function: BaseType_t MPU_xTaskCheckForTimeOut
 * Inputs:     TimeOut_t * const pxTimeOut
 * Inputs:     TickType_t * const pxTicksToWait
*/
.align 4
.global MPU_xTaskCheckForTimeOut
.type MPU_xTaskCheckForTimeOut, function
MPU_xTaskCheckForTimeOut:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xTaskCheckForTimeOut
    B       MPU_xTaskCheckForTimeOutImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xQueueGenericSendImpl
/**
 * Function: BaseType_t MPU_xQueueGenericSend
 * Inputs:     QueueHandle_t xQueue
 * Inputs:     const void * const pvItemToQueue
 * Inputs:     TickType_t xTicksToWait
 * Inputs:     constBaseType_t xCopyPosition
*/
.align 4
.global MPU_xQueueGenericSend
.type MPU_xQueueGenericSend, function
MPU_xQueueGenericSend:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xQueueGenericSend
    B       MPU_xQueueGenericSendImpl

/*---------------------------------------------------------------------------*/

.extern MPU_uxQueueMessagesWaitingImpl
/**
 * Function: UBaseType_t MPU_uxQueueMessagesWaiting
 * Inputs:     const QueueHandle_t xQueue
*/
.align 4
.global MPU_uxQueueMessagesWaiting
.type MPU_uxQueueMessagesWaiting, function
MPU_uxQueueMessagesWaiting:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_uxQueueMessagesWaiting
    B       MPU_uxQueueMessagesWaitingImpl

/*---------------------------------------------------------------------------*/

.extern MPU_uxQueueSpacesAvailableImpl
/**
 * Function: UBaseType_t MPU_uxQueueSpacesAvailable
 * Inputs:     const QueueHandle_t xQueue
*/
.align 4
.global MPU_uxQueueSpacesAvailable
.type MPU_uxQueueSpacesAvailable, function
MPU_uxQueueSpacesAvailable:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_uxQueueSpacesAvailable
    B       MPU_uxQueueSpacesAvailableImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xQueueReceiveImpl
/**
 * Function: BaseType_t MPU_xQueueReceive
 * Inputs:     QueueHandle_t xQueue
 * Inputs:     void * const pvBuffer
 * Inputs:     TickType_t xTicksToWait
*/
.align 4
.global MPU_xQueueReceive
.type MPU_xQueueReceive, function
MPU_xQueueReceive:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xQueueReceive
    B       MPU_xQueueReceiveImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xQueuePeekImpl
/**
 * Function: BaseType_t MPU_xQueuePeek
 * Inputs:     QueueHandle_t xQueue
 * Inputs:     void * const pvBuffer
 * Inputs:     TickType_t xTicksToWait
*/
.align 4
.global MPU_xQueuePeek
.type MPU_xQueuePeek, function
MPU_xQueuePeek:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xQueuePeek
    B       MPU_xQueuePeekImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xQueueSemaphoreTakeImpl
/**
 * Function: BaseType_t MPU_xQueueSemaphoreTake
 * Inputs:     QueueHandle_t xQueue
 * Inputs:     TickType_t xTicksToWait
*/
.align 4
.global MPU_xQueueSemaphoreTake
.type MPU_xQueueSemaphoreTake, function
MPU_xQueueSemaphoreTake:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xQueueSemaphoreTake
    B       MPU_xQueueSemaphoreTakeImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xEventGroupWaitBitsImpl
/**
 * Function: EventBits_t MPU_xEventGroupWaitBitsEntry
 * Inputs:     const xEventGroupWaitBitsParams_t * pxParams
*/
.align 4
.global MPU_xEventGroupWaitBitsEntry
.type MPU_xEventGroupWaitBitsEntry, function
MPU_xEventGroupWaitBitsEntry:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xEventGroupWaitBits
    B       MPU_xEventGroupWaitBitsImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xEventGroupClearBitsImpl
/**
 * Function: EventBits_t MPU_xEventGroupClearBits
 * Inputs:     EventGroupHandle_t xEventGroup
 * Inputs:     constEventBits_t uxBitsToClear
*/
.align 4
.global MPU_xEventGroupClearBits
.type MPU_xEventGroupClearBits, function
MPU_xEventGroupClearBits:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xEventGroupClearBits
    B       MPU_xEventGroupClearBitsImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xEventGroupSetBitsImpl
/**
 * Function: EventBits_t MPU_xEventGroupSetBits
 * Inputs:     EventGroupHandle_t xEventGroup
 * Inputs:     constEventBits_t uxBitsToSet
*/
.align 4
.global MPU_xEventGroupSetBits
.type MPU_xEventGroupSetBits, function
MPU_xEventGroupSetBits:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xEventGroupSetBits
    B       MPU_xEventGroupSetBitsImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xEventGroupSyncImpl
/**
 * Function: EventBits_t MPU_xEventGroupSync
 * Inputs:     EventGroupHandle_t xEventGroup
 * Inputs:     constEventBits_t uxBitsToSet
 * Inputs:     constEventBits_t uxBitsToWaitFor
 * Inputs:     TickType_t xTicksToWait
*/
.align 4
.global MPU_xEventGroupSync
.type MPU_xEventGroupSync, function
MPU_xEventGroupSync:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xEventGroupSync
    B       MPU_xEventGroupSyncImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xStreamBufferSendImpl
/**
 * Function: size_t MPU_xStreamBufferSend
 * Inputs:     StreamBufferHandle_t xStreamBuffer
 * Inputs:     const void * pvTxData
 * Inputs:     size_t xDataLengthBytes
 * Inputs:     TickType_t xTicksToWait
*/
.align 4
.global MPU_xStreamBufferSend
.type MPU_xStreamBufferSend, function
MPU_xStreamBufferSend:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xStreamBufferSend
    B       MPU_xStreamBufferSendImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xStreamBufferReceiveImpl
/**
 * Function: size_t MPU_xStreamBufferReceive
 * Inputs:     StreamBufferHandle_t xStreamBuffer
 * Inputs:     void * pvRxData
 * Inputs:     size_t xBufferLengthBytes
 * Inputs:     TickType_t xTicksToWait
*/
.align 4
.global MPU_xStreamBufferReceive
.type MPU_xStreamBufferReceive, function
MPU_xStreamBufferReceive:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xStreamBufferReceive
    B       MPU_xStreamBufferReceiveImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xStreamBufferIsFullImpl
/**
 * Function: BaseType_t MPU_xStreamBufferIsFull
 * Inputs:     StreamBufferHandle_t xStreamBuffer
*/
.align 4
.global MPU_xStreamBufferIsFull
.type MPU_xStreamBufferIsFull, function
MPU_xStreamBufferIsFull:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xStreamBufferIsFull
    B       MPU_xStreamBufferIsFullImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xStreamBufferIsEmptyImpl
/**
 * Function: BaseType_t MPU_xStreamBufferIsEmpty
 * Inputs:     StreamBufferHandle_t xStreamBuffer
*/
.align 4
.global MPU_xStreamBufferIsEmpty
.type MPU_xStreamBufferIsEmpty, function
MPU_xStreamBufferIsEmpty:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xStreamBufferIsEmpty
    B       MPU_xStreamBufferIsEmptyImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xStreamBufferSpacesAvailableImpl
/**
 * Function: size_t MPU_xStreamBufferSpacesAvailable
 * Inputs:     StreamBufferHandle_t xStreamBuffer
*/
.align 4
.global MPU_xStreamBufferSpacesAvailable
.type MPU_xStreamBufferSpacesAvailable, function
MPU_xStreamBufferSpacesAvailable:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xStreamBufferSpacesAvailable
    B       MPU_xStreamBufferSpacesAvailableImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xStreamBufferBytesAvailableImpl
/**
 * Function: size_t MPU_xStreamBufferBytesAvailable
 * Inputs:     StreamBufferHandle_t xStreamBuffer
*/
.align 4
.global MPU_xStreamBufferBytesAvailable
.type MPU_xStreamBufferBytesAvailable, function
MPU_xStreamBufferBytesAvailable:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xStreamBufferBytesAvailable
    B       MPU_xStreamBufferBytesAvailableImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xStreamBufferSetTriggerLevelImpl
/**
 * Function: BaseType_t MPU_xStreamBufferSetTriggerLevel
 * Inputs:     StreamBufferHandle_t xStreamBuffer
 * Inputs:     size_t xTriggerLevel
*/
.align 4
.global MPU_xStreamBufferSetTriggerLevel
.type MPU_xStreamBufferSetTriggerLevel, function
MPU_xStreamBufferSetTriggerLevel:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xStreamBufferSetTriggerLevel
    B       MPU_xStreamBufferSetTriggerLevelImpl

/*---------------------------------------------------------------------------*/

.extern MPU_xStreamBufferNextMessageLengthBytesImpl
/**
 * Function: size_t MPU_xStreamBufferNextMessageLengthBytes
 * Inputs:     StreamBufferHandle_t xStreamBuffer
*/
.align 4
.global MPU_xStreamBufferNextMessageLengthBytes
.type MPU_xStreamBufferNextMessageLengthBytes, function
MPU_xStreamBufferNextMessageLengthBytes:
    processorInUserMode
    SVCEQ   #SYSTEM_CALL_xStreamBufferNextMessageLengthBytes
    B       MPU_xStreamBufferNextMessageLengthBytesImpl

/*---------------------------------------------------------------------------*/

#if INCLUDE_xTaskDelayUntil == 1
    .extern MPU_xTaskDelayUntilImpl
    /**
     * Function: TaskHandle_t MPU_xTaskDelayUntil
     * Inputs:     TickType_t * const pxPreviousWakeTime
     * Inputs:     constTickType_t xTimeIncrement
    */
    .align 4
    .global MPU_xTaskDelayUntil
    .type MPU_xTaskDelayUntil, function
    MPU_xTaskDelayUntil:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskDelayUntil
        B       MPU_xTaskDelayUntilImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_xTaskDelayUntil == 1 ) */

#if INCLUDE_xTaskAbortDelay == 1

/*---------------------------------------------------------------------------*/

    .extern MPU_xTaskAbortDelayImpl
    /**
     * Function: TaskHandle_t MPU_xTaskAbortDelay
     * Inputs:     TaskHandle_t xTask
    */
    .align 4
    .global MPU_xTaskAbortDelay
    .type MPU_xTaskAbortDelay, function
    MPU_xTaskAbortDelay:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskAbortDelay
        B       MPU_xTaskAbortDelayImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_xTaskAbortDelay == 1 ) */

#if INCLUDE_vTaskDelay == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_vTaskDelayImpl
    /**
     * Function: void MPU_vTaskDelay
     * Inputs:     const TickType_t xTicksToDelay
    */
    .align 4
    .global MPU_vTaskDelay
    .type MPU_vTaskDelay, function
    MPU_vTaskDelay:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vTaskDelay
        B       MPU_vTaskDelayImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_vTaskDelay == 1 ) */

#if INCLUDE_uxTaskPriorityGet == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_uxTaskPriorityGetImpl
    /**
     * Function: UBaseType_t MPU_uxTaskPriorityGet
     * Inputs:     const TaskHandle_t xTask
    */
    .align 4
    .global MPU_uxTaskPriorityGet
    .type MPU_uxTaskPriorityGet, function
    MPU_uxTaskPriorityGet:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_uxTaskPriorityGet
        B       MPU_uxTaskPriorityGetImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_uxTaskPriorityGet == 1 ) */

#if INCLUDE_eTaskGetState == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_eTaskGetStateImpl
    /**
     * Function: eTaskState MPU_eTaskGetState
     * Inputs:     TaskHandle_t xTask
    */
    .align 4
    .global MPU_eTaskGetState
    .type MPU_eTaskGetState, function
    MPU_eTaskGetState:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_eTaskGetState
        B       MPU_eTaskGetStateImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_eTaskGetState == 1 ) */

#if configUSE_TRACE_FACILITY == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_vTaskGetInfoImpl
    /**
     * Function: void MPU_vTaskGetInfo
     * Inputs:     TaskHandle_t xTask
     * Inputs:     TaskStatus_t* pxTaskStatus
     * Inputs:     TaskHandle_t xGetFreeStackSpace
     * Inputs:     eTaskState eState
    */
    .align 4
    .global MPU_vTaskGetInfo
    .type MPU_vTaskGetInfo, function
    MPU_vTaskGetInfo:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vTaskGetInfo
        B       MPU_vTaskGetInfoImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_uxTaskGetSystemStateImpl
    /**
     * Function: UBaseType_t MPU_uxTaskGetSystemState
     * Inputs:     TaskStatus_t * const pxTaskStatusArray
     * Inputs:     constUBaseType_t uxArraySize
     * Inputs:     configRUN_TIME_COUNTER_TYPE* const pulTotalRunTime
    */
    .align 4
    .global MPU_uxTaskGetSystemState
    .type MPU_uxTaskGetSystemState, function
    MPU_uxTaskGetSystemState:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_uxTaskGetSystemState
        B       MPU_uxTaskGetSystemStateImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_uxEventGroupGetNumberImpl
    /**
     * Function: UBaseType_t MPU_uxEventGroupGetNumber
     * Inputs:     void * xEventGroup
    */
    .align 4
    .global MPU_uxEventGroupGetNumber
    .type MPU_uxEventGroupGetNumber, function
    MPU_uxEventGroupGetNumber:
    processorInUserMode
        SVCEQ   #SYSTEM_CALL_uxEventGroupGetNumber
        B       MPU_uxEventGroupGetNumberImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_vEventGroupSetNumberImpl
    /**
     * Function: void MPU_vEventGroupSetNumber
     * Inputs:     void * xEventGroup
     * Inputs:     UBaseType_t uxEventGroupNumber
    */
    .align 4
    .global MPU_vEventGroupSetNumber
    .type MPU_vEventGroupSetNumber, function
    MPU_vEventGroupSetNumber:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vEventGroupSetNumber
        B       MPU_vEventGroupSetNumberImpl

    /*-----------------------------------------------------------------------*/
#endif /* if ( configUSE_TRACE_FACILITY == 1 ) */

#if INCLUDE_xTaskGetIdleTaskHandle == 1

    /*-----------------------------------------------------------------------*/
    .extern MPU_xTaskGetIdleTaskHandleImpl
    /**
     * Function: TaskHandle_t MPU_xTaskGetIdleTaskHandle
     * Inputs:     void - No Inputs
    */
    .align 4
    .global MPU_xTaskGetIdleTaskHandle
    .type MPU_xTaskGetIdleTaskHandle, function
    MPU_xTaskGetIdleTaskHandle:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskGetIdleTaskHandle
        B       MPU_xTaskGetIdleTaskHandleImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_xTaskGetIdleTaskHandle == 1 ) */

#if INCLUDE_vTaskSuspend == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_vTaskSuspendImpl
    /**
     * Function: void MPU_vTaskSuspend
     * Inputs:     TaskHandle_t xTaskToSuspend
    */
    .align 4
    .global MPU_vTaskSuspend
    .type MPU_vTaskSuspend, function
    MPU_vTaskSuspend:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vTaskSuspend
        B       MPU_vTaskSuspendImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_vTaskResumeImpl
    /**
     * Function: void MPU_vTaskResume
     * Inputs:     TaskHandle_t xTaskToResume
    */
    .align 4
    .global MPU_vTaskResume
    .type MPU_vTaskResume, function
    MPU_vTaskResume:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vTaskResume
        B       MPU_vTaskResumeImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_vTaskSuspend == 1 ) */

#if configGENERATE_RUN_TIME_STATS == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_ulTaskGetRunTimeCounterImpl
    /**
     * Function: configRUN_TIME_COUNTER_TYPE MPU_ulTaskGetRunTimeCounter
     * Inputs:     const TaskHandle_t xTask
    */
    .align 4
    .global MPU_ulTaskGetRunTimeCounter
    .type MPU_ulTaskGetRunTimeCounter, function
    MPU_ulTaskGetRunTimeCounter:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_ulTaskGetRunTimeCounter
        B       MPU_ulTaskGetRunTimeCounterImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_ulTaskGetRunTimePercentImpl
    /**
     * Function: configRUN_TIME_COUNTER_TYPE MPU_ulTaskGetRunTimePercent
     * Inputs:     const TaskHandle_t xTask
    */
    .align 4
    .global MPU_ulTaskGetRunTimePercent
    .type MPU_ulTaskGetRunTimePercent, function
    MPU_ulTaskGetRunTimePercent:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_ulTaskGetRunTimePercent
        B       MPU_ulTaskGetRunTimePercentImpl

    /*-----------------------------------------------------------------------*/

    #if INCLUDE_xTaskGetIdleTaskHandle == 1

        /*-------------------------------------------------------------------*/

        .extern MPU_ulTaskGetIdleRunTimePercentImpl
        /**
         * Function: configRUN_TIME_COUNTER_TYPE MPU_ulTaskGetIdleRunTimePercent
         * Inputs:     void
        */
        .align 4
        .global MPU_ulTaskGetIdleRunTimePercent
        .type MPU_ulTaskGetIdleRunTimePercent, function
        MPU_ulTaskGetIdleRunTimePercent:
            processorInUserMode
            SVCEQ   #SYSTEM_CALL_ulTaskGetIdleRunTimePercent
            B       MPU_ulTaskGetIdleRunTimePercentImpl

        /*-------------------------------------------------------------------*/

        .extern MPU_ulTaskGetIdleRunTimeCounterImpl
        /**
         * Function: configRUN_TIME_COUNTER_TYPE MPU_ulTaskGetIdleRunTimeCounter
         * Inputs:     void - No Inputs
        */
        .align 4
        .global MPU_ulTaskGetIdleRunTimeCounter
        .type MPU_ulTaskGetIdleRunTimeCounter, function
        MPU_ulTaskGetIdleRunTimeCounter:
            processorInUserMode
            SVCEQ   #SYSTEM_CALL_ulTaskGetIdleRunTimeCounter
            B       MPU_ulTaskGetIdleRunTimeCounterImpl

        /*-------------------------------------------------------------------*/

    #endif /* if ( ( configGENERATE_RUN_TIME_STATS == 1 ) && ( INCLUDE_xTaskGetIdleTaskHandle == 1 ) ) */
#endif /* configGENERATE_RUN_TIME_STATS */

#if configUSE_APPLICATION_TASK_TAG == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_vTaskSetApplicationTaskTagImpl
    /**
     * Function: void MPU_vTaskSetApplicationTaskTag
     * Inputs:     TaskHandle_t xTask
     * Inputs:     TaskHookFunction_tpxHookFunction
    */
    .align 4
    .global MPU_vTaskSetApplicationTaskTag
    .type MPU_vTaskSetApplicationTaskTag, function
    MPU_vTaskSetApplicationTaskTag:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vTaskSetApplicationTaskTag
        B       MPU_vTaskSetApplicationTaskTagImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTaskGetApplicationTaskTagImpl
    /**
     * Function: TaskHookFunction_t MPU_xTaskGetApplicationTaskTag
     * Inputs:     TaskHandle_t xTask
    */
    .align 4
    .global MPU_xTaskGetApplicationTaskTag
    .type MPU_xTaskGetApplicationTaskTag, function
    MPU_xTaskGetApplicationTaskTag:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskGetApplicationTaskTag
        B       MPU_xTaskGetApplicationTaskTagImpl

    /*-----------------------------------------------------------------------*/
#endif /* if ( configUSE_APPLICATION_TASK_TAG == 1 ) */

#if configNUM_THREAD_LOCAL_STORAGE_POINTERS != 0

    /*-----------------------------------------------------------------------*/

    .extern MPU_vTaskSetThreadLocalStoragePointerImpl
    /**
     * Function: void MPU_vTaskSetThreadLocalStoragePointer
     * Inputs:     TaskHandle_t xTaskToSet
     * Inputs:     TaskHandle_t xIndex
     * Inputs:     void * pvValue
    */
    .align 4
    .global MPU_vTaskSetThreadLocalStoragePointer
    .type MPU_vTaskSetThreadLocalStoragePointer, function
    MPU_vTaskSetThreadLocalStoragePointer:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vTaskSetThreadLocalStoragePointer
        B       MPU_vTaskSetThreadLocalStoragePointerImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_pvTaskGetThreadLocalStoragePointerImpl
    /**
     * Function: void * MPU_pvTaskGetThreadLocalStoragePointer
     * Inputs:     TaskHandle_t xTaskToQuery
     * Inputs:     TaskHandle_t xIndex
    */
    .align 4
    .global MPU_pvTaskGetThreadLocalStoragePointer
    .type MPU_pvTaskGetThreadLocalStoragePointer, function
    MPU_pvTaskGetThreadLocalStoragePointer:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_pvTaskGetThreadLocalStoragePointer
        B       MPU_pvTaskGetThreadLocalStoragePointerImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( configNUM_THREAD_LOCAL_STORAGE_POINTERS != 0 ) */

#if INCLUDE_uxTaskGetStackHighWaterMark == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_uxTaskGetStackHighWaterMarkImpl
    /**
     * Function: UBaseType_t MPU_uxTaskGetStackHighWaterMark
     * Inputs:     TaskHandle_t xTask
    */
    .align 4
    .global MPU_uxTaskGetStackHighWaterMark
    .type MPU_uxTaskGetStackHighWaterMark, function
    MPU_uxTaskGetStackHighWaterMark:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_uxTaskGetStackHighWaterMark
        B       MPU_uxTaskGetStackHighWaterMarkImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_uxTaskGetStackHighWaterMark == 1 ) */


#if INCLUDE_uxTaskGetStackHighWaterMark == 2

    /*-----------------------------------------------------------------------*/

    .extern MPU_uxTaskGetStackHighWaterMark2Impl
    /**
     * Function: configSTACK_DEPTH_TYPE MPU_uxTaskGetStackHighWaterMark2
     * Inputs:     TaskHandle_t xTask
    */
    .align 4
    .global MPU_uxTaskGetStackHighWaterMark2
    .type MPU_uxTaskGetStackHighWaterMark2, function
    MPU_uxTaskGetStackHighWaterMark2:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_uxTaskGetStackHighWaterMark2
        B       MPU_uxTaskGetStackHighWaterMark2Impl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_uxTaskGetStackHighWaterMark2 == 1 ) */


#if INCLUDE_xTaskGetCurrentTaskHandle == 1 || configUSE_MUTEXES == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTaskGetCurrentTaskHandleImpl
    /**
     * Function: TaskHandle_t MPU_xTaskGetCurrentTaskHandle
     * Inputs:     void - No Inputs
    */
    .align 4
    .global MPU_xTaskGetCurrentTaskHandle
    .type MPU_xTaskGetCurrentTaskHandle, function
    MPU_xTaskGetCurrentTaskHandle:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskGetCurrentTaskHandle
        B       MPU_xTaskGetCurrentTaskHandleImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( ( INCLUDE_xTaskGetCurrentTaskHandle == 1 ) || ( configUSE_MUTEXES == 1 ) ) */

#if INCLUDE_xTaskGetSchedulerState == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTaskGetSchedulerStateImpl
    /**
     * Function: TaskHandle_t MPU_xTaskGetSchedulerState
     * Inputs:     void - No Inputs
    */
    .align 4
    .global MPU_xTaskGetSchedulerState
    .type MPU_xTaskGetSchedulerState, function
    MPU_xTaskGetSchedulerState:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskGetSchedulerState
        B       MPU_xTaskGetSchedulerStateImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( INCLUDE_xTaskGetSchedulerState == 1 ) */

#if configUSE_MUTEXES == 1 && INCLUDE_xSemaphoreGetMutexHolder

    /*-----------------------------------------------------------------------*/

    .extern MPU_xQueueGetMutexHolderImpl
    /**
     * Function: TaskHandle_t MPU_xQueueGetMutexHolder
     * Inputs:     QueueHandle_t xSemaphore
    */
    .align 4
    .global MPU_xQueueGetMutexHolder
    .type MPU_xQueueGetMutexHolder, function
    MPU_xQueueGetMutexHolder:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xQueueGetMutexHolder
        B       MPU_xQueueGetMutexHolderImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( ( configUSE_MUTEXES == 1 ) && ( INCLUDE_xSemaphoreGetMutexHolder == 1 ) ) */

#if configUSE_RECURSIVE_MUTEXES == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_xQueueTakeMutexRecursiveImpl
    /**
     * Function: TaskHandle_t MPU_xQueueTakeMutexRecursive
     * Inputs:     QueueHandle_t xMutex
     * Inputs:     TickType_t xTicksToWait
    */
    .align 4
    .global MPU_xQueueTakeMutexRecursive
    .type MPU_xQueueTakeMutexRecursive, function
    MPU_xQueueTakeMutexRecursive:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xQueueTakeMutexRecursive
        B       MPU_xQueueTakeMutexRecursiveImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xQueueGiveMutexRecursiveImpl
    /**
     * Function: TaskHandle_t MPU_xQueueGiveMutexRecursive
     * Inputs:     QueueHandle_t pxMutex
    */
    .align 4
    .global MPU_xQueueGiveMutexRecursive
    .type MPU_xQueueGiveMutexRecursive, function
    MPU_xQueueGiveMutexRecursive:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xQueueGiveMutexRecursive
        B       MPU_xQueueGiveMutexRecursiveImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( configUSE_RECURSIVE_MUTEXES == 1 ) */

#if configUSE_QUEUE_SETS == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_xQueueSelectFromSetImpl
    /**
     * Function: QueueSetMemberHandle_t MPU_xQueueSelectFromSet
     * Inputs:     QueueSetHandle_t xQueueSet
     * Inputs:     constTickType_t xTicksToWait
    */
    .align 4
    .global MPU_xQueueSelectFromSet
    .type MPU_xQueueSelectFromSet, function
    MPU_xQueueSelectFromSet:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xQueueSelectFromSet
        B       MPU_xQueueSelectFromSetImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xQueueAddToSetImpl
    /**
     * Function: TaskHandle_t MPU_xQueueAddToSet
     * Inputs:     QueueSetMemberHandle_t xQueueOrSemaphore
     * Inputs:     QueueSetHandle_t xQueueSet
    */
    .align 4
    .global MPU_xQueueAddToSet
    .type MPU_xQueueAddToSet, function
    MPU_xQueueAddToSet:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xQueueAddToSet
        B       MPU_xQueueAddToSetImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( configUSE_QUEUE_SETS == 1 ) */

#if configQUEUE_REGISTRY_SIZE == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_vQueueAddToRegistryImpl
    /**
     * Function: void MPU_vQueueAddToRegistry
     * Inputs:     QueueHandle_t xQueue
     * Inputs:     constchar * pcName
    */
    .align 4
    .global MPU_vQueueAddToRegistry
    .type MPU_vQueueAddToRegistry, function
    MPU_vQueueAddToRegistry:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vQueueAddToRegistry
        B       MPU_vQueueAddToRegistryImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_vQueueUnregisterQueueImpl
    /**
     * Function: void MPU_vQueueUnregisterQueue
     * Inputs:     QueueHandle_t xQueue
    */
    .align 4
    .global MPU_vQueueUnregisterQueue
    .type MPU_vQueueUnregisterQueue, function
    MPU_vQueueUnregisterQueue:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vQueueUnregisterQueue
        B       MPU_vQueueUnregisterQueueImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_pcQueueGetNameImpl
    /**
     * Function: const char * MPU_pcQueueGetName
     * Inputs:     QueueHandle_t xQueue
    */
    .align 4
    .global MPU_pcQueueGetName
    .type MPU_pcQueueGetName, function
    MPU_pcQueueGetName:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_pcQueueGetName
        B       MPU_pcQueueGetNameImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( configQUEUE_REGISTRY_SIZE > 0 ) */

#if configUSE_TIMERS == 1

    /*-----------------------------------------------------------------------*/

    .extern MPU_pvTimerGetTimerIDImpl
    /**
     * Function: void * MPU_pvTimerGetTimerID
     * Inputs:     const TimerHandle_t xTimer
    */
    .align 4
    .global MPU_pvTimerGetTimerID
    .type MPU_pvTimerGetTimerID, function
    MPU_pvTimerGetTimerID:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_pvTimerGetTimerID
        B       MPU_pvTimerGetTimerIDImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_vTimerSetTimerIDImpl
    /**
     * Function: void MPU_vTimerSetTimerID
     * Inputs:     TimerHandle_t xTimer
     * Inputs:     void * pvNewID
    */
    .align 4
    .global MPU_vTimerSetTimerID
    .type MPU_vTimerSetTimerID, function
    MPU_vTimerSetTimerID:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vTimerSetTimerID
        B       MPU_vTimerSetTimerIDImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTimerIsTimerActiveImpl
    /**
     * Function: TaskHandle_t MPU_xTimerIsTimerActive
     * Inputs:     TimerHandle_t xTimer
    */
    .align 4
    .global MPU_xTimerIsTimerActive
    .type MPU_xTimerIsTimerActive, function
    MPU_xTimerIsTimerActive:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTimerIsTimerActive
        B       MPU_xTimerIsTimerActiveImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTimerGetTimerDaemonTaskHandleImpl
    /**
     * Function: TaskHandle_t MPU_xTimerGetTimerDaemonTaskHandle
     * Inputs:     void - No Inputs
    */
    .align 4
    .global MPU_xTimerGetTimerDaemonTaskHandle
    .type MPU_xTimerGetTimerDaemonTaskHandle, function
    MPU_xTimerGetTimerDaemonTaskHandle:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTimerGetTimerDaemonTaskHandle
        B       MPU_xTimerGetTimerDaemonTaskHandleImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTimerGenericCommandFromTaskImpl
    /**
    * Function: TaskHandle_t MPU_xTimerGenericCommandFromTaskEntry
    * Inputs:     const xTimerGenericCommandParams_t * pxParams
    */
    .align 4
    .global MPU_xTimerGenericCommandFromTaskEntry
    .type MPU_xTimerGenericCommandFromTaskEntry, function
    MPU_xTimerGenericCommandFromTaskEntry:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTimerGenericCommandFromTask
        B       MPU_xTimerGenericCommandFromTaskImpl

    /*-----------------------------------------------------------------------*/


    .extern MPU_pcTimerGetNameImpl
    /**
     * Function: const char * MPU_pcTimerGetName
     * Inputs:     TimerHandle_t xTimer
    */
    .align 4
    .global MPU_pcTimerGetName
    .type MPU_pcTimerGetName, function
    MPU_pcTimerGetName:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_pcTimerGetName
        B       MPU_pcTimerGetNameImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_vTimerSetReloadModeImpl
    /**
     * Function: void MPU_vTimerSetReloadMode
     * Inputs:     TimerHandle_t xTimer
     * Inputs:     constBaseType_t uxAutoReload
    */
    .align 4
    .global MPU_vTimerSetReloadMode
    .type MPU_vTimerSetReloadMode, function
    MPU_vTimerSetReloadMode:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_vTimerSetReloadMode
        B       MPU_vTimerSetReloadModeImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTimerGetReloadModeImpl
    /**
     * Function: TaskHandle_t MPU_xTimerGetReloadMode
     * Inputs:     TimerHandle_t xTimer
    */
    .align 4
    .global MPU_xTimerGetReloadMode
    .type MPU_xTimerGetReloadMode, function
    MPU_xTimerGetReloadMode:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTimerGetReloadMode
        B       MPU_xTimerGetReloadModeImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_uxTimerGetReloadModeImpl
    /**
     * Function: UBaseType_t MPU_uxTimerGetReloadMode
     * Inputs:     TimerHandle_t xTimer
    */
    .align 4
    .global MPU_uxTimerGetReloadMode
    .type MPU_uxTimerGetReloadMode, function
    MPU_uxTimerGetReloadMode:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_uxTimerGetReloadMode
        B       MPU_uxTimerGetReloadModeImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTimerGetPeriodImpl
    /**
     * Function: TickType_t MPU_xTimerGetPeriod
     * Inputs:     TimerHandle_t xTimer
    */
    .align 4
    .global MPU_xTimerGetPeriod
    .type MPU_xTimerGetPeriod, function
    MPU_xTimerGetPeriod:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTimerGetPeriod
        B       MPU_xTimerGetPeriodImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTimerGetExpiryTimeImpl
    /**
     * Function: TickType_t MPU_xTimerGetExpiryTime
     * Inputs:     TimerHandle_t xTimer
    */
    .align 4
    .global MPU_xTimerGetExpiryTime
    .type MPU_xTimerGetExpiryTime, function
    MPU_xTimerGetExpiryTime:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTimerGetExpiryTime
        B       MPU_xTimerGetExpiryTimeImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( configUSE_TIMERS == 1 ) */

#if configUSE_TASK_NOTIFICATIONS == 1
    .extern MPU_xTaskGenericNotifyImpl
    /**
    * Function: TaskHandle_t MPU_xTaskGenericNotifyEntry
    * Inputs:      const xTaskGenericNotifyParams_t * pxParams
    */
    .align 4
    .global MPU_xTaskGenericNotifyEntry
    .type MPU_xTaskGenericNotifyEntry, function
    MPU_xTaskGenericNotifyEntry:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskGenericNotify
        B       MPU_xTaskGenericNotifyImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTaskGenericNotifyWaitImpl
    /**
     * Function: TaskHandle_t MPU_xTaskGenericNotifyWaitEntry
     * Inputs:     const xTaskGenericNotifyWaitParams_t * pxParams
    */
    .align 4
    .global MPU_xTaskGenericNotifyWaitEntry
    .type MPU_xTaskGenericNotifyWaitEntry, function
    MPU_xTaskGenericNotifyWaitEntry:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskGenericNotifyWait
        B       MPU_xTaskGenericNotifyWaitImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_ulTaskGenericNotifyTakeImpl
    /**
     * Function: uint32_t MPU_ulTaskGenericNotifyTake
     * Inputs:     UBaseType_t uxIndexToWaitOn
     * Inputs:     TaskHandle_t xClearCountOnExit
     * Inputs:     TickType_t xTicksToWait
    */
    .align 4
    .global MPU_ulTaskGenericNotifyTake
    .type MPU_ulTaskGenericNotifyTake, function
    MPU_ulTaskGenericNotifyTake:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_ulTaskGenericNotifyTake
        B       MPU_ulTaskGenericNotifyTakeImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_xTaskGenericNotifyStateClearImpl
    /**
     * Function: TaskHandle_t MPU_xTaskGenericNotifyStateClear
     * Inputs:     TaskHandle_t xTask
     * Inputs:     UBaseType_t uxIndexToClear
    */
    .align 4
    .global MPU_xTaskGenericNotifyStateClear
    .type MPU_xTaskGenericNotifyStateClear, function
    MPU_xTaskGenericNotifyStateClear:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_xTaskGenericNotifyStateClear
        B       MPU_xTaskGenericNotifyStateClearImpl

    /*-----------------------------------------------------------------------*/

    .extern MPU_ulTaskGenericNotifyValueClearImpl
    /**
     * Function: uint32_t MPU_ulTaskGenericNotifyValueClear
     * Inputs:     TaskHandle_t xTask
     * Inputs:     UBaseType_t uxIndexToClear
     * Inputs:     uint32_t ulBitsToClear
    */
    .align 4
    .global MPU_ulTaskGenericNotifyValueClear
    .type MPU_ulTaskGenericNotifyValueClear, function
    MPU_ulTaskGenericNotifyValueClear:
        processorInUserMode
        SVCEQ   #SYSTEM_CALL_ulTaskGenericNotifyValueClear
        B       MPU_ulTaskGenericNotifyValueClearImpl

    /*-----------------------------------------------------------------------*/

#endif /* if ( configUSE_TASK_NOTIFICATIONS == 1 ) */
