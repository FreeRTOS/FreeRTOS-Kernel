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


#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE
#include "FreeRTOS.h"
#include "syscall.h"
#include "task.h"
#include "queue.h"
#include "trap.h"
#include "timers.h"
#include "x86_64.h"
#include "freertos_serial.h"
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE
#define MAX_SYSCALLS 128

/* Alse file syscall.asm these constants are also defined there */
#define SYSCALL_NUM_writec 0
#define SYSCALL_NUM_xTaskGetTickCount 1
#define SYSCALL_NUM_xTaskDelayUntil 2
#define SYSCALL_NUM_xQueueGenericSend 3
#define SYSCALL_NUM_xQueueReceive 4
#define SYSCALL_NUM_xTimerGenericCommandFromTask 5
#define SYSCALL_NUM_eTaskGetState 6
#define SYSCALL_NUM_pcQueueGetName 7
#define SYSCALL_NUM_pcTimerGetName 8
#define SYSCALL_NUM_pvTimerGetTimerID 9
#define SYSCALL_NUM_ulTaskGenericNotifyTake 10
#define SYSCALL_NUM_ulTaskGenericNotifyValueClear 11
#define SYSCALL_NUM_uxQueueMessagesWaiting 12
#define SYSCALL_NUM_uxQueueSpacesAvailable 13
#define SYSCALL_NUM_uxTaskGetNumberOfTasks 14
#define SYSCALL_NUM_uxTaskGetSystemState 15
#define SYSCALL_NUM_uxTaskPriorityGet 16
#define SYSCALL_NUM_uxTimerGetReloadMode 17
#define SYSCALL_NUM_vQueueAddToRegistry 18
#define SYSCALL_NUM_vQueueUnregisterQueue 19
#define SYSCALL_NUM_vTaskDelay 20
#define SYSCALL_NUM_vTaskGetInfo 21
#define SYSCALL_NUM_vTaskResume 22
#define SYSCALL_NUM_vTaskSetTimeOutState 23
#define SYSCALL_NUM_vTaskSuspend 24
#define SYSCALL_NUM_vTaskSuspendAll 25
#define SYSCALL_NUM_vTimerSetReloadMode 26
#define SYSCALL_NUM_vTimerSetTimerID 27
#define SYSCALL_NUM_xQueueAddToSet 28
#define SYSCALL_NUM_xQueueGiveMutexRecursive 29
#define SYSCALL_NUM_xQueuePeek 30
#define SYSCALL_NUM_xQueueRemoveFromSet 31
#define SYSCALL_NUM_xQueueSelectFromSet 32
#define SYSCALL_NUM_xQueueSemaphoreTake 33
#define SYSCALL_NUM_xQueueTakeMutexRecursive 34
#define SYSCALL_NUM_xTaskCheckForTimeOut 35
#define SYSCALL_NUM_xTaskGenericNotify 36
#define SYSCALL_NUM_xTaskGenericNotifyStateClear 37
#define SYSCALL_NUM_xTaskGenericNotifyWait 38
#define SYSCALL_NUM_xTaskGetCurrentTaskHandle 39
#define SYSCALL_NUM_xTaskGetSchedulerState 40
#define SYSCALL_NUM_xTimerGetExpiryTime 41
#define SYSCALL_NUM_xTimerGetPeriod 42
#define SYSCALL_NUM_xTimerGetTimerDaemonTaskHandle 43
#define SYSCALL_NUM_xTimerIsTimerActive 44
#define SYSCALL_NUM_xTaskAbortDelay 45
#define SYSCALL_NUM_xTaskGetHandle 46
#define SYSCALL_NUM_xEventGroupCreate 47
#define SYSCALL_NUM_xEventGroupWaitBits 48
#define SYSCALL_NUM_vEventGroupDelete 49
#define SYSCALL_NUM_xStreamBufferGenericCreate 50 
#define SYSCALL_NUM_xStreamBufferReceive 51 
#define SYSCALL_NUM_vStreamBufferDelete 52 
#define SYSCALL_NUM_xQueueGetMutexHolder 53 
#define SYSCALL_NUM_xEventGroupSync 54 
#define SYSCALL_NUM_xEventGroupSetBits 55 
#define SYSCALL_NUM_xEventGroupClearBits 56 
#define SYSCALL_NUM_xStreamBufferSend 57 
#define SYSCALL_NUM_xStreamBufferIsEmpty 58 
#define SYSCALL_NUM_xStreamBufferNextMessageLengthBytes 59 
#define SYSCALL_NUM_xStreamBufferIsFull 60 
#define SYSCALL_NUM_xStreamBufferSpacesAvailable 61 
#define SYSCALL_NUM_xStreamBufferReset 62 
#define SYSCALL_NUM_xStreamBufferBytesAvailable 64

static SYSTEMCALL system_calls[MAX_SYSCALLS];


static uint64_t *getpgd() {
    extern StackType_t *pxCurrentTCB;
    xMPU_SETTINGS * xMPUSettings = (xMPU_SETTINGS *) (pxCurrentTCB+1);
    return (uint64_t *) xMPUSettings->pgd;
}

/* Check that a user space address is mapped */
int  check_address_valid(uint64_t target_address) {
     uint64_t *pml4=getpgd();
     uint64_t addr = target_address;
     if (target_address < USER_VA_START) {
         return 0;
     }
     uint32_t pml4_index=0;
     uint32_t pml3_index=0;
     uint32_t pml2_index=0;
     uint32_t pml1_index=0;
     uint64_t *pml3, *pml2,*pml1;

     pml4_index = (addr >> 39) & 0x1ff;
     pml3=(uint64_t *)(pml4[pml4_index]&0xfffffffff000);
     if (!pml3){
         return 0;
     }
     pml3_index = (addr >> 30) & 0x1ff;
     pml2=(uint64_t *)(pml3[pml3_index]&0xfffffffff000);
     if (!pml2){
         return 0;
     }
     pml2_index = (addr >> 21) & 0x1ff;
     pml1=(uint64_t *)(pml2[pml2_index]&0xfffffffff000);
     if (!pml1){
         return 0;
     }
     pml1_index = (addr >> 12) & 0x1ff;
     uint64_t phyaddr = pml1[pml1_index]&0xfffffffff000;
     if (!phyaddr){
         return 0;
     }
     return 1;
}

#define CHECK_USER_PARAM(x)            \
if (!check_address_valid(argptr[x]))    \
   return -1

uint64_t sys_writec(uint64_t *argptr)
{
    serial_send((char) argptr[0]&0xff);
    return (uint64_t) 0;
}
uint64_t sys_xTaskGetTickCount(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xTaskGetTickCount();
}
uint64_t sys_xTaskDelayUntil(uint64_t *argptr)
{
    CHECK_USER_PARAM(0);
    return (uint64_t) (BaseType_t) xTaskDelayUntil((TickType_t * const) argptr[0],( TickType_t) argptr[1]);
}
uint64_t sys_xQueueGenericSend(uint64_t *argptr)
{
    CHECK_USER_PARAM(1);
    return (uint64_t) (BaseType_t) xQueueGenericSend((QueueHandle_t) argptr[0],( const void * const) argptr[1],(TickType_t) argptr[2],( BaseType_t) argptr[3]);
}
uint64_t sys_xQueueReceive(uint64_t *argptr)
{
    CHECK_USER_PARAM(1);
    return (uint64_t) (BaseType_t) xQueueReceive((QueueHandle_t) argptr[0],(void * const) argptr[1],(TickType_t) argptr[2]);
}
uint64_t sys_xTimerGenericCommandFromTask(uint64_t *argptr)
{
    CHECK_USER_PARAM(3);
    return (uint64_t) (BaseType_t) xTimerGenericCommandFromTask((TimerHandle_t) argptr[0],(const BaseType_t) argptr[1],( const TickType_t) argptr[2],( BaseType_t * const) argptr[3],( const TickType_t) argptr[4]);
}
uint64_t sys_vTaskDelay(uint64_t *argptr)
{
    vTaskDelay((TickType_t) argptr[0]);
    return (uint64_t) 0;
}
uint64_t sys_uxTaskPriorityGet(uint64_t *argptr)
{
    return (uint64_t) (UBaseType_t) uxTaskPriorityGet((const TaskHandle_t) argptr[0]);
}
uint64_t sys_vTaskPrioritySet(uint64_t *argptr)
{
    vTaskPrioritySet((TaskHandle_t) argptr[0],( UBaseType_t) argptr[1]);
    return (uint64_t) 0;
}
uint64_t sys_eTaskGetState(uint64_t *argptr)
{
    return (uint64_t) (eTaskState) eTaskGetState((TaskHandle_t) argptr[0]);
}
uint64_t sys_vTaskGetInfo(uint64_t *argptr)
{
    CHECK_USER_PARAM(1);
    vTaskGetInfo((TaskHandle_t) argptr[0],( TaskStatus_t * ) argptr[1],( BaseType_t) argptr[2],( eTaskState) argptr[3]);
    return (uint64_t) 0;
}
uint64_t sys_vTaskSuspend(uint64_t *argptr)
{
    vTaskSuspend((TaskHandle_t) argptr[0]);
    return (uint64_t) 0;
}
uint64_t sys_vTaskResume(uint64_t *argptr)
{
    vTaskResume((TaskHandle_t) argptr[0]);
    return (uint64_t) 0;
}
uint64_t sys_vTaskSuspendAll(uint64_t *argptr)
{
    vTaskSuspendAll();
    return (uint64_t) 0;
}
uint64_t sys_uxTaskGetNumberOfTasks(uint64_t *argptr)
{
    return (uint64_t) (UBaseType_t) uxTaskGetNumberOfTasks();
}
uint64_t sys_uxTaskGetSystemState(uint64_t *argptr)
{
    CHECK_USER_PARAM(0);
    CHECK_USER_PARAM(2);
    return (uint64_t) (UBaseType_t) uxTaskGetSystemState((TaskStatus_t *) argptr[0],( UBaseType_t) argptr[1],( configRUN_TIME_COUNTER_TYPE *) argptr[2]);
}
uint64_t sys_xTaskGetCurrentTaskHandle(uint64_t *argptr)
{
    return (uint64_t) (TaskHandle_t) xTaskGetCurrentTaskHandle();
}
uint64_t sys_xTaskGetSchedulerState(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xTaskGetSchedulerState();
}
uint64_t sys_vTaskSetTimeOutState(uint64_t *argptr)
{
    CHECK_USER_PARAM(0);
    vTaskSetTimeOutState((TimeOut_t * const) argptr[0]);
    return (uint64_t) 0;
}
uint64_t sys_xTaskCheckForTimeOut(uint64_t *argptr)
{
    CHECK_USER_PARAM(0);
    CHECK_USER_PARAM(1);
    return (uint64_t) (BaseType_t) xTaskCheckForTimeOut((TimeOut_t * const) argptr[0],( TickType_t * const) argptr[1]);
}
uint64_t sys_xTaskGenericNotify(uint64_t *argptr)
{
    CHECK_USER_PARAM(4);
    return (uint64_t) (BaseType_t) xTaskGenericNotify((TaskHandle_t) argptr[0],( UBaseType_t) argptr[1],( uint32_t) argptr[2],( eNotifyAction) argptr[3],( uint32_t *) argptr[4]);
}
uint64_t sys_xTaskGenericNotifyWait(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xTaskGenericNotifyWait((UBaseType_t) argptr[0],( uint32_t) argptr[1],( uint32_t) argptr[2],( uint32_t *) argptr[3],( TickType_t) argptr[4]);
}
uint64_t sys_ulTaskGenericNotifyTake(uint64_t *argptr)
{
    return (uint64_t) (uint32_t) ulTaskGenericNotifyTake((UBaseType_t) argptr[0],( BaseType_t) argptr[1],( TickType_t) argptr[2]);
}
uint64_t sys_xTaskGenericNotifyStateClear(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xTaskGenericNotifyStateClear((TaskHandle_t) argptr[0],( UBaseType_t) argptr[1]);
}
uint64_t sys_ulTaskGenericNotifyValueClear(uint64_t *argptr)
{
    return (uint64_t) (uint32_t) ulTaskGenericNotifyValueClear((TaskHandle_t) argptr[0],( UBaseType_t) argptr[1],( uint32_t) argptr[2]);
}
uint64_t sys_xQueueGenericReset(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xQueueGenericReset((QueueHandle_t) argptr[0],( BaseType_t) argptr[1]);
}
uint64_t sys_uxQueueMessagesWaiting(uint64_t *argptr)
{
    return (uint64_t) (UBaseType_t) uxQueueMessagesWaiting((const QueueHandle_t) argptr[0]);
}
uint64_t sys_uxQueueSpacesAvailable(uint64_t *argptr)
{
    return (uint64_t) (UBaseType_t) uxQueueSpacesAvailable((const QueueHandle_t) argptr[0]);
}
uint64_t sys_xQueuePeek(uint64_t *argptr)
{
    CHECK_USER_PARAM(1);
    return (uint64_t) (BaseType_t) xQueuePeek((QueueHandle_t) argptr[0],( void * const) argptr[1],( TickType_t) argptr[2]);
}
uint64_t sys_xQueueSemaphoreTake(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xQueueSemaphoreTake((QueueHandle_t) argptr[0],( TickType_t) argptr[1]);
}
uint64_t sys_xQueueCreateMutex(uint64_t *argptr)
{
    return (uint64_t) (QueueHandle_t) xQueueCreateMutex((const uint8_t) argptr[0]);
}
uint64_t sys_xQueueCreateCountingSemaphore(uint64_t *argptr)
{
    return (uint64_t) (QueueHandle_t) xQueueCreateCountingSemaphore((UBaseType_t) argptr[0],( UBaseType_t) argptr[1]);
}
uint64_t sys_xQueueTakeMutexRecursive(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xQueueTakeMutexRecursive((QueueHandle_t) argptr[0],( TickType_t) argptr[1]);
}
uint64_t sys_xQueueGiveMutexRecursive(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xQueueGiveMutexRecursive((QueueHandle_t) argptr[0]);
}
uint64_t sys_xQueueCreateSet(uint64_t *argptr)
{
    return (uint64_t) (QueueSetHandle_t) xQueueCreateSet((UBaseType_t) argptr[0]);
}
uint64_t sys_xQueueSelectFromSet(uint64_t *argptr)
{
    return (uint64_t) (QueueSetMemberHandle_t) xQueueSelectFromSet((QueueSetHandle_t) argptr[0],( TickType_t) argptr[1]);
}
uint64_t sys_xQueueAddToSet(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xQueueAddToSet((QueueSetMemberHandle_t) argptr[0],( QueueSetHandle_t) argptr[1]);
}
uint64_t sys_xQueueRemoveFromSet(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xQueueRemoveFromSet((QueueSetMemberHandle_t) argptr[0],( QueueSetHandle_t) argptr[1]);
}
uint64_t sys_vQueueAddToRegistry(uint64_t *argptr)
{
    CHECK_USER_PARAM(1);
    vQueueAddToRegistry((QueueHandle_t) argptr[0],( const char *) argptr[1]);
    return (uint64_t) 0;
}
uint64_t sys_vQueueUnregisterQueue(uint64_t *argptr)
{
    vQueueUnregisterQueue((QueueHandle_t) argptr[0]);
    return (uint64_t) 0;
}
uint64_t sys_pcQueueGetName(uint64_t *argptr)
{
    return (uint64_t) (const char *) pcQueueGetName((QueueHandle_t) argptr[0]);
}
uint64_t sys_vQueueDelete(uint64_t *argptr)
{
    vQueueDelete((QueueHandle_t) argptr[0]);
    return (uint64_t) 0;
}
uint64_t sys_pvTimerGetTimerID(uint64_t *argptr)
{
    return (uint64_t) (void *) pvTimerGetTimerID((const TimerHandle_t) argptr[0]);
}
uint64_t sys_vTimerSetTimerID(uint64_t *argptr)
{
    CHECK_USER_PARAM(1);
    vTimerSetTimerID((TimerHandle_t) argptr[0],( void *) argptr[1]);
    return (uint64_t) 0;
}
uint64_t sys_xTimerIsTimerActive(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xTimerIsTimerActive((TimerHandle_t) argptr[0]);
}
uint64_t sys_xTimerGetTimerDaemonTaskHandle(uint64_t *argptr)
{
    return (uint64_t) (TaskHandle_t) xTimerGetTimerDaemonTaskHandle();
}
uint64_t sys_vTimerSetReloadMode(uint64_t *argptr)
{
    vTimerSetReloadMode((TimerHandle_t) argptr[0],( const BaseType_t) argptr[1]);
    return (uint64_t) 0;
}
uint64_t sys_uxTimerGetReloadMode(uint64_t *argptr)
{
    return (uint64_t) (UBaseType_t) uxTimerGetReloadMode((TimerHandle_t) argptr[0]);
}
uint64_t sys_pcTimerGetName(uint64_t *argptr)
{
    // Return a pointer.
    return (uint64_t) (const char *) pcTimerGetName((TimerHandle_t) argptr[0]);
}
uint64_t sys_xTimerGetPeriod(uint64_t *argptr)
{
    return (uint64_t) (TickType_t) xTimerGetPeriod((TimerHandle_t) argptr[0]);
}
uint64_t sys_xTimerGetExpiryTime(uint64_t *argptr)
{
    return (uint64_t) (TickType_t) xTimerGetExpiryTime((TimerHandle_t) argptr[0]);
}

uint64_t sys_xTaskAbortDelay(uint64_t *argptr)
{
   return (uint64_t) (BaseType_t) xTaskAbortDelay((TaskHandle_t) argptr[0]);
}

uint64_t sys_xTaskGetHandle(uint64_t *argptr)
{
   return (uint64_t) (TaskHandle_t) xTaskGetHandle((const char *) argptr[0]);
}

uint64_t sys_xEventGroupCreate(uint64_t *argptr)
{
   return (uint64_t) (EventGroupHandle_t) xEventGroupCreate();
}

uint64_t sys_xEventGroupWaitBits(uint64_t *argptr)
{
   return (uint64_t) (EventBits_t) xEventGroupWaitBits((EventGroupHandle_t) argptr[0], (const EventBits_t) argptr[1], (const BaseType_t) argptr[2], (const BaseType_t)argptr[3], (TickType_t)argptr[4]);
}


uint64_t sys_vEventGroupDelete(uint64_t *argptr)
{
    CHECK_USER_PARAM(0);
    vEventGroupDelete((EventGroupHandle_t) argptr[0]);
    return (uint64_t) 0;
}

uint64_t sys_xStreamBufferGenericCreate(uint64_t *argptr)
{
   return (uint64_t) (StreamBufferHandle_t) xStreamBufferGenericCreate((size_t) argptr[0], (size_t) argptr[1], (BaseType_t) argptr[2], (StreamBufferCallbackFunction_t )argptr[3], (StreamBufferCallbackFunction_t)argptr[4]);
}

uint64_t sys_xStreamBufferReceive(uint64_t *argptr)
{
   return (uint64_t) (size_t) xStreamBufferReceive((StreamBufferHandle_t) argptr[0], (void *) argptr[1], (size_t) argptr[2], (TickType_t)argptr[3]);
}

uint64_t sys_vStreamBufferDelete(uint64_t *argptr)
{
    CHECK_USER_PARAM(0);
    vStreamBufferDelete((StreamBufferHandle_t) argptr[0]);
    return (uint64_t) 0;
}
uint64_t sys_xQueueGetMutexHolder(uint64_t *argptr)
{
    CHECK_USER_PARAM(1);
    return (uint64_t) (TaskHandle_t) xQueueGetMutexHolder((QueueHandle_t) argptr[0]);
}

uint64_t sys_xEventGroupSync(uint64_t *argptr)
{
   return (uint64_t) (EventBits_t) xEventGroupSync((EventGroupHandle_t) argptr[0], (const EventBits_t) argptr[1], (const EventBits_t ) argptr[2], (TickType_t )argptr[3]);
}

uint64_t sys_xEventGroupSetBits(uint64_t *argptr)
{
   return (uint64_t) ( EventBits_t) xEventGroupSetBits((EventGroupHandle_t) argptr[0], (const EventBits_t) argptr[1]);
}

uint64_t sys_xEventGroupClearBits(uint64_t *argptr)
{
   return (uint64_t) ( EventBits_t) xEventGroupClearBits((EventGroupHandle_t) argptr[0], (const EventBits_t) argptr[1]);
}

uint64_t sys_xStreamBufferSend(uint64_t *argptr)
{
   return (uint64_t) (size_t) xStreamBufferSend((StreamBufferHandle_t) argptr[0], (const void *) argptr[1], (size_t) argptr[2], (TickType_t)argptr[3]);
}

uint64_t sys_xStreamBufferIsEmpty(uint64_t *argptr)
{
   return (uint64_t) ( size_t ) xStreamBufferIsEmpty((StreamBufferHandle_t) argptr[0]);
}

uint64_t sys_xStreamBufferNextMessageLengthBytes(uint64_t *argptr)
{
   return (uint64_t) ( size_t ) xStreamBufferNextMessageLengthBytes((StreamBufferHandle_t) argptr[0]);
}

uint64_t sys_xStreamBufferIsFull(uint64_t *argptr)
{
    return (uint64_t) (BaseType_t) xStreamBufferIsFull((StreamBufferHandle_t) argptr[0]);
}

uint64_t sys_xStreamBufferSpacesAvailable(uint64_t *argptr)
{
    return (uint64_t) (size_t) xStreamBufferSpacesAvailable((StreamBufferHandle_t) argptr[0]);
}

uint64_t sys_xStreamBufferReset(uint64_t *argptr)
{
    return (uint64_t) (size_t) xStreamBufferReset((StreamBufferHandle_t) argptr[0]);
}


uint64_t sys_xStreamBufferBytesAvailable(uint64_t *argptr)
{
    return (uint64_t) (size_t) xStreamBufferBytesAvailable((StreamBufferHandle_t) argptr[0]);
}

extern StackType_t *pxCurrentTCB;
void vInitSystemCall(void)
{
    int i=0;
    for (i=0;i<MAX_SYSCALLS;i++) {
        system_calls[i] = NULL;
    }
    system_calls[SYSCALL_NUM_writec] = sys_writec;
    system_calls[SYSCALL_NUM_xTaskGetTickCount] = sys_xTaskGetTickCount;
    system_calls[SYSCALL_NUM_xTaskDelayUntil] = sys_xTaskDelayUntil;
    system_calls[SYSCALL_NUM_xQueueGenericSend] = sys_xQueueGenericSend;
    system_calls[SYSCALL_NUM_xQueueReceive] = sys_xQueueReceive;
    system_calls[SYSCALL_NUM_xTimerGenericCommandFromTask] = sys_xTimerGenericCommandFromTask;
    system_calls[SYSCALL_NUM_eTaskGetState]=sys_eTaskGetState;
    system_calls[SYSCALL_NUM_pcQueueGetName]=sys_pcQueueGetName;
    system_calls[SYSCALL_NUM_pcTimerGetName]=sys_pcTimerGetName;
    system_calls[SYSCALL_NUM_pvTimerGetTimerID]=sys_pvTimerGetTimerID;
    system_calls[SYSCALL_NUM_ulTaskGenericNotifyTake]=sys_ulTaskGenericNotifyTake;
    system_calls[SYSCALL_NUM_ulTaskGenericNotifyValueClear]=sys_ulTaskGenericNotifyValueClear;
    system_calls[SYSCALL_NUM_uxQueueMessagesWaiting]=sys_uxQueueMessagesWaiting;
    system_calls[SYSCALL_NUM_uxQueueSpacesAvailable]=sys_uxQueueSpacesAvailable;
    system_calls[SYSCALL_NUM_uxTaskGetNumberOfTasks]=sys_uxTaskGetNumberOfTasks;
    system_calls[SYSCALL_NUM_uxTaskGetSystemState]=sys_uxTaskGetSystemState;
    system_calls[SYSCALL_NUM_uxTaskPriorityGet]=sys_uxTaskPriorityGet;
    system_calls[SYSCALL_NUM_uxTimerGetReloadMode]=sys_uxTimerGetReloadMode;
    system_calls[SYSCALL_NUM_vQueueAddToRegistry]=sys_vQueueAddToRegistry;
    system_calls[SYSCALL_NUM_vQueueUnregisterQueue]=sys_vQueueUnregisterQueue;
    system_calls[SYSCALL_NUM_vTaskDelay]=sys_vTaskDelay;
    system_calls[SYSCALL_NUM_vTaskGetInfo]=sys_vTaskGetInfo;
    system_calls[SYSCALL_NUM_vTaskResume]=sys_vTaskResume;
    system_calls[SYSCALL_NUM_vTaskSetTimeOutState]=sys_vTaskSetTimeOutState;
    system_calls[SYSCALL_NUM_vTaskSuspend]=sys_vTaskSuspend;
    system_calls[SYSCALL_NUM_vTaskSuspendAll]=sys_vTaskSuspendAll;
    system_calls[SYSCALL_NUM_vTimerSetReloadMode]=sys_vTimerSetReloadMode;
    system_calls[SYSCALL_NUM_vTimerSetTimerID]=sys_vTimerSetTimerID;
    system_calls[SYSCALL_NUM_xQueueAddToSet]=sys_xQueueAddToSet;
    system_calls[SYSCALL_NUM_xQueueGiveMutexRecursive]=sys_xQueueGiveMutexRecursive;
    system_calls[SYSCALL_NUM_xQueuePeek]=sys_xQueuePeek;
    system_calls[SYSCALL_NUM_xQueueRemoveFromSet]=sys_xQueueRemoveFromSet;
    system_calls[SYSCALL_NUM_xQueueSelectFromSet]=sys_xQueueSelectFromSet;
    system_calls[SYSCALL_NUM_xQueueSemaphoreTake]=sys_xQueueSemaphoreTake;
    system_calls[SYSCALL_NUM_xQueueTakeMutexRecursive]=sys_xQueueTakeMutexRecursive;
    system_calls[SYSCALL_NUM_xTaskCheckForTimeOut]=sys_xTaskCheckForTimeOut;
    system_calls[SYSCALL_NUM_xTaskGenericNotify]=sys_xTaskGenericNotify;
    system_calls[SYSCALL_NUM_xTaskGenericNotifyStateClear]=sys_xTaskGenericNotifyStateClear;
    system_calls[SYSCALL_NUM_xTaskGenericNotifyWait]=sys_xTaskGenericNotifyWait;
    system_calls[SYSCALL_NUM_xTaskGetCurrentTaskHandle]=sys_xTaskGetCurrentTaskHandle;
    system_calls[SYSCALL_NUM_xTaskGetSchedulerState]=sys_xTaskGetSchedulerState;
    system_calls[SYSCALL_NUM_xTimerGetExpiryTime]=sys_xTimerGetExpiryTime;
    system_calls[SYSCALL_NUM_xTimerGetPeriod]=sys_xTimerGetPeriod;
    system_calls[SYSCALL_NUM_xTimerGetTimerDaemonTaskHandle]=sys_xTimerGetTimerDaemonTaskHandle;
    system_calls[SYSCALL_NUM_xTimerIsTimerActive]=sys_xTimerIsTimerActive;
    system_calls[SYSCALL_NUM_xTaskAbortDelay]=sys_xTaskAbortDelay;
    system_calls[SYSCALL_NUM_xTaskGetHandle]=sys_xTaskGetHandle;
    system_calls[SYSCALL_NUM_xEventGroupCreate]=sys_xEventGroupCreate;
    system_calls[SYSCALL_NUM_xEventGroupWaitBits]=sys_xEventGroupWaitBits;
    system_calls[SYSCALL_NUM_vEventGroupDelete]=sys_vEventGroupDelete;
    system_calls[SYSCALL_NUM_xStreamBufferGenericCreate]=sys_xStreamBufferGenericCreate;
    system_calls[SYSCALL_NUM_xStreamBufferReceive]=sys_xStreamBufferReceive;
    system_calls[SYSCALL_NUM_vStreamBufferDelete]=sys_vStreamBufferDelete;
    system_calls[SYSCALL_NUM_xQueueGetMutexHolder]=sys_xQueueGetMutexHolder;
    system_calls[SYSCALL_NUM_xEventGroupSync]=sys_xEventGroupSync;
    system_calls[SYSCALL_NUM_xEventGroupSetBits]=sys_xEventGroupSetBits;
    system_calls[SYSCALL_NUM_xEventGroupClearBits]=sys_xEventGroupClearBits;
    system_calls[SYSCALL_NUM_xStreamBufferSend]=sys_xStreamBufferSend;
    system_calls[SYSCALL_NUM_xStreamBufferIsEmpty]=sys_xStreamBufferIsEmpty;
    system_calls[SYSCALL_NUM_xStreamBufferNextMessageLengthBytes]=sys_xStreamBufferNextMessageLengthBytes;
    system_calls[SYSCALL_NUM_xStreamBufferIsFull]=sys_xStreamBufferIsFull;
    system_calls[SYSCALL_NUM_xStreamBufferSpacesAvailable]=sys_xStreamBufferSpacesAvailable;
    system_calls[SYSCALL_NUM_xStreamBufferReset]=sys_xStreamBufferReset;
    system_calls[SYSCALL_NUM_xStreamBufferBytesAvailable]=sys_xStreamBufferBytesAvailable;
}

void vSystemCall(struct TrapFrame *tf)
{
    int64_t i = tf->rax;
    int64_t param_count = tf->rdi;
    int64_t *argptr = (int64_t*)tf->rsi;

    if (param_count < 0 || i >= MAX_SYSCALLS || i < 0) {
        tf->rax = -1;
        return;
    }
    if (system_calls[i]){
        tf->rax = system_calls[i](argptr);
    }
    else{
        tf->rax = -1;
    }
}

