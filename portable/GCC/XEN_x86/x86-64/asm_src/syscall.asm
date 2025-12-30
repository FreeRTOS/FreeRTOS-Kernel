 ; syscall
 ; 
 ; Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 ;
 ; SPDX-License-Identifier: MIT
 ;
 ; Permission is hereby granted, free of charge, to any person obtaining a copy of
 ; this software and associated documentation files (the "Software"), to deal in
 ; the Software without restriction, including without limitation the rights to
 ; use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 ; the Software, and to permit persons to whom the Software is furnished to do so,
 ; subject to the following conditions:
 ;
 ; The above copyright notice and this permission notice shall be included in all
 ; copies or substantial portions of the Software.
 ;
 ; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 ; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 ; FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 ; COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 ; IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 ; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ;

section freertos_system_calls
%define SYSCALL_NUM_writec 0
%define SYSCALL_NUM_xTaskGetTickCount 1
%define SYSCALL_NUM_xTaskDelayUntil 2
%define SYSCALL_NUM_xQueueGenericSend 3
%define SYSCALL_NUM_xQueueReceive 4
%define SYSCALL_NUM_xTimerGenericCommandFromTask 5
%define SYSCALL_NUM_eTaskGetState 6
%define SYSCALL_NUM_pcQueueGetName 7
%define SYSCALL_NUM_pcTimerGetName 8
%define SYSCALL_NUM_pvTimerGetTimerID 9
%define SYSCALL_NUM_ulTaskGenericNotifyTake 10
%define SYSCALL_NUM_ulTaskGenericNotifyValueClear 11
%define SYSCALL_NUM_uxQueueMessagesWaiting 12
%define SYSCALL_NUM_uxQueueSpacesAvailable 13
%define SYSCALL_NUM_uxTaskGetNumberOfTasks 14
%define SYSCALL_NUM_uxTaskGetSystemState 15
%define SYSCALL_NUM_uxTaskPriorityGet 16
%define SYSCALL_NUM_uxTimerGetReloadMode 17
%define SYSCALL_NUM_vQueueAddToRegistry 18
%define SYSCALL_NUM_vQueueUnregisterQueue 19
%define SYSCALL_NUM_vTaskDelay 20
%define SYSCALL_NUM_vTaskGetInfo 21
%define SYSCALL_NUM_vTaskResume 22
%define SYSCALL_NUM_vTaskSetTimeOutState 23
%define SYSCALL_NUM_vTaskSuspend 24
%define SYSCALL_NUM_vTaskSuspendAll 25
%define SYSCALL_NUM_vTimerSetReloadMode 26
%define SYSCALL_NUM_vTimerSetTimerID 27
%define SYSCALL_NUM_xQueueAddToSet 28
%define SYSCALL_NUM_xQueueGiveMutexRecursive 29
%define SYSCALL_NUM_xQueuePeek 30
%define SYSCALL_NUM_xQueueRemoveFromSet 31
%define SYSCALL_NUM_xQueueSelectFromSet 32
%define SYSCALL_NUM_xQueueSemaphoreTake 33
%define SYSCALL_NUM_xQueueTakeMutexRecursive 34
%define SYSCALL_NUM_xTaskCheckForTimeOut 35
%define SYSCALL_NUM_xTaskGenericNotify 36
%define SYSCALL_NUM_xTaskGenericNotifyStateClear 37
%define SYSCALL_NUM_xTaskGenericNotifyWait 38
%define SYSCALL_NUM_xTaskGetCurrentTaskHandle 39
%define SYSCALL_NUM_xTaskGetSchedulerState 40
%define SYSCALL_NUM_xTimerGetExpiryTime 41
%define SYSCALL_NUM_xTimerGetPeriod 42
%define SYSCALL_NUM_xTimerGetTimerDaemonTaskHandle 43
%define SYSCALL_NUM_xTimerIsTimerActive 44
%define SYSCALL_NUM_xTaskAbortDelay 45
%define SYSCALL_NUM_xTaskGetHandle 46
%define SYSCALL_NUM_xEventGroupCreate 47
%define SYSCALL_NUM_xEventGroupWaitBits 48
%define SYSCALL_NUM_vEventGroupDelete 49
%define SYSCALL_NUM_xStreamBufferGenericCreate 50
%define SYSCALL_NUM_xStreamBufferReceive 51
%define SYSCALL_NUM_vStreamBufferDelete 52
%define SYSCALL_NUM_xQueueGetMutexHolder 53
%define SYSCALL_NUM_xEventGroupSync 54
%define SYSCALL_NUM_xEventGroupSetBits 55
%define SYSCALL_NUM_xEventGroupClearBits 56
%define SYSCALL_NUM_xStreamBufferSend 57
%define SYSCALL_NUM_xStreamBufferIsEmpty 58
%define SYSCALL_NUM_xStreamBufferNextMessageLengthBytes 59
%define SYSCALL_NUM_xStreamBufferIsFull 60 
%define SYSCALL_NUM_xStreamBufferSpacesAvailable 61 
%define SYSCALL_NUM_xStreamBufferReset 62 
%define SYSCALL_NUM_xStreamBufferBytesAvailable 64 


%macro SYSCALL_0 2
global %1
%1:
    mov eax,%2
    mov rdi,0
    mov rsi,rsp
    int 0x80
    ret
%endmacro

%macro SYSCALL_1 2
global %1
%1:
    sub rsp,8
    mov eax, %2

    mov [rsp],rdi

    mov rdi,1
    mov rsi,rsp
    int 0x80

    add rsp,8
    ret
%endmacro

%macro SYSCALL_2 2
global %1
%1:
    sub rsp,16
    mov eax, %2

    mov [rsp],rdi
    mov [rsp+8],rsi

    mov rdi,2
    mov rsi,rsp
    int 0x80

    add rsp,16
    ret
%endmacro

%macro SYSCALL_3 2
global %1
%1:
    sub rsp,24
    mov eax, %2

    mov [rsp],rdi
    mov [rsp+8],rsi
    mov [rsp+16],rdx

    mov rdi,3
    mov rsi,rsp
    int 0x80

    add rsp,24
    ret
%endmacro

%macro SYSCALL_4 2
global %1
%1:
    sub rsp, 32
    mov eax, %2

    mov [rsp],rdi
    mov [rsp+8],rsi
    mov [rsp+16],rdx
    mov [rsp+24],rcx

    mov rdi,4
    mov rsi,rsp
    int 0x80

    add rsp,32
    ret
%endmacro

%macro SYSCALL_5 2
global %1
%1:
    sub rsp, 40
    mov eax, %2

    mov [rsp],rdi
    mov [rsp+8],rsi
    mov [rsp+16],rdx
    mov [rsp+24],rcx
    mov [rsp+32],r8

    mov rdi,5
    mov rsi,rsp
    int 0x80

    add rsp,40
    ret
%endmacro

%macro SYSCALL_6 2
global %1
%1:
    sub rsp, 48
    mov eax, %2

    mov [rsp],rdi
    mov [rsp+8],rsi
    mov [rsp+16],rdx
    mov [rsp+24],rcx
    mov [rsp+32],r8
    mov [rsp+40],r9

    mov rdi,6
    mov rsi,rsp
    int 0x80

    add rsp,48
    ret
%endmacro

%macro SYSCALL_7 2
global %1
%1:
    sub rsp, 56
    mov eax, %7

    mov [rsp],rdi
    mov [rsp+8],rsi
    mov [rsp+16],rdx
    mov [rsp+24],rcx
    mov [rsp+32],r8
    mov [rsp+40],r9

    mov rdi,6
    mov rsi,rsp
    int 0x80

    add rsp,56
    ret
%endmacro

SYSCALL_1 syscall_writec, SYSCALL_NUM_writec
SYSCALL_0 syscall_xTaskGetTickCount, SYSCALL_NUM_xTaskGetTickCount
SYSCALL_2 syscall_xTaskDelayUntil, SYSCALL_NUM_xTaskDelayUntil
SYSCALL_4 syscall_xQueueGenericSend, SYSCALL_NUM_xQueueGenericSend
SYSCALL_3 syscall_xQueueReceive, SYSCALL_NUM_xQueueReceive
SYSCALL_5 syscall_xTimerGenericCommandFromTask, SYSCALL_NUM_xQueueGenericSend
SYSCALL_1 syscall_eTaskGetState, SYSCALL_NUM_eTaskGetState
SYSCALL_1 syscall_pcQueueGetName, SYSCALL_NUM_pcQueueGetName
SYSCALL_1 syscall_pcTimerGetName, SYSCALL_NUM_pcTimerGetName
SYSCALL_1 syscall_pvTimerGetTimerID, SYSCALL_NUM_pvTimerGetTimerID
SYSCALL_3 syscall_ulTaskGenericNotifyTake, SYSCALL_NUM_ulTaskGenericNotifyTake
SYSCALL_3 syscall_ulTaskGenericNotifyValueClear, SYSCALL_NUM_ulTaskGenericNotifyValueClear
SYSCALL_1 syscall_uxQueueMessagesWaiting, SYSCALL_NUM_uxQueueMessagesWaiting
SYSCALL_1 syscall_uxQueueSpacesAvailable, SYSCALL_NUM_uxQueueSpacesAvailable
SYSCALL_0 syscall_uxTaskGetNumberOfTasks, SYSCALL_NUM_uxTaskGetNumberOfTasks
SYSCALL_3 syscall_uxTaskGetSystemState, SYSCALL_NUM_uxTaskGetSystemState
SYSCALL_1 syscall_uxTaskPriorityGet, SYSCALL_NUM_uxTaskPriorityGet
SYSCALL_1 syscall_uxTimerGetReloadMode, SYSCALL_NUM_uxTimerGetReloadMode
SYSCALL_2 syscall_vQueueAddToRegistry, SYSCALL_NUM_vQueueAddToRegistry
SYSCALL_1 syscall_vQueueUnregisterQueue, SYSCALL_NUM_vQueueUnregisterQueue
SYSCALL_1 syscall_vTaskDelay, SYSCALL_NUM_vTaskDelay
SYSCALL_4 syscall_vTaskGetInfo, SYSCALL_NUM_vTaskGetInfo
SYSCALL_1 syscall_vTaskResume, SYSCALL_NUM_vTaskResume
SYSCALL_1 syscall_vTaskSetTimeOutState, SYSCALL_NUM_vTaskSetTimeOutState
SYSCALL_1 syscall_vTaskSuspend, SYSCALL_NUM_vTaskSuspend
SYSCALL_0 syscall_vTaskSuspendAll, SYSCALL_NUM_vTaskSuspendAll
SYSCALL_2 syscall_vTimerSetReloadMode, SYSCALL_NUM_vTimerSetReloadMode
SYSCALL_2 syscall_vTimerSetTimerID, SYSCALL_NUM_vTimerSetTimerID
SYSCALL_2 syscall_xQueueAddToSet, SYSCALL_NUM_xQueueAddToSet
SYSCALL_1 syscall_xQueueGiveMutexRecursive, SYSCALL_NUM_xQueueGiveMutexRecursive
SYSCALL_3 syscall_xQueuePeek, SYSCALL_NUM_xQueuePeek
SYSCALL_2 syscall_xQueueRemoveFromSet, SYSCALL_NUM_xQueueRemoveFromSet
SYSCALL_2 syscall_xQueueSelectFromSet, SYSCALL_NUM_xQueueSelectFromSet
SYSCALL_2 syscall_xQueueSemaphoreTake, SYSCALL_NUM_xQueueSemaphoreTake
SYSCALL_2 syscall_xQueueTakeMutexRecursive, SYSCALL_NUM_xQueueTakeMutexRecursive
SYSCALL_2 syscall_xTaskCheckForTimeOut, SYSCALL_NUM_xTaskCheckForTimeOut
SYSCALL_5 syscall_xTaskGenericNotify, SYSCALL_NUM_xTaskGenericNotify
SYSCALL_2 syscall_xTaskGenericNotifyStateClear, SYSCALL_NUM_xTaskGenericNotifyStateClear
SYSCALL_5 syscall_xTaskGenericNotifyWait, SYSCALL_NUM_xTaskGenericNotifyWait
SYSCALL_0 syscall_xTaskGetCurrentTaskHandle, SYSCALL_NUM_xTaskGetCurrentTaskHandle
SYSCALL_0 syscall_xTaskGetSchedulerState, SYSCALL_NUM_xTaskGetSchedulerState
SYSCALL_1 syscall_xTimerGetExpiryTime, SYSCALL_NUM_xTimerGetExpiryTime
SYSCALL_1 syscall_xTimerGetPeriod, SYSCALL_NUM_xTimerGetPeriod
SYSCALL_0 syscall_xTimerGetTimerDaemonTaskHandle, SYSCALL_NUM_xTimerGetTimerDaemonTaskHandle
SYSCALL_1 syscall_xTimerIsTimerActive, SYSCALL_NUM_xTimerIsTimerActive
SYSCALL_1 syscall_xTaskAbortDelay, SYSCALL_NUM_xTaskAbortDelay
SYSCALL_1 syscall_xTaskGetHandle, SYSCALL_NUM_xTaskGetHandle
SYSCALL_0 syscall_xEventGroupCreate, SYSCALL_NUM_xEventGroupCreate
SYSCALL_5 syscall_xEventGroupWaitBits, SYSCALL_NUM_xEventGroupWaitBits
SYSCALL_1 syscall_vEventGroupDelete, SYSCALL_NUM_vEventGroupDelete
SYSCALL_5 syscall_xStreamBufferGenericCreate, SYSCALL_NUM_xStreamBufferGenericCreate
SYSCALL_4 syscall_xStreamBufferReceive, SYSCALL_NUM_xStreamBufferReceive
SYSCALL_1 syscall_vStreamBufferDelete, SYSCALL_NUM_vStreamBufferDelete
SYSCALL_1 syscall_xQueueGetMutexHolder, SYSCALL_NUM_xQueueGetMutexHolder
SYSCALL_4 syscall_xEventGroupSync, SYSCALL_NUM_xEventGroupSync
SYSCALL_2 syscall_xEventGroupSetBits, SYSCALL_NUM_xEventGroupSetBits
SYSCALL_2 syscall_xEventGroupClearBits, SYSCALL_NUM_xEventGroupClearBits
SYSCALL_2 syscall_xStreamBufferSend, SYSCALL_NUM_xStreamBufferSend
SYSCALL_1 syscall_xStreamBufferIsEmpty, SYSCALL_NUM_xStreamBufferIsEmpty
SYSCALL_1 syscall_xStreamBufferNextMessageLengthBytes, SYSCALL_NUM_xStreamBufferNextMessageLengthBytes
SYSCALL_1 syscall_xStreamBufferIsFull, SYSCALL_NUM_xStreamBufferIsFull
SYSCALL_1 syscall_xStreamBufferSpacesAvailable, SYSCALL_NUM_xStreamBufferSpacesAvailable
SYSCALL_1 syscall_xStreamBufferReset, SYSCALL_NUM_xStreamBufferReset
SYSCALL_1 syscall_xStreamBufferBytesAvailable, SYSCALL_NUM_xStreamBufferBytesAvailable

