/* SPDX-License-Identifier: MIT */
#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

#include <stdlib.h>

#define configUSE_PREEMPTION                 1
#define configUSE_IDLE_HOOK                  0
#define configUSE_TICK_HOOK                  0
#define configTICK_RATE_HZ                   100
#define configMAX_PRIORITIES                 4
#define configMINIMAL_STACK_SIZE             4096
#define configTOTAL_HEAP_SIZE                ( 256 * 1024 )
#define configMAX_TASK_NAME_LEN              16
#define configUSE_16_BIT_TICKS               0
#define configUSE_MUTEXES                    1
#define configUSE_TIMERS                     0
#define configSUPPORT_STATIC_ALLOCATION      0
#define configSUPPORT_DYNAMIC_ALLOCATION     1
#define INCLUDE_vTaskDelay                   1
#define INCLUDE_vTaskDelete                  1
#define INCLUDE_xTaskGetCurrentTaskHandle    1

#if TEST_ASSERT_ENABLED
    #define configASSERT( x )    do { if( !( x ) ) { abort(); } } while( 0 )
#endif

#endif /* ifndef FREERTOS_CONFIG_H */
