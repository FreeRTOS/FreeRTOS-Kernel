#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

#include <stdio.h>
#include <stdlib.h>

/* ---- Scheduler ---- */
#define configUSE_PREEMPTION                1
#define configUSE_TIME_SLICING              1
#define configUSE_IDLE_HOOK                 0
#define configUSE_TICK_HOOK                 0
#define configTICK_RATE_HZ                  ( ( TickType_t ) 1000 )
#define configMAX_PRIORITIES                ( 8 )
#define configMINIMAL_STACK_SIZE            ( ( unsigned short ) 2048 )   /* POSIX threads need big stacks */
#define configTOTAL_HEAP_SIZE               ( ( size_t ) ( 64 * 1024 ) )
#define configMAX_TASK_NAME_LEN             ( 16 )
#define configUSE_16_BIT_TICKS              0
#define configIDLE_SHOULD_YIELD             1

/* ---- Kernel objects ---- */
#define configUSE_MUTEXES                   1
#define configUSE_COUNTING_SEMAPHORES       1
#define configQUEUE_REGISTRY_SIZE           8
#define configSUPPORT_DYNAMIC_ALLOCATION    1
#define configUSE_TRACE_FACILITY            1   /* needed for uxTaskGetSystemState */

/* ---- Debug ---- */
#define configCHECK_FOR_STACK_OVERFLOW      0
#define configASSERT( x )   if( ( x ) == 0 ) { printf( "ASSERT %s:%d\n", __FILE__, __LINE__ ); abort(); }

/* ---- OUR CUSTOM FEATURE (see tasks.c / task.h) ---- */
#define configUSE_SWITCH_STATS              1
#define configSWITCH_TRACE_DEPTH            12

/* ---- API inclusion ---- */
#define INCLUDE_vTaskDelay                  1
#define INCLUDE_vTaskDelayUntil             1
#define INCLUDE_vTaskDelete                 1
#define INCLUDE_vTaskPrioritySet            1
#define INCLUDE_uxTaskPriorityGet           1
#define INCLUDE_uxTaskGetStackHighWaterMark 1
#define INCLUDE_xTaskGetCurrentTaskHandle   1

#endif
