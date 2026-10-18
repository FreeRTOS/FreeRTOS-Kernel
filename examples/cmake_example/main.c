/* Advanced FreeRTOS demo for the modified kernel (configUSE_SWITCH_STATS = 1)
 *  - Producer -> Queue -> Consumer
 *  - Mutex-protected shared counter updated by two workers
 *  - Monitor task: per-task switch counts, last switch-in tick, stack high
 *    water mark, and the kernel's ring-buffer trace of recent context switches
 */
#include <stdio.h>
#include <stdlib.h>
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

#define QUEUE_LEN        5
#define MAX_TASKS        10
#define MONITOR_PERIOD   pdMS_TO_TICKS( 1000 )
#define MONITOR_REPORTS  4          /* demo exits after this many reports */

static QueueHandle_t     xDataQueue;
static SemaphoreHandle_t xCounterMutex;
static volatile uint32_t ulSharedCounter = 0;

static void vProducer( void * pv )
{
    uint32_t ulValue = 0;
    ( void ) pv;

    for( ;; )
    {
        if( xQueueSend( xDataQueue, &ulValue, pdMS_TO_TICKS( 100 ) ) == pdPASS )
        {
            ulValue++;
        }
        vTaskDelay( pdMS_TO_TICKS( 50 ) );
    }
}

static void vConsumer( void * pv )
{
    uint32_t ulReceived;
    ( void ) pv;

    for( ;; )
    {
        if( xQueueReceive( xDataQueue, &ulReceived, portMAX_DELAY ) == pdPASS )
        {
            /* simulate processing */
            vTaskDelay( pdMS_TO_TICKS( 20 ) );
        }
    }
}

static void vWorker( void * pv )
{
    TickType_t xPeriod = pdMS_TO_TICKS( ( uint32_t ) ( uintptr_t ) pv );
    TickType_t xLastWake = xTaskGetTickCount();

    for( ;; )
    {
        if( xSemaphoreTake( xCounterMutex, portMAX_DELAY ) == pdTRUE )
        {
            ulSharedCounter++;
            xSemaphoreGive( xCounterMutex );
        }
        vTaskDelayUntil( &xLastWake, xPeriod );   /* drift-free periodic task */
    }
}

static void vMonitor( void * pv )
{
    TaskStatus_t      xStatus[ MAX_TASKS ];
    SwitchTraceEntry_t xTrace[ 12 ];
    TickType_t        xLastWake = xTaskGetTickCount();
    int               iReports = 0;
    ( void ) pv;

    for( ;; )
    {
        vTaskDelayUntil( &xLastWake, MONITOR_PERIOD );

        UBaseType_t n = uxTaskGetSystemState( xStatus, MAX_TASKS, NULL );

        printf( "\n=== Report %d | tick=%lu | total switches=%lu | shared=%lu ===\n",
                iReports + 1,
                ( unsigned long ) xTaskGetTickCount(),
                ( unsigned long ) ulTaskGetTotalSwitchCount(),
                ( unsigned long ) ulSharedCounter );
        printf( "%-10s %4s %9s %12s %10s\n", "Task", "Pri", "Switches", "LastInTick", "StackHWM" );

        for( UBaseType_t i = 0; i < n; i++ )
        {
            printf( "%-10s %4lu %9lu %12lu %10lu\n",
                    xStatus[ i ].pcTaskName,
                    ( unsigned long ) xStatus[ i ].uxCurrentPriority,
                    ( unsigned long ) ulTaskGetSwitchCount( xStatus[ i ].xHandle ),
                    ( unsigned long ) xTaskGetLastSwitchInTick( xStatus[ i ].xHandle ),
                    ( unsigned long ) uxTaskGetStackHighWaterMark( xStatus[ i ].xHandle ) );
        }

        uint32_t m = ulTaskGetSwitchTrace( xTrace, 12 );
        printf( "Last %lu switches (oldest -> newest):\n  ", ( unsigned long ) m );
        for( uint32_t i = 0; i < m; i++ )
        {
            printf( "%s@%lu%s", xTrace[ i ].pcTaskName, ( unsigned long ) xTrace[ i ].xTick,
                    ( i + 1 < m ) ? " -> " : "\n" );
        }
        fflush( stdout );

        if( ++iReports >= MONITOR_REPORTS )
        {
            printf( "\nDemo finished.\n" );
            exit( 0 );
        }
    }
}

int main( void )
{
    xDataQueue    = xQueueCreate( QUEUE_LEN, sizeof( uint32_t ) );
    xCounterMutex = xSemaphoreCreateMutex();
    configASSERT( xDataQueue != NULL );
    configASSERT( xCounterMutex != NULL );

    xTaskCreate( vProducer, "Producer", configMINIMAL_STACK_SIZE, NULL, 2, NULL );
    xTaskCreate( vConsumer, "Consumer", configMINIMAL_STACK_SIZE, NULL, 3, NULL );
    xTaskCreate( vWorker,   "WorkerA",  configMINIMAL_STACK_SIZE, ( void * ) 100, 1, NULL );
    xTaskCreate( vWorker,   "WorkerB",  configMINIMAL_STACK_SIZE, ( void * ) 130, 1, NULL );
    xTaskCreate( vMonitor,  "Monitor",  configMINIMAL_STACK_SIZE, NULL, 4, NULL );

    vTaskStartScheduler();
    return 0;
}

/* Needed by the POSIX port when static/idle allocation hooks are requested. */
void vApplicationMallocFailedHook( void ) { printf( "malloc failed\n" ); abort(); }
