/* SPDX-License-Identifier: MIT */
#include "FreeRTOS.h"
#include "task.h"

static volatile int iTaskRan;

static void prvTask( void * pvUnused )
{
    ( void ) pvUnused;
    vTaskDelay( 2 );
    iTaskRan = 1;
    vTaskEndScheduler();
}

int main( void )
{
    if( xTaskCreate( prvTask, "smoke", configMINIMAL_STACK_SIZE, NULL, 1, NULL ) != pdPASS )
    {
        return EXIT_FAILURE;
    }

    vTaskStartScheduler();
    return iTaskRan ? EXIT_SUCCESS : EXIT_FAILURE;
}
