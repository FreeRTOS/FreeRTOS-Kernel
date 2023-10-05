/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * license and copyright intentionally withheld to promote copying into user code.
 */

#include "FreeRTOS.h"
#include "task.h"

BaseType_t xPortStartScheduler( void )
{
    return pdTRUE;
}

void vPortEndScheduler( void )
{
}

StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
    return NULL;
}

void vPortYield( void )
{
    /* Save the current Context */
    /* Switch to the highest priority task that is ready to run. */
    vTaskSwitchContext();
    /* Start executing the task we have just switched to. */
}

static void prvTickISR( void )
{
    /* Interrupts must have been enabled for the ISR to fire, so we have to
     * save the context with interrupts enabled. */

    /* Maintain the tick count. */
    if( xTaskIncrementTick() != pdFALSE )
    {
        /* Switch to the highest priority task that is ready to run. */
        vTaskSwitchContext();
    }

    /* start executing the new task */
}
