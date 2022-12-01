
#ifndef WORKQUEUE_H
#define WORKQUEUE_H


#include "FreeRTOS.h"
#include <stdbool.h>
#include "task.h"

/*-----------------------------------------------------------
* MACROS AND DEFINITIONS
*----------------------------------------------------------*/

#if configUSE_WORKQUEUE == 1

    #ifndef configWORK_TASK_QUEUE_LENGTH
        #error If configUSE_WORKQUEUE is set to 1 then configWORK_TASK_QUEUE_LENGTH must also be defined.
    #endif

    // TODO: use a default stack size or print a warning instead?
    #ifndef configWORK_TASK_STACK_SIZE
        #define configWORK_TASK_STACK_SIZE    ( configMINIMAL_STACK_SIZE*2 )
    #endif

    #ifndef configWORK_TASK_PRIORITY
        #define configWORK_TASK_PRIORITY    ( tskIDLE_PRIORITY+1 )
    #endif

typedef void (*WorkerFunction_t)(void* pvParam);

extern BaseType_t xWorkerQueueSendFromISR(WorkerFunction_t xFunctionToCall, void* pvParam, BaseType_t * pxHigherPriorityTaskWoken);
extern BaseType_t xWorkerQueueSend(WorkerFunction_t xFunctionToCall, void* pvParam, TickType_t xTicksToWait);


/*
 * Functions beyond this part are not part of the public API and are intended
 * for use by the kernel only.
 */
BaseType_t xWorkerCreateWorkerTask( void ) PRIVILEGED_FUNCTION;

#endif /* configUSE_WORKQUEUE */

#endif
