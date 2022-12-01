#include "workqueue.h"
#include "FreeRTOS.h"
#include "queue.h"

#if ( configUSE_WORKQUEUE == 1 )

#ifndef configWORK_TASK_NAME
    #define configWORK_TASK_NAME    "WORKER"
#endif


/* The definition of "work tasks" that can be put on the work queue. */
typedef struct
{
  WorkerFunction_t pxCallbackFunction;
  void* pvParam;
} CallbackParameters_t;


/*
 * The worker task. This task performs low-priority or lengthy operations that
 * are defered to it by application software. Other tasks communicate with the
 * worker task via the xWorkerQueueSend and xWorkerQueueSendFromISR calls. */
static portTASK_FUNCTION_PROTO( prvWorkerTask, pvParameters ) PRIVILEGED_FUNCTION;


/* the actual queue which holds the tasks that have to be performed. */
PRIVILEGED_DATA static QueueHandle_t xWorkQueue = NULL;

/* the handle to the worker task, in case it will be needed later. */
PRIVILEGED_DATA static TaskHandle_t xWorkTaskHandle = NULL;


/* creates the actual worker task and the associated work queue. */
BaseType_t xWorkerCreateWorkerTask(void)
{
  BaseType_t xReturn = pdFAIL;

  #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
    // TODO: implement static allocation too.
  #else

      /* create the queue which the work tasks are posted to. If queue creation fails, abort and don't start the worker task. */
      xWorkQueue = xQueueCreate(configWORK_TASK_QUEUE_LENGTH, sizeof(CallbackParameters_t));
      if(xWorkQueue == NULL)
      {
        return pdFAIL;
      }

      /* if the queue creation is successful, create the worker task. If this fails for some reason, the queue is also not needed
       * anymore and should be deleted. */
      xReturn = xTaskCreate(prvWorkerTask,
                            configWORK_TASK_NAME,
                            configWORK_TASK_STACK_SIZE,
                            NULL,
                            configWORK_TASK_PRIORITY,
                            &xWorkTaskHandle);
      if(xReturn != pdPASS)
      {
        vQueueDelete(xWorkQueue);
        xWorkQueue = NULL;
        return pdFAIL;
      }

  #endif

  return pdPASS;
}



BaseType_t xWorkerQueueSend(WorkerFunction_t xFunctionToCall, void* pvParam, TickType_t xTicksToWait)
{
  CallbackParameters_t xCallback;
  xCallback.pxCallbackFunction = xFunctionToCall;
  xCallback.pvParam = pvParam;
  return xQueueSendToBack(xWorkQueue, &xCallback, xTicksToWait);
}



BaseType_t xWorkerQueueSendFromISR(WorkerFunction_t xFunctionToCall, void* pvParam, BaseType_t * pxHigherPriorityTaskWoken)
{
  CallbackParameters_t xCallback;
  xCallback.pxCallbackFunction = xFunctionToCall;
  xCallback.pvParam = pvParam;
  return xQueueSendToBackFromISR(xWorkQueue, &xCallback, pxHigherPriorityTaskWoken);
}



static portTASK_FUNCTION( prvWorkerTask, pvParameters )
{
  /* parameter is unused. avoid compiler warning. */
  (void)pvParameters;

  for( ; ; )
  {
    /* wait on the work queue until actual work tasks are sent to it.
     * as long as the queue is empty, there is nothing to do and the worker
     * task should stay blocked such that no CPU cycles are wasted to it. */
    CallbackParameters_t xCallback;
    if(xQueueReceive(xWorkQueue, &xCallback, portMAX_DELAY))
    {

      /* at least one work task has been sent to the queue. We should determine the
       * callback function and its parameter, check the callback function for validity and
       * then actually call it. */
      WorkerFunction_t pxCallbackFunction = xCallback.pxCallbackFunction;
      void* pvParam = xCallback.pvParam;
      if(pxCallbackFunction != NULL)
      {
        pxCallbackFunction(pvParam);
      }
    }
  }
}

#endif

