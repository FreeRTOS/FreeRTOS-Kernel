/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2020 Cambridge Consultants Ltd.
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

/*-----------------------------------------------------------
* Implementation of functions defined in portable.h for the Posix port.
*
* Each task has a pthread which eases use of standard debuggers
* (allowing backtraces of tasks etc). Threads for tasks that are not
* running are blocked in sigwait().
*
* Task switch is done by resuming the thread for the next task by
* signaling the condition variable and then waiting on a condition variable
* with the current thread.
*
* The timer interrupt uses SIGALRM and care is taken to ensure that
* the signal handler runs only on the thread for the current task.
*
* Use of part of the standard C library requires care as some
* functions can take pthread mutexes internally which can result in
* deadlocks as the FreeRTOS kernel can switch tasks while they're
* holding a pthread mutex.
*
* stdio (printf() and friends) should be called from a single task
* only or serialized with a FreeRTOS primitive such as a binary
* semaphore or mutex.
*----------------------------------------------------------*/
#include "portmacro.h"

#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/times.h>
#include <time.h>

#ifdef __APPLE__
    #include <mach/mach_vm.h>
#endif

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"
#include "timers.h"
#include "utils/wait_for_event.h"
/*-----------------------------------------------------------*/

#define SIG_RESUME    SIGUSR1

typedef struct THREAD
{
    pthread_t pthread;
    TaskFunction_t pxCode;
    void * pvParams;
    BaseType_t xDying;
    struct event * ev;
    ListItem_t xThreadListItem;
} Thread_t;

/*
 * The additional per-thread data is stored at the beginning of the
 * task's stack.
 */
static inline Thread_t * prvGetThreadFromTask( TaskHandle_t xTask )
{
    StackType_t * pxTopOfStack = *( StackType_t ** ) xTask;

    return ( Thread_t * ) ( pxTopOfStack + 1 );
}

/*-----------------------------------------------------------*/

static pthread_once_t hSigSetupThread = PTHREAD_ONCE_INIT;
static sigset_t xAllSignals;
static sigset_t xSchedulerOriginalSignalMask;
static pthread_t hMainThread = ( pthread_t ) NULL;
static volatile BaseType_t uxCriticalNesting;
static BaseType_t xSchedulerEnd = pdFALSE;
static pthread_t hTimerTickThread;
static bool xTimerTickThreadShouldRun;
static uint64_t prvStartTimeNs;
static List_t xThreadList;
/*-----------------------------------------------------------*/

static void prvSetupSignalsAndSchedulerPolicy( void );
static void prvSetupTimerInterrupt( void );
static void * prvWaitForStart( void * pvParams );
static void prvSwitchThread( Thread_t * xThreadToResume,
                             Thread_t * xThreadToSuspend );
static void prvSuspendSelf( Thread_t * thread );
static void prvResumeThread( Thread_t * xThreadId );
static void vPortSystemTickHandler( int sig );
static void vPortStartFirstTask( void );
static void prvPortYieldFromISR( void );
/*-----------------------------------------------------------*/

static void prvFatalError( const char * pcCall,
                           int iErrno ) __attribute__( ( __noreturn__ ) );

void prvFatalError( const char * pcCall,
                    int iErrno )
{
    fprintf( stderr, "%s: %s\n", pcCall, strerror( iErrno ) );
    abort();
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     StackType_t * pxEndOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
    Thread_t * thread;
    pthread_attr_t xThreadAttributes;
    size_t ulStackSize;
    int iRet;

    ( void ) pthread_once( &hSigSetupThread, prvSetupSignalsAndSchedulerPolicy );

    /*
     * Store the additional thread data at the start of the stack.
     */
    thread = ( Thread_t * ) ( pxTopOfStack + 1 ) - 1;
    pxTopOfStack = ( StackType_t * ) thread - 1;

    #ifdef __APPLE__
        pxEndOfStack = ( StackType_t * ) mach_vm_round_page( pxEndOfStack );
    #endif

    ulStackSize = ( size_t ) ( pxTopOfStack + 1 - pxEndOfStack ) * sizeof( *pxTopOfStack );

    #ifdef __APPLE__
        ulStackSize = mach_vm_trunc_page( ulStackSize );
    #endif

    thread->pxCode = pxCode;
    thread->pvParams = pvParameters;
    thread->xDying = pdFALSE;

    /* Ensure ulStackSize is at least PTHREAD_STACK_MIN */
    ulStackSize = ( ulStackSize < PTHREAD_STACK_MIN ) ? PTHREAD_STACK_MIN : ulStackSize;

    pthread_attr_init( &xThreadAttributes );
    iRet = pthread_attr_setstacksize( &xThreadAttributes, ulStackSize );

    if( iRet != 0 )
    {
        fprintf( stderr, "[WARN] pthread_attr_setstacksize failed with return value: %d. Default stack size will be used.\n", iRet );
    }

    thread->ev = event_create();

    vListInitialiseItem( &thread->xThreadListItem );
    listSET_LIST_ITEM_OWNER( &thread->xThreadListItem, thread );

    vPortEnterCritical();

    /* Add the new thread in xThreadList. */
    vListInsertEnd( &xThreadList, &thread->xThreadListItem );

    iRet = pthread_create( &thread->pthread, &xThreadAttributes,
                           prvWaitForStart, thread );

    if( iRet != 0 )
    {
        prvFatalError( "pthread_create", iRet );
    }

    vPortExitCritical();

    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

void vPortStartFirstTask( void )
{
    Thread_t * pxFirstThread = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

    /* Start the first task. */
    prvResumeThread( pxFirstThread );
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
BaseType_t xPortStartScheduler( void )
{
    int iSignal;
    sigset_t xSignals;
    ListItem_t * pxIterator;
    const ListItem_t * pxEndMarker;

    hMainThread = pthread_self();

    /* Start the timer that generates the tick ISR(SIGALRM).
     * Interrupts are disabled here already. */
    prvSetupTimerInterrupt();

    /*
     * Block SIG_RESUME before starting any tasks so the main thread can sigwait on it.
     * To sigwait on an unblocked signal is undefined.
     * https://pubs.opengroup.org/onlinepubs/009604499/functions/sigwait.html
     */
    sigemptyset( &xSignals );
    sigaddset( &xSignals, SIG_RESUME );
    ( void ) pthread_sigmask( SIG_BLOCK, &xSignals, NULL );

    /* Start the first task. */
    vPortStartFirstTask();

    /* Wait until signaled by vPortEndScheduler(). */
    while( xSchedulerEnd != pdTRUE )
    {
        sigwait( &xSignals, &iSignal );
    }

    /* Cancel all the running thread. */
    pxEndMarker = listGET_END_MARKER( &xThreadList );

    for( pxIterator = listGET_HEAD_ENTRY( &xThreadList ); pxIterator != pxEndMarker; pxIterator = listGET_NEXT( pxIterator ) )
    {
        Thread_t * pxThread = ( Thread_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

        pthread_cancel( pxThread->pthread );
        pthread_join( pxThread->pthread, NULL );
        event_delete( pxThread->ev );
    }

    /*
     * clear out the variable that is used to end the scheduler, otherwise
     * subsequent scheduler restarts will end immediately.
     */
    xSchedulerEnd = pdFALSE;

    /* Reset the pthread_once_t structure. This is required if the port
     * starts the scheduler again. */
    hSigSetupThread = PTHREAD_ONCE_INIT;

    /* Restore original signal mask. */
    ( void ) pthread_sigmask( SIG_SETMASK, &xSchedulerOriginalSignalMask, NULL );

    return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
    /* Stop the timer tick thread. */
    xTimerTickThreadShouldRun = false;
    pthread_join( hTimerTickThread, NULL );

    /* Signal the scheduler to exit its loop. */
    xSchedulerEnd = pdTRUE;
    ( void ) pthread_kill( hMainThread, SIG_RESUME );

    pthread_exit( NULL );
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
    if( uxCriticalNesting == 0 )
    {
        vPortDisableInterrupts();
    }

    uxCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
    uxCriticalNesting--;

    /* If we have reached 0 then re-enable the interrupts. */
    if( uxCriticalNesting == 0 )
    {
        vPortEnableInterrupts();
    }
}
/*-----------------------------------------------------------*/

static void prvPortYieldFromISR( void )
{
    Thread_t * xThreadToSuspend;
    Thread_t * xThreadToResume;

    xThreadToSuspend = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

    vTaskSwitchContext();

    xThreadToResume = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

    prvSwitchThread( xThreadToResume, xThreadToSuspend );
}
/*-----------------------------------------------------------*/

void vPortYield( void )
{
    vPortEnterCritical();

    prvPortYieldFromISR();

    vPortExitCritical();
}
/*-----------------------------------------------------------*/

void vPortDisableInterrupts( void )
{
    pthread_sigmask( SIG_BLOCK, &xAllSignals, NULL );
}
/*-----------------------------------------------------------*/

void vPortEnableInterrupts( void )
{
    pthread_sigmask( SIG_UNBLOCK, &xAllSignals, NULL );
}
/*-----------------------------------------------------------*/

UBaseType_t xPortSetInterruptMask( void )
{
    /* Interrupts are always disabled inside ISRs (signals
     * handlers). */
    return ( UBaseType_t ) 0;
}
/*-----------------------------------------------------------*/

void vPortClearInterruptMask( UBaseType_t uxMask )
{
    ( void ) uxMask;
}
/*-----------------------------------------------------------*/

static uint64_t prvGetTimeNs( void )
{
    struct timespec t;

    clock_gettime( CLOCK_MONOTONIC, &t );

    return ( uint64_t ) t.tv_sec * ( uint64_t ) 1000000000UL + ( uint64_t ) t.tv_nsec;
}
/*-----------------------------------------------------------*/

/* commented as part of the code below in vPortSystemTickHandler,
 * to adjust timing according to full demo requirements */
/* static uint64_t prvTickCount; */

static void * prvTimerTickHandler( void * arg )
{
    while( xTimerTickThreadShouldRun )
    {
        /*
         * signal to the active task to cause tick handling or
         * preemption (if enabled)
         */
        TaskHandle_t hCurrentTask;
        Thread_t * thread;

        hCurrentTask = xTaskGetCurrentTaskHandle();

        if( hCurrentTask != NULL )
        {
            thread = prvGetThreadFromTask( hCurrentTask );
            pthread_kill( thread->pthread, SIGALRM );
        }

        usleep( portTICK_RATE_MICROSECONDS );
        pthread_testcancel();
    }

    return NULL;
}
/*-----------------------------------------------------------*/

/*
 * Setup the systick timer to generate the tick interrupts at the required
 * frequency.
 */
void prvSetupTimerInterrupt( void )
{
    xTimerTickThreadShouldRun = true;
    pthread_create( &hTimerTickThread, NULL, prvTimerTickHandler, NULL );

    prvStartTimeNs = prvGetTimeNs();
}
/*-----------------------------------------------------------*/

static void vPortSystemTickHandler( int sig )
{
    Thread_t * pxThreadToSuspend;
    Thread_t * pxThreadToResume;

    ( void ) sig;

/* uint64_t xExpectedTicks; */

    uxCriticalNesting++; /* Signals are blocked in this signal handler. */

    #if ( configUSE_PREEMPTION == 1 )
        pxThreadToSuspend = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );
    #endif

    /* Tick Increment, accounting for any lost signals or drift in
     * the timer. */

/*
 *      Comment code to adjust timing according to full demo requirements
 *      xExpectedTicks = (prvGetTimeNs() - prvStartTimeNs)
 *        / (portTICK_RATE_MICROSECONDS * 1000);
 * do { */
    xTaskIncrementTick();

/*        prvTickCount++;
 *    } while (prvTickCount < xExpectedTicks);
 */

    #if ( configUSE_PREEMPTION == 1 )
        /* Select Next Task. */
        vTaskSwitchContext();

        pxThreadToResume = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

        prvSwitchThread( pxThreadToResume, pxThreadToSuspend );
    #endif

    uxCriticalNesting--;
}
/*-----------------------------------------------------------*/

void vPortThreadDying( void * pxTaskToDelete,
                       volatile BaseType_t * pxPendYield )
{
    Thread_t * pxThread = prvGetThreadFromTask( pxTaskToDelete );

    ( void ) pxPendYield;

    pxThread->xDying = pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortCancelThread( void * pxTaskToDelete )
{
    Thread_t * pxThreadToCancel = prvGetThreadFromTask( pxTaskToDelete );

    /* Remove the thread from xThreadList. */
    vPortEnterCritical();
    uxListRemove( &pxThreadToCancel->xThreadListItem );
    vPortExitCritical();

    /*
     * The thread has already been suspended so it can be safely cancelled.
     */
    pthread_cancel( pxThreadToCancel->pthread );
    pthread_join( pxThreadToCancel->pthread, NULL );
    event_delete( pxThreadToCancel->ev );
}
/*-----------------------------------------------------------*/

static void * prvWaitForStart( void * pvParams )
{
    Thread_t * pxThread = pvParams;

    prvSuspendSelf( pxThread );

    /* Resumed for the first time, unblocks all signals. */
    uxCriticalNesting = 0;
    vPortEnableInterrupts();

    /* Call the task's entry point. */
    pxThread->pxCode( pxThread->pvParams );

    /* A function that implements a task must not exit or attempt to return to
     * its caller as there is nothing to return to. If a task wants to exit it
     * should instead call vTaskDelete( NULL ). Artificially force an assert()
     * to be triggered if configASSERT() is defined, so application writers can
     * catch the error. */
    configASSERT( pdFALSE );

    return NULL;
}
/*-----------------------------------------------------------*/

static void prvSwitchThread( Thread_t * pxThreadToResume,
                             Thread_t * pxThreadToSuspend )
{
    BaseType_t uxSavedCriticalNesting;

    if( pxThreadToSuspend != pxThreadToResume )
    {
        /*
         * Switch tasks.
         *
         * The critical section nesting is per-task, so save it on the
         * stack of the current (suspending thread), restoring it when
         * we switch back to this task.
         */
        uxSavedCriticalNesting = uxCriticalNesting;

        prvResumeThread( pxThreadToResume );

        if( pxThreadToSuspend->xDying == pdTRUE )
        {
            pthread_exit( NULL );
        }

        prvSuspendSelf( pxThreadToSuspend );

        uxCriticalNesting = uxSavedCriticalNesting;
    }
}
/*-----------------------------------------------------------*/

static void prvSuspendSelf( Thread_t * thread )
{
    /*
     * Suspend this thread by waiting for a pthread_cond_signal event.
     *
     * A suspended thread must not handle signals (interrupts) so
     * all signals must be blocked by calling this from:
     *
     * - Inside a critical section (vPortEnterCritical() /
     *   vPortExitCritical()).
     *
     * - From a signal handler that has all signals masked.
     *
     * - A thread with all signals blocked with pthread_sigmask().
     */
    event_wait( thread->ev );
    pthread_testcancel();
}

/*-----------------------------------------------------------*/

static void prvResumeThread( Thread_t * xThreadId )
{
    if( pthread_self() != xThreadId->pthread )
    {
        event_signal( xThreadId->ev );
    }
}
/*-----------------------------------------------------------*/

static void prvSetupSignalsAndSchedulerPolicy( void )
{
    struct sigaction sigtick;
    int iRet;

    hMainThread = pthread_self();

    /* Setup thread list to record all the task which are not deleted. */
    vListInitialise( &xThreadList );

    /* Initialise common signal masks. */
    sigfillset( &xAllSignals );

    /* Don't block SIGINT so this can be used to break into GDB while
     * in a critical section. */
    sigdelset( &xAllSignals, SIGINT );

    /*
     * Block all signals in this thread so all new threads
     * inherits this mask.
     *
     * When a thread is resumed for the first time, all signals
     * will be unblocked.
     */
    ( void ) pthread_sigmask( SIG_SETMASK,
                              &xAllSignals,
                              &xSchedulerOriginalSignalMask );

    sigtick.sa_flags = 0;
    sigtick.sa_handler = vPortSystemTickHandler;
    sigfillset( &sigtick.sa_mask );

    iRet = sigaction( SIGALRM, &sigtick, NULL );

    if( iRet == -1 )
    {
        prvFatalError( "sigaction", errno );
    }
}
/*-----------------------------------------------------------*/

uint32_t ulPortGetRunTime( void )
{
    struct tms xTimes;

    times( &xTimes );

    return ( uint32_t ) xTimes.tms_utime;
}
/*-----------------------------------------------------------*/
