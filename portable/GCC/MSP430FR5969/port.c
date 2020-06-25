/*
 * FreeRTOS Kernel V10.3.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Standard includes. */
#include <stdlib.h>
#include <signal.h>

#include <msp430.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the MSP430 port.
 *----------------------------------------------------------*/

/* Constants required for hardware setup.  The tick ISR runs off the ACLK,
not the MCLK. */
#define portACLK_FREQUENCY_HZ           ( ( TickType_t ) 32768 )
#define portINITIAL_CRITICAL_NESTING    ( ( uint16_t ) 10 )
#define portFLAGS_INT_ENABLED           ( ( StackType_t ) 0x08 )

/* We require the address of the pxCurrentTCB variable, but don't want to know
any details of its type. */
typedef void TCB_t;
extern volatile TCB_t * volatile pxCurrentTCB;

/* Most ports implement critical sections by placing the interrupt flags on
the stack before disabling interrupts.  Exiting the critical section is then
simply a case of popping the flags from the stack.  As mspgcc does not use
a frame pointer this cannot be done as modifying the stack will clobber all
the stack variables.  Instead each task maintains a count of the critical
section nesting depth.  Each time a critical section is entered the count is
incremented.  Each time a critical section is left the count is decremented -
with interrupts only being re-enabled if the count is zero.

usCriticalNesting will get set to zero when the scheduler starts, but must
not be initialised to zero as this will cause problems during the startup
sequence. */
volatile uint16_t usCriticalNesting = portINITIAL_CRITICAL_NESTING;
/*-----------------------------------------------------------*/

/*
 * Macro to save a task context to the task stack.  This simply pushes all the
 * general purpose msp430 registers onto the stack, followed by the
 * usCriticalNesting value used by the task.  Finally the resultant stack
 * pointer value is saved into the task control block so it can be retrieved
 * the next time the task executes.
 */
#ifdef __LARGE_DATA_MODEL__
#define portSAVE_CONTEXT()                                   \
    asm volatile (  "pushm.a #12, r15                 \n\t"  \
                    "movx.w &usCriticalNesting, r14   \n\t"  \
                    "pushm.a #1, r14                  \n\t"  \
                    "movx.a &pxCurrentTCB, r12        \n\t"  \
                    "movx.a sp, 0(r12)                \n\t"  \
                );
#else
#define portSAVE_CONTEXT()                                   \
    asm volatile (  "pushm.w #12, r15                 \n\t"  \
                    "mov.w &usCriticalNesting, r14    \n\t"  \
                    "push.w r14                       \n\t"  \
                    "mov.w &pxCurrentTCB, r12         \n\t"  \
                    "mov.w sp, 0(r12)                 \r\t"  \
                );
#endif

/*
 * Macro to restore a task context from the task stack.  This is effectively
 * the reverse of portSAVE_CONTEXT().  First the stack pointer value is
 * loaded from the task control block.  Next the value for usCriticalNesting
 * used by the task is retrieved from the stack - followed by the value of all
 * the general purpose msp430 registers.
 *
 */
#ifdef __LARGE_DATA_MODEL__
#define portRESTORE_CONTEXT()                                \
    asm volatile (  "movx.a &pxCurrentTCB, r12        \n\t"  \
                    "movx.a @r12, sp                  \n\t"  \
                    "popm.a #1, r15                   \n\t"  \
                    "movx.w r15, &usCriticalNesting   \n\t"  \
                    "popm.a #12, r15                  \n\t"  \
                    "nop                              \n\t"  \
                    "pop.w sr                         \n\t"  \
                    "nop                              \n\t"  \
                    "reta                             \n\t"  \
                );
#else
#define portRESTORE_CONTEXT()                                \
    asm volatile (  "mov.w  &pxCurrentTCB, r12       \n\t"   \
                    "mov.w @r12, sp                  \n\t"   \
                    "pop.w r15                       \n\t"   \
                    "mov.w r15, &usCriticalNesting   \n\t"   \
                    "popm.w #12, r15                 \n\t"   \
                    "nop                             \n\t"   \
                    "pop.w sr                        \n\t"   \
                    "nop                             \n\t"   \
                    "ret                             \n\t"   \
                );
#endif
/*-----------------------------------------------------------*/

/*
 * Sets up the periodic ISR used for the RTOS tick.  This uses timer 0, but
 * could have alternatively used the watchdog timer or timer 1.
 */
static void prvSetupTimerInterrupt( void );
/*-----------------------------------------------------------*/

/*
 * Initialise the stack of a task to look exactly as if a call to
 * portSAVE_CONTEXT had been called.
 *
 * See the header file portable.h.
 */

StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
    uint16_t *pusTopOfStack;
    uint32_t *pulTopOfStack, ulTemp;

    /*
        Place a few bytes of known values on the bottom of the stack.
        This is just useful for debugging and can be included if required.

        *pxTopOfStack = ( StackType_t ) 0x1111;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0x2222;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0x3333;
        pxTopOfStack--;
    */

    /* Data types are need either 16 bits or 32 bits depending on the data
    and code model used. */
    if( sizeof( pxCode ) == sizeof( uint16_t ) )
    {
        pusTopOfStack = ( uint16_t * ) pxTopOfStack;
        ulTemp = ( uint32_t ) pxCode;
        *pusTopOfStack = ( uint16_t ) ulTemp;
    }
    else
    {
        /* Make room for a 20 bit value stored as a 32 bit value. */
        pusTopOfStack = ( uint16_t * ) pxTopOfStack;
        pusTopOfStack--;
        pulTopOfStack = ( uint32_t * ) pusTopOfStack;
        *pulTopOfStack = ( uint32_t ) pxCode;
    }

    pusTopOfStack--;
    *pusTopOfStack = portFLAGS_INT_ENABLED;
    pusTopOfStack -= ( sizeof( StackType_t ) / 2 );

    /* From here on the size of stacked items depends on the memory model. */
    pxTopOfStack = ( StackType_t * ) pusTopOfStack;

    /* Next the general purpose registers. */
    #ifdef PRELOAD_REGISTER_VALUES
        *pxTopOfStack = ( StackType_t ) 0xffff;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0xeeee;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0xdddd;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) pvParameters;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0xbbbb;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0xaaaa;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0x9999;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0x8888;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0x7777;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0x6666;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0x5555;
        pxTopOfStack--;
        *pxTopOfStack = ( StackType_t ) 0x4444;
        pxTopOfStack--;
    #else
        pxTopOfStack -= 3;
        *pxTopOfStack = ( StackType_t ) pvParameters;
        pxTopOfStack -= 9;
    #endif

    /* A variable is used to keep track of the critical section nesting.
    This variable has to be stored as part of the task context and is
    initially set to zero. */
    *pxTopOfStack = ( StackType_t ) portNO_CRITICAL_SECTION_NESTING;

    /* Return a pointer to the top of the stack we have generated so this can
    be stored in the task control block for the task. */
    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
    /* Setup the hardware to generate the tick.  Interrupts are disabled when
    this function is called. */
    prvSetupTimerInterrupt();

    /* Restore the context of the first task that is going to run. */
    portRESTORE_CONTEXT();

    /* Should not get here as the tasks are now running! */
    return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
    /* It is unlikely that the MSP430 port will get stopped.  If required simply
    disable the tick interrupt here. */
}
/*-----------------------------------------------------------*/

/*
 * Manual context switch called by portYIELD or taskYIELD.
 *
 * The first thing we do is save the registers so we can use a naked attribute.
 */

void vPortYield( void ) __attribute__ ( ( naked ) );
void vPortYield( void )
{
    asm volatile ( "push.w  sr" );

    portDISABLE_INTERRUPTS();
    portSAVE_CONTEXT();

    vTaskSwitchContext();

    portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

/*
 * Hardware initialisation to generate the RTOS tick.  This uses timer 0
 * but could alternatively use the watchdog timer or timer 1.
 */
static void prvSetupTimerInterrupt( void )
{
    vApplicationSetupTimerInterrupt();
}
/*-----------------------------------------------------------*/

/*
 * The interrupt service routine used depends on whether the pre-emptive
 * scheduler is being used or not.
 */

#if configUSE_PREEMPTION == 1
void vPortPreemptiveTickISR(void)
{
    asm volatile("push.w sr");
    portSAVE_CONTEXT();

    if(xTaskIncrementTick() != pdFALSE)
    {
        vTaskSwitchContext();
    }

    portRESTORE_CONTEXT();
}

__attribute__((interrupt(configTICK_VECTOR))) void prvTickISR(void)
{
    __bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );
    vPortPreemptiveTickISR();
}
#else
void vPortCooperativeTickISR(void)
{
    asm volatile("push.w sr");
    portSAVE_CONTEXT();

    xTaskIncrementTick();

    portRESTORE_CONTEXT();
}

__attribute__((interrupt(configTICK_VECTOR))) void prvTickISR(void)
{
    __bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );

    vPortCooperativeTickISR();
}
#endif
