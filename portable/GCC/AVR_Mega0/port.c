/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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
 */

#include <stdlib.h>

#include <avr/interrupt.h>
#include "porthardware.h"
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------
* Implementation of functions defined in portable.h for the AVR port.
*----------------------------------------------------------*/

/* Start tasks with interrupts enables. */
#define portFLAGS_INT_ENABLED    ( ( StackType_t ) 0x80 )

/*-----------------------------------------------------------*/

/* We require the address of the pxCurrentTCB variable, but don't want to know
 * any details of its type. */
typedef void RTOS_TCB_t;
extern volatile RTOS_TCB_t * volatile pxCurrentTCB;

/*-----------------------------------------------------------*/

/*
 * Macro to save all the general purpose registers, the save the stack pointer
 * into the TCB.
 *
 * The first thing we do is save the flags then disable interrupts.  This is to
 * guard our stack against having a context switch interrupt after we have already
 * pushed the registers onto the stack - causing the 32 registers to be on the
 * stack twice.
 *
 * r1 is set to zero as the compiler expects it to be thus, however some
 * of the math routines make use of R1.
 *
 * The interrupts will have been disabled during the call to portSAVE_CONTEXT()
 * so we need not worry about reading/writing to the stack pointer.
 */

#define portSAVE_CONTEXT()                              \
    asm volatile ( "push  r0                      \n\t" \
                   "in    r0, __SREG__            \n\t" \
                   "cli                           \n\t" \
                   "push  r0                      \n\t" \
                   "push  r1                      \n\t" \
                   "clr   r1                      \n\t" \
                   "push  r2                      \n\t" \
                   "push  r3                      \n\t" \
                   "push  r4                      \n\t" \
                   "push  r5                      \n\t" \
                   "push  r6                      \n\t" \
                   "push  r7                      \n\t" \
                   "push  r8                      \n\t" \
                   "push  r9                      \n\t" \
                   "push  r10                     \n\t" \
                   "push  r11                     \n\t" \
                   "push  r12                     \n\t" \
                   "push  r13                     \n\t" \
                   "push  r14                     \n\t" \
                   "push  r15                     \n\t" \
                   "push  r16                     \n\t" \
                   "push  r17                     \n\t" \
                   "push  r18                     \n\t" \
                   "push  r19                     \n\t" \
                   "push  r20                     \n\t" \
                   "push  r21                     \n\t" \
                   "push  r22                     \n\t" \
                   "push  r23                     \n\t" \
                   "push  r24                     \n\t" \
                   "push  r25                     \n\t" \
                   "push  r26                     \n\t" \
                   "push  r27                     \n\t" \
                   "push  r28                     \n\t" \
                   "push  r29                     \n\t" \
                   "push  r30                     \n\t" \
                   "push  r31                     \n\t" \
                   "lds   r26, pxCurrentTCB       \n\t" \
                   "lds   r27, pxCurrentTCB + 1   \n\t" \
                   "in    r0, __SP_L__            \n\t" \
                   "st    x+, r0                  \n\t" \
                   "in    r0, __SP_H__            \n\t" \
                   "st    x+, r0                  \n\t" );

/*
 * Opposite to portSAVE_CONTEXT().  Interrupts will have been disabled during
 * the context save so we can write to the stack pointer.
 */

#define portRESTORE_CONTEXT()                           \
    asm volatile ( "lds   r26, pxCurrentTCB       \n\t" \
                   "lds   r27, pxCurrentTCB + 1   \n\t" \
                   "ld    r28, x+                 \n\t" \
                   "out   __SP_L__, r28           \n\t" \
                   "ld    r29, x+                 \n\t" \
                   "out   __SP_H__, r29           \n\t" \
                   "pop   r31                     \n\t" \
                   "pop   r30                     \n\t" \
                   "pop   r29                     \n\t" \
                   "pop   r28                     \n\t" \
                   "pop   r27                     \n\t" \
                   "pop   r26                     \n\t" \
                   "pop   r25                     \n\t" \
                   "pop   r24                     \n\t" \
                   "pop   r23                     \n\t" \
                   "pop   r22                     \n\t" \
                   "pop   r21                     \n\t" \
                   "pop   r20                     \n\t" \
                   "pop   r19                     \n\t" \
                   "pop   r18                     \n\t" \
                   "pop   r17                     \n\t" \
                   "pop   r16                     \n\t" \
                   "pop   r15                     \n\t" \
                   "pop   r14                     \n\t" \
                   "pop   r13                     \n\t" \
                   "pop   r12                     \n\t" \
                   "pop   r11                     \n\t" \
                   "pop   r10                     \n\t" \
                   "pop   r9                      \n\t" \
                   "pop   r8                      \n\t" \
                   "pop   r7                      \n\t" \
                   "pop   r6                      \n\t" \
                   "pop   r5                      \n\t" \
                   "pop   r4                      \n\t" \
                   "pop   r3                      \n\t" \
                   "pop   r2                      \n\t" \
                   "pop   r1                      \n\t" \
                   "pop   r0                      \n\t" \
                   "out   __SREG__, r0            \n\t" \
                   "pop   r0                      \n\t" );

/*-----------------------------------------------------------*/

/*
 * Perform hardware setup to enable ticks from timer.
 */
static void prvSetupTimerInterrupt( void );
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
    uint16_t usAddress;

    /*lint -e950 -e611 -e923 Lint doesn't like this much - but nothing I can do about it. */

    /* Place a few bytes of known values on the bottom of the stack.
     * This is just useful for debugging. Uncomment if needed. */
    /* *pxTopOfStack = 0x11; */
    /* pxTopOfStack--; */
    /* *pxTopOfStack = 0x22; */
    /* pxTopOfStack--; */
    /* *pxTopOfStack = 0x33; */
    /* pxTopOfStack--; */

    /* The start of the task code will be popped off the stack last, so place
     * it on first. */
    usAddress = ( uint16_t ) pxCode;
    *pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
    pxTopOfStack--;

    usAddress >>= 8;
    *pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
    pxTopOfStack--;

    /* Next simulate the stack as if after a call to portSAVE_CONTEXT().
    *  portSAVE_CONTEXT places the flags on the stack immediately after r0
    *  to ensure the interrupts get disabled as soon as possible, and so ensuring
    *  the stack use is minimal should a context switch interrupt occur. */
    *pxTopOfStack = ( StackType_t ) 0x00; /* R0 */
    pxTopOfStack--;
    *pxTopOfStack = portFLAGS_INT_ENABLED;
    pxTopOfStack--;

    /* Now the remaining registers.   The compiler expects R1 to be 0. */
    *pxTopOfStack = ( StackType_t ) 0x00; /* R1 */

    /* Leave R2 - R23 untouched */
    pxTopOfStack -= 23;

    /* Place the parameter on the stack in the expected location. */
    usAddress = ( uint16_t ) pvParameters;
    *pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
    pxTopOfStack--;

    usAddress >>= 8;
    *pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );

    /* Leave register R26 - R31 untouched */
    pxTopOfStack -= 7;

    /*lint +e950 +e611 +e923 */

    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
    /* Setup the hardware to generate the tick. */
    prvSetupTimerInterrupt();

    /* Restore the context of the first task that is going to run. */
    portRESTORE_CONTEXT();

    /* Simulate a function call end as generated by the compiler.  We will now
     * jump to the start of the task the context of which we have just restored. */
    asm volatile ( "ret" );

    /* Should not get here. */
    return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
    /* vPortEndScheduler is not implemented in this port. */
}
/*-----------------------------------------------------------*/

/*
 * Manual context switch.  The first thing we do is save the registers so we
 * can use a naked attribute.
 */
void vPortYield( void ) __attribute__( ( naked ) );
void vPortYield( void )
{
    portSAVE_CONTEXT();
    vTaskSwitchContext();
    portRESTORE_CONTEXT();
    asm volatile ( "ret" );
}
/*-----------------------------------------------------------*/

/*
 * Manual context switch callable from ISRs. The first thing
 * we do is save the registers so we can use a naked attribute.
 */
void vPortYieldFromISR( void ) __attribute__( ( naked ) );
void vPortYieldFromISR( void )
{
    portSAVE_CONTEXT();
    vTaskSwitchContext();
    portRESTORE_CONTEXT();
    asm volatile ( "reti" );
}
/*-----------------------------------------------------------*/

/*
 * Context switch function used by the tick.  This must be identical to
 * vPortYield() from the call to vTaskSwitchContext() onwards.  The only
 * difference from vPortYield() is the tick count is incremented as the
 * call comes from the tick ISR.
 */
void vPortYieldFromTick( void ) __attribute__( ( naked ) );
void vPortYieldFromTick( void )
{
    portSAVE_CONTEXT();

    if( xTaskIncrementTick() != pdFALSE )
    {
        vTaskSwitchContext();
    }

    portRESTORE_CONTEXT();

    asm volatile ( "reti" );
}
/*-----------------------------------------------------------*/

/*
 * Setup timer to generate a tick interrupt.
 */
static void prvSetupTimerInterrupt( void )
{
    TICK_init();
}
/*-----------------------------------------------------------*/

#if configUSE_PREEMPTION == 1

/*
 * Tick ISR for preemptive scheduler.  We can use a naked attribute as
 * the context is saved at the start of vPortYieldFromTick().  The tick
 * count is incremented after the context is saved.
 */
    ISR( TICK_INT_vect, ISR_NAKED )
    {
        /* Clear tick interrupt flag. */
        CLR_INT( INT_FLAGS, INT_MASK );

        vPortYieldFromTick();

        asm volatile ( "reti" );
    }
#else  /* if configUSE_PREEMPTION == 1 */

/*
 * Tick ISR for the cooperative scheduler.  All this does is increment the
 * tick count.  We don't need to switch context, this can only be done by
 * manual calls to taskYIELD();
 */
    ISR( TICK_INT_vect )
    {
        /* Clear tick interrupt flag. */
        INT_FLAGS = INT_MASK;
        xTaskIncrementTick();
    }
#endif /* if configUSE_PREEMPTION == 1 */
