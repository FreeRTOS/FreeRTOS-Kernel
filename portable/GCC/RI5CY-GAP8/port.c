/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the RI5CY-GAP8 port.
 *----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "system_gap8.h"

/* Macro definitions. */
#include "chip_specific_extensions/gap8/freertos_risc_v_chip_specific_extensions.h"

/* Internal Functions. */

/* Setup timer to enable Systick interruptions. */
void prvSetupTimerInterrupt( void );

#if (portUSING_MPU_WRAPPERS == 1)
/* Setup MPU. */
void prvSetupMPU( void ) PRIVILEGED_FUNCTION;

/*
 * Checks to see if being called from the context of an unprivileged task, and
 * if so raises the privilege level and returns false - otherwise does nothing
 * other than return true.
 */
BaseType_t xPortRaisePrivilege( void );

/* Reset privilege level after call to xPortRaisePrivilege(). */
void vPortResetPrivilege( BaseType_t xRunningPrivileged );
#endif /* portUSING_MPU_WRAPPERS == 1 */

/* Scheduler utilities. */

/* Critical sections management. */
void vPortEnter_Critical( void );
void vPortExit_Critical( void );
uint32_t uPortSet_Interrupt_Mask_From_ISR( void );
void vPortClear_Interrupt_Mask_From_ISR( uint32_t irqSet );

/* FreeRTOS Handlers in gap8_it.c. */

/* Variables. */
volatile uint32_t ulCriticalNesting = 0ul;

/*-----------------------------------------------------------*/
/* See header file for description. */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack,
                                    TaskFunction_t pxCode,
                                    void *pvParameters )
{
    /* Few bytes on the bottom of the stack. May be useful for debugging. */
    pxTopOfStack--;
    *pxTopOfStack = 0xdeedfeed;

    /* GAP8 extensions. */
    {
        /* Hardware Loop registers. */
        pxTopOfStack -= (uint32_t) portGAP8_ADDITIONAL_EXTENSIONS;
    }
    /* Control and status registers saved if R/W. */
    {
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) pxCode; /* MEPC */
        pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) portINITIAL_MSTATUS; /* MSTATUS */
    }
    /* General purpose registers saved. sp reg stored in Task Control Block. */
    {
	pxTopOfStack -= 27; /* a1-a7 + t0-t6 +  s0-11 */
	*pxTopOfStack = ( StackType_t ) pvParameters; /* a0 */
	pxTopOfStack -= 1;
        *pxTopOfStack = ( StackType_t ) pxCode; /* ra */
    }

/*
 * Task's stack view.
 *     LOW
 * *************  <------ pxTopOfStack
 * *    ra     *
 * *    a0     *  <------ Parameters sent to task
 * *    a1     *
 * *    --     *
 * *    a7     *
 * *    t0     *
 * *    --     *
 * *    t6     *
 * *    s0     *
 * *    --     *
 * *    s11    *
 * *-----------*
 * *  MSTATUS  *  <------ Initial mstatus for the task
 * *   MEPC    *  <------ MEPC contains address of task's function, jump to it after mret.
 * *-----------*
 * *  HW loop  *
 * *===========*
 * * deedfeed  *
 * *************
 *    HIGH
 */
    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
    /* Do not implement. */
}
/*-----------------------------------------------------------*/

/* Setup Systick timer to generate tick interrupts. */
void prvSetupTimerInterrupt( void )
{
    /* Compared value. */
    /* SysTick->CMP_LO = ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1ul; */
    system_setup_systick((uint32_t) configTICK_RATE_HZ);
}
/*-----------------------------------------------------------*/

#if portUSING_MPU_WRAPPERS == 1
void prvSetupMPU( void )
{
}
/*-----------------------------------------------------------*/

void vPortStoreTaskMPUSettings( xMPU_SETTINGS *xMPUSettings,
				const struct xMEMORY_REGION * const xRegions,
				StackType_t *pxBottomOfStack,
				uint32_t ulStackDepth )
{
}
/*-----------------------------------------------------------*/

BaseType_t xPortRaisePrivilege( void )
{
    return 1;
}
/*-----------------------------------------------------------*/

void vPortResetPrivilege( BaseType_t xRunningPrivileged )
{
    ( void ) xRunningPrivileged;
}
#endif /* portUSING_MPU_WRAPPERS == 1 */
/*-----------------------------------------------------------*/

void vPortEnter_Critical( void )
{
    portDISABLE_INTERRUPTS();
    /* Increment nesting value everytime a critical section is entered. */
    ulCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExit_Critical( void )
{
    /* Decrement nesting value everytime a critical section is exit. */
    if( ulCriticalNesting > 0 )
    {
	ulCriticalNesting--;
	if( ulCriticalNesting == 0 )
	{
	    /* If no more in any critical sections, enable interruptions. */
	    portENABLE_INTERRUPTS();
	}
    }
}
/*-----------------------------------------------------------*/

uint32_t uPortSet_Interrupt_Mask_From_ISR( void )
{
    /* No nested IRQ, so IRQ are either enabled or disabled.  */
    return __disable_irq();
}
/*-----------------------------------------------------------*/

void vPortClear_Interrupt_Mask_From_ISR( uint32_t irqSet )
{
    __restore_irq(irqSet);
    /* No nested IRQ, so IRQ are either enabled or disabled.  */
}
/*-----------------------------------------------------------*/
