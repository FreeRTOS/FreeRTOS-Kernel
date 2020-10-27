/*
 * FreeRTOS Kernel V10.4.1
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 * 1 tab == 4 spaces!
 */
 
#include "port.h"

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* TriCore specific includes. */
#include <machine/intrinsics.h>
#include <machine/cint.h>
#include <machine/wdtcon.h>
#include <tc38xa/Ifx_reg.h>
#include <tc38xa/IfxScu_reg.h>
#include "interrupts.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#if configCHECK_FOR_STACK_OVERFLOW > 0
	#error "Stack checking cannot be used with this port, as, unlike most ports, the pxTopOfStack member of the TCB is consumed CSA.  CSA starvation, loosely equivalent to stack overflow, will result in a trap exception."
	/* The stack pointer is accessible using portCSA_TO_ADDRESS( portCSA_TO_ADDRESS( pxCurrentTCB->pxTopOfStack )[ 0 ] )[ 2 ]; */
#endif /* configCHECK_FOR_STACK_OVERFLOW */

#define CPU_ID (_mfcr(CPU_CORE_ID) & 0x0f)

static volatile Ifx_STM* STMs[4] = {&MODULE_STM0, &MODULE_STM1, &MODULE_STM2, &MODULE_STM3};
static const unsigned short STM_SRCs[4] = {SRC_ID_STM0SR0, SRC_ID_STM1SR0, SRC_ID_STM2SR0, SRC_ID_STM3SR0};
static volatile Ifx_INT_SRB* SRBs[4] = {&INT_SRB0, &INT_SRB1, &INT_SRB2, &INT_SRB3};
static const unsigned short GPSRs[4] = {SRC_ID_GPSR00, SRC_ID_GPSR10, SRC_ID_GPSR20, SRC_ID_GPSR30};

typedef struct
{
	unsigned int PCXI, PSW, A10, A11, D8, D9, D10, D11, A12, A13, A14, A15, D12, D13, D14, D15;
} UPPER_CONTEXT;

/*-----------------------------------------------------------*/

/* System register Definitions. */
#define portSYSTEM_PROGRAM_STATUS_WORD					( 0x000008FFUL ) /* Supervisor Mode, MPU Register Set 0 and Call Depth Counting disabled. */
#define portINITIAL_PRIVILEGED_PROGRAM_STATUS_WORD		( 0x000014FFUL ) /* IO Level 1, MPU Register Set 1 and Call Depth Counting disabled. */
#define portINITIAL_UNPRIVILEGED_PROGRAM_STATUS_WORD	( 0x000010FFUL ) /* IO Level 0, MPU Register Set 1 and Call Depth Counting disabled. */
//#define portINITIAL_PCXI_UPPER_CONTEXT_WORD	        ( 0x00C00000UL ) /* The lower 20 bits identify the CSA address. */
//#define portINITIAL_PCXI_UPPER_CONTEXT_WORD			( 0x10300000UL ) // ATENlower 20 bits identify the CSA address. */
#define portINITIAL_PCXI_UPPER_CONTEXT_WORD				( 0x00300000UL ) // ATEN, default value as read from the CPU after init
#define portINITIAL_SYSCON								( 0x00000000UL ) /* MPU Disable. */

/* CSA manipulation macros. */
#define portCSA_FCX_MASK					( 0x000FFFFFUL )

/* OS Interrupt and Trap mechanisms. */
#define portRESTORE_PSW_MASK				( ~( 0x000000FFUL ) )
#define portSYSCALL_TRAP					( 6 )

/* Each CSA contains 16 words of data. */
#define portNUM_WORDS_IN_CSA				( 16 )

/* The interrupt enable bit in the PCP_SRC register. */
#define portENABLE_CPU_INTERRUPT 			( 1U << 12U )
/*-----------------------------------------------------------*/

/*
 * Perform any hardware configuration necessary to generate the tick interrupt.
 */
static void prvSystemTickHandler( int ) __attribute__((longcall));
static void prvERUISRHandler( int ) __attribute__((longcall));
static void prvSetupTimerInterrupt( void );

#define ERUInterruptCoreID 0
static void prvSetupERUInterrupt(void);

/*
 * Priority 1 interrupt handler for yields pended from an interrupt.
 */
static void prvInterruptYield( int iTrapIdentification );

/*-----------------------------------------------------------*/

/* This reference is required by the save/restore context macros. */
extern volatile uint32_t *pxCurrentTCB;

extern TaskHandle_t xTaskHandle0[E_TASKS_CPU0_SIZE];

/* Precalculate the compare match value at compile time. */
static const uint32_t ulCompareMatchValue = ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ );

/*-----------------------------------------------------------*/

StackType_t *pxPortInitialiseStack( StackType_t * pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
uint32_t *pulUpperCSA = NULL;
uint32_t *pulLowerCSA = NULL;

	/* 16 Address Registers (4 Address registers are global), 16 Data
	Registers, and 3 System Registers.

	There are 3 registers that track the CSAs.
		FCX points to the head of globally free set of CSAs.
		PCX for the task needs to point to Lower->Upper->NULL arrangement.
		LCX points to the last free CSA so that corrective action can be taken.

	Need two CSAs to store the context of a task.
		The upper context contains D8-D15, A10-A15, PSW and PCXI->NULL.
		The lower context contains D0-D7, A2-A7, A11 and PCXI->UpperContext.
		The pxCurrentTCB->pxTopOfStack points to the Lower Context RSLCX matching the initial BISR.
		The Lower Context points to the Upper Context ready for the return from the interrupt handler.

	 The Real stack pointer for the task is stored in the A10 which is restored
	 with the upper context. */

	/* Have to disable interrupts here because the CSAs are going to be
	manipulated. */
	portENTER_CRITICAL();
	{
		/* DSync to ensure that buffering is not a problem. */
		_dsync();

		/* Consume two free CSAs. */
		pulLowerCSA = portCSA_TO_ADDRESS( __MFCR( $FCX ) );
		if( NULL != pulLowerCSA )
		{
			/* The Lower Links to the Upper. */
			pulUpperCSA = portCSA_TO_ADDRESS( pulLowerCSA[ 0 ] );
		}

		/* Check that we have successfully reserved two CSAs. */
		if( ( NULL != pulLowerCSA ) && ( NULL != pulUpperCSA ) )
		{
			/* Remove the two consumed CSAs from the free CSA list. */
			_disable();
			_dsync();
			_mtcr( $FCX, pulUpperCSA[ 0 ] );
			_isync();
			_enable();
		}
		else
		{
			/* Simply trigger a context list depletion trap. */
			_svlcx();
		}
	}
	portEXIT_CRITICAL();

	/* Clear the upper CSA. */
	memset( pulUpperCSA, 0, portNUM_WORDS_IN_CSA * sizeof( uint32_t ) );

	/* Upper Context. */
	pulUpperCSA[ 2 ] = ( uint32_t )pxTopOfStack;		/* A10;	Stack Return aka Stack Pointer */
	pulUpperCSA[ 1 ] = portSYSTEM_PROGRAM_STATUS_WORD;		/* PSW	*/

	/* Clear the lower CSA. */
	memset( pulLowerCSA, 0, portNUM_WORDS_IN_CSA * sizeof( uint32_t ) );

	/* Lower Context. */
	pulLowerCSA[ 8 ] = ( uint32_t ) pvParameters;		/* A4;	Address Type Parameter Register	*/
	pulLowerCSA[ 1 ] = ( uint32_t ) pxCode;			/* A11;	Return Address aka RA */

	/* PCXI pointing to the Upper context. */
	pulLowerCSA[ 0 ] = ( portINITIAL_PCXI_UPPER_CONTEXT_WORD | ( uint32_t ) portADDRESS_TO_CSA( pulUpperCSA ) );

	/* Save the link to the CSA in the top of stack. */
	pxTopOfStack = (uint32_t * ) portADDRESS_TO_CSA( pulLowerCSA );

	/* DSync to ensure that buffering is not a problem. */
	_dsync();

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

int32_t xPortStartScheduler( void )
{
	extern void vTrapInstallHandlers( void );
	uint32_t ulMFCR = 0UL;
	uint32_t *pulUpperCSA = NULL;
	uint32_t *pulLowerCSA = NULL;

	/* prevent compiler warnings */
	(void)pulUpperCSA;

	/* Interrupts at or below configMAX_SYSCALL_INTERRUPT_PRIORITY are disable
	when this function is called. */

	/* Set-up the ERU interrupt. */
	prvSetupERUInterrupt();

	/* Set-up the timer interrupt. */
	prvSetupTimerInterrupt();

	/* Install the Trap Handlers. */
	// vTrapInstallHandlers();

	/* Install the Syscall Handler for yield calls. */
	// if( 0 == _install_trap_handler( portSYSCALL_TRAP, prvTrapYield ) )
	// {
	// 	/* Failed to install the yield handler, force an assert. */
	// 	configASSERT( ( ( volatile void * ) NULL ) );
	// }

	/* Enable and install the priority 1 interrupt for pending context switches from an ISR. */
	InterruptInstall(GPSRs[CPU_ID], prvInterruptYield, configKERNEL_YIELD_PRIORITY, 0);       //ATEN

	_disable();

	/* Load the initial SYSCON. */
	_mtcr( $SYSCON, portINITIAL_SYSCON );
	_isync();

	/* ENDINIT has already been applied in the 'cstart.c' code. */

	/* Clear the PSW.CDC to enable the use of an RFE without it generating an
	exception because this code is not genuinely in an exception. */
	ulMFCR = __MFCR( $PSW );
	ulMFCR &= portRESTORE_PSW_MASK;
	_dsync();
	_mtcr( $PSW, ulMFCR );
	_isync();

	/* Finally, perform the equivalent of a portRESTORE_CONTEXT() */
	pulLowerCSA = portCSA_TO_ADDRESS( ( *pxCurrentTCB ) );
	pulUpperCSA = portCSA_TO_ADDRESS( pulLowerCSA[0] );

	_dsync();
	_mtcr( $PCXI, *pxCurrentTCB );
	_isync();
	_nop();
	_rslcx();
	_nop();


	/* Return to the first task selected to execute. */
	__asm volatile( "rfe" );

	/* Will not get here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
	unsigned short cpuid = CPU_ID;

	//  Install handler for timer interrupt & reset interrupt flag
	STMs[cpuid]->ISCR.U = 1;
	InterruptInstall(STM_SRCs[cpuid], prvSystemTickHandler, configKERNEL_INTERRUPT_PRIORITY, 0);

	// prepare compare register for first interrupt
	STMs[cpuid]->CMP[0].U = STMs[cpuid]->TIM0.U + ulCompareMatchValue;
	STMs[cpuid]->CMCON.U  = 31;
	STMs[cpuid]->OCS.B.SUS = 2;
	STMs[cpuid]->ICR.B.CMP0EN = 1;

}
/*-----------------------------------------------------------*/

/*****************************************************************/
static void prvSetupERUInterrupt(void)
{
	unsigned short cpuid = CPU_ID;

	if(cpuid == ERUInterruptCoreID)
	{
		SCU_FMR.B.FC0 = 1;	//Clear the interrupt flag
		InterruptInstall(SRC_ID_SCUERU0, prvERUISRHandler, 3, 0);	//Load the interrupt routine and priortiy
	}
}

/*****************************************************************/

static void prvSystemTickHandler( int iArg )
{
uint32_t ulSavedInterruptMask;
uint32_t *pxUpperCSA = NULL;
uint32_t xUpperCSA = 0UL;
extern volatile uint32_t *pxCurrentTCB;
int32_t lYieldRequired;
unsigned short cpuid = CPU_ID;

	/* Just to avoid compiler warnings about unused parameters. */
	( void ) iArg;

	/* Clear the interrupt source. */
	//STM_ISRR.reg = 1UL; //ATEN

	/* Reload the Compare Match register for X ticks into the future.

	If critical section or interrupt nesting budgets are exceeded, then
	it is possible that the calculated next compare match value is in the
	past.  If this occurs (unlikely), it is possible that the resulting
	time slippage will exceed a single tick period.  Any adverse effect of
	this is time bounded by the fact that only the first n bits of the 56 bit
	STM timer are being used for a compare match, so another compare match
	will occur after an overflow in just those n bits (not the entire 56 bits).
	As an example, if the peripheral clock is 75MHz, and the tick rate is 1KHz,
	a missed tick could result in the next tick interrupt occurring within a
	time that is 1.7 times the desired period.  The fact that this is greater
	than a single tick period is an effect of using a timer that cannot be
	automatically reset, in hardware, by the occurrence of a tick interrupt.
	Changing the tick source to a timer that has an automatic reset on compare
	match (such as a GPTA timer) will reduce the maximum possible additional
	period to exactly 1 times the desired period. */

	STMs[cpuid]->CMP[0].U = STMs[cpuid]->TIM0.U + ulCompareMatchValue; //ATEN
	STMs[cpuid]->ISCR.B.CMP0IRR = 1;
	//STM_CMP0.reg += ulCompareMatchValue;

	/* Kernel API calls require Critical Sections. */
	ulSavedInterruptMask = portSET_INTERRUPT_MASK_FROM_ISR();
	{
		/* Increment the Tick. */
		lYieldRequired = xTaskIncrementTick();
	}
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulSavedInterruptMask );

	if( lYieldRequired != pdFALSE )
	{
		/* Save the context of a task.
		The upper context is automatically saved when entering a trap or interrupt.
		Need to save the lower context as well and copy the PCXI CSA ID into
		pxCurrentTCB->pxTopOfStack. Only Lower Context CSA IDs may be saved to the
		TCB of a task.

		Call vTaskSwitchContext to select the next task, note that this changes the
		value of pxCurrentTCB so that it needs to be reloaded.

		Call vPortSetMPURegisterSetOne to change the MPU mapping for the task
		that has just been switched in.

		Load the context of the task.
		Need to restore the lower context by loading the CSA from
		pxCurrentTCB->pxTopOfStack into PCXI (effectively changing the call stack).
		In the Interrupt handler post-amble, RSLCX will restore the lower context
		of the task. RFE will restore the upper context of the task, jump to the
		return address and restore the previous state of interrupts being
		enabled/disabled. */
		_disable();
		_dsync();
		xUpperCSA = __MFCR( $PCXI );
		pxUpperCSA = portCSA_TO_ADDRESS( xUpperCSA );
		*pxCurrentTCB = pxUpperCSA[ 0 ];
		vTaskSwitchContext();
		pxUpperCSA[ 0 ] = *pxCurrentTCB;
		SRBs[cpuid]->B.TRIG0 = 0;       //ATEN
		//CPU_SRC0.bits.SETR = 0;
		_isync();
	}
}
/*-----------------------------------------------------------*/

static void prvERUISRHandler( int iArg )
{
	BaseType_t checkIfYieldRequired;
	/* Just to avoid compiler warnings about unused parameters. */
	( void ) iArg;

	SCU_FMR.B.FC0 = 1;	//Clear the interrupt flag

	checkIfYieldRequired = xTaskResumeFromISR(xTaskHandle0[E_FPGA_TASK]);	//Check the state of the FPGA task
	portYIELD_FROM_ISR(checkIfYieldRequired);	//Yield the FPGA task if it was suspended
}

/*
 * When a task is deleted, it is yielded permanently until the IDLE task
 * has an opportunity to reclaim the memory that that task was using.
 * Typically, the memory used by a task is the TCB and Stack but in the
 * TriCore this includes the CSAs that were consumed as part of the Call
 * Stack. These CSAs can only be returned to the Globally Free Pool when
 * they are not part of the current Call Stack, hence, delaying the
 * reclamation until the IDLE task is freeing the task's other resources.
 * This function uses the head of the linked list of CSAs (from when the
 * task yielded for the last time) and finds the tail (the very bottom of
 * the call stack) and inserts this list at the head of the Free list,
 * attaching the existing Free List to the tail of the reclaimed call stack.
 *
 * NOTE: the IDLE task needs processing time to complete this function
 * and in heavily loaded systems, the Free CSAs may be consumed faster
 * than they can be freed assuming that tasks are being spawned and
 * deleted frequently.
 */
void vPortReclaimCSA( uint32_t *pxTCB )
{
uint32_t pxHeadCSA, pxTailCSA, pxFreeCSA;
uint32_t *pulNextCSA;

	/* A pointer to the first CSA in the list of CSAs consumed by the task is
	stored in the first element of the tasks TCB structure (where the stack
	pointer would be on a traditional stack based architecture). */
	pxHeadCSA = ( *pxTCB ) & portCSA_FCX_MASK;

	/* Mask off everything in the CSA link field other than the address.  If
	the	address is NULL, then the CSA is not linking anywhere and there is
	nothing	to do. */
	pxTailCSA = pxHeadCSA;

	/* Convert the link value to contain just a raw address and store this
	in a local variable. */
	pulNextCSA = portCSA_TO_ADDRESS( pxTailCSA );

	/* Iterate over the CSAs that were consumed as part of the task.  The
	first field in the CSA is the pointer to then next CSA.  Mask off
	everything in the pointer to the next CSA, other than the link address.
	If this is NULL, then the CSA currently being pointed to is the last in
	the chain. */
	while( 0UL != ( pulNextCSA[ 0 ] & portCSA_FCX_MASK ) )
	{
		/* Clear all bits of the pointer to the next in the chain, other
		than the address bits themselves. */
		pulNextCSA[ 0 ] = pulNextCSA[ 0 ] & portCSA_FCX_MASK;

		/* Move the pointer to point to the next CSA in the list. */
		pxTailCSA = pulNextCSA[ 0 ];

		/* Update the local pointer to the CSA. */
		pulNextCSA = portCSA_TO_ADDRESS( pxTailCSA );
	}

	_disable();
	{
		/* Look up the current free CSA head. */
		_dsync();
		pxFreeCSA = __MFCR( $FCX );

		/* Join the current Free onto the Tail of what is being reclaimed. */
		portCSA_TO_ADDRESS( pxTailCSA )[ 0 ] = pxFreeCSA;

		/* Move the head of the reclaimed into the Free. */
		_dsync();
		_mtcr( $FCX, pxHeadCSA );
		_isync();
	}
	_enable();
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Nothing to do. Unlikely to want to end. */
}
/*-----------------------------------------------------------*/

void vTrapSysCallYield( int iTrapIdentification )
{
uint32_t *pxUpperCSA = NULL;
uint32_t xUpperCSA = 0UL;

extern volatile uint32_t *pxCurrentTCB;

	switch( iTrapIdentification )
	{
		case portSYSCALL_TASK_YIELD:
			/* Save the context of a task.
			The upper context is automatically saved when entering a trap or interrupt.
			Need to save the lower context as well and copy the PCXI CSA ID into
			pxCurrentTCB->pxTopOfStack. Only Lower Context CSA IDs may be saved to the
			TCB of a task.

			Call vTaskSwitchContext to select the next task, note that this changes the
			value of pxCurrentTCB so that it needs to be reloaded.

			Call vPortSetMPURegisterSetOne to change the MPU mapping for the task
			that has just been switched in.

			Load the context of the task.
			Need to restore the lower context by loading the CSA from
			pxCurrentTCB->pxTopOfStack into PCXI (effectively changing the call stack).
			In the Interrupt handler post-amble, RSLCX will restore the lower context
			of the task. RFE will restore the upper context of the task, jump to the
			return address and restore the previous state of interrupts being
			enabled/disabled. */
			_disable();
			_dsync();
			xUpperCSA = __MFCR( $PCXI );
			pxUpperCSA = portCSA_TO_ADDRESS( xUpperCSA );
			*pxCurrentTCB = pxUpperCSA[ 0 ];
			vTaskSwitchContext();
			pxUpperCSA[ 0 ] = *pxCurrentTCB;
			SRBs[CPU_ID]->B.TRIG0 = 0; //ATEN
			// CPU_SRC0.bits.SETR = 0;
			_isync();
			break;

		default:
			/* Unimplemented trap called. */
			configASSERT( ( ( volatile void * ) NULL ) );
			break;
	}
}
/*-----------------------------------------------------------*/

static void prvInterruptYield( int iId )
{
uint32_t *pxUpperCSA = NULL;
uint32_t xUpperCSA = 0UL;
extern volatile uint32_t *pxCurrentTCB;

	/* Just to remove compiler warnings. */
	( void ) iId;

	/* Save the context of a task.
	The upper context is automatically saved when entering a trap or interrupt.
	Need to save the lower context as well and copy the PCXI CSA ID into
	pxCurrentTCB->pxTopOfStack. Only Lower Context CSA IDs may be saved to the
	TCB of a task.

	Call vTaskSwitchContext to select the next task, note that this changes the
	value of pxCurrentTCB so that it needs to be reloaded.

	Call vPortSetMPURegisterSetOne to change the MPU mapping for the task
	that has just been switched in.

	Load the context of the task.
	Need to restore the lower context by loading the CSA from
	pxCurrentTCB->pxTopOfStack into PCXI (effectively changing the call stack).
	In the Interrupt handler post-amble, RSLCX will restore the lower context
	of the task. RFE will restore the upper context of the task, jump to the
	return address and restore the previous state of interrupts being
	enabled/disabled. */
	_disable();
	_dsync();
	xUpperCSA = __MFCR( $PCXI );
	pxUpperCSA = portCSA_TO_ADDRESS( xUpperCSA );
	*pxCurrentTCB = pxUpperCSA[ 0 ];
	vTaskSwitchContext();
	pxUpperCSA[ 0 ] = *pxCurrentTCB;
	SRBs[CPU_ID]->B.TRIG0 = 0;      //ATEN
	//CPU_SRC0.bits.SETR = 0;
	_isync();
}
/*-----------------------------------------------------------*/

uint32_t uxPortSetInterruptMaskFromISR( void )
{
uint32_t uxReturn = 0UL;

	_disable();
	uxReturn = __MFCR( $ICR );
	_mtcr( $ICR, ( ( uxReturn & ~portCCPN_MASK ) | configMAX_SYSCALL_INTERRUPT_PRIORITY ) );
	_isync();
	_enable();

	/* Return just the interrupt mask bits. */
	return ( uxReturn & portCCPN_MASK );
}
/*-----------------------------------------------------------*/


