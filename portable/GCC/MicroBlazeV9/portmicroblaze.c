/*
 * FreeRTOS Kernel V10.4.2
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Copyright (C) 2012 - 2020 Xilinx, Inc. All rights reserved.
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Xilinx includes. */
#include "xil_printf.h"
#include "xparameters.h"

#if defined( XPAR_XTMRCTR_NUM_INSTANCES )
	#if( XPAR_XTMRCTR_NUM_INSTANCES > 0 )
		#include "xtmrctr.h"
		/* The timer is used to generate the RTOS tick interrupt. */
		static XTmrCtr xTickTimerInstance;
	#endif
#elif defined (XPAR_XTTCPS_NUM_INSTANCES)
	#if(XPAR_XTTCPS_NUM_INSTANCES  > 0)
		#include "xttcps.h"
		/* The timer is used to generate the RTOS tick interrupt. */
        static XTtcPs xTickTimerInstance;
	#endif
#endif


/*
 * Some FreeRTOSConfig.h settings require the application writer to provide the
 * implementation of a callback function that has a specific name, and a linker
 * error will result if the application does not provide the required function.
 * To avoid the risk of a configuration file setting resulting in a linker error
 * this file provides default implementations of each callback that might be
 * required.  The default implementations are declared as weak symbols to allow
 * the application writer to override the default implementation by providing
 * their own implementation in the application itself.
 */
void vApplicationAssert( const char *pcFileName, uint32_t ulLine ) __attribute__((weak));
void vApplicationTickHook( void ) __attribute__((weak));
void vApplicationIdleHook( void ) __attribute__((weak));
void vApplicationMallocFailedHook( void ) __attribute((weak));
void vApplicationStackOverflowHook( TaskHandle_t xTask, char *pcTaskName ) __attribute__((weak));
void vApplicationSetupTimerInterrupt( void ) __attribute__((weak));
void vApplicationClearTimerInterrupt( void ) __attribute__((weak));

/*-----------------------------------------------------------*/


/* This version of vApplicationAssert() is declared as a weak symbol to allow it
to be overridden by a version implemented within the application that is using
this BSP. */
void vApplicationAssert( const char *pcFileName, uint32_t ulLine )
{
volatile uint32_t ul = 0;
volatile const char *pcLocalFileName = pcFileName; /* To prevent pcFileName being optimized away. */
volatile uint32_t ulLocalLine = ulLine; /* To prevent ulLine being optimized away. */

	/* Prevent compile warnings about the following two variables being set but
	not referenced.  They are intended for viewing in the debugger. */
	( void ) pcLocalFileName;
	( void ) ulLocalLine;

	xil_printf( "Assert failed in file %s, line %lu\r\n", pcLocalFileName, ulLocalLine );

	/* If this function is entered then a call to configASSERT() failed in the
	FreeRTOS code because of a fatal error.  The pcFileName and ulLine
	parameters hold the file name and line number in that file of the assert
	that failed.  Additionally, if using the debugger, the function call stack
	can be viewed to find which line failed its configASSERT() test.  Finally,
	the debugger can be used to set ul to a non-zero value, then step out of
	this function to find where the assert function was entered. */
	taskENTER_CRITICAL();
	{
		while( ul == 0 )
		{
			__asm volatile( "NOP" );
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

/* This default tick hook does nothing and is declared as a weak symbol to allow
the application writer to override this default by providing their own
implementation in the application code. */
void vApplicationTickHook( void )
{
}
/*-----------------------------------------------------------*/

/* This default idle hook does nothing and is declared as a weak symbol to allow
the application writer to override this default by providing their own
implementation in the application code. */
void vApplicationIdleHook( void )
{
}
/*-----------------------------------------------------------*/

/* This default malloc failed hook does nothing and is declared as a weak symbol
to allow the application writer to override this default by providing their own
implementation in the application code. */
void vApplicationMallocFailedHook( void )
{
	xil_printf( "vApplicationMallocFailedHook() called\n" );
}
/*-----------------------------------------------------------*/

/* This default stack overflow hook will stop the application for executing.  It
is declared as a weak symbol to allow the application writer to override this
default by providing their own implementation in the application code. */
void vApplicationStackOverflowHook( TaskHandle_t xTask, char *pcTaskName )
{
/* Attempt to prevent the handle and name of the task that overflowed its stack
from being optimised away because they are not used. */
volatile TaskHandle_t xOverflowingTaskHandle = xTask;
volatile char *pcOverflowingTaskName = pcTaskName;

	( void ) xOverflowingTaskHandle;
	( void ) pcOverflowingTaskName;

	xil_printf( "HALT: Task %s overflowed its stack.", pcOverflowingTaskName );
	portDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

#if defined( XPAR_XTMRCTR_NUM_INSTANCES )
	#if( XPAR_XTMRCTR_NUM_INSTANCES > 0 )
		/* This is a default implementation of what is otherwise an application defined
		callback function used to install the tick interrupt handler.  It is provided as
		an application callback because the kernel will run on lots of different
		MicroBlaze and FPGA configurations - not all of which will have the same timer
		peripherals defined or available.  vApplicationSetupTimerInterrupt() is declared
		as a weak symbol, allowing the application writer to provide their own
		implementation, if this default implementation is not suitable. */
		void vApplicationSetupTimerInterrupt( void )
		{
		portBASE_TYPE xStatus;
		const unsigned char ucTickTimerCounterNumber = ( unsigned char ) 0U;
		const unsigned char ucRunTimeStatsCounterNumber = ( unsigned char ) 1U;
		const unsigned long ulCounterValue = ( ( XPAR_TMRCTR_0_CLOCK_FREQ_HZ / configTICK_RATE_HZ ) - 1UL );
		extern void vPortTickISR( void *pvUnused );

			/* Initialise the timer/counter. */
			xStatus = XTmrCtr_Initialize( &xTickTimerInstance, XPAR_TMRCTR_0_DEVICE_ID );

			if( xStatus == XST_SUCCESS )
			{
				/* Install the tick interrupt handler as the timer ISR.
				*NOTE* The xPortInstallInterruptHandler() API function must be used for
				this purpose. */
				xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_TMRCTR_0_VEC_ID, vPortTickISR, NULL );
			}

			if( xStatus == pdPASS )
			{
				/* Enable the timer interrupt in the interrupt controller.
				*NOTE* The vPortEnableInterrupt() API function must be used for this
				purpose. */
				vPortEnableInterrupt( XPAR_INTC_0_TMRCTR_0_VEC_ID );

				/* Configure the timer interrupt handler.  This installs the handler
				directly, rather than through the Xilinx driver.  This is done for
				efficiency. */
				XTmrCtr_SetHandler( &xTickTimerInstance, ( void * ) vPortTickISR, NULL );

				/* Set the correct period for the timer. */
				XTmrCtr_SetResetValue( &xTickTimerInstance, ucTickTimerCounterNumber, ulCounterValue );

				/* Enable the interrupts.  Auto-reload mode is used to generate a
				periodic tick.  Note that interrupts are disabled when this function is
				called, so interrupts will not start to be processed until the first
				task has started to run. */
				XTmrCtr_SetOptions( &xTickTimerInstance, ucTickTimerCounterNumber, ( XTC_INT_MODE_OPTION | XTC_AUTO_RELOAD_OPTION | XTC_DOWN_COUNT_OPTION ) );

				/* Start the timer. */
				XTmrCtr_Start( &xTickTimerInstance, ucTickTimerCounterNumber );




				/* The second timer is used as the time base for the run time stats.
				Auto-reload mode is used to ensure the timer does not stop. */
				XTmrCtr_SetOptions( &xTickTimerInstance, ucRunTimeStatsCounterNumber, XTC_AUTO_RELOAD_OPTION );

				/* Start the timer. */
				XTmrCtr_Start( &xTickTimerInstance, ucRunTimeStatsCounterNumber );
			}

			/* Sanity check that the function executed as expected. */
			configASSERT( ( xStatus == pdPASS ) );
		}
	#endif /* XPAR_XTMRCTR_NUM_INSTANCES > 0 */
#elif defined (XPAR_XTTCPS_NUM_INSTANCES)
	#if(XPAR_XTTCPS_NUM_INSTANCES  > 0)
		void vApplicationSetupTimerInterrupt( void )
		{
		portBASE_TYPE xStatus;
		XInterval usInterval;
		uint8_t ucPrescaler;
		extern void vPortTickISR( void *pvUnused );
		XTtcPs_Config *pxTimerConfiguration;

			/* Initialise the timer/counter. */
			pxTimerConfiguration = XTtcPs_LookupConfig( configTIMER_ID );
			xStatus = XTtcPs_CfgInitialize( &xTickTimerInstance, pxTimerConfiguration, pxTimerConfiguration->BaseAddress );

			if( xStatus != XST_SUCCESS )
	        {
				XTtcPs_Stop(&xTickTimerInstance);
		        xStatus = XTtcPs_CfgInitialize( &xTickTimerInstance, pxTimerConfiguration, pxTimerConfiguration->BaseAddress );
				if( xStatus != XST_SUCCESS )
				{
					xil_printf( "In %s: Timer Cfg initialization failed...\r\n", __func__ );
					return;
				}
			}

			if( xStatus == XST_SUCCESS )
			{
				/* Install the tick interrupt handler as the timer ISR.
				*NOTE* The xPortInstallInterruptHandler() API function must be used for
				this purpose. */
				xStatus = xPortInstallInterruptHandler( configTIMER_INTERRUPT_ID, vPortTickISR, NULL );
			}

			if( xStatus == pdPASS )
			{
				XTtcPs_SetOptions( &xTickTimerInstance, XTTCPS_OPTION_INTERVAL_MODE | XTTCPS_OPTION_WAVE_DISABLE );
	/*
	 * The Xilinx implementation of generating run time task stats uses the same timer used for generating
	 * FreeRTOS ticks. In case user decides to generate run time stats the timer time out interval is changed
	 * as "configured tick rate * 10". The multiplying factor of 10 is hard coded for Xilinx FreeRTOS ports.
	 */
#if (configGENERATE_RUN_TIME_STATS == 1)
				XTtcPs_CalcIntervalFromFreq( &xTickTimerInstance, configTICK_RATE_HZ*10, &usInterval, &ucPrescaler );
#else
				XTtcPs_CalcIntervalFromFreq( &xTickTimerInstance, configTICK_RATE_HZ, &usInterval, &ucPrescaler );
#endif
				XTtcPs_SetInterval( &xTickTimerInstance, usInterval );
				XTtcPs_SetPrescaler( &xTickTimerInstance, ucPrescaler );
				/* Enable the timer interrupt in the interrupt controller.
				*NOTE* The vPortEnableInterrupt() API function must be used for this
				purpose. */
				vPortEnableInterrupt( configTIMER_INTERRUPT_ID );
				/* Enable the interrupt for timer. */
				XTtcPs_EnableInterrupts( &xTickTimerInstance, XTTCPS_IXR_INTERVAL_MASK );

				/* Start the timer */
				XTtcPs_Start( &xTickTimerInstance );
			}

			/* Sanity check that the function executed as expected. */
			configASSERT( ( xStatus == pdPASS ) );
		}
	#endif	/* XPAR_XTTCPS_NUM_INSTANCES */
#endif /* XPAR_XTMRCTR_NUM_INSTANCES */
/*-----------------------------------------------------------*/

#if defined( XPAR_XTMRCTR_NUM_INSTANCES )
	#if( XPAR_XTMRCTR_NUM_INSTANCES > 0 )
		/* This is a default implementation of what is otherwise an application defined
		callback function used to clear whichever timer interrupt is used to generate
		the tick interrupt.  It is provided as an application callback because the
		kernel will run on lots of different MicroBlaze and FPGA configurations - not
		all of which will have the same timer peripherals defined or available.
		vApplicationSetupTimerInterrupt() is declared as a weak symbol, allowing the
		application writer to provide their own implementation, if this default
		implementation is not suitable. */
		void vApplicationClearTimerInterrupt( void )
		{
		unsigned long ulCSR;

			/* Clear the timer interrupt */
			ulCSR = XTmrCtr_GetControlStatusReg( XPAR_TMRCTR_0_BASEADDR, 0 );
			XTmrCtr_SetControlStatusReg( XPAR_TMRCTR_0_BASEADDR, 0, ulCSR );
		}
	#endif /* XPAR_XTMRCTR_NUM_INSTANCES > 0 */
#elif defined (XPAR_XTTCPS_NUM_INSTANCES)
	#if(XPAR_XTTCPS_NUM_INSTANCES  > 0)

		void vApplicationClearTimerInterrupt( void )
		{
			uint32_t ulStatusEvent;

			ulStatusEvent = XTtcPs_GetInterruptStatus( &xTickTimerInstance );
			XTtcPs_ClearInterruptStatus( &xTickTimerInstance, ulStatusEvent );
		}
	#endif
#endif /* XPAR_XTMRCTR_NUM_INSTANCES */
