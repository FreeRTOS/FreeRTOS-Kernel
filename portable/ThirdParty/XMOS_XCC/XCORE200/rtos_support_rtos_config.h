
/* 
 * Copyright (c) 2020, XMOS Ltd, All rights reserved
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#ifndef RTOS_SUPPORT_RTOS_CONFIG_H_
#define RTOS_SUPPORT_RTOS_CONFIG_H_

/**
 * Lets the application know that the RTOS in use is FreeRTOS.
 */
#define RTOS_FREERTOS 1

/**
 * The number of words to extend the stack by when entering an ISR.
 *
 * When entering an ISR we need to grow the stack by one more word than
 * we actually need to save the thread context. This is because there are
 * some functions, written in assembly *cough* memcpy() *cough*, that think
 * it is OK to store words at SP[0]. Therefore the ISR must leave SP[0] alone
 * even though it is normally not necessary to do so.
 */
#define RTOS_SUPPORT_INTERRUPT_STACK_GROWTH ( 19 + 1 )

/**
 * The word offset into the stack where R1 is to be stored after it
 * is extended when saving a thread's context.
 */
#define RTOS_SUPPORT_INTERRUPT_R1_STACK_OFFSET 9

/**
 * The word offset into the stack where R11 is to be stored after it
 * is extended when saving a thread's context.
 */
#define RTOS_SUPPORT_INTERRUPT_R11_STACK_OFFSET 19

/**
 * The RTOS provided handler that should run when a
 * core receives an intercore interrupt request.
 */
#define RTOS_INTERCORE_INTERRUPT_ISR()

/**
 * The number of hardware locks that the RTOS
 * requires. For a single core RTOS this could be
 * zero. Locks are recursive.
 *
 * Note that the IRQ routines require a lock and
 * will share the first one with the RTOS.
 */
#define RTOS_LOCK_COUNT 0

/**
 * Remaps all calls to debug_printf() to rtos_printf().
 * When this is on, files should not include both rtos_support.h
 * and debug_print.h.
 */
#define RTOS_DEBUG_PRINTF_REMAP 1


#ifdef configENABLE_DEBUG_PRINTF
	#if configENABLE_DEBUG_PRINTF

		/* ensure that debug_printf is enabled */
		#ifdef DEBUG_PRINT_ENABLE
			#undef DEBUG_PRINT_ENABLE
		#endif
		#define DEBUG_PRINT_ENABLE 1

	#else /* configENABLE_DEBUG_PRINTF */

		/* ensure that debug_printf is disabled */
		#ifdef DEBUG_UNIT
			#undef DEBUG_UNIT
		#endif
		#ifdef DEBUG_PRINT_ENABLE
			#undef DEBUG_PRINT_ENABLE
		#endif

		#define DEBUG_PRINT_ENABLE 0

	#endif /* configENABLE_DEBUG_PRINTF */
#endif

#endif /* RTOS_SUPPORT_RTOS_CONFIG_H_ */

