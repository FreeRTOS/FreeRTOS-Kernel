/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution and was contributed
    to the project by Technolution B.V. (www.technolution.nl,
    freertos-riscv@technolution.eu) under the terms of the FreeRTOS
    contributors license.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry''s de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/


#if __riscv_xlen == 64
# define STORE    sd
# define LOAD     ld
# define REGBYTES 8
#else
# define STORE    sw
# define LOAD     lw
# define REGBYTES 4
#endif

/* Enable interrupts when returning from the handler */
#define MSTATUS_PRV1 0x1880

.global xPortStartFirstTask
.global portSAVE_CONTEXT
.global portRESTORE_CONTEXT
.global TIMER_CMP_INT
.global vPortYield
.global vTaskIncrementTick
.global xExitStack

#define portCONTEXT_SIZE ( 30 * REGBYTES )

/*-----------------------------------------------------------*/
.align 8
.func
xPortStartFirstTask:

	/* If there is a clint then interrupts can branch directly to the FreeRTOS
	trap handler.  Otherwise the interrupt controller will need to be configured
	outside of this file. */
	la t0, freertos_risc_v_trap_handler
	csrw mtvec, t0

	LOAD  sp, pxCurrentTCB			/* Load pxCurrentTCB. */
	LOAD  sp, 0( sp )				 	/* Read sp from first TCB member. */

	LOAD  x1, 0( sp ) /* Note for starting the scheduler the exception return address is used as the function return address. */

	// portasmRESTORE_ADDITIONAL_REGISTERS	/* Defined in freertos_risc_v_chip_specific_extensions.h to restore any registers unique to the RISC-V implementation. */

	LOAD  t0, 29 * REGBYTES( sp )	/* mstatus */
	addi t0, t0, 0x08						/* Set MIE bit so the first task starts with interrupts enabled - required as returns with ret not eret. */
	csrrw  x0, mstatus, t0					/* Interrupts enabled from here! */

	LOAD  x5, 2 * REGBYTES( sp )		/* t0 */
	LOAD  x6, 3 * REGBYTES( sp )		/* t1 */
	LOAD  x7, 4 * REGBYTES( sp )		/* t2 */
	LOAD  x8, 5 * REGBYTES( sp )		/* s0/fp */
	LOAD  x9, 6 * REGBYTES( sp )		/* s1 */
	LOAD  x10, 7 * REGBYTES( sp )	/* a0 */
	LOAD  x11, 8 * REGBYTES( sp )	/* a1 */
	LOAD  x12, 9 * REGBYTES( sp )	/* a2 */
	LOAD  x13, 10 * REGBYTES( sp )	/* a3 */
	LOAD  x14, 11 * REGBYTES( sp )	/* a4 */
	LOAD  x15, 12 * REGBYTES( sp )	/* a5 */
	LOAD  x16, 13 * REGBYTES( sp )	/* a6 */
	LOAD  x17, 14 * REGBYTES( sp )	/* a7 */
	LOAD  x18, 15 * REGBYTES( sp )	/* s2 */
	LOAD  x19, 16 * REGBYTES( sp )	/* s3 */
	LOAD  x20, 17 * REGBYTES( sp )	/* s4 */
	LOAD  x21, 18 * REGBYTES( sp )	/* s5 */
	LOAD  x22, 19 * REGBYTES( sp )	/* s6 */
	LOAD  x23, 20 * REGBYTES( sp )	/* s7 */
	LOAD  x24, 21 * REGBYTES( sp )	/* s8 */
	LOAD  x25, 22 * REGBYTES( sp )	/* s9 */
	LOAD  x26, 23 * REGBYTES( sp )	/* s10 */
	LOAD  x27, 24 * REGBYTES( sp )	/* s11 */
	LOAD  x28, 25 * REGBYTES( sp )	/* t3 */
	LOAD  x29, 26 * REGBYTES( sp )	/* t4 */
	LOAD  x30, 27 * REGBYTES( sp )	/* t5 */
	LOAD  x31, 28 * REGBYTES( sp )	/* t6 */
	addi	sp, sp, portCONTEXT_SIZE
	ret
	.endfunc
/*-----------------------------------------------------------*/

.align 8
.func
freertos_risc_v_trap_handler:
	addi sp, sp, -portCONTEXT_SIZE
	STORE x1, 1 * REGBYTES( sp )
	STORE x5, 2 * REGBYTES( sp )
	STORE x6, 3 * REGBYTES( sp )
	STORE x7, 4 * REGBYTES( sp )
	STORE x8, 5 * REGBYTES( sp )
	STORE x9, 6 * REGBYTES( sp )
	STORE x10, 7 * REGBYTES( sp )
	STORE x11, 8 * REGBYTES( sp )
	STORE x12, 9 * REGBYTES( sp )
	STORE x13, 10 * REGBYTES( sp )
	STORE x14, 11 * REGBYTES( sp )
	STORE x15, 12 * REGBYTES( sp )
	STORE x16, 13 * REGBYTES( sp )
	STORE x17, 14 * REGBYTES( sp )
	STORE x18, 15 * REGBYTES( sp )
	STORE x19, 16 * REGBYTES( sp )
	STORE x20, 17 * REGBYTES( sp )
	STORE x21, 18 * REGBYTES( sp )
	STORE x22, 19 * REGBYTES( sp )
	STORE x23, 20 * REGBYTES( sp )
	STORE x24, 21 * REGBYTES( sp )
	STORE x25, 22 * REGBYTES( sp )
	STORE x26, 23 * REGBYTES( sp )
	STORE x27, 24 * REGBYTES( sp )
	STORE x28, 25 * REGBYTES( sp )
	STORE x29, 26 * REGBYTES( sp )
	STORE x30, 27 * REGBYTES( sp )
	STORE x31, 28 * REGBYTES( sp )

	csrr t0, mstatus					/* Required for MPIE bit. */
	STORE t0, 29 * REGBYTES( sp )

	// portasmSAVE_ADDITIONAL_REGISTERS	/* Defined in freertos_risc_v_chip_specific_extensions.h to save any registers unique to the RISC-V implementation. */

	LOAD  t0, pxCurrentTCB			/* Load pxCurrentTCB. */
	STORE  sp, 0( t0 )				/* Write sp to first TCB member. */

	csrr a0, mcause
	csrr a1, mepc


/* Macro for saving task context */
.macro portSAVE_CONTEXT
	.global	pxCurrentTCB
	/* make room in stack */
	addi	sp, sp, -REGBYTES * 32

	/* Save Context */
	STORE	x1, 0x0(sp)
	STORE	x2, 1 * REGBYTES(sp)
	STORE	x3, 2 * REGBYTES(sp)
	STORE	x4, 3 * REGBYTES(sp)
	STORE	x5, 4 * REGBYTES(sp)
	STORE	x6, 5 * REGBYTES(sp)
	STORE	x7, 6 * REGBYTES(sp)
	STORE	x8, 7 * REGBYTES(sp)
	STORE	x9, 8 * REGBYTES(sp)
	STORE	x10, 9 * REGBYTES(sp)
	STORE	x11, 10 * REGBYTES(sp)
	STORE	x12, 11 * REGBYTES(sp)
	STORE	x13, 12 * REGBYTES(sp)
	STORE	x14, 13 * REGBYTES(sp)
	STORE	x15, 14 * REGBYTES(sp)
	STORE	x16, 15 * REGBYTES(sp)
	STORE	x17, 16 * REGBYTES(sp)
	STORE	x18, 17 * REGBYTES(sp)
	STORE	x19, 18 * REGBYTES(sp)
	STORE	x20, 19 * REGBYTES(sp)
	STORE	x21, 20 * REGBYTES(sp)
	STORE	x22, 21 * REGBYTES(sp)
	STORE	x23, 22 * REGBYTES(sp)
	STORE	x24, 23 * REGBYTES(sp)
	STORE	x25, 24 * REGBYTES(sp)
	STORE	x26, 25 * REGBYTES(sp)
	STORE	x27, 26 * REGBYTES(sp)
	STORE	x28, 27 * REGBYTES(sp)
	STORE	x29, 28 * REGBYTES(sp)
	STORE	x30, 29 * REGBYTES(sp)
	STORE	x31, 30 * REGBYTES(sp)

	/* Store current stackpointer in task control block (TCB) */
	LOAD	t0, pxCurrentTCB	//pointer
	STORE	sp, 0x0(t0)
	.endm

/* Saves current error program counter (EPC) as task program counter */
.macro portSAVE_EPC
  	csrr	t0, mepc
	STORE	t0, 31 * REGBYTES(sp)
	.endm

/* Saves current return adress (RA) as task program counter */
.macro portSAVE_RA
	STORE	ra, 31 * REGBYTES(sp)
	.endm

/* Macro for restoring task context */
.macro portRESTORE_CONTEXT

	.global	pxCurrentTCB
	/* Load stack pointer from the current TCB */
	LOAD	sp, pxCurrentTCB
	LOAD	sp, 0x0(sp)

	/* Load task program counter */
	LOAD	t0, 31 * REGBYTES(sp)
  	csrw	mepc, t0

	/* Run in machine mode */
  	li 		t0, MSTATUS_PRV1
  	csrs	mstatus, t0

	/* Restore registers,
	   Skip global pointer because that does not change */
	LOAD	x1, 0x0(sp)
	LOAD	x4, 3 * REGBYTES(sp)
	LOAD	x5, 4 * REGBYTES(sp)
	LOAD	x6, 5 * REGBYTES(sp)
	LOAD	x7, 6 * REGBYTES(sp)
	LOAD	x8, 7 * REGBYTES(sp)
	LOAD	x9, 8 * REGBYTES(sp)
	LOAD	x10, 9 * REGBYTES(sp)
	LOAD	x11, 10 * REGBYTES(sp)
	LOAD	x12, 11 * REGBYTES(sp)
	LOAD	x13, 12 * REGBYTES(sp)
	LOAD	x14, 13 * REGBYTES(sp)
	LOAD	x15, 14 * REGBYTES(sp)
	LOAD	x16, 15 * REGBYTES(sp)
	LOAD	x17, 16 * REGBYTES(sp)
	LOAD	x18, 17 * REGBYTES(sp)
	LOAD	x19, 18 * REGBYTES(sp)
	LOAD	x20, 19 * REGBYTES(sp)
	LOAD	x21, 20 * REGBYTES(sp)
	LOAD	x22, 21 * REGBYTES(sp)
	LOAD	x23, 22 * REGBYTES(sp)
	LOAD	x24, 23 * REGBYTES(sp)
	LOAD	x25, 24 * REGBYTES(sp)
	LOAD	x26, 25 * REGBYTES(sp)
	LOAD	x27, 26 * REGBYTES(sp)
	LOAD	x28, 27 * REGBYTES(sp)
	LOAD	x29, 28 * REGBYTES(sp)
	LOAD	x30, 29 * REGBYTES(sp)
	LOAD	x31, 30 * REGBYTES(sp)

	addi	sp, sp, REGBYTES * 32
	mret
	.endm

/* Macro for restoring task context */
TIMER_CMP_INT:
	portSAVE_CONTEXT
	portSAVE_EPC
	jal	vPortSysTickHandler
	portRESTORE_CONTEXT


vPortYield:
	/*
	*  This routine can be called from outside of interrupt handler. This means
	*  interrupts may be enabled at this point. This is probably okay for registers and
	*  stack. However, "mepc" will be overwritten by the interrupt handler if a timer
	*  interrupt happens during the yield. To avoid this, prevent interrupts before starting.
	*  The write to mstatus in the restore context routine will enable interrupts after the
	*  mret. A more fine-grain lock may be possible.
	*/
	csrci mstatus, 8

	portSAVE_CONTEXT
	portSAVE_RA
	jal	vTaskSwitchContext
	portRESTORE_CONTEXT
