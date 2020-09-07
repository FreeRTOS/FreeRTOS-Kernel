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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 * 1 tab == 4 spaces!
 */

/*
 * The FreeRTOS kernel's RISC-V port is split between the the code that is
 * common across all currently supported RISC-V chips (implementations of the
 * RISC-V ISA), and code which tailors the port to a specific RISC-V chip:
 *
 * + The code that is common to all RISC-V chips is implemented in
 *   FreeRTOS\Source\portable\GCC\RISC-V-RV32\portASM.S.  There is only one
 *   portASM.S file because the same file is used no matter which RISC-V chip is
 *   in use.
 *
 * + The code that tailors the kernel's RISC-V port to a specific RISC-V
 *   chip is implemented in freertos_risc_v_chip_specific_extensions.h.  There
 *   is one freertos_risc_v_chip_specific_extensions.h that can be used with any
 *   RISC-V chip that both includes a standard CLINT and does not add to the
 *   base set of RISC-V registers.  There are additional
 *   freertos_risc_v_chip_specific_extensions.h files for RISC-V implementations
 *   that do not include a standard CLINT or do add to the base set of RISC-V
 *   registers.
 *
 * CARE MUST BE TAKEN TO INCLDUE THE CORRECT
 * freertos_risc_v_chip_specific_extensions.h HEADER FILE FOR THE CHIP
 * IN USE.  To include the correct freertos_risc_v_chip_specific_extensions.h
 * header file ensure the path to the correct header file is in the assembler's
 * include path.
 *
 * This freertos_risc_v_chip_specific_extensions.h is for use on RISC-V chips
 * that include a standard CLINT and do not add to the base set of RISC-V
 * registers.
 *
 */

/* ------------------------------------------------------------------
 * This file is part of the FreeRTOS distribution and was contributed
 * to the project by SiFive
 * ------------------------------------------------------------------
 */

#if( __riscv_xlen == 64 )
	#define store_x sd
	#define load_x ld
#elif( __riscv_xlen == 32 )
	#define store_x sw
	#define load_x lw
#else
	#error Assembler did not define __riscv_xlen
#endif /* ( __riscv_xlen == xx ) */

/* Nb registers to save */
#ifdef __riscv_32e
#define portasmNB_REGS_SAVED			(16)
#else
#define portasmNB_REGS_SAVED			(32)
#endif /* __riscv_32e */

#define portWORD_SIZE					(__riscv_xlen / 8)

/* Number of FPU register */
#ifdef __riscv_fdiv
	#define MSTATUS_FS           0x00006000 /* Floating-point Status */
	#define MSTATUS_FS_OFF       0x00000000
	#define MSTATUS_FS_INITIAL   0x00002000
	#define MSTATUS_FS_CLEAN     0x00004000
	#define MSTATUS_FS_DIRTY     0x00006000

	#if __riscv_flen == 32
		#define store_fpu fsw
		#define load_fpu flw
	#endif /* __riscv_flen == 32 */

	#if __riscv_flen == 64
		#define store_fpu fsd
		#define load_fpu fld
	#endif /* __riscv_flen == 64 */

	#define portasmFPU_CONTEXT_SIZE			(32)
	#define portFPUWORD_SIZE 				(__riscv_flen / 8)
#else
	#define portasmFPU_CONTEXT_SIZE			(0)
	#define portFPUWORD_SIZE				(0)
#endif /* __riscv_fdiv */

#include "freertos_risc_v_chip_specific_extensions.h"

/* Check the freertos_risc_v_chip_specific_extensions.h and/or command line
definitions. */
#if defined( portasmHAS_CLINT ) && defined( portasmHAS_MTIME )
	#error The portasmHAS_CLINT constant has been deprecated.  Please replace it with portasmHAS_MTIME.  portasmHAS_CLINT and portasmHAS_MTIME cannot both be defined at once.  See https://www.FreeRTOS.org/Using-FreeRTOS-on-RISC-V.html
#endif

#ifdef portasmHAS_CLINT
	#warning The portasmHAS_CLINT constant has been deprecated.  Please replace it with portasmHAS_MTIME and portasmHAS_SIFIVE_CLINT.  For now portasmHAS_MTIME and portasmHAS_SIFIVE_CLINT are derived from portasmHAS_CLINT.  See https://www.FreeRTOS.org/Using-FreeRTOS-on-RISC-V.html
	#define portasmHAS_MTIME portasmHAS_CLINT
	#define portasmHAS_SIFIVE_CLINT portasmHAS_CLINT
#endif

#ifndef portasmHAS_MTIME
	#error freertos_risc_v_chip_specific_extensions.h must define portasmHAS_MTIME to either 1 (MTIME clock present) or 0 (MTIME clock not present).  See https://www.FreeRTOS.org/Using-FreeRTOS-on-RISC-V.html
#endif

#ifndef portHANDLE_INTERRUPT
	#error portHANDLE_INTERRUPT must be defined to the function to be called to handle external/peripheral interrupts.
#endif

#ifndef portHANDLE_EXCEPTION
	#error portHANDLE_EXCEPTION must be defined to the function to be called to handle execptions.
 #endif

#ifndef portasmHAS_SIFIVE_CLINT
	#define portasmHAS_SIFIVE_CLINT 0
#endif

/*
 * To maintain RISCV ABI stack alignment requirements (16bytes)
 * this data structure must be a MULTIPLE of 16 bytes in size.
 * 32 Registers (for standard core) is 16byte aligned :)
 * We add space to save additional information so it must be multiple of 4.
 * mepc 33th register 
 * mstatus 34th register
 * ruf 35th register
 * ruf 36th register
 */

#define PORT_CONTEXT_mepcIDX		(portasmNB_REGS_SAVED)
#define PORT_CONTEXT_mstatusIDX		(portasmNB_REGS_SAVED + 1)

#define portasmLAST_BASE_REGS		(portasmNB_REGS_SAVED + 4)
#define PORT_CONTEXT_lastIDX		((portasmNB_REGS_SAVED) + portasmADDITIONAL_CONTEXT_SIZE)

/* used in assembler, as byte offsets from the start of the context */
#define PORT_CONTEXT_xIDX(X)		(X) /* index into "raw" for register x? */
#define PORT_CONTEXT_xOFFSET(X) 	(PORT_CONTEXT_xIDX(X)		* portWORD_SIZE)
#define PORT_CONTEXT_mepcOFFSET     (PORT_CONTEXT_mepcIDX		* portWORD_SIZE)
#define PORT_CONTEXT_mstatusOFFSET  (PORT_CONTEXT_mstatusIDX	* portWORD_SIZE)
#define PORT_CONTEXT_rufOFFSET   	(PORT_CONTEXT_rufIDX		* portWORD_SIZE)
#define PORT_CONTEXT_fpuOFFSET(X) 	((X) 						* portFPUWORD_SIZE)
/* total size of the structure usable in ASM. */

#define portasmREGISTER_CONTEXT_WORDSIZE		((portasmLAST_BASE_REGS) * (portWORD_SIZE))
#define portasmADDITIONAL_CONTEXT_WORDSIZE		((portasmADDITIONAL_CONTEXT_SIZE) * (portWORD_SIZE))
#define portasmFPU_CONTEXT_WORDSIZE				((portasmFPU_CONTEXT_SIZE) * (portFPUWORD_SIZE))

.global xPortStartFirstTask
.global freertos_risc_v_trap_handler
.global pxPortInitialiseStack
.extern pxCurrentTCB
.extern ulPortTrapHandler
.extern vTaskSwitchContext
.extern xTaskIncrementTick
.extern Timer_IRQHandler
.extern pullMachineTimerCompareRegister
.extern pullNextTime
.extern uxTimerIncrementsForOneTick /* size_t type so 32-bit on 32-bit core and 64-bits on 64-bit core. */
.extern xISRStackTop
.extern portHANDLE_INTERRUPT
.extern portHANDLE_EXCEPTION
/*-----------------------------------------------------------*/
 
#ifdef __riscv_fdiv
.macro portSAVE_FpuReg
	/* get FS field from mstatus */
	li t0, MSTATUS_FS
	csrr 	t1, mstatus
	and t0, t1, t0
	li t2, MSTATUS_FS_DIRTY
	bne t2, t0, 1f
	/* FS == dirty */
	/* Make room for the additional FPU registers. */
	addi sp, sp, -portasmFPU_CONTEXT_WORDSIZE
	store_fpu  f0,  PORT_CONTEXT_fpuOFFSET(0)(sp)		/* f0(ft0)		FP temporary register */
	store_fpu  f1,  PORT_CONTEXT_fpuOFFSET(1)(sp)		/* f1(ft1)		FP temporary register */
	store_fpu  f2,  PORT_CONTEXT_fpuOFFSET(2)(sp)		/* f2(ft2)		FP temporary register */
	store_fpu  f3,  PORT_CONTEXT_fpuOFFSET(3)(sp)		/* f3(ft3)		FP temporary register */
	store_fpu  f4,  PORT_CONTEXT_fpuOFFSET(4)(sp)		/* f4(ft4)		FP temporary register */
	store_fpu  f5,  PORT_CONTEXT_fpuOFFSET(5)(sp)		/* f5(ft5)		FP temporary register */
	store_fpu  f6,  PORT_CONTEXT_fpuOFFSET(6)(sp)		/* f6(ft6)		FP temporary register */
	store_fpu  f7,  PORT_CONTEXT_fpuOFFSET(7)(sp)		/* f7(ft7)		FP temporary register */

	store_fpu  f8,  PORT_CONTEXT_fpuOFFSET(8)(sp)		/* f8(fs0)		FP Saved register */
	store_fpu  f9,  PORT_CONTEXT_fpuOFFSET(9)(sp)		/* f9(fs0)		FP Saved register */

	store_fpu  f10,  PORT_CONTEXT_fpuOFFSET(10)(sp)	/* f10(fa0)		FP arguments/return values register */
	store_fpu  f11,  PORT_CONTEXT_fpuOFFSET(11)(sp)	/* f11(fa1)		FP arguments/return values register */

	store_fpu  f12,  PORT_CONTEXT_fpuOFFSET(12)(sp)	/* f12(fa2)		FP arguments register */
	store_fpu  f13,  PORT_CONTEXT_fpuOFFSET(13)(sp)	/* f13(fa3)		FP arguments register */
	store_fpu  f14,  PORT_CONTEXT_fpuOFFSET(14)(sp)	/* f14(fa4)		FP arguments register */
	store_fpu  f15,  PORT_CONTEXT_fpuOFFSET(15)(sp)	/* f15(fa5)		FP arguments register */
	store_fpu  f16,  PORT_CONTEXT_fpuOFFSET(16)(sp)	/* f16(fa6)		FP arguments register */
	store_fpu  f17,  PORT_CONTEXT_fpuOFFSET(17)(sp)	/* f17(fa7)		FP arguments register */

	store_fpu  f18,  PORT_CONTEXT_fpuOFFSET(18)(sp)	/* f18(fs2)		FP Saved register */
	store_fpu  f19,  PORT_CONTEXT_fpuOFFSET(19)(sp)	/* f19(fs3)		FP Saved register */
	store_fpu  f20,  PORT_CONTEXT_fpuOFFSET(20)(sp)	/* f20(fs4)		FP Saved register */
	store_fpu  f21,  PORT_CONTEXT_fpuOFFSET(21)(sp)	/* f21(fs5)		FP Saved register */
	store_fpu  f22,  PORT_CONTEXT_fpuOFFSET(22)(sp)	/* f22(fs6)		FP Saved register */
	store_fpu  f23,  PORT_CONTEXT_fpuOFFSET(23)(sp)	/* f23(fs7)		FP Saved register */
	store_fpu  f24,  PORT_CONTEXT_fpuOFFSET(24)(sp)	/* f24(fs8)		FP Saved register */
	store_fpu  f25,  PORT_CONTEXT_fpuOFFSET(25)(sp)	/* f25(fs9)		FP Saved register */
	store_fpu  f26,  PORT_CONTEXT_fpuOFFSET(26)(sp)	/* f26(fs10)	FP Saved register */
	store_fpu  f27,  PORT_CONTEXT_fpuOFFSET(27)(sp)	/* f27(fs11)	FP Saved register */

	store_fpu  f28,  PORT_CONTEXT_fpuOFFSET(28)(sp)	/* f28(ft8)		FP temporary register */
	store_fpu  f29,  PORT_CONTEXT_fpuOFFSET(29)(sp)	/* f29(ft9)		FP temporary register */
	store_fpu  f30,  PORT_CONTEXT_fpuOFFSET(30)(sp)	/* f30(ft10)	FP temporary register */
	store_fpu  f31,  PORT_CONTEXT_fpuOFFSET(31)(sp)	/* f31(ft11)	FP temporary register */

	/* must set FS to clean */
	csrc 	mstatus, t0
	li 	t1, MSTATUS_FS_CLEAN
	csrs	mstatus, t1
1:
	.endm
#else
.macro portSAVE_FpuReg
	/* No fpu registers to save, so this macro does nothing. */
	.endm
#endif /* __riscv_fdiv */
/*-----------------------------------------------------------*/

#ifdef __riscv_fdiv
.macro portRESTORE_FpuReg
	/* get FS field from mstatus */
	li t0, MSTATUS_FS
	csrr 	t1, mstatus
	and t0, t1, t0
	li t2, MSTATUS_FS_OFF
	beq t2, t0, 1f
	/* FS != off */
	csrs mstatus, t0
	/* Remove space added for additional fpu registers. */
	addi sp, sp, portasmFPU_CONTEXT_WORDSIZE
	load_fpu  f0,  PORT_CONTEXT_fpuOFFSET(0)(sp)		/* f0(ft0)		FP temporary register */
	load_fpu  f1,  PORT_CONTEXT_fpuOFFSET(1)(sp)		/* f1(ft1)		FP temporary register */
	load_fpu  f2,  PORT_CONTEXT_fpuOFFSET(2)(sp)		/* f2(ft2)		FP temporary register */
	load_fpu  f3,  PORT_CONTEXT_fpuOFFSET(3)(sp)		/* f3(ft3)		FP temporary register */
	load_fpu  f4,  PORT_CONTEXT_fpuOFFSET(4)(sp)		/* f4(ft4)		FP temporary register */
	load_fpu  f5,  PORT_CONTEXT_fpuOFFSET(5)(sp)		/* f5(ft5)		FP temporary register */
	load_fpu  f6,  PORT_CONTEXT_fpuOFFSET(6)(sp)		/* f6(ft6)		FP temporary register */
	load_fpu  f7,  PORT_CONTEXT_fpuOFFSET(7)(sp)		/* f7(ft7)		FP temporary register */

	load_fpu  f8,  PORT_CONTEXT_fpuOFFSET(8)(sp)		/* f8(fs0)		FP Saved register */
	load_fpu  f9,  PORT_CONTEXT_fpuOFFSET(9)(sp)		/* f9(fs0)		FP Saved register */

	load_fpu  f10,  PORT_CONTEXT_fpuOFFSET(10)(sp)	/* f10(fa0)		FP arguments/return values register */
	load_fpu  f11,  PORT_CONTEXT_fpuOFFSET(11)(sp)	/* f11(fa1)		FP arguments/return values register */

	load_fpu  f12,  PORT_CONTEXT_fpuOFFSET(12)(sp)	/* f12(fa2)		FP arguments register */
	load_fpu  f13,  PORT_CONTEXT_fpuOFFSET(13)(sp)	/* f13(fa3)		FP arguments register */
	load_fpu  f14,  PORT_CONTEXT_fpuOFFSET(14)(sp)	/* f14(fa4)		FP arguments register */
	load_fpu  f15,  PORT_CONTEXT_fpuOFFSET(15)(sp)	/* f15(fa5)		FP arguments register */
	load_fpu  f16,  PORT_CONTEXT_fpuOFFSET(16)(sp)	/* f16(fa6)		FP arguments register */
	load_fpu  f17,  PORT_CONTEXT_fpuOFFSET(17)(sp)	/* f17(fa7)		FP arguments register */

	load_fpu  f18,  PORT_CONTEXT_fpuOFFSET(18)(sp)	/* f18(fs2)		FP Saved register */
	load_fpu  f19,  PORT_CONTEXT_fpuOFFSET(19)(sp)	/* f19(fs3)		FP Saved register */
	load_fpu  f20,  PORT_CONTEXT_fpuOFFSET(20)(sp)	/* f20(fs4)		FP Saved register */
	load_fpu  f21,  PORT_CONTEXT_fpuOFFSET(21)(sp)	/* f21(fs5)		FP Saved register */
	load_fpu  f22,  PORT_CONTEXT_fpuOFFSET(22)(sp)	/* f22(fs6)		FP Saved register */
	load_fpu  f23,  PORT_CONTEXT_fpuOFFSET(23)(sp)	/* f23(fs7)		FP Saved register */
	load_fpu  f24,  PORT_CONTEXT_fpuOFFSET(24)(sp)	/* f24(fs8)		FP Saved register */
	load_fpu  f25,  PORT_CONTEXT_fpuOFFSET(25)(sp)	/* f25(fs9)		FP Saved register */
	load_fpu  f26,  PORT_CONTEXT_fpuOFFSET(26)(sp)	/* f26(fs10)	FP Saved register */
	load_fpu  f27,  PORT_CONTEXT_fpuOFFSET(27)(sp)	/* f27(fs11)	FP Saved register */

	load_fpu  f28,  PORT_CONTEXT_fpuOFFSET(28)(sp)	/* f28(ft8)		FP temporary register */
	load_fpu  f29,  PORT_CONTEXT_fpuOFFSET(29)(sp)	/* f29(ft9)		FP temporary register */
	load_fpu  f30,  PORT_CONTEXT_fpuOFFSET(30)(sp)	/* f30(ft10)	FP temporary register */
	load_fpu  f31,  PORT_CONTEXT_fpuOFFSET(31)(sp)	/* f31(ft11)	FP temporary register */

	/* must set FS to clean */
	csrc 	mstatus, t0
	li 	t1, MSTATUS_FS_CLEAN
	csrs	mstatus, t1
1:
	.endm
#else
.macro portRESTORE_FpuReg
	/* No fpu registers to restore, so this macro does nothing. */
	.endm
#endif /* __riscv_fdiv */
/*-----------------------------------------------------------*/

.macro portSAVE_BaseReg
	/* Make room for the registers. */
	addi	sp, sp, -portasmREGISTER_CONTEXT_WORDSIZE
    store_x  x1,  PORT_CONTEXT_xOFFSET(1)(sp)		/* x1(ra)		Return address */
													/* x2(sp) ***** Should be save ouside this macro */
    store_x  x3,  PORT_CONTEXT_xOFFSET(3)(sp)		/* x3(gp)		Global pointer */
    store_x  x4,  PORT_CONTEXT_xOFFSET(4)(sp)		/* x4(tp)		Thread pointer */
    store_x  x5,  PORT_CONTEXT_xOFFSET(5)(sp)		/* x5(t0)		Temporary register */
    store_x  x6,  PORT_CONTEXT_xOFFSET(6)(sp)		/* x6(t1)		Temporary register*/
    store_x  x7,  PORT_CONTEXT_xOFFSET(7)(sp)		/* x7(t2)		Temporary register */
    store_x  x8,  PORT_CONTEXT_xOFFSET(8)(sp)		/* x8(s0/fp)	Saved register/Frame pointer */
    store_x  x9,  PORT_CONTEXT_xOFFSET(9)(sp)		/* x9(s1)		Saved register */
    store_x  x10, PORT_CONTEXT_xOFFSET(10)(sp)		/* x10(a0)		Function argument */
    store_x  x11, PORT_CONTEXT_xOFFSET(11)(sp)		/* x11(a1)		Function argument */
    store_x  x12, PORT_CONTEXT_xOFFSET(12)(sp)		/* x12(a2)		Function argument */
    store_x  x13, PORT_CONTEXT_xOFFSET(13)(sp)		/* x13(a3)		Function argument */
    store_x  x14, PORT_CONTEXT_xOFFSET(14)(sp)		/* x14(a4)		Function argument */
    store_x  x15, PORT_CONTEXT_xOFFSET(15)(sp)		/* x15(a5)		Function argument */
#ifndef __riscv_32e
    store_x  x16, PORT_CONTEXT_xOFFSET(16)(sp)		/* x16(a6)		Function arguments */
    store_x  x17, PORT_CONTEXT_xOFFSET(17)(sp)		/* x17(a7)		Function arguments */
    store_x  x18, PORT_CONTEXT_xOFFSET(18)(sp)		/* x18(s2)		Saved register */
    store_x  x19, PORT_CONTEXT_xOFFSET(19)(sp)		/* x19(s3)		Saved register */
    store_x  x20, PORT_CONTEXT_xOFFSET(20)(sp)		/* x20(s4)		Saved register */
    store_x  x21, PORT_CONTEXT_xOFFSET(21)(sp)		/* x21(s5)		Saved register */
    store_x  x22, PORT_CONTEXT_xOFFSET(22)(sp)		/* x22(s6)		Saved register */
    store_x  x23, PORT_CONTEXT_xOFFSET(23)(sp)		/* x23(s7)		Saved register */
    store_x  x24, PORT_CONTEXT_xOFFSET(24)(sp)		/* x24(s8)		Saved register */
    store_x  x25, PORT_CONTEXT_xOFFSET(25)(sp)		/* x25(s9)		Saved register */
    store_x  x26, PORT_CONTEXT_xOFFSET(26)(sp)		/* x26(s10)		Saved register */
    store_x  x27, PORT_CONTEXT_xOFFSET(27)(sp)		/* x27(s11)		Saved register */
    store_x  x28, PORT_CONTEXT_xOFFSET(28)(sp)		/* x28(t3)		Temporary register */
    store_x  x29, PORT_CONTEXT_xOFFSET(29)(sp)		/* x29(t4)		Temporary register */
    store_x  x30, PORT_CONTEXT_xOFFSET(30)(sp)		/* x30(t5)		Temporary register */
    store_x  x31, PORT_CONTEXT_xOFFSET(31)(sp)		/* x31(t6)		Temporary register */
#endif /* __riscv_32e */
	/* Save mcause, mepc & mstatus state */
	csrr a4, mepc
	csrr a5, mstatus		/* Required for MPIE bit. */
	store_x a4, PORT_CONTEXT_mepcOFFSET(sp)
	store_x a5, PORT_CONTEXT_mstatusOFFSET(sp)
	.endm
/*-----------------------------------------------------------*/

.macro portRESTORE_BaseReg
	/* Restore mepc & mstatus state */
	load_x  t0, PORT_CONTEXT_mepcOFFSET(sp)
	load_x  t1, PORT_CONTEXT_mstatusOFFSET(sp)
	csrw	mepc, t0
	csrw	mstatus, t1

    load_x  x1,  PORT_CONTEXT_xOFFSET(1)(sp)		/* x1(ra)		Return address */
													/* x2(sp) ***** Should be save ouside this macro */
    load_x  x3,  PORT_CONTEXT_xOFFSET(3)(sp)		/* x3(gp)		Global pointer */
    load_x  x4,  PORT_CONTEXT_xOFFSET(4)(sp)		/* x4(tp)		Thread pointer */
    load_x  x5,  PORT_CONTEXT_xOFFSET(5)(sp)		/* x5(t0)		Temporary register */
    load_x  x6,  PORT_CONTEXT_xOFFSET(6)(sp)		/* x6(t1)		Temporary register*/
    load_x  x7,  PORT_CONTEXT_xOFFSET(7)(sp)		/* x7(t2)		Temporary register */
    load_x  x8,  PORT_CONTEXT_xOFFSET(8)(sp)		/* x8(s0/fp)	Saved register/Frame pointer */
    load_x  x9,  PORT_CONTEXT_xOFFSET(9)(sp)		/* x9(s1)		Saved register */
    load_x  x10, PORT_CONTEXT_xOFFSET(10)(sp)		/* x10(a0)		Function argument */
    load_x  x11, PORT_CONTEXT_xOFFSET(11)(sp)		/* x11(a1)		Function argument */
    load_x  x12, PORT_CONTEXT_xOFFSET(12)(sp)		/* x12(a2)		Function argument */
    load_x  x13, PORT_CONTEXT_xOFFSET(13)(sp)		/* x13(a3)		Function argument */
    load_x  x14, PORT_CONTEXT_xOFFSET(14)(sp)		/* x14(a4)		Function argument */
    load_x  x15, PORT_CONTEXT_xOFFSET(15)(sp)		/* x15(a5)		Function argument */
#ifndef __riscv_32e
    load_x  x16, PORT_CONTEXT_xOFFSET(16)(sp)		/* x16(a6)		Function arguments */
    load_x  x17, PORT_CONTEXT_xOFFSET(17)(sp)		/* x17(a7)		Function arguments */
    load_x  x18, PORT_CONTEXT_xOFFSET(18)(sp)		/* x18(s2)		Saved register */
    load_x  x19, PORT_CONTEXT_xOFFSET(19)(sp)		/* x19(s3)		Saved register */
    load_x  x20, PORT_CONTEXT_xOFFSET(20)(sp)		/* x20(s4)		Saved register */
    load_x  x21, PORT_CONTEXT_xOFFSET(21)(sp)		/* x21(s5)		Saved register */
    load_x  x22, PORT_CONTEXT_xOFFSET(22)(sp)		/* x22(s6)		Saved register */
    load_x  x23, PORT_CONTEXT_xOFFSET(23)(sp)		/* x23(s7)		Saved register */
    load_x  x24, PORT_CONTEXT_xOFFSET(24)(sp)		/* x24(s8)		Saved register */
    load_x  x25, PORT_CONTEXT_xOFFSET(25)(sp)		/* x25(s9)		Saved register */
    load_x  x26, PORT_CONTEXT_xOFFSET(26)(sp)		/* x26(s10)		Saved register */
    load_x  x27, PORT_CONTEXT_xOFFSET(27)(sp)		/* x27(s11)		Saved register */
    load_x  x28, PORT_CONTEXT_xOFFSET(28)(sp)		/* x28(t3)		Temporary register */
    load_x  x29, PORT_CONTEXT_xOFFSET(29)(sp)		/* x29(t4)		Temporary register */
    load_x  x30, PORT_CONTEXT_xOFFSET(30)(sp)		/* x30(t5)		Temporary register */
    load_x  x31, PORT_CONTEXT_xOFFSET(31)(sp)		/* x31(t6)		Temporary register */
#endif /* __riscv_32e */
	.endm
/*-----------------------------------------------------------*/

.align 8
.func
freertos_risc_v_trap_handler:
	/* We do not know if this is an ASYNC or SYNC
	 * If ASYNC, it is a normal interrupt
	 *  and the stack pointer is assumed good.
	 * else (SYNC)
	 *  We could be here due to a bus fault.
	 */
    csrw	mscratch, t0
    csrr	t0, mcause
    blt  	t0, x0, handle_interrupt

handle_exception:
	/* mscratch = old t0
	 * t0 = mcause
	 * mcause = small number 0..16
	 *  0 Instruction address misaligned
	 *  1 Instruction access fault
	 *  2 Illegal instruction
	 *  3 Breakpoint
	 *  4 Load address misaligned
	 *  5 Load access fault
	 *  6 Store/AMO address misaligned
	 *  7 Store/AMO access fault
	 *  8 Environment call from U-mode
	 *  9 Environment call from S-mode
	 *  10 Reserved
	 *  11 Environment call from M-mode
	 *  12 Instruction page fault
	 *  13 Load page fault
	 *  14 Reserved
	 *  15 Store/AMO page fault
	 *  ≥16 Reserved
	 *
	 * if( mcause between 8 and 11  ) we are good - ecall
	 * else: problem
	 */

	addi	t0, t0, -8
	blt		t0, x0, is_exception /* mcause < 8, must be fault */
	addi	t0, t0, -4
	blt		t0, x0, ecall_yield

is_exception:
	/* restore t0 and save sp in mscratch. */
	csrr	t0, mscratch
	   csrw	mscratch, sp
	/* Switch to ISR stack before function call. */
	load_x	sp, xISRStackTop			
	portSAVE_BaseReg
	csrrw	t0, mscratch, t0
	/* SP = X2, so save it */
	store_x	t0, PORT_CONTEXT_xOFFSET(2)(sp)
	/* Defined in freertos_risc_v_chip_specific_extensions.h to save any registers unique to the RISC-V implementation. */
	portasmSAVE_ADDITIONAL_REGISTERS
	/* Save any fpu registers */
	portSAVE_FpuReg
	/* Execption is treated by external function */
	jal portHANDLE_EXCEPTION
	/* in case that the go back from exception, restore registers */
	portRESTORE_FpuReg
	portasmRESTORE_ADDITIONAL_REGISTERS
	portRESTORE_BaseReg
	load_x  x2, PORT_CONTEXT_xOFFSET(2)(sp)
	mret
 
ecall_yield:
	portSAVE_BaseReg
	/* a4 = mepc
	 * a5 = mstatus
	 * s0 will be use for pxCurrentTCB
	 * s1 will be use to save sp
	 */
	/* Synchronous so updated exception return address to the instruction after the instruction that generated the exeption. */
	addi	t0, a4, 4
	store_x	t0, PORT_CONTEXT_mepcOFFSET(sp) 
	/* Store the value of sp when the interrupt occur */
	addi 	t0, sp, portasmREGISTER_CONTEXT_WORDSIZE
	store_x t0, PORT_CONTEXT_xOFFSET(2)(sp)

	/* Defined in freertos_risc_v_chip_specific_extensions.h to save any registers unique to the RISC-V implementation. */
	portasmSAVE_ADDITIONAL_REGISTERS
	/* Save any fpu registers */
	portSAVE_FpuReg

	/* Load pxCurrentTCB and update first TCB member(pxTopOfStack) with sp. */
	load_x  s0, pxCurrentTCB
	store_x  sp, 0( s0 )

	/* Save sp into s1 */
	mv  s1, sp
	load_x sp, xISRStackTop			/* Switch to ISR stack before function call. */

	j	switch_context

handle_interrupt:
	portSAVE_BaseReg
	/* a4 = mepc
	 * a5 = mstatus
	 * s0 will be use for pxCurrentTCB
	 * s1 will be use to save sp
	 */

	/* Store the value of sp when the interrupt occur */
	addi t0, sp, portasmREGISTER_CONTEXT_WORDSIZE
	store_x  t0, PORT_CONTEXT_xOFFSET(2)(sp)

	/* Defined in freertos_risc_v_chip_specific_extensions.h to save any registers unique to the RISC-V implementation. */
	portasmSAVE_ADDITIONAL_REGISTERS
	/* Save any fpu registers */
	portSAVE_FpuReg

	/* Load pxCurrentTCB and update first TCB member(pxTopOfStack) with sp. */
	load_x  s0, pxCurrentTCB
	store_x  sp, 0( s0 )

	/* Save sp into s1 */
	mv  s1, sp
	load_x sp, xISRStackTop			/* Switch to ISR stack before function call. */

#if( portasmHAS_MTIME != 0 )
	addi t0, x0, 1

	slli t0, t0, __riscv_xlen - 1   /* LSB is already set, shift into MSB.  Shift 31 on 32-bit or 63 on 64-bit cores. */
	addi t1, t0, 7					/* 0x8000[]0007 == machine timer interrupt. */
    csrr t2, mcause
	bne t2, t1, test_if_external_interrupt

	load_x t0, pullMachineTimerCompareRegister  /* Load address of compare register into t0. */
	load_x t1, pullNextTime  		/* Load the address of ullNextTime into t1. */

	#if( __riscv_xlen == 32 )
		/* Update the 64-bit mtimer compare match value in two 32-bit writes. */
		lw 	a0, 0(t1)				/* Load the low word of ullNextTime into a0. */
		lw 	a1, 4(t1)				/* Load the high word of ullNextTime into a1. */
		li  t2, -1
		sw 	t2, 4(t0)				/* Store low word of ullNextTime into compare register. */
		sw 	a0, 0(t0)				/* Store low word of ullNextTime into compare register. */
		sw 	a1, 4(t0)				/* Store high word of ullNextTime into compare register. */
		lw 	t0, uxTimerIncrementsForOneTick	/* Load the value of ullTimerIncrementForOneTick into t0 (could this be optimized by storing in an array next to pullNextTime?). */
		add a2, t0, a0				/* Add the low word of ullNextTime to the timer increments for one tick (assumes timer increment for one tick fits in 32-bits). */
		sltu t2, a2, a0				/* See if the sum of low words overflowed (what about the zero case?). */
		add a3, a1, t2				/* Add overflow to high word of ullNextTime. */
		sw 	a2, 0(t1)				/* Store new low word of ullNextTime. */
		sw 	a3, 4(t1)				/* Store new high word of ullNextTime. */
	#endif /* ( __riscv_xlen == 32 ) */
	#if( __riscv_xlen == 64 )
		/* Update the 64-bit mtimer compare match value. */
		ld 	a0, 0(t1)			 	/* Load ullNextTime into a0. */
		sd 	a0, 0(t0)				/* Store ullNextTime into compare register. */
		ld 	t0, uxTimerIncrementsForOneTick  /* Load the value of ullTimerIncrementForOneTick into t0 (could this be optimized by storing in an array next to pullNextTime?). */
		add 	a2, t0, a0				/* Add ullNextTime to the timer increments for one tick. */
		sd 	a2, 0(t1)				/* Store ullNextTime. */
	#endif /* ( __riscv_xlen == 64 ) */

	jal xTaskIncrementTick
	beqz a0, restore_before_exit		/* Don't switch context if incrementing tick didn't unblock a task. */
	j switch_context

restore_before_exit:
	mv  sp, s1
	j end_trap_handler

test_if_external_interrupt:			/* If there is a CLINT and the mtimer interrupt is not pending then check to see if an external interrupt is pending. */
	addi t1, t1, 4					/* 0x80000007 + 4 = 0x8000000b == Machine external interrupt. */
    csrr t2, mcause
	bne t2, t1, unrecoverable_error	/* Something as yet unhandled. */
	j unrecoverable_error
#endif /* ( portasmHAS_MTIME != 0 ) */

external_interrupt:
	/* Switch to ISR stack before function call. */
	load_x sp, xISRStackTop
	jal portHANDLE_INTERRUPT
	mv	sp, s1
	j end_trap_handler

unrecoverable_error:
    csrr 	t0, mcause              /* For viewing in the debugger only. */
    csrr	t1, mepc                /* For viewing in the debugger only. */
    csrr 	t2, mstatus
	wfi
	j unrecoverable_error

switch_context:
	jal	vTaskSwitchContext
	load_x s0, pxCurrentTCB			/* Load pxCurrentTCB. */
	load_x  sp, 0( s0 )				/* Read sp from first TCB member. */

end_trap_handler:	
	load_x s0, pxCurrentTCB			/* Load pxCurrentTCB. */
	load_x  t1, PORT_CONTEXT_xOFFSET(2)(sp)
	store_x  t1, 0( s0 )			/* Write sp saved value to first TCB member. */

	/* restore registers */
	portRESTORE_FpuReg
	portasmRESTORE_ADDITIONAL_REGISTERS
	portRESTORE_BaseReg
	load_x  x2, PORT_CONTEXT_xOFFSET(2)(sp)
	mret
	.endfunc
/*-----------------------------------------------------------*/

.align 8
.func
xPortStartFirstTask:

#if( portasmHAS_SIFIVE_CLINT != 0 )
	/* If there is a clint then interrupts can branch directly to the FreeRTOS
	trap handler.  Otherwise the interrupt controller will need to be configured
	outside of this file. */
	la t0, freertos_risc_v_trap_handler
	csrw mtvec, t0
#endif /* ( portasmHAS_SIFIVE_CLINT != 0 ) */

	/** Set all register to the FirstTask context */
	load_x  t2, pxCurrentTCB			/* Load pxCurrentTCB. */
	load_x  sp, 0( t2 )				 	/* Read sp from first TCB member. */

	/* Restore first TCB member */
	load_x  t1,  PORT_CONTEXT_xOFFSET(2)(sp)
	store_x  t1, 0( t2 )				/* Write sp saved value to first TCB member. */

	/* enable interrupt */
    #if( portasmHAS_MTIME != 0 )
	    li t0, 0x880
	    csrs mie, t0
    #else
	    li t0, 0x800
	    csrs mie, t0
    #endif /* ( portasmHAS_MTIME != 0 ) */

	portRESTORE_FpuReg
	portasmRESTORE_ADDITIONAL_REGISTERS
	/* Set MIE bit so the first task starts with interrupts enabled - required as returns with ret not eret. */
	load_x  t1, PORT_CONTEXT_mstatusOFFSET(sp)
	addi	t1, t1, 0x08				
	store_x t1, PORT_CONTEXT_mstatusOFFSET(sp)

	portRESTORE_BaseReg

	load_x  ra, PORT_CONTEXT_mepcOFFSET(sp) /* Note for starting the scheduler the exception return address is used as the function return address. */
	load_x  x2, PORT_CONTEXT_xOFFSET(2)(sp)
	mret
	.endfunc
/*-----------------------------------------------------------*/

/*
 * Unlike other ports pxPortInitialiseStack() is written in assembly code as it
 * needs access to the portasmADDITIONAL_CONTEXT_SIZE constant.  The prototype
 * for the function is as per the other ports:
 * StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters );
 *
 * As per the standard RISC-V ABI pxTopcOfStack is passed in in a0, pxCode in
 * a1, and pvParameters in a2.  The new top of stack is passed out in a0.
 *
 * RISC-V maps registers to ABI names as follows (X1 to X31 integer registers
 * for the 'I' profile, X1 to X15 for the 'E' profile).
 *
 * Register		ABI Name	Description						Saver
 * x0			zero		Hard-wired zero					-
 * x1			ra			Return address					Caller
 * x2			sp			Stack pointer					Callee
 * x3			gp			Global pointer					-
 * x4			tp			Thread pointer					-
 * x5-7			t0-2		Temporaries						Caller
 * x8			s0/fp		Saved register/Frame pointer	Callee
 * x9			s1			Saved register					Callee
 * x10-11		a0-1		Function Arguments/return values Caller
 * x12-17		a2-7		Function arguments				Caller
 * x18-27		s2-11		Saved registers					Callee
 * x28-31		t3-6		Temporaries						Caller
 *
 * The RISC-V context is saved t FreeRTOS tasks in the following stack frame,
 * where the global and thread pointers are currently assumed to be constant so
 * are not saved:
 * The RISC-V context is saved t FreeRTOS tasks in the following stack frame:
 *
 * ruf (in order to be 16 bytes aligned)
 * ruf (in order to be 16 bytes aligned)
 * pxCode - mepc
 * mstatus
 * x31 (Only for 'I' profile)
 * x30 (Only for 'I' profile)
 * x29 (Only for 'I' profile)
 * x28 (Only for 'I' profile)
 * x27 (Only for 'I' profile)
 * x26 (Only for 'I' profile)
 * x25 (Only for 'I' profile)
 * x24 (Only for 'I' profile)
 * x23 (Only for 'I' profile)
 * x22 (Only for 'I' profile)
 * x21 (Only for 'I' profile)
 * x20 (Only for 'I' profile)
 * x19 (Only for 'I' profile)
 * x18 (Only for 'I' profile)
 * x17 (Only for 'I' profile)
 * x16 (Only for 'I' profile)
 * x15
 * x14
 * x13
 * x12
 * x11
 * pvParameters - x10 (a0)
 * x9
 * x8
 * x7
 * x6
 * x5
 * x4 (tp)
 * x3 (gp)
 * x2 (sp)
 * portTASK_RETURN_ADDRESS - x1 (ra)
 * x0
 * [chip specific registers go here]
 * pxCode
 */
.align 8
.func
pxPortInitialiseStack:

	csrr t0, mstatus					/* Obtain current mstatus value. */
	andi t0, t0, ~0x8					/* Ensure interrupts are disabled when the stack is restored within an ISR.  Required when a task is created after the schedulre has been started, otherwise interrupts would be disabled anyway. */
	addi t1, x0, 0x188					/* Generate the value 0x1880, which are the MPIE and MPP bits to set in mstatus. */
	slli t1, t1, 4
	not t2, t1							/* reset previous value */
	and t0, t0, t2
	or t0, t0, t1						/* Set MPIE and MPP bits in mstatus value. */

	/* Make room for the registers. */
	addi	t2, a0, -portasmREGISTER_CONTEXT_WORDSIZE
	
	store_x  x0,  PORT_CONTEXT_xOFFSET(1)(t2)	/* x1(ra)		Return address */
	store_x  a0,  PORT_CONTEXT_xOFFSET(2)(t2)	/* x2(sp) 		Stack pointer */
	store_x  x3,  PORT_CONTEXT_xOFFSET(3)(t2)	/* x3(gp)		Global pointer */
	store_x  x4,  PORT_CONTEXT_xOFFSET(4)(t2)	/* x4(tp)		Thread pointer */
	store_x  x0,  PORT_CONTEXT_xOFFSET(5)(t2)	/* x5(t0)		Temporaries */
	store_x  x0,  PORT_CONTEXT_xOFFSET(6)(t2)	/* x6(t1)		Temporaries */
	store_x  x0,  PORT_CONTEXT_xOFFSET(7)(t2)	/* x7(t2)		Temporaries */
	store_x  x0,  PORT_CONTEXT_xOFFSET(8)(t2)	/* x8(s0/fp)	Saved register/Frame pointer */
	store_x  x0,  PORT_CONTEXT_xOFFSET(9)(t2)	/* x9(s1)		Saved register */
	store_x  a2, PORT_CONTEXT_xOFFSET(10)(t2)	/* x10(a0)		Function arguments */
	store_x  x0, PORT_CONTEXT_xOFFSET(11)(t2)	/* x11(a1)		Function arguments */
	store_x  x0, PORT_CONTEXT_xOFFSET(12)(t2)	/* x12(a2)		Function arguments */
	store_x  x0, PORT_CONTEXT_xOFFSET(13)(t2)	/* x13(a3)		Function arguments */
	store_x  x0, PORT_CONTEXT_xOFFSET(14)(t2)	/* x14(a4)		Function arguments */
	store_x  x0, PORT_CONTEXT_xOFFSET(15)(t2)	/* x15(a5)		Function arguments */
#ifndef __riscv_32e
	store_x  x0, PORT_CONTEXT_xOFFSET(16)(t2)	/* x16(a6)		Function arguments */
	store_x  x0, PORT_CONTEXT_xOFFSET(17)(t2)	/* x17(a7)		Function arguments */
	store_x  x0, PORT_CONTEXT_xOFFSET(18)(t2)	/* x18(s2)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(19)(t2)	/* x19(s3)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(20)(t2)	/* x20(s4)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(21)(t2)	/* x21(s5)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(22)(t2)	/* x22(s6)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(23)(t2)	/* x23(s7)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(24)(t2)	/* x24(s8)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(25)(t2)	/* x25(s9)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(26)(t2)	/* x26(s10)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(27)(t2)	/* x27(s11)		Saved registers */
	store_x  x0, PORT_CONTEXT_xOFFSET(28)(t2)	/* x28(t3)		Temporaries */
	store_x  x0, PORT_CONTEXT_xOFFSET(29)(t2)	/* x29(t4)		Temporaries */
	store_x  x0, PORT_CONTEXT_xOFFSET(30)(t2)	/* x30(t5)		Temporaries */
	store_x  x0, PORT_CONTEXT_xOFFSET(31)(t2)	/* x31(t6)		Temporaries */
#endif /* __riscv_32e */

	store_x a1, PORT_CONTEXT_mepcOFFSET(t2)
	store_x t0, PORT_CONTEXT_mstatusOFFSET(t2)

	/* The number of additional registers. */
	addi t0, x0, portasmADDITIONAL_CONTEXT_SIZE 
chip_specific_stack_frame:				/* First add any chip specific registers to the stack frame being created. */
	beq t0, x0, 1f						/* No more chip specific registers to save. */
	addi t2, t2, -portWORD_SIZE			/* Make space for chip specific register. */
	store_x x0, 0(t2)					/* Give the chip specific register an initial value of zero. */
	addi t0, t0, -1						/* Decrement the count of chip specific registers remaining. */
	j chip_specific_stack_frame			/* Until no more chip specific registers. */
1:

	#ifdef __riscv_fdiv
		/* Make room for the fpu registers. */
		/* Here we use the memory space needed for all fpu registers instead of using the number of fpu registers */
		/* Thanks to it we usually manage any xxbits core with yybits fpu */
		addi t0, x0, portasmFPU_CONTEXT_WORDSIZE
	fpu_specific_stack_frame:
		beq t0, x0, 1f						/* No more space is needed. */
		addi t2, t2, -portWORD_SIZE
		store_x x0, 0(t2)					/* Give an initial value of zero. */
		addi t0, t0, -portWORD_SIZE			/* Decrement the count space remaining. */
		j fpu_specific_stack_frame			/* Until no more space is needed. */
	1:	
	#endif /* __riscv_fdiv */

	mv a0, t2
	ret
	.endfunc
/*-----------------------------------------------------------*/
