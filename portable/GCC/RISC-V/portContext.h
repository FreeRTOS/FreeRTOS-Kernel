/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#ifndef PORTCONTEXT_H
#define PORTCONTEXT_H

#ifndef configENABLE_FPU
    #define configENABLE_FPU 0
#endif

#if __riscv_xlen == 64
    #define portWORD_SIZE    8
    #define store_x          sd
    #define load_x           ld
#elif __riscv_xlen == 32
    #define store_x          sw
    #define load_x           lw
    #define portWORD_SIZE    4
#else
    #error Assembler did not define __riscv_xlen
#endif

#include "freertos_risc_v_chip_specific_extensions.h"

/* Only the standard core registers are stored by default.  Any additional
 * registers must be saved by the portasmSAVE_ADDITIONAL_REGISTERS and
 * portasmRESTORE_ADDITIONAL_REGISTERS macros - which can be defined in a chip
 * specific version of freertos_risc_v_chip_specific_extensions.h.  See the
 * notes at the top of portASM.S file. */
#ifdef __riscv_32e
    #define portCONTEXT_SIZE               ( 15 * portWORD_SIZE )
    #define portCRITICAL_NESTING_OFFSET    14
#else
    #define portCONTEXT_SIZE               ( 31 * portWORD_SIZE )
    #define portCRITICAL_NESTING_OFFSET    30
#endif

#if ( configENABLE_FPU == 1 )
    /* Bit [14:13] in the mstatus encode the status of FPU state which is one of
     * the following values:
     * 1. Value: 0, Meaning: Off.
     * 2. Value: 1, Meaning: Initial.
     * 3. Value: 2, Meaning: Clean.
     * 4. Value: 3, Meaning: Dirty.
     */
    #define MSTATUS_FS_MASK                 0x6000
    #define MSTATUS_FS_INITIAL              0x2000
    #define MSTATUS_FS_CLEAN                0x4000
    #define MSTATUS_FS_DIRTY                0x6000
    #define MSTATUS_FS_OFFSET               13

    #ifdef __riscv_fdiv
        #if __riscv_flen == 32
            #define load_f                  flw
            #define store_f                 fsw
        #elif __riscv_flen == 64
            #define load_f                  fld
            #define store_f                 fsd
        #else
            #error Assembler did not define __riscv_flen
        #endif

        #define portFPU_REG_SIZE                ( __riscv_flen / 8 )
        #define portFPU_REG_COUNT               33 /* 32 Floating point registers plus one CSR. */
        #define portFPU_CONTEXT_SIZE            ( portFPU_REG_SIZE * portFPU_REG_COUNT )
    #else
        #error configENABLE_FPU must not be set to 1 if the hardwar does not have FPU
    #endif
#endif
/*-----------------------------------------------------------*/

.extern pxCurrentTCB
.extern xISRStackTop
.extern xCriticalNesting
.extern pxCriticalNesting
/*-----------------------------------------------------------*/

    .macro portcontexSAVE_FPU_CONTEXT
addi sp, sp, -( portFPU_CONTEXT_SIZE )
/* Store the FPU registers. */
store_f f0,  2  * portFPU_REG_SIZE( sp )
store_f f1,  3  * portFPU_REG_SIZE( sp )
store_f f2,  4  * portFPU_REG_SIZE( sp )
store_f f3,  5  * portFPU_REG_SIZE( sp )
store_f f4,  6  * portFPU_REG_SIZE( sp )
store_f f5,  7  * portFPU_REG_SIZE( sp )
store_f f6,  8  * portFPU_REG_SIZE( sp )
store_f f7,  9  * portFPU_REG_SIZE( sp )
store_f f8,  10 * portFPU_REG_SIZE( sp )
store_f f9,  11 * portFPU_REG_SIZE( sp )
store_f f10, 12 * portFPU_REG_SIZE( sp )
store_f f11, 13 * portFPU_REG_SIZE( sp )
store_f f12, 14 * portFPU_REG_SIZE( sp )
store_f f13, 15 * portFPU_REG_SIZE( sp )
store_f f14, 16 * portFPU_REG_SIZE( sp )
store_f f15, 17 * portFPU_REG_SIZE( sp )
store_f f16, 18 * portFPU_REG_SIZE( sp )
store_f f17, 19 * portFPU_REG_SIZE( sp )
store_f f18, 20 * portFPU_REG_SIZE( sp )
store_f f19, 21 * portFPU_REG_SIZE( sp )
store_f f20, 22 * portFPU_REG_SIZE( sp )
store_f f21, 23 * portFPU_REG_SIZE( sp )
store_f f22, 24 * portFPU_REG_SIZE( sp )
store_f f23, 25 * portFPU_REG_SIZE( sp )
store_f f24, 26 * portFPU_REG_SIZE( sp )
store_f f25, 27 * portFPU_REG_SIZE( sp )
store_f f26, 28 * portFPU_REG_SIZE( sp )
store_f f27, 29 * portFPU_REG_SIZE( sp )
store_f f28, 30 * portFPU_REG_SIZE( sp )
store_f f29, 31 * portFPU_REG_SIZE( sp )
store_f f30, 32 * portFPU_REG_SIZE( sp )
store_f f31, 33 * portFPU_REG_SIZE( sp )
csrr t0, fcsr
store_x t0,  34 * portFPU_REG_SIZE( sp )
    .endm
/*-----------------------------------------------------------*/

    .macro portcontextRESTORE_FPU_CONTEXT
/* Restore the FPU registers. */
load_f f0,  2  * portFPU_REG_SIZE( sp )
load_f f1,  3  * portFPU_REG_SIZE( sp )
load_f f2,  4  * portFPU_REG_SIZE( sp )
load_f f3,  5  * portFPU_REG_SIZE( sp )
load_f f4,  6  * portFPU_REG_SIZE( sp )
load_f f5,  7  * portFPU_REG_SIZE( sp )
load_f f6,  8  * portFPU_REG_SIZE( sp )
load_f f7,  9  * portFPU_REG_SIZE( sp )
load_f f8,  10 * portFPU_REG_SIZE( sp )
load_f f9,  11 * portFPU_REG_SIZE( sp )
load_f f10, 12 * portFPU_REG_SIZE( sp )
load_f f11, 13 * portFPU_REG_SIZE( sp )
load_f f12, 14 * portFPU_REG_SIZE( sp )
load_f f13, 15 * portFPU_REG_SIZE( sp )
load_f f14, 16 * portFPU_REG_SIZE( sp )
load_f f15, 17 * portFPU_REG_SIZE( sp )
load_f f16, 18 * portFPU_REG_SIZE( sp )
load_f f17, 19 * portFPU_REG_SIZE( sp )
load_f f18, 20 * portFPU_REG_SIZE( sp )
load_f f19, 21 * portFPU_REG_SIZE( sp )
load_f f20, 22 * portFPU_REG_SIZE( sp )
load_f f21, 23 * portFPU_REG_SIZE( sp )
load_f f22, 24 * portFPU_REG_SIZE( sp )
load_f f23, 25 * portFPU_REG_SIZE( sp )
load_f f24, 26 * portFPU_REG_SIZE( sp )
load_f f25, 27 * portFPU_REG_SIZE( sp )
load_f f26, 28 * portFPU_REG_SIZE( sp )
load_f f27, 29 * portFPU_REG_SIZE( sp )
load_f f28, 30 * portFPU_REG_SIZE( sp )
load_f f29, 31 * portFPU_REG_SIZE( sp )
load_f f30, 32 * portFPU_REG_SIZE( sp )
load_f f31, 33 * portFPU_REG_SIZE( sp )
load_x t0,  34 * portFPU_REG_SIZE( sp )
csrw fcsr, t0
addi sp, sp, ( portFPU_CONTEXT_SIZE )
    .endm
/*-----------------------------------------------------------*/

   .macro portcontextSAVE_CONTEXT_INTERNAL
addi sp, sp, -portCONTEXT_SIZE
store_x x1,  2  * portWORD_SIZE( sp )
store_x x5,  3  * portWORD_SIZE( sp )
store_x x6,  4  * portWORD_SIZE( sp )
store_x x7,  5  * portWORD_SIZE( sp )
store_x x8,  6  * portWORD_SIZE( sp )
store_x x9,  7  * portWORD_SIZE( sp )
store_x x10, 8  * portWORD_SIZE( sp )
store_x x11, 9  * portWORD_SIZE( sp )
store_x x12, 10 * portWORD_SIZE( sp )
store_x x13, 11 * portWORD_SIZE( sp )
store_x x14, 12 * portWORD_SIZE( sp )
store_x x15, 13 * portWORD_SIZE( sp )
#ifndef __riscv_32e
    store_x x16, 14 * portWORD_SIZE( sp )
    store_x x17, 15 * portWORD_SIZE( sp )
    store_x x18, 16 * portWORD_SIZE( sp )
    store_x x19, 17 * portWORD_SIZE( sp )
    store_x x20, 18 * portWORD_SIZE( sp )
    store_x x21, 19 * portWORD_SIZE( sp )
    store_x x22, 20 * portWORD_SIZE( sp )
    store_x x23, 21 * portWORD_SIZE( sp )
    store_x x24, 22 * portWORD_SIZE( sp )
    store_x x25, 23 * portWORD_SIZE( sp )
    store_x x26, 24 * portWORD_SIZE( sp )
    store_x x27, 25 * portWORD_SIZE( sp )
    store_x x28, 26 * portWORD_SIZE( sp )
    store_x x29, 27 * portWORD_SIZE( sp )
    store_x x30, 28 * portWORD_SIZE( sp )
    store_x x31, 29 * portWORD_SIZE( sp )
#endif /* ifndef __riscv_32e */

load_x t0, xCriticalNesting                                   /* Load the value of xCriticalNesting into t0. */
store_x t0, portCRITICAL_NESTING_OFFSET * portWORD_SIZE( sp ) /* Store the critical nesting value to the stack. */

#if( configENABLE_FPU == 1 )
    csrr t0, mstatus
    srl t1, t0, MSTATUS_FS_OFFSET
    andi t1, t1, 3
    addi t2, x0, 3
    bne t1, t2, 1f /* If FPU status is not dirty, do not save FPU registers. */

    portcontexSAVE_FPU_CONTEXT
1:
#endif

portasmSAVE_ADDITIONAL_REGISTERS /* Defined in freertos_risc_v_chip_specific_extensions.h to save any registers unique to the RISC-V implementation. */

csrr t0, mstatus
store_x t0, 1 * portWORD_SIZE( sp )

#if( configENABLE_FPU == 1 )
    /* Mark the FPU as clean, if it was dirty and we saved FPU registers. */
    srl t1, t0, MSTATUS_FS_OFFSET
    andi t1, t1, 3
    addi t2, x0, 3
    bne t1, t2, 2f

    li t1, ~MSTATUS_FS_MASK
    and t0, t0, t1
    li t1, MSTATUS_FS_CLEAN
    or t0, t0, t1
    csrw mstatus, t0
2:
#endif

load_x t0, pxCurrentTCB          /* Load pxCurrentTCB. */
store_x sp, 0 ( t0 )             /* Write sp to first TCB member. */

   .endm
/*-----------------------------------------------------------*/

   .macro portcontextSAVE_EXCEPTION_CONTEXT
portcontextSAVE_CONTEXT_INTERNAL
csrr a0, mcause
csrr a1, mepc
addi a1, a1, 4          /* Synchronous so update exception return address to the instruction after the instruction that generated the exception. */
store_x a1, 0 ( sp )    /* Save updated exception return address. */
load_x sp, xISRStackTop /* Switch to ISR stack. */
   .endm
/*-----------------------------------------------------------*/

   .macro portcontextSAVE_INTERRUPT_CONTEXT
portcontextSAVE_CONTEXT_INTERNAL
csrr a0, mcause
csrr a1, mepc
store_x a1, 0 ( sp )    /* Asynchronous interrupt so save unmodified exception return address. */
load_x sp, xISRStackTop /* Switch to ISR stack. */
   .endm
/*-----------------------------------------------------------*/

   .macro portcontextRESTORE_CONTEXT
load_x t1, pxCurrentTCB /* Load pxCurrentTCB. */
load_x sp, 0 ( t1 )     /* Read sp from first TCB member. */

/* Load mepc with the address of the instruction in the task to run next. */
load_x t0, 0 ( sp )
csrw mepc, t0

/* Restore mstatus register. */
load_x t0, 1 * portWORD_SIZE( sp )
csrw mstatus, t0

/* Defined in freertos_risc_v_chip_specific_extensions.h to restore any registers unique to the RISC-V implementation. */
portasmRESTORE_ADDITIONAL_REGISTERS

#if( configENABLE_FPU == 1 )
    csrr t0, mstatus
    srl t1, t0, MSTATUS_FS_OFFSET
    andi t1, t1, 3
    addi t2, x0, 3
    bne t1, t2, 3f /* If FPU status is not dirty, do not restore FPU registers. */

    portcontextRESTORE_FPU_CONTEXT
3:
#endif /* ifdef portasmSTORE_FPU_CONTEXT */

load_x t0, portCRITICAL_NESTING_OFFSET * portWORD_SIZE( sp ) /* Obtain xCriticalNesting value for this task from task's stack. */
load_x t1, pxCriticalNesting                                 /* Load the address of xCriticalNesting into t1. */
store_x t0, 0 ( t1 )                                         /* Restore the critical nesting value for this task. */

load_x x1,  2  * portWORD_SIZE( sp )
load_x x5,  3  * portWORD_SIZE( sp )
load_x x6,  4  * portWORD_SIZE( sp )
load_x x7,  5  * portWORD_SIZE( sp )
load_x x8,  6  * portWORD_SIZE( sp )
load_x x9,  7  * portWORD_SIZE( sp )
load_x x10, 8  * portWORD_SIZE( sp )
load_x x11, 9  * portWORD_SIZE( sp )
load_x x12, 10 * portWORD_SIZE( sp )
load_x x13, 11 * portWORD_SIZE( sp )
load_x x14, 12 * portWORD_SIZE( sp )
load_x x15, 13 * portWORD_SIZE( sp )
#ifndef __riscv_32e
    load_x x16, 14 * portWORD_SIZE( sp )
    load_x x17, 15 * portWORD_SIZE( sp )
    load_x x18, 16 * portWORD_SIZE( sp )
    load_x x19, 17 * portWORD_SIZE( sp )
    load_x x20, 18 * portWORD_SIZE( sp )
    load_x x21, 19 * portWORD_SIZE( sp )
    load_x x22, 20 * portWORD_SIZE( sp )
    load_x x23, 21 * portWORD_SIZE( sp )
    load_x x24, 22 * portWORD_SIZE( sp )
    load_x x25, 23 * portWORD_SIZE( sp )
    load_x x26, 24 * portWORD_SIZE( sp )
    load_x x27, 25 * portWORD_SIZE( sp )
    load_x x28, 26 * portWORD_SIZE( sp )
    load_x x29, 27 * portWORD_SIZE( sp )
    load_x x30, 28 * portWORD_SIZE( sp )
    load_x x31, 29 * portWORD_SIZE( sp )
#endif /* ifndef __riscv_32e */
addi sp, sp, portCONTEXT_SIZE

mret
   .endm
/*-----------------------------------------------------------*/

#endif /* PORTCONTEXT_H */
