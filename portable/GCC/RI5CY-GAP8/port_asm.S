/*
 * Copyright (c) 2018, GreenWaves Technologies, Inc.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * o Redistributions of source code must retain the above copyright notice, this list
 *   of conditions and the following disclaimer.
 *
 * o Redistributions in binary form must reproduce the above copyright notice, this
 *   list of conditions and the following disclaimer in the documentation and/or
 *   other materials provided with the distribution.
 *
 * o Neither the name of GreenWaves Technologies, Inc. nor the names of its
 *   contributors may be used to endorse or promote products derived from this
 *   software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

        .file "port_asm.S"

#include "chip_specific_extensions/gap8/freertos_risc_v_chip_specific_extensions.h"
/*******************************************************************************
        This file contains some macro definitions and functions defined in ASM.
        Functions :
        *xPortStartScheduler
********************************************************************************/

/*******************************************************************************
        EXTERNAL VARIABLES & FUNCTIONS
*******************************************************************************/
        .extern pxCurrentTCB
        .extern prvSetupTimerInterrupt
        .extern ulCriticalNesting
/******************************************************************************/


/*******************************************************************************
        MACRO DEFINITION
*******************************************************************************/

/******************************************************************************/
        .macro DECLARE Routine
        .global \Routine
        .func \Routine
        .type \Routine, %function
        \Routine:
        .endm
/******************************************************************************/

/******************************************************************************/
        .macro portGAP8_SAVE_ADDITIONAL_CONTEXT

        addi sp, sp, -(portGAP8_ADDITIONAL_CONTEXT_SIZE * portWORD_SIZE)

        /* HW Loop regs. */
        csrr t0, LP_START_0
        sw t0, 0*portWORD_SIZE(sp)
        csrr t1, LP_END_0
        sw t1, 1*portWORD_SIZE(sp)
        csrr t2, LP_COUNT_0
        sw t2, 2*portWORD_SIZE(sp)
        csrr t0, LP_START_1
        sw t0, 3*portWORD_SIZE(sp)
        csrr t1, LP_END_1
        sw t1, 4*portWORD_SIZE(sp)
        csrr t2, LP_COUNT_1
        sw t2, 5*portWORD_SIZE(sp)

        .endm
/******************************************************************************/

/******************************************************************************/
        .macro portGAP8_RESTORE_ADDITIONAL_CONTEXT

        /* HW Loop regs. */
        lw t2, 5*portWORD_SIZE(sp)
        csrw LP_COUNT_1, t2
        lw t1, 4*portWORD_SIZE(sp)
        csrw LP_END_1, t1
        lw t0, 3*portWORD_SIZE(sp)
        csrw LP_START_1, t0
        lw t2, 2*portWORD_SIZE(sp)
        csrw LP_COUNT_0, t2
        lw t1, 1*portWORD_SIZE(sp)
        csrw LP_END_0, t1
        lw t0, 0*portWORD_SIZE(sp)
        csrw LP_START_0, t0

        addi sp, sp, +(portGAP8_ADDITIONAL_CONTEXT_SIZE * portWORD_SIZE)

        .endm
/******************************************************************************/

/******************************************************************************/
        .macro portGAP8_SAVE_CONTEXT

        addi sp, sp, -(portGAP8_CONTEXT_SIZE * portWORD_SIZE)

        /* General purpose registers. */
        sw ra, 0*portWORD_SIZE(sp)
        sw a0, 1*portWORD_SIZE(sp)
        sw a1, 2*portWORD_SIZE(sp)
        sw a2, 3*portWORD_SIZE(sp)
        sw a3, 4*portWORD_SIZE(sp)
        sw a4, 5*portWORD_SIZE(sp)
        sw a5, 6*portWORD_SIZE(sp)
        sw a6, 7*portWORD_SIZE(sp)
        sw a7, 8*portWORD_SIZE(sp)
        sw t0, 9*portWORD_SIZE(sp)
        sw t1, 10*portWORD_SIZE(sp)
        sw t2, 11*portWORD_SIZE(sp)
        sw t3, 12*portWORD_SIZE(sp)
        sw t4, 13*portWORD_SIZE(sp)
        sw t5, 14*portWORD_SIZE(sp)
        sw t6, 15*portWORD_SIZE(sp)
        sw s0, 16*portWORD_SIZE(sp)
        sw s1, 17*portWORD_SIZE(sp)
        sw s2, 18*portWORD_SIZE(sp)
        sw s3, 19*portWORD_SIZE(sp)
        sw s4, 20*portWORD_SIZE(sp)
        sw s5, 21*portWORD_SIZE(sp)
        sw s6, 22*portWORD_SIZE(sp)
        sw s7, 23*portWORD_SIZE(sp)
        sw s8, 24*portWORD_SIZE(sp)
        sw s9, 25*portWORD_SIZE(sp)
        sw s10, 26*portWORD_SIZE(sp)
        sw s11, 27*portWORD_SIZE(sp)

        /* MSTATUS */
        csrr t0, mstatus
        sw t0, 28*portWORD_SIZE(sp)

        /* MEPC */
        csrr t0, mepc
        sw t0, 29*portWORD_SIZE(sp)

        .endm
/******************************************************************************/

/******************************************************************************/
        .macro portGAP8_RESTORE_CONTEXT

        /* MEPC */
        lw t0, 29*portWORD_SIZE(sp)
        csrw mepc, t0

        /* MSTATUS */
        lw t0, 28*portWORD_SIZE(sp)
        csrw mstatus, t0

        /* General purpose registers. */
        lw s11, 27*portWORD_SIZE(sp)
        lw s10, 26*portWORD_SIZE(sp)
        lw s9, 25*portWORD_SIZE(sp)
        lw s8, 24*portWORD_SIZE(sp)
        lw s7, 23*portWORD_SIZE(sp)
        lw s6, 22*portWORD_SIZE(sp)
        lw s5, 21*portWORD_SIZE(sp)
        lw s4, 20*portWORD_SIZE(sp)
        lw s3, 19*portWORD_SIZE(sp)
        lw s2, 18*portWORD_SIZE(sp)
        lw s1, 17*portWORD_SIZE(sp)
        lw s0, 16*portWORD_SIZE(sp)
        lw t6, 15*portWORD_SIZE(sp)
        lw t5, 14*portWORD_SIZE(sp)
        lw t4, 13*portWORD_SIZE(sp)
        lw t3, 12*portWORD_SIZE(sp)
        lw t2, 11*portWORD_SIZE(sp)
        lw t1, 10*portWORD_SIZE(sp)
        lw t0, 9*portWORD_SIZE(sp)
        lw a7, 8*portWORD_SIZE(sp)
        lw a6, 7*portWORD_SIZE(sp)
        lw a5, 6*portWORD_SIZE(sp)
        lw a4, 5*portWORD_SIZE(sp)
        lw a3, 4*portWORD_SIZE(sp)
        lw a2, 3*portWORD_SIZE(sp)
        lw a1, 2*portWORD_SIZE(sp)
        lw a0, 1*portWORD_SIZE(sp)
        lw ra, 0*portWORD_SIZE(sp)

        addi sp, sp, +(portGAP8_CONTEXT_SIZE * portWORD_SIZE)

        .endm
/******************************************************************************/

/******************************************************************************/
        .macro portGAP8_SAVE_EPC

        csrr t0, mepc
        sw t0, 29*4(sp)

        .endm
/******************************************************************************/

/******************************************************************************/
        .macro portGAP8_SAVE_RA

        sw ra, 29*4(sp)

        .endm
/******************************************************************************/

/******************************************************************************/
        .macro portSAVE_CONTEXT

        portGAP8_SAVE_ADDITIONAL_CONTEXT
        portGAP8_SAVE_CONTEXT
        lw tp, pxCurrentTCB
        sw sp, 0*0(tp)

        .endm
/******************************************************************************/

/******************************************************************************/
        .macro portRESTORE_CONTEXT

        lw tp, pxCurrentTCB
        lw sp, 0*0(tp)
        portGAP8_RESTORE_CONTEXT
        portGAP8_RESTORE_ADDITIONAL_CONTEXT
        mret
        .endm
/******************************************************************************/


/*******************************************************************************
        FUNCTION DEFINITION
*******************************************************************************/

        /* xPortStartScheduler Function. */
        DECLARE xPortStartScheduler
        jal ra, prvSetupTimerInterrupt
        ;; la t0, ulCriticalNesting
        ;; sw zero, 0*0(t0)
        portRESTORE_CONTEXT
        .endfunc

/******************************************************************************/
