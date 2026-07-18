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

    .text

    /* Variables and functions. */
    .extern ullMaxAPIPriorityMask
    .extern pxCurrentTCB
    .extern vTaskSwitchContext
    .extern vApplicationIRQHandler
    .extern ullPortInterruptNesting
    .extern ullPortTaskHasFPUContext
    .extern ullCriticalNesting
    .extern ullPortYieldRequired
    .extern _freertos_vector_table

    .global FreeRTOS_IRQ_Handler
    .global FreeRTOS_SWI_Handler
    .global vPortRestoreTaskContext


.macro portSAVE_CONTEXT

    /* Switch to use the EL0 stack pointer. */
    MSR     SPSEL, #0

    /* Save the entire context. */
    STP     X0, X1, [SP, #-0x10]!
    STP     X2, X3, [SP, #-0x10]!
    STP     X4, X5, [SP, #-0x10]!
    STP     X6, X7, [SP, #-0x10]!
    STP     X8, X9, [SP, #-0x10]!
    STP     X10, X11, [SP, #-0x10]!
    STP     X12, X13, [SP, #-0x10]!
    STP     X14, X15, [SP, #-0x10]!
    STP     X16, X17, [SP, #-0x10]!
    STP     X18, X19, [SP, #-0x10]!
    STP     X20, X21, [SP, #-0x10]!
    STP     X22, X23, [SP, #-0x10]!
    STP     X24, X25, [SP, #-0x10]!
    STP     X26, X27, [SP, #-0x10]!
    STP     X28, X29, [SP, #-0x10]!
#if ( configARMV9_PAC_FRAME == 1 )
    PACIA   X30, SP             /* Sign LR with SP as modifier before saving */
#endif
    STP     X30, XZR, [SP, #-0x10]!

    /* Save the SPSR. */
#if defined( GUEST )
    MRS     X3, SPSR_EL1
    MRS     X2, ELR_EL1
#else
    MRS     X3, SPSR_EL3
    /* Save the ELR. */
    MRS     X2, ELR_EL3
#endif

    STP     X2, X3, [SP, #-0x10]!

    /* Save the critical section nesting depth. */
    LDR     X0, ullCriticalNestingConst
    LDR     X3, [X0]

    /* Save the FPU context indicator. */
    LDR     X0, ullPortTaskHasFPUContextConst
    LDR     X2, [X0]

    /* Save the FPU/SVE context, if any. */
    CMP     X2, #0
    B.EQ    1f

#if ( configARMV9_SVE2 == 1 )
    /* SVE2: save FPSR/FPCR first (SP aligned), then Z0-Z31, then P0-P15+FFR */
    MRS     X9, FPSR
    MRS     X10, FPCR
    STP     X9, X10, [SP, #-0x10]!

    ADDVL   SP, SP, #-32
    STR     Z0,  [SP, #0, MUL VL]
    STR     Z1,  [SP, #1, MUL VL]
    STR     Z2,  [SP, #2, MUL VL]
    STR     Z3,  [SP, #3, MUL VL]
    STR     Z4,  [SP, #4, MUL VL]
    STR     Z5,  [SP, #5, MUL VL]
    STR     Z6,  [SP, #6, MUL VL]
    STR     Z7,  [SP, #7, MUL VL]
    STR     Z8,  [SP, #8, MUL VL]
    STR     Z9,  [SP, #9, MUL VL]
    STR     Z10, [SP, #10, MUL VL]
    STR     Z11, [SP, #11, MUL VL]
    STR     Z12, [SP, #12, MUL VL]
    STR     Z13, [SP, #13, MUL VL]
    STR     Z14, [SP, #14, MUL VL]
    STR     Z15, [SP, #15, MUL VL]
    STR     Z16, [SP, #16, MUL VL]
    STR     Z17, [SP, #17, MUL VL]
    STR     Z18, [SP, #18, MUL VL]
    STR     Z19, [SP, #19, MUL VL]
    STR     Z20, [SP, #20, MUL VL]
    STR     Z21, [SP, #21, MUL VL]
    STR     Z22, [SP, #22, MUL VL]
    STR     Z23, [SP, #23, MUL VL]
    STR     Z24, [SP, #24, MUL VL]
    STR     Z25, [SP, #25, MUL VL]
    STR     Z26, [SP, #26, MUL VL]
    STR     Z27, [SP, #27, MUL VL]
    STR     Z28, [SP, #28, MUL VL]
    STR     Z29, [SP, #29, MUL VL]
    STR     Z30, [SP, #30, MUL VL]
    STR     Z31, [SP, #31, MUL VL]

    ADDVL   SP, SP, #-3
    STR     P0,  [SP, #0, MUL VL]
    STR     P1,  [SP, #1, MUL VL]
    STR     P2,  [SP, #2, MUL VL]
    STR     P3,  [SP, #3, MUL VL]
    STR     P4,  [SP, #4, MUL VL]
    STR     P5,  [SP, #5, MUL VL]
    STR     P6,  [SP, #6, MUL VL]
    STR     P7,  [SP, #7, MUL VL]
    STR     P8,  [SP, #8, MUL VL]
    STR     P9,  [SP, #9, MUL VL]
    STR     P10, [SP, #10, MUL VL]
    STR     P11, [SP, #11, MUL VL]
    STR     P12, [SP, #12, MUL VL]
    STR     P13, [SP, #13, MUL VL]
    STR     P14, [SP, #14, MUL VL]
    STR     P15, [SP, #15, MUL VL]
    RDFFR   P0.B
    STR     P0,  [SP, #16, MUL VL]

#else /* configARMV9_SVE2 */
    STP     Q0, Q1, [SP,#-0x20]!
    STP     Q2, Q3, [SP,#-0x20]!
    STP     Q4, Q5, [SP,#-0x20]!
    STP     Q6, Q7, [SP,#-0x20]!
    STP     Q8, Q9, [SP,#-0x20]!
    STP     Q10, Q11, [SP,#-0x20]!
    STP     Q12, Q13, [SP,#-0x20]!
    STP     Q14, Q15, [SP,#-0x20]!
    STP     Q16, Q17, [SP,#-0x20]!
    STP     Q18, Q19, [SP,#-0x20]!
    STP     Q20, Q21, [SP,#-0x20]!
    STP     Q22, Q23, [SP,#-0x20]!
    STP     Q24, Q25, [SP,#-0x20]!
    STP     Q26, Q27, [SP,#-0x20]!
    STP     Q28, Q29, [SP,#-0x20]!
    STP     Q30, Q31, [SP,#-0x20]!
    MRS     X9, FPSR
    MRS     X10, FPCR
    STP     X9, X10, [SP, #-0x10]!
#endif /* configARMV9_SVE2 */

1:

#if ( configARMV9_PAC == 1 )
    /* Save PAC keys. configARMV9_PAC_KEYS controls how many key pairs:
     * 4 = all (APIA+APIB+APDA+APDB), 2 = APIA+APDA, 1 = APIA only. */
    MRS     X9, APIAKeyLo_EL1
    MRS     X10, APIAKeyHi_EL1
    STP     X9, X10, [SP, #-0x10]!
#if ( !defined( configARMV9_PAC_KEYS ) || configARMV9_PAC_KEYS >= 4 )
    MRS     X9, APIBKeyLo_EL1
    MRS     X10, APIBKeyHi_EL1
    STP     X9, X10, [SP, #-0x10]!
#endif
#if ( !defined( configARMV9_PAC_KEYS ) || configARMV9_PAC_KEYS >= 2 )
    MRS     X9, APDAKeyLo_EL1
    MRS     X10, APDAKeyHi_EL1
    STP     X9, X10, [SP, #-0x10]!
#endif
#if ( !defined( configARMV9_PAC_KEYS ) || configARMV9_PAC_KEYS >= 4 )
    MRS     X9, APDBKeyLo_EL1
    MRS     X10, APDBKeyHi_EL1
    STP     X9, X10, [SP, #-0x10]!
#endif
#endif /* configARMV9_PAC */

    /* Store the critical nesting count and FPU context indicator. */
    STP     X2, X3, [SP, #-0x10]!

    LDR     X0, pxCurrentTCBConst
    LDR     X1, [X0]
    MOV     X0, SP   /* Move SP into X0 for saving. */
    STR     X0, [X1]

    /* Switch to use the ELx stack pointer. */
    MSR     SPSEL, #1

    .endm

; /**********************************************************************/

.macro portRESTORE_CONTEXT

    /* Switch to use the EL0 stack pointer. */
    MSR     SPSEL, #0

    /* Set the SP to point to the stack of the task being restored. */
    LDR     X0, pxCurrentTCBConst
    LDR     X1, [X0]
    LDR     X0, [X1]
    MOV     SP, X0

    LDP     X2, X3, [SP], #0x10  /* Critical nesting and FPU context. */

#if ( configARMV9_PAC == 1 )
    /* Restore PAC keys (reverse order of save). */
#if ( !defined( configARMV9_PAC_KEYS ) || configARMV9_PAC_KEYS >= 4 )
    LDP     X9, X10, [SP], #0x10
    MSR     APDBKeyLo_EL1, X9
    MSR     APDBKeyHi_EL1, X10
#endif
#if ( !defined( configARMV9_PAC_KEYS ) || configARMV9_PAC_KEYS >= 2 )
    LDP     X9, X10, [SP], #0x10
    MSR     APDAKeyLo_EL1, X9
    MSR     APDAKeyHi_EL1, X10
#endif
#if ( !defined( configARMV9_PAC_KEYS ) || configARMV9_PAC_KEYS >= 4 )
    LDP     X9, X10, [SP], #0x10
    MSR     APIBKeyLo_EL1, X9
    MSR     APIBKeyHi_EL1, X10
#endif
    LDP     X9, X10, [SP], #0x10
    MSR     APIAKeyLo_EL1, X9
    MSR     APIAKeyHi_EL1, X10
    /* ISB deferred: merged with ISB after ICC_PMR_EL1 write below. */
#endif /* configARMV9_PAC */

    /* Set the PMR register to be correct for the current critical nesting
    depth. */
    LDR     X0, ullCriticalNestingConst /* X0 holds the address of ullCriticalNesting. */
    MOV     X1, #255                    /* X1 holds the unmask value. */
    CMP     X3, #0
    B.EQ    1f
    LDR     X6, ullMaxAPIPriorityMaskConst
    LDR     X1, [X6]                    /* X1 holds the mask value. */
1:
    MSR     s3_0_c4_c6_0, X1            /* Write the mask value to ICCPMR. s3_0_c4_c6_0 is ICC_PMR_EL1. */
    DSB     SY                          /* Required when ICC_CTLR_EL1.PMHE==1 (GIC IHI 0069H §12.1.6). */
    ISB     SY                          /* Synchronizes both PAC key and PMR writes. */
    STR     X3, [X0]                    /* Restore the task's critical nesting count. */

    /* Restore the FPU context indicator. */
    LDR     X0, ullPortTaskHasFPUContextConst
    STR     X2, [X0]

    /* Restore the FPU/SVE context, if any. */
    CMP     X2, #0
    B.EQ    1f

#if ( configARMV9_SVE2 == 1 )
    /* SVE2: restore P0-P15+FFR, then Z0-Z31, then FPSR/FPCR */
    LDR     P0,  [SP, #16, MUL VL]
    WRFFR   P0.B
    LDR     P15, [SP, #15, MUL VL]
    LDR     P14, [SP, #14, MUL VL]
    LDR     P13, [SP, #13, MUL VL]
    LDR     P12, [SP, #12, MUL VL]
    LDR     P11, [SP, #11, MUL VL]
    LDR     P10, [SP, #10, MUL VL]
    LDR     P9,  [SP, #9, MUL VL]
    LDR     P8,  [SP, #8, MUL VL]
    LDR     P7,  [SP, #7, MUL VL]
    LDR     P6,  [SP, #6, MUL VL]
    LDR     P5,  [SP, #5, MUL VL]
    LDR     P4,  [SP, #4, MUL VL]
    LDR     P3,  [SP, #3, MUL VL]
    LDR     P2,  [SP, #2, MUL VL]
    LDR     P1,  [SP, #1, MUL VL]
    LDR     P0,  [SP, #0, MUL VL]
    ADDVL   SP, SP, #3

    LDR     Z31, [SP, #31, MUL VL]
    LDR     Z30, [SP, #30, MUL VL]
    LDR     Z29, [SP, #29, MUL VL]
    LDR     Z28, [SP, #28, MUL VL]
    LDR     Z27, [SP, #27, MUL VL]
    LDR     Z26, [SP, #26, MUL VL]
    LDR     Z25, [SP, #25, MUL VL]
    LDR     Z24, [SP, #24, MUL VL]
    LDR     Z23, [SP, #23, MUL VL]
    LDR     Z22, [SP, #22, MUL VL]
    LDR     Z21, [SP, #21, MUL VL]
    LDR     Z20, [SP, #20, MUL VL]
    LDR     Z19, [SP, #19, MUL VL]
    LDR     Z18, [SP, #18, MUL VL]
    LDR     Z17, [SP, #17, MUL VL]
    LDR     Z16, [SP, #16, MUL VL]
    LDR     Z15, [SP, #15, MUL VL]
    LDR     Z14, [SP, #14, MUL VL]
    LDR     Z13, [SP, #13, MUL VL]
    LDR     Z12, [SP, #12, MUL VL]
    LDR     Z11, [SP, #11, MUL VL]
    LDR     Z10, [SP, #10, MUL VL]
    LDR     Z9,  [SP, #9, MUL VL]
    LDR     Z8,  [SP, #8, MUL VL]
    LDR     Z7,  [SP, #7, MUL VL]
    LDR     Z6,  [SP, #6, MUL VL]
    LDR     Z5,  [SP, #5, MUL VL]
    LDR     Z4,  [SP, #4, MUL VL]
    LDR     Z3,  [SP, #3, MUL VL]
    LDR     Z2,  [SP, #2, MUL VL]
    LDR     Z1,  [SP, #1, MUL VL]
    LDR     Z0,  [SP, #0, MUL VL]
    ADDVL   SP, SP, #31
    ADDVL   SP, SP, #1

    LDP     X9, X10, [SP], #0x10
    MSR     FPSR, X9
    MSR     FPCR, X10

#else /* configARMV9_SVE2 */
    LDP     X9, X10, [SP], #0x10
    LDP     Q30, Q31, [SP], #0x20
    LDP     Q28, Q29, [SP], #0x20
    LDP     Q26, Q27, [SP], #0x20
    LDP     Q24, Q25, [SP], #0x20
    LDP     Q22, Q23, [SP], #0x20
    LDP     Q20, Q21, [SP], #0x20
    LDP     Q18, Q19, [SP], #0x20
    LDP     Q16, Q17, [SP], #0x20
    LDP     Q14, Q15, [SP], #0x20
    LDP     Q12, Q13, [SP], #0x20
    LDP     Q10, Q11, [SP], #0x20
    LDP     Q8, Q9, [SP], #0x20
    LDP     Q6, Q7, [SP], #0x20
    LDP     Q4, Q5, [SP], #0x20
    LDP     Q2, Q3, [SP], #0x20
    LDP     Q0, Q1, [SP], #0x20
    MSR     FPSR, X9
    MSR     FPCR, X10
#endif /* configARMV9_SVE2 */
1:
    LDP     X2, X3, [SP], #0x10  /* SPSR and ELR. */

#if defined( GUEST )
    /* Restore the SPSR. */
    MSR     SPSR_EL1, X3
    /* Restore the ELR. */
    MSR     ELR_EL1, X2
#else
    /* Restore the SPSR. */
    MSR     SPSR_EL3, X3 /*_RB_ Assumes started in EL3. */
    /* Restore the ELR. */
    MSR     ELR_EL3, X2
#endif

    LDP     X30, XZR, [SP], #0x10
#if ( configARMV9_PAC_FRAME == 1 )
    AUTIA   X30, SP             /* Verify LR signature — faults if frame was corrupted */
#endif
    LDP     X28, X29, [SP], #0x10
    LDP     X26, X27, [SP], #0x10
    LDP     X24, X25, [SP], #0x10
    LDP     X22, X23, [SP], #0x10
    LDP     X20, X21, [SP], #0x10
    LDP     X18, X19, [SP], #0x10
    LDP     X16, X17, [SP], #0x10
    LDP     X14, X15, [SP], #0x10
    LDP     X12, X13, [SP], #0x10
    LDP     X10, X11, [SP], #0x10
    LDP     X8, X9, [SP], #0x10
    LDP     X6, X7, [SP], #0x10
    LDP     X4, X5, [SP], #0x10
    LDP     X2, X3, [SP], #0x10
    LDP     X0, X1, [SP], #0x10

    /* Switch to use the ELx stack pointer.  _RB_ Might not be required. */
    MSR     SPSEL, #1

    ERET

    .endm


/******************************************************************************
 * FreeRTOS_SWI_Handler handler is used to perform a context switch.
 *****************************************************************************/
.align 8
.type FreeRTOS_SWI_Handler, %function
FreeRTOS_SWI_Handler:
    bti     j
    /* Save the context of the current task and select a new task to run. */
    portSAVE_CONTEXT
#if defined( GUEST )
    MRS     X0, ESR_EL1
#else
    MRS     X0, ESR_EL3
#endif

    LSR     X1, X0, #26

#if defined( GUEST )
    CMP     X1, #0x15   /* 0x15 = SVC instruction. */
#else
    CMP     X1, #0x17   /* 0x17 = SMC instruction. */
#endif
    B.NE    FreeRTOS_Abort
    BL      vTaskSwitchContext

    portRESTORE_CONTEXT

FreeRTOS_Abort:
    /* Full ESR is in X0, exception class code is in X1. */
    B       .

/******************************************************************************
 * vPortRestoreTaskContext is used to start the scheduler.
 *****************************************************************************/
.align 8
.type vPortRestoreTaskContext, %function
vPortRestoreTaskContext:
    bti     c
.set freertos_vector_base,  _freertos_vector_table

    /* Install the FreeRTOS interrupt handlers. */
    LDR     X1, =freertos_vector_base
#if defined( GUEST )
    MSR     VBAR_EL1, X1
#else
    MSR     VBAR_EL3, X1
#endif
    DSB     SY
    ISB     SY

    /* Start the first task. */
    portRESTORE_CONTEXT


/******************************************************************************
 * FreeRTOS_IRQ_Handler handles IRQ entry and exit.

 * This handler is supposed to be used only for IRQs and never for FIQs. Per ARM
 * GIC documentation [1], Group 0 interrupts are always signaled as FIQs. Since
 * this handler is only for IRQs, We can safely assume Group 1 while accessing
 * Interrupt Acknowledge and End Of Interrupt registers and therefore, use
 * ICC_IAR1_EL1 and ICC_EOIR1_EL1.
 *
 * [1] https://developer.arm.com/documentation/198123/0300/Arm-CoreLink-GIC-fundamentals
 *****************************************************************************/
.align 8
.type FreeRTOS_IRQ_Handler, %function
FreeRTOS_IRQ_Handler:
    bti     j
    /* Save volatile registers. */
    STP     X0, X1, [SP, #-0x10]!
    STP     X2, X3, [SP, #-0x10]!
    STP     X4, X5, [SP, #-0x10]!
    STP     X6, X7, [SP, #-0x10]!
    STP     X8, X9, [SP, #-0x10]!
    STP     X10, X11, [SP, #-0x10]!
    STP     X12, X13, [SP, #-0x10]!
    STP     X14, X15, [SP, #-0x10]!
    STP     X16, X17, [SP, #-0x10]!
    STP     X18, XZR, [SP, #-0x10]!  /* X19 is callee-saved; preserved by BL vApplicationIRQHandler. */
    STP     X29, X30, [SP, #-0x10]!

    /* Save the SPSR and ELR. */
#if defined( GUEST )
    MRS     X3, SPSR_EL1
    MRS     X2, ELR_EL1
#else
    MRS     X3, SPSR_EL3
    MRS     X2, ELR_EL3
#endif
    STP     X2, X3, [SP, #-0x10]!

    /* Increment the interrupt nesting counter. */
    LDR     X5, ullPortInterruptNestingConst
    LDR     X1, [X5]    /* Old nesting count in X1. */
    ADD     X6, X1, #1
    STR     X6, [X5]    /* Address of nesting count variable in X5. */

    /* Maintain the interrupt nesting information across the function call. */
    STP     X1, X5, [SP, #-0x10]!

    /* Read interrupt ID from the interrupt acknowledge register and store it
    in X0 for future parameter and interrupt clearing use. */
    MRS     X0, S3_0_C12_C12_0  /* S3_0_C12_C12_0 is ICC_IAR1_EL1. */

    /* Maintain the interrupt ID value across the function call. */
    STP     X0, X1, [SP, #-0x10]!

    /* Call the C handler. */
    BL vApplicationIRQHandler

    /* Disable interrupts. */
    MSR     DAIFSET, #2
    ISB     SY

    /* Restore the interrupt ID value. */
    LDP     X0, X1, [SP], #0x10

    /* End IRQ processing by writing interrupt ID value to the EOI register. */
    MSR     S3_0_C12_C12_1, X0  /* S3_0_C12_C12_1 is ICC_EOIR1_EL1. */

    /* Restore the critical nesting count. */
    LDP     X1, X5, [SP], #0x10
    STR     X1, [X5]

    /* Has interrupt nesting unwound? */
    CMP     X1, #0
    B.NE    Exit_IRQ_No_Context_Switch

    /* Is a context switch required? */
    LDR     X0, ullPortYieldRequiredConst
    LDR     X1, [X0]
    CMP     X1, #0
    B.EQ    Exit_IRQ_No_Context_Switch

    /* Reset ullPortYieldRequired to 0. */
    MOV     X2, #0
    STR     X2, [X0]

    /* Restore volatile registers. */
    LDP     X4, X5, [SP], #0x10  /* SPSR and ELR. */
#if defined( GUEST )
    MSR     SPSR_EL1, X5
    MSR     ELR_EL1, X4
#else
    MSR     SPSR_EL3, X5 /*_RB_ Assumes started in EL3. */
    MSR     ELR_EL3, X4
#endif
    /* DSB+ISB removed: portSAVE_CONTEXT follows, then ERET in portRESTORE_CONTEXT. */

    LDP     X29, X30, [SP], #0x10
    LDP     X18, XZR, [SP], #0x10
    LDP     X16, X17, [SP], #0x10
    LDP     X14, X15, [SP], #0x10
    LDP     X12, X13, [SP], #0x10
    LDP     X10, X11, [SP], #0x10
    LDP     X8, X9, [SP], #0x10
    LDP     X6, X7, [SP], #0x10
    LDP     X4, X5, [SP], #0x10
    LDP     X2, X3, [SP], #0x10
    LDP     X0, X1, [SP], #0x10

    /* Save the context of the current task and select a new task to run. */
    portSAVE_CONTEXT
    BL vTaskSwitchContext
    portRESTORE_CONTEXT

Exit_IRQ_No_Context_Switch:
    /* Restore volatile registers. */
    LDP     X4, X5, [SP], #0x10  /* SPSR and ELR. */
#if defined( GUEST )
    MSR     SPSR_EL1, X5
    MSR     ELR_EL1, X4
#else
    MSR     SPSR_EL3, X5 /*_RB_ Assumes started in EL3. */
    MSR     ELR_EL3, X4
#endif
    /* DSB+ISB removed: ERET is a context synchronization event (ARM ARM §D1.10.2). */

    LDP     X29, X30, [SP], #0x10
    LDP     X18, XZR, [SP], #0x10
    LDP     X16, X17, [SP], #0x10
    LDP     X14, X15, [SP], #0x10
    LDP     X12, X13, [SP], #0x10
    LDP     X10, X11, [SP], #0x10
    LDP     X8, X9, [SP], #0x10
    LDP     X6, X7, [SP], #0x10
    LDP     X4, X5, [SP], #0x10
    LDP     X2, X3, [SP], #0x10
    LDP     X0, X1, [SP], #0x10

    ERET

/******************************************************************************
 * If the application provides an implementation of vApplicationIRQHandler(),
 * then it will get called directly without saving the FPU registers on
 * interrupt entry, and this weak implementation of
 * vApplicationIRQHandler() will not get called.
 *
 * If the application provides its own implementation of
 * vApplicationFPUSafeIRQHandler() then this implementation of
 * vApplicationIRQHandler() will be called, save the FPU registers, and then
 * call vApplicationFPUSafeIRQHandler().
 *
 * Therefore, if the application writer wants FPU registers to be saved on
 * interrupt entry their IRQ handler must be called
 * vApplicationFPUSafeIRQHandler(), and if the application writer does not want
 * FPU registers to be saved on interrupt entry their IRQ handler must be
 * called vApplicationIRQHandler().
 *****************************************************************************/

.align 8
.weak vApplicationIRQHandler
.type vApplicationIRQHandler, %function
vApplicationIRQHandler:
    bti     c
    /* Save LR and FP on the stack */
    STP     X29, X30, [SP, #-0x10]!

    /* Save FPU/SVE volatile registers around C handler call */
#if ( configARMV9_SVE2 == 1 )
    MRS     X9, FPSR
    MRS     X10, FPCR
    STP     X9, X10, [SP, #-0x10]!
    ADDVL   SP, SP, #-32
    STR     Z0,  [SP, #0, MUL VL]
    STR     Z1,  [SP, #1, MUL VL]
    STR     Z2,  [SP, #2, MUL VL]
    STR     Z3,  [SP, #3, MUL VL]
    STR     Z4,  [SP, #4, MUL VL]
    STR     Z5,  [SP, #5, MUL VL]
    STR     Z6,  [SP, #6, MUL VL]
    STR     Z7,  [SP, #7, MUL VL]
    STR     Z8,  [SP, #8, MUL VL]
    STR     Z9,  [SP, #9, MUL VL]
    STR     Z10, [SP, #10, MUL VL]
    STR     Z11, [SP, #11, MUL VL]
    STR     Z12, [SP, #12, MUL VL]
    STR     Z13, [SP, #13, MUL VL]
    STR     Z14, [SP, #14, MUL VL]
    STR     Z15, [SP, #15, MUL VL]
    STR     Z16, [SP, #16, MUL VL]
    STR     Z17, [SP, #17, MUL VL]
    STR     Z18, [SP, #18, MUL VL]
    STR     Z19, [SP, #19, MUL VL]
    STR     Z20, [SP, #20, MUL VL]
    STR     Z21, [SP, #21, MUL VL]
    STR     Z22, [SP, #22, MUL VL]
    STR     Z23, [SP, #23, MUL VL]
    STR     Z24, [SP, #24, MUL VL]
    STR     Z25, [SP, #25, MUL VL]
    STR     Z26, [SP, #26, MUL VL]
    STR     Z27, [SP, #27, MUL VL]
    STR     Z28, [SP, #28, MUL VL]
    STR     Z29, [SP, #29, MUL VL]
    STR     Z30, [SP, #30, MUL VL]
    STR     Z31, [SP, #31, MUL VL]
    ADDVL   SP, SP, #-3
    STR     P0,  [SP, #0, MUL VL]
    STR     P1,  [SP, #1, MUL VL]
    STR     P2,  [SP, #2, MUL VL]
    STR     P3,  [SP, #3, MUL VL]
    STR     P4,  [SP, #4, MUL VL]
    STR     P5,  [SP, #5, MUL VL]
    STR     P6,  [SP, #6, MUL VL]
    STR     P7,  [SP, #7, MUL VL]
    STR     P8,  [SP, #8, MUL VL]
    STR     P9,  [SP, #9, MUL VL]
    STR     P10, [SP, #10, MUL VL]
    STR     P11, [SP, #11, MUL VL]
    STR     P12, [SP, #12, MUL VL]
    STR     P13, [SP, #13, MUL VL]
    STR     P14, [SP, #14, MUL VL]
    STR     P15, [SP, #15, MUL VL]
#else
    STP     Q0, Q1, [SP,#-0x20]!
    STP     Q2, Q3, [SP,#-0x20]!
    STP     Q4, Q5, [SP,#-0x20]!
    STP     Q6, Q7, [SP,#-0x20]!
    STP     Q8, Q9, [SP,#-0x20]!
    STP     Q10, Q11, [SP,#-0x20]!
    STP     Q12, Q13, [SP,#-0x20]!
    STP     Q14, Q15, [SP,#-0x20]!
    STP     Q16, Q17, [SP,#-0x20]!
    STP     Q18, Q19, [SP,#-0x20]!
    STP     Q20, Q21, [SP,#-0x20]!
    STP     Q22, Q23, [SP,#-0x20]!
    STP     Q24, Q25, [SP,#-0x20]!
    STP     Q26, Q27, [SP,#-0x20]!
    STP     Q28, Q29, [SP,#-0x20]!
    STP     Q30, Q31, [SP,#-0x20]!
    MRS     X9, FPSR
    MRS     X10, FPCR
    STP     X9, X10, [SP, #-0x10]!
#endif /* configARMV9_SVE2 */

    /* Call the C handler. */
    BL vApplicationFPUSafeIRQHandler

    /* Restore FPU/SVE volatile registers */
#if ( configARMV9_SVE2 == 1 )
    LDR     P15, [SP, #15, MUL VL]
    LDR     P14, [SP, #14, MUL VL]
    LDR     P13, [SP, #13, MUL VL]
    LDR     P12, [SP, #12, MUL VL]
    LDR     P11, [SP, #11, MUL VL]
    LDR     P10, [SP, #10, MUL VL]
    LDR     P9,  [SP, #9, MUL VL]
    LDR     P8,  [SP, #8, MUL VL]
    LDR     P7,  [SP, #7, MUL VL]
    LDR     P6,  [SP, #6, MUL VL]
    LDR     P5,  [SP, #5, MUL VL]
    LDR     P4,  [SP, #4, MUL VL]
    LDR     P3,  [SP, #3, MUL VL]
    LDR     P2,  [SP, #2, MUL VL]
    LDR     P1,  [SP, #1, MUL VL]
    LDR     P0,  [SP, #0, MUL VL]
    ADDVL   SP, SP, #3
    LDR     Z31, [SP, #31, MUL VL]
    LDR     Z30, [SP, #30, MUL VL]
    LDR     Z29, [SP, #29, MUL VL]
    LDR     Z28, [SP, #28, MUL VL]
    LDR     Z27, [SP, #27, MUL VL]
    LDR     Z26, [SP, #26, MUL VL]
    LDR     Z25, [SP, #25, MUL VL]
    LDR     Z24, [SP, #24, MUL VL]
    LDR     Z23, [SP, #23, MUL VL]
    LDR     Z22, [SP, #22, MUL VL]
    LDR     Z21, [SP, #21, MUL VL]
    LDR     Z20, [SP, #20, MUL VL]
    LDR     Z19, [SP, #19, MUL VL]
    LDR     Z18, [SP, #18, MUL VL]
    LDR     Z17, [SP, #17, MUL VL]
    LDR     Z16, [SP, #16, MUL VL]
    LDR     Z15, [SP, #15, MUL VL]
    LDR     Z14, [SP, #14, MUL VL]
    LDR     Z13, [SP, #13, MUL VL]
    LDR     Z12, [SP, #12, MUL VL]
    LDR     Z11, [SP, #11, MUL VL]
    LDR     Z10, [SP, #10, MUL VL]
    LDR     Z9,  [SP, #9, MUL VL]
    LDR     Z8,  [SP, #8, MUL VL]
    LDR     Z7,  [SP, #7, MUL VL]
    LDR     Z6,  [SP, #6, MUL VL]
    LDR     Z5,  [SP, #5, MUL VL]
    LDR     Z4,  [SP, #4, MUL VL]
    LDR     Z3,  [SP, #3, MUL VL]
    LDR     Z2,  [SP, #2, MUL VL]
    LDR     Z1,  [SP, #1, MUL VL]
    LDR     Z0,  [SP, #0, MUL VL]
    ADDVL   SP, SP, #31
    ADDVL   SP, SP, #1
    LDP     X9, X10, [SP], #0x10
    MSR     FPSR, X9
    MSR     FPCR, X10
#else
    LDP     X9, X10, [SP], #0x10
    LDP     Q30, Q31, [SP], #0x20
    LDP     Q28, Q29, [SP], #0x20
    LDP     Q26, Q27, [SP], #0x20
    LDP     Q24, Q25, [SP], #0x20
    LDP     Q22, Q23, [SP], #0x20
    LDP     Q20, Q21, [SP], #0x20
    LDP     Q18, Q19, [SP], #0x20
    LDP     Q16, Q17, [SP], #0x20
    LDP     Q14, Q15, [SP], #0x20
    LDP     Q12, Q13, [SP], #0x20
    LDP     Q10, Q11, [SP], #0x20
    LDP     Q8, Q9, [SP], #0x20
    LDP     Q6, Q7, [SP], #0x20
    LDP     Q4, Q5, [SP], #0x20
    LDP     Q2, Q3, [SP], #0x20
    LDP     Q0, Q1, [SP], #0x20
    MSR     FPSR, X9
    MSR     FPCR, X10
#endif /* configARMV9_SVE2 */

    /* Restore FP and LR */
    LDP     X29, X30, [SP], #0x10
    RET

.align 8
pxCurrentTCBConst: .dword pxCurrentTCB
ullCriticalNestingConst: .dword ullCriticalNesting
ullPortTaskHasFPUContextConst: .dword ullPortTaskHasFPUContext

ullMaxAPIPriorityMaskConst: .dword ullMaxAPIPriorityMask
ullPortInterruptNestingConst: .dword ullPortInterruptNesting
ullPortYieldRequiredConst: .dword ullPortYieldRequired

.end
