/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "FreeRTOSConfig.h"

.section .interrupt_handlers, "ax"

    /* Variables and functions. */
    .extern ullMaxAPIPriorityMask
#if configNUMBER_OF_CORES == 1
	.extern pxCurrentTCB
    .extern ullCriticalNesting
    .extern ullPortInterruptNesting
#else
    .extern pxCurrentTCBs
    .extern ullCriticalNestings
    .extern ullPortInterruptNestings
#endif
    .extern vTaskSwitchContext
    .extern vApplicationIRQHandler
    .extern ullPortTaskHasFPUContext
    .extern ullPortYieldRequired
    .extern ullICCEOIR
    .extern ullICCIAR
    .extern _freertos_vector_table

    .global FreeRTOS_IRQ_Handler
    .global FreeRTOS_SWI_Handler
    .global vPortRestoreTaskContext

.macro saveallgpregisters
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
    STP     X30, XZR, [SP, #-0x10]!
.endm

.macro restoreallgpregisters
    LDP     X30, XZR, [SP], #0x10
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
.endm

.macro savefuncontextgpregs
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
    STP     X29, X30, [SP, #-0x10]!
.endm

.macro restorefuncontextgpregs
    LDP     X29, X30, [SP], #0x10
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
.endm

.macro savefloatregisters
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
.endm

.macro restorefloatregisters
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
.endm

.macro portSAVE_CONTEXT
    /* Switch to use the EL0 stack pointer. */
    MSR     SPSEL, #0
    /* Save the entire context. */
    saveallgpregisters

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
    LDR     X0, ullCriticalNestingsConst
#if configNUMBER_OF_CORES > 1
    /* Calculate the correct index for ullCriticalNestings array based on core ID. */
    MRS     X1, MPIDR_EL1          // Read the Multiprocessor Affinity Register
    AND     X1, X1, #0xff          // Extract Aff0 which contains the core ID

    /* Calculate offset to the correct critical nesting value based on the core ID */
    LSL     X1, X1, #3             // Multiply core ID by 8 (size of a pointer on ARM64)

    ADD     X0, X0, X1             // Add to the base of the critical nesting array
#endif
    LDR     X3, [X0]

    /* Save the FPU context indicator. */
    LDR     X0, ullPortTaskHasFPUContextConst
#if configNUMBER_OF_CORES > 1
    ADD     X0, X0, X1             // Add to the base of the FPU array
#endif
    LDR     X2, [X0]

    /* Save the FPU context, if any (32 128-bit registers). */
    CMP     X2, #0
    B.EQ    1f
    savefloatregisters

1:
    /* Store the critical nesting count and FPU context indicator. */
    STP     X2, X3, [SP, #-0x10]!

    LDR     X0, pxCurrentTCBsConst
#if configNUMBER_OF_CORES > 1
    MRS     X1, MPIDR_EL1          // Read the Multiprocessor Affinity Register
    AND     X1, X1, #0xff          // Extract Aff0 which contains the core ID

    /* Calculate offset to the correct TCB pointer based on the core ID */
    LSL     X1, X1, #3             // Multiply core ID by 8 (size of a pointer on ARM64)
    ADD     X0, X0, X1             // Add to the base of the TCB array
#endif

    /* Load the address of the TCB for the current core */
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
    LDR     X0, pxCurrentTCBsConst
#if configNUMBER_OF_CORES > 1
    /* Get the core ID to index the TCB correctly. */
    MRS     X2, MPIDR_EL1             // Read the Multiprocessor Affinity Register
    AND     X2, X2, #0xff             // Extract Aff0 which contains the core ID
    LSL     X2, X2, #3                // Scale the core ID to the size of a pointer (64-bit system)

    ADD     X0, X0, X2                // Add the offset for the current core's TCB pointer
#endif
    LDR     X1, [X0]
    LDR     X0, [X1]
    MOV     SP, X0

    LDP     X2, X3, [SP], #0x10  /* Critical nesting and FPU context. */


    /* Calculate offset for the current core's ullCriticalNesting and load its address. */
    LDR     X0, ullCriticalNestingsConst    /* Load base address of the ullCriticalNesting array */
#if configNUMBER_OF_CORES > 1
    /* Existing code to get core ID and scale to pointer size is reused. */
    MRS     X1, MPIDR_EL1             /* Read Multiprocessor Affinity Register */
    AND     X1, X1, #0xff             /* Extract Aff0, which contains the core ID */
    LSL     X1, X1, #3                /* Scale core ID to the size of a pointer (assuming 64-bit system) */
    ADD     X0, X0, X1                      /* Add offset for the current core's ullCriticalNesting */
    LDR     X0, [X0]                        /* Load the address of the ullCriticalNesting for the current core */
#endif

    MOV     X1, #255                    /* X1 holds the unmask value. */
    LDR     X4, ullICCPMRConst          /* X4 holds the address of the ICCPMR constant. */
    CMP     X3, #0
    LDR     X5, [X4]                    /* X5 holds the address of the ICCPMR register. */
    B.EQ    1f
    LDR     X6, ullMaxAPIPriorityMaskConst
    LDR     X1, [X6]                    /* X1 holds the mask value. */
1:
    STR     W1, [X5]                    /* Write the mask value to ICCPMR. */
    DSB     SY                          /* _RB_Barriers probably not required here. */
    ISB     SY
    STR     X3, [X0]                    /* Restore the task's critical nesting count. */

    LDR     X0, ullPortTaskHasFPUContextConst

#if configNUMBER_OF_CORES > 1
	/* Existing code to get core ID and scale to pointer size is reused. */
    MRS     X1, MPIDR_EL1             /* Read Multiprocessor Affinity Register */
    AND     X1, X1, #0xff             /* Extract Aff0, which contains the core ID */
    LSL     X1, X1, #3                /* Scale core ID to the size of a pointer (assuming 64-bit system) */
    /* Restore the FPU context indicator. */
    ADD     X0, X0, X1             // Add to the base of the FPU array
#endif
    STR     X2, [X0]

    /* Restore the FPU context, if any. */
    CMP     X2, #0
    B.EQ    1f
    restorefloatregisters
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

    restoreallgpregisters

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
    MRS 	x0, mpidr_el1
    AND     x0, x0, 255
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
 *****************************************************************************/
.align 8
.type FreeRTOS_IRQ_Handler, %function
FreeRTOS_IRQ_Handler:
    /* Save volatile registers. */
    savefuncontextgpregs
    savefloatregisters

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
    LDR     X5, ullPortInterruptNestingsConst   /* Load base address of the ullPortYieldRequired array */
#if configNUMBER_OF_CORES > 1
    /* Existing code to get core ID and scale to pointer size is reused. */
    MRS     X2, MPIDR_EL1             /* Read Multiprocessor Affinity Register */
    AND     X2, X2, #0xff             /* Extract Aff0, which contains the core ID */
    LSL     X2, X2, #3                /* Scale core ID to the size of a pointer (assuming 64-bit system) */

    /* Calculate offset for the current core's ullPortYieldRequired and load its address. */
    ADD     X5, X5, X2                      /* Add offset for the current core's ullPortYieldRequired */
#endif
    LDR     X1, [X5]    /* Old nesting count in X1. */
    ADD     X6, X1, #1
    STR     X6, [X5]    /* Address of nesting count variable in X5. */

    /* Maintain the interrupt nesting information across the function call. */
    STP     X1, X5, [SP, #-0x10]!

    /* Read value from the interrupt acknowledge register, which is stored in W0
    for future parameter and interrupt clearing use. */
    LDR     X2, ullICCIARConst
    LDR     X3, [X2]
    LDR     W0, [X3]    /* ICCIAR in W0 as parameter. */

	/* ICCIAR in W0 as parameter. */
    /* Maintain the ICCIAR value across the function call. */
    STP     X0, X1, [SP, #-0x10]!

    /* Call the C handler. */
    BL vApplicationIRQHandler

    /* Disable interrupts. */
    MSR     DAIFSET, #2
    DSB     SY
    ISB     SY

    /* Restore the ICCIAR value. */
    LDP     X0, X1, [SP], #0x10

    /* End IRQ processing by writing ICCIAR to the EOI register. */
    LDR     X4, ullICCEOIRConst
    LDR     X4, [X4]
    STR     W0, [X4]

    /* Restore the critical nesting count. */
    LDP     X1, X5, [SP], #0x10
    STR     X1, [X5]

    /* Has interrupt nesting unwound? */
    CMP     X1, #0
    B.NE    Exit_IRQ_No_Context_Switch

    /* Is a context switch required? */
    LDR     X0, ullPortYieldRequiredConst

#if configNUMBER_OF_CORES > 1
    /* Existing code to get core ID and scale to pointer size is reused. */
    MRS     X2, MPIDR_EL1             /* Read Multiprocessor Affinity Register */
    AND     X2, X2, #0xff             /* Extract Aff0, which contains the core ID */
    LSL     X2, X2, #3                /* Scale core ID to the size of a pointer (assuming 64-bit system) */

    /* Calculate offset for the current core's ullPortYieldRequired and load its address. */
    ADD     X0, X0, X2                      /* Add offset for the current core's ullPortYieldRequired */
#endif
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
    DSB     SY
    ISB     SY

    restorefloatregisters
    restorefuncontextgpregs

    /* Save the context of the current task and select a new task to run. */
    portSAVE_CONTEXT
    MRS 	x0, mpidr_el1
    AND     x0, x0, 255
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
    DSB     SY
    ISB     SY

    restorefloatregisters
    restorefuncontextgpregs

    ERET




.align 8
#if configNUMBER_OF_CORES == 1
	pxCurrentTCBsConst: .dword pxCurrentTCB
	ullCriticalNestingsConst: .dword ullCriticalNesting
	ullPortInterruptNestingsConst: .dword ullPortInterruptNesting
	ullPortYieldRequiredConst: .dword ullPortYieldRequired
	ullPortTaskHasFPUContextConst: .dword ullPortTaskHasFPUContext
#else
	pxCurrentTCBsConst: .dword pxCurrentTCBs
	ullCriticalNestingsConst: .dword ullCriticalNestings
	ullPortInterruptNestingsConst: .dword ullPortInterruptNestings
	ullPortYieldRequiredConst: .dword ullPortYieldRequired
	ullPortTaskHasFPUContextConst: .dword ullPortTaskHasFPUContext
#endif

ullICCPMRConst: .dword ullICCPMR
ullMaxAPIPriorityMaskConst: .dword ullMaxAPIPriorityMask
ullICCIARConst: .dword ullICCIAR
ullICCEOIRConst: .dword ullICCEOIR
vApplicationIRQHandlerConst: .word vApplicationIRQHandler



.end
