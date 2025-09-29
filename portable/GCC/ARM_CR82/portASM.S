/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * Copyright 2025 Arm Limited and/or its affiliates
 * <open-source-office@arm.com>
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

/*
 * This file is tailored for ARM Cortex-R82 with SMP enabled.
 * It includes macros and functions for saving/restoring task context,
 * handling interrupts, and supporting multi-core operations.
 */

#include "FreeRTOSConfig.h"
#include "portmacro.h"

.text

/* Variables and functions. */
   .extern ullMaxAPIPriorityMask
#if ( configNUMBER_OF_CORES == 1 )
       .extern pxCurrentTCB
       .extern ullCriticalNesting
       .extern ullPortInterruptNesting
#else /* #if ( configNUMBER_OF_CORES == 1 ) */
       .extern pxCurrentTCBs
       .extern ullCriticalNestings
       .extern ullPortInterruptNestings
#endif
   .extern vTaskSwitchContext
   .extern vApplicationIRQHandler
   .extern ullPortTaskHasFPUContext
   .extern ullPortYieldRequired
   .extern _freertos_vector_table

   .global FreeRTOS_IRQ_Handler
   .global FreeRTOS_SWI_Handler
   .global vPortRestoreTaskContext


   .macro saveallgpregisters
/* Save all general-purpose registers on stack. */
STP X0, X1, [ SP, # - 0x10 ] !
STP X2, X3, [ SP, # - 0x10 ] !
STP X4, X5, [ SP, # - 0x10 ] !
STP X6, X7, [ SP, # - 0x10 ] !
STP X8, X9, [ SP, # - 0x10 ] !
STP X10, X11, [ SP, # - 0x10 ] !
STP X12, X13, [ SP, # - 0x10 ] !
STP X14, X15, [ SP, # - 0x10 ] !
STP X16, X17, [ SP, # - 0x10 ] !
STP X18, X19, [ SP, # - 0x10 ] !
STP X20, X21, [ SP, # - 0x10 ] !
STP X22, X23, [ SP, # - 0x10 ] !
STP X24, X25, [ SP, # - 0x10 ] !
STP X26, X27, [ SP, # - 0x10 ] !
STP X28, X29, [ SP, # - 0x10 ] !
STR X30, [ SP, # - 0x10 ] !
   .endm

/*-----------------------------------------------------------*/

   .macro restoreallgpregisters
/* Restore all general-purpose registers from stack. */
LDR X30, [ SP ], # 0x10
LDP X28, X29, [ SP ], # 0x10
LDP X26, X27, [ SP ], # 0x10
LDP X24, X25, [ SP ], # 0x10
LDP X22, X23, [ SP ], # 0x10
LDP X20, X21, [ SP ], # 0x10
LDP X18, X19, [ SP ], # 0x10
LDP X16, X17, [ SP ], # 0x10
LDP X14, X15, [ SP ], # 0x10
LDP X12, X13, [ SP ], # 0x10
LDP X10, X11, [ SP ], # 0x10
LDP X8, X9, [ SP ], # 0x10
LDP X6, X7, [ SP ], # 0x10
LDP X4, X5, [ SP ], # 0x10
LDP X2, X3, [ SP ], # 0x10
LDP X0, X1, [ SP ], # 0x10
   .endm

/*-----------------------------------------------------------*/

   .macro savefuncontextgpregs
/* Save function context general-purpose registers. */
STP X0, X1, [ SP, # - 0x10 ] !
STP X2, X3, [ SP, # - 0x10 ] !
STP X4, X5, [ SP, # - 0x10 ] !
STP X6, X7, [ SP, # - 0x10 ] !
STP X8, X9, [ SP, # - 0x10 ] !
STP X10, X11, [ SP, # - 0x10 ] !
STP X12, X13, [ SP, # - 0x10 ] !
STP X14, X15, [ SP, # - 0x10 ] !
STP X16, X17, [ SP, # - 0x10 ] !
STP X18, X29, [ SP, # - 0x10 ] !
STR X30, [ SP, # - 0x10 ] !
   .endm

/*-----------------------------------------------------------*/

   .macro restorefuncontextgpregs
/* Restore function context general-purpose registers. */
LDR X30, [ SP ], # 0x10
LDP X18, X29, [ SP ], # 0x10
LDP X16, X17, [ SP ], # 0x10
LDP X14, X15, [ SP ], # 0x10
LDP X12, X13, [ SP ], # 0x10
LDP X10, X11, [ SP ], # 0x10
LDP X8, X9, [ SP ], # 0x10
LDP X6, X7, [ SP ], # 0x10
LDP X4, X5, [ SP ], # 0x10
LDP X2, X3, [ SP ], # 0x10
LDP X0, X1, [ SP ], # 0x10
   .endm

/*-----------------------------------------------------------*/

   .macro savefloatregisters
/* Save floating-point registers and configuration/status registers. */
STP Q0, Q1, [ SP, # - 0x20 ] !
STP Q2, Q3, [ SP, # - 0x20 ] !
STP Q4, Q5, [ SP, # - 0x20 ] !
STP Q6, Q7, [ SP, # - 0x20 ] !
STP Q8, Q9, [ SP, # - 0x20 ] !
STP Q10, Q11, [ SP, # - 0x20 ] !
STP Q12, Q13, [ SP, # - 0x20 ] !
STP Q14, Q15, [ SP, # - 0x20 ] !
STP Q16, Q17, [ SP, # - 0x20 ] !
STP Q18, Q19, [ SP, # - 0x20 ] !
STP Q20, Q21, [ SP, # - 0x20 ] !
STP Q22, Q23, [ SP, # - 0x20 ] !
STP Q24, Q25, [ SP, # - 0x20 ] !
STP Q26, Q27, [ SP, # - 0x20 ] !
STP Q28, Q29, [ SP, # - 0x20 ] !
STP Q30, Q31, [ SP, # - 0x20 ] !
MRS X9, FPSR
MRS X10, FPCR
STP W9, W10, [ SP, # - 0x10 ] !
   .endm

/*-----------------------------------------------------------*/

   .macro restorefloatregisters
/* Restore floating-point registers and configuration/status registers. */
LDP W9, W10, [ SP ], # 0x10
MSR FPSR, X9
MSR FPCR, X10
LDP Q30, Q31, [ SP ], # 0x20
LDP Q28, Q29, [ SP ], # 0x20
LDP Q26, Q27, [ SP ], # 0x20
LDP Q24, Q25, [ SP ], # 0x20
LDP Q22, Q23, [ SP ], # 0x20
LDP Q20, Q21, [ SP ], # 0x20
LDP Q18, Q19, [ SP ], # 0x20
LDP Q16, Q17, [ SP ], # 0x20
LDP Q14, Q15, [ SP ], # 0x20
LDP Q12, Q13, [ SP ], # 0x20
LDP Q10, Q11, [ SP ], # 0x20
LDP Q8, Q9, [ SP ], # 0x20
LDP Q6, Q7, [ SP ], # 0x20
LDP Q4, Q5, [ SP ], # 0x20
LDP Q2, Q3, [ SP ], # 0x20
LDP Q0, Q1, [ SP ], # 0x20
   .endm

/*-----------------------------------------------------------*/

   .macro portSAVE_CONTEXT
/* Switch to use the EL0 stack pointer. */
MSR SPSEL, # 0
/* Save the entire context. */
saveallgpregisters
/* Save the SPSR and ELR values. */
MRS X3, SPSR_EL1
MRS X2, ELR_EL1

STP X2, X3, [ SP, # - 0x10 ] !

/* Save the critical section nesting depth. */
LDR X0, ullCriticalNestingsConst
#if configNUMBER_OF_CORES > 1
    /* Calculate per-core index using MPIDR_EL1 for SMP support. */
    MRS X1, MPIDR_EL1    /* Read the Multiprocessor Affinity Register. */
    AND X1, X1, # 0xff   /* Extract Aff0 (core ID). */
    LSL X1, X1, # 3      /* Multiply core ID by pointer size (8 bytes). */
    ADD X0, X0, X1       /* Add offset to base address. */
#endif
LDR X3, [ X0 ]

/* Save the FPU context indicator. */
LDR X0, ullPortTaskHasFPUContextConst
#if configNUMBER_OF_CORES > 1
    ADD X0, X0, X1 /* Add to the base of the FPU array. */
#endif
LDR X2, [ X0 ]

/* Save the FPU context, if any (32 128-bit registers). */
CMP X2, # 0
B.EQ    1f   /* FPU context not present, skip saving FPU registers. */
savefloatregisters

1 :
/* Store the critical nesting count and FPU context indicator. */
STP X2, X3, [ SP, # - 0x10 ] !
LDR X0, pxCurrentTCBsConst
#if ( configNUMBER_OF_CORES > 1 )
    MRS X1, MPIDR_EL1    /* Read Multiprocessor Affinity Register .*/
    AND X1, X1, # 0xff   /* Extract core ID. */
    LSL X1, X1, # 3      /* Multiply core ID by pointer size. */
    ADD X0, X0, X1       /* Offset for current core's TCB pointer. */
#endif

LDR X1, [ X0 ]
MOV X0, SP             /* Save current stack pointer. */
STR X0, [ X1 ]

/* Switch to use the ELx stack pointer. */
MSR SPSEL, # 1
   .endm

/*-----------------------------------------------------------*/

.macro portRESTORE_CONTEXT
/* Switch to use the EL0 stack pointer. */
MSR SPSEL, # 0

/* Set the SP to point to the stack of the task being restored. */
LDR X0, pxCurrentTCBsConst
#if configNUMBER_OF_CORES > 1
    /* Get the core ID to index the TCB correctly. */
    MRS X2, MPIDR_EL1  /* Read the Multiprocessor Affinity Register. */
    AND X2, X2, # 0xff /* Extract Aff0 which contains the core ID. */
    LSL X2, X2, # 3    /* Scale the core ID to the size of a pointer (64-bit system). */

    ADD X0, X0, X2     /* Add the offset for the current core's TCB pointer. */
#endif
LDR X1, [ X0 ]
LDR X0, [ X1 ]
MOV SP, X0
LDP X2, X3, [ SP ], # 0x10   /* Retrieve critical nesting and FPU indicator. */
LDR X0, ullCriticalNestingsConst
/* Calculate offset for current core's ullCriticalNesting. */
#if configNUMBER_OF_CORES > 1
/* Existing code to get core ID and scale to pointer size is reused. */
    MRS X1, MPIDR_EL1  /* Read Multiprocessor Affinity Register. */
    AND X1, X1, # 0xff /* Extract Aff0, which contains the core ID. */
    LSL X1, X1, # 3    /* Scale core ID to the size of a pointer (assuming 64-bit system). */
    ADD X0, X0, X1     /* Add offset for the current core's ullCriticalNesting. */
#endif
MOV X1, # 255            /* Default mask. */
CMP X3, # 0
B.EQ    1f
LDR X6, ullMaxAPIPriorityMaskConst
LDR X1, [ X6 ]           /* Use computed mask value. */
1 :
MSR ICC_PMR_EL1, X1      /* Set interrupt mask. */
DSB SY
ISB SY
STR X3, [ X0 ]           /* Restore critical nesting .*/
/* Restore the FPU context indicator. */
LDR X0, ullPortTaskHasFPUContextConst
#if configNUMBER_OF_CORES > 1
/* Existing code to get core ID and scale to pointer size is reused. */
    MRS X1, MPIDR_EL1  /* Read Multiprocessor Affinity Register. */
    AND X1, X1, # 0xff /* Extract Aff0, which contains the core ID. */
    LSL X1, X1, # 3    /* Scale core ID to the size of a pointer (assuming 64-bit system). */
/* Restore the FPU context indicator. */
    ADD X0, X0, X1     /* Add to the base of the FPU array. */
#endif
STR X2, [ X0 ]

/* Restore the FPU context, if any. */
CMP X2, # 0
B.EQ    1f
restorefloatregisters
1 :
LDP X2, X3, [ SP ], # 0x10   /* Restore SPSR and ELR. */
MSR SPSR_EL1, X3
MSR ELR_EL1, X2

restoreallgpregisters
/* Switch to use the ELx stack pointer. */
MSR SPSEL, # 1

ERET
   .endm

/*-----------------------------------------------------------*/

/******************************************************************************
 * FreeRTOS_SWI_Handler handler is used to perform a context switch.
 *****************************************************************************/
   .align 8
   .type FreeRTOS_SWI_Handler, % function
FreeRTOS_SWI_Handler:
/* Save X0-X2 temporarily as they are used in the handler. */
STP X0, X1, [SP, #-0x10]!
STR X2, [SP, #-0x10]!
/* Decide action based on SVC immediate without corrupting any task context. */
MRS X0, ESR_EL1

/* Extract exception class. */
LSR X1, X0, # 26
CMP X1, # 0x15             /* 0x15 = SVC instruction. */
B.NE FreeRTOS_Abort

/* Extract SVC immediate from ISS[15:0]. */
AND X2, X0, # 0xFFFF

/* portSVC_START_FIRST_TASK: start first task on this core without saving any prior context. */
CMP X2, # portSVC_START_FIRST_TASK
B.NE 1f
/* Discard temp-saved X0-X2 before restoring first task. */
ADD SP, SP, # 0x20
B Start_First_Task

1:
/* portSVC_DISABLE_INTERRUPTS: disable IRQs (DAIF.I) without touching task context. */
CMP X2, # portSVC_DISABLE_INTERRUPTS
B.NE 2f
MSR DAIFSET, # 2
LDR X2, [SP], #0x10
LDP X0, X1, [SP], #0x10
DSB SY
ISB SY
ERET

2:
/* portSVC_ENABLE_INTERRUPTS: enable IRQs (DAIF.I clear) without touching task context. */
CMP X2, # portSVC_ENABLE_INTERRUPTS
B.NE 3f
MSR DAIFCLR, # 2
LDR X2, [SP], #0x10
LDP X0, X1, [SP], #0x10
DSB SY
ISB SY
ERET

3:
/* portSVC_GET_CORE_ID: return core ID in X0 (Aff0 of MPIDR_EL1). */
CMP X2, # portSVC_GET_CORE_ID
B.NE 4f
MRS X0, MPIDR_EL1
AND X0, X0, # 0xff
/* Restore X2, then restore X1 while discarding old X0. */
LDR X2, [ SP ], # 0x10
LDP XZR, X1, [ SP ], # 0x10
ERET

4:
/* portSVC_MASK_ALL_INTERRUPTS: set ICC_PMR_EL1 to max API mask and return previous-mask-equal flag in X0. */
CMP X2, # portSVC_MASK_ALL_INTERRUPTS
B.NE 5f
/* Load max API mask from ullMaxAPIPriorityMask. */
LDR X3, ullMaxAPIPriorityMaskConst
LDR X1, [ X3 ]
/* Read current PMR and compare. */
MRS X2, ICC_PMR_EL1
CMP X2, X1
B.EQ 41f
/* Disable IRQs while updating PMR. */
MSR DAIFSET, # 2
DSB SY
ISB SY
/* Write new PMR value. */
MSR ICC_PMR_EL1, X1
DSB SY
ISB SY
/* Re-enable IRQs. */
MSR DAIFCLR, # 2
DSB SY
ISB SY

41:
MOV X0, X2 /* return ICC_PMR_EL1 original value */
/* Restore X2, then restore X1 while discarding old X0. */
LDR X2, [ SP ], # 0x10
LDP XZR, X1, [ SP ], # 0x10
ERET

5:
/* portSVC_UNMASK_ALL_INTERRUPTS: set ICC_PMR_EL1 to portUNMASK_VALUE to unmask all interrupts. */
CMP X2, # portSVC_UNMASK_ALL_INTERRUPTS
B.NE 6f
/* Disable IRQs while updating PMR. */
MSR DAIFSET, # 2
DSB SY
ISB SY
MOV X0, #portUNMASK_VALUE             /* Unmask all interrupts. */
MSR ICC_PMR_EL1, X0
DSB SY
ISB SY
/* Re-enable IRQs. */
MSR DAIFCLR, # 2
DSB SY
ISB SY
LDR X2, [SP], #0x10
LDP X0, X1, [SP], #0x10
ERET

6:
/* portSVC_UNMASK_INTERRUPTS: set ICC_PMR_EL1 to uxNewMaskValue. */
CMP X2, # portSVC_UNMASK_INTERRUPTS
B.NE 7f
/* Disable IRQs while updating PMR. */
MSR DAIFSET, # 2
DSB SY
ISB SY
MOV X0, X1             /* uxNewMaskValue is in X1. */
MSR ICC_PMR_EL1, X0
DSB SY
ISB SY
/* Re-enable IRQs. */
MSR DAIFCLR, # 2
DSB SY
ISB SY
LDR X2, [SP], #0x10
LDP X0, X1, [SP], #0x10
ERET

7:
/* Default (portSVC_YIELD): yield from a running task. Save context first. */
/* Restore X0-X2 to their original values before saving full context. */
LDR X2, [SP], #0x10
LDP X0, X1, [SP], #0x10
portSAVE_CONTEXT
#if configNUMBER_OF_CORES > 1
MRS x0, mpidr_el1
AND x0, x0, 255
#endif
BL vTaskSwitchContext
portRESTORE_CONTEXT

Start_First_Task:
/* Start-first-task path: pick a task and restore it (no prior save). */
portRESTORE_CONTEXT

FreeRTOS_Abort:
/* Full ESR is in X0, exception class code is in X1. */
B       .

/******************************************************************************
 * vPortRestoreTaskContext is used to start the scheduler.
 *****************************************************************************/
   .align 8
   .type vPortRestoreTaskContext, % function
vPortRestoreTaskContext:
.set freertos_vector_base, _freertos_vector_table

/* Install the FreeRTOS interrupt handlers. */
LDR X1, = freertos_vector_base
          MSR VBAR_EL1, X1
DSB SY
ISB SY

/* Start the first task. */
    portRESTORE_CONTEXT


/******************************************************************************
 * FreeRTOS_IRQ_Handler handles IRQ entry and exit.
 *
 * This handler is supposed to be used only for IRQs and never for FIQs. Per ARM
 * GIC documentation [1], Group 0 interrupts are always signaled as FIQs. Since
 * this handler is only for IRQs, We can safely assume Group 1 while accessing
 * Interrupt Acknowledge and End Of Interrupt registers and therefore, use
 * ICC_IAR1_EL1 and ICC_EOIR1_EL1.
 *
 * [1] https://developer.arm.com/documentation/198123/0300/Arm-CoreLink-GIC-fundamentals
 *****************************************************************************/
   .align 8
   .type FreeRTOS_IRQ_Handler, % function
FreeRTOS_IRQ_Handler:
/* Save volatile registers. */
savefuncontextgpregs
savefloatregisters

/* Save the SPSR and ELR. */
MRS X3, SPSR_EL1
MRS X2, ELR_EL1

STP X2, X3, [ SP, # - 0x10 ] !

/* Increment the interrupt nesting counter. */
LDR X5, ullPortInterruptNestingsConst /* Load base address of the ullPortYieldRequired array */
#if configNUMBER_OF_CORES > 1
    /* Existing code to get core ID and scale to pointer size is reused. */
    MRS X2, MPIDR_EL1  /* Read Multiprocessor Affinity Register. */
    AND X2, X2, # 0xff /* Extract Aff0, which contains the core ID. */
    LSL X2, X2, # 3    /* Scale core ID to the size of a pointer (assuming 64-bit system). */

/* Calculate offset for the current core's ullPortYieldRequired and load its address. */
    ADD X5, X5, X2 /* Add offset for the current core's ullPortYieldRequired. */
#endif
LDR X1, [ X5 ]     /* Old nesting count in X1. */
ADD X6, X1, # 1
STR X6, [ X5 ]     /* Address of nesting count variable in X5. */

/* Maintain the interrupt nesting information across the function call. */
STP X1, X5, [ SP, # - 0x10 ] !

/* Read interrupt ID from the interrupt acknowledge register and store it
 * in X0 for future parameter and interrupt clearing use. */
MRS X0, ICC_IAR1_EL1

/* Maintain the interrupt ID value across the function call. */
STP X0, X1, [ SP, # - 0x10 ] !

/* Call the C handler. */
BL vApplicationIRQHandler

/* Disable interrupts. */
MSR DAIFSET, # 2
DSB SY
ISB SY

/* Restore the interrupt ID value. */
LDP X0, X1, [ SP ], # 0x10


/* End IRQ processing by writing interrupt ID value to the EOI register. */
MSR ICC_EOIR1_EL1, X0

/* Restore the critical nesting count. */
LDP X1, X5, [ SP ], # 0x10
STR X1, [ X5 ]

/* Has interrupt nesting unwound? */
CMP X1, # 0
B.NE Exit_IRQ_No_Context_Switch

/* Is a context switch required? */
LDR X0, ullPortYieldRequiredConst
#if configNUMBER_OF_CORES > 1
/* Existing code to get core ID and scale to pointer size is reused. */
    MRS X2, MPIDR_EL1  /* Read Multiprocessor Affinity Register. */
    AND X2, X2, # 0xff /* Extract Aff0, which contains the core ID. */
    LSL X2, X2, # 3    /* Scale core ID to the size of a pointer (assuming 64-bit system). */

/* Calculate offset for the current core's ullPortYieldRequired and load its address. */
    ADD X0, X0, X2 /* Add offset for the current core's ullPortYieldRequired. */
#endif
LDR X1, [ X0 ]
CMP X1, # 0
B.EQ Exit_IRQ_No_Context_Switch

/* Reset ullPortYieldRequired to 0. */
MOV X2, # 0
STR X2, [ X0 ]

/* Restore volatile registers. */
LDP X4, X5, [ SP ], # 0x10 /* SPSR and ELR. */

MSR SPSR_EL1, X5
MSR ELR_EL1, X4
DSB SY
ISB SY

restorefloatregisters
restorefuncontextgpregs

/* Save the context of the current task and select a new task to run. */
portSAVE_CONTEXT
#if configNUMBER_OF_CORES > 1
    MRS x0, mpidr_el1
    AND x0, x0, 255
#endif
BL vTaskSwitchContext
portRESTORE_CONTEXT

Exit_IRQ_No_Context_Switch:
/* Restore volatile registers. */
LDP X4, X5, [ SP ], # 0x10 /* SPSR and ELR. */

MSR SPSR_EL1, X5
MSR ELR_EL1, X4
DSB SY
ISB SY

restorefloatregisters
restorefuncontextgpregs

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
   .type vApplicationIRQHandler, % function
vApplicationIRQHandler:
/* Save LR and FP on the stack. */
STP X29, X30, [ SP, # - 0x10 ] !

/* Save FPU registers (32 128-bits + 2 64-bits configuration and status registers). */
savefloatregisters

/* Call the C handler. */
BL vApplicationFPUSafeIRQHandler

/* Restore FPU registers. */
restorefloatregisters

/* Restore FP and LR. */
LDP X29, X30, [ SP ], # 0x10
RET

   .align 8
#if ( configNUMBER_OF_CORES == 1 )
pxCurrentTCBsConst:.dword pxCurrentTCB
ullCriticalNestingsConst:.dword ullCriticalNesting
ullPortInterruptNestingsConst:.dword ullPortInterruptNesting
ullPortYieldRequiredConst:.dword ullPortYieldRequired
ullPortTaskHasFPUContextConst:.dword ullPortTaskHasFPUContext
#else
pxCurrentTCBsConst:.dword pxCurrentTCBs
ullCriticalNestingsConst:.dword ullCriticalNestings
ullPortInterruptNestingsConst:.dword ullPortInterruptNestings
ullPortYieldRequiredConst:.dword ullPortYieldRequired
ullPortTaskHasFPUContextConst:.dword ullPortTaskHasFPUContext
#endif /* if ( configNUMBER_OF_CORES == 1 ) */
ullMaxAPIPriorityMaskConst:.dword ullMaxAPIPriorityMask
vApplicationIRQHandlerConst:.word vApplicationIRQHandler
   .end
