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

    .arm
    .syntax unified
    /* All code in the portASM.S file is intended to be run from a prvileged
     * operating mode, as such mark the entire file as privileged_functions */
    .section privileged_functions

#define FREERTOS_ASSEMBLY
    #include "portmacro_asm.h"
    #include "mpu_syscall_numbers.h"
#undef FREERTOS_ASSEMBLY

    /* External FreeRTOS-Kernel Variables */
    .extern pxCurrentTCB
    .extern uxSystemCallImplementations
    .extern ulPortInterruptNesting
    .extern ulPortYieldRequired

    /* External Linker script variables that are needed by the port */
    .extern __privileged_functions_start__
    .extern __privileged_functions_end__
    .extern __privileged_stacks_start__
    .extern __privileged_stacks_end__
    .extern __syscalls_flash_length__
    .extern __syscalls_flash_start__
    .extern __syscalls_flash_end__

    /* External FreeRTOS-Kernel Functions */
    .extern vAssertCalled
    .extern vTaskSwitchContext
    .extern vApplicationIRQHandler

/* ----------------------------------------------------------------------------------- */
/* Save the register context of a FreeRTOS Task. */
.macro portSAVE_CONTEXT
    DSB
    ISB
    /* Push R0 and the Link Register (LR) for scratch register space */
    PUSH    { R0, LR }
    /* Load the pointer to the current task's Task Control Block (TCB) */
    LDR     LR, =pxCurrentTCB
    /* Load the actual TCB into LR */
    LDR     LR, [LR]
    /* Set LR to pxTopOfStack, the address of where to save the task context */
    LDR     LR, [LR]

    /* Load the address of ulCriticalNesting */
    LDR     R0, =ulCriticalNesting
    /* Load the value of ulCriticalNesting into R0 */
    LDR     R0, [R0]
    /* Push the value of ulCriticalNesting into the context, auto-increment the
     * LR by using the ! operator. */
    STM     LR!, { R0 }

#if ( portENABLE_FPU == 1 )
    /* Save the floating point context */
    /* Copy the Floating Point Status and Control Register (FPSRC) */
    FMRX    R0, FPSCR
    /* Push the value of FPSCR onto the stack */
    STM     LR!, { R0 }
    /* Push the 32 Floating Point Registers (FPRs) onto the stack */
    VSTM    LR!, { D0-D15 }
#endif /* ( portENABLE_FPU == 1 ) */

    /* Restore the saved register */
    POP     { R0 }
    /* Save the General Purpose Registers (GPRs). Also save the pre-exception
     * Stack Pointer (SP) and LR. The ^ operator causes this instruction to store
     * the mode selected in the Saved Program Status Register (SPSR) */
    STM     LR, { R0-R14 }^
    /* Not allowed to auto-increment with ! when using banked registers */
    ADD     LR, LR, #portREGISTER_LENGTH
    /* Pop the pushed LR, which is the pre-exception Program Counter (PC) */
    POP     { R0 }
    /* Copy the pre-exception Current Program Status Register (CPSR), which,
     * is banked as the SPSR and save it as part of the task context */
    MRS     R1, SPSR
    /* Store the pre-exception CPSR and PC */
    STM     LR!, { R0-R1 }

.endm

/* ----------------------------------------------------------------------------------- */
/* Restore the register context of a FreeRTOS Task. */
.macro portRESTORE_CONTEXT
    /* Load the pointer to the current task's Task Control Block (TCB) */
    LDR     LR, =pxCurrentTCB
    /* Load the actual TCB into LR */
    LDR     LR, [LR]
    /* Set R1 to the second member of the TCB struct, xMPUSettings */
    ADD     R1, LR, #0x4
    /* Set LR to pxTopOfStack, the address to restore the task context from */
    LDR     LR, [LR]
    /* Load the first per-task MPU region into R5 */
    MOV     R5, #portFIRST_CONFIGURABLE_REGION
    /* When creating a loop label in a macro it has to be a numeric label.
     * For (R5 = portFIRST_CONFIGURABLE_REGION ; R5 <= portNUM_CONFIGURABLE_REGIONS ; R5++ ) */
    123:
        /* Load values of struct MPU_REGION_REGISTERS into R2-R4 */
        LDMIA   R1!, { R2-R4 }
        /* Load the values set in xMPU_REGION_REGISTERS
         * R2 Will hold ulRegionSize
         * R3 will hold ulRegionAttribute
         * R4 will hold ulRegionBaseAddress
         * R5 will hold the MPU Region number */

        /* Select the MPU Region using R5 */
        MCR     p15, #0, R5, c6, c2, #0
        /* Set the MPU Region Base Address using ulRegionBaseAddress */
        MCR     p15, #0, R4, c6, c1, #0
        /* Set the MPU Region Access Attributes using ulRegionAttribute */
        MCR     p15, #0, R3, c6, c1, #4
        /* Set the MPU Region Size, and if the region is enabled using ulRegionSize */
        MCR     p15, #0, R2, c6, c1, #2
        /* R5++ */
        ADD     R5, R5, #1
        /* R5 <= R6 */
        CMP     R5, #portNUM_CONFIGURABLE_REGIONS
        /* R5 <= R6, loop again */
        BLE     123b
    /* R5 > portSTACK_REGION, all MPU regions have been restored */

    /* Load the address of the ulCriticalNesting variable into R1 */
    LDR     R1, =ulCriticalNesting
    /* Pop the previously saved value of ulCriticalNesting from ulContext */
    LDM     LR!, { R2 }
    /* Store the value of ulCriticalNesting into address of ulCriticalNesting */
    STR     R2, [R1]

#if ( portENABLE_FPU == 1 )
    /* Restore Floating Point Context: Restore previous FPSCR from ulContext */
    LDM     LR!, { R1 }
    /* Move the saved FPSCR value into the FPSCR */
    VMSR    FPSCR, R1
    /* Restore the Floating Point Registers */
    VLDM   LR!, { D0-D15 }
#endif /* portENABLE_FPU*/

    /* Load the value of the CPSR into R0, needed to set the SP and the LR */
    LDR     R0, [LR, +#(portREGISTER_LENGTH + 4UL)]
    /* Move the CPSR the into our SPSR */
    MSR     SPSR_cxsf, R0
    /* Restore the saved Stack Pointer and Link Register into User Mode */
    LDM     LR, { R0-R14 }^
    /* Not allowed to auto-increment with ! when using banked registers */
    ADD     LR, LR, #portREGISTER_LENGTH
    /* Load the PC to return from the exception */
    RFE     LR

.endm

/* ----------------------------------------------------------------------------------- */
/* Load the context of the first task, starting the FreeRTOS-Scheduler */
.align 4
.global vPortStartFirstTask
.type vPortStartFirstTask, %function
vPortStartFirstTask:
    /** This function is called from Supervisor Mode to start the FreeRTOS-Kernel.
     * This is done by restoring the context of the first task.
     * Restoring the context of a task will allow interrupts.
     * This allows the FreeRTOS Scheduler Tick to start, and therefore
     * starts the FreeRTOS-Kernel.
     */
    /* Swap to SVC Mode for context restore */
    CPS #SVC_MODE
    /* Load the context of first task, starting the FreeRTOS-Scheduler */
    portRESTORE_CONTEXT

/* ----------------------------------------------------------------------------------- */
/* Handler for Supervisor Calls (SVCs) when using this FreeRTOS Port */

/* Upon entering here the LR, or R14, will hold the address of the following
 * instruction. This then checks that instruction for the SVC # raised.
 * Checks:
 *    1. SVC is raised from the system call section (i.e. application is
 *       not raising SVC directly).
 *    2. pxMpuSettings->xSystemCallStackInfo.pulTaskStack must be NULL as
 *       it is non-NULL only during the execution of a system call (i.e.
 *       between system call enter and exit).
 *    3. System call is not for a kernel API disabled by the configuration
 *       in FreeRTOSConfig.h.
 *    4. We do not need to check that ucSystemCallNumber is within range
 *       because the assembly SVC handler checks that before calling
 *       this function.
 */
.align 4
.global FreeRTOS_SVC_Handler
.type FreeRTOS_SVC_Handler, %function
FreeRTOS_SVC_Handler:
    /* Push R11-R12 for scratch space */
    PUSH    { R11-R12 }

    /* -------------------- Caller Flash Location Check -------------------- */

    /* The address of the caller will be in the Link Register (LR), it will
     * be the caller's Program Counter (PC). Check this address to ensure the
     * Supervisor call (SVC) was raised from inside the FreRTOS-Kernel. */

    /* Get the starting address for FreeRTOS System Calls */
    LDR     R12, =__syscalls_flash_start__
    /* Subtract the start point from the Program Counter of the caller */
    SUB     R11, LR, R12
    /* Now check if it is less than the length of the section */
    LDR     R12, =__syscalls_flash_length__
    /* Check if an SVC was raised after the end of FreeRTOS System Calls */
    CMP     R11, R12
    /* If the SVC was raised from outside FreeRTOS System Calls exit now */
    BGE     SVC_Handler_Exit

    /* ----------------------- Get Caller SVC Number ----------------------- */

    /* The SPSR will be the CPSR of the calling task, store it in R11 */
    MRS     R11, SPSR
    /* Thumb Mode is bit 5 of the CPSR, AND for comparison */
    ANDS    R11, R11, #0x20
    /* In Thumb Mode, the instruction 0x2 before holds the SVC numebr */
    LDRHNE  R11, [LR, #-0x2]
    /* Not in Thumb Mode, the instruction 0x4 before holds the SVC numebr */
    LDRHEQ  R11, [LR, #-0x4]

    /* ---------------------------- SVC Routing ---------------------------- */

    /* Determine if the SVC number is below #NUM_SYSTEM_CALLS */
    CMP     R11, #NUM_SYSTEM_CALLS
    /* If it is go to the entry point for FreeRTOS System Calls */
    BLT     svcSystemCallEnter

    /* Check if the caller is leaving a FreeRTOS System Call */
    CMP     R11, #portSVC_SYSTEM_CALL_EXIT
    BEQ     svcSystemCallExit

    /* Check if the caller is requesting to yield */
    CMP     R11, #portSVC_YIELD
    BEQ     svcPortYield

    /* If one of the above jumps wasn't taken, go straight to the exit */
SVC_Handler_Exit:
    /** Restore the saved R11 and R12, then return to the caller */
    POP     { R11-R12 }
    /* This instruction loads the SPSR into the CPSR, performing the mode swap */
    MOVS    PC, LR

/* Perform a task swap */
svcPortYield:
    /* Restore the previously saved R11, R12 */
    POP     { R11-R12 }
    /* Save the context of the current task and select a new task to run. */
    portSAVE_CONTEXT
    /* Select a new task to swap to */
    BL      vTaskSwitchContext
    /* Restore the context of the task selected to execute. */
    portRESTORE_CONTEXT

/* Reset task stack and link register after a FreeRTOS System Call */
svcSystemCallExit:
    /* Restore the Task Stack Pointer and Link Register */
    /* Load the address of pxCurrentTCB into R11 */
    LDR     R11, =pxCurrentTCB
    /* Load pxCurrentTCB into R11 */
    LDR     R11, [R11]
    /* Set R11 to be the location of xSystemCallStackInfo inside the TCB */
    ADD     R11, R11, #portSYSTEM_CALL_INFO_OFFSET
    /* Restore the user mode Stack Pointer and Link Register */
    LDMIB   R11, { R13-R14 }^
    /* Zero out R12 so we can set ulTaskStackPointer back to NULL */
    AND     R12, R12, #0x0
    /* Set pulTaskStackPointer to be 0x0 */
    STR     R12, [R11, #0x4]
    /* Set pulLinkRegisterAtSystemCallEntry to be 0x0 */
    STR     R12, [R11, #0x8]
    /* Load the ulTaskFlag so we can determine if we're going to lower privilege */
    LDM     R11, { R12 }
    /* Check if the task is privileged */
    CMP     R12, #portTASK_IS_PRIVILEGED_FLAG
    /* If the task is privileged we can leave now */
    BEQ     SVC_Handler_Exit
    /* Otherwise, we need to set the SPSR back to USER mode */
    MRS     R12, SPSR
    /* Clear the last 4 bits, which are the MODE bits */
    BIC     R12, R12, #0x0F
    /* Move the new value into the SPSR */
    MSR     SPSR_cxsf, R12
    /* Jump back */
    B   SVC_Handler_Exit

/* Save task's SP and LR, swap to ulSystemCallStack Buffer, raise privilege */
svcSystemCallEnter:
    /* Load the base address of the uxSystemCallImplementations[] table into R14 */
    LDR     R14, =uxSystemCallImplementations

    /** Shift the value of R11, the SVC number, left by two to get the jump offset
     * Add this offset to R14, which holds the jump table address. This is the address
     * of the SVC that the relevant function is trying to complete.
     * Now when the Link Register is loaded as the Program Counter at the end of this
     * handler, the caller will immediately execute the requested function */
    LDR     R14, [R14, R11, lsl #2]

    /* Load the address of pxCurrentTCB into R11 */
    LDR     R11, =pxCurrentTCB
    /* Load pxCurrentTCB into R11 */
    LDR     R11, [R11]
    /* Set R11 to be the location of xSystemCallStackInfo inside the TCB */
    ADD     R11, R11, #portSYSTEM_CALL_INFO_OFFSET
    /* Get the value in the TCB for ulTaskStackPointer */
    LDMIB   R11!, { R12 }
    /* Ensure ulTaskStackPointer is null, signifying initial entry */
    TEQ     R12, #0x0
    /* Make sure that the function pointer loaded is not NULL */
    CMPEQ   R14, #0x0

    /* Hard code the ascii value of the function name and line number to call
     * assert if the ulTaskStackPointer is not null. */
    MOVWEQ  R0, #0x706F
    MOVTEQ  R0, #0x7274
    MOVEQ   R1, #342
    BEQ     vAssertCalled

    /* Store the task's SP and LR to xSYSTEM_CALL_STACK_INFO */
    STM     R11, { R13-R14 }^
    /* Not allowed to auto-increment with ! when using banked registers */
    ADD     R11, R11, 0x8
    /* Load pulSystemCallStackPointer and pulSystemCallLinkRegister now */
    LDM     R11, { R13-R14 }^

    /* Swap the SPSR to SYS_MODE for the System Call. Move SPSR into R12 */
    MRS     R12, SPSR
    /* Set the MODE bits to SYS_MODE */
    ORR     R12, R12, #SYS_MODE
    /* Assign the new value to SPSR */
    MSR     SPSR_cxsf, R12
    /* Leave through the SVC Exit */
    B       SVC_Handler_Exit

/* ----------------------------------------------------------------------------------- */
/* Disable IRQs and increment the critical nesting count */
.align 4
.global vPortEnterCritical
.type vPortEnterCritical, %function
vPortEnterCritical:
    /* Disable IRQs */
    CPSID    I
    /* Save scratch registers */
    PUSH    { R0-R1 }
    /* Load address of current critical nesting count */
    LDR     R0, =ulCriticalNesting
    /* Load value of current critical nesting count */
    LDR     R1, [R0]
    /* Add one to ulCriticalNesting */
    ADD     R1, R1, #1
    /* Store the modified ulCriticalNesting back into RAM */
    STR     R1, [R0]
    /* Restore pushed registers */
    POP     { R0-R1 }
    /* Return to caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
/* Disable IRQs */
.align 4
.global vPortDisableInterrupts
.type vPortDisableInterrupts, %function
vPortDisableInterrupts:
    /* Disable IRQs */
    CPSID    I
    /* Return to caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
/* Enable IRQs and decrement the critical nesting count */
.align 4
.global vPortExitCritical
.type vPortExitCritical, %function
vPortExitCritical:
    /* Store two scratch registers and LR for IRQ Mode re-entry */
    PUSH    { R0-R1, LR }
    /* Load address of current critical nesting count */
    LDR     R0, =ulCriticalNesting
    /* Load value of current critical nesting count */
    LDR     R1, [R0]
    /* Check if the count is 0 */
    CMP      R1, #0
    /* If ulCriticalNesting is greater than 0, Subtract 1 from it */
    SUBGT    R1, R1, #1
    /* Store the modified ulCriticalNesting back into RAM */
    STRGT    R1, [R0]
    /* Enable IRQs */
    CPSIE   I
    /* Restore Pushed registers */
    POP     { R0-R1, LR }
    /* Return to caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
/* Enable IRQs */
.align 4
.global vPortEnableInterrupts
.type vPortEnableInterrupts, %function
vPortEnableInterrupts:
    /* Push LR to account for re-entry in IRQ Mode */
    PUSH    { LR }
    /* Enable IRQs */
    CPSIE   I
    /* Restore previous LR */
    POP     { LR }
    /* Return to caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
/** Set MPU Registers using provided values
 * Function: void vMPUSetRegion
 * Inputs:     uint32_t ulRegionNumber
 * Inputs:     uint32_t ulBaseAddress
 * Inputs:     uint32_t ulRegionSize
 * Inputs:     uint32_t ulRegionPermissions
*/
.align 4
.global vMPUSetRegion
.type vMPUSetRegion, %function
vMPUSetRegion:
    /* Only 15 possible regions, drop all other bits */
    AND     R0,  R0, #15
    /* Select the MPU Region selected by ulRegionNumber */
    MCR     p15, #0, R0, c6, c2, #0
    /* Set the Base Address to be ulBaseAddress */
    MCR     p15, #0, R1, c6, c1, #0
    /* Set the Access Attributes to be ulRegionPermissions */
    MCR     p15, #0, R3, c6, c1, #4
    /* Set the Size and Enable bits to be ulRegionSize */
    MCR     p15, #0, R2, c6, c1, #2
    /* Return to caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
/* Set the Enable bit of the MPU Enable Register to 1. */
.align 4
.global vMPUEnable
.type vMPUEnable, %function
vMPUEnable:
    /* Read the current MPU control register into R0 */
    MRC     p15, #0, R0, c1, c0, #0
    /* Set the enable bit to high */
    ORR     R0,  R0, #0x1
    /* Data sync */
    DSB
    /* Write out previous MPU control register with a high enable bit */
    MCR     p15, #0, R0, c1, c0, #0
    /* Instruction sync */
    ISB
    /* Return to caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
/* Set the Enable bit of the MPU Enable Register to 0. */
.align 4
.global vMPUDisable
.type vMPUDisable, %function
vMPUDisable:
    /* Read the MPU enable register values into R0 */
    MRC     p15, #0, R0, c1, c0, #0
    /* Perform a bitwise AND of R0 and NOT #1, i.e. clear bit 1 */
    BIC     R0,  R0, #1
    /* Wait for all pending explicit data accesses to complete */
    DSB
    /* Write out to the MPU Enable Register */
    MCR     p15, #0, R0, c1, c0, #0
    /* Flushes the pipeline and prefetch buffer(s) in the processor. */
    /* Ensures all following instructions are fetched from cache or memory. */
    ISB
    /* Return to caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
/* Enable the MPU Background Region */
.align 4
.global vMPUEnableBackgroundRegion
.type vMPUEnableBackgroundRegion, %function
vMPUEnableBackgroundRegion:
    /* Save value in R0 */
    PUSH    { R0 }
    /* Read CP15 System Control Register into R0 */
    MRC     p15, 0, R0, c1, c0, 0
    /* Set bit 17 so that privileged modes won't trigger unmapped MPU region faults */
    ORR     R0, R0, #0x20000
    /* Write the value back out */
    MCR     p15, 0, R0, c1, c0, 0
    /* Restore the used register */
    POP     { R0 }
    /* Return to the caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
/* Disable the MPU Background Region */
.align 4
.global vMPUDisableBackgroundRegion
.type vMPUDisableBackgroundRegion, %function
vMPUDisableBackgroundRegion:
    /* Save value in R0 */
    PUSH    { R0 }
    /* Read CP15 System Control Register into R0 */
    MRC     p15, 0, R0, c1, c0, 0
    /* Clear bit 17 so that privileged modes won't trigger unmapped MPU region faults */
    BIC     R0, R0, #0x20000
    /* Write the value back out */
    MCR     p15, 0, R0, c1, c0, 0
    /* Restore the used register */
    POP     { R0 }
    /* Return to the caller */
    BX      LR

/* ----------------------------------------------------------------------------------- */
.align 4
.global FreeRTOS_IRQ_Handler
.type FreeRTOS_IRQ_Handler, %function
FreeRTOS_IRQ_Handler:
    /* Disable IRQs */
    CPSID   I
    /* Return to the interrupted instruction. */
    SUB     LR, LR, #4
    /* Save the return state to the IRQ stack */
    SRSDB     SP!, #IRQ_MODE
    /* Push used registers. */
    PUSH    { R0-R3, R12 }

    /* Load &ulPortInterruptNesting into R0 */
    LDR     R0, =ulPortInterruptNesting
    /* Load the value of ulPortInterruptNesting into R1 */
    LDR     R1, [R0]
    /* R2 = ulPortInterruptNesting + 1 */
    ADD     R2, R1, #1
    /* Store the value of ulPortInterruptNesting++ back into the variable */
    STR     R2, [R0]

    /* Save Calling Registers */
    PUSH    { R0-R3, LR }
    /* Call the User provided IRQ handler */
    BL      vApplicationIRQHandler

    /* Disable IRQs incase vApplicationIRQHandler enabled them for re-entry */
    CPSID    I
    /* Perform a data and instruction buffer flush */
    DSB
    ISB

    /* Restore the previous registers */
    POP     { R0-R3, LR }
    /* R0 holds the address of ulPortInterruptNesting, R1 holds original value */
    STR     R1, [R0]
    /* Check if ulPortInterruptNesting is 0 */
    CMP     R1, #0
    /* If ulPortInterruptNesting is not zero, unwind the nested interrupt */
    BNE     exit_without_switch

    /* ulPortInterruptNesting is zero, check if ulPortYieldRequired is set */
    LDR     R1, =ulPortYieldRequired
    /* Load the value of ulPortYieldRequired */
    LDR     R0, [R1]
    /* Check if the value of ulPortYieldRequired is zero */
    CMP     R0, #0
    /* If it is non-zero select a new task to run */
    BNE     switch_before_exit

exit_without_switch:
    /* No context switch. Restore used registers, LR_irq and SPSR before returning. */
    POP     { R0-R3, R12 }
    /* Return from exception, load pre-exception PC and CPSR */
    RFE     SP!

switch_before_exit:
    /* A context swtich is to be performed. Clear the context switch pending flag. */
    MOV     R0, #0
    /* Set ulPortYieldRequired back to zero */
    STR     R0, [R1]

    /* Restore used registers, LR_irq and SPSR before saving the context */
    POP     { R0-R3, R12 }
    /* Load the pushed SPSR from the stack */
    LDMIB   SP!, { LR }
    /* Move it into the SPSR */
    MSR     SPSR_cxsf, LR
    /* Load the pushed pre-exception Program Counter into LR_irq */
    LDMDB   SP, { LR }
    /* Increment the Stack Pointer an additional 0x4 */
    ADD     SP, SP, 0x4
    /* Save the current task's context */
    portSAVE_CONTEXT

    /* Call the function that selects the new task to execute. */
    BLX     vTaskSwitchContext

    /* Restore the context of the selected task, which will start executing. */
    portRESTORE_CONTEXT

.end
