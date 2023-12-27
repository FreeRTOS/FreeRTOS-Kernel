/*
 * FreeRTOS Kernel V10.6.0
 * Copyright (C) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
    .extern ulPortInterruptNesting
    .extern ulICCEOIR
    .extern ulPortYieldRequired
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

/******************************************************************************
 * portSAVE_CONTEXT is used to save all the registers, variables, and MPU
 * settings that make up a task's context.
 *****************************************************************************/
.macro portSAVE_CONTEXT
    DSB
    ISB
    /* Move the SVC SP backwards before calling the SRS */
    SRSDB     SP!, #SVC_MODE
    /* Change to Supervisor Mode for the Context Save */
    CPS     #SVC_MODE
    /* Get the saved SPSR that was pushed to the SVC SP */
    LDR     LR, [SP, #0x4]
    /* Move it to our SPSR so we can save the correct SP and LR */
    MSR     SPSR_cxsf, LR
    /* Save the previous operating modes Registers, Stack Pointer, and Link Register */
    STMDB   SP, {R0-R14}^
    /** Can't do a PUSH when using the ^ character, so need to manually move
     * the SP after pushing the registers */
    SUB     SP, SP, #portREGISTER_CONTEXT_LENGTH
#ifdef portENABLE_FPU
    /* Save the floating point context */
    /* Push the 16 floating point registers onto the stack */
    VPUSH   {D0-D15}
    /* Load the FPSCR into R0 */
    FMRX    R0, FPSCR
    /* Push the value of FPSCR onto the stack */
    PUSH   {R0}
#endif /* portENABLE_FPU */
    /* Load the address of ulCriticalNesting */
    LDR     R0, =ulCriticalNesting
    /* Load the value of ulCriticalNesting into R0 */
    LDR     R0, [R0]
    /* Push the value of ulCriticalNesting into the context */
    PUSH    {R0}
    /* Load the address of pxCurrentTCB into R0 */
    LDR     R0, =pxCurrentTCB
    /* Load the TCB into R0 */
    LDR     R0, [R0]
    /* Set pxTopOfStack in the TCB to be the current Stack Pointer. This is
     * where to load the FreeRTOS-Task context from. */
    STR     SP, [R0]
    /* Move the SVC SP forward to the scratch area in ulContext */
    ADD     SP, SP, 0x8
.endm

/******************************************************************************
 * portRESTORE_CONTEXT is used to restore all the registers, variables, and MPU
 * settings that make up a task's context.
 *****************************************************************************/
.macro portRESTORE_CONTEXT
    /* Load the address of the current task TCB */
    LDR     R0, =pxCurrentTCB
    /* Load the TCB into R0 */
    LDR     R0, [R0]
    /* Set R1 to the second member of the TCB struct, xMPUSettings */
    ADD     R1, R0, #0x4
    /* Set our SP to pxTopOfStack, the address of the Task context */
    LDR     SP, [R0]
    /* Load the first per-task MPU region into R5 */
    MOV     R5, #portFIRST_CONFIGURABLE_REGION
    /* Dynamically load the last MPU region */
    MRC     p15, 0, R6, c0, c0, 0x4
    /* Move the number of MPU regions forward */
    LSR     R6, #0x8
    /* Clear other bits, as there can only be 8-16 regions */
    AND     R6, 0x1F
    /* When creating a loop label in a macro it has to be a numeric label. */
123:    /* For (R5 = portFIRST_CONFIGURABLE_REGION ; R5 <= portSTACK_REGION ; R5++ ) */
    /* Load values of struct MPU_REGION_REGISTERS into R1-R3 */
    LDMIA   R1!, {R2-R4}
    /* Load the values set in xMPU_REGION_REGISTERS */
    /* R2 Will hold ulRegionSize */
    /* R3 will hold ulRegionAttribute */
    /* R4 will hold ulRegionBaseAddress */
    /* R5 will hold the MPU Region number  */

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
    CMP     R5, #portSTACK_REGION
    /* R5 <= R6, loop again */
    BLE     123b
    /* R5 > portSTACK_REGION, all MPU regions have been restored */

    /* Restore the critical section nesting depth. */
    /* Load the address of the ulCriticalNesting variable into R1 */
    LDR     R1, =ulCriticalNesting
    /* Pop the previously saved value of ulCriticalNesting from ulContext */
    POP     {R2}
    /* Store the value of ulCriticalNesting into address of ulCriticalNesting */
    STR     R2, [R1]

#ifdef portENABLE_FPU
    /* Restore the Floating Point Context */
    /* Pop the value of FPSCR from ulContext */
    POP   {R1}
    /* Move the saved FPSCR value into the FPSCR */
    VMSR    FPSCR, R1
    /* Restore the Floating Point Registers */
    VPOP   {D0-D15}
#endif /* portENABLE_FPU*/
    /* At this point the SVC stack pointer will be in one of three places:
     * 1. ulContext[51] - This is the bottom of the context inside of the TCB for task saving
     * 1. ulContext[1]  - We reloaded a nested context, the next context to restore is a task context
     * 2. ulSystemCallStackBuffer[?] - Restoring a nested context inside of an exception handler
    */

    /* Restore the register context, first need to load the mode bits */
    /* Set R1 to be past R0-R12 */
    ADD     R1, SP, #portGPR_LENGTH
    /* Get the CPSR from the context, needed to set the SP and the LR */
    LDR     R2, [R1, +#0x0C]
    /* Move the CPSR the into our SPSR */
    MSR     SPSR_cxsf, R2
    /* Load the stored Stack Pointer and Link Register  */
    LDM     R1, {R13-R14}^
    /* Load R0-R12 from the context */
    POP     {R0-R12}
    /* Jump over the already set R13 and R14 */
    ADD       SP, SP, #0x8
    /* Return from the exception, loading the PC and CPSR */
    RFE       SP!

.endm

/******************************************************************************
 * FreeRTOS_Tick_Handler is used to save context, increment the tick count, and
  * then switch tasks if neeeded
 *****************************************************************************/
.align 4
.global FreeRTOS_Tick_Handler
.type FreeRTOS_Tick_Handler, %function
FreeRTOS_Tick_Handler:
    /* Return to the interrupted instruction. */
    SUB     LR, LR, #4
    /* Save the context of the current task. */
    portSAVE_CONTEXT
    /* Enter back into IRQ mode after saving task context */
    CPS     #IRQ_MODE
    /* Clear interrupt flag in RTI. */
    LDR     R0, =configRTI_ADDRESS
    MOV     R1, #1
    STR     R1, [R0]
    /* Increment the tick count, making any adjustments to the blocked lists
    that may be necessary. */
    BL      xTaskIncrementTick
    /* If xTaskIncrementTick returned non-zero then select the next task to execute. */
    CMP     R0, #0
    BLNE    vTaskSwitchContext
    /* Swap to SVC Mode to restore the task context */
    CPS #SVC_MODE
    /* Restore the context of the task selected to execute. */
    portRESTORE_CONTEXT

/*-----------------------------------------------------------*/
/* Yield to another task from within the FreeRTOS API */

.align 4
.global vPortYieldWithinAPI
.type vPortYieldWithinAPI, %function
vPortYieldWithinAPI:
    /* Return to the interrupted instruction. */
    SUB     LR, LR, #4
    /* Save the context of the current task */
    portSAVE_CONTEXT
    /* Swap back to IRQ Mode for selecting the next task */
    CPS     #IRQ_MODE
    /* Clear the Interrupt Flag for vPortYieldWithinAPI */
    MOV     R0, #configSSI_ADDRESS
    LDR     R0, [R0]
    /* Select the next task to execute. */
    BL      vTaskSwitchContext
    /* Swap back to SVC Mode for context restore */
    CPS     #SVC_MODE
    /* Restore the context of the task selected to execute. */
    portRESTORE_CONTEXT

/******************************************************************************
 * vPortStartFirstTask is used to start the scheduler.
 *****************************************************************************/
.align 4
.global vPortStartFirstTask
.type vPortStartFirstTask, %function
vPortStartFirstTask:
    /** This function is called from System Mode to start the FreeRTOS-Kernel.
     * This is done by restoring the context of the first task.
     * Restoring the context of a task will allow interrupts.
     * This allows the FreeRTOS Scheduler Tick to start, and therefore
     * starts the FreeRTOS-Kernel.
     */
    /* Swap to SVC Mode for context restore */
    CPS #SVC_MODE
    /* Restore context of first task, which enables IRQs, starting the sys tick timer */
    portRESTORE_CONTEXT

/******************************************************************************
 * The FreeRTOS SVC Handler is used to handle Supervisor Calls
 *****************************************************************************/
/** Upon entering here the LR, or R14, will hold the address of the
    * following instruction. The instruction can be inspected to determine
    * what SVC # was raised.
    * This handler is ONLY safe when called from the exposed SVC wrapper functions
    * located after this handler in this file.
*/

    /* Checks:
    * 1. SVC is raised from the system call section (i.e. application is
    *    not raising SVC directly).
    * 2. pxMpuSettings->xSystemCallStackInfo.pulTaskStack must be NULL as
    *    it is non-NULL only during the execution of a system call (i.e.
    *    between system call enter and exit).
    * 3. System call is not for a kernel API disabled by the configuration
    *    in FreeRTOSConfig.h.
    * 4. We do not need to check that ucSystemCallNumber is within range
    *    because the assembly SVC handler checks that before calling
    *    this function.
    */

.align 4
.global FreeRTOS_SVC_Handler
.type FreeRTOS_SVC_Handler, %function
FreeRTOS_SVC_Handler:
    /* Push R11 and R12 to the bottom two, pre-resereved, addresses in ulContext */
    STM    R13, {R11, R12}

    /* -------------------- Caller Flash Location Check -------------------- */

    /** The address of the caller will be in the Link Register (LR), it will be
     * the caller's Program Counter (PC). Check this address to ensure the
     * Supervisor call (SVC) was raised from inside the FreRTOS-Kernel. */

    /* Get the starting address for FreeRTOS System Calls */
    LDR     R12, =__syscalls_flash_start__
    /* Subtract the start point from the Program Counter of the caller */
    SUB     R11, LR, R12
    /* Now check if it is less than the length of the section */
    LDR     R12, =__syscalls_flash_length__
    /* Check if an SVC was raised after the end of FreeRTOS System Calls */
    CMP     R11, R12
    /* If the SVC was raised from outside FreeRTOS System Calls exit */
    BGE     SVC_Handler_Exit

    /* ----------------------- Get Caller SVC Number ----------------------- */

svcNumberCheck:
    /* The SPSR will be the CPSR of the calling task, store it in R11 */
    MRS    R11, SPSR
    /* Thumb Mode is bit 5 of the CPSR. And it with the CPSR for comparison check */
    ANDS    R11, R11, #0x20

    /* The SVC instruction will be 0x2 before LR in Thumb Mode, or 0x4 if not */

    /* In Thumb Mode, so get instruction 0x2 before */
    LDRHNE  R11, [LR, #-0x2]
    /* Not in Thumb Mode, so get the instruction 0x4 before */
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
    LDM     SP, {R11, R12}
    /* This instruction loads the SPSR into the CPSR, performing the mode swap */
    MOVS    PC, LR

/*-----------------------------------------------------------*/

/* Save a FreeRTOS-Task's Context, select a new task, and then restore its context */
svcPortYield:
    /* Restore the previously saved R11, R12 */
    LDM     SP, {R11, R12}
    /* Save the context of the current task and select a new task to run. */
    portSAVE_CONTEXT
    /* Run the following function from the IRQ stack */
    CPS #IRQ_MODE
    /* Select a new task to swap to */
    BL vTaskSwitchContext
    /* Swap back to SVC Mode for context restore */
    CPS #SVC_MODE
    /* Restore the context of the task selected to execute. */
    portRESTORE_CONTEXT

/* Swap a task back to using its task stack, and reset its privilege level if needed */
svcSystemCallExit:
    /* Restore the Task Stack Pointer and Link Register */
    /* Load the address of pxCurrentTCB into R11 */
    LDR     R11, =pxCurrentTCB
    /* Load pxCurrentTCB into R11 */
    LDR     R11, [R11]
    /* Set R11 to be the location of xSystemCallStackInfo inside the TCB */
    ADD     R11, R11, #portSYSTEM_CALL_INFO_OFFSET
    /* Restore the user mode Stack Pointer and Link Register */
    LDMIB   R11, {R13-R14}^
    /* Zero out R12 so we can set ulTaskStackPointer back to NULL */
    AND     R12, R12, #0x0
    /* Set pulTaskStackPointer to be 0x0 */
    STR     R12, [R11, #0x4]
    /* Set pulLinkRegisterAtSystemCallEntry to be 0x0 */
    STR     R12, [R11, #0x8]
    /* Load the ulTaskFlag so we can determine if we're going to lower privilege */
    LDM     R11, {R12}
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

/* svcSystemCallEnter */
/* Swap a task to using the ulSystemCallStack Buffer, and set its privilege high */
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
    /*  Make sure that ulTaskStackPointer was null, meaning that this is initial entry */
    TST     R12, #0x0
    /** Hard code the ascii value of the function name and line number to call
     * assert if the ulTaskStackPointer is not null. */
    MOVWNE  R0, #0x706F
    MOVTNE  R0, #0x7274
    MOVNE   R1, #458
    BNE     vAssertCalled

    /* Store the task's SP and LR to xSYSTEM_CALL_STACK_INFO */
    STM     R11, {R13-R14}^
    /* It's a compilation warning to use the ! for writeback, so manually move R11 */
    ADD     R11, R11, 0x8
    /* Load pulSystemCallStackPointer and pulSystemCallLinkRegister now */
    LDM     R11, {R13-R14}^

    /* Swap the SPSR to SYS_MODE for the System Call. Move SPSR into R12 */
    MRS     R12, SPSR
    /* Set the MODE bits to SYS_MODE */
    ORR     R12, R12, #SYS_MODE
    /* Assign the new value to SPSR */
    MSR     SPSR_cxsf, R12
    /* Leave through the SVC Exit */
    B   SVC_Handler_Exit

/*-------------------------------------------------------------------------------*/
/* vPortEnterCritical */
.align 4
.global vPortEnterCritical
.type vPortEnterCritical, %function
vPortEnterCritical:
    /* Disable IRQs */
    CPSID    I
    /* Save scratch registers */
    PUSH    {R0-R1}
    /* Load address of current critical nesting count */
    LDR     R0, =ulCriticalNesting
    /* Load value of current critical nesting count */
    LDR     R1, [R0]
    /* Add one to ulCriticalNesting */
    ADD     R1, R1, #1
    /* Store the modified ulCriticalNesting back into RAM */
    STR     R1, [R0]
    /* Return to caller */
    POP     {R0-R1}
    BX      LR

/*-------------------------------------------------------------------------------*/
/* vPortDisableInterrupts */
.align 4
.global vPortDisableInterrupts
.type vPortDisableInterrupts, %function
vPortDisableInterrupts:
    /* Disable IRQs */
    CPSID    I
    /* Return to caller */
    BX      LR

/*-------------------------------------------------------------------------------*/
/* vPortExitCritical */
.align 4
.global vPortExitCritical
.type vPortExitCritical, %function
vPortExitCritical:
    /* Store two scratch registers */
    PUSH    {R0-R1}
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
    /* Return to caller */
    POP     {R0-R1}
    BX      LR

/*-------------------------------------------------------------------------------*/
/* vPortEnableInterrupts */
.align 4
.global vPortEnableInterrupts
.type vPortEnableInterrupts, %function
vPortEnableInterrupts:
    /* Enable IRQs */
    CPSIE   I
    /* Return to caller */
    BX  LR

/******************************************************************************
 * prvMpuSetRegion is used to set the base address, access attributes,
 * and the size and enable bits of a selected MPU region.
 * void prvMpuSetRegion(unsigned region, unsigned base, unsigned size, unsigned access)
 *****************************************************************************/
.align 4
.global prvMpuSetRegion
.type prvMpuSetRegion, %function
prvMpuSetRegion:
    /* Only 15 possible regions, drop all other bits */
    AND   R0,  R0, #15
    /* Select the MPU Region selected by region */
    MCR   p15, #0, R0, c6, c2, #0
    /* Set the Base Address to be base */
    MCR   p15, #0, R1, c6, c1, #0
    /* Set the Access Attributes to be access */
    MCR   p15, #0, R3, c6, c1, #4
    /* Set the Size and Enable bits to be size */
    MCR   p15, #0, R2, c6, c1, #2
    BX    LR

/******************************************************************************
 * prvMpuEnable is used to set the Enable bit of the MPU Enable Register to 1.
 *****************************************************************************/
.align 4
.global prvMpuEnable
.type prvMpuEnable, %function
prvMpuEnable:
    /* Read the current MPU control register into R0 */
    MRC   p15, #0, R0, c1, c0, #0
    /* Set the enable bit to high */
    ORR   R0,  R0, #0x1
    /* Data sync */
    DSB
    /* Write out previous MPU control register with a high enable bit */
    MCR   p15, #0, R0, c1, c0, #0
    /* Instruction sync */
    ISB
    BX    LR

/******************************************************************************
 * prvMpuDisable is used to set the Enable bit of the MPU Enable Register to 0.
 *****************************************************************************/
.align 4
.global prvMpuDisable
.type prvMpuDisable, %function
prvMpuDisable:
    /* Read the MPU enable register values into R0 */
    MRC   p15, #0, R0, c1, c0, #0
    /* Clear out all bits in R0 except for bit 1 */
    BIC   R0,  R0, #1
    /* Wait for all pending explicit data accesses to complete */
    DSB
    /* Write out to the MPU Enable Register */
    MCR   p15, #0, R0, c1, c0, #0
    /* Flushes the pipeline and prefetch buffer(s) in the processor. */
    /* Ensures all following instructions are fetched from cache or memory. */
    ISB
    BX    LR

.align 4
.global FreeRTOS_IRQ_Handler
.type FreeRTOS_IRQ_Handler, %function
FreeRTOS_IRQ_Handler:
    /* Return to the interrupted instruction. */
    SUB     LR, LR, #4

    /* Save the return state to the IRQ stack */
    SRS     SP!, #IRQ_MODE

    /* Push used registers. */
    PUSH    {R0-R3, R12}

    /* Increment nesting count. R3 holds the address of ulPortInterruptNesting
    for future use. R1 holds the original ulPortInterruptNesting value for
    future use. */
    LDR     R3, =ulPortInterruptNesting
    LDR     R1, [R3]
    ADD     R0, R1, #1
    STR     R0, [R3]

    /* Ensure bit 2 of the stack pointer is clear. R2 holds the bit 2 value for
    future use. */
    MOV     R0, SP
    AND     R2, R0, #4
    SUB     SP, SP, R2

    /* Call the interrupt handler. */
    PUSH    {R0-R3, LR}
    BL      vApplicationIRQHandler

    /* Restore the registers */
    POP     {R0-R3, LR}
    ADD     SP, SP, R2

    CPSID    i
    DSB
    ISB

    /* Write to the EOI register. */
    LDR     R0, =ulICCEOIR
    LDR     R2, [R0]
    STR     R0, [R2]

    /* Restore the old nesting count. */
    STR     R1, [R3]

    /* A context switch is never performed if the nesting count is not 0. */
    CMP     R1, #0
    BNE     exit_without_switch

    /* Did the interrupt request a context switch? R1 holds the address of
    ulPortYieldRequired and R0 the value of ulPortYieldRequired for future use. */
    LDR     R1, =ulPortYieldRequired
    LDR     R0, [R1]
    CMP     R0, #0
    BNE     switch_before_exit

exit_without_switch:
    /* No context switch. Restore used registers, LR_irq and SPSR before returning. */
    POP     {R0-R3, R12}
    CPS     #IRQ_MODE
    POP     {LR}
    MSR     SPSR_cxsf, LR
    POP     {LR}
    MOVS    PC, LR

switch_before_exit:
    /* A context swtich is to be performed. Clear the context switch pending flag. */
    MOV     R0, #0
    STR     R0, [R1]

    /* Restore used registers, LR-irq and SPSR before saving the context
    to the task stack. */
    POP     {R0-R3, R12}
    CPS     #IRQ_MODE
    POP     {LR}
    MSR     SPSR_cxsf, LR
    POP     {LR}
    portSAVE_CONTEXT

    /* Call the function that selects the new task to execute.
    vTaskSwitchContext() if vTaskSwitchContext() uses LDRD or STRD
    instructions, or 8 byte aligned stack allocated data. LR does not need
    saving as a new LR will be loaded by portRESTORE_CONTEXT anyway. */
    LDR     R0, =vTaskSwitchContext
    BLX     R0

    /* Restore the context of, and branch to, the task selected to execute next. */
    portRESTORE_CONTEXT

.end
