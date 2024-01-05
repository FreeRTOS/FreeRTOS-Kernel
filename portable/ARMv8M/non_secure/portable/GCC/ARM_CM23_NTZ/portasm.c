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

/* Standard includes. */
#include <stdint.h>

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE ensures that PRIVILEGED_FUNCTION
 * is defined correctly and privileged functions are placed in correct sections. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* Portasm includes. */
#include "portasm.h"

/* System call numbers includes. */
#include "mpu_syscall_numbers.h"

/* MPU_WRAPPERS_INCLUDED_FROM_API_FILE is needed to be defined only for the
 * header files. */
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#if ( configENABLE_FPU == 1 )
    #error Cortex-M23 does not have a Floating Point Unit (FPU) and therefore configENABLE_FPU must be set to 0.
#endif

#if ( configENABLE_MPU == 1 )

    void vRestoreContextOfFirstTask( void ) /* __attribute__ (( naked )) PRIVILEGED_FUNCTION */
    {
        __asm volatile
        (
            " .syntax unified                                 \n"
            "                                                 \n"
            " program_mpu_first_task:                         \n"
            "    ldr r3, pxCurrentTCBConst2                   \n" /* Read the location of pxCurrentTCB i.e. &( pxCurrentTCB ). */
            "    ldr r0, [r3]                                 \n" /* r0 = pxCurrentTCB.*/
            "                                                 \n"
            "    dmb                                          \n" /* Complete outstanding transfers before disabling MPU. */
            "    ldr r1, xMPUCTRLConst2                       \n" /* r1 = 0xe000ed94 [Location of MPU_CTRL]. */
            "    ldr r2, [r1]                                 \n" /* Read the value of MPU_CTRL. */
            "    movs r3, #1                                  \n" /* r3 = 1. */
            "    bics r2, r3                                  \n" /* r2 = r2 & ~r3 i.e. Clear the bit 0 in r2. */
            "    str r2, [r1]                                 \n" /* Disable MPU. */
            "                                                 \n"
            "    adds r0, #4                                  \n" /* r0 = r0 + 4. r0 now points to MAIR0 in TCB. */
            "    ldr r1, [r0]                                 \n" /* r1 = *r0 i.e. r1 = MAIR0. */
            "    ldr r2, xMAIR0Const2                         \n" /* r2 = 0xe000edc0 [Location of MAIR0]. */
            "    str r1, [r2]                                 \n" /* Program MAIR0. */
            "                                                 \n"
            "    adds r0, #4                                  \n" /* r0 = r0 + 4. r0 now points to first RBAR in TCB. */
            "    ldr r1, xRNRConst2                           \n" /* r1 = 0xe000ed98 [Location of RNR]. */
            "                                                 \n"
            "    movs r3, #4                                  \n" /* r3 = 4. */
            "    str r3, [r1]                                 \n" /* Program RNR = 4. */
            "    ldmia r0!, {r4-r5}                           \n" /* Read first set of RBAR/RLAR registers from TCB. */
            "    ldr r2, xRBARConst2                          \n" /* r2 = 0xe000ed9c [Location of RBAR]. */
            "    stmia r2!, {r4-r5}                           \n" /* Write first set of RBAR/RLAR registers. */
            "    movs r3, #5                                  \n" /* r3 = 5. */
            "    str r3, [r1]                                 \n" /* Program RNR = 5. */
            "    ldmia r0!, {r4-r5}                           \n" /* Read second set of RBAR/RLAR registers from TCB. */
            "    ldr r2, xRBARConst2                          \n" /* r2 = 0xe000ed9c [Location of RBAR]. */
            "    stmia r2!, {r4-r5}                           \n" /* Write second set of RBAR/RLAR registers. */
            "    movs r3, #6                                  \n" /* r3 = 6. */
            "    str r3, [r1]                                 \n" /* Program RNR = 6. */
            "    ldmia r0!, {r4-r5}                           \n" /* Read third set of RBAR/RLAR registers from TCB. */
            "    ldr r2, xRBARConst2                          \n" /* r2 = 0xe000ed9c [Location of RBAR]. */
            "    stmia r2!, {r4-r5}                           \n" /* Write third set of RBAR/RLAR registers. */
            "    movs r3, #7                                  \n" /* r3 = 6. */
            "    str r3, [r1]                                 \n" /* Program RNR = 7. */
            "    ldmia r0!, {r4-r5}                           \n" /* Read fourth set of RBAR/RLAR registers from TCB. */
            "    ldr r2, xRBARConst2                          \n" /* r2 = 0xe000ed9c [Location of RBAR]. */
            "    stmia r2!, {r4-r5}                           \n" /* Write fourth set of RBAR/RLAR registers. */
            "                                                 \n"
            "    ldr r1, xMPUCTRLConst2                       \n" /* r1 = 0xe000ed94 [Location of MPU_CTRL]. */
            "    ldr r2, [r1]                                 \n" /* Read the value of MPU_CTRL. */
            "    movs r3, #1                                  \n" /* r3 = 1. */
            "    orrs r2, r3                                  \n" /* r2 = r2 | r3 i.e. Set the bit 0 in r2. */
            "    str r2, [r1]                                 \n" /* Enable MPU. */
            "    dsb                                          \n" /* Force memory writes before continuing. */
            "                                                 \n"
            " restore_context_first_task:                     \n"
            "    ldr r2, pxCurrentTCBConst2                   \n" /* Read the location of pxCurrentTCB i.e. &( pxCurrentTCB ). */
            "    ldr r0, [r2]                                 \n" /* r0 = pxCurrentTCB.*/
            "    ldr r1, [r0]                                 \n" /* r1 = Location of saved context in TCB. */
            "                                                 \n"
            " restore_special_regs_first_task:                \n"
            "    subs r1, #16                                 \n"
            "    ldmia r1!, {r2-r5}                           \n" /* r2 = original PSP, r3 = PSPLIM, r4 = CONTROL, r5 = LR. */
            "    subs r1, #16                                 \n"
            "    msr psp, r2                                  \n"
            #if ( configRUN_FREERTOS_SECURE_ONLY == 1 )
                "    msr psplim, r3                           \n"
            #endif
            "    msr control, r4                              \n"
            "    mov lr, r5                                   \n"
            "                                                 \n"
            " restore_general_regs_first_task:                \n"
            "    subs r1, #32                                 \n"
            "    ldmia r1!, {r4-r7}                           \n" /* r4-r7 contain half of the hardware saved context. */
            "    stmia r2!, {r4-r7}                           \n" /* Copy half of the the hardware saved context on the task stack. */
            "    ldmia r1!, {r4-r7}                           \n" /* r4-r7 contain rest half of the hardware saved context. */
            "    stmia r2!, {r4-r7}                           \n" /* Copy rest half of the the hardware saved context on the task stack. */
            "    subs r1, #48                                 \n"
            "    ldmia r1!, {r4-r7}                           \n" /* Restore r8-r11. */
            "    mov r8, r4                                   \n" /* r8 = r4. */
            "    mov r9, r5                                   \n" /* r9 = r5. */
            "    mov r10, r6                                  \n" /* r10 = r6. */
            "    mov r11, r7                                  \n" /* r11 = r7. */
            "    subs r1, #32                                 \n"
            "    ldmia r1!, {r4-r7}                           \n" /* Restore r4-r7. */
            "    subs r1, #16                                 \n"
            "                                                 \n"
            " restore_context_done_first_task:                \n"
            "    str r1, [r0]                                 \n" /* Save the location where the context should be saved next as the first member of TCB. */
            "    bx lr                                        \n"
            "                                                 \n"
            " .align 4                                        \n"
            " pxCurrentTCBConst2: .word pxCurrentTCB          \n"
            " xMPUCTRLConst2: .word 0xe000ed94                \n"
            " xMAIR0Const2: .word 0xe000edc0                  \n"
            " xRNRConst2: .word 0xe000ed98                    \n"
            " xRBARConst2: .word 0xe000ed9c                   \n"
        );
    }

#else /* configENABLE_MPU */

    void vRestoreContextOfFirstTask( void ) /* __attribute__ (( naked )) PRIVILEGED_FUNCTION */
    {
        __asm volatile
        (
            "   .syntax unified                                 \n"
            "                                                   \n"
            "   ldr  r2, pxCurrentTCBConst2                     \n" /* Read the location of pxCurrentTCB i.e. &( pxCurrentTCB ). */
            "   ldr  r1, [r2]                                   \n" /* Read pxCurrentTCB. */
            "   ldr  r0, [r1]                                   \n" /* Read top of stack from TCB - The first item in pxCurrentTCB is the task top of stack. */
            "                                                   \n"
            "   ldm  r0!, {r1-r2}                               \n" /* Read from stack - r1 = PSPLIM and r2 = EXC_RETURN. */
            #if ( configRUN_FREERTOS_SECURE_ONLY == 1 )
                "   msr  psplim, r1                             \n" /* Set this task's PSPLIM value. */
            #endif
            "   movs r1, #2                                     \n" /* r1 = 2. */
            "   msr  CONTROL, r1                                \n" /* Switch to use PSP in the thread mode. */
            "   adds r0, #32                                    \n" /* Discard everything up to r0. */
            "   msr  psp, r0                                    \n" /* This is now the new top of stack to use in the task. */
            "   isb                                             \n"
            "   bx   r2                                         \n" /* Finally, branch to EXC_RETURN. */
            "                                                   \n"
            "   .align 4                                        \n"
            "pxCurrentTCBConst2: .word pxCurrentTCB             \n"
        );
    }

#endif /* configENABLE_MPU */
/*-----------------------------------------------------------*/

BaseType_t xIsPrivileged( void ) /* __attribute__ (( naked )) */
{
    __asm volatile
    (
        "   .syntax unified                                 \n"
        "                                                   \n"
        "   mrs r0, control                                 \n" /* r0 = CONTROL. */
        "   movs r1, #1                                     \n" /* r1 = 1. */
        "   tst r0, r1                                      \n" /* Perform r0 & r1 (bitwise AND) and update the conditions flag. */
        "   beq running_privileged                          \n" /* If the result of previous AND operation was 0, branch. */
        "   movs r0, #0                                     \n" /* CONTROL[0]!=0. Return false to indicate that the processor is not privileged. */
        "   bx lr                                           \n" /* Return. */
        " running_privileged:                               \n"
        "   movs r0, #1                                     \n" /* CONTROL[0]==0. Return true to indicate that the processor is privileged. */
        "   bx lr                                           \n" /* Return. */
        "                                                   \n"
        "   .align 4                                        \n"
        ::: "r0", "r1", "memory"
    );
}
/*-----------------------------------------------------------*/

void vRaisePrivilege( void ) /* __attribute__ (( naked )) PRIVILEGED_FUNCTION */
{
    __asm volatile
    (
        "   .syntax unified                                 \n"
        "                                                   \n"
        "   mrs  r0, control                                \n" /* Read the CONTROL register. */
        "   movs r1, #1                                     \n" /* r1 = 1. */
        "   bics r0, r1                                     \n" /* Clear the bit 0. */
        "   msr  control, r0                                \n" /* Write back the new CONTROL value. */
        "   bx lr                                           \n" /* Return to the caller. */
        ::: "r0", "r1", "memory"
    );
}
/*-----------------------------------------------------------*/

void vResetPrivilege( void ) /* __attribute__ (( naked )) */
{
    __asm volatile
    (
        "   .syntax unified                                 \n"
        "                                                   \n"
        "   mrs r0, control                                 \n" /* r0 = CONTROL. */
        "   movs r1, #1                                     \n" /* r1 = 1. */
        "   orrs r0, r1                                     \n" /* r0 = r0 | r1. */
        "   msr control, r0                                 \n" /* CONTROL = r0. */
        "   bx lr                                           \n" /* Return to the caller. */
        ::: "r0", "r1", "memory"
    );
}
/*-----------------------------------------------------------*/

void vStartFirstTask( void ) /* __attribute__ (( naked )) PRIVILEGED_FUNCTION */
{
    __asm volatile
    (
        "   .syntax unified                                 \n"
        "                                                   \n"
        "   ldr r0, xVTORConst                              \n" /* Use the NVIC offset register to locate the stack. */
        "   ldr r0, [r0]                                    \n" /* Read the VTOR register which gives the address of vector table. */
        "   ldr r0, [r0]                                    \n" /* The first entry in vector table is stack pointer. */
        "   msr msp, r0                                     \n" /* Set the MSP back to the start of the stack. */
        "   cpsie i                                         \n" /* Globally enable interrupts. */
        "   dsb                                             \n"
        "   isb                                             \n"
        "   svc %0                                          \n" /* System call to start the first task. */
        "   nop                                             \n"
        "                                                   \n"
        "   .align 4                                        \n"
        "xVTORConst: .word 0xe000ed08                       \n"
        ::"i" ( portSVC_START_SCHEDULER ) : "memory"
    );
}
/*-----------------------------------------------------------*/

uint32_t ulSetInterruptMask( void ) /* __attribute__(( naked )) PRIVILEGED_FUNCTION */
{
    __asm volatile
    (
        "   .syntax unified                                 \n"
        "                                                   \n"
        "   mrs r0, PRIMASK                                 \n"
        "   cpsid i                                         \n"
        "   bx lr                                           \n"
        ::: "memory"
    );
}
/*-----------------------------------------------------------*/

void vClearInterruptMask( __attribute__( ( unused ) ) uint32_t ulMask ) /* __attribute__(( naked )) PRIVILEGED_FUNCTION */
{
    __asm volatile
    (
        "   .syntax unified                                 \n"
        "                                                   \n"
        "   msr PRIMASK, r0                                 \n"
        "   bx lr                                           \n"
        ::: "memory"
    );
}
/*-----------------------------------------------------------*/

#if ( configENABLE_MPU == 1 )

    void PendSV_Handler( void ) /* __attribute__ (( naked )) PRIVILEGED_FUNCTION */
    {
        __asm volatile
        (
            " .syntax unified                                 \n"
            "                                                 \n"
            " ldr r2, pxCurrentTCBConst                       \n" /* Read the location of pxCurrentTCB i.e. &( pxCurrentTCB ). */
            " ldr r0, [r2]                                    \n" /* r0 = pxCurrentTCB. */
            " ldr r1, [r0]                                    \n" /* r1 = Location in TCB where the context should be saved. */
            " mrs r2, psp                                     \n" /* r2 = PSP. */
            "                                                 \n"
            " save_general_regs:                              \n"
            "    stmia r1!, {r4-r7}                           \n" /* Store r4-r7. */
            "    mov r4, r8                                   \n" /* r4 = r8. */
            "    mov r5, r9                                   \n" /* r5 = r9. */
            "    mov r6, r10                                  \n" /* r6 = r10. */
            "    mov r7, r11                                  \n" /* r7 = r11. */
            "    stmia r1!, {r4-r7}                           \n" /* Store r8-r11. */
            "    ldmia r2!, {r4-r7}                           \n" /* Copy half of the  hardware saved context into r4-r7. */
            "    stmia r1!, {r4-r7}                           \n" /* Store the hardware saved context. */
            "    ldmia r2!, {r4-r7}                           \n" /* Copy rest half of the  hardware saved context into r4-r7. */
            "    stmia r1!, {r4-r7}                           \n" /* Store the hardware saved context. */
            "                                                 \n"
            " save_special_regs:                              \n"
            "    mrs r2, psp                                  \n" /* r2 = PSP. */
            #if ( configRUN_FREERTOS_SECURE_ONLY == 1 )
                "    mrs r3, psplim                           \n" /* r3 = PSPLIM. */
            #else
                "    movs r3, #0                              \n" /* r3 = 0. 0 is stored in the PSPLIM slot. */
            #endif
            "    mrs r4, control                              \n" /* r4 = CONTROL. */
            "    mov r5, lr                                   \n" /* r5 = LR. */
            "    stmia r1!, {r2-r5}                           \n" /* Store original PSP (after hardware has saved context), PSPLIM, CONTROL and LR. */
            "    str r1, [r0]                                 \n" /* Save the location from where the context should be restored as the first member of TCB. */
            "                                                 \n"
            " select_next_task:                               \n"
            "    cpsid i                                      \n"
            "    bl vTaskSwitchContext                        \n"
            "    cpsie i                                      \n"
            "                                                 \n"
            " program_mpu:                                    \n"
            "    ldr r3, pxCurrentTCBConst                    \n" /* Read the location of pxCurrentTCB i.e. &( pxCurrentTCB ). */
            "    ldr r0, [r3]                                 \n" /* r0 = pxCurrentTCB.*/
            "                                                 \n"
            "    dmb                                          \n" /* Complete outstanding transfers before disabling MPU. */
            "    ldr r1, xMPUCTRLConst                        \n" /* r1 = 0xe000ed94 [Location of MPU_CTRL]. */
            "    ldr r2, [r1]                                 \n" /* Read the value of MPU_CTRL. */
            "    movs r3, #1                                  \n" /* r3 = 1. */
            "    bics r2, r3                                  \n" /* r2 = r2 & ~r3 i.e. Clear the bit 0 in r2. */
            "    str r2, [r1]                                 \n" /* Disable MPU. */
            "                                                 \n"
            "    adds r0, #4                                  \n" /* r0 = r0 + 4. r0 now points to MAIR0 in TCB. */
            "    ldr r1, [r0]                                 \n" /* r1 = *r0 i.e. r1 = MAIR0. */
            "    ldr r2, xMAIR0Const                          \n" /* r2 = 0xe000edc0 [Location of MAIR0]. */
            "    str r1, [r2]                                 \n" /* Program MAIR0. */
            "                                                 \n"
            "    adds r0, #4                                  \n" /* r0 = r0 + 4. r0 now points to first RBAR in TCB. */
            "    ldr r1, xRNRConst                            \n" /* r1 = 0xe000ed98 [Location of RNR]. */
            "                                                 \n"
            "    movs r3, #4                                  \n" /* r3 = 4. */
            "    str r3, [r1]                                 \n" /* Program RNR = 4. */
            "    ldmia r0!, {r4-r5}                           \n" /* Read first set of RBAR/RLAR registers from TCB. */
            "    ldr r2, xRBARConst                           \n" /* r2 = 0xe000ed9c [Location of RBAR]. */
            "    stmia r2!, {r4-r5}                           \n" /* Write first set of RBAR/RLAR registers. */
            "    movs r3, #5                                  \n" /* r3 = 5. */
            "    str r3, [r1]                                 \n" /* Program RNR = 5. */
            "    ldmia r0!, {r4-r5}                           \n" /* Read second set of RBAR/RLAR registers from TCB. */
            "    ldr r2, xRBARConst                           \n" /* r2 = 0xe000ed9c [Location of RBAR]. */
            "    stmia r2!, {r4-r5}                           \n" /* Write second set of RBAR/RLAR registers. */
            "    movs r3, #6                                  \n" /* r3 = 6. */
            "    str r3, [r1]                                 \n" /* Program RNR = 6. */
            "    ldmia r0!, {r4-r5}                           \n" /* Read third set of RBAR/RLAR registers from TCB. */
            "    ldr r2, xRBARConst                           \n" /* r2 = 0xe000ed9c [Location of RBAR]. */
            "    stmia r2!, {r4-r5}                           \n" /* Write third set of RBAR/RLAR registers. */
            "    movs r3, #7                                  \n" /* r3 = 6. */
            "    str r3, [r1]                                 \n" /* Program RNR = 7. */
            "    ldmia r0!, {r4-r5}                           \n" /* Read fourth set of RBAR/RLAR registers from TCB. */
            "    ldr r2, xRBARConst                           \n" /* r2 = 0xe000ed9c [Location of RBAR]. */
            "    stmia r2!, {r4-r5}                           \n" /* Write fourth set of RBAR/RLAR registers. */
            "                                                 \n"
            "    ldr r1, xMPUCTRLConst                        \n" /* r1 = 0xe000ed94 [Location of MPU_CTRL]. */
            "    ldr r2, [r1]                                 \n" /* Read the value of MPU_CTRL. */
            "    movs r3, #1                                  \n" /* r3 = 1. */
            "    orrs r2, r3                                  \n" /* r2 = r2 | r3 i.e. Set the bit 0 in r2. */
            "    str r2, [r1]                                 \n" /* Enable MPU. */
            "    dsb                                          \n" /* Force memory writes before continuing. */
            "                                                 \n"
            " restore_context:                                \n"
            "    ldr r2, pxCurrentTCBConst                    \n" /* Read the location of pxCurrentTCB i.e. &( pxCurrentTCB ). */
            "    ldr r0, [r2]                                 \n" /* r0 = pxCurrentTCB.*/
            "    ldr r1, [r0]                                 \n" /* r1 = Location of saved context in TCB. */
            "                                                 \n"
            " restore_special_regs:                           \n"
            "    subs r1, #16                                 \n"
            "    ldmia r1!, {r2-r5}                           \n" /* r2 = original PSP, r3 = PSPLIM, r4 = CONTROL, r5 = LR. */
            "    subs r1, #16                                 \n"
            "    msr psp, r2                                  \n"
            #if ( configRUN_FREERTOS_SECURE_ONLY == 1 )
                "    msr psplim, r3                           \n"
            #endif
            "    msr control, r4                              \n"
            "    mov lr, r5                                   \n"
            "                                                 \n"
            " restore_general_regs:                           \n"
            "    subs r1, #32                                 \n"
            "    ldmia r1!, {r4-r7}                           \n" /* r4-r7 contain half of the hardware saved context. */
            "    stmia r2!, {r4-r7}                           \n" /* Copy half of the the hardware saved context on the task stack. */
            "    ldmia r1!, {r4-r7}                           \n" /* r4-r7 contain rest half of the hardware saved context. */
            "    stmia r2!, {r4-r7}                           \n" /* Copy rest half of the the hardware saved context on the task stack. */
            "    subs r1, #48                                 \n"
            "    ldmia r1!, {r4-r7}                           \n" /* Restore r8-r11. */
            "    mov r8, r4                                   \n" /* r8 = r4. */
            "    mov r9, r5                                   \n" /* r9 = r5. */
            "    mov r10, r6                                  \n" /* r10 = r6. */
            "    mov r11, r7                                  \n" /* r11 = r7. */
            "    subs r1, #32                                 \n"
            "    ldmia r1!, {r4-r7}                           \n" /* Restore r4-r7. */
            "    subs r1, #16                                 \n"
            "                                                 \n"
            " restore_context_done:                           \n"
            "    str r1, [r0]                                 \n" /* Save the location where the context should be saved next as the first member of TCB. */
            "    bx lr                                        \n"
            "                                                 \n"
            " .align 4                                        \n"
            " pxCurrentTCBConst: .word pxCurrentTCB           \n"
            " xMPUCTRLConst: .word 0xe000ed94                 \n"
            " xMAIR0Const: .word 0xe000edc0                   \n"
            " xRNRConst: .word 0xe000ed98                     \n"
            " xRBARConst: .word 0xe000ed9c                    \n"
        );
    }

#else /* configENABLE_MPU */

    void PendSV_Handler( void ) /* __attribute__ (( naked )) PRIVILEGED_FUNCTION */
    {
        __asm volatile
        (
            "   .syntax unified                                 \n"
            "                                                   \n"
            "   mrs r0, psp                                     \n" /* Read PSP in r0. */
            "   ldr r2, pxCurrentTCBConst                       \n" /* Read the location of pxCurrentTCB i.e. &( pxCurrentTCB ). */
            "   ldr r1, [r2]                                    \n" /* Read pxCurrentTCB. */
            "   subs r0, r0, #40                                \n" /* Make space for PSPLIM, LR and the remaining registers on the stack. */
            "   str r0, [r1]                                    \n" /* Save the new top of stack in TCB. */
            #if ( configRUN_FREERTOS_SECURE_ONLY == 1 )
                "   mrs r2, psplim                              \n" /* r2 = PSPLIM. */
            #else
                "   movs r2, #0                                 \n" /* r2 = 0. 0 is stored in the PSPLIM slot. */
            #endif
            "   mov r3, lr                                      \n" /* r3 = LR/EXC_RETURN. */
            "   stmia r0!, {r2-r7}                              \n" /* Store on the stack - PSPLIM, LR and low registers that are not automatically saved. */
            "   mov r4, r8                                      \n" /* r4 = r8. */
            "   mov r5, r9                                      \n" /* r5 = r9. */
            "   mov r6, r10                                     \n" /* r6 = r10. */
            "   mov r7, r11                                     \n" /* r7 = r11. */
            "   stmia r0!, {r4-r7}                              \n" /* Store the high registers that are not saved automatically. */
            "                                                   \n"
            "   cpsid i                                         \n"
            "   bl vTaskSwitchContext                           \n"
            "   cpsie i                                         \n"
            "                                                   \n"
            "   ldr r2, pxCurrentTCBConst                       \n" /* Read the location of pxCurrentTCB i.e. &( pxCurrentTCB ). */
            "   ldr r1, [r2]                                    \n" /* Read pxCurrentTCB. */
            "   ldr r0, [r1]                                    \n" /* The first item in pxCurrentTCB is the task top of stack. r0 now points to the top of stack. */
            "                                                   \n"
            "   adds r0, r0, #24                                \n" /* Move to the high registers. */
            "   ldmia r0!, {r4-r7}                              \n" /* Restore the high registers that are not automatically restored. */
            "   mov r8, r4                                      \n" /* r8 = r4. */
            "   mov r9, r5                                      \n" /* r9 = r5. */
            "   mov r10, r6                                     \n" /* r10 = r6. */
            "   mov r11, r7                                     \n" /* r11 = r7. */
            "   msr psp, r0                                     \n" /* Remember the new top of stack for the task. */
            "   subs r0, r0, #40                                \n" /* Move to the starting of the saved context. */
            "   ldmia r0!, {r2-r7}                              \n" /* Read from stack - r2 = PSPLIM, r3 = LR and r4-r7 restored. */
            #if ( configRUN_FREERTOS_SECURE_ONLY == 1 )
                "   msr psplim, r2                              \n" /* Restore the PSPLIM register value for the task. */
            #endif
            "   bx r3                                           \n"
            "                                                   \n"
            "   .align 4                                        \n"
            "pxCurrentTCBConst: .word pxCurrentTCB              \n"
        );
    }

#endif /* configENABLE_MPU */
/*-----------------------------------------------------------*/

#if ( ( configENABLE_MPU == 1 ) && ( configUSE_MPU_WRAPPERS_V1 == 0 ) )

    void SVC_Handler( void ) /* __attribute__ (( naked )) PRIVILEGED_FUNCTION */
    {
        __asm volatile
        (
            ".syntax unified                \n"
            ".extern vPortSVCHandler_C      \n"
            ".extern vSystemCallEnter       \n"
            ".extern vSystemCallExit        \n"
            "                               \n"
            "movs r0, #4                    \n"
            "mov r1, lr                     \n"
            "tst r0, r1                     \n"
            "beq stack_on_msp               \n"
            "stack_on_psp:                  \n"
            "    mrs r0, psp                \n"
            "    b route_svc                \n"
            "stack_on_msp:                  \n"
            "    mrs r0, msp                \n"
            "    b route_svc                \n"
            "                               \n"
            "route_svc:                     \n"
            "    ldr r3, [r0, #24]          \n"
            "    subs r3, #2                \n"
            "    ldrb r2, [r3, #0]          \n"
            "    cmp r2, %0                 \n"
            "    blt system_call_enter      \n"
            "    cmp r2, %1                 \n"
            "    beq system_call_exit       \n"
            "    b vPortSVCHandler_C        \n"
            "                               \n"
            "system_call_enter:             \n"
            "    b vSystemCallEnter         \n"
            "system_call_exit:              \n"
            "    b vSystemCallExit          \n"
            "                               \n"
            : /* No outputs. */
            : "i" ( NUM_SYSTEM_CALLS ), "i" ( portSVC_SYSTEM_CALL_EXIT )
            : "r0", "r1", "r2", "r3", "memory"
        );
    }

#else /* ( configENABLE_MPU == 1 ) && ( configUSE_MPU_WRAPPERS_V1 == 0 ) */

    void SVC_Handler( void ) /* __attribute__ (( naked )) PRIVILEGED_FUNCTION */
    {
        __asm volatile
        (
            "   .syntax unified                                 \n"
            "                                                   \n"
            "   movs r0, #4                                     \n"
            "   mov r1, lr                                      \n"
            "   tst r0, r1                                      \n"
            "   beq stacking_used_msp                           \n"
            "   mrs r0, psp                                     \n"
            "   ldr r2, svchandler_address_const                \n"
            "   bx r2                                           \n"
            " stacking_used_msp:                                \n"
            "   mrs r0, msp                                     \n"
            "   ldr r2, svchandler_address_const                \n"
            "   bx r2                                           \n"
            "                                                   \n"
            "   .align 4                                        \n"
            "svchandler_address_const: .word vPortSVCHandler_C  \n"
        );
    }

#endif /* ( configENABLE_MPU == 1 ) && ( configUSE_MPU_WRAPPERS_V1 == 0 ) */
/*-----------------------------------------------------------*/
