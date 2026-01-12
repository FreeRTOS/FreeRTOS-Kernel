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

#include "PriorityDefinitions.h"

    PUBLIC _prvStartFirstTask
    PUBLIC ___interrupt_27

    EXTERN _pxCurrentTCB
    EXTERN _vTaskSwitchContext

    CFI Names cfiNames0
    CFI StackFrame CFA SP DATA
    CFI VirtualResource ?RET:32
    CFI Resource R1:32, R2:32, R3:32, R4:32, R5:32, R6:32, R7:32, R8:32
    CFI Resource R9:32, R10:32, R11:32, R12:32, R13:32, R14:32, R15:32
    CFI Resource SP:32
    CFI EndNames cfiNames0

    CFI Common cfiCommon0 Using cfiNames0
    CFI CodeAlign 1
    CFI DataAlign 1
    CFI ReturnAddress ?RET CODE
    CFI CFA SP+4
    CFI ?RET Frame(CFA, -4)
    CFI R1 Undefined
    CFI R2 Undefined
    CFI R3 Undefined
    CFI R4 Undefined
    CFI R5 Undefined
    CFI R6 SameValue
    CFI R7 SameValue
    CFI R8 SameValue
    CFI R9 SameValue
    CFI R10 SameValue
    CFI R11 SameValue
    CFI R12 SameValue
    CFI R13 SameValue
    CFI R14 Undefined
    CFI R15 Undefined
    CFI EndCommon cfiCommon0

    RSEG CODE:CODE(4)

_prvStartFirstTask:

        /* When starting the scheduler there is nothing that needs moving to the
        interrupt stack because the function is not called from an interrupt.
        Just ensure the current stack is the user stack. */
        SETPSW      U

        /* Obtain the location of the stack associated with which ever task
        pxCurrentTCB is currently pointing to. */
        MOV.L       #_pxCurrentTCB, R15
        MOV.L       [R15], R15
        MOV.L       [R15], R0

        /* Restore the registers from the stack of the task pointed to by
        pxCurrentTCB. */
        POP         R15

        /* Accumulator low 32 bits. */
        MVTACLO     R15, A0
        POP         R15

        /* Accumulator high 32 bits. */
        MVTACHI     R15, A0
        POP         R15

        /* Accumulator guard. */
        MVTACGU     R15, A0
        POP         R15

        /* Accumulator low 32 bits. */
        MVTACLO     R15, A1
        POP         R15

        /* Accumulator high 32 bits. */
        MVTACHI     R15, A1
        POP         R15

        /* Accumulator guard. */
        MVTACGU     R15, A1
        POP         R15

        /* Floating point status word. */
        MVTC        R15, FPSW

        /* R1 to R15 - R0 is not included as it is the SP. */
        POPM        R1-R15

        /* This pops the remaining registers. */
        RTE
        NOP
        NOP

/*-----------------------------------------------------------*/

/* The software interrupt - overwrite the default 'weak' definition. */
        CFI Block cfiBlock0 Using cfiCommon0
        CFI Function ___interrupt_27
        CODE
___interrupt_27:

        /* Re-enable interrupts. */
        SETPSW      I

        /* Move the data that was automatically pushed onto the interrupt stack when
        the interrupt occurred from the interrupt stack to the user stack.

        R15 is saved before it is clobbered. */
        PUSH.L      R15

        /* Read the user stack pointer. */
        MVFC        USP, R15

        /* Move the address down to the data being moved. */
        SUB     #12, R15
        MVTC        R15, USP

        /* Copy the data across, R15, then PC, then PSW. */
        MOV.L       [ R0 ], [ R15 ]
        MOV.L       4[ R0 ], 4[ R15 ]
        MOV.L       8[ R0 ], 8[ R15 ]

        /* Move the interrupt stack pointer to its new correct position. */
        ADD     #12, R0

        /* All the rest of the registers are saved directly to the user stack. */
        SETPSW      U

        /* Save the rest of the general registers (R15 has been saved already). */
        PUSHM       R1-R14

        /* Save the FPSW and accumulator. */
        MVFC        FPSW, R15
        PUSH.L      R15
        MVFACGU     #0, A1, R15
        PUSH.L      R15
        MVFACHI     #0, A1, R15
        PUSH.L      R15
        /* Low order word. */
        MVFACLO     #0, A1, R15
        PUSH.L      R15
        MVFACGU     #0, A0, R15
        PUSH.L      R15
        MVFACHI     #0, A0, R15
        PUSH.L      R15
        /* Low order word. */
        MVFACLO     #0, A0, R15
        PUSH.L      R15

        /* Save the stack pointer to the TCB. */
        MOV.L       #_pxCurrentTCB, R15
        MOV.L       [ R15 ], R15
        MOV.L       R0, [ R15 ]

        /* Ensure the interrupt mask is set to the syscall priority while the kernel
        structures are being accessed. */
        MVTIPL      #configMAX_SYSCALL_INTERRUPT_PRIORITY

        /* Select the next task to run. */
        CFI ?RET Frame(CFA, -8)
        CFI R15 Frame(CFA, -12)
        CFI R14 Frame(CFA, -16)
        CFI R13 Frame(CFA, -20)
        CFI R12 Frame(CFA, -24)
        CFI R11 Frame(CFA, -28)
        CFI R10 Frame(CFA, -32)
        CFI R9 Frame(CFA, -36)
        CFI R8 Frame(CFA, -40)
        CFI R7 Frame(CFA, -44)
        CFI R6 Frame(CFA, -48)
        CFI R5 Frame(CFA, -52)
        CFI R4 Frame(CFA, -56)
        CFI R3 Frame(CFA, -60)
        CFI R2 Frame(CFA, -64)
        CFI R1 Frame(CFA, -68)
        CFI CFA SP+96
        CFI FunCall _vTaskSwitchContext
        BSR.A       _vTaskSwitchContext

        /* Reset the interrupt mask as no more data structure access is required. */
        MVTIPL      #configKERNEL_INTERRUPT_PRIORITY

        /* Load the stack pointer of the task that is now selected as the Running
        state task from its TCB. */
        MOV.L       #_pxCurrentTCB,R15
        MOV.L       [ R15 ], R15
        MOV.L       [ R15 ], R0

        /* Restore the context of the new task.  The PSW (Program Status Word) and
        PC will be popped by the RTE instruction. */
        POP     R15

        /* Accumulator low 32 bits. */
        MVTACLO R15, A0
        POP     R15

        /* Accumulator high 32 bits. */
        MVTACHI R15, A0
        POP     R15

        /* Accumulator guard. */
        MVTACGU R15, A0
        POP     R15

        /* Accumulator low 32 bits. */
        MVTACLO R15, A1
        POP     R15

        /* Accumulator high 32 bits. */
        MVTACHI R15, A1
        POP     R15

        /* Accumulator guard. */
        MVTACGU R15, A1
        POP     R15
        MVTC        R15, FPSW
        POPM        R1-R15
        RTE
        NOP
        NOP
        CFI EndBlock cfiBlock0

/*-----------------------------------------------------------*/

        END
