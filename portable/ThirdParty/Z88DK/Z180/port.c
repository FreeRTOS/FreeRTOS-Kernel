/*
 * FreeRTOS Kernel V10.4.3
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
 */


#include <stdlib.h>

#include "include/FreeRTOS.h"

#if __SDCC
#include "include/sdcc/task.h"
#elif __SCCZ80
#include "include/sccz80/task.h"
#endif

/*-----------------------------------------------------------*/

/* We require the address of the pxCurrentTCB variable, but don't want to know
any details of its type. */

typedef void TCB_t;
extern volatile TCB_t * volatile pxCurrentTCB;
/*-----------------------------------------------------------*/

/*
 * Macro to save all the general purpose registers, the save the stack pointer
 * into the TCB.
 *
 * The first thing we do is save the flags then disable interrupts. This is to
 * guard our stack against having a context switch interrupt after we have already
 * pushed the registers onto the stack.
 *
 * The interrupts will have been disabled during the call to portSAVE_CONTEXT()
 * so we need not worry about reading/writing to the stack pointer.
 */

#define configTICK_RATE_HZ              (256)               /* Timer configured */
#define configISR_ORG                   ASMPC               /* ISR relocation */
#define configISR_IVT                   0xFFE6              /* PRT1 address */

#ifdef __SCCZ80

#define configSETUP_TIMER_INTERRUPT()                           \
    do{                                                         \
        asm(                                                    \
            "EXTERN __CPU_CLOCK                             \n" \
            "EXTERN RLDR1L, RLDR1H                          \n" \
            "EXTERN TCR, TCR_TIE1, TCR_TDE1                 \n" \
            "ld de,_timer_isr                               \n" \
            "ld hl,"string(configISR_IVT)" ; PRT1 address   \n" \
            "ld (hl),e                                      \n" \
            "inc hl                                         \n" \
            "ld (hl),d                                      \n" \
            "; we do configTICK_RATE_HZ ticks per second    \n" \
            "ld hl,__CPU_CLOCK/"string(configTICK_RATE_HZ)"/20-1 \n" \
            "out0(RLDR1L),l                                 \n" \
            "out0(RLDR1H),h                                 \n" \
            "in0 a,(TCR)                                    \n" \
            "or TCR_TIE1|TCR_TDE1                           \n" \
            "out0 (TCR),a                                   \n" \
            );                                                  \
    }while(0)

#define configRESET_TIMER_INTERRUPT()                           \
    do{                                                         \
        asm(                                                    \
            "EXTERN TCR, TMDR1L                             \n" \
            "in0 a,(TCR)                                    \n" \
            "in0 a,(TMDR1L)                                 \n" \
            );                                                  \
    }while(0)

#define configSTOP_TIMER_INTERRUPT()                            \
    do{                                                         \
        asm(                                                    \
            "EXTERN TCR, TCR_TIE1, TCR_TDE1                 \n" \
            "; disable down counting and interrupts for PRT1\n" \
            "in0 a,(TCR)                                    \n" \
            "xor TCR_TIE1|TCR_TDE1                          \n" \
            "out0 (TCR),a                                   \n" \
            );                                                  \
    }while(0)

#endif

#ifdef __SDCC

#define configSETUP_TIMER_INTERRUPT()                           \
    do{                                                         \
        __asm                                                   \
            EXTERN __CPU_CLOCK                                  \
            EXTERN RLDR1L, RLDR1H                               \
            EXTERN TCR, TCR_TIE1, TCR_TDE1                      \
            ; address of ISR                                    \
            ld de,_timer_isr                                    \
            ld hl,configISR_IVT ; PRT1 address                  \
            ld (hl),e                                           \
            inc hl                                              \
            ld (hl),d                                           \
            ; we do configTICK_RATE_HZ ticks per second         \
            ld hl,__CPU_CLOCK/configTICK_RATE_HZ/20-1           \
            out0(RLDR1L),l                                      \
            out0(RLDR1H),h                                      \
            ; enable down counting and interrupts for PRT1      \
            in0 a,(TCR)                                         \
            or TCR_TIE1|TCR_TDE1                                \
            out0 (TCR),a                                        \
        __endasm;                                               \
    }while(0)

#define configRESET_TIMER_INTERRUPT()                           \
    do{                                                         \
        __asm                                                   \
            EXTERN TCR, TMDR1L                                  \
            ; reset interrupt for PRT1                          \
            in0 a,(TCR)                                         \
            in0 a,(TMDR1L)                                      \
        __endasm;                                               \
    }while(0)

#define configSTOP_TIMER_INTERRUPT()                            \
    do{                                                         \
        __asm                                                   \
            EXTERN TCR, TCR_TIE1, TCR_TDE1                      \
            ; disable down counting and interrupts for PRT1     \
            in0 a,(TCR)                                         \
            xor TCR_TIE1|TCR_TDE1                               \
            out0 (TCR),a                                        \
        __endasm;                                               \
    }while(0)

#endif

/*-----------------------------------------------------------*/

/*
 * Perform hardware setup to enable ticks from Timer.
 */
static void prvSetupTimerInterrupt( void ) __preserves_regs(iyh,iyl);
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
    /* Place the parameter on the stack in the expected location. */
    *pxTopOfStack-- = ( StackType_t ) pvParameters;

    /* Place the task return address on stack. Not used */
    *pxTopOfStack-- = ( StackType_t ) 0;

    /* The start of the task code will be popped off the stack last, so place
    it on first. */
    *pxTopOfStack-- = ( StackType_t ) pxCode;

    /* Now the registers. */
    *pxTopOfStack-- = ( StackType_t ) 0xAFAF;   /* AF  */
    *pxTopOfStack-- = ( StackType_t ) 0x0404;   /* IF  */
    *pxTopOfStack-- = ( StackType_t ) 0xBCBC;   /* BC  */
    *pxTopOfStack-- = ( StackType_t ) 0xDEDE;   /* DE  */
    *pxTopOfStack-- = ( StackType_t ) 0xEFEF;   /* HL  */
    *pxTopOfStack-- = ( StackType_t ) 0xFAFA;   /* AF' */
    *pxTopOfStack-- = ( StackType_t ) 0xCBCB;   /* BC' */
    *pxTopOfStack-- = ( StackType_t ) 0xEDED;   /* DE' */
    *pxTopOfStack-- = ( StackType_t ) 0xFEFE;   /* HL' */
    *pxTopOfStack-- = ( StackType_t ) 0xCEFA;   /* IX  */
    *pxTopOfStack   = ( StackType_t ) 0xADDE;   /* IY  */

    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void ) __preserves_regs(a,b,c,d,e,iyh,iyl) __naked
{
    /* Setup the relevant timer hardware to generate the tick. */
    prvSetupTimerInterrupt();

    /* Restore the context of the first task that is going to run. */
    portRESTORE_CONTEXT();

    /* Should not get here. */
    return pdFALSE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void ) __preserves_regs(b,c,d,e,h,l,iyh,iyl)
{
    /*
     * It is unlikely that the Z80 port will get stopped.
     * If required simply disable the tick interrupt here.
     */
    configSTOP_TIMER_INTERRUPT();
}
/*-----------------------------------------------------------*/

/*
 * Manual context switch.  The first thing we do is save the registers so we
 * can use a naked attribute. This is called by the application, so we don't have
 * to check which bank is loaded.
 */
void vPortYield( void ) __preserves_regs(a,b,c,d,e,h,l,iyh,iyl) __naked
{
    portSAVE_CONTEXT();
    vTaskSwitchContext();
    portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

/*
 * Manual context switch callable from ISRs. The first thing we do is save
 * the registers so we can use a naked attribute.
 */
void vPortYieldFromISR(void)  __preserves_regs(a,b,c,d,e,h,l,iyh,iyl) __naked
void vPortYieldFromISR(void)
{
    portSAVE_CONTEXT_IN_ISR();
    vTaskSwitchContext();
    portRESTORE_CONTEXT_IN_ISR();
}
/*-----------------------------------------------------------*/

/*
 * Initialize Timer (PRT1 for YAZ180, and SCZ180 HBIOS).
 */
void prvSetupTimerInterrupt( void ) __preserves_regs(iyh,iyl)
{
    configSETUP_TIMER_INTERRUPT();
}
/*-----------------------------------------------------------*/

void timer_isr(void) __preserves_regs(a,b,c,d,e,h,l,iyh,iyl) __naked
{
#if configUSE_PREEMPTION == 1
    /*
     * Tick ISR for preemptive scheduler.  We can use a naked attribute as
     * the context is saved at the start of timer_isr().  The tick
     * count is incremented after the context is saved.
     *
     * Context switch function used by the tick.  This must be identical to
     * vPortYield() from the call to vTaskSwitchContext() onwards.  The only
     * difference from vPortYield() is the tick count is incremented as the
     * call comes from the tick ISR.
     */
    portSAVE_CONTEXT_IN_ISR();
    configRESET_TIMER_INTERRUPT();
    xTaskIncrementTick();
    vTaskSwitchContext();
    portRESTORE_CONTEXT_IN_ISR();
#else
    /*
     * Tick ISR for the cooperative scheduler.  All this does is increment the
     * tick count.  We don't need to switch context, this can only be done by
     * manual calls to taskYIELD();
     */
    portSAVE_CONTEXT_IN_ISR();
    configRESET_TIMER_INTERRUPT();
    xTaskIncrementTick();
    portRESTORE_CONTEXT_IN_ISR();
#endif
} // configUSE_PREEMPTION
