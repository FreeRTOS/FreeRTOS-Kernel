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

/* Standard includes. */
#include <limits.h>
#include <stdint.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "trap.h"
#include "x86_64.h"
#include "sectionapi.h"
#include "ioapic.h"
#include "io.h"
#include "stdio.h"
#include "string.h"
/* A critical section is exited when the critical section nesting count reaches
 * this value. */
#define portNO_CRITICAL_NESTING          ( ( uint32_t ) 0 )

/* This is the lowest possible ISR vector available to application code. */
#define portAPIC_MIN_ALLOWABLE_VECTOR    ( 0x20 )

/* EFLAGS bits. */
#define portEFLAGS_IF                    ( 0x200UL )

/* If configASSERT() is defined then the system stack is filled with this value
 * to allow for a crude stack overflow check. */
#define portSTACK_WORD                   ( 0xecececec )
/*-----------------------------------------------------------*/

/*
 * Starts the first task executing.
 */
void vPortStartFirstTask( void );
void vPortStoreTaskMPUSettings( xMPU_SETTINGS * xMPUSettings,
                              const struct xMEMORY_REGION * const xRegions,
                              StackType_t * pxBottomOfStack,
                              configSTACK_DEPTH_TYPE uxStackDepth );
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters,
                                     BaseType_t xRunPrivileged,
                                     xMPU_SETTINGS * xMPUSettings);
void vPortTaskUsesFPU( void );
static void prvSetupLAPIC( void );
void vPortSetupIDT( void );
BaseType_t xPortStartScheduler( void );
void vPortEndScheduler( void );
void vPortEnterCritical( void );
void vPortExitCritical( void );
uint32_t ulPortSetInterruptMask( void );
void vPortClearInterruptMask( uint32_t ulNewMaskValue );
void enable_sci(void);
void init_time(void);



extern struct TSS Tss;

/* A variable is used to keep track of the critical section nesting.  This
 * variable must be initialised to a non zero value to ensure interrupts don't
 * inadvertently become unmasked before the scheduler starts. It is set to zero
 * before the first task starts executing. */
 volatile uint32_t ulCriticalNesting = 9999UL;


/* Saved as part of the task context.  If pucPortTaskFPUContextBuffer is NULL
 * then the task does not have an FPU context.  If pucPortTaskFPUContextBuffer is
 * not NULL then it points to a buffer into which the FPU context can be saved. */
#define portFPU_CONTEXT_SIZE_BYTES 512
uint8_t pucPortTaskFPUContextBuffer [portFPU_CONTEXT_SIZE_BYTES] __attribute__((aligned(16)));
uint32_t xTaskUsesFPU  = pdFALSE;

/* The stack used by interrupt handlers. */
static uint64_t ulSystemStack[ configISR_STACK_SIZE ] __attribute__( ( used ) ) = { 0 };

/* Don't use the very top of the system stack so the return address
 * appears as 0 if the debugger tries to unwind the stack. */
volatile uint64_t ulTopOfSystemStack __attribute__( ( used ) ) = ( uint64_t ) &( ulSystemStack[ configISR_STACK_SIZE - 5 ] );


/* If a yield is requested from an interrupt or from a critical section then
 * the yield is not performed immediately, and ulPortYieldPending is set to pdTRUE
 * instead to indicate the yield should be performed at the end of the interrupt
 * when the critical section is exited. */
volatile uint32_t ulPortYieldPending __attribute__( ( used ) ) = pdFALSE;
volatile uint32_t schedStart __attribute__( ( used ) ) = pdFALSE;

/* Counts the interrupt nesting depth.  Used to know when to switch to the
 * interrupt/system stack and when to save/restore a complete context. */
volatile uint32_t ulInterruptNesting __attribute__( ( used ) ) = 0;

/*-----------------------------------------------------------*/

int vHaltCPU(void) ;
int vHaltCPU(void) {
    __asm__ volatile("hlt");
    return 1;
}

extern StackType_t *pxCurrentTCB;
void vPortStartFirstTask() {
    schedStart = pdTRUE;
    struct TrapFrame* tf = (struct TrapFrame*) *pxCurrentTCB;
    xMPU_SETTINGS * xMPUSettings = (xMPU_SETTINGS*) (pxCurrentTCB+1);
    load_cr3(xMPUSettings->pgd);
    Tss.rsp0 = (uint64_t) xMPUSettings->kernel_stack;
    starttask((void*)*pxCurrentTCB);
}

/*
* This method is called by FreeRTOS to store
*/
void vPortStoreTaskMPUSettings( xMPU_SETTINGS * xMPUSettings,
                              const struct xMEMORY_REGION * const xRegions,
                              StackType_t * pxBottomOfStack,
                              configSTACK_DEPTH_TYPE uxStackDepth )
{
    extern uint64_t pml4;
    if (uxStackDepth > 0 ) {
        xMPUSettings->kernel_stack = &ulSystemStack[configMINIMAL_STACK_SIZE-1];
        if (xRegions != NULL) {
            // Allocate page table
            uint64_t *pgd = pMallocPageTable();
            for (int region_index = 0; region_index < portNUM_CONFIGURABLE_REGIONS; region_index++) {
                 if (xRegions[region_index].pvBaseAddress == 0)  {
                     // last defined index
                     break;
                 }
                 vMapPages((uint64_t) xRegions[region_index].pvBaseAddress, ((uint64_t)xRegions[region_index].pvBaseAddress) + xRegions[region_index].ulLengthInBytes, pgd, xRegions[region_index].ulParameters);
                 // Copy half page tables address from kernel
                 (void) memcpy(pgd, &pml4, PAGE_TABLE_SIZE/2*sizeof(uint64_t));
            }
            xMPUSettings->pgd = (uint64_t) pgd;
        } else {
            xMPUSettings->pgd = (uint64_t) &pml4;
        }
    } 
}

/*
 * See header file for description.
 */
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters,
                                     BaseType_t xRunPrivileged,
                                     xMPU_SETTINGS * xMPUSettings)
{
    uint32_t ulCodeSegment;

    pxTopOfStack = (StackType_t *)(pxTopOfStack - sizeof(struct TrapFrame));
    struct TrapFrame* tf = (struct TrapFrame *)pxTopOfStack;
    tf->rdi = (uint64_t) pvParameters;
    tf->cs = 0x8;
    tf->rip = (uint64_t) pxCode;
    tf->ss = 0x10;
    tf->rsp = (uint64_t) pxTopOfStack;
    tf->rflags = 0x202;
    int param = 0;
    if (xRunPrivileged == 0) {
       Tss.rsp0 = (uint64_t) xMPUSettings->kernel_stack;
       tf->cs = (int64_t)((int64_t)0x18|(int64_t)0x3);
       tf->ss = (int64_t)((int64_t)0x20|(int64_t)0x3);
       tf->rip = USER_VA_START+(uint64_t)pxCode;
    }
    return pxTopOfStack;
}
/*-----------------------------------------------------------*/
#if defined( configSUPPORT_FPU )
#if ( configSUPPORT_FPU == 1 )

    void vPortTaskUsesFPU( void )
    {
        /* A task is registering the fact that it needs an FPU context.  Allocate a
         * buffer into which the context can be saved. */
        xTaskUsesFPU = pdTRUE;
        /* Initialise the floating point registers. */
        __asm volatile ( "fninit" );
    }

#endif /* configSUPPORT_FPU */
#endif
/*-----------------------------------------------------------*/
#define portAPIC_LVT_ERROR_VECTOR        ( 0xfe )
#define portAPIC_SPURIOUS_INT_VECTOR     ( 0xff )
//#define configCPU_CLOCK_HZ               ( 2994354000UL )
#define configCPU_CLOCK_HZ               ( 400000000UL )


static void prvSetupLAPIC( void )
{
    /* Initialise LAPIC to a well known state. */
    portAPIC_LDR = 0xFFFFFFFF;
    portAPIC_LDR = ( ( portAPIC_LDR & 0x00FFFFFF ) | 0x00000001 );
    portAPIC_LVT_TIMER = portAPIC_DISABLE;
    portAPIC_LVT_PERF = portAPIC_NMI;
    portAPIC_LVT_LINT0 = portAPIC_DISABLE;
    portAPIC_LVT_LINT1 = portAPIC_DISABLE;
    portAPIC_TASK_PRIORITY = 0;

    /* Enable the APIC, mapping the spurious interrupt at the same time. */
    portAPIC_SPURIOUS_INT = portAPIC_SPURIOUS_INT_VECTOR | portAPIC_ENABLE_BIT;

    /* Set timer error vector. */
    portAPIC_LVT_ERROR = portAPIC_LVT_ERROR_VECTOR;

}

/*-----------------------------------------------------------*/

#define PIC1            0x20
#define PIC2            0xA0
#define PIC1_COMMAND    PIC1
#define PIC1_DATA       (PIC1+1)
#define PIC2_COMMAND    PIC2
#define PIC2_DATA       (PIC2+1)

void vPortSetupIDT( void )
{
    // Disable interrupts from 8259
    outb(PIC1_COMMAND, 0x21);
    outb(PIC1_DATA, 0xFF);
    outb(PIC1_COMMAND, 0x22);
    outb(PIC1_DATA, 0xFF);
    vIDTInit();
    prvSetupLAPIC();
    set_ioapic_irq_mask(portAPIC_TIMER_INT_VECTOR-0x20, 0);
    enable_sci();
    portENABLE_INTERRUPTS();
}
/*-----------------------------------------------------------*/
BaseType_t xPortStartScheduler( void )
{
    /* Initialise Interrupt Descriptor Table (IDT). */
    vPortSetupIDT();

    init_time();

    /* Make sure the stack used by interrupts is aligned. */
    ulTopOfSystemStack &= ~portBYTE_ALIGNMENT_MASK;

    ulCriticalNesting = 0;
    /* Enable LAPIC Counter.*/
    // portAPIC_LVT_TIMER = portAPIC_TIMER_PERIODIC | portAPIC_TIMER_INT_VECTOR;

    /* Sometimes needed. */
    // portAPIC_TMRDIV = portAPIC_DIV_16;

    /* Should not return from the following function as the scheduler will then
     * be executing the tasks. */
    vPortStartFirstTask();

    return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
    /* Not implemented in ports where there is nothing to return to.
     * Artificially force an assert. */
    configASSERT( ulCriticalNesting == 1000UL );
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
    if( ulCriticalNesting == 0UL )
    {
        __asm volatile ( "cli" );
    }

    /* Now that interrupts are disabled, ulCriticalNesting can be accessed
     * directly.  Increment ulCriticalNesting to keep a count of how many times
     * portENTER_CRITICAL() has been called. */
    ulCriticalNesting++;

}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
    if( ulCriticalNesting > 0UL )
    {
        /* Decrement the nesting count as the critical section is being
         * exited. */
        ulCriticalNesting--;

        /* If the nesting level has reached zero then all interrupt
         * priorities must be re-enabled. */
        if( ulCriticalNesting == portNO_CRITICAL_NESTING )
        {
            __asm volatile ( "sti" );

            /* If a yield was pended from within the critical section then
             * perform the yield now. */
            if( ulPortYieldPending != pdFALSE )
            {
                ulPortYieldPending = pdFALSE;
                __asm volatile ( portYIELD_INTERRUPT );
            }
        }
    }

}
/*-----------------------------------------------------------*/

uint32_t ulPortSetInterruptMask( void )
{
    volatile uint64_t ulOriginalMask;

    /* Set mask to max syscall priority. */
#if defined (configMAX_API_CALL_INTERRUPT_PRIORITY)
   #if defined (portMAX_PRIORITY)
    #if ( configMAX_API_CALL_INTERRUPT_PRIORITY == portMAX_PRIORITY )
    {
        /* Return whether interrupts were already enabled or not.  Pop adjusts
         * the stack first. */
            __asm__ volatile (
                "pushfq             \n\t"
                "popq %%rax         \n\t"
                "cli                \n\t"
                "movq %%rax, %0     \n\t"
                : "=r" (ulOriginalMask)
                :
                : "rax", "memory"
            );

        ulOriginalMask &= portEFLAGS_IF;
    }
    #else
    {
        /* Return original mask. */
        ulOriginalMask = portAPIC_TASK_PRIORITY;
        portAPIC_TASK_PRIORITY = portMAX_API_CALL_PRIORITY;
        configASSERT( portAPIC_TASK_PRIORITY == portMAX_API_CALL_PRIORITY );
    }
    #endif /* if ( configMAX_API_CALL_INTERRUPT_PRIORITY == portMAX_PRIORITY ) */
#endif
#endif
    return ulOriginalMask;
}
/*-----------------------------------------------------------*/
void vPortClearInterruptMask( uint32_t ulNewMaskValue )
{
#if defined (configMAX_API_CALL_INTERRUPT_PRIORITY)
   #if defined (portMAX_PRIORITY)
    #if ( configMAX_API_CALL_INTERRUPT_PRIORITY == portMAX_PRIORITY )
    {
        if( ulNewMaskValue != pdFALSE )
        {
            __asm volatile ( "sti" );
        }
    }
    #else
    {
        portAPIC_TASK_PRIORITY = ulNewMaskValue;
        configASSERT( portAPIC_TASK_PRIORITY == ulNewMaskValue );
    }
    #endif /* if ( configMAX_API_CALL_INTERRUPT_PRIORITY == portMAX_PRIORITY ) */
#endif
#endif
}
/*-----------------------------------------------------------*/
FREERTOS_SYSTEM_CALL int vPortIsPrivileged(void) {
    unsigned short cs =(unsigned short)0;
    // Read the Code Segment (CS) register
    __asm__ __volatile__("mov %%cs, %0" : "=r"(cs));
    // Check if the Current Privilege Level (CPL) is 0 (Ring 0)
    if ((cs & (unsigned short)0x3) ==(unsigned short) 0) {
        return 1; // In Ring 0
    } else {
        return 0; // Not in Ring 0
    }
}
