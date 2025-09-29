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

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

#ifndef configINTERRUPT_CONTROLLER_BASE_ADDRESS
    #error configINTERRUPT_CONTROLLER_BASE_ADDRESS must be defined.  Refer to Cortex-A equivalent: /* https://www.freertos.org/Using-FreeRTOS-on-Cortex-A-Embedded-Processors */
#endif

#ifndef configINTERRUPT_CONTROLLER_CPU_INTERFACE_OFFSET
    #error configINTERRUPT_CONTROLLER_CPU_INTERFACE_OFFSET must be defined.  Refer to Cortex-A equivalent: /* https://www.freertos.org/Using-FreeRTOS-on-Cortex-A-Embedded-Processors */
#endif

#ifndef configUNIQUE_INTERRUPT_PRIORITIES
    #error configUNIQUE_INTERRUPT_PRIORITIES must be defined.  Refer to Cortex-A equivalent: /* https://www.freertos.org/Using-FreeRTOS-on-Cortex-A-Embedded-Processors */
#endif

#ifndef configSETUP_TICK_INTERRUPT
    #error configSETUP_TICK_INTERRUPT() must be defined.  Refer to Cortex-A equivalent: /* https://www.freertos.org/Using-FreeRTOS-on-Cortex-A-Embedded-Processors */
#endif /* configSETUP_TICK_INTERRUPT */

#ifndef configMAX_API_CALL_INTERRUPT_PRIORITY
    #error configMAX_API_CALL_INTERRUPT_PRIORITY must be defined.  Refer to Cortex-A equivalent: /* https://www.freertos.org/Using-FreeRTOS-on-Cortex-A-Embedded-Processors */
#endif

#if configMAX_API_CALL_INTERRUPT_PRIORITY == 0
    #error "configMAX_API_CALL_INTERRUPT_PRIORITY must not be set to 0"
#endif

#if configMAX_API_CALL_INTERRUPT_PRIORITY > configUNIQUE_INTERRUPT_PRIORITIES
    #error "configMAX_API_CALL_INTERRUPT_PRIORITY must be less than or equal to configUNIQUE_INTERRUPT_PRIORITIES as the lower the numeric priority value the higher the logical interrupt priority"
#endif

#if configUSE_PORT_OPTIMISED_TASK_SELECTION == 1
    /* Check the configuration. */
    #if ( configMAX_PRIORITIES > 32 )
        #error "configUSE_PORT_OPTIMISED_TASK_SELECTION can only be set to 1 when configMAX_PRIORITIES is less than or equal to 32.  It is very rare that a system requires more than 10 to 15 different priorities as tasks that share a priority will time slice."
    #endif
#endif /* configUSE_PORT_OPTIMISED_TASK_SELECTION */

/* In case security extensions are implemented. */
#if configMAX_API_CALL_INTERRUPT_PRIORITY <= ( configUNIQUE_INTERRUPT_PRIORITIES / 2 )
    #error "configMAX_API_CALL_INTERRUPT_PRIORITY must be greater than ( configUNIQUE_INTERRUPT_PRIORITIES / 2 )"
#endif

#ifndef configCLEAR_TICK_INTERRUPT
    #error configCLEAR_TICK_INTERRUPT must be defined in FreeRTOSConfig.h to clear which ever interrupt was used to generate the tick interrupt.
#endif

#if configNUMBER_OF_CORES < 1
    #error configNUMBER_OF_CORES must be set to 1 or greater.  If the application is not using multiple cores then set configNUMBER_OF_CORES to 1.
#endif /* configNUMBER_OF_CORES < 1 */

/* A critical section is exited when the critical section nesting count reaches
 * this value. */
#define portNO_CRITICAL_NESTING    ( ( size_t ) 0 )

/* Macro to unmask all interrupt priorities. */
#define portCLEAR_INTERRUPT_PRIORITIES_MASK()    __asm volatile ( "SVC %0" : : "i" ( portSVC_UNMASK_ALL_INTERRUPTS ) : "memory" )

/* Tasks are not created with a floating point context, but can be given a
 * floating point context after they have been created.  A variable is stored as
 * part of the tasks context that holds portNO_FLOATING_POINT_CONTEXT if the task
 * does not have an FPU context, or any other value if the task does have an FPU
 * context. */
#define portNO_FLOATING_POINT_CONTEXT    ( ( StackType_t ) 0 )

/* Constants required to setup the initial task context. */
#define portSP_ELx                       ( ( StackType_t ) 0x01 )
#define portSP_EL0                       ( ( StackType_t ) 0x00 )
#define portEL1                          ( ( StackType_t ) 0x04 )
#define portEL0                          ( ( StackType_t ) 0x00 )

#define portINITIAL_PSTATE               ( portEL0 | portSP_EL0 )

/* Used by portASSERT_IF_INTERRUPT_PRIORITY_INVALID() when ensuring the binary
 * point is zero. */
#define portBINARY_POINT_BITS            ( ( uint8_t ) 0x03 )

/* Masks all bits in the APSR other than the mode bits. */
#define portAPSR_MODE_BITS_MASK          ( 0x0C )

/* The I bit in the DAIF bits. */
#define portDAIF_I                       ( 0x80 )

#define portMAX_8_BIT_VALUE              ( ( uint8_t ) 0xff )
#define portBIT_0_SET                    ( ( uint8_t ) 0x01 )

/* The space on the stack required to hold the FPU registers.
 * There are 32 128-bit plus 2 64-bit status registers. */
#define portFPU_REGISTER_WORDS           ( ( 32 * 2 ) + 2 )

/*-----------------------------------------------------------*/

/*
 * Starts the first task executing.  This function is necessarily written in
 * assembly code so is implemented in portASM.s.
 */
extern void vPortRestoreTaskContext( void );

extern void vGIC_EnableIRQ( uint32_t ulInterruptID );
extern void vGIC_SetPriority( uint32_t ulInterruptID, uint32_t ulPriority );
extern void vGIC_PowerUpRedistributor( void );
extern void vGIC_EnableCPUInterface( void );

/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES == 1 )
    volatile uint64_t ullCriticalNesting = 0ULL;

/* Saved as part of the task context.  If ullPortTaskHasFPUContext is non-zero
 * then floating point context must be saved and restored for the task. */
    uint64_t ullPortTaskHasFPUContext = pdFALSE;

/* Set to 1 to pend a context switch from an ISR. */
    uint64_t ullPortYieldRequired = pdFALSE;

/* Counts the interrupt nesting depth.  A context switch is only performed if
 * if the nesting depth is 0. */
    uint64_t ullPortInterruptNesting = 0;
#else /* #if ( configNUMBER_OF_CORES == 1 ) */
    volatile uint64_t ullCriticalNestings[ configNUMBER_OF_CORES ] = { 0 };

    /* Saved as part of the task context.  If ullPortTaskHasFPUContext is non-zero
     * then floating point context must be saved and restored for the task. */
    uint64_t ullPortTaskHasFPUContext[ configNUMBER_OF_CORES ] = { pdFALSE };
    uint64_t ullPortYieldRequired[ configNUMBER_OF_CORES ] = { pdFALSE };
    uint64_t ullPortInterruptNestings[ configNUMBER_OF_CORES ] = { 0 };

    /* Flags to check if the secondary cores are ready. */
    volatile uint8_t ucSecondaryCoresReadyFlags[ configNUMBER_OF_CORES - 1 ] = { 0 };
    volatile uint8_t ucPrimaryCoreInitDoneFlag = 0;
#endif /* #if ( configNUMBER_OF_CORES == 1 ) */

/* Used in the ASM code. */
__attribute__( ( used ) ) const uint64_t ullMaxAPIPriorityMask = ( configMAX_API_CALL_INTERRUPT_PRIORITY << portPRIORITY_SHIFT );

/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
    /* Setup the initial stack of the task.  The stack is set exactly as
     * expected by the portRESTORE_CONTEXT() macro. */

    /* First all the general purpose registers. */
    pxTopOfStack--;
    *pxTopOfStack = 0x0101010101010101ULL;        /* R1 */
    pxTopOfStack--;
    *pxTopOfStack = ( StackType_t ) pvParameters; /* R0 */
    pxTopOfStack--;
    *pxTopOfStack = 0x0303030303030303ULL;        /* R3 */
    pxTopOfStack--;
    *pxTopOfStack = 0x0202020202020202ULL;        /* R2 */
    pxTopOfStack--;
    *pxTopOfStack = 0x0505050505050505ULL;        /* R5 */
    pxTopOfStack--;
    *pxTopOfStack = 0x0404040404040404ULL;        /* R4 */
    pxTopOfStack--;
    *pxTopOfStack = 0x0707070707070707ULL;        /* R7 */
    pxTopOfStack--;
    *pxTopOfStack = 0x0606060606060606ULL;        /* R6 */
    pxTopOfStack--;
    *pxTopOfStack = 0x0909090909090909ULL;        /* R9 */
    pxTopOfStack--;
    *pxTopOfStack = 0x0808080808080808ULL;        /* R8 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1111111111111111ULL;        /* R11 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1010101010101010ULL;        /* R10 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1313131313131313ULL;        /* R13 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1212121212121212ULL;        /* R12 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1515151515151515ULL;        /* R15 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1414141414141414ULL;        /* R14 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1717171717171717ULL;        /* R17 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1616161616161616ULL;        /* R16 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1919191919191919ULL;        /* R19 */
    pxTopOfStack--;
    *pxTopOfStack = 0x1818181818181818ULL;        /* R18 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2121212121212121ULL;        /* R21 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2020202020202020ULL;        /* R20 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2323232323232323ULL;        /* R23 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2222222222222222ULL;        /* R22 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2525252525252525ULL;        /* R25 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2424242424242424ULL;        /* R24 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2727272727272727ULL;        /* R27 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2626262626262626ULL;        /* R26 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2929292929292929ULL;        /* R29 */
    pxTopOfStack--;
    *pxTopOfStack = 0x2828282828282828ULL;        /* R28 */
    pxTopOfStack--;
    *pxTopOfStack = ( StackType_t ) 0x00;         /* XZR - has no effect, used so there are an even number of registers. */
    pxTopOfStack--;
    *pxTopOfStack = ( StackType_t ) 0x00;         /* R30 - procedure call link register. */

    pxTopOfStack--;
    *pxTopOfStack = portINITIAL_PSTATE;

    pxTopOfStack--;
    *pxTopOfStack = ( StackType_t ) pxCode; /* Exception return address. */

    #if ( configUSE_TASK_FPU_SUPPORT == portTASK_NO_FPU_CONTEXT_BY_DEFAULT )
    {
        /* The task will start with a critical nesting count of 0 as interrupts are
         * enabled. */
        pxTopOfStack--;
        *pxTopOfStack = portNO_CRITICAL_NESTING;

        /* The task will start without a floating point context.  A task that
         * uses the floating point hardware must call vPortTaskUsesFPU() before
         * executing any floating point instructions. */
        pxTopOfStack--;
        *pxTopOfStack = portNO_FLOATING_POINT_CONTEXT;
    }
    #elif ( configUSE_TASK_FPU_SUPPORT == portTASK_HAVE_FPU_CONTEXT_BY_DEFAULT )
    {
        /* The task will start with a floating point context.  Leave enough
         * space for the registers - and ensure they are initialised to 0. */
        pxTopOfStack -= portFPU_REGISTER_WORDS;
        memset( pxTopOfStack, 0x00, portFPU_REGISTER_WORDS * sizeof( StackType_t ) );

        /* The task will start with a critical nesting count of 0 as interrupts are
         * enabled. */
        pxTopOfStack--;
        *pxTopOfStack = portNO_CRITICAL_NESTING;

        pxTopOfStack--;
        *pxTopOfStack = pdTRUE;
        #if ( configNUMBER_OF_CORES == 1 )
        ullPortTaskHasFPUContext = pdTRUE;
        #else
        ullPortTaskHasFPUContext[ portGET_CORE_ID() ] = pdTRUE;
        #endif
    }
    #else /* if ( configUSE_TASK_FPU_SUPPORT == portTASK_NO_FPU_CONTEXT_BY_DEFAULT ) */
    {
        #error "Invalid configUSE_TASK_FPU_SUPPORT setting - configUSE_TASK_FPU_SUPPORT must be set to 1, 2, or left undefined."
    }
    #endif /* if ( configUSE_TASK_FPU_SUPPORT == portTASK_NO_FPU_CONTEXT_BY_DEFAULT ) */

    return pxTopOfStack;

}

/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
    uint64_t ullAPSR;

    #if ( configASSERT_DEFINED == 1 )
    {
        volatile uint8_t ucOriginalPriority;
        volatile uint8_t * const pucFirstUserPriorityRegister = ( volatile uint8_t * const ) ( configINTERRUPT_CONTROLLER_BASE_ADDRESS + portINTERRUPT_PRIORITY_REGISTER_OFFSET );
        volatile uint8_t ucMaxPriorityValue;

        /* Determine how many priority bits are implemented in the GIC.
            *
            * Save the interrupt priority value that is about to be clobbered. */
        ucOriginalPriority = *pucFirstUserPriorityRegister;

        /* Determine the number of priority bits available.  First write to
            * all possible bits. */
        *pucFirstUserPriorityRegister = portMAX_8_BIT_VALUE;

        /* Read the value back to see how many bits stuck. */
        ucMaxPriorityValue = *pucFirstUserPriorityRegister;

        /* Shift to the least significant bits. */
        while( ( ucMaxPriorityValue & portBIT_0_SET ) != portBIT_0_SET )
        {
            ucMaxPriorityValue >>= ( uint8_t ) 0x01;
        }

        /* Sanity check configUNIQUE_INTERRUPT_PRIORITIES matches the read
            * value. */
        configASSERT( ucMaxPriorityValue >= portLOWEST_INTERRUPT_PRIORITY );


        /* Restore the clobbered interrupt priority register to its original
            * value. */
        *pucFirstUserPriorityRegister = ucOriginalPriority;
    }
    #endif /* configASSERT_DEFINED */

    __asm volatile ( "MRS %0, CurrentEL" : "=r" ( ullAPSR ) );
    ullAPSR &= portAPSR_MODE_BITS_MASK;

    configASSERT( ullAPSR == portEL1 );

    /* Interrupts are turned off in the CPU itself to ensure a tick does
     * not execute while the scheduler is being started.  Interrupts are
     * automatically turned back on in the CPU when the first task starts
     * executing. */
    __asm volatile ( "MSR DAIFSET, #2\n"
                     "DSB SY\n"
                     "ISB SY\n" ::: "memory" );
    #if ( configNUMBER_OF_CORES > 1 )
        /* Start the timer that generates the tick ISR. */
        configSETUP_TICK_INTERRUPT();
        ucPrimaryCoreInitDoneFlag = 1;
        __asm volatile ( "SEV                       \n"
                         "DSB SY                    \n"
                         "ISB SY                    \n"
                         ::: "memory" );
        /* Hold the primary core here until all the secondary cores are ready, this would be achieved only when
         * all elements of ucSecondaryCoresReadyFlags are set.
         */
        while( 1 )
        {
            BaseType_t xAllCoresReady = pdTRUE;
            for( uint32_t ulCoreID = 0; ulCoreID < ( configNUMBER_OF_CORES - 1 ); ulCoreID++ )
            {
                if( ucSecondaryCoresReadyFlags[ ulCoreID ] != pdTRUE )
                {
                    xAllCoresReady = pdFALSE;
                    break;
                }
            }

            if ( xAllCoresReady == pdTRUE )
            {
                break;
            }
        }
    #else /* if ( configNUMBER_OF_CORES > 1 ) */
        /* Start the timer that generates the tick ISR. */
        configSETUP_TICK_INTERRUPT();
    #endif /* if ( configNUMBER_OF_CORES > 1 ) */

    /* Start the first task executing. */
    vPortRestoreTaskContext();

    return 0;
}

/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
    /* Stub implementation for ports where there is nothing to return to
     * Artificially force an assert. */
    configASSERT( NULL );
}

/*-----------------------------------------------------------*/

#if  ( configNUMBER_OF_CORES == 1 )
    void vPortEnterCritical( void )
    {
        /* Mask interrupts up to the max syscall interrupt priority. */
        uxPortSetInterruptMask();

        /* Now interrupts are disabled ullCriticalNesting can be accessed
         * directly.  Increment ullCriticalNesting to keep a count of how many times
         * portENTER_CRITICAL() has been called. */
        ullCriticalNesting++;

        /* This is not the interrupt safe version of the enter critical function so
         * assert() if it is being called from an interrupt context.  Only API
         * functions that end in "FromISR" can be used in an interrupt.  Only assert if
         * the critical nesting count is 1 to protect against recursive calls if the
         * assert function also uses a critical section. */
        if( ullCriticalNesting == 1ULL )
        {
            configASSERT( ullPortInterruptNesting == 0 );
        }
    }

/*-----------------------------------------------------------*/

    void vPortExitCritical( void )
    {
        if( ullCriticalNesting > portNO_CRITICAL_NESTING )
        {
            /* Decrement the nesting count as the critical section is being
             * exited. */
            ullCriticalNesting--;

            /* If the nesting level has reached zero then all interrupt
             * priorities must be re-enabled. */
            if( ullCriticalNesting == portNO_CRITICAL_NESTING )
            {
                /* Critical nesting has reached zero so all interrupt priorities
                 * should be unmasked. */
                portCLEAR_INTERRUPT_PRIORITIES_MASK();
            }
        }
    }
#endif /* if ( configNUMBER_OF_CORES == 1 ) */

/*-----------------------------------------------------------*/

void FreeRTOS_Tick_Handler( void )
{
    /* Must be the lowest possible priority. */
    uint64_t ullRunningInterruptPriority;
    __asm volatile ( "MRS %0, ICC_RPR_EL1" : "=r" ( ullRunningInterruptPriority ) );

    configASSERT( ullRunningInterruptPriority == ( portLOWEST_USABLE_INTERRUPT_PRIORITY << portPRIORITY_SHIFT ) );

    /* Interrupts should not be enabled before this point. */
    #if ( configASSERT_DEFINED == 1 )
    {
        uint64_t ullMaskBits;

        __asm volatile ( "MRS %0, DAIF" : "=r" ( ullMaskBits )::"memory" );
        configASSERT( ( ullMaskBits & portDAIF_I ) != 0 );
    }
    #endif /* configASSERT_DEFINED */

    /* Set interrupt mask before altering scheduler structures.   The tick
     * handler runs at the lowest priority, so interrupts cannot already be masked,
     * so there is no need to save and restore the current mask value.  It is
     * necessary to turn off interrupts in the CPU itself while the ICCPMR is being
     * updated. */
    __asm volatile ( "MSR ICC_PMR_EL1, %0      \n"
                     "DSB SY                    \n"
                     "ISB SY                    \n"
                     ::"r" ( configMAX_API_CALL_INTERRUPT_PRIORITY << portPRIORITY_SHIFT ) : "memory" );

    /* Ok to enable interrupts after the interrupt source has been cleared. */
    configCLEAR_TICK_INTERRUPT();
    __asm volatile ( "MSR DAIFCLR, #2\n"
                     "DSB SY\n"
                     "ISB SY\n" ::: "memory" );

    #if ( configNUMBER_OF_CORES > 1 )
        UBaseType_t x = portENTER_CRITICAL_FROM_ISR();
    #endif /* if ( configNUMBER_OF_CORES > 1 ) */

    /* Increment the RTOS tick. */
    if( xTaskIncrementTick() != pdFALSE )
    {
        #if ( configNUMBER_OF_CORES == 1 )
            ullPortYieldRequired = pdTRUE;
        #else
            ullPortYieldRequired[ portGET_CORE_ID() ] = pdTRUE;
        #endif
    }
    #if ( configNUMBER_OF_CORES > 1 )
        portEXIT_CRITICAL_FROM_ISR(x);
    #endif /* if ( configNUMBER_OF_CORES > 1 ) */

    /* Ensure all interrupt priorities are active again. */
    portCLEAR_INTERRUPT_PRIORITIES_MASK();
}

/*-----------------------------------------------------------*/

#if ( configUSE_TASK_FPU_SUPPORT == portTASK_NO_FPU_CONTEXT_BY_DEFAULT )

    void vPortTaskUsesFPU( void )
    {
        /* A task is registering the fact that it needs an FPU context.  Set the
         * FPU flag (which is saved as part of the task context). */
        #if  ( configNUMBER_OF_CORES == 1 )
            ullPortTaskHasFPUContext = pdTRUE;
        #else
            ullPortTaskHasFPUContext[ portGET_CORE_ID() ] = pdTRUE;
        #endif

        /* Consider initialising the FPSR here - but probably not necessary in
         * AArch64. */
    }

#endif /* configUSE_TASK_FPU_SUPPORT */

/*-----------------------------------------------------------*/

void vPortClearInterruptMask( UBaseType_t uxNewMaskValue )
{
    if( uxNewMaskValue == portUNMASK_VALUE )
    {
        /* Unmask all interrupt priorities. */
        portCLEAR_INTERRUPT_PRIORITIES_MASK();
    }
    else
    {
        __asm volatile (
            "SVC %0 \n"
            :
            : "i" ( portSVC_UNMASK_INTERRUPTS ), "r" ( uxNewMaskValue )
            : "memory"
        );
    }
}

void vPortClearInterruptMaskFromISR( UBaseType_t uxNewMaskValue )
{
    __asm volatile (
        "MSR DAIFSET, #2        \n"
        "DSB SY                 \n"
        "ISB SY                 \n"
        "MSR ICC_PMR_EL1, %0    \n"
        "DSB SY                 \n"
        "ISB SY                 \n"
        "MSR DAIFCLR, #2        \n"
        "DSB SY                 \n"
        "ISB SY                 \n"
        :
        : "r" ( uxNewMaskValue )
    );
}
/*-----------------------------------------------------------*/

UBaseType_t uxPortSetInterruptMask( void )
{
    UBaseType_t ullPMRValue;

    /* Use SVC so this can be called safely from EL0 tasks. */
    __asm volatile (
        "svc %1        \n"
        "mov %0, x0    \n"
        : "=r" ( ullPMRValue )
        : "i" ( portSVC_MASK_ALL_INTERRUPTS )
        : "x0", "memory"
    );

    return ullPMRValue;
}

/* EL1/ISR variant to avoid SVC from interrupt context. */
UBaseType_t uxPortSetInterruptMaskFromISR( void )
{
    UBaseType_t ullPMRValue;

    __asm volatile ( "MRS %0, ICC_PMR_EL1" : "=r" ( ullPMRValue ) );

    if( ullPMRValue != ( configMAX_API_CALL_INTERRUPT_PRIORITY << portPRIORITY_SHIFT ) )
    {
        __asm volatile ( "MSR DAIFSET, #2        \n"
                         "DSB SY                 \n"
                         "ISB SY                 \n"
                         "MSR ICC_PMR_EL1, %0    \n"
                         "DSB SY                 \n"
                         "ISB SY                 \n"
                         "MSR DAIFCLR, #2        \n"
                         "DSB SY                 \n"
                         "ISB SY                 \n"
                         ::"r" ( configMAX_API_CALL_INTERRUPT_PRIORITY << portPRIORITY_SHIFT ) : "memory" );
    }

    return ullPMRValue;
}

/*-----------------------------------------------------------*/

#if ( configASSERT_DEFINED == 1 )

    void vPortValidateInterruptPriority( void )
    {
        /* The following assertion will fail if a service routine (ISR) for
         * an interrupt that has been assigned a priority above
         * configMAX_SYSCALL_INTERRUPT_PRIORITY calls an ISR safe FreeRTOS API
         * function. ISR safe FreeRTOS API functions must *only* be called
         * from interrupts that have been assigned a priority at or below
         * configMAX_SYSCALL_INTERRUPT_PRIORITY.
         *
         * Numerically low interrupt priority numbers represent logically high
         * interrupt priorities, therefore the priority of the interrupt must
         * be set to a value equal to or numerically *higher* than
         * configMAX_SYSCALL_INTERRUPT_PRIORITY.
         *
         * FreeRTOS maintains separate thread and ISR API functions to ensure
         * interrupt entry is as fast and simple as possible. */
        uint64_t ullRunningInterruptPriority;
        __asm volatile ( "MRS %0, ICC_RPR_EL1" : "=r" ( ullRunningInterruptPriority ) );
        configASSERT( ullRunningInterruptPriority >= ( configMAX_API_CALL_INTERRUPT_PRIORITY << portPRIORITY_SHIFT ) );
    }

#endif /* configASSERT_DEFINED */

/*-----------------------------------------------------------*/

/*
 * If the application provides an implementation of vApplicationIRQHandler(),
 * then it will get called directly without saving the FPU registers on
 * interrupt entry, and this weak implementation of
 * vApplicationFPUSafeIRQHandler() is just provided to remove linkage errors -
 * it should never actually get called so its implementation contains a
 * call to configASSERT() that will always fail.
 *
 * If the application provides its own implementation of
 * vApplicationFPUSafeIRQHandler() then the implementation of
 * vApplicationIRQHandler() provided in portASM.S will save the FPU registers
 * before calling it.
 *
 * Therefore, if the application writer wants FPU registers to be saved on
 * interrupt entry their IRQ handler must be called
 * vApplicationFPUSafeIRQHandler(), and if the application writer does not want
 * FPU registers to be saved on interrupt entry their IRQ handler must be
 * called vApplicationIRQHandler().
 */
 __attribute__( ( weak ) ) void vApplicationFPUSafeIRQHandler( uint32_t ulICCIAR )
{
    ( void ) ulICCIAR;
    configASSERT( ( volatile void * ) NULL );
}

/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES > 1 )

    /* Which core owns the lock? */
    volatile uint64_t ucOwnedByCore[ portMAX_CORE_COUNT ];
    /* Lock count a core owns. */
    volatile uint64_t ucRecursionCountByLock[ eLockCount ];
    /* Index 0 is used for ISR lock and Index 1 is used for task lock. */
    uint32_t ulGateWord[ eLockCount ];

    void vInterruptCore( uint32_t ulInterruptID, uint32_t ulCoreID )
    {
        uint64_t ulRegVal = 0;
        uint32_t ulCoreMask = ( 1UL << ulCoreID );
        ulRegVal |= ( (ulCoreMask & 0xFFFF) | ( ( ulInterruptID & 0xF ) << 24U ) );
        __asm__ volatile ( "msr ICC_SGI1R_EL1, %0" : : "r" ( ulRegVal ) );
        __asm__ volatile ( "dsb sy");
        __asm__ volatile ( "isb sy");
    }

/*-----------------------------------------------------------*/

    static inline void prvSpinUnlock( uint32_t * ulLock )
    {
        __asm volatile (
            "dmb sy\n"
            "mov w1, #0\n"
            "str w1, [%x0]\n"
            "sev\n"
            "dsb sy\n"
            "isb sy\n"
            :
            : "r" ( ulLock )
            : "memory", "w1"
        );
    }

/*-----------------------------------------------------------*/

    static inline uint32_t prvSpinTrylock( uint32_t * ulLock )
    {
        register uint32_t ulRet;
        /* Try to acquire spinlock; caller is responsible for further barriers. */
        __asm volatile (
            "1:\n"
            "ldxr w1, [%x1]\n"
            "cmp w1, #1\n"
            "beq 2f\n"
            "mov w2, #1\n"
            "stxr w1, w2, [%x1]\n"
            "cmp w1, #0\n"
            "bne 1b\n"
            "2:\n"
            "mov %w0, w1\n"
            : "=r" ( ulRet )
            : "r" ( ulLock )
            : "memory", "w1", "w2"
        );

        return ulRet;
    }

/*-----------------------------------------------------------*/

    /* Read 64b value shared between cores. */
    static inline uint64_t prvGet64( volatile uint64_t * x )
    {
        __asm( "dsb sy" );
        return *x;
    }

/*-----------------------------------------------------------*/

    /* Write 64b value shared between cores. */
    static inline void prvSet64( volatile uint64_t * x,
                                 uint64_t value )
    {
        *x = value;
        __asm( "dsb sy" );
    }

/*-----------------------------------------------------------*/

    void vPortRecursiveLock( BaseType_t xCoreID,
                             ePortRTOSLock eLockNum,
                             BaseType_t uxAcquire )
    {
        /* Validate the core ID and lock number. */
        configASSERT( xCoreID < portMAX_CORE_COUNT );
        configASSERT( eLockNum < eLockCount );

        uint32_t ulLockBit = 1u << eLockNum;

        /* Lock acquire */
        if( uxAcquire )
        {
            /* Check if spinlock is available. */
            /* If spinlock is not available check if the core owns the lock. */
            /* If the core owns the lock wait increment the lock count by the core. */
            /* If core does not own the lock wait for the spinlock. */
            if( prvSpinTrylock( &ulGateWord[ eLockNum ] ) != 0 )
            {
                /* Check if the core owns the spinlock. */
                if( prvGet64( &ucOwnedByCore[ xCoreID ] ) & ulLockBit )
                {
                    configASSERT( prvGet64( &ucRecursionCountByLock[ eLockNum ] ) != 255u );
                    prvSet64( &ucRecursionCountByLock[ eLockNum ], ( prvGet64( &ucRecursionCountByLock[ eLockNum ] ) + 1 ) );
                    return;
                }

                /* Preload the gate word into the cache. */
                uint32_t dummy = ulGateWord[ eLockNum ];
                dummy++;

                while( prvSpinTrylock( &ulGateWord[ eLockNum ] ) != 0 )
                {
                    /* Follow Arm's recommended way of sleeping
                     * sevl is used to prime the wait loop,
                     * the first wfe wakes immediately as sevl has set the flag
                     * the second wfe sleeps the core. This way the core is ensured
                     * to sleep.
                     */
                    __asm volatile ( "sevl; wfe; wfe" );
                }
            }

            /* Add barrier to ensure lock is taken before we proceed. */
            __asm__ __volatile__ ( "dmb sy" ::: "memory" );

            /* Assert the lock count is 0 when the spinlock is free and is acquired. */
            configASSERT( prvGet64( &ucRecursionCountByLock[ eLockNum ] ) == 0 );

            /* Set lock count as 1. */
            prvSet64( &ucRecursionCountByLock[ eLockNum ], 1 );
            /* Set ucOwnedByCore. */
            prvSet64( &ucOwnedByCore[ xCoreID ], ( prvGet64( &ucOwnedByCore[ xCoreID ] ) | ulLockBit ) );
        }
        /* Lock release. */
        else
        {
            /* Assert the lock is not free already. */
            configASSERT( ( prvGet64( &ucOwnedByCore[ xCoreID ] ) & ulLockBit ) != 0 );
            configASSERT( prvGet64( &ucRecursionCountByLock[ eLockNum ] ) != 0 );

            /* Reduce ucRecursionCountByLock by 1. */
            prvSet64( &ucRecursionCountByLock[ eLockNum ], ( prvGet64( &ucRecursionCountByLock[ eLockNum ] ) - 1 ) );

            if( !prvGet64( &ucRecursionCountByLock[ eLockNum ] ) )
            {
                prvSet64( &ucOwnedByCore[ xCoreID ], ( prvGet64( &ucOwnedByCore[ xCoreID ] ) & ~ulLockBit ) );
                prvSpinUnlock( &ulGateWord[ eLockNum ] );
                /* Add barrier to ensure lock status is reflected before we proceed. */
                __asm__ __volatile__ ( "dmb sy" ::: "memory" );
            }
        }
    }

/*-----------------------------------------------------------*/

    BaseType_t xPortGetCoreID( void )
    {
        BaseType_t xCoreID;
        __asm volatile (
            "svc %1             \n"
            "mov %0, x0         \n"
            : "=r" ( xCoreID )
            : "i" ( portSVC_GET_CORE_ID )
            : "x0", "memory"
        );
        return xCoreID;
    }

/*-----------------------------------------------------------*/

    void FreeRTOS_SGI_Handler( void )
    {
        /* Must be the lowest possible priority. */
        uint64_t ullRunningInterruptPriority;
        __asm volatile ( "MRS %0, ICC_RPR_EL1" : "=r" ( ullRunningInterruptPriority ) );

        configASSERT( ullRunningInterruptPriority == ( portLOWEST_USABLE_INTERRUPT_PRIORITY << portPRIORITY_SHIFT ) );
        /* Interrupts should not be enabled before this point. */
        #if ( configASSERT_DEFINED == 1 )
        {
            uint64_t ullMaskBits;

            __asm volatile ( "mrs %0, DAIF" : "=r" ( ullMaskBits )::"memory" );
            configASSERT( ( ullMaskBits & portDAIF_I ) != 0 );
        }
        #endif /* configASSERT_DEFINED */

        /* Set interrupt mask before altering scheduler structures.   The SGI
         * handler runs at the lowest priority, so interrupts cannot already be masked,
         * so there is no need to save and restore the current mask value.  It is
         * necessary to turn off interrupts in the CPU itself while the ICCPMR is being
         * updated. */
        __asm volatile ( "MSR ICC_PMR_EL1, %0      \n"
                        "DSB SY                    \n"
                        "ISB SY                    \n"
                        ::"r" ( configMAX_API_CALL_INTERRUPT_PRIORITY << portPRIORITY_SHIFT ) : "memory" );

        /* Ok to enable interrupts after the interrupt source has been cleared. */
        __asm volatile ( "MSR DAIFCLR, #2\n"
                         "DSB SY\n"
                         "ISB SY\n" ::: "memory" );

        #if ( configNUMBER_OF_CORES == 1 )
            ullPortYieldRequired = pdTRUE;
        #else
            ullPortYieldRequired[ portGET_CORE_ID() ] = pdTRUE;
        #endif

        /* Ensure all interrupt priorities are active again. */
        portCLEAR_INTERRUPT_PRIORITIES_MASK();
    }

/*-----------------------------------------------------------*/

#endif /* if( configNUMBER_OF_CORES > 1 ) */
