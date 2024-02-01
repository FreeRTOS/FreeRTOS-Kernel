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

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
 * all the API functions to use the MPU wrappers. That should only be done when
 * task.h is included from an application file. */
#ifndef MPU_WRAPPERS_INCLUDED_FROM_API_FILE
    #define MPU_WRAPPERS_INCLUDED_FROM_API_FILE
#endif /* MPU_WRAPPERS_INCLUDED_FROM_API_FILE */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "portmacro.h"
#include "task.h"
#include "mpu_syscall_numbers.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/**
 * @brief Variable used to keep track of critical section nesting.
 * @ingroup Critical Sections
 * @note
 * This variable has to be stored as part of the task context and must be
 * initialised to a non zero value to ensure interrupts don't inadvertently
 * become unmasked before the scheduler starts. As it is stored as part of the
 * task context it will be set to 0 when the first task is started.
 */
PRIVILEGED_DATA volatile UBaseType_t ulCriticalNesting = 0xFFFF;

/** @brief Set to 1 to pend a context switch from an ISR.
 * @ingroup Interrupt Management
 */
PRIVILEGED_DATA volatile UBaseType_t ulPortYieldRequired = pdFALSE;

/**
 * @brief Interrupt nesting depth, used to count the number of interrupts to unwind.
 * @ingroup Interrupt Management
 */
PRIVILEGED_DATA volatile UBaseType_t ulPortInterruptNesting = 0UL;

/**
 * @brief Variable to track whether or not the scheduler has been started.
 * @ingroup Scheduler
 * @note This is the port specific version of the Kernel's xSchedulerRunning
 */
PRIVILEGED_DATA static BaseType_t prvPortSchedulerRunning = pdFALSE;

/* -------------------------- Private Function Declarations -------------------------- */

/**
 * @brief Determine if a FreeRTOS Task has been granted access to a memory region.
 *
 * @param xTaskMPURegion Pointer to a single set of MPU region registers.
 * @param ulRegionStart Base address of the memory region access is being requested.
 * @param ulRegionLength The length of the memory region that access is being requested.
 * @param ulAccessRequested The type of access being requested, either read or write.
 * @return BaseType_t pdTRUE if the task can access the region, pdFALSE otherwise
 *
 * @ingroup Task Context
 * @ingroup MPU Control
 */
PRIVILEGED_FUNCTION static BaseType_t prvTaskCanAccessRegion(
    const xMPU_REGION_REGISTERS * xTaskMPURegion,
    const uint32_t ulRegionStart,
    const uint32_t ulRegionLength,
    const uint32_t ulAccessRequested
);

/**
 * @brief Determine smallest MPU Region Setting for a number of bytes.
 *
 * @ingroup MPU Control
 *
 * @param ulActualSizeInBytes Number of bytes to find a valid MPU region size for.
 * @return uint32_t The smallest MPU region size that can hold the requested bytes.
 */
PRIVILEGED_FUNCTION static uint32_t prvGetMPURegionSizeSetting(
    uint32_t ulActualSizeInBytes
);

/** @brief Set up a default MPU memory Map
 * @return PRIVILEGED_FUNCTION VOID
 * @ingroup MPU Control
 * @note This function shall be called before calling vPortStartFirstTask().
 * @note This function works by pulling variables from the linker script.
 * Ensure that the variables used in your linker script match up with the variable names
 * used at the start of this function.
 */
PRIVILEGED_FUNCTION static void prvSetupMPU( void );

/**
 * @brief Determine if a FreeRTOS Task has been granted access to a memory region.
 *
 * @param xTaskMPURegion Pointer to a single set of MPU region registers.
 * @param ulRegionStart Base address of the memory region access is being requested.
 * @param ulRegionLength The length of the memory region that access is being requested.
 * @param ulAccessRequested The type of access being requested, either read or write.
 * @return BaseType_t pdTRUE if the task can access the region, pdFALSE otherwise
 *
 * @ingroup Task Context
 * @ingroup MPU Control
 */
PRIVILEGED_FUNCTION static BaseType_t prvTaskCanAccessRegion(
    const xMPU_REGION_REGISTERS * xTaskMPURegion,
    const uint32_t ulRegionStart,
    const uint32_t ulRegionLength,
    const uint32_t ulAccessRequested
);

/* ----------------------------------------------------------------------------------- */

/**
 * @brief Set a FreeRTOS Task's initial context.
 *
 * @param pxTopOfStack Pointer to where the task's stack starts.
 * @param pxCode Pointer to the function a task will run.
 * @param pvParameters Pointer to any arguments to be passed to the task's function.
 * @param xRunPrivileged Marks if the task is to be run in a privileged CPU mode.
 * @param xMPUSettings MPU settings to be loaded as part of a task's context.
 * @return StackType_t* Pointer to where to restore the task's context from.
 *
 * @ingroup Task Context
 * @note pxTopOfStack must be a region of memory that is a valid MPU region size.
 */
/* PRIVILEGED_FUNCTION */ StackType_t * pxPortInitialiseStack(
    StackType_t * pxTopOfStack,
    TaskFunction_t pxCode,
    void * pvParameters,
    BaseType_t xRunPrivileged,
    xMPU_SETTINGS * xMPUSettings
)
{
    /** Setup the initial context of the task. The context is set exactly as
     * expected by the portRESTORE_CONTEXT() macro and as described above the
     * MAX_CONTEXT_SIZE declaration in portmacro_asm.h  */
    UBaseType_t ulIndex = MAX_CONTEXT_SIZE - 1U;

    xSYSTEM_CALL_STACK_INFO * xSysCallInfo = NULL;

    if( pdTRUE == xRunPrivileged )
    {
        /* Current Program Status Register (CPSR) */
        xMPUSettings->ulTaskFlags |= portTASK_IS_PRIVILEGED_FLAG;
        xMPUSettings->ulContext[ ulIndex ] = SYS_MODE;
    }
    else
    {
        /* Current Program Status Register (CPSR) */
        xMPUSettings->ulTaskFlags &= ( ~portTASK_IS_PRIVILEGED_FLAG );
        xMPUSettings->ulContext[ ulIndex ] = USER_MODE;
    }

    if( 0x0UL != ( ( uint32_t ) pxCode & portTHUMB_MODE_ADDRESS ) )
    {
        /* The task will start in THUMB mode, set the bit in the CPSR. */
        xMPUSettings->ulContext[ ulIndex ] |= portTHUMB_MODE_BIT;
    }

    /* Decrement ulIndex here after setting the CPSR */
    ulIndex--;

    /** Set Task Program Counter to provided Task Function */
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) pxCode;
    ulIndex--;

    /** A FreeRTOS Task is not designed to return or exit from its function.
     * As such a default Link Register is provided that will return to an
     * error handling function. */
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) portTASK_RETURN_ADDRESS;
    ulIndex--;

    /** CPU Stack Grows up, set Task's Stack Pointer's to bottom of stack */
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) pxTopOfStack; /* SP */
    ulIndex--;

    /* Next the General Purpose Registers */
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x12121212;   /* R12 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x11111111;   /* R11 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x10101010;   /* R10 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x09090909;   /* R9 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x08080808;   /* R8 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x07070707;   /* R7 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x06060606;   /* R6 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x05050505;   /* R5 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x04040404;   /* R4 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x03030303;   /* R3 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x02020202;   /* R2 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0x01010101;   /* R1 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) pvParameters; /* R0 */
    ulIndex--;

#ifdef portENABLE_FPU
    /* Initial Floating Point Context is the Floating Point Registers (FPRs) */
    /* There are 16 Double FPRs, D0-D15 on the Cortex-R FPU enabled chips */
    /* These map to the Single Precision FPRs, S0-S31 */
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000015; /* S31 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD1500000; /* S30 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000014; /* S29 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD1400000; /* S28 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000013; /* S27 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD1300000; /* S26 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000012; /* S25 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD1200000; /* S24 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000011; /* S23 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD1100000; /* S22 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000010; /* S21 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD1000000; /* S20 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000009; /* S19 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD9000000; /* S18 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000008; /* S17 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD8000000; /* S16 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000007; /* S15 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD7000000; /* S14 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000006; /* S13 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD6000000; /* S12 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000005; /* S11 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD5000000; /* S10 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000004; /* S9 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD4000000; /* S8 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000003; /* S7 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD3000000; /* S6 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000002; /* S5 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD2000000; /* S4 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000001; /* S3 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD1000000; /* S2 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000000; /* S1 */
    ulIndex--;
    xMPUSettings->ulContext[ ulIndex ] = ( StackType_t ) 0xD0000000; /* S0 */
    ulIndex--;

    /* Floating Point Status and Control Register */
    xMPUSettings->ulContext[ ulIndex-- ] = ( StackType_t ) 0x00000000; /* FPSR */
#endif /* portENABLE_FPU */

    /* The task will start with a critical nesting count of 0. */
    xMPUSettings->ulContext[ ulIndex ] = portNO_CRITICAL_NESTING;

    /* Ensure that the system call stack is double word aligned. */
    xSysCallInfo = &( xMPUSettings->xSystemCallStackInfo );
    xSysCallInfo->pulSystemCallStackPointer = &(
        xSysCallInfo->ulSystemCallStackBuffer[ configSYSTEM_CALL_STACK_SIZE - 1U ]
    );

    xSysCallInfo->pulSystemCallStackPointer =
        ( uint32_t * ) ( ( uint32_t ) ( xSysCallInfo->pulSystemCallStackPointer ) & ( uint32_t ) ( ~( portBYTE_ALIGNMENT_MASK ) ) );

    /* This is not NULL only for the duration of a system call. */
    xSysCallInfo->pulTaskStackPointer = NULL;

    /* Set the System Call LR to go directly to vPortSystemCallExit */
    xSysCallInfo->pulSystemCallLinkRegister = &vPortSystemCallExit;

    /* Return the address where the context of this task should be restored from */
    return ( &xMPUSettings->ulContext[ ulIndex ] );
}

/*----------------------------------------------------------------------------*/

/* PRIVILEGED_FUNCTION */ static uint32_t prvGetMPURegionSizeSetting(
    uint32_t ulActualSizeInBytes
)
{
    uint32_t ulRegionSize, ulReturnValue = 4U;

    /* 32 bytes is the smallest valid region for Cortex R4 and R5 CPUs */
    for( ulRegionSize = 0x20UL; ulReturnValue < 0x1FUL; ( ulRegionSize <<= 1UL ) )
    {
        if( ulActualSizeInBytes <= ulRegionSize )
        {
            break;
        }
        else
        {
            ulReturnValue++;
        }
    }

    /* Shift the code by one before returning so it can be written directly
     * into the the correct bit position of the attribute register. */
    return ulReturnValue << 1UL;
}

/*----------------------------------------------------------------------------*/

/**
 * @brief Stores a FreeRTOS Task's MPU Settings in its TCB.
 *
 * @param xMPUSettings The memory location in the TCB to store MPU settings
 * @param xRegions The MPU settings being requested by the task.
 * @param pxBottomOfStack The base address of the Task's Stack
 * @param ulStackDepth The length of the task's stack.
 *
 * @ingroup Task Context
 * @ingroup MPU Control
 *
 * @note pxBottomOfStack must be aligned to a region size of length ulStackDepth.
 * @note ulStackDepth must be a power of 2 larger than 32 bytes.
 */
/* PRIVILEGED_FUNCTION */ void vPortStoreTaskMPUSettings(
    xMPU_SETTINGS * xMPUSettings,
    const struct xMEMORY_REGION * const xRegions,
    StackType_t * pxBottomOfStack,
    uint32_t ulStackDepth
)
{
#if defined( __ARMCC_VERSION )

    /* Declaration when these variable are defined in code instead of being
     * exported from linker scripts. */
    extern uint32_t * __SRAM_segment_start__;
    extern uint32_t * __SRAM_segment_end__;
#else
    /* Declaration when these variable are exported from linker scripts. */
    extern uint32_t __SRAM_segment_start__[];
    extern uint32_t __SRAM_segment_end__[];

#endif /* if defined( __ARMCC_VERSION ) */
    uint32_t ulIndex = 0x0;
    uint32_t ulRegionStart;
    uint32_t ulRegionEnd;
    uint32_t ulRegionLen;
    uint32_t ulAlignment;

    /* Allow Read/Write from User and Privileged modes */
    uint32_t ulRegionAttr = portMPU_PRIV_RW_USER_RW_NOEXEC |
                            portMPU_NORMAL_OIWTNOWA_SHARED;

    if( NULL == xRegions )
    {
        /* No MPU regions are specified so allow access to all of the RAM. */
        ulRegionStart = ( uint32_t ) __SRAM_segment_start__;
        ulRegionEnd = ( uint32_t ) __SRAM_segment_end__;
        ulRegionLen = ulRegionEnd - ulRegionStart;
        ulRegionLen = prvGetMPURegionSizeSetting( ulRegionLen );
        ulRegionLen |= portMPU_REGION_ENABLE;

        /* MPU Settings is zero'd out in the TCB before reaching this function.
         * Set this region as the highest configurable MPU Region so it overrides
         * the lower unused regions.
         */
        ulIndex = portNUM_CONFIGURABLE_REGIONS;

        xMPUSettings->xRegion[ ulIndex ].ulRegionBaseAddress = ulRegionStart;
        xMPUSettings->xRegion[ ulIndex ].ulRegionSize = ulRegionLen;
        xMPUSettings->xRegion[ ulIndex ].ulRegionAttribute = ulRegionAttr;
    }
    else
    {
        for( ulIndex = 0UL; ulIndex < portNUM_CONFIGURABLE_REGIONS; ulIndex++ )
        {
            /* If a length has been provided, the region is in use. */
            if( ( xRegions[ ulIndex ] ).ulLengthInBytes > 0UL )
            {
                ulRegionStart = ( uint32_t ) xRegions[ ulIndex ].pvBaseAddress;
                ulRegionAttr = xRegions[ ulIndex ].ulParameters;

                ulRegionLen = xRegions[ ulIndex ].ulLengthInBytes;
                ulRegionLen = prvGetMPURegionSizeSetting( ulRegionLen );
                ulRegionLen |= portMPU_REGION_ENABLE;

                /* MPU Regions must be aligned to a power of 2 equal to length */
                ulAlignment = 2UL << ( ulRegionLen >> 1UL );
                configASSERT( 0U == ( ulRegionStart % 2UL ) );
                configASSERT( 0U == ( ulRegionStart % ( ulAlignment ) ) );
            }
            else
            {
                /* Otherwise ensure the region is zero'd out */
                ulRegionStart = 0x0UL;
                ulRegionLen = 0x0UL;
                ulRegionAttr = 0x0UL;
            }

            xMPUSettings->xRegion[ ulIndex ].ulRegionBaseAddress = ulRegionStart;
            xMPUSettings->xRegion[ ulIndex ].ulRegionSize = ulRegionLen;
            xMPUSettings->xRegion[ ulIndex ].ulRegionAttribute = ulRegionAttr;
        }
        /* This function is called automatically when the task is created - in
         * which case the stack region parameters will be valid. At all other
         * times the stack parameters will not be valid and it is assumed that the
         * stack region has already been configured. */

        /* Cannot have a task stack of size 0 */
        if( 0x0UL != ulStackDepth )
        {
            /* Define the region that allows access to the stack. */
                ulRegionStart = ( uint32_t ) pxBottomOfStack;
                ulRegionAttr = portMPU_PRIV_RW_USER_RW_NOEXEC |
                                 portMPU_NORMAL_OIWTNOWA_SHARED;
                ulRegionLen = prvGetMPURegionSizeSetting( ulStackDepth << 2UL );
                ulRegionLen |= portMPU_REGION_ENABLE;

                /* MPU Regions must be aligned to a power of 2 equal to length */
                ulAlignment = 2UL << ( ulRegionLen >> 1UL );
                configASSERT( 0U == ( ulRegionStart % 2UL ) );
                configASSERT( 0U == ( ulRegionStart % ( ulAlignment ) ) );

                /* xRegion[portNUM_CONFIGURABLE_REGIONS] is the Task Stack */
                ulIndex = portNUM_CONFIGURABLE_REGIONS;

                xMPUSettings->xRegion[ ulIndex ].ulRegionBaseAddress = ulRegionStart;
                xMPUSettings->xRegion[ ulIndex ].ulRegionSize = ulRegionLen;
                xMPUSettings->xRegion[ ulIndex ].ulRegionAttribute = ulRegionAttr;
        }
    }
}

/*----------------------------------------------------------------------------*/

/* PRIVILEGED_FUNCTION */ static void prvSetupMPU( void )
{
#if defined( __ARMCC_VERSION )
    /* Declaration when these variable are defined in code. */
    /* Sections used for FLASH */
    extern uint32_t * __FLASH_segment_start__;
    extern uint32_t * __FLASH_segment_end__;
    extern uint32_t * __privileged_functions_start__;
    extern uint32_t * __privileged_functions_end__;

    /* Sections used for RAM */
    extern uint32_t * __SRAM_segment_start__;
    extern uint32_t * __SRAM_segment_end__;
    extern uint32_t * __privileged_data_start__;
    extern uint32_t * __privileged_data_end__;

#else
    /* Declaration when these variable are exported from linker scripts. */
    /* Sections used for FLASH */
    extern uint32_t __FLASH_segment_start__[];
    extern uint32_t __FLASH_segment_end__[];
    extern uint32_t __privileged_functions_start__[];
    extern uint32_t __privileged_functions_end__[];

    /* Sections used for RAM */
    extern uint32_t __SRAM_segment_start__[];
    extern uint32_t __SRAM_segment_end__[];
    extern uint32_t __privileged_data_start__[];
    extern uint32_t __privileged_data_end__[];

#endif /* if defined( __ARMCC_VERSION ) */
    uint32_t ulRegionStart;
    uint32_t ulRegionEnd;
    uint32_t ulRegionLength;

    /* Ensure the MPU is disabled */
    vMPUDisable();

    /* Unprivileged and Privileged Read and Exec MPU Region for Flash */
    ulRegionStart = ( uint32_t ) __FLASH_segment_start__;
    ulRegionEnd = ( uint32_t ) __FLASH_segment_end__;
    ulRegionLength = ulRegionEnd - ulRegionStart;
    ulRegionLength = prvGetMPURegionSizeSetting( ulRegionLength );
    ulRegionLength |= portMPU_REGION_ENABLE;

    vMPUSetRegion(
        portUNPRIVILEGED_FLASH_REGION,
        ulRegionStart,
        ulRegionLength,
        portMPU_PRIV_RO_USER_RO_EXEC | portMPU_NORMAL_OIWTNOWA_SHARED
    );

    /* Privileged Read and Exec MPU Region for PRIVILEGED_FUNCTIONS. */
    ulRegionStart = ( uint32_t ) __privileged_functions_start__;
    ulRegionEnd = ( uint32_t ) __privileged_functions_end__;
    ulRegionLength = ulRegionEnd - ulRegionStart;
    ulRegionLength = prvGetMPURegionSizeSetting( ulRegionLength );
    ulRegionLength |= portMPU_REGION_ENABLE;

    vMPUSetRegion(
        portPRIVILEGED_FLASH_REGION,
        ulRegionStart,
        ulRegionLength,
        portMPU_PRIV_RO_USER_NA_EXEC | portMPU_NORMAL_OIWTNOWA_SHARED
    );

    /* Privileged Write and Read Access for PRIVILEGED_DATA. */
    ulRegionStart = ( uint32_t ) __privileged_data_start__;
    ulRegionEnd = ( uint32_t ) __privileged_data_end__;
    ulRegionLength = ulRegionEnd - ulRegionStart;
    ulRegionLength = prvGetMPURegionSizeSetting( ulRegionLength );
    ulRegionLength |= portMPU_REGION_ENABLE;

    vMPUSetRegion(
        portPRIVILEGED_RAM_REGION,
        ulRegionStart,
        ulRegionLength,
        portMPU_PRIV_RW_USER_NA_NOEXEC | portMPU_NORMAL_OIWTNOWA_SHARED
    );

    /* Enable the MPU Background region, allows privileged operating modes access to
     * unmapped regions of memory without generating a fault. */
    vMPUEnableBackgroundRegion();

    /* After setting default regions, enable the MPU */
    vMPUEnable();
}

/* ----------------------------------------------------------------------------------- */

/* PRIVILEGED_FUNCTION */ static BaseType_t prvTaskCanAccessRegion(
    const xMPU_REGION_REGISTERS * xTaskMPURegion,
    const uint32_t ulRegionStart,
    const uint32_t ulRegionLength,
    const uint32_t ulAccessRequested
)
{
    BaseType_t xAccessGranted;
    uint32_t ulRegionEnd = ulRegionStart + ulRegionLength;

    /* Get Region Size value in words, need to clear the enable bit */
    uint32_t ulTaskRegionLength = 2UL << ( xTaskMPURegion->ulRegionSize >> 1UL );
    uint32_t ulTaskRegionEnd = xTaskMPURegion->ulRegionBaseAddress + ulTaskRegionLength;

    /* Perform three different checks:
     * 1. Ensure region being accessed is after the start of an MPU Region
     * 2. Ensure region being accessed is before the end of the MPU Region
     * 3. Ensure region being accessed ends after the start of the MPU region */
    if( ( ulRegionStart >= xTaskMPURegion->ulRegionBaseAddress ) &&
        ( ulRegionEnd <= ulTaskRegionEnd ) && ( ulRegionEnd >= ulRegionStart ) )
    {
        /* Unprivileged read is MPU Ctrl Access Bit Value bX1X */
        if( ( tskMPU_READ_PERMISSION == ulAccessRequested ) &&
            ( ( portMPU_PRIV_RW_USER_RO_NOEXEC ) &xTaskMPURegion->ulRegionAttribute ) )
        {
            xAccessGranted = pdTRUE;
        }

        /* Unprivileged Write is MPU Ctrl Access Bit Value b011 */
        else if( ( tskMPU_WRITE_PERMISSION & ulAccessRequested ) &&
                ( portMPU_PRIV_RW_USER_RW_NOEXEC ==
                ( portMPU_PRIV_RW_USER_RW_NOEXEC & xTaskMPURegion->ulRegionAttribute ) ) )
        {
            xAccessGranted = pdTRUE;
        }

        else
        {
            xAccessGranted = pdFALSE;
        }
    }
    else
    {
        xAccessGranted = pdFALSE;
    }

    return xAccessGranted;
}

/* ------------------------------------------------------------------------- */

/* PRIVILEGED_FUNCTION */ BaseType_t xPortIsAuthorizedToAccessBuffer(
    const void * pvBuffer,
    uint32_t ulBufferLength,
    uint32_t ulAccessRequested
)
{
    BaseType_t xAccessGranted;

    /* Calling task's MPU settings. */
    xMPU_SETTINGS * xTaskMPUSettings = NULL;
    xMPU_REGION_REGISTERS * xTaskMPURegion = NULL;

    if( pdFALSE == prvPortSchedulerRunning )
    {
        /* Before the scheduler starts an unknown task will be pxCurrentTCB */
        xAccessGranted = pdTRUE;
    }
    else
    {
        /* Only way to receive a NULL here is if no task has been created,
         * but the scheduler has been started. */
        xTaskMPUSettings = xTaskGetMPUSettings( NULL );

        if( xTaskMPUSettings->ulTaskFlags & portTASK_IS_PRIVILEGED_FLAG )
        {
            /* If a task is privileged it is assumed that it can access the buffer */
            xAccessGranted = pdTRUE;
        }
        else
        {
            uint32_t ulRegionIndex = 0x0UL;
            do
            {
                xTaskMPURegion = &( xTaskMPUSettings->xRegion[ ulRegionIndex++ ] );
                xAccessGranted = prvTaskCanAccessRegion(
                    xTaskMPURegion,
                    ( uint32_t ) pvBuffer,
                    ulBufferLength,
                    ulAccessRequested
                );
            } while( ( pdFALSE == xAccessGranted ) &&
                     ( ulRegionIndex < portTOTAL_NUM_REGIONS_IN_TCB ) );
        }
    }
    return xAccessGranted;
}

/*---------------------------------------------------------------------------*/

/**
 * @brief Determine if the FreeRTOS Task was created as a privileged task.
 *
 * @ingroup MPU Control
 * @ingroup Task Context
 *
 * @return pdTRUE if the Task was created as a privileged task.
 * pdFALSE if the task was not created as a privileged task.
 *
 */
/* PRIVILEGED_FUNCTION */ BaseType_t xPortIsTaskPrivileged( void )
{
    BaseType_t xTaskIsPrivileged = pdFALSE;

    /* Calling task's MPU settings. */
    const xMPU_SETTINGS * xTaskMpuSettings = xTaskGetMPUSettings( NULL );

    if( ( xTaskMpuSettings->ulTaskFlags & portTASK_IS_PRIVILEGED_FLAG ) ==
        portTASK_IS_PRIVILEGED_FLAG )
    {
        xTaskIsPrivileged = pdTRUE;
    }

    return xTaskIsPrivileged;
}

/**
 * @brief Start the System Tick Timer, starting the FreeRTOS-Kernel.
 *
 * @ingroup Scheduler
 * @return BaseType_t This function is not meant to be returned from.
 * If it does return it returns pdFALSE to mark that the scheduler could not be started.
 */
/* PRIVILEGED_FUNCTION */ BaseType_t xPortStartScheduler( void )
{
    /* Start the timer that generates the tick ISR. */
    configSETUP_TICK_INTERRUPT();

    /* Reset the critical section nesting count read to execute the first task. */
    ulCriticalNesting = 0UL;

    /* Configure the regions in the MPU that are common to all tasks. */
    prvSetupMPU();

    /* Mark the port specific scheduler running variable as true */
    prvPortSchedulerRunning = pdTRUE;

    /* Load the context of the first task, starting the FreeRTOS-Scheduler's control. */
    vPortStartFirstTask();

    /* Will only get here if vTaskStartScheduler() was called with the CPU in
     * a non-privileged mode or the binary point register was not set to its lowest
     * possible value. prvTaskExitError() is referenced to prevent a compiler
     * warning about it being defined but not referenced in the case that the user
     * defines their own exit address. */
    ( void ) prvTaskExitError();
    return pdFALSE;
}
/*---------------------------------------------------------------------------*/

#if( configENABLE_ACCESS_CONTROL_LIST == 1 )

/* PRIVILEGED_FUNCTION */ BaseType_t xPortIsAuthorizedToAccessKernelObject(
    int32_t lInternalIndexOfKernelObject
)
{
    uint32_t ulAccessControlListEntryIndex, ulAccessControlListEntryBit;
    BaseType_t xAccessGranted = pdFALSE;
    const xMPU_SETTINGS * xTaskMpuSettings;

    if( pdFALSE == prvPortSchedulerRunning )
    {
        /* Grant access to all the kernel objects before the scheduler
         * is started. It is necessary because there is no task running
         * yet and therefore, we cannot use the permissions of any
         * task. */
        xAccessGranted = pdTRUE;
    }
    else
    {
        xTaskMpuSettings = xTaskGetMPUSettings( NULL ); /* Calling task's MPU settings. */

        ulAccessControlListEntryIndex =
            ( ( uint32_t ) lInternalIndexOfKernelObject / portACL_ENTRY_SIZE_BITS );
        ulAccessControlListEntryBit =
            ( ( uint32_t ) lInternalIndexOfKernelObject % portACL_ENTRY_SIZE_BITS );

        if( ( xTaskMpuSettings->ulTaskFlags & portTASK_IS_PRIVILEGED_FLAG ) ==
            portTASK_IS_PRIVILEGED_FLAG )
        {
            xAccessGranted = pdTRUE;
        }
        else
        {
            if( ( xTaskMpuSettings->ulAccessControlList[ ulAccessControlListEntryIndex ] &
                  ( 1U << ulAccessControlListEntryBit ) ) != 0 )
            {
                xAccessGranted = pdTRUE;
            }
        }
    }

    return xAccessGranted;
}

/* PRIVILEGED_FUNCTION */ void vPortGrantAccessToKernelObject(
    TaskHandle_t xInternalTaskHandle,
    int32_t lInternalIndexOfKernelObject
)
{
    uint32_t ulAccessControlListEntryIndex, ulAccessControlListEntryBit;
    xMPU_SETTINGS * xTaskMpuSettings;

    ulAccessControlListEntryIndex =
        ( ( uint32_t ) lInternalIndexOfKernelObject / portACL_ENTRY_SIZE_BITS );
    ulAccessControlListEntryBit =
        ( ( uint32_t ) lInternalIndexOfKernelObject % portACL_ENTRY_SIZE_BITS );

    xTaskMpuSettings = xTaskGetMPUSettings( xInternalTaskHandle );

    xTaskMpuSettings->ulAccessControlList
        [ ulAccessControlListEntryIndex ] |= ( 1U << ulAccessControlListEntryBit );
}

/* PRIVILEGED_FUNCTION */ void vPortRevokeAccessToKernelObject(
    TaskHandle_t xInternalTaskHandle,
    int32_t lInternalIndexOfKernelObject
)
{
    uint32_t ulAccessControlListEntryIndex, ulAccessControlListEntryBit;
    xMPU_SETTINGS * xTaskMpuSettings;

    ulAccessControlListEntryIndex =
        ( ( uint32_t ) lInternalIndexOfKernelObject / portACL_ENTRY_SIZE_BITS );
    ulAccessControlListEntryBit =
        ( ( uint32_t ) lInternalIndexOfKernelObject % portACL_ENTRY_SIZE_BITS );

    xTaskMpuSettings = xTaskGetMPUSettings( xInternalTaskHandle );

    xTaskMpuSettings->ulAccessControlList[ ulAccessControlListEntryIndex ] &= ~(
        1U << ulAccessControlListEntryBit
    );
}

#else

/* PRIVILEGED_FUNCTION */ BaseType_t xPortIsAuthorizedToAccessKernelObject(
    int32_t lInternalIndexOfKernelObject
)
{
    ( void ) lInternalIndexOfKernelObject;

    /* If Access Control List feature is not used, all the tasks have
     * access to all the kernel objects. */
    return pdTRUE;
}

#endif /* #if ( configENABLE_ACCESS_CONTROL_LIST == 1 ) */

/*---------------------------------------------------------------------------*/

void prvTaskExitError( void )
{
    /* A function that implements a task must not exit or attempt to return to
     * its caller as there is nothing to return to. If a task wants to exit it
     * should instead call vTaskDelete( NULL ).
     *
     * Artificially force an assert() to be triggered if configASSERT() is
     * defined, then stop here so application writers can catch the error. */
    configASSERT( ulPortInterruptNesting == ~0UL );

    for( ;; )
    {
    }
}

/*---------------------------------------------------------------------------*/

/**
 * @brief Function meant to end the FreeRTOS Scheduler, not implemented on this port.
 * @ingroup Scheduler
 */
void vPortEndScheduler( void )
{
    prvPortSchedulerRunning = pdFALSE;
    /* Not implemented in ports where there is nothing to return to.
     * Artificially force an assert. */
    configASSERT( prvPortSchedulerRunning );
}

/*---------------------------------------------------------------------------*/
