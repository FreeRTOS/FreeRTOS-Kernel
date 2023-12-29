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
#include "FreeRTOSConfig.h"
#include "FreeRTOS.h"
#include "portmacro_asm.h"
#include "portmacro.h"
#include "task.h"
#include "mpu_syscall_numbers.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/** @brief Variable used to keep track of critical section nesting.
 * @ingroup Critical Sections
 * @note
 * This variable has to be stored as part of the task context and must be
 * initialised to a non zero value to ensure interrupts don't inadvertently
 * become unmasked before the scheduler starts. As it is stored as part of the
 * task context it will be set to 0 when the first task is started.
 */
PRIVILEGED_DATA volatile uint32_t ulCriticalNesting = 0xFFFF;

/** @brief Set to 1 to pend a context switch from an ISR.
 * @ingroup Interrupt Management
 */
PRIVILEGED_DATA volatile uint32_t ulPortYieldRequired = pdFALSE;

/** @brief Interrupt nesting depth, used to count the number of interrupts to unwind.
 * @ingroup Interrupt Management
 */
PRIVILEGED_DATA volatile uint32_t ulPortInterruptNesting = 0UL;

/** @brief Variable to track whether or not the scheduler has been started.
 * @ingroup Scheduler
 * @note This variable is set to pdTRUE when the scheduler is started.
 */
PRIVILEGED_DATA static BaseType_t xSchedulerRunning = pdFALSE;

/** @brief Used in portASM.S's IRQ Handler to clear an interrupt.
 * @ingroup Interrupt Management
 */
PRIVILEGED_DATA volatile uint32_t ulICCEOIR = configEOI_ADDRESS;

/*---------------------------------------------------------------------------*/

/** @brief Set a FreeRTOS Task's initial context
 *
 * @param pxTopOfStack Pointer to where the task's stack starts
 * @param pxCode Pointer to the function a task will run
 * @param pvParameters Pointer to any arguments to be passed to the task's function
 * @param xRunPrivileged Marks if the task is to be run in a privileged CPU mode.
 * @param xMPUSettings MPU settings to be loaded as part of a task's context
 * @return StackType_t* Pointer to where to restore the task's context from.
 *
 * @ingroup Task Context
 * @note pxTopOfStack must be a region of memory that is a valid MPU region size.
 */
StackType_t * pxPortInitialiseStack(
    StackType_t * pxTopOfStack,
    TaskFunction_t pxCode,
    void * pvParameters,
    BaseType_t xRunPrivileged,
    xMPU_SETTINGS * xMPUSettings
) /* PRIVILEGED_FUNCTION */
{
    /** Setup the initial context of the task. The context is set exactly as
     * expected by the portRESTORE_CONTEXT() macro. */
    UBaseType_t ulContextIndex = MAX_CONTEXT_SIZE - 1U;

    /* These two locations are used for SVC entry, fill them for debugging */
    xMPUSettings->ulContext[ ulContextIndex-- ] = 0xFEED2002;
    xMPUSettings->ulContext[ ulContextIndex-- ] = 0xFEED1001;

    if( xRunPrivileged == pdTRUE )
    {
        /* Current Program Status and Control Register */
        xMPUSettings->ulTaskFlags |= portTASK_IS_PRIVILEGED_FLAG;
        xMPUSettings->ulTaskFlags |= 0x1F000000;
        xMPUSettings->ulContext[ ulContextIndex ] = SYS_MODE;
    }
    else
    {
        /* Current Program Status and Control Register */
        xMPUSettings->ulTaskFlags &= ( ~portTASK_IS_PRIVILEGED_FLAG );
        xMPUSettings->ulTaskFlags |= 0x10000000;
        xMPUSettings->ulContext[ ulContextIndex ] = USER_MODE;
    }

    if( ( ( uint32_t ) pxCode & portTHUMB_MODE_ADDRESS ) != 0x00UL )
    {
        /* The task will start in THUMB mode, set the bit in the CPSR. */
        xMPUSettings->ulContext[ ulContextIndex ] |= portTHUMB_MODE_BIT;
        xMPUSettings->ulTaskFlags |= portSTACK_FRAME_HAS_PADDING_FLAG;
    }

    /* Decrement ulContextIndex here after setting the CPSR */
    ulContextIndex--;

    /** First we load the Memory Location of the Task's function.
     * Task Program Counter */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) pxCode;

    /** A FreeRTOS Task is not designed to return or exit from its function.
     * As such a default Link Register is provided that will return to an
     * error handling function.
     * Task Link Register */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) portTASK_RETURN_ADDRESS;

    /** Set the task's stack pointer to be the bottom of it's stack, since on this
     * CPU stacks grow upwards.
     * Task Stack Pointer */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) pxTopOfStack; /* SP */

    /* Next the General Purpose Registers */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x12121212;   /* R12 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x11111111;   /* R11 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x10101010;   /* R10 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x09090909;   /* R9 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x08080808;   /* R8 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x07070707;   /* R7 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x06060606;   /* R6 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x05050505;   /* R5 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x04040404;   /* R4 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x03030303;   /* R3 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x02020202;   /* R2 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x01010101;   /* R1 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) pvParameters; /* R0 */

#ifdef portENABLE_FPU
    /* Initial Floating Point Context is the Floating Point Registers (FPRs) */
    /* There are 16 Double FPRs, D0-D15 on the Cortex-R FPU enabled chips */
    /* These map to the Single Precision FPRs, S0-S31 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000015; /* S31 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD1500000; /* S30 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000014; /* S29 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD1400000; /* S28 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000013; /* S27 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD1300000; /* S26 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000012; /* S25 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD1200000; /* S24 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000011; /* S23 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD1100000; /* S22 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000010; /* S21 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD1000000; /* S20 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000009; /* S19 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD9000000; /* S18 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000008; /* S17 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD8000000; /* S16 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000007; /* S15 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD7000000; /* S14 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000006; /* S13 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD6000000; /* S12 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000005; /* S11 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD5000000; /* S10 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000004; /* S9 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD4000000; /* S8 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000003; /* S7 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD3000000; /* S6 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000002; /* S5 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD2000000; /* S4 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000001; /* S3 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD1000000; /* S2 */

    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000000; /* S1 */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0xD0000000; /* S0 */

    /* Floating Point Status and Control Register */
    xMPUSettings->ulContext[ ulContextIndex-- ] = ( StackType_t ) 0x00000000; /* FPSR */
#endif /* portENABLE_FPU */

    /* The task will start with a critical nesting count of 0. */
    xMPUSettings->ulContext[ ulContextIndex ] = portNO_CRITICAL_NESTING;

    /* Ensure that the system call stack is double word aligned. */
    xMPUSettings->xSystemCallStackInfo.pulSystemCallStackPointer = &(
        xMPUSettings->xSystemCallStackInfo
            .ulSystemCallStackBuffer[ configSYSTEM_CALL_STACK_SIZE - 1 ]
    );
    xMPUSettings->xSystemCallStackInfo.pulSystemCallStackPointer =
        ( uint32_t * ) ( ( uint32_t ) ( xMPUSettings->xSystemCallStackInfo
                                            .pulSystemCallStackPointer ) &
                         ( uint32_t ) ( ~( portBYTE_ALIGNMENT_MASK ) ) );

    /* This is not NULL only for the duration of a system call. */
    xMPUSettings->xSystemCallStackInfo.pulTaskStackPointer = NULL;
    /* Set the System Call LR  to go directly to vPortSystemCallExit */
    xMPUSettings->xSystemCallStackInfo.pulSystemCallLinkRegister = &vPortSystemCallExit;
    UBaseType_t ulStackIndex;
    /* Fill the System Call Stack with known values for debugging. */
    for( ulStackIndex = 0x0; ulStackIndex < configSYSTEM_CALL_STACK_SIZE; ulStackIndex++ )
    {
        xMPUSettings->xSystemCallStackInfo.ulSystemCallStackBuffer[ ulStackIndex ] =
            0x575B | ulStackIndex;
    }

    /* Return the address where the context of this task should be restored from*/
    return ( &xMPUSettings->ulContext[ ulContextIndex ] );
}

/*----------------------------------------------------------------------------*/

/** @brief Returns the smallest valid MPU Region size that can hold a number of bytes.
 *
 * @ingroup MPU Control
 *
 * @param ulActualSizeInBytes Number of bytes to find a valid MPU region size for
 * @return uint32_t The smallest MPU region size that can hold the requested bytes.
 */
PRIVILEGED_FUNCTION static uint32_t prvGetMPURegionSizeSetting(
    uint32_t ulActualSizeInBytes
);

static uint32_t prvGetMPURegionSizeSetting( uint32_t ulActualSizeInBytes
) /* PRIVILEGED_FUNCTION */
{
    uint32_t ulRegionSize, ulReturnValue = 4U;

    /* 32 is the smallest region size, 31 is the largest valid value for
     * ulReturnValue. */
    for( ulRegionSize = 32UL; ulReturnValue < 31UL; ( ulRegionSize <<= 1UL ) )
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

/** @brief Stores a FreeRTOS Task's MPU Settings in its TCB
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
void vPortStoreTaskMPUSettings(
    xMPU_SETTINGS * xMPUSettings,
    const struct xMEMORY_REGION * const xRegions,
    StackType_t * pxBottomOfStack,
    uint32_t ulStackDepth
) /* PRIVILEGED_FUNCTION */
{
#if defined( __ARMCC_VERSION )

    /* Declaration when these variable are defined in code instead of being
     * exported from linker scripts. */
    extern uint32_t * __SRAM_segment_start__;
    extern uint32_t * __SRAM_segment_end__;
    extern uint32_t * __privileged_data_start__;
    extern uint32_t * __privileged_data_end__;
#else
    /* Declaration when these variable are exported from linker scripts. */
    extern uint32_t __SRAM_segment_start__[];
    extern uint32_t __SRAM_segment_end__[];

#endif /* if defined( __ARMCC_VERSION ) */
    uint32_t lIndex = 0x0;
    uint32_t ul = 0x0;

    if( xRegions == NULL )
    {
        /* No MPU regions are specified so allow access to all of the RAM. */
        xMPUSettings->xRegion[ 0 ].ulRegionBaseAddress = ( uint32_t
        ) __SRAM_segment_start__;
        xMPUSettings->xRegion[ 0 ].ulRegionSize =
            ( prvGetMPURegionSizeSetting(
                ( uint32_t ) __SRAM_segment_end__ - ( uint32_t ) __SRAM_segment_start__
            ) ) |
            portMPU_REGION_ENABLE;
        xMPUSettings->xRegion[ 0 ].ulRegionAttribute =
            portMPU_PRIV_RW_USER_RW_NOEXEC | portMPU_NORMAL_OIWTNOWA_SHARED;

        /* Invalidate all other regions. */
        for( ul = 1; ul <= portNUM_CONFIGURABLE_REGIONS; ul++ )
        {
            xMPUSettings->xRegion[ ul ].ulRegionBaseAddress = 0x0UL;
            xMPUSettings->xRegion[ ul ].ulRegionSize = 0x0UL;
            xMPUSettings->xRegion[ ul ].ulRegionAttribute = 0x0UL;
        }
    }
    else
    {
        /* This function is called automatically when the task is created - in
         * which case the stack region parameters will be valid. At all other
         * times the stack parameters will not be valid and it is assumed that the
         * stack region has already been configured. */

        if( ulStackDepth > 0 )
        {
            uint32_t ulSmallestRegion = prvGetMPURegionSizeSetting( ulStackDepth * 0x4 );
            /* Define the region that allows access to the stack. */
            xMPUSettings->xRegion[ 0 ].ulRegionBaseAddress = ( uint32_t ) pxBottomOfStack;
            xMPUSettings->xRegion[ 0 ].ulRegionSize =
                ulSmallestRegion | portMPU_REGION_ENABLE;
            xMPUSettings->xRegion[ 0 ].ulRegionAttribute =
                portMPU_PRIV_RW_USER_RW_NOEXEC | portMPU_NORMAL_OIWTNOWA_SHARED;
        }

        for( ul = 1; ul <= portNUM_CONFIGURABLE_REGIONS; ul++ )
        {
            if( ( xRegions[ lIndex ] ).ulLengthInBytes > 0UL )
            {
                /* Translate the generic region definition contained in
                 * xRegions into the R4 specific MPU settings that are then
                 * stored in xMPUSettings. */
                xMPUSettings->xRegion[ ul ].ulRegionBaseAddress =
                    ( uint32_t ) xRegions[ lIndex ].pvBaseAddress;
                xMPUSettings->xRegion[ ul ].ulRegionSize =
                    prvGetMPURegionSizeSetting( xRegions[ lIndex ].ulLengthInBytes ) |
                    portMPU_REGION_ENABLE;
                xMPUSettings->xRegion[ ul ].ulRegionAttribute =
                    xRegions[ lIndex ].ulParameters;
            }
            else
            {
                /* Invalidate the region. */
                xMPUSettings->xRegion[ ul ].ulRegionBaseAddress = 0x0UL;
                xMPUSettings->xRegion[ ul ].ulRegionSize = 0x0UL;
                xMPUSettings->xRegion[ ul ].ulRegionAttribute = 0x0UL;
            }

            lIndex++;
        }
    }
}

/*----------------------------------------------------------------------------*/

/** @brief Set up a default MPU memory Map
 * @return PRIVILEGED_FUNCTION VOID
 * @ingroup MPU Control
 * @note This function shall be called before calling vPortStartFirstTask().
 * @note This function works by pulling variables from the linker script.
 * Ensure that the variables used in your linker script match up with the variable names
 * used at the start of this function.
 */
PRIVILEGED_FUNCTION static void prvSetupDefaultMPU( void )
{
#if defined( __ARMCC_VERSION )
    /* Declaration when these variable are defined in code instead of being
     * exported from linker scripts. */
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

    /* Sections used for system peripherals, such as UART */
    extern uint32_t * __peripherals_start__;
    extern uint32_t * __peripherals_end__;

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

    /* Sections used for system peripherals, such as UART */
    extern uint32_t __peripherals_start__[];
    extern uint32_t __peripherals_end__[];
#endif /* if defined( __ARMCC_VERSION ) */
    uint32_t ulRegionStart;
    uint32_t ulRegionEnd;
    uint32_t ulRegionLength;

    /* Ensure the MPU is disabled */
    prvMpuDisable();

    /* Unprivileged and Privileged Read and Exec MPU Region for Flash */
    ulRegionStart = ( uint32_t ) __FLASH_segment_start__;
    ulRegionEnd = ( uint32_t ) __FLASH_segment_end__;
    ulRegionLength = ulRegionEnd - ulRegionStart;
    ulRegionLength = prvGetMPURegionSizeSetting( ulRegionLength ) | portMPU_REGION_ENABLE;

    prvMpuSetRegion(
        portUNPRIVILEGED_FLASH_REGION,
        ulRegionStart,
        ulRegionLength,
        portMPU_PRIV_RO_USER_RO_EXEC | portMPU_NORMAL_OIWTNOWA_SHARED
    );

    /* Privileged Read and Exec MPU Region for PRIVILEGED_FUNCTIONS. */
    ulRegionStart = ( uint32_t ) __privileged_functions_start__;
    ulRegionEnd = ( uint32_t ) __privileged_functions_end__;
    ulRegionLength = ulRegionEnd - ulRegionStart;
    ulRegionLength = prvGetMPURegionSizeSetting( ulRegionLength ) | portMPU_REGION_ENABLE;
    prvMpuSetRegion(
        portPRIVILEGED_FLASH_REGION,
        ulRegionStart,
        ulRegionLength,
        portMPU_PRIV_RO_USER_NA_EXEC | portMPU_NORMAL_OIWTNOWA_SHARED
    );

    /* MPU Region for Peripheral Usage */
    ulRegionStart = ( uint32_t ) __peripherals_start__;
    ulRegionEnd = ( uint32_t ) __peripherals_end__;
    ulRegionLength = ulRegionEnd - ulRegionStart;
    ulRegionLength = prvGetMPURegionSizeSetting( ulRegionLength ) | portMPU_REGION_ENABLE;
    prvMpuSetRegion(
        portGENERAL_PERIPHERALS_REGION,
        ulRegionStart,
        ulRegionLength,
        portMPU_PRIV_RW_USER_RW_NOEXEC | portMPU_DEVICE_NONSHAREABLE
    );

    /* All Read, and Privileged Write MPU Region for PRIVILEGED_DATA. */
    ulRegionStart = ( uint32_t ) __privileged_data_start__;
    ulRegionEnd = ( uint32_t ) __privileged_data_end__;
    ulRegionLength = ulRegionEnd - ulRegionStart;
    ulRegionLength = prvGetMPURegionSizeSetting( ulRegionLength ) | portMPU_REGION_ENABLE;
    prvMpuSetRegion(
        portPRIVILEGED_RAM_REGION,
        ulRegionStart,
        ulRegionLength,
        portMPU_PRIV_RW_USER_RO_NOEXEC | portMPU_NORMAL_OIWTNOWA_SHARED
    );

    /* After setting default regions, enable the MPU */
    prvMpuEnable();
}

/* ------------------------------------------------------------------------- */

/** @brief Determine if a FreeRTOS Task has been granted access to a memory region
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
                                      const uint32_t ulAccessRequested )
{
    BaseType_t xAccessGranted;
    uint32_t ulRegionEnd = ulRegionStart + ulRegionLength;

    /* Convert the MPU Region Size value to the actual size */
    uint32_t ulTaskRegionLength = 1 << ( ( xTaskMPURegion->ulRegionSize >> 1 ) + 1U );
    // uint32_t ulTaskRegionLength = 2 << ( xTaskMPURegion->ulRegionSize >> 1 );
    uint32_t ulTaskRegionEnd = xTaskMPURegion->ulRegionBaseAddress + ulTaskRegionLength;
    if( ( ulRegionStart >= xTaskMPURegion->ulRegionBaseAddress )
        && ( ulRegionEnd <= ulTaskRegionEnd ) )
    {
        /* Unprivileged read is MPU Ctrl Access Bit Value bX1X */
        if( ( tskMPU_READ_PERMISSION == ulAccessRequested ) &&
            ( ( portMPU_PRIV_RW_USER_RO_NOEXEC )
                & xTaskMPURegion->ulRegionAttribute ) )
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


BaseType_t xPortIsAuthorizedToAccessBuffer( const void * pvBuffer,
                                            uint32_t ulBufferLength,
                                            uint32_t ulAccessRequested ) /* PRIVILEGED_FUNCTION */

{
    BaseType_t xAccessGranted;

    /* Calling task's MPU settings. */
    xMPU_SETTINGS * xTaskMPUSettings = NULL;
    xMPU_REGION_REGISTERS * xTaskMPURegion = NULL;

    if( pdFALSE == xSchedulerRunning )
    {
        /* Before the scheduler starts an unknown task will be pxCurrentTCB */
        xAccessGranted = pdTRUE;
    }
    else
    {
        xTaskMPUSettings = xTaskGetMPUSettings( NULL );

        if( NULL == xTaskMPUSettings )
        {
            xAccessGranted = pdFALSE;
        }
        else if( xTaskMPUSettings->ulTaskFlags & portTASK_IS_PRIVILEGED_FLAG )
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
                xAccessGranted = prvTaskCanAccessRegion( xTaskMPURegion,
                                                        ( uint32_t ) pvBuffer,
                                                        ulBufferLength,
                                                        ulAccessRequested );
            } while( ( pdFALSE == xAccessGranted ) &&
                     ( ulRegionIndex < portTOTAL_NUM_REGIONS_IN_TCB ) );
        }
    }
    return xAccessGranted;
}


/*---------------------------------------------------------------------------*/

/** @brief Determine if the FreeRTOS Task was created as a privileged task
 *
 * @ingroup MPU Control
 * @ingroup Task Context
 *
 * @return pdTRUE if the Task was created as a privileged task.
 * pdFALSE if the task was not created as a privileged task.
 *
 */
BaseType_t xPortIsTaskPrivileged( void ) /* PRIVILEGED_FUNCTION */
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

/** @brief Start the FreeRTOS-Kernel's control of Tasks by starting the System Tick
 * Interrupt.
 *
 * @ingroup Scheduler
 * @return BaseType_t This function is not meant to be returned from.
 * If it does return it returns pdFALSE to mark that the scheduler could not be started.
 */
BaseType_t xPortStartScheduler( void )
{
    /* Start the timer that generates the tick ISR. */
    configSETUP_TICK_INTERRUPT();

    /* Reset the critical section nesting count read to execute the first task. */
    ulCriticalNesting = 0UL;

    /* Configure the regions in the MPU that are common to all tasks. */
    prvSetupDefaultMPU();

    xSchedulerRunning = pdTRUE;

    /* Load the context of the first task, starting the FreeRTOS-Scheduler's control. */
    vPortStartFirstTask();

    /* Will only get here if vTaskStartScheduler() was called with the CPU in
     * a non-privileged mode or the binary point register was not set to its lowest
     * possible value. prvTaskExitError() is referenced to prevent a compiler
     * warning about it being defined but not referenced in the case that the user
     * defines their own exit address. */
    ( void ) prvTaskExitError();
    return 0;
}
/*---------------------------------------------------------------------------*/

#if( configENABLE_ACCESS_CONTROL_LIST == 1 )

 BaseType_t xPortIsAuthorizedToAccessKernelObject( int32_t lInternalIndexOfKernelObject ) /* PRIVILEGED_FUNCTION */
        {
            uint32_t ulAccessControlListEntryIndex, ulAccessControlListEntryBit;
            BaseType_t xAccessGranted = pdFALSE;
            const xMPU_SETTINGS * xTaskMpuSettings;

            if( xSchedulerRunning == pdFALSE )
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

                ulAccessControlListEntryIndex = ( ( uint32_t ) lInternalIndexOfKernelObject / portACL_ENTRY_SIZE_BITS );
                ulAccessControlListEntryBit = ( ( uint32_t ) lInternalIndexOfKernelObject % portACL_ENTRY_SIZE_BITS );

                if( ( xTaskMpuSettings->ulTaskFlags & portTASK_IS_PRIVILEGED_FLAG ) == portTASK_IS_PRIVILEGED_FLAG )
                {
                    xAccessGranted = pdTRUE;
                }
                else
                {
                    if( ( xTaskMpuSettings->ulAccessControlList[ ulAccessControlListEntryIndex ] & ( 1U << ulAccessControlListEntryBit ) ) != 0 )
                    {
                        xAccessGranted = pdTRUE;
                    }
                }
            }

            return xAccessGranted;
        }


    void vPortGrantAccessToKernelObject( TaskHandle_t xInternalTaskHandle,
                                         int32_t lInternalIndexOfKernelObject ) /* PRIVILEGED_FUNCTION */
    {
        uint32_t ulAccessControlListEntryIndex, ulAccessControlListEntryBit;
        xMPU_SETTINGS * xTaskMpuSettings;

        ulAccessControlListEntryIndex = ( ( uint32_t ) lInternalIndexOfKernelObject / portACL_ENTRY_SIZE_BITS );
        ulAccessControlListEntryBit = ( ( uint32_t ) lInternalIndexOfKernelObject % portACL_ENTRY_SIZE_BITS );

        xTaskMpuSettings = xTaskGetMPUSettings( xInternalTaskHandle );

        xTaskMpuSettings->ulAccessControlList[ ulAccessControlListEntryIndex ] |= ( 1U << ulAccessControlListEntryBit );
    }

    void vPortRevokeAccessToKernelObject( TaskHandle_t xInternalTaskHandle,
                                          int32_t lInternalIndexOfKernelObject ) /* PRIVILEGED_FUNCTION */
    {
        uint32_t ulAccessControlListEntryIndex, ulAccessControlListEntryBit;
        xMPU_SETTINGS * xTaskMpuSettings;

        ulAccessControlListEntryIndex = ( ( uint32_t ) lInternalIndexOfKernelObject / portACL_ENTRY_SIZE_BITS );
        ulAccessControlListEntryBit = ( ( uint32_t ) lInternalIndexOfKernelObject % portACL_ENTRY_SIZE_BITS );

        xTaskMpuSettings = xTaskGetMPUSettings( xInternalTaskHandle );

        xTaskMpuSettings->ulAccessControlList[ ulAccessControlListEntryIndex ] &= ~( 1U << ulAccessControlListEntryBit );
    }

#else

BaseType_t xPortIsAuthorizedToAccessKernelObject( int32_t lInternalIndexOfKernelObject
) /* PRIVILEGED_FUNCTION */
{
    ( void ) lInternalIndexOfKernelObject;

    /* If Access Control List feature is not used, all the tasks have
     * access to all the kernel objects. */
    return pdTRUE;
}

#endif /* #if ( configENABLE_ACCESS_CONTROL_LIST == 1 ) */

/*---------------------------------------------------------------------------*/

/** @brief Function that is used as the default Link Register address for a new Task
 *
 * @ingroup Task Context
 * @note This function is used as the default Link Register address if
 * configTASK_RETURN_ADDRESS is not defined in FreeRTOSConfig.h
 *
 */
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

/** @brief Function meant to end the FreeRTOS Scheduler, not implemented on this port.
 * @ingroup Scheduler
 */
void vPortEndScheduler( void )
{
    xSchedulerRunning = pdFALSE;
    /* Not implemented in ports where there is nothing to return to.
     * Artificially force an assert. */
    configASSERT( xSchedulerRunning );
}

/*---------------------------------------------------------------------------*/
