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

#ifndef PORTMACRO_ASM_H
#define PORTMACRO_ASM_H

#ifdef __cplusplus
extern "C" {
#endif

#include "FreeRTOSConfig.h"

#ifndef configTOTAL_MPU_REGIONS
    #error "Set configTOTAL_MPU_REGIONS to the humber of MPU regions in FreeRTOSConfig.h"
#elif( configTOTAL_MPU_REGIONS == 8 )
    #define portMPU_TOTAL_REGIONS ( 8UL )
#elif( configTOTAL_MPU_REGIONS == 12 )
    #define portMPU_TOTAL_REGIONS ( 12UL )
#elif( configTOTAL_MPU_REGIONS == 16 )
    #define portMPU_TOTAL_REGIONS ( 16UL )
#else
    #error "Set configTOTAL_MPU_REGIONS to the number of MPU regions in FreeRTOSConfig.h"
#endif /* configTOTAL_MPU_REGIONS */

/** On the ArmV7-R Architecture the Operating mode of the Processor is set using
 * the Current Program Status and Control Register (CPSR) Mode bits, [4:0]
 * the only registers banked between modes are the CPSR, Stack Pointer (R13),
 * and the Link Register (R14). FIQ mode also banks the GPRs R8-R12
 * Of note, the only mode not "Privileged" is User Mode
 *
 * Additional information about the Processor Modes can be found here:
 * https://developer.arm.com/documentation/ddi0406/cb/System-Level-Architecture/The-System-Level-Programmers--Model/ARM-processor-modes-and-ARM-core-registers/ARM-processor-modes?lang=en
 *
 * */

/**
 * @brief CPSR Mode bit field value for User Mode.
 * @ingroup Port Privilege
 */
#define USER_MODE                        0x10U

/**
 * @brief CPSR Mode bit field value for Fast Interrupt Handler (FIQ) Mode.
 * @ingroup Port Privilege
 */
#define FIQ_MODE                         0x11U

/**
 * @brief CPSR Mode bit field value for Interrupt Handler (IRQ) Mode.
 * @ingroup Port Privilege
 */
#define IRQ_MODE                         0x12U

/**
 * @brief CPSR Mode bit field value for Supervisor (SVC) Mode.
 * @ingroup Port Privilege
 */
#define SVC_MODE                         0x13U

/**
 * @brief CPSR Mode bit field value for Monitor (MON) Mode.
 * @ingroup Port Privilege
 */
#define MON_MODE                         0x16U

/**
 * @brief CPSR Mode bit field value for Abort (ABT) Mode.
 * @ingroup Port Privilege
 */
#define ABT_MODE                         0x17U

/**
 * @brief CPSR Mode bit field value for Hypervisor (HYP) Mode.
 * @ingroup Port Privilege
 */
#define HYP_MODE                         0x1AU

/**
 * @brief CPSR Mode bit field value for Undefined (UND) Mode.
 * @ingroup Port Privilege
 */
#define UND_MODE                         0x1BU

/**
 * @brief CPSR Mode bit field value for System (SYS) Mode.
 * @ingroup Port Privilege
 */
#define SYS_MODE                         0x1FU

/**
 * @brief Used to mark if a task should be created as a privileged task.
 *
 * @ingroup Task Context
 * @ingroup MPU Control
 *
 * @note This is done by performing a bitwise OR of this value and the task priority.
 * For example, to create a privileged task at priority 2 the uxPriority
 * parameter should be set to ( 2 | portPRIVILEGE_BIT ).
 */
#define portPRIVILEGE_BIT                    ( 0x80000000UL )

/**
 * @brief Flag uses to mark that a FreeRTOS Task is privileged.
 * @ingroup Port Privilege
 */
#define portTASK_IS_PRIVILEGED_FLAG      ( 1UL << 1UL )

/**
 * @brief SVC Number to use when requesting a context swap.
 * @ingroup Scheduler
 */
#define portSVC_YIELD                    0x0100

/**
 * @brief SVC Number to use when exiting a FreeRTOS System Call.
 * @ingroup MPU Control
 */
#define portSVC_SYSTEM_CALL_EXIT         0x0104

/**
 * @addtogroup MPU Control
 * @note The Region Access Control Register is used to set MPU Region Settings.
 * Further information about this register can be found in Arm's documentation
 * https://developer.arm.com/documentation/ddi0363/g/System-Control/Register-descriptions/c6--MPU-memory-region-programming-registers
 *
 */

/* MPU Sub Region settings */
#define portMPU_SUBREGION_0_DISABLE      ( 0x1UL << 8UL )
#define portMPU_SUBREGION_1_DISABLE      ( 0x1UL << 9UL )
#define portMPU_SUBREGION_2_DISABLE      ( 0x1UL << 10UL )
#define portMPU_SUBREGION_3_DISABLE      ( 0x1UL << 11UL )
#define portMPU_SUBREGION_4_DISABLE      ( 0x1UL << 12UL )
#define portMPU_SUBREGION_5_DISABLE      ( 0x1UL << 13UL )
#define portMPU_SUBREGION_6_DISABLE      ( 0x1UL << 14UL )
#define portMPU_SUBREGION_7_DISABLE      ( 0x1UL << 15UL )

/* Default MPU regions */
#define portFIRST_CONFIGURABLE_REGION    ( 0 )
#define portLAST_CONFIGURABLE_REGION     ( portMPU_TOTAL_REGIONS - 6UL )
#define portSTACK_REGION                 ( portMPU_TOTAL_REGIONS - 5UL )
#define portGENERAL_PERIPHERALS_REGION   ( portMPU_TOTAL_REGIONS - 4UL )
#define portUNPRIVILEGED_FLASH_REGION    ( portMPU_TOTAL_REGIONS - 3UL )
#define portPRIVILEGED_FLASH_REGION      ( portMPU_TOTAL_REGIONS - 2UL )
#define portPRIVILEGED_RAM_REGION        ( portMPU_TOTAL_REGIONS - 1UL )
#define portNUM_CONFIGURABLE_REGIONS \
    ( ( portLAST_CONFIGURABLE_REGION - portFIRST_CONFIGURABLE_REGION ) + 1UL )
/* Plus one to make space for the stack region*/
#define portTOTAL_NUM_REGIONS_IN_TCB         ( portNUM_CONFIGURABLE_REGIONS + 1UL )

/* MPU region sizes */
#define portMPU_SIZE_32B                     ( 0x04UL << 1UL )
#define portMPU_SIZE_64B                     ( 0x05UL << 1UL )
#define portMPU_SIZE_128B                    ( 0x06UL << 1UL )
#define portMPU_SIZE_256B                    ( 0x07UL << 1UL )
#define portMPU_SIZE_512B                    ( 0x08UL << 1UL )
#define portMPU_SIZE_1KB                     ( 0x09UL << 1UL )
#define portMPU_SIZE_2KB                     ( 0x0AUL << 1UL )
#define portMPU_SIZE_4KB                     ( 0x0BUL << 1UL )
#define portMPU_SIZE_8KB                     ( 0x0CUL << 1UL )
#define portMPU_SIZE_16KB                    ( 0x0DUL << 1UL )
#define portMPU_SIZE_32KB                    ( 0x0EUL << 1UL )
#define portMPU_SIZE_64KB                    ( 0x0FUL << 1UL )
#define portMPU_SIZE_128KB                   ( 0x10UL << 1UL )
#define portMPU_SIZE_256KB                   ( 0x11UL << 1UL )
#define portMPU_SIZE_512KB                   ( 0x12UL << 1UL )
#define portMPU_SIZE_1MB                     ( 0x13UL << 1UL )
#define portMPU_SIZE_2MB                     ( 0x14UL << 1UL )
#define portMPU_SIZE_4MB                     ( 0x15UL << 1UL )
#define portMPU_SIZE_8MB                     ( 0x16UL << 1UL )
#define portMPU_SIZE_16MB                    ( 0x17UL << 1UL )
#define portMPU_SIZE_32MB                    ( 0x18UL << 1UL )
#define portMPU_SIZE_64MB                    ( 0x19UL << 1UL )
#define portMPU_SIZE_128MB                   ( 0x1AUL << 1UL )
#define portMPU_SIZE_256MB                   ( 0x1BUL << 1UL )
#define portMPU_SIZE_512MB                   ( 0x1CUL << 1UL )
#define portMPU_SIZE_1GB                     ( 0x1DUL << 1UL )
#define portMPU_SIZE_2GB                     ( 0x1EUL << 1UL )
#define portMPU_SIZE_4GB                     ( 0x1FUL << 1UL )

/* MPU Device Memory Types */
#define portMPU_REGION_STRONGLY_ORDERED      ( 0x00UL )
#define portMPU_REGION_DEVICE                ( 0x01UL )
#define portMPU_REGION_CACHEABLE_BUFFERABLE  ( 0x03UL )
#define portMPU_REGION_EXECUTE_NEVER         ( 0x01UL << 12UL )
#define portMPU_STRONGLYORDERED_SHAREABLE    ( 0x0000UL )
#define portMPU_DEVICE_SHAREABLE             ( 0x0001UL )
#define portMPU_DEVICE_NONSHAREABLE          ( 0x0010UL )
#define portMPU_NORMAL_OIWTNOWA_NONSHARED    ( 0x0002UL )
#define portMPU_NORMAL_OIWBNOWA_NONSHARED    ( 0x0003UL )
#define portMPU_NORMAL_OIWTNOWA_SHARED       ( 0x0006UL )
#define portMPU_NORMAL_OIWBNOWA_SHARED       ( 0x0007UL )
#define portMPU_NORMAL_OINC_NONSHARED        ( 0x0008UL )
#define portMPU_NORMAL_OIWBWA_NONSHARED      ( 0x000BUL )
#define portMPU_NORMAL_OINC_SHARED           ( 0x000CUL )
#define portMPU_NORMAL_OIWBWA_SHARED         ( 0x000FUL )

/**
 * @brief MPU_CTRL value for: No Access and No Execute
 *
 * @ingroup MPU Control
 *
 * @brief No Access in a Privileged Operating Mode
 * No Access in User Mode
 * Cannot Execute Code from this region
 */
#define portMPU_PRIV_NA_USER_NA_NOEXEC       ( 0x1000UL )

/**
 * @brief MPU_CTRL value for Privileged Read and Exec
 *
 * @ingroup MPU Control
 *
 * @note Read Only Access in Privileged Operating Modes.
 * No Read/Write Access in User Mode
 * Allowed to Execute Code from this region
 */
#define portMPU_PRIV_RO_USER_NA_EXEC         ( 0x0500UL )

/**
 * @brief MPU_CTRL value for Privileged Read, Write, and Exec
 *
 * @ingroup MPU Control
 *
 * Read/Write in a Privileged Operating Mode
 * No Access in User Mode
 * Allowed to Execute Code from this region
 */
#define portMPU_PRIV_RW_USER_NA_EXEC         ( 0x0100UL )

/**
 * @brief MPU_CTRL value for Read Only and Execute
 *
 * @ingroup MPU Control
 *
 * @note Read Only in a Privileged Operating Mode
 * Read Only in User Mode
 * Allowed to Execute Code from this region
 * */
#define portMPU_PRIV_RO_USER_RO_EXEC         ( 0x0600UL )

/**
 * @brief MPU_CTRL value for: Read, Execute, and Privileged Write
 *
 * @ingroup MPU Control
 *
 * @note Read/Write in a Privileged Operating Mode
 * Read Only in User Mode
 * Allowed to Execute Code from this region
 */
#define portMPU_PRIV_RW_USER_RO_EXEC         ( 0x0200UL )

/**
 * @brief MPU_CTRL value for: Read, Write, and Execute
 *
 * @ingroup MPU Control
 *
 * @note Read/Write in a Privileged Operating Mode
 * Read/write in User Mode
 * Allowed to Execute Code from this region
 */
#define portMPU_PRIV_RW_USER_RW_EXEC         ( 0x0300UL )

/**
 * @brief MPU_CTRL value for: Privileged Read, Write Only, no Execute
 *
 * @ingroup MPU Control
 *
 * @note Read/Write in a Privileged Operating Mode
 * No Access in User Mode
 * Cannot Execute Code from this region
 */
#define portMPU_PRIV_RW_USER_NA_NOEXEC       ( 0x1100UL )

/**
 * @brief MPU_CTRL value for: All Read, Privileged Write, no Execute
 *
 * @ingroup MPU Control
 *
 * Read/Write in a Privileged Operating Mode
 * Read Only in User Mode
 * Cannot Execute Code from this region
 */
#define portMPU_PRIV_RW_USER_RO_NOEXEC       ( 0x1200UL )

/**
 * @brief MPU_CTRL value for: Read, Write, no Execute
 *
 * @ingroup MPU Control
 *
 * @note Read/Write in a Privileged Operating Mode
 * Read/Write in User Mode
 * Cannot Execute Code from this region
 */
#define portMPU_PRIV_RW_USER_RW_NOEXEC       ( 0x1300UL )

/**
 * @brief MPU_CTRL value for: Privileged Read Only, No Execute
 *
 * @ingroup MPU Control
 *
 * @note Read Only in a Privileged Operating Mode
 * No Access in User Mode
 * Cannot Execute Code from this region
 */
#define portMPU_PRIV_RO_USER_NA_NOEXEC       ( 0x1500UL )

/**
 * @brief MPU_CTRL value for: Read Only, No Execute
 *
 * @ingroup MPU Control
 *
 * @note Read Only in a Privileged Operating Mode
 * Read Only in User Mode
 * Cannot Execute Code from this region
 */
#define portMPU_PRIV_RO_USER_RO_NOEXEC       ( 0x1600UL )

/**
 * @brief MPU_CTRL value to enable an MPU Region
 * @ingroup MPU Control
 */
#define portMPU_REGION_ENABLE                ( 0x01UL )

/** This following section is used to create the proper size for the ulContext array.
 * This array is where all registers related to a task's context are saved.
 * The size of this array will depend on if the system is using an integrated
 * Floating Point Unit (FPU) or not. If we are using the FPU we must save the
 * Floating Point Status and Control Register (FPSCR),
 * and the Floating Point Registers (FPRs). The FPSCR holds the conditional bits
 * used for floating point calculations. The FPRs hold the actual floating point bits.
 * The remainder of a task's context consists of the General Purpose Registers (GPRs).
 * General Purpose Registers are used to manipulate almost all variables.
 * The Current Program Status and Control Register, which holds the operating mode
 * and bits that correspond to any conditional checks, such as if statements.
 * And the Critical Nesting Depth of the task.
 *
 *
 * For more information about the FPU, FPSCR, and FPRs please reference ARM's website:
 * https://developer.arm.com/documentation/den0042/a/Floating-Point
 *
 * Additional information related to the Cortex R4-F's FPU Implementation:
 * https://developer.arm.com/documentation/ddi0363/e/fpu-programmer-s-model
 *
 * Additional information related to the Cortex R5-F's FPU Implementation:
 * https://developer.arm.com/documentation/ddi0460/d/FPU-Programmers-Model
 *
 * Additional information related to the ArmV7-R CPSR
 * https://developer.arm.com/documentation/ddi0406/cb/Application-Level-Architecture/Application-Level-Programmers--Model/The-Application-Program-Status-Register--APSR-?lang=en
 *
 * Additional information related to the GPRs:
 * https://developer.arm.com/documentation/ddi0406/cb/System-Level-Architecture/The-System-Level-Programmers--Model/ARM-processor-modes-and-ARM-core-registers/ARM-core-registers?lang=en
 *
 */

/**
 * @brief The length in ulContext for the General Purpose Registers in bytes.
 * @note There are 13 GPRs, R0-R12, the SP, and the LR. Each are 32 bits,
 * which leads to the 15 registers * 4 in length.
 */
#define portREGISTER_LENGTH                       ( 15U * 4U )

/**
 * If you KNOW that your system will not utilize the FPU in any capacity
 * you can set portENABLE_FPU to 0, which will reduce the per-task RAM usage
 * by ( 32 FPRs + 32 bit FPSCR ) * 4 bytes per register = 132, or 0x84, Bytes Per Task
 * BE CAREFUL DISABLING THIS: Certain APIs will try and optimize themselves
 * by using the FPRs. If the FPU context is not saved and this happens it could be
 * exceedingly difficult to debug why a strcpy() or other similar function
 * seems to randomly fail.
 */
#ifndef configENABLE_FPU
    #define configENABLE_FPU 1
#endif /* configENABLE_FPU */

/**
 * @brief Mark if the Floating Point Registers will be saved.
 * @ingroup Task Context
 * @note When using the FPU, we must save additional registers into the task's context
 * These consist of the Floating Point Status and Control Register (FPSCR),
 * As well as the Floating Point Registers (FPRs)
 */
#define portENABLE_FPU configENABLE_FPU

#if( portENABLE_FPU == 1 )
    /**
     * @brief Length of a Task's Register Context when using an FPU.
     * @ingroup Task Context
     * @note Task Context which is stored in ulContext in order, consists of:
     * ulContext[ 0 ]:      Critical Nesting Count: ulCriticalNesting
     * ulContext[ 1 ]:      Floating Point Status and Control Register
     * ulContext[ 2 - 33 ]: Floating Point Registers: S0-S31
     * ulContext[ 34 - 46 ]:  General Purpose Registers: R0-R12
     * ulContext[ 48 ]:     Stack Pointer
     * ulContext[ 49 ]:     Link Register
     * ulContext[ 50 ]:     Program Counter
     * ulContext[ 51 ]:     Current Program Status and Control Register
     */
    #define MAX_CONTEXT_SIZE 51U
#else
    /**
     * @brief Length of a Task's Register Context when not using an FPU.
     * @ingroup Task Context
     * @note Task Context which is stored in ulContext in order, consists of:
     * ulContext[ 0 ]:      Critical Nesting Count: ulCriticalNesting
     * ulContext[ 1 - 13 ]:  General Purpose Registers: R0-R12
     * ulContext[ 14 ]:     Stack Pointer
     * ulContext[ 15 ]:     Link Register
     * ulContext[ 16 ]:     Program Counter
     * ulContext[ 17 ]:     Current Program Status and Control Register
     */
    #define MAX_CONTEXT_SIZE 18U
#endif /* MAX_CONTEXT_SIZE */

/**
 * @brief Numerical offset from the start of a TCB to xSystemCallStackInfo.
 * @note In the exception handlers it is necessary to load this variable from the TCB.
 * This provides an easy way for the exception handlers to get this structure.
 * The numerical value here should be equal to:
 * sizeof( xRegion ) + sizeof( ulContext ) + sizeof( ulTaskFlags)
 */
#define portSYSTEM_CALL_INFO_OFFSET \
    ( ( ( portTOTAL_NUM_REGIONS_IN_TCB * 3U ) + ( MAX_CONTEXT_SIZE ) + 1 ) * 4U )

#ifdef __cplusplus
} /* extern C */
#endif

#endif /* PORTMACRO_ASM_H */
