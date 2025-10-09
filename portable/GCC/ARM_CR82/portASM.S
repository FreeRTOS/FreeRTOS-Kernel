/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * Copyright 2025-2026 Arm Limited and/or its affiliates
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

/*
 * This file is tailored for ARM Cortex-R82 with SMP enabled.
 * It includes macros and functions for saving/restoring task context,
 * handling interrupts, and supporting multi-core operations.
 */

#include "FreeRTOSConfig.h"
#include "portmacro.h"

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE ensures that PRIVILEGED_FUNCTION
 * is defined correctly and privileged functions are placed in correct sections. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* System call numbers includes. */
#include "mpu_syscall_numbers.h"

/* MPU_WRAPPERS_INCLUDED_FROM_API_FILE is needed to be defined only for the
 * header files. */
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

.text

/* Variables and functions. */
#if ( configNUMBER_OF_CORES == 1 )
   .extern pxCurrentTCB
   .extern ullCriticalNesting
   .extern ullPortInterruptNesting
#else /* #if ( configNUMBER_OF_CORES == 1 ) */
   .extern pxCurrentTCBs
   .extern ullCriticalNestings
   .extern ullPortInterruptNestings
#endif
   .extern vTaskSwitchContext
   .extern vApplicationIRQHandler
   .extern ullPortTaskHasFPUContext
   .extern ullPortYieldRequired
   .extern _freertos_vector_table

#if ( configENABLE_MPU == 1 )
   .extern xPortIsTaskPrivileged
   .extern vSystemCallEnter
   .extern vSystemCallExit
   .extern vRequestSystemCallExit
   .extern uxSystemCallImplementations
#endif /* #if ( configENABLE_MPU == 1 ) */

   .global FreeRTOS_IRQ_Handler
   .global FreeRTOS_SWI_Handler
   .global vPortSaveTaskContext
   .global vPortRestoreTaskContext

#if ( configENABLE_MPU == 1 )

   .macro portLOAD_MPU_REGIONS_ADDRESSES
MOV     X3, # portSTACK_REGION                      /* Task's first programmed region is its stack region as the first four MPU regions are already programmed.*/
MOV     X4, # configTOTAL_MPU_REGIONS - 1           /* Upper limit = configTOTAL_MPU_REGIONS - 1 */
1 :
    CMP     X3, X4                                  /* Compare i with ( configTOTAL_MPU_REGIONS - 1 ) */
    B.GT    2f                                      /* if i > ( configTOTAL_MPU_REGIONS - 1 ), exit loop */
    MSR     PRSELR_EL1, X3                          /* Program PRSELR_EL1. */
    ISB                                             /* Ensure PRSELR selection takes effect before registers access. */
    LDP     X1, X2, [ X0 ], # 0x10                  /* Retrieve ullPrbarEl1 and ullPrlarEl1r */
    MSR     PRBAR_EL1, X1                           /* Program PRBAR_EL1. */
    MSR     PRLAR_EL1, X2                           /* Program PRLAR_EL1. */
    ADD     X3, X3, # 1                             /* i++ */
    B       1b
2 :
    DSB     SY
    ISB
   .endm

   .macro portSTORE_MPU_REGIONS_ADDRESSES
MOV     X3, # portSTACK_REGION                      /* Task's first programmed region is its stack region as the first four MPU regions are already programmed.*/
MOV     X4, # configTOTAL_MPU_REGIONS - 1           /* Upper limit = configTOTAL_MPU_REGIONS - 1 */
1 :
    CMP     X3, X4                                  /* Compare i with ( configTOTAL_MPU_REGIONS - 1 ) */
    B.GT    2f                                      /* if i > ( configTOTAL_MPU_REGIONS - 1 ), exit loop */
    MSR     PRSELR_EL1, X3                          /* Program PRSELR_EL1. */
    ISB                                             /* Ensure PRSELR selection takes effect before registers access. */
    MRS     X1, PRBAR_EL1                           /* Retrieve PRBAR_EL1. */
    MRS     X2, PRLAR_EL1                           /* Retrieve PRLAR_EL1. */
    STP     X1, X2, [ X0 ], # 0x10                  /* Store PRBAR_EL1 and PRLAR_EL1 in ullPrbarEl1 and ullPrlarEl1r */
    ADD     X3, X3, # 1                             /* i++ */
    B       1b
2 :
    /* No additional barrier required after reading PR* registers. */
   .endm

#endif /* #if ( configENABLE_MPU == 1 ) */

/*-----------------------------------------------------------*/

   .macro savefuncontextgpregs
/* Save function context general-purpose registers. */
STP X0, X1, [ SP, # - 0x10 ] !
STP X2, X3, [ SP, # - 0x10 ] !
STP X4, X5, [ SP, # - 0x10 ] !
STP X6, X7, [ SP, # - 0x10 ] !
STP X8, X9, [ SP, # - 0x10 ] !
STP X10, X11, [ SP, # - 0x10 ] !
STP X12, X13, [ SP, # - 0x10 ] !
STP X14, X15, [ SP, # - 0x10 ] !
STP X16, X17, [ SP, # - 0x10 ] !
STP X18, X29, [ SP, # - 0x10 ] !
STR X30, [ SP, # - 0x10 ] !
   .endm

/*-----------------------------------------------------------*/

   .macro savesyscallcontextgpregs
/* Save system call context general-purpose registers. */
STP X4, X5, [ SP, # - 0x10 ] !
STP X6, X7, [ SP, # - 0x10 ] !
STP X8, X9, [ SP, # - 0x10 ] !
STP X10, X11, [ SP, # - 0x10 ] !
STP X12, X13, [ SP, # - 0x10 ] !
STP X14, X15, [ SP, # - 0x10 ] !
STP X16, X17, [ SP, # - 0x10 ] !
STP X18, X29, [ SP, # - 0x10 ] !
   .endm

/*-----------------------------------------------------------*/

   .macro restorefuncontextgpregs
/* Restore function context general-purpose registers. */
LDR X30, [ SP ], # 0x10
LDP X18, X29, [ SP ], # 0x10
LDP X16, X17, [ SP ], # 0x10
LDP X14, X15, [ SP ], # 0x10
LDP X12, X13, [ SP ], # 0x10
LDP X10, X11, [ SP ], # 0x10
LDP X8, X9, [ SP ], # 0x10
LDP X6, X7, [ SP ], # 0x10
LDP X4, X5, [ SP ], # 0x10
LDP X2, X3, [ SP ], # 0x10
LDP X0, X1, [ SP ], # 0x10
   .endm

/*-----------------------------------------------------------*/

   .macro restorefuncontextgpregexceptx0
/* Restore function context general-purpose registers while discarding old X0. */
LDR X30, [ SP ], # 0x10
LDP X18, X29, [ SP ], # 0x10
LDP X16, X17, [ SP ], # 0x10
LDP X14, X15, [ SP ], # 0x10
LDP X12, X13, [ SP ], # 0x10
LDP X10, X11, [ SP ], # 0x10
LDP X8, X9, [ SP ], # 0x10
LDP X6, X7, [ SP ], # 0x10
LDP X4, X5, [ SP ], # 0x10
LDP X2, X3, [ SP ], # 0x10
LDP XZR, X1, [ SP ], # 0x10
   .endm

/*-----------------------------------------------------------*/

   .macro restoresyscallcontextgpregs
/* Restore system call context general-purpose registers. */
LDP X18, X29, [ SP ], # 0x10
LDP X16, X17, [ SP ], # 0x10
LDP X14, X15, [ SP ], # 0x10
LDP X12, X13, [ SP ], # 0x10
LDP X10, X11, [ SP ], # 0x10
LDP X8, X9, [ SP ], # 0x10
LDP X6, X7, [ SP ], # 0x10
LDP X4, X5, [ SP ], # 0x10
   .endm
/*-----------------------------------------------------------*/

   .macro saveallgpregisters
/* Save all general-purpose registers on stack. */
STP X0, X1, [ SP, # - 0x10 ] !
STP X2, X3, [ SP, # - 0x10 ] !
STP X4, X5, [ SP, # - 0x10 ] !
STP X6, X7, [ SP, # - 0x10 ] !
STP X8, X9, [ SP, # - 0x10 ] !
STP X10, X11, [ SP, # - 0x10 ] !
STP X12, X13, [ SP, # - 0x10 ] !
STP X14, X15, [ SP, # - 0x10 ] !
STP X16, X17, [ SP, # - 0x10 ] !
STP X18, X19, [ SP, # - 0x10 ] !
STP X20, X21, [ SP, # - 0x10 ] !
STP X22, X23, [ SP, # - 0x10 ] !
STP X24, X25, [ SP, # - 0x10 ] !
STP X26, X27, [ SP, # - 0x10 ] !
STP X28, X29, [ SP, # - 0x10 ] !
STP X30, XZR, [ SP, # - 0x10 ] !
   .endm

/*-----------------------------------------------------------*/

   .macro restoreallgpregisters
/* Restore all general-purpose registers from stack. */
LDP X30, XZR, [ SP ], # 0x10
LDP X28, X29, [ SP ], # 0x10
LDP X26, X27, [ SP ], # 0x10
LDP X24, X25, [ SP ], # 0x10
LDP X22, X23, [ SP ], # 0x10
LDP X20, X21, [ SP ], # 0x10
LDP X18, X19, [ SP ], # 0x10
LDP X16, X17, [ SP ], # 0x10
LDP X14, X15, [ SP ], # 0x10
LDP X12, X13, [ SP ], # 0x10
LDP X10, X11, [ SP ], # 0x10
LDP X8, X9, [ SP ], # 0x10
LDP X6, X7, [ SP ], # 0x10
LDP X4, X5, [ SP ], # 0x10
LDP X2, X3, [ SP ], # 0x10
LDP X0, X1, [ SP ], # 0x10
   .endm

/*-----------------------------------------------------------*/

   .macro savefloatregisters
/* Save floating-point registers and configuration/status registers. */
STP Q0, Q1, [ SP, # - 0x20 ] !
STP Q2, Q3, [ SP, # - 0x20 ] !
STP Q4, Q5, [ SP, # - 0x20 ] !
STP Q6, Q7, [ SP, # - 0x20 ] !
STP Q8, Q9, [ SP, # - 0x20 ] !
STP Q10, Q11, [ SP, # - 0x20 ] !
STP Q12, Q13, [ SP, # - 0x20 ] !
STP Q14, Q15, [ SP, # - 0x20 ] !
STP Q16, Q17, [ SP, # - 0x20 ] !
STP Q18, Q19, [ SP, # - 0x20 ] !
STP Q20, Q21, [ SP, # - 0x20 ] !
STP Q22, Q23, [ SP, # - 0x20 ] !
STP Q24, Q25, [ SP, # - 0x20 ] !
STP Q26, Q27, [ SP, # - 0x20 ] !
STP Q28, Q29, [ SP, # - 0x20 ] !
STP Q30, Q31, [ SP, # - 0x20 ] !
MRS X9, FPSR
MRS X10, FPCR
STP W9, W10, [ SP, # - 0x10 ] !
   .endm

/*-----------------------------------------------------------*/

   .macro restorefloatregisters
/* Restore floating-point registers and configuration/status registers. */
LDP W9, W10, [ SP ], # 0x10
MSR FPSR, X9
MSR FPCR, X10
LDP Q30, Q31, [ SP ], # 0x20
LDP Q28, Q29, [ SP ], # 0x20
LDP Q26, Q27, [ SP ], # 0x20
LDP Q24, Q25, [ SP ], # 0x20
LDP Q22, Q23, [ SP ], # 0x20
LDP Q20, Q21, [ SP ], # 0x20
LDP Q18, Q19, [ SP ], # 0x20
LDP Q16, Q17, [ SP ], # 0x20
LDP Q14, Q15, [ SP ], # 0x20
LDP Q12, Q13, [ SP ], # 0x20
LDP Q10, Q11, [ SP ], # 0x20
LDP Q8, Q9, [ SP ], # 0x20
LDP Q6, Q7, [ SP ], # 0x20
LDP Q4, Q5, [ SP ], # 0x20
LDP Q2, Q3, [ SP ], # 0x20
LDP Q0, Q1, [ SP ], # 0x20
   .endm

/*-----------------------------------------------------------*/

   .macro portSAVE_CONTEXT

#if ( configENABLE_MPU == 1 )
   /* Switch to use the EL1 stack pointer. */
   MSR SPSEL, # 1

   /* Store X0-X4 as they are being used to save the user allocated task stack and to program the MPU */
   STP X0, X1,  [ SP, # - 0x10 ] !
   STP X2, X3, [ SP, # - 0x10 ] !
   STR X4, [ SP, # - 0x10 ] !

   /* Switch to use the EL0 stack pointer. */
   MSR SPSEL, # 0

   /* Store user allocated task stack and use ullContext as the SP */
   #if ( configNUMBER_OF_CORES == 1 )
      adrp    X0, pxCurrentTCB
      add     X0, X0, :lo12:pxCurrentTCB   /* X0 = &pxCurrentTCB */
   #else
      adrp    X0, pxCurrentTCBs
      add     X0, X0, :lo12:pxCurrentTCBs  /* X0 = &pxCurrentTCBs */
      /* Get the core ID to index the TCB correctly. */
      MRS X2, MPIDR_EL1  /* Read the Multiprocessor Affinity Register */
      AND X2, X2, # 0xff /* Extract Aff0 which contains the core ID */
      LSL X2, X2, # 3    /* Scale the core ID to the size of a pointer (64-bit system) */
      ADD X0, X0, X2     /* Add the offset for the current core's TCB pointer */
   #endif
   LDR X1, [ X0 ]
   ADD X1, X1, #8         /* X1 = X1 + 8, X1 now points to ullTaskUnprivilegedSP in TCB. */
   MOV X0, SP
   STR X0, [ X1 ]         /* Save ullTaskUnprivilegedSP on task's TCB */
   SUB X1, X1, #8         /* X1 = X1 - 8, X1 now points to pxTopOfStack in TCB. */
   LDR X1, [ X1 ]
   MOV SP, X1             /* Use pxTopOfStack ( ullContext ) as the SP. */

   savefuncontextgpregs
   #if ( configNUMBER_OF_CORES > 1 )
      MRS X1, ELR_EL1       /* Save ELR_EL1 before calling xPortIsTaskPrivileged which would change its value in case of multicore */
      STR X1, [ SP, # - 0x10 ] !
   #endif
   BL xPortIsTaskPrivileged
   #if ( configNUMBER_OF_CORES > 1 )
      LDR X1, [ SP ], # 0x10
      MSR ELR_EL1, X1
   #endif
   CBNZ X0, 3f               /* If task is privileged, skip saving MPU context. */
   #if ( configNUMBER_OF_CORES == 1 )
      adrp    X0, pxCurrentTCB
      add     X0, X0, :lo12:pxCurrentTCB   /* X0 = &pxCurrentTCB */
   #else
      adrp    X0, pxCurrentTCBs
      add     X0, X0, :lo12:pxCurrentTCBs  /* X0 = &pxCurrentTCBs */
      /* Get the core ID to index the TCB correctly. */
      MRS X2, MPIDR_EL1  /* Read the Multiprocessor Affinity Register */
      AND X2, X2, # 0xff /* Extract Aff0 which contains the core ID */
      LSL X2, X2, # 3    /* Scale the core ID to the size of a pointer (64-bit system) */
      ADD X0, X0, X2     /* Add the offset for the current core's TCB pointer */
   #endif
   LDR X0, [ X0 ]

   ADD X0, X0, #16         /* X0 = X0 + 16. X0 now points to MAIR_EL1 in TCB. */
   MRS X1, MAIR_EL1        /* X1 = MAIR_EL1. */
   STR X1, [ X0 ], # 0x8   /* Store MAIR_EL1 in TCB, X0 = X0 + 8. */

   portSTORE_MPU_REGIONS_ADDRESSES /* Store MPU region addresses onto TCB. */

3 :
   restorefuncontextgpregs
   MSR SPSEL, # 1

   /* Restore X0-X4. */
   LDR X4, [ SP ], # 0x10
   LDP X2, X3, [ SP ], # 0x10
   LDP X0, X1, [ SP ], # 0x10
#endif /* #if ( configENABLE_MPU == 1 ) */

MSR SPSEL, # 0

/* Save the entire context. */
saveallgpregisters

/* Save the SPSR and ELR values. */
MRS X3, SPSR_EL1
MRS X2, ELR_EL1

STP X2, X3, [ SP, # - 0x10 ] !

/* Save the critical section nesting depth. */
#if ( configNUMBER_OF_CORES == 1 )
   adrp    X0, ullCriticalNesting
   add     X0, X0, :lo12:ullCriticalNesting   /* X0 = &ullCriticalNesting */
#else
   adrp    X0, ullCriticalNestings
   add     X0, X0, :lo12:ullCriticalNestings  /* X0 = &ullCriticalNestings */
   /* Calculate per-core index using MPIDR_EL1 for SMP support. */
   MRS X1, MPIDR_EL1    /* Read the Multiprocessor Affinity Register. */
   AND X1, X1, # 0xff   /* Extract Aff0 (core ID). */
   LSL X1, X1, # 3      /* Multiply core ID by pointer size (8 bytes). */
   ADD X0, X0, X1       /* Add offset to base address. */
#endif

LDR X3, [ X0 ]

/* Save the FPU context indicator. */
adrp    X0, ullPortTaskHasFPUContext
add     X0, X0, :lo12:ullPortTaskHasFPUContext   /* X0 = &ullPortTaskHasFPUContext */

#if ( configNUMBER_OF_CORES > 1 )
   ADD X0, X0, X1 /* Add to the base of the FPU array. */
#endif
LDR X2, [ X0 ]

/* Save the FPU context, if any (32 128-bit registers). */
CBZ X2, 4f /* FPU context not present, skip saving FPU registers. */
savefloatregisters

4 :
/* Store the critical nesting count and FPU context indicator. */
STP X2, X3, [ SP, # - 0x10 ] !

#if ( configNUMBER_OF_CORES == 1 )
   adrp    X0, pxCurrentTCB
   add     X0, X0, :lo12:pxCurrentTCB   /* X0 = &pxCurrentTCB */
#else
   adrp    X0, pxCurrentTCBs
   add     X0, X0, :lo12:pxCurrentTCBs  /* X0 = &pxCurrentTCBs */
   MRS X1, MPIDR_EL1    /* Read Multiprocessor Affinity Register .*/
   AND X1, X1, # 0xff   /* Extract core ID. */
   LSL X1, X1, # 3      /* Multiply core ID by pointer size. */
   ADD X0, X0, X1       /* Offset for current core's TCB pointer. */
#endif

LDR X1, [ X0 ]
MOV X0, SP
STR X0, [ X1 ]      /* Save pxTopOfStack on the TCB. */

/* Switch to use the EL1 stack pointer. */
MSR SPSEL, # 1
   .endm

/*-----------------------------------------------------------*/

   .macro portRESTORE_CONTEXT

#if ( configENABLE_MPU == 1 )
   /* Switch to use the EL1 stack pointer. */
   MSR SPSEL, # 1

   savefuncontextgpregs
   BL xPortIsTaskPrivileged
   CBNZ X0, 3f              /* If task is privileged, skip restoring MPU context. */

   /* Switch to use the EL0 stack pointer. */
   MSR SPSEL, # 0
   #if ( configNUMBER_OF_CORES == 1 )
      adrp    X0, pxCurrentTCB
      add     X0, X0, :lo12:pxCurrentTCB   /* X0 = &pxCurrentTCB */
   #else
      adrp    X0, pxCurrentTCBs
      add     X0, X0, :lo12:pxCurrentTCBs  /* X0 = &pxCurrentTCBs */
      /* Get the core ID to index the TCB correctly. */
      MRS X2, MPIDR_EL1  /* Read the Multiprocessor Affinity Register */
      AND X2, X2, # 0xff /* Extract Aff0 which contains the core ID */
      LSL X2, X2, # 3    /* Scale the core ID to the size of a pointer (64-bit system) */

      ADD X0, X0, X2     /* Add the offset for the current core's TCB pointer */
   #endif
   LDR X0, [ X0 ]

   DMB SY                 /* Complete outstanding transfers before disabling MPU. */
   MRS X1, SCTLR_EL1      /* X1 = SCTLR_EL1 */
   BIC X1, X1, # (1 << 0) /* Clears bit 0 of X1 */
   MSR SCTLR_EL1, X1      /* Disable MPU. */

   ADD X0, X0, #16         /* X0 = X0 + 16. X0 now points to MAIR_EL1 in TCB. */
   LDR X1, [ X0 ], # 0x8   /* X1 = *X0 i.e. X1 = MAIR_EL1, X0 = X0 + 8. */
   MSR MAIR_EL1, X1        /* Program MAIR_EL1. */

   portLOAD_MPU_REGIONS_ADDRESSES /* Load MPU region addresses from TCB. */
   MRS X1, SCTLR_EL1              /* X1 = SCTLR_EL1 */
   ORR X1, X1, # (1 << 0)         /* Sets bit 0 of X1 */
   MSR SCTLR_EL1, X1              /* Enable MPU. */
   DSB SY                         /* Force memory writes before continuing. */

3 :
   MSR SPSEL, # 1
   restorefuncontextgpregs
#endif /* #if ( configENABLE_MPU == 1 ) */

   /* Switch to use the EL0 stack pointer. */
   MSR SPSEL, # 0

   #if ( configNUMBER_OF_CORES == 1 )
      adrp    X0, pxCurrentTCB
      add     X0, X0, :lo12:pxCurrentTCB   /* X0 = &pxCurrentTCB */
   #else
      adrp    X0, pxCurrentTCBs
      add     X0, X0, :lo12:pxCurrentTCBs  /* X0 = &pxCurrentTCBs */
      /* Get the core ID to index the TCB correctly. */
      MRS X2, MPIDR_EL1  /* Read the Multiprocessor Affinity Register */
      AND X2, X2, # 0xff /* Extract Aff0 which contains the core ID */
      LSL X2, X2, # 3    /* Scale the core ID to the size of a pointer (64-bit system) */
      ADD X0, X0, X2     /* Add the offset for the current core's TCB pointer */
   #endif
   LDR X1, [ X0 ]
   LDR X0, [ X1 ]               /* X0 = Location of saved context in TCB. */
   MOV SP, X0
   LDP X2, X3, [ SP ], # 0x10   /* Retrieve critical nesting and FPU indicator */

   #if ( configNUMBER_OF_CORES == 1 )
      adrp    X0, ullCriticalNesting
      add     X0, X0, :lo12:ullCriticalNesting   /* X0 = &ullCriticalNesting */
   #else
      adrp    X0, ullCriticalNestings
      add     X0, X0, :lo12:ullCriticalNestings  /* X0 = &ullCriticalNestings */
      /* Calculate offset for current core's ullCriticalNesting */
      MRS X1, MPIDR_EL1  /* Read Multiprocessor Affinity Register */
      AND X1, X1, # 0xff /* Extract Aff0, which contains the core ID */
      LSL X1, X1, # 3    /* Scale core ID to the size of a pointer (assuming 64-bit system) */
      ADD X0, X0, X1     /* Add offset for the current core's ullCriticalNesting */
   #endif

   MOV X1, # 255            /* Default mask */
   CBZ X3, 4f
   MOV X1, # portMAX_API_PRIORITY_MASK

4:
   MSR ICC_PMR_EL1, X1      /* Set interrupt mask */
   DSB SY
   ISB SY
   STR X3, [ X0 ]           /* Restore critical nesting */
   /* Restore the FPU context indicator. */
   adrp    X0, ullPortTaskHasFPUContext
   add     X0, X0, :lo12:ullPortTaskHasFPUContext   /* X0 = &ullPortTaskHasFPUContext */
   #if ( configNUMBER_OF_CORES > 1 )
      MRS X1, MPIDR_EL1  /* Read Multiprocessor Affinity Register */
      AND X1, X1, # 0xff /* Extract Aff0, which contains the core ID */
      LSL X1, X1, # 3    /* Scale core ID to the size of a pointer (assuming 64-bit system) */
      ADD X0, X0, X1     /* Add to the base of the FPU array */
   #endif
   STR X2, [ X0 ]
   /* Restore the FPU context, if any. */
   CBZ X2, 5f
   restorefloatregisters

5:
   LDP X2, X3, [ SP ], # 0x10  /* Restore SPSR and ELR */

   MSR SPSR_EL1, X3
   MSR ELR_EL1, X2
   restoreallgpregisters

#if ( configENABLE_MPU == 1 )
   /* Save pxTopOfStack ( ullContext ) on the task's TCB and set SP_EL0 to ullTaskUnprivilegedSP. */
   MSR SPSEL, # 1
   STP   X8, X9, [ SP, # - 0x10 ] !
   STR   X10, [ SP, # - 0x10 ] !
   #if ( configNUMBER_OF_CORES == 1 )
      adrp    X8, pxCurrentTCB
      add     X8, X8, :lo12:pxCurrentTCB   /* X8 = &pxCurrentTCB */
   #else
      adrp    X8, pxCurrentTCBs
      add     X8, X8, :lo12:pxCurrentTCBs  /* X8 = &pxCurrentTCBs */
      /* Get the core ID to index the TCB correctly. */
      MRS X10, MPIDR_EL1   /* Read the Multiprocessor Affinity Register */
      AND X10, X10, # 0xff /* Extract Aff0 which contains the core ID */
      LSL X10, X10, # 3    /* Scale the core ID to the size of a pointer (64-bit system) */
      ADD X8, X8, X10      /* Add the offset for the current core's TCB pointer */
   #endif
   LDR X9, [ X8 ]
   MRS X8, SP_EL0
   STR X8, [ X9 ]         /* Store pxTopOfStack on task's TCB */
   ADD X9, X9, #8         /* X9 = X9 + 8. X1 now points to ullTaskUnprivilegedSP in TCB. */
   LDR X9, [ X9 ]
   MSR SP_EL0, X9        /* Use ullTaskUnprivilegedSP as SP_EL0. */
   LDR X10, [ SP ], # 0x10
   LDP X8, X9, [ SP ], # 0x10
#endif /* #if ( configENABLE_MPU == 1 ) */

   /* Switch to use the EL1 stack pointer. */
   MSR SPSEL, # 1
   .endm

/*-----------------------------------------------------------*/

/******************************************************************************
 * FreeRTOS_SWI_Handler handler is used to perform a context switch.
 *****************************************************************************/
   .align 8
   .type FreeRTOS_SWI_Handler, % function
FreeRTOS_SWI_Handler:
/* Save X0-X5 temporarily as they are used in the handler. */
STP X0, X1, [SP, #-0x10]!
STP X2, X3, [SP, #-0x10]!
STP X4, X5, [SP, #-0x10]!

MRS X4, ELR_EL1  /* Save exception return address. */
MRS X5, SPSR_EL1 /* Save program status register address. */

/* Decide action based on SVC immediate without corrupting any task context. */
MRS X0, ESR_EL1

/* Extract exception class. */
LSR X1, X0, # 26
CMP X1, # 0x15             /* 0x15 = SVC instruction. */
B.NE FreeRTOS_Abort

/* Extract SVC immediate from ISS[15:0]. */
AND X2, X0, # 0xFFFF

/* portSVC_YIELD: yield from a running task. */
CMP X2, # portSVC_YIELD
B.EQ FreeRTOS_Yield

/* portSVC_START_FIRST_TASK: start first task on this core without saving any prior context. */
CMP X2, # portSVC_START_FIRST_TASK
B.EQ Start_First_Task

1:
/* portSVC_DISABLE_INTERRUPTS: disable IRQs (DAIF.I) in SPSR_EL1 without touching task context. */
CMP X2, # portSVC_DISABLE_INTERRUPTS
B.NE 2f
ORR X5, X5, # (1 << portPSTATE_I_BIT) /* Set I bit in SPSR_EL1 */
MSR ELR_EL1, X4
MSR SPSR_EL1, X5
LDP X4, X5, [SP], #0x10
LDP X2, X3, [SP], #0x10
LDP X0, X1, [SP], #0x10
DSB SY
ISB SY
ERET

2:
/* portSVC_ENABLE_INTERRUPTS: enable IRQs (DAIF.I clear) in SPSR_EL1 without touching task context. */
CMP X2, # portSVC_ENABLE_INTERRUPTS
B.NE 3f
BIC X5, X5, # (1 << portPSTATE_I_BIT) /* Clear I bit in SPSR_EL1 */
MSR ELR_EL1, X4
MSR SPSR_EL1, X5
LDP X4, X5, [SP], #0x10
LDP X2, X3, [SP], #0x10
LDP X0, X1, [SP], #0x10
ERET

3:
/* portSVC_GET_CORE_ID: return core ID in X0 (Aff0 of MPIDR_EL1). */
CMP X2, # portSVC_GET_CORE_ID
B.NE 4f
MRS X0, MPIDR_EL1
AND X0, X0, # 0xff
MSR SPSR_EL1, X5
/* Restore X5-X1 while discarding old X0. */
LDP X4, X5, [SP], #0x10
LDP X2, X3, [ SP ], # 0x10
LDP XZR, X1, [ SP ], # 0x10
ERET

4:
/* portSVC_MASK_ALL_INTERRUPTS: set ICC_PMR_EL1 to max API mask and return previous-mask-equal flag in X0. */
CMP X2, # portSVC_MASK_ALL_INTERRUPTS
B.NE 5f
/* Read current PMR and compare. */
MRS X0, ICC_PMR_EL1
CMP X0, # portMAX_API_PRIORITY_MASK
B.EQ 41f
/* Disable IRQs while updating PMR. */
MSR DAIFSET, # 2
DSB SY
ISB SY
/* Write new PMR value. */
MOV X1, # portMAX_API_PRIORITY_MASK
MSR ICC_PMR_EL1, X1
DSB SY
ISB SY
/* Re-enable IRQs. */
MSR DAIFCLR, # 2
DSB SY
ISB SY
MSR ELR_EL1, X4
MSR SPSR_EL1, X5

41:
/* Restore X5-X1 while discarding old X0. */
LDP X4, X5, [ SP ], # 0x10
LDP X2, X3, [ SP ], # 0x10
LDP XZR, X1, [ SP ], # 0x10
ERET

5:
/* portSVC_UNMASK_ALL_INTERRUPTS: set ICC_PMR_EL1 to portUNMASK_VALUE to unmask all interrupts. */
CMP X2, # portSVC_UNMASK_ALL_INTERRUPTS
B.NE 6f
/* Disable IRQs while updating PMR. */
MSR DAIFSET, # 2
DSB SY
ISB SY
MOV X0, #portUNMASK_VALUE             /* Unmask all interrupts. */
MSR ICC_PMR_EL1, X0
DSB SY
ISB SY
/* Re-enable IRQs. */
MSR DAIFCLR, # 2
DSB SY
ISB SY
MSR ELR_EL1, X4
MSR SPSR_EL1, X5
LDP X4, X5, [SP], #0x10
LDP X2, X3, [SP], #0x10
LDP X0, X1, [SP], #0x10
ERET

6:
/* portSVC_UNMASK_INTERRUPTS: set ICC_PMR_EL1 to uxNewMaskValue stored in X0. */
CMP X2, # portSVC_UNMASK_INTERRUPTS
B.NE 7f
/* Disable IRQs while updating PMR. */
MSR DAIFSET, # 2
DSB SY
ISB SY
LDR X0, [ SP, # 0x20 ]                    /* Original X0 */
MSR ICC_PMR_EL1, X0
DSB SY
ISB SY
/* Re-enable IRQs. */
MSR DAIFCLR, # 2
DSB SY
ISB SY
MSR ELR_EL1, X4
MSR SPSR_EL1, X5
LDP X4, X5, [SP], #0x10
LDP X2, X3, [SP], #0x10
LDP X0, X1, [SP], #0x10
ERET

7:
#if ( configENABLE_MPU == 1 )
   /* portSVC_CHECK_PRIVILEGE: Check if the task is a privileged task */
   CMP X2, # portSVC_CHECK_PRIVILEGE
   B.NE 8f
   savefuncontextgpregs
   BL xPortIsTaskPrivileged
   restorefuncontextgpregexceptx0 /* xPortIsTaskPrivileged() return value is stored in X0. */
   MSR ELR_EL1, X4
   MSR SPSR_EL1, X5
   /* Restore X5-X1 while discarding old X0. */
   LDP X4, X5, [ SP ], # 0x10
   LDP X2, X3, [ SP ], # 0x10
   LDP XZR, X1, [ SP ], # 0x10
   ERET
#endif /* #if ( configENABLE_MPU == 1 ) */

8:
/* portSVC_SAVE_TASK_CONTEXT: Save task's context */
CMP X2, # portSVC_SAVE_TASK_CONTEXT
B.NE 9f
MSR ELR_EL1, X4
MSR SPSR_EL1, X5
/* Restore X5-X0. */
LDP X4, X5, [ SP ], # 0x10
LDP X2, X3, [ SP ], # 0x10
LDP X0, X1, [ SP ], # 0x10
portSAVE_CONTEXT
ERET

9:
/* portSVC_RESTORE_CONTEXT: Restore task's context */
CMP X2, # portSVC_RESTORE_CONTEXT
B.NE 10f
MSR ELR_EL1, X4
MSR SPSR_EL1, X5
/* Restore X5-X0. */
LDP X4, X5, [ SP ], # 0x10
LDP X2, X3, [ SP ], # 0x10
LDP X0, X1, [ SP ], # 0x10
portRESTORE_CONTEXT
ERET

10:
/* portSVC_DELETE_CURRENT_TASK: Delete current task */
CMP X2, # portSVC_DELETE_CURRENT_TASK
B.NE 11f
/* Restore X5-X0. */
LDP X4, X5, [ SP ], #0x10
LDP X2, X3, [ SP ], # 0x10
LDP X0, X1, [ SP ], # 0x10
#if ( configNUMBER_OF_CORES == 1 )
   adrp    X0, pxCurrentTCB
   add     X0, X0, :lo12:pxCurrentTCB   /* X0 = &pxCurrentTCB */
#else
   adrp    X0, pxCurrentTCBs
   add     X0, X0, :lo12:pxCurrentTCBs  /* X0 = &pxCurrentTCBs */
   /* Get the core ID to index the TCB correctly. */
   MRS X1, MPIDR_EL1  /* Read the Multiprocessor Affinity Register */
   AND X1, X1, # 0xff /* Extract Aff0 which contains the core ID */
   LSL X1, X1, # 3    /* Scale the core ID to the size of a pointer (64-bit system) */
   ADD X0, X0, X1     /* Add the offset for the current core's TCB pointer */
#endif
LDR X0, [ X0 ] /* X0 = pxCurrentTCB */
B vTaskDelete

11:
/* portSVC_INTERRUPT_CORE: Interrupt core */
CMP X2, # portSVC_INTERRUPT_CORE
B.NE 12f
LDR X0, [ SP, # 0x20 ]                    /* Original X0 */
MSR ICC_SGI1R_EL1, X0                     /* X0 contains the value to write to ICC_SGI1R_EL1 */
MSR ELR_EL1, X4
MSR SPSR_EL1, X5
/* Restore X5-X0. */
LDP X4, X5, [SP], #0x10
LDP X2, X3, [ SP ], # 0x10
LDP X0, X1, [ SP ], # 0x10
ERET

12:
#if ( configENABLE_MPU == 1 )
   /* ---------- SystemCallEnter? ---------------------------------*/
   LDR     X3, =NUM_SYSTEM_CALLS
   CMP     X2, X3
   BLO     121f                          /* imm 0 … NUM_SYSCALLS-1 */

   /* ---------- SystemCallExit? ----------------------------------*/
   LDR     X3, =portSVC_SYSTEM_CALL_EXIT
   CMP     X2, X3
   BEQ     122f

/* ---------- SystemCallEnter -------------------------------------*/
121:
   /* If calling task is privileged, directly tail-call the implementation at EL1. */
   savefuncontextgpregs
   BL xPortIsTaskPrivileged
   restorefuncontextgpregexceptx0         /* X0 holds pdTRUE if privileged */
   CBNZ X0, priv_path

   /* Unprivileged tasks path */
   #if ( configNUMBER_OF_CORES == 1 )
      adrp    X0, pxCurrentTCB
      add     X0, X0, :lo12:pxCurrentTCB   /* X0 = &pxCurrentTCB */
   #else
      adrp    X0, pxCurrentTCBs
      add     X0, X0, :lo12:pxCurrentTCBs  /* X0 = &pxCurrentTCBs */
      /* Get the core ID to index the TCB correctly. */
      MRS X1, MPIDR_EL1  /* Read the Multiprocessor Affinity Register */
      AND X1, X1, # 0xff /* Extract Aff0 which contains the core ID */
      LSL X1, X1, # 3    /* Scale the core ID to the size of a pointer (64-bit system) */
      ADD X0, X0, X1     /* Add the offset for the current core's TCB pointer */
   #endif
   LDR X0, [ X0 ]
   LDR X0, [ X0 ]         /* X0 = Location of saved context in TCB. */

   /* Save inputs (X0-X3) and LR (X30)
    * onto the current task's context to be used by the system call implementation.
    */
   STR X30, [ X0, # ( portOFFSET_TO_LR * 8 ) ]

   /* Read original X0, X1, X2, and X3 from the EL1 stack without modifying SP, and store.
    * [SP+0x20] -> X0, [SP+0x28] -> X1, [SP+0x10] -> X2, [SP+0x18] -> X3. */
   LDR X1, [ SP, # 0x20 ]                    /* Original X0 */
   STR X1, [ X0, # ( portOFFSET_TO_X0 * 8 ) ]
   LDR X1, [ SP, # 0x28 ]                    /* Original X1 */
   STR X1, [ X0, # ( portOFFSET_TO_X1 * 8 ) ]
   LDR X1, [ SP, # 0x10 ]                    /* Original X2 */
   STR X1, [ X0, # ( portOFFSET_TO_X2 * 8 ) ]
   LDR X1, [ SP, # 0x18 ]                    /* Original X3 */
   STR X1, [ X0, # ( portOFFSET_TO_X3 * 8 ) ]

   /* Restore X2-X5 to their original values, discard X1 and X0 as they contain system call number
    * and location of task's saved context in TCB.
    */
   MOV X1, X2                                /* Pass system call */
   LDP X4, X5, [ SP ], #0x10
   LDP X2, X3, [ SP ], #0x10
   ADD SP, SP, #0x10                         /* Discard X0 and X1 */

   savesyscallcontextgpregs
   BL  vSystemCallEnter   /* returns after programming ELR/SPSR/SP_EL0 and args */
   /* Set LR for the syscall implementation to point to vRequestSystemCallExit. */
   adrp    X30, vRequestSystemCallExit
   add     X30, X30, :lo12:vRequestSystemCallExit
   restoresyscallcontextgpregs
   ERET

priv_path:
   /* Load implementation address: uxSystemCallImplementations[X2] (64-bit entries). */
   adrp    X3, uxSystemCallImplementations
   add     X3, X3, :lo12:uxSystemCallImplementations
   LSL     X2, X2, #3           /* Multiply index by size of pointer (8 bytes). */
   ADD     X3, X3, X2           /* X3 = &uxSystemCallImplementations[X2] */
   LDR     X3, [ X3 ]           /* X3 = uxSystemCallImplementations[X2] */
   /* Return from exception directly to implementation; preserve original LR and registers. */
   MSR     ELR_EL1, X3
   MSR     SPSR_EL1, X5
   /* Restore X5-X0. */
   LDP     X4, X5, [ SP ], #0x10
   LDP     X2, X3, [ SP ], #0x10
   LDP     X0, X1, [ SP ], #0x10
   ERET

   /* ---------- SystemCallExit -----------------------------------*/
122:
   LDR     X0, [ SP, # 0x20 ]    /* Restore X0 without changing SP as it contains system call return value */
   savefuncontextgpregs
   BL      vSystemCallExit
   restorefuncontextgpregexceptx0
   /* Restore X5-X1 while discarding old X0. */
   LDP     X4, X5, [ SP ], #0x10
   LDP     X2, X3, [ SP ], #0x10
   LDP     XZR, X1, [ SP ], #0x10
   ERET
#endif /* #if ( configENABLE_MPU == 1 ) */

/* ---------- Unexpected EC – just hang in place ---------------------------*/
FreeRTOS_Abort:
B       FreeRTOS_Abort

FreeRTOS_Yield:
MSR SPSR_EL1, X5

/* Check if the task is in a critical section by inspecting ullCriticalNesting. */
#if ( configNUMBER_OF_CORES > 1 )
   adrp X0, ullCriticalNestings
   add  X0, X0, :lo12:ullCriticalNestings      /* X0 = &ullCriticalNestings */
   MRS  X1, MPIDR_EL1                          /* Read the Multiprocessor Affinity Register. */
   AND  X1, X1, # 0xff                         /* Extract Aff0 (core ID). */
   LSL  X1, X1, # 3                            /* Multiply core ID by pointer size (8 bytes). */
   ADD  X0, X0, X1                             /* Add offset to base address. */
   LDR  X1, [ X0 ]                             /* Load ullCriticalNesting for this core. */
   CBNZ X1, Skip_Context_Switch                /* Skip context switch if in a critical section. */
#endif

/* Restore X5-X0 to their original values before saving full context. */
LDP X4, X5, [SP], #0x10
LDP X2, X3, [SP], #0x10
LDP X0, X1, [SP], #0x10
portSAVE_CONTEXT
savefuncontextgpregs
#if ( configNUMBER_OF_CORES > 1 )
   MRS x0, mpidr_el1
   AND x0, x0, 255
#endif
BL vTaskSwitchContext
restorefuncontextgpregs
portRESTORE_CONTEXT
ERET

Skip_Context_Switch:
/* Restore X5-X0 to their original values. */
LDP X4, X5, [SP], #0x10
LDP X2, X3, [SP], #0x10
LDP X0, X1, [SP], #0x10
ERET

Start_First_Task:
   /* Restore X5-X0 to their original values. */
   LDP X4, X5, [SP], #0x10
   LDP X2, X3, [SP], #0x10
   LDP X0, X1, [SP], #0x10
   portRESTORE_CONTEXT
   ERET

/******************************************************************************
 * vPortSaveTaskContext is used to save the task's context into its stack.
 *****************************************************************************/
   .align 8
   .type vPortSaveTaskContext, % function
vPortSaveTaskContext:
portSAVE_CONTEXT
RET

/******************************************************************************
 * vPortRestoreTaskContext is used to start the scheduler.
 *****************************************************************************/
   .align 8
   .type vPortRestoreTaskContext, % function
vPortRestoreTaskContext:
.set freertos_vector_base, _freertos_vector_table
/* Install the FreeRTOS interrupt handlers. */
LDR X1, = freertos_vector_base
MSR VBAR_EL1, X1
DSB SY
ISB SY
/* Start the first task. */
portRESTORE_CONTEXT
ERET

/******************************************************************************
 * FreeRTOS_IRQ_Handler handles IRQ entry and exit.
 *
 * This handler is supposed to be used only for IRQs and never for FIQs. Per ARM
 * GIC documentation [1], Group 0 interrupts are always signaled as FIQs. Since
 * this handler is only for IRQs, We can safely assume Group 1 while accessing
 * Interrupt Acknowledge and End Of Interrupt registers and therefore, use
 * ICC_IAR1_EL1 and ICC_EOIR1_EL1.
 *
 * [1] https://developer.arm.com/documentation/198123/0300/Arm-CoreLink-GIC-fundamentals
 *****************************************************************************/
   .align 8
   .type FreeRTOS_IRQ_Handler, % function
FreeRTOS_IRQ_Handler:
/* Save volatile registers. */
saveallgpregisters
savefloatregisters

/* Save the SPSR and ELR. */
MRS X3, SPSR_EL1
MRS X2, ELR_EL1

STP X2, X3, [ SP, # - 0x10 ] !

/* Increment the interrupt nesting counter. */
#if ( configNUMBER_OF_CORES == 1 )
   adrp    X5, ullPortInterruptNesting
   add     X5, X5, :lo12:ullPortInterruptNesting   /* X5 = &ullPortInterruptNesting */
#else
   adrp    X5, ullPortInterruptNestings
   add     X5, X5, :lo12:ullPortInterruptNestings  /* X5 = &ullPortInterruptNestings */
   MRS X2, MPIDR_EL1  /* Read Multiprocessor Affinity Register. */
   AND X2, X2, # 0xff /* Extract Aff0, which contains the core ID. */
   LSL X2, X2, # 3    /* Scale core ID to the size of a pointer (assuming 64-bit system). */

   /* Calculate offset for the current core's ullPortYieldRequired and load its address. */
   ADD X5, X5, X2     /* Add offset for the current core's ullPortYieldRequired. */
#endif
LDR X1, [ X5 ]     /* Old nesting count in X1. */
ADD X6, X1, # 1
STR X6, [ X5 ]     /* Address of nesting count variable in X5. */

/* Maintain the interrupt nesting information across the function call. */
STP X1, X5, [ SP, # - 0x10 ] !

/* Read interrupt ID from the interrupt acknowledge register and store it
 * in X0 for future parameter and interrupt clearing use. */
MRS X0, ICC_IAR1_EL1

/* Maintain the interrupt ID value across the function call. */
STP X0, X1, [ SP, # - 0x10 ] !

savefuncontextgpregs
/* Call the C handler. */
BL vApplicationIRQHandler
restorefuncontextgpregs

/* Disable interrupts. */
MSR DAIFSET, # 2
DSB SY
ISB SY

/* Restore the interrupt ID value. */
LDP X0, X1, [ SP ], # 0x10

/* End IRQ processing by writing interrupt ID value to the EOI register. */
MSR ICC_EOIR1_EL1, X0

/* Restore the critical nesting count. */
LDP X1, X5, [ SP ], # 0x10

STR X1, [ X5 ]

/* Has interrupt nesting unwound? */
CMP X1, # 0
B.NE Exit_IRQ_No_Context_Switch

/* Is a context switch required? */
adrp    X0, ullPortYieldRequired
add     X0, X0, :lo12:ullPortYieldRequired  /* X0 = &ullPortYieldRequired */
#if ( configNUMBER_OF_CORES > 1 )
   MRS X2, MPIDR_EL1  /* Read Multiprocessor Affinity Register. */
   AND X2, X2, # 0xff /* Extract Aff0, which contains the core ID. */
   LSL X2, X2, # 3    /* Scale core ID to the size of a pointer (assuming 64-bit system). */
/* Calculate offset for the current core's ullPortYieldRequired and load its address. */
   ADD X0, X0, X2     /* Add offset for the current core's ullPortYieldRequired. */
#endif
LDR X1, [ X0 ]
CMP X1, # 0
B.EQ Exit_IRQ_No_Context_Switch

/* Check if the task is in a critical section by inspecting ullCriticalNesting. */
#if ( configNUMBER_OF_CORES > 1 )
   adrp X0, ullCriticalNestings
   add  X0, X0, :lo12:ullCriticalNestings      /* X0 = &ullCriticalNestings */
   MRS  X1, MPIDR_EL1                          /* Read the Multiprocessor Affinity Register. */
   AND  X1, X1, # 0xff                         /* Extract Aff0 (core ID). */
   LSL  X1, X1, # 3                            /* Multiply core ID by pointer size (8 bytes). */
   ADD  X0, X0, X1                             /* Add offset to base address. */
   LDR  X1, [ X0 ]                             /* Load ullCriticalNesting for this core. */
   CBNZ X1, Exit_IRQ_No_Context_Switch         /* Skip context switch if in a critical section. */
#endif

/* Reset ullPortYieldRequired to 0. */
MOV X2, # 0
STR X2, [ X0 ]

/* Restore volatile registers. */
LDP X4, X5, [ SP ], # 0x10 /* SPSR and ELR. */

MSR SPSR_EL1, X5
MSR ELR_EL1, X4
DSB SY
ISB SY

restorefloatregisters
restoreallgpregisters

/* Save the context of the current task and select a new task to run. */
portSAVE_CONTEXT
#if configNUMBER_OF_CORES > 1
   MRS x0, mpidr_el1
   AND x0, x0, 255
#endif
savefuncontextgpregs
BL vTaskSwitchContext
restorefuncontextgpregs
portRESTORE_CONTEXT
ERET

Exit_IRQ_No_Context_Switch:
/* Restore volatile registers. */
LDP X4, X5, [ SP ], # 0x10 /* SPSR and ELR. */

MSR SPSR_EL1, X5
MSR ELR_EL1, X4
DSB SY
ISB SY

restorefloatregisters
restoreallgpregisters

ERET

/******************************************************************************
 * If the application provides an implementation of vApplicationIRQHandler(),
 * then it will get called directly without saving the FPU registers on
 * interrupt entry, and this weak implementation of
 * vApplicationIRQHandler() will not get called.
 *
 * If the application provides its own implementation of
 * vApplicationFPUSafeIRQHandler() then this implementation of
 * vApplicationIRQHandler() will be called, save the FPU registers, and then
 * call vApplicationFPUSafeIRQHandler().
 *
 * Therefore, if the application writer wants FPU registers to be saved on
 * interrupt entry their IRQ handler must be called
 * vApplicationFPUSafeIRQHandler(), and if the application writer does not want
 * FPU registers to be saved on interrupt entry their IRQ handler must be
 * called vApplicationIRQHandler().
 *****************************************************************************/

   .align 8
   .weak vApplicationIRQHandler
   .type vApplicationIRQHandler, % function
vApplicationIRQHandler:

/* Save FPU registers (32 128-bits + 2 64-bits configuration and status registers). */
savefloatregisters

savefuncontextgpregs
/* Call the C handler. */
BL vApplicationFPUSafeIRQHandler
restorefuncontextgpregs

/* Restore FPU registers. */
restorefloatregisters

RET
   .end
