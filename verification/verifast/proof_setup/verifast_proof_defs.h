/*
 * This file contains defines to configure the VeriFast proof setup which are
 * not already handled in `port.c` or `portmacro.h`.
 *
 */

// /Users/reitobia/repos/forked/FreeRTOS-Kernel/verification/verifast/proof_setup_incremental/verifast_proof_defs.h


#ifndef VERIFAST_DEFS_H
    // The following defines are required by `FRTOS.h`
    // line 93
    #define configMAX_PRIORITIES 100

    // The following defines are required by `cdefs.h`
    #define __GNUC__ 10
    #define __STDC__ 1

    // line 827
    // This proof setup assumes an RP2040 processor (Raspberry Pi Pico).
    #define __arm__


#endif /* VERIFAST_DEFS_H */
