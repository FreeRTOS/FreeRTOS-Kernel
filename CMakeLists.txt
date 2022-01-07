cmake_minimum_required(VERSION 3.15)

# Absolute path to FreeRTOS config file directory
set(FREERTOS_CONFIG_FILE_DIRECTORY "" CACHE STRING "Absolute path to the directory with FreeRTOSConfig.h")
if(NOT FREERTOS_CONFIG_FILE_DIRECTORY)
    message(FATAL_ERROR " FreeRTOSConfig.h file directory not specified. Please specify absolute path to it from top-level CMake file:\n"
        "  set(FREERTOS_CONFIG_FILE_DIRECTORY <absolute path to FreeRTOSConfig.h directory> CACHE STRING \"\")\n"
        " or from CMake command line option:\n"
        "  -DFREERTOS_CONFIG_FILE_DIRECTORY='/absolute_path/to/FreeRTOSConfig.h/directory'")
endif()

# Heap number or absolute path to custom heap implementation provided by user
set(FREERTOS_HEAP "4" CACHE STRING "FreeRTOS heap model number. 1 .. 5. Or absolute path to custom heap source file")

# FreeRTOS ports
option(FREERTOS_PORT_BCC_16BIT_DOS_FLSH186 "FreeRTOS port (BCC) for 16 bit DOS Flsh186")
option(FREERTOS_PORT_BCC_16BIT_DOS_PC "FreeRTOS port (BCC) for 16 bit DOS PC")
option(FREERTOS_PORT_CCS_ARM_CM3 "FreeRTOS port (CCS) for ARM Cortex-M3")
option(FREERTOS_PORT_CCS_ARM_CM4F "FreeRTOS port (CCS) for ARM Cortex-M4 with FPU")
option(FREERTOS_PORT_CCS_ARM_CR4 "FreeRTOS port (CCS) for ARM Cortex-R4")
option(FREERTOS_PORT_CCS_MSP430X "FreeRTOS port (CCS) for MSP430X")
option(FREERTOS_PORT_CODEWARRIOR_COLDFIRE_V1 "FreeRTOS port (CoreWarrior) for ColdFire V1")
option(FREERTOS_PORT_CODEWARRIOR_COLDFIRE_V2 "FreeRTOS port (CoreWarrior) for ColdFire V2")
option(FREERTOS_PORT_CODEWARRIOR_HCS12 "FreeRTOS port (CoreWarrior) for HCS12")
option(FREERTOS_PORT_GCC_ARM_CA9 "FreeRTOS port (GCC) for ARM Cortex-A9")
option(FREERTOS_PORT_GCC_ARM_CA53_64_BIT "FreeRTOS port (GCC) for ARM Cortex-A53 64 bit")
option(FREERTOS_PORT_GCC_ARM_CA53_64_BIT_SRE "FreeRTOS port (GCC) for ARM Cortex-A53 64 bit SRE")
option(FREERTOS_PORT_GCC_ARM_CM0 "FreeRTOS port (GCC) for ARM Cortex-M0")
option(FREERTOS_PORT_GCC_ARM_CM3 "FreeRTOS port (GCC) for ARM Cortex-M3")
option(FREERTOS_PORT_GCC_ARM_CM3_MPU "FreeRTOS port (GCC) for ARM Cortex-M3 with MPU")
option(FREERTOS_PORT_GCC_ARM_CM4_MPU "FreeRTOS port (GCC) for ARM Cortex-M4 with MPU")
option(FREERTOS_PORT_GCC_ARM_CM4F "FreeRTOS port (GCC) for ARM Cortex-M4 with FPU")
option(FREERTOS_PORT_GCC_ARM_CM7 "FreeRTOS port (GCC) for ARM Cortex-M7")
option(FREERTOS_PORT_GCC_ARM_CM23_NONSECURE "FreeRTOS port (GCC) for ARM Cortex-M23 non-secure")
option(FREERTOS_PORT_GCC_ARM_CM23_SECURE "FreeRTOS port (GCC) for ARM Cortex-M23 secure")
option(FREERTOS_PORT_GCC_ARM_CM23_NTZ_NONSECURE "FreeRTOS port (GCC) for ARM Cortex-M23 non-trustzone non-secure")
option(FREERTOS_PORT_GCC_ARM_CM33_NONSECURE "FreeRTOS port (GCC) for ARM Cortex-M33 non-secure")
option(FREERTOS_PORT_GCC_ARM_CM33_SECURE "FreeRTOS port (GCC) for ARM Cortex-M33 secure")
option(FREERTOS_PORT_GCC_ARM_CM33_NTZ_NONSECURE "FreeRTOS port (GCC) for ARM Cortex-M33 non-trustzone non-secure")
option(FREERTOS_PORT_GCC_ARM_CR5 "FreeRTOS port (GCC) for ARM Cortex-R5")
option(FREERTOS_PORT_GCC_ARM_CRX_NOGIC "FreeRTOS port (GCC) for ARM Cortex-Rx no GIC")
option(FREERTOS_PORT_GCC_ARM7_AT91FR40008 "FreeRTOS port (GCC) for ARM7 Atmel AT91R40008")
option(FREERTOS_PORT_GCC_ARM7_AT91SAM7S "FreeRTOS port (GCC) for ARM7 Atmel AT91SAM7S")
option(FREERTOS_PORT_GCC_ARM7_LPC2000 "FreeRTOS port (GCC) for ARM7 LPC2000")
option(FREERTOS_PORT_GCC_ARM7_LPC23XX "FreeRTOS port (GCC) for ARM7 LPC23xx")
option(FREERTOS_PORT_GCC_ATMEGA323 "FreeRTOS port (GCC) for ATMega323")
option(FREERTOS_PORT_GCC_AVR32_UC3 "FreeRTOS port (GCC) for AVR32 UC3")
option(FREERTOS_PORT_GCC_COLDFIRE_V2 "FreeRTOS port (GCC) for ColdFire V2")
option(FREERTOS_PORT_GCC_CORTUS_APS3 "FreeRTOS port (GCC) for CORTUS APS3")
option(FREERTOS_PORT_GCC_H8S2329 "FreeRTOS port (GCC) for H8S2329")
option(FREERTOS_PORT_GCC_HCS12 "FreeRTOS port (GCC) for HCS12")
option(FREERTOS_PORT_GCC_IA32_FLAT "FreeRTOS port (GCC) for IA32 flat")
option(FREERTOS_PORT_GCC_MICROBLAZE "FreeRTOS port (GCC) for MicroBlaze")
option(FREERTOS_PORT_GCC_MICROBLAZE_V8 "FreeRTOS port (GCC) for MicroBlaze V8")
option(FREERTOS_PORT_GCC_MICROBLAZE_V9 "FreeRTOS port (GCC) for MicroBlaze V9")
option(FREERTOS_PORT_GCC_MSP430F449 "FreeRTOS port (GCC) for MSP430F449")
option(FREERTOS_PORT_GCC_NIOSII "FreeRTOS port (GCC) for NiosII")
option(FREERTOS_PORT_GCC_PPC405_XILINX "FreeRTOS port (GCC) for Xilinx PPC405")
option(FREERTOS_PORT_GCC_PPC440_XILINX "FreeRTOS port (GCC) for Xilinx PPC440")
option(FREERTOS_PORT_GCC_RISC_V "FreeRTOS port (GCC) for RISC-V")
option(FREERTOS_PORT_GCC_RISC_V_PULPINO_VEGA_RV32M1RM "FreeRTOS port (GCC) for RISC-V Pulpino Vega RV32M1RM")
option(FREERTOS_PORT_GCC_RL78 "FreeRTOS port (GCC) for Renesas RL78")
option(FREERTOS_PORT_GCC_RX100 "FreeRTOS port (GCC) for Renesas RX100")
option(FREERTOS_PORT_GCC_RX200 "FreeRTOS port (GCC) for Renesas RX200")
option(FREERTOS_PORT_GCC_RX600 "FreeRTOS port (GCC) for Renesas RX600")
option(FREERTOS_PORT_GCC_RX600_V2 "FreeRTOS port (GCC) for Renesas RX600 v2")
option(FREERTOS_PORT_GCC_RX700_V3_DPFPU "FreeRTOS port (GCC) for Renesas RX700 v3 with DPFPU")
option(FREERTOS_PORT_GCC_STR75X "FreeRTOS port (GCC) for STR75x")
option(FREERTOS_PORT_GCC_TRICORE_1782 "FreeRTOS port (GCC) for TriCore 1782")
option(FREERTOS_PORT_GCC_ARC_EM_HS "FreeRTOS port (GCC) for DesignWare ARC EM HS")
option(FREERTOS_PORT_GCC_ARC_V1 "FreeRTOS port (GCC) for DesignWare ARC v1")
option(FREERTOS_PORT_GCC_ARM_CM33_TFM "FreeRTOS port (GCC) for ARM Cortex-M33 trusted firmware")
option(FREERTOS_PORT_GCC_ATMEGA "FreeRTOS port (GCC) for ATmega")
option(FREERTOS_PORT_GCC_POSIX "FreeRTOS port (GCC) for Posix")
option(FREERTOS_PORT_GCC_RP2040 "FreeRTOS port for RP2040 ARM Cortex-M0+")
option(FREERTOS_PORT_GCC_XTENSA_ESP32 "FreeRTOS port (GCC) for Xtensa ESP32")
option(FREERTOS_PORT_GCC_AVRDX "FreeRTOS port (GCC) for AVRDx")
option(FREERTOS_PORT_GCC_AVR_MEGA0 "FreeRTOS port (GCC) for AVR Mega0")
option(FREERTOS_PORT_IAR_78K0K "FreeRTOS port (IAR) for Renesas 78K0K")
option(FREERTOS_PORT_IAR_ARM_CA5_NOGIC "FreeRTOS port (IAR) for ARM Cortex-A5 no GIC")
option(FREERTOS_PORT_IAR_ARM_CA9 "FreeRTOS port (IAR) for ARM Cortex-A9")
option(FREERTOS_PORT_IAR_ARM_CM0 "FreeRTOS port (IAR) for ARM Cortex-M0")
option(FREERTOS_PORT_IAR_ARM_CM3 "FreeRTOS port (IAR) for ARM Cortex-M3")
option(FREERTOS_PORT_IAR_ARM_CM4F "FreeRTOS port (IAR) for ARM Cortex-M4 with FPU")
option(FREERTOS_PORT_IAR_ARM_CM4F_MPU "FreeRTOS port (IAR) for ARM Cortex-M4 with FPU and MPU")
option(FREERTOS_PORT_IAR_ARM_CM7 "FreeRTOS port (IAR) for ARM Cortex-M7")
option(FREERTOS_PORT_IAR_ARM_CM23_NONSECURE "FreeRTOS port (IAR) for ARM Cortex-M23 non-secure")
option(FREERTOS_PORT_IAR_ARM_CM23_SECURE "FreeRTOS port (IAR) for ARM Cortex-M23 secure")
option(FREERTOS_PORT_IAR_ARM_CM23_NTZ_NONSECURE "FreeRTOS port (GCC) for ARM Cortex-M23 non-trustzone non-secure")
option(FREERTOS_PORT_IAR_ARM_CM33_NONSECURE "FreeRTOS port (IAR) for ARM Cortex-M33 non-secure")
option(FREERTOS_PORT_IAR_ARM_CM33_SECURE "FreeRTOS port (IAR) for ARM Cortex-M33 secure")
option(FREERTOS_PORT_IAR_ARM_CM33_NTZ_NONSECURE "FreeRTOS port (GCC) for ARM Cortex-M33 non-trustzone non-secure")
option(FREERTOS_PORT_IAR_ARM_CRX_NOGIC "FreeRTOS port (IAR) for ARM Cortex-Rx no GIC")
option(FREERTOS_PORT_IAR_ATMEGA323 "FreeRTOS port (IAR) for ATMega323")
option(FREERTOS_PORT_IAR_ATMEL_SAM7S64 "FreeRTOS port (IAR) for Atmel SAM7S64")
option(FREERTOS_PORT_IAR_ATMEL_SAM9XE "FreeRTOS port (IAR) for Atmel SAM9XE")
option(FREERTOS_PORT_IAR_AVR_AVRDX "FreeRTOS port (IAR) for AVRDx")
option(FREERTOS_PORT_IAR_AVR_MEGA0 "FreeRTOS port (IAR) for AVR Mega0")
option(FREERTOS_PORT_IAR_AVR32_UC3 "FreeRTOS port (IAR) for AVR32 UC3")
option(FREERTOS_PORT_IAR_LPC2000 "FreeRTOS port (IAR) for LPC2000")
option(FREERTOS_PORT_IAR_MSP430 "FreeRTOS port (IAR) for MSP430")
option(FREERTOS_PORT_IAR_MSP430X "FreeRTOS port (IAR) for MSP430X")
option(FREERTOS_PORT_IAR_RISC_V "FreeRTOS port (IAR) for RISC-V")
option(FREERTOS_PORT_IAR_RL78 "FreeRTOS port (IAR) for Renesas RL78")
option(FREERTOS_PORT_IAR_RX100 "FreeRTOS port (IAR) for Renesas RX100")
option(FREERTOS_PORT_IAR_RX600 "FreeRTOS port (IAR) for Renesas RX600")
option(FREERTOS_PORT_IAR_RX700_V3_DPFPU "FreeRTOS port (IAR) for Renesas RX700 v3 with DPFPU")
option(FREERTOS_PORT_IAR_RX_V2 "FreeRTOS port (IAR) for Renesas RX v2")
option(FREERTOS_PORT_IAR_STR71X "FreeRTOS port (IAR) for STR71x")
option(FREERTOS_PORT_IAR_STR75X "FreeRTOS port (IAR) for STR75x")
option(FREERTOS_PORT_IAR_STR91X "FreeRTOS port (IAR) for STR91x")
option(FREERTOS_PORT_IAR_V850ES_FX3 "FreeRTOS port (IAR) for Renesas V850ES/Fx3")
option(FREERTOS_PORT_IAR_V850ES_HX3 "FreeRTOS port (IAR) for Renesas V850ES/Hx3")
option(FREERTOS_PORT_MIKROC_ARM_CM4F "FreeRTOS port (MikroC) for ARM Cortex-M4 with FPU")
option(FREERTOS_PORT_MPLAB_PIC18F "FreeRTOS port (MPLAB) for PIC18F")
option(FREERTOS_PORT_MPLAB_PIC24 "FreeRTOS port (MPLAB) for PIC24")
option(FREERTOS_PORT_MPLAB_PIC32MEC14XX "FreeRTOS port (MPLAB) for PIC32MEC14xx")
option(FREERTOS_PORT_MPLAB_PIC32MX "FreeRTOS port (MPLAB) for PIC32MX")
option(FREERTOS_PORT_MPLAB_PIC32MZ "FreeRTOS port (MPLAB) for PIC32MZ")
option(FREERTOS_PORT_MSVC_MINGW "FreeRTOS port for x86 MSVC or MinGW")
option(FREERTOS_PORT_OWATCOM_16BIT_DOS_FLSH186 "FreeRTOS port (Open Watcom) for 16 bit DOS Flsh186")
option(FREERTOS_PORT_OWATCOM_16BIT_DOS_PC "FreeRTOS port (Open Watcom) for 16 bit DOS PC")
option(FREERTOS_PORT_PARADIGM_TERN_EE_LARGE "FreeRTOS port (Paradigm) for Tern EE large")
option(FREERTOS_PORT_PARADIGM_TERN_EE_SMALL "FreeRTOS port (Paradigm) for Tern EE small")
option(FREERTOS_PORT_RENESAS_RX100 "FreeRTOS port (Renesas) for RX100")
option(FREERTOS_PORT_RENESAS_RX200 "FreeRTOS port (Renesas) for RX200")
option(FREERTOS_PORT_RENESAS_RX600 "FreeRTOS port (Renesas) for RX600")
option(FREERTOS_PORT_RENESAS_RX600_V2 "FreeRTOS port (Renesas) for RX600 v2")
option(FREERTOS_PORT_RENESAS_RX700_V3_DPFPU "FreeRTOS port (Renesas) for RX700 v3 with DPFPU")
option(FREERTOS_PORT_RENESAS_SH2A_FPU "FreeRTOS port (Renesas) for SH2A with FPU")
option(FREERTOS_PORT_ROWLEY_MSP430F449 "FreeRTOS port (Rowley) for MSP430F449")
option(FREERTOS_PORT_RVDS_ARM_CA9 "FreeRTOS port (RVDS) for ARM Cortex-A9")
option(FREERTOS_PORT_RVDS_ARM_CM0 "FreeRTOS port (RVDS) for ARM Cortex-M0")
option(FREERTOS_PORT_RVDS_ARM_CM3 "FreeRTOS port (RVDS) for ARM Cortex-M3")
option(FREERTOS_PORT_RVDS_ARM_CM4_MPU "FreeRTOS port (RVDS) for ARM Cortex-M4 with MPU")
option(FREERTOS_PORT_RVDS_ARM_CM4F "FreeRTOS port (RVDS) for ARM Cortex-M4 with FPU")
option(FREERTOS_PORT_RVDS_ARM_CM7 "FreeRTOS port (RVDS) for ARM Cortex-M7")
option(FREERTOS_PORT_RVDS_ARM7_LPC21XX "FreeRTOS port (RVDS) for ARM7 LPC21xx")
option(FREERTOS_PORT_SDCC_CYGNAL "FreeRTOS port (SDCC) for Cygnal")
option(FREERTOS_PORT_SOFTUNE_MB91460 "FreeRTOS port (Softune) for MB91460")
option(FREERTOS_PORT_SOFTUNE_MB96340 "FreeRTOS port (Softune) for MB96340")
option(FREERTOS_PORT_TASKING_ARM_CM4F "FreeRTOS port (Tasking) for ARM Cortex-M4 with FPU")
option(FREERTOS_PORT_CDK_THEAD_CK802 "FreeRTOS port (CDK) for T-head CK802")
option(FREERTOS_PORT_XCC_XTENSA "FreeRTOS port (XCC) for Xtensa")
option(FREERTOS_PORT_WIZC_PIC18 "FreeRTOS port (WizC) for PIC18")

add_library(freertos_kernel STATIC
    croutine.c
    event_groups.c
    list.c
    queue.c
    stream_buffer.c
    tasks.c
    timers.c
    portable/Common/mpu_wrappers.c

    # If FREERTOS_HEAP is digit between 1 .. 5 - it is heap number, otherwise - it is path to custom heap source file
    $<IF:$<BOOL:$<FILTER:${FREERTOS_HEAP},EXCLUDE,^[1-5]$>>,${FREERTOS_HEAP},portable/MemMang/heap_${FREERTOS_HEAP}.c>

    $<$<BOOL:${FREERTOS_PORT_BCC_16BIT_DOS_FLSH186}>:portable/BCC/16BitDOS/common/portcomn.c;portable/BCC/16BitDOS/Flsh186/port.c>
    $<$<BOOL:${FREERTOS_PORT_BCC_16BIT_DOS_PC}>:portable/BCC/16BitDOS/common/portcomn.c;portable/BCC/16BitDOS/PC/port.c>
    $<$<BOOL:${FREERTOS_PORT_CCS_ARM_CM3}>:portable/CCS/ARM_CM3/port.c;portable/CCS/ARM_CM3/portasm.asm>
    $<$<BOOL:${FREERTOS_PORT_CCS_ARM_CM4F}>:portable/CCS/ARM_CM4F/port.c;portable/CCS/ARM_CM4F/portasm.asm>
    $<$<BOOL:${FREERTOS_PORT_CCS_ARM_CR4}>:portable/CCS/ARM_Cortex-R4/port.c;portable/CCS/ARM_Cortex-R4/portASM.asm>
    $<$<BOOL:${FREERTOS_PORT_CCS_MSP430X}>:portable/CCS/MSP430X/port.c;portable/CCS/MSP430X/portext.asm>
    $<$<BOOL:${FREERTOS_PORT_CODEWARRIOR_COLDFIRE_V1}>:portable/CodeWarrior/ColdFire_V1/port.c;portable/CodeWarrior/ColdFire_V1/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_CODEWARRIOR_COLDFIRE_V2}>:portable/CodeWarrior/ColdFire_V2/port.c;portable/CodeWarrior/ColdFire_V2/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_CODEWARRIOR_HCS12}>:portable/CodeWarrior/HCS12/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CA9}>:portable/GCC/ARM_CA9/port.c;portable/GCC/ARM_CA9/portASM.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CA53_64_BIT}>:portable/GCC/ARM_CA53_64_BIT/port.c;portable/GCC/ARM_CA53_64_BIT/portASM.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CA53_64_BIT_SRE}>:portable/GCC/ARM_CA53_64_BIT_SRE/port.c;portable/GCC/ARM_CA53_64_BIT_SRE/portASM.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM0}>:portable/GCC/ARM_CM0/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM3}>:portable/GCC/ARM_CM3/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM3_MPU}>:portable/GCC/ARM_CM3_MPU/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM4_MPU}>:portable/GCC/ARM_CM4_MPU/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM4F}>:portable/GCC/ARM_CM4F/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM7}>:portable/GCC/ARM_CM7/r0p1/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM23_NONSECURE}>:portable/GCC/ARM_CM23/non_secure/port.c;portable/GCC/ARM_CM23/non_secure/portasm.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM23_SECURE}>:portable/GCC/ARM_CM23/secure/secure_context_port.c;portable/GCC/ARM_CM23/secure/secure_context.c;portable/GCC/ARM_CM23/secure/secure_heap.c;portable/GCC/ARM_CM23/secure/secure_init.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM23_NTZ_NONSECURE}>:portable/GCC/ARM_CM23_NTZ/non_secure/port.c;portable/GCC/ARM_CM23_NTZ/non_secure/portasm.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM33_NONSECURE}>:portable/GCC/ARM_CM33/non_secure/port.c;portable/GCC/ARM_CM33/non_secure/portasm.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM33_SECURE}>:portable/GCC/ARM_CM33/secure/secure_context_port.c;portable/GCC/ARM_CM33/secure/secure_context.c;portable/GCC/ARM_CM33/secure/secure_heap.c;portable/GCC/ARM_CM33/secure/secure_init.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM33_NTZ_NONSECURE}>:portable/GCC/ARM_CM33_NTZ/non_secure/port.c;portable/GCC/ARM_CM33_NTZ/non_secure/portasm.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CR5}>:portable/GCC/ARM_CR5/port.c;portable/GCC/ARM_CR5/portASM.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CRX_NOGIC}>:portable/GCC/ARM_CRx_No_GIC/port.c;portable/GCC/ARM_CRx_No_GIC/portASM.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM7_AT91FR40008}>:portable/GCC/ARM7_AT91FR40008/port.c;portable/GCC/ARM7_AT91FR40008/portISR.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM7_AT91SAM7S}>:portable/GCC/ARM7_AT91SAM7S/lib_AT91SAM7X256.c;portable/GCC/ARM7_AT91SAM7S/port.c;portable/GCC/ARM7_AT91SAM7S/portISR.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM7_LPC2000}>:portable/GCC/ARM7_LPC2000/port.c;portable/GCC/ARM7_LPC2000/portISR.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM7_LPC23XX}>:portable/GCC/ARM7_LPC23xx/port.c;portable/GCC/ARM7_LPC23xx/portISR.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ATMEGA323}>:portable/GCC/ATMega323/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_AVR32_UC3}>:portable/GCC/AVR32_UC3/exception.S;portable/GCC/AVR32_UC3/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_COLDFIRE_V2}>:portable/GCC/ColdFire_V2/port.c;portable/GCC/ColdFire_V2/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_CORTUS_APS3}>:portable/GCC/CORTUS_APS3/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_H8S2329}>:portable/GCC/H8S2329/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_HCS12}>:portable/GCC/HCS12/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_IA32_FLAT}>:portable/GCC/IA32_flat/port.c;portable/GCC/IA32_flat/portASM.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_MICROBLAZE}>:portable/GCC/MicroBlaze/port.c;portable/GCC/MicroBlaze/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_GCC_MICROBLAZE_V8}>:portable/GCC/MicroBlazeV8/port.c;portable/GCC/MicroBlazeV8/port_exceptions.c;portable/GCC/MicroBlazeV8/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_MICROBLAZE_V9}>:portable/GCC/MicroBlazeV9/port.c;portable/GCC/MicroBlazeV9/port_exceptions.c;portable/GCC/MicroBlazeV9/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_MSP430F449}>:portable/GCC/MSP430F449/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_NIOSII}>:portable/GCC/NiosII/port.c;portable/GCC/NiosII/port_asm.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_PPC405_XILINX}>:portable/GCC/PPC405_Xilinx/port.c;portable/GCC/PPC405_Xilinx/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_PPC440_XILINX}>:portable/GCC/PPC440_Xilinx/port.c;portable/GCC/PPC440_Xilinx/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_RISC_V}>:portable/GCC/RISC-V/port.c;portable/GCC/RISC-V/portASM.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_RISC_V_PULPINO_VEGA_RV32M1RM}>:portable/GCC/RISC-V/port.c;portable/GCC/RISC-V/portASM.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_RL78}>:portable/GCC/RL78/port.c;portable/GCC/RL78/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_RX100}>:portable/GCC/RX100/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_RX200}>:portable/GCC/RX200/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_RX600}>:portable/GCC/RX600/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_RX600_V2}>:portable/GCC/RX600v2/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_RX700_V3_DPFPU}>:portable/GCC/RX700v3_DPFPU/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_STR75X}>:portable/GCC/STR75x/port.c;portable/GCC/STR75x/portISR.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_TRICORE_1782}>:portable/GCC/TriCore_1782/port.c;portable/GCC/TriCore_1782/porttrap.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARC_EM_HS}>:portable/ThirdParty/GCC/ARC_EM_HS/arc_freertos_exceptions.c;portable/ThirdParty/GCC/ARC_EM_HS/arc_support.s;portable/ThirdParty/GCC/ARC_EM_HS/freertos_tls.c;portable/ThirdParty/GCC/ARC_EM_HS/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARC_V1}>:portable/ThirdParty/GCC/ARC_v1/arc_freertos_exceptions.c;portable/ThirdParty/GCC/ARC_v1/arc_support.s;portable/ThirdParty/GCC/ARC_v1/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM33_TFM}>:portable/ThirdParty/GCC/ARM_CM33_TFM/os_wrapper_freertos.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_ATMEGA}>:portable/ThirdParty/GCC/ATmega/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_POSIX}>:portable/ThirdParty/GCC/Posix/port.c;portable/ThirdParty/GCC/Posix/utils/wait_for_event.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_RP2040}>:portable/ThirdParty/GCC/RP2040/idle_task_static_memory.c;portable/ThirdParty/GCC/RP2040/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_XTENSA_ESP32}>:portable/ThirdParty/GCC/Xtensa_ESP32/FreeRTOS-openocd.c;portable/ThirdParty/GCC/Xtensa_ESP32/port.c;portable/ThirdParty/GCC/Xtensa_ESP32/portasm.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_context.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_init.c;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_intr_asm.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_intr.c;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_loadstore_handler.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_overlay_os_hook.c;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_vector_defaults.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_vectors.S>
    $<$<BOOL:${FREERTOS_PORT_GCC_AVRDX}>:portable/ThirdParty/Partner-Supported-Ports/GCC/AVR_AVRDx/port.c>
    $<$<BOOL:${FREERTOS_PORT_GCC_AVR_MEGA0}>:portable/ThirdParty/Partner-Supported-Ports/GCC/AVR_Mega0/port.c>
    $<$<BOOL:${FREERTOS_PORT_IAR_78K0K}>:portable/IAR/78K0R/port.c;portable/IAR/78K0R/portasm.s26>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CA5_NOGIC}>:portable/IAR/ARM_CA5_No_GIC/port.c;portable/IAR/ARM_CA5_No_GIC/portASM.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CA9}>:portable/IAR/ARM_CA9/port.c;portable/IAR/ARM_CA9/portASM.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM0}>:portable/IAR/ARM_CM0/port.c;portable/IAR/ARM_CM0/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM3}>:portable/IAR/ARM_CM3/port.c;portable/IAR/ARM_CM3/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM4F}>:portable/IAR/ARM_CM4F/port.c;portable/IAR/ARM_CM4F/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM4F_MPU}>:portable/IAR/ARM_CM4F_MPU/port.c;portable/IAR/ARM_CM4F_MPU/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM7}>:portable/IAR/ARM_CM7/r0p1/port.c;portable/IAR/ARM_CM7/r0p1/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM23_NONSECURE}>:portable/IAR/ARM_CM23/non_secure/port.c;portable/IAR/ARM_CM23/non_secure/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM23_SECURE}>:portable/IAR/ARM_CM23/secure/secure_context_port_asm.s;portable/IAR/ARM_CM23/secure/secure_context.c;portable/IAR/ARM_CM23/secure/secure_heap.c;portable/IAR/ARM_CM23/secure/secure_init.c>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM23_NTZ_NONSECURE}>:portable/IAR/ARM_CM23_NTZ/non_secure/port.c;portable/IAR/ARM_CM23_NTZ/non_secure/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM33_NONSECURE}>:portable/IAR/ARM_CM33/non_secure/port.c;portable/IAR/ARM_CM33/non_secure/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM33_SECURE}>:portable/IAR/ARM_CM33/secure/secure_context_port_asm.s;portable/IAR/ARM_CM33/secure/secure_context.c;portable/IAR/ARM_CM33/secure/secure_heap.c;portable/IAR/ARM_CM33/secure/secure_init.c>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM33_NTZ_NONSECURE}>:portable/IAR/ARM_CM33_NTZ/non_secure/port.c;portable/IAR/ARM_CM33_NTZ/non_secure/portasm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CRX_NOGIC}>:portable/IAR/ARM_CRx_No_GIC/port.c;portable/IAR/ARM_CRx_No_GIC/portASM.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_ATMEGA323}>:portable/IAR/ATMega323/port.c;portable/IAR/ATMega323/portmacro.s90>
    $<$<BOOL:${FREERTOS_PORT_IAR_ATMEL_SAM7S64}>:portable/IAR/AtmelSAM7S64/port.c;portable/IAR/AtmelSAM7S64/portasm.s79>
    $<$<BOOL:${FREERTOS_PORT_IAR_ATMEL_SAM9XE}>:portable/IAR/AtmelSAM9XE/port.c;portable/IAR/AtmelSAM9XE/portasm.s79>
    $<$<BOOL:${FREERTOS_PORT_IAR_AVR_AVRDX}>:portable/IAR/AVR_AVRDx/port.c;portable/IAR/AVR_AVRDx/portmacro.s90>
    $<$<BOOL:${FREERTOS_PORT_IAR_AVR_MEGA0}>:portable/IAR/AVR_Mega0/port.c;portable/IAR/AVR_Mega0/portmacro.s90>
    $<$<BOOL:${FREERTOS_PORT_IAR_AVR32_UC3}>:portable/IAR/AVR32_UC3/exception.s82;portable/IAR/AVR32_UC3/port.c;portable/IAR/AVR32_UC3/read.c;portable/IAR/AVR32_UC3/write.c>
    $<$<BOOL:${FREERTOS_PORT_IAR_LPC2000}>:portable/IAR/LPC2000/port.c;portable/IAR/LPC2000/portasm.s79>
    $<$<BOOL:${FREERTOS_PORT_IAR_MSP430}>:portable/IAR/MSP430/port.c;portable/IAR/MSP430/portext.s43>
    $<$<BOOL:${FREERTOS_PORT_IAR_MSP430X}>:portable/IAR/MSP430X/port.c;portable/IAR/MSP430X/portext.s43>
    $<$<BOOL:${FREERTOS_PORT_IAR_RISC_V}>:portable/IAR/RISC-V/port.c;portable/IAR/RISC-V/portASM.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_RL78}>:portable/IAR/RL78/port.c;portable/IAR/RL78/portasm.s87>
    $<$<BOOL:${FREERTOS_PORT_IAR_RX100}>:portable/IAR/RX100/port.c;portable/IAR/RX100/port_asm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_RX600}>:portable/IAR/RX600/port.c;portable/IAR/RX600/port_asm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_RX700_V3_DPFPU}>:portable/IAR/RX700v3_DPFPU/port.c>
    $<$<BOOL:${FREERTOS_PORT_IAR_RX_V2}>:portable/IAR/RXv2/port.c;portable/IAR/RXv2/port_asm.s>
    $<$<BOOL:${FREERTOS_PORT_IAR_STR71X}>:portable/IAR/STR71x/port.c;portable/IAR/STR71x/portasm.s79>
    $<$<BOOL:${FREERTOS_PORT_IAR_STR75X}>:portable/IAR/STR75x/port.c;portable/IAR/STR75x/portasm.s79>
    $<$<BOOL:${FREERTOS_PORT_IAR_STR91X}>:portable/IAR/STR91x/port.c;portable/IAR/STR91x/portasm.s79>
    $<$<BOOL:${FREERTOS_PORT_IAR_V850ES_FX3}>:portable/IAR/V850ES/port.c;portable/IAR/V850ES/portasm_Fx3.s85>
    $<$<BOOL:${FREERTOS_PORT_IAR_V850ES_HX3}>:portable/IAR/V850ES/port.c;portable/IAR/V850ES/portasm_Hx2.s85>
    $<$<BOOL:${FREERTOS_PORT_MIKROC_ARM_CM4F}>:portable/MikroC/ARM_CM4F/port.c>
    $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC18F}>:portable/MPLAB/PIC18F/port.c>
    $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC24}>:portable/MPLAB/PIC24_dsPIC/port.c;portable/MPLAB/PIC24_dsPIC/portasm_PIC24.S> # TODO: What to do with portasm_dsPIC.S ?
    $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC32MEC14XX}>:portable/MPLAB/PIC32MEC14xx/port.c;portable/MPLAB/PIC32MEC14xx/port_asm.S>
    $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC32MX}>:portable/MPLAB/PIC32MX/port.c;portable/MPLAB/PIC32MX/port_asm.S>
    $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC32MZ}>:portable/MPLAB/PIC32MZ/port.c;portable/MPLAB/PIC32MZ/port_asm.S>
    $<$<BOOL:${FREERTOS_PORT_MSVC_MINGW}>:portable/MSVC-MingW/port.c>
    $<$<BOOL:${FREERTOS_PORT_OWATCOM_16BIT_DOS_FLSH186}>:portable/oWatcom/16BitDOS/common/portcomn.c;portable/oWatcom/16BitDOS/Flsh186/port.c>
    $<$<BOOL:${FREERTOS_PORT_OWATCOM_16BIT_DOS_PC}>:portable/oWatcom/16BitDOS/common/portcomn.c;portable/oWatcom/16BitDOS/PC/port.c>
    $<$<BOOL:${FREERTOS_PORT_PARADIGM_TERN_EE_LARGE}>:portable/Paradigm/Tern_EE/large_untested/port.c>
    $<$<BOOL:${FREERTOS_PORT_PARADIGM_TERN_EE_SMALL}>:portable/Paradigm/Tern_EE/small/port.c>
    $<$<BOOL:${FREERTOS_PORT_RENESAS_RX100}>:portable/Renesas/RX100/port.c;portable/Renesas/RX100/port_asm.src>
    $<$<BOOL:${FREERTOS_PORT_RENESAS_RX200}>:portable/Renesas/RX200/port.c;portable/Renesas/RX200/port_asm.src>
    $<$<BOOL:${FREERTOS_PORT_RENESAS_RX600}>:portable/Renesas/RX600/port.c;portable/Renesas/RX600/port_asm.src>
    $<$<BOOL:${FREERTOS_PORT_RENESAS_RX600_V2}>:portable/Renesas/RX600v2/port.c;portable/Renesas/RX600v2/port_asm.src>
    $<$<BOOL:${FREERTOS_PORT_RENESAS_RX700_V3_DPFPU}>:portable/Renesas/RX700v3_DPFPU/port.c;portable/Renesas/RX700v3_DPFPU/port_asm.src>
    $<$<BOOL:${FREERTOS_PORT_RENESAS_SH2A_FPU}>:portable/Renesas/SH2A_FPU/port.c;portable/Renesas/SH2A_FPU/portasm.src>
    $<$<BOOL:${FREERTOS_PORT_ROWLEY_MSP430F449}>:portable/Rowley/MSP430F449/port.c;portable/Rowley/MSP430F449/portext.asm>
    $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CA9}>:portable/RVDS/ARM_CA9/port.c;portable/RVDS/ARM_CA9/portASM.s>
    $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM0}>:portable/RVDS/ARM_CM0/port.c>
    $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM3}>:portable/RVDS/ARM_CM3/port.c>
    $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM4_MPU}>:portable/RVDS/ARM_CM4_MPU/port.c>
    $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM4F}>:portable/RVDS/ARM_CM4F/port.c>
    $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM7}>:portable/RVDS/ARM_CM7/r0p1/port.c>
    $<$<BOOL:${FREERTOS_PORT_RVDS_ARM7_LPC21XX}>:portable/RVDS/ARM7_LPC21xx/port.c;portable/RVDS/ARM7_LPC21xx/portASM.s>
    $<$<BOOL:${FREERTOS_PORT_SDCC_CYGNAL}>:portable/SDCC/Cygnal/port.c>
    $<$<BOOL:${FREERTOS_PORT_SOFTUNE_MB91460}>:portable/Softune/MB91460/__STD_LIB_sbrk.c;portable/Softune/MB91460/port.c>
    $<$<BOOL:${FREERTOS_PORT_SOFTUNE_MB96340}>:portable/Softune/MB96340/__STD_LIB_sbrk.c;portable/Softune/MB96340/port.c>
    $<$<BOOL:${FREERTOS_PORT_TASKING_ARM_CM4F}>:portable/Tasking/ARM_CM4F/port.c;portable/Tasking/ARM_CM4F/port_asm.asm>
    $<$<BOOL:${FREERTOS_PORT_CDK_THEAD_CK802}>:portable/ThirdParty/CDK/T-HEAD_CK802/port.c;portable/ThirdParty/CDK/T-HEAD_CK802/portasm.S>
    $<$<BOOL:${FREERTOS_PORT_XCC_XTENSA}>:portable/ThirdParty/XCC/Xtensa/port.c;portable/ThirdParty/XCC/Xtensa/portasm.S;portable/ThirdParty/XCC/Xtensa/portclib.c;portable/ThirdParty/XCC/Xtensa/xtensa_context.S;portable/ThirdParty/XCC/Xtensa/xtensa_init.c;portable/ThirdParty/XCC/Xtensa/xtensa_intr_asm.S;portable/ThirdParty/XCC/Xtensa/xtensa_intr.c;portable/ThirdParty/XCC/Xtensa/xtensa_overlay_os_hook.c;portable/ThirdParty/XCC/Xtensa/xtensa_vectors.S>
    $<$<BOOL:${FREERTOS_PORT_WIZC_PIC18}>:portable/WizC/PIC18/port.c;portable/WizC/PIC18/Drivers/Tick/isrTick.c;portable/WizC/PIC18/Drivers/Tick/Tick.c>
)

target_include_directories(freertos_kernel
    PUBLIC
        include
        ${FREERTOS_CONFIG_FILE_DIRECTORY}
        $<$<BOOL:${FREERTOS_PORT_BCC_16BIT_DOS_FLSH186}>:${CMAKE_CURRENT_LIST_DIR}/portable/BCC/16BitDOS/common;${CMAKE_CURRENT_LIST_DIR}/portable/BCC/16BitDOS/Flsh186>
        $<$<BOOL:${FREERTOS_PORT_BCC_16BIT_DOS_PC}>:${CMAKE_CURRENT_LIST_DIR}/portable/BCC/16BitDOS/common;${CMAKE_CURRENT_LIST_DIR}/portable/BCC/16BitDOS/PC>
        $<$<BOOL:${FREERTOS_PORT_CCS_ARM_CM3}>:${CMAKE_CURRENT_LIST_DIR}/portable/CCS/ARM_CM3>
        $<$<BOOL:${FREERTOS_PORT_CCS_ARM_CM4F}>:${CMAKE_CURRENT_LIST_DIR}/portable/CCS/ARM_CM4F>
        $<$<BOOL:${FREERTOS_PORT_CCS_ARM_CR4}>:${CMAKE_CURRENT_LIST_DIR}/portable/CCS/ARM_Cortex-R4>
        $<$<BOOL:${FREERTOS_PORT_CCS_MSP430X}>:${CMAKE_CURRENT_LIST_DIR}/portable/CCS/MSP430X>
        $<$<BOOL:${FREERTOS_PORT_CODEWARRIOR_COLDFIRE_V1}>:${CMAKE_CURRENT_LIST_DIR}/portable/CodeWarrior/ColdFire_V1>
        $<$<BOOL:${FREERTOS_PORT_CODEWARRIOR_COLDFIRE_V2}>:${CMAKE_CURRENT_LIST_DIR}/portable/CodeWarrior/ColdFire_V2>
        $<$<BOOL:${FREERTOS_PORT_CODEWARRIOR_HCS12}>:${CMAKE_CURRENT_LIST_DIR}/portable/CodeWarrior/HCS12>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CA9}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CA9>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CA53_64_BIT}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CA53_64_BIT>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CA53_64_BIT_SRE}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CA53_64_BIT_SRE>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM0}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM0>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM3}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM3>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM3_MPU}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM3_MPU>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM4_MPU}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM4_MPU>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM4F}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM4F>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM7}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM7/r0p1>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM23_NONSECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM23/non_secure>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM23_SECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM23/secure>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM23_NTZ_NONSECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM23_NTZ/non_secure>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM33_NONSECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM33/non_secure>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM33_SECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM33/secure>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CM33_NTZ_NONSECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM33_NTZ/non_secure>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CR5}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CR5>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM_CRX_NOGIC}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CRx_No_GIC>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM7_AT91FR40008}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM7_AT91FR40008>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM7_AT91SAM7S}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM7_AT91SAM7S>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM7_LPC2000}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM7_LPC2000>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARM7_LPC23XX}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM7_LPC23xx>
        $<$<BOOL:${FREERTOS_PORT_GCC_ATMEGA323}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ATMega323>
        $<$<BOOL:${FREERTOS_PORT_GCC_AVR32_UC3}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/AVR32_UC3>
        $<$<BOOL:${FREERTOS_PORT_GCC_COLDFIRE_V2}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ColdFire_V2>
        $<$<BOOL:${FREERTOS_PORT_GCC_CORTUS_APS3}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/CORTUS_APS3>
        $<$<BOOL:${FREERTOS_PORT_GCC_H8S2329}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/H8S2329>
        $<$<BOOL:${FREERTOS_PORT_GCC_HCS12}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/HCS12>
        $<$<BOOL:${FREERTOS_PORT_GCC_IA32_FLAT}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/IA32_flat>
        $<$<BOOL:${FREERTOS_PORT_GCC_MICROBLAZE}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/MicroBlaze>
        $<$<BOOL:${FREERTOS_PORT_GCC_MICROBLAZE_V8}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/MicroBlazeV8>
        $<$<BOOL:${FREERTOS_PORT_GCC_MICROBLAZE_V9}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/MicroBlazeV9>
        $<$<BOOL:${FREERTOS_PORT_GCC_MSP430F449}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/MSP430F449>
        $<$<BOOL:${FREERTOS_PORT_GCC_NIOSII}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/NiosII>
        $<$<BOOL:${FREERTOS_PORT_GCC_PPC405_XILINX}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/PPC405_Xilinx>
        $<$<BOOL:${FREERTOS_PORT_GCC_PPC440_XILINX}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/PPC440_Xilinx>
        $<$<BOOL:${FREERTOS_PORT_GCC_RISC_V}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RISC-V;${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RISC-V/chip_specific_extensions/RISCV_MTIME_CLINT_no_extensions>
        $<$<BOOL:${FREERTOS_PORT_GCC_RISC_V_PULPINO_VEGA_RV32M1RM}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RISC-V;${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RISC-V/chip_specific_extensions/Pulpino_Vega_RV32M1RM>
        $<$<BOOL:${FREERTOS_PORT_GCC_RL78}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RL78>
        $<$<BOOL:${FREERTOS_PORT_GCC_RX100}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX100>
        $<$<BOOL:${FREERTOS_PORT_GCC_RX200}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX200>
        $<$<BOOL:${FREERTOS_PORT_GCC_RX600}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX600>
        $<$<BOOL:${FREERTOS_PORT_GCC_RX600_V2}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX600v2>
        $<$<BOOL:${FREERTOS_PORT_GCC_RX700_V3_DPFPU}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX700v3_DPFPU>
        $<$<BOOL:${FREERTOS_PORT_GCC_STR75X}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/STR75x>
        $<$<BOOL:${FREERTOS_PORT_GCC_TRICORE_1782}>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/TriCore_1782>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARC_EM_HS}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/ARC_EM_HS>
        $<$<BOOL:${FREERTOS_PORT_GCC_ARC_V1}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/ARC_v1>
        $<$<BOOL:${FREERTOS_PORT_GCC_ATMEGA}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/ATmega>
        $<$<BOOL:${FREERTOS_PORT_GCC_POSIX}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/Posix;${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/Posix/utils>
        $<$<BOOL:${FREERTOS_PORT_GCC_RP2040}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/RP2040/include>
        $<$<BOOL:${FREERTOS_PORT_GCC_XTENSA_ESP32}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/Xtensa_ESP32;${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/Xtensa_ESP32/include>
        $<$<BOOL:${FREERTOS_PORT_GCC_AVRDX}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/Partner-Supported-Ports/GCC/AVR_AVRDx>
        $<$<BOOL:${FREERTOS_PORT_GCC_AVR_MEGA0}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/Partner-Supported-Ports/GCC/AVR_Mega0>
        $<$<BOOL:${FREERTOS_PORT_IAR_78K0K}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/78K0R>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CA5_NOGIC}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CA5_No_GIC>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CA9}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CA9>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM0}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM0>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM3}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM3>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM4F}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM4F>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM4F_MPU}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM4F_MPU>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM7}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM7/r0p1>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM23_NONSECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM23/non_secure>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM23_SECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM23/secure>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM23_NTZ_NONSECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM23_NTZ/non_secure>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM33_NONSECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM33/non_secure>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM33_SECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM33/secure>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CM33_NTZ_NONSECURE}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM33_NTZ/non_secure>
        $<$<BOOL:${FREERTOS_PORT_IAR_ARM_CRX_NOGIC}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CRx_No_GIC>
        $<$<BOOL:${FREERTOS_PORT_IAR_ATMEGA323}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ATMega323>
        $<$<BOOL:${FREERTOS_PORT_IAR_ATMEL_SAM7S64}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AtmelSAM7S64>
        $<$<BOOL:${FREERTOS_PORT_IAR_ATMEL_SAM9XE}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AtmelSAM9XE>
        $<$<BOOL:${FREERTOS_PORT_IAR_AVR_AVRDX}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AVR_AVRDx>
        $<$<BOOL:${FREERTOS_PORT_IAR_AVR_MEGA0}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AVR_Mega0>
        $<$<BOOL:${FREERTOS_PORT_IAR_AVR32_UC3}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AVR32_UC3>
        $<$<BOOL:${FREERTOS_PORT_IAR_LPC2000}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/LPC2000>
        $<$<BOOL:${FREERTOS_PORT_IAR_MSP430}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/MSP430>
        $<$<BOOL:${FREERTOS_PORT_IAR_MSP430X}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/MSP430X>
        $<$<BOOL:${FREERTOS_PORT_IAR_RISC_V}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RISC-V;${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RISC-V/chip_specific_extensions/RV32I_CLINT_no_extensions>
        $<$<BOOL:${FREERTOS_PORT_IAR_RL78}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RL78>
        $<$<BOOL:${FREERTOS_PORT_IAR_RX100}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RX100>
        $<$<BOOL:${FREERTOS_PORT_IAR_RX600}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RX600>
        $<$<BOOL:${FREERTOS_PORT_IAR_RX700_V3_DPFPU}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RX700v3_DPFPU>
        $<$<BOOL:${FREERTOS_PORT_IAR_RX_V2}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RXv2>
        $<$<BOOL:${FREERTOS_PORT_IAR_STR71X}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/STR71x>
        $<$<BOOL:${FREERTOS_PORT_IAR_STR75X}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/STR75x>
        $<$<BOOL:${FREERTOS_PORT_IAR_STR91X}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/STR91x>
        $<$<BOOL:${FREERTOS_PORT_IAR_V850ES_FX3}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/V850ES>
        $<$<BOOL:${FREERTOS_PORT_IAR_V850ES_HX3}>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/V850ES>
        $<$<BOOL:${FREERTOS_PORT_MIKROC_ARM_CM4F}>:${CMAKE_CURRENT_LIST_DIR}/portable/MikroC/ARM_CM4F>
        $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC18F}>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC18F>
        $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC24}>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC24_dsPIC>
        $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC32MEC14XX}>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC32MEC14xx>
        $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC32MX}>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC32MX>
        $<$<BOOL:${FREERTOS_PORT_MPLAB_PIC32MZ}>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC32MZ>
        $<$<BOOL:${FREERTOS_PORT_MSVC_MINGW}>:${CMAKE_CURRENT_LIST_DIR}/portable/MSVC-MingW>
        $<$<BOOL:${FREERTOS_PORT_OWATCOM_16BIT_DOS_FLSH186}>:${CMAKE_CURRENT_LIST_DIR}/portable/oWatcom/16BitDOS/common;${CMAKE_CURRENT_LIST_DIR}/portable/oWatcom/16BitDOS/Flsh186>
        $<$<BOOL:${FREERTOS_PORT_OWATCOM_16BIT_DOS_PC}>:${CMAKE_CURRENT_LIST_DIR}/portable/oWatcom/16BitDOS/common;${CMAKE_CURRENT_LIST_DIR}/portable/oWatcom/16BitDOS/PC>
        $<$<BOOL:${FREERTOS_PORT_PARADIGM_TERN_EE_LARGE}>:${CMAKE_CURRENT_LIST_DIR}/portable/Paradigm/Tern_EE/large_untested>
        $<$<BOOL:${FREERTOS_PORT_PARADIGM_TERN_EE_SMALL}>:${CMAKE_CURRENT_LIST_DIR}/portable/Paradigm/Tern_EE/small>
        $<$<BOOL:${FREERTOS_PORT_RENESAS_RX100}>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX100>
        $<$<BOOL:${FREERTOS_PORT_RENESAS_RX200}>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX200>
        $<$<BOOL:${FREERTOS_PORT_RENESAS_RX600}>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX600>
        $<$<BOOL:${FREERTOS_PORT_RENESAS_RX600_V2}>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX600v2>
        $<$<BOOL:${FREERTOS_PORT_RENESAS_RX700_V3_DPFPU}>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX700v3_DPFPU>
        $<$<BOOL:${FREERTOS_PORT_RENESAS_SH2A_FPU}>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/SH2A_FPU>
        $<$<BOOL:${FREERTOS_PORT_ROWLEY_MSP430F449}>:${CMAKE_CURRENT_LIST_DIR}/portable/Rowley/MSP430F449>
        $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CA9}>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CA9>
        $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM0}>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM0>
        $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM3}>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM3>
        $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM4_MPU}>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM4_MPU>
        $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM4F}>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM4F>
        $<$<BOOL:${FREERTOS_PORT_RVDS_ARM_CM7}>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM7/r0p1>
        $<$<BOOL:${FREERTOS_PORT_RVDS_ARM7_LPC21XX}>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM7_LPC21xx>
        $<$<BOOL:${FREERTOS_PORT_SDCC_CYGNAL}>:${CMAKE_CURRENT_LIST_DIR}/portable/SDCC/Cygnal>
        $<$<BOOL:${FREERTOS_PORT_SOFTUNE_MB91460}>:${CMAKE_CURRENT_LIST_DIR}/portable/Softune/MB91460>
        $<$<BOOL:${FREERTOS_PORT_SOFTUNE_MB96340}>:${CMAKE_CURRENT_LIST_DIR}/portable/Softune/MB96340>
        $<$<BOOL:${FREERTOS_PORT_TASKING_ARM_CM4F}>:${CMAKE_CURRENT_LIST_DIR}/portable/Tasking/ARM_CM4F>
        $<$<BOOL:${FREERTOS_PORT_CDK_THEAD_CK802}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/CDK/T-HEAD_CK802>
        $<$<BOOL:${FREERTOS_PORT_XCC_XTENSA}>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/XCC/Xtensa>
        $<$<BOOL:${FREERTOS_PORT_WIZC_PIC18}>:${CMAKE_CURRENT_LIST_DIR}/portable/WizC/PIC18>
)

target_link_libraries(freertos_kernel
    PUBLIC
        $<$<BOOL:${FREERTOS_PORT_GCC_RP2040}>:pico_base_headers>
        $<$<BOOL:${FREERTOS_PORT_GCC_XTENSA_ESP32}>:idf::esp32>
    PRIVATE
        "$<$<BOOL:${FREERTOS_PORT_GCC_RP2040}>:hardware_clocks;hardware_exception>"
        $<$<BOOL:${FREERTOS_PORT_MSVC_MINGW}>:winmm> # Windows library which implements timers
)
