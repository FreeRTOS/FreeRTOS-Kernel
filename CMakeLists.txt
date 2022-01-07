cmake_minimum_required(VERSION 3.15)

# User is responsible to set two mandatory options:
# FREERTOS_CONFIG_FILE_DIRECTORY
# FREERTOS_PORT

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

# FreeRTOS port option
set(FREERTOS_PORT "" CACHE STRING "FreeRTOS port name")
if(NOT FREERTOS_PORT)
    message(FATAL_ERROR " FREERTOS_PORT is not set. Please specify it from top-level CMake file (example):\n"
        "  set(FREERTOS_PORT GCC_ARM_CM4F CACHE STRING \"\")\n"
        " or from CMake command line option:\n"
        "  -DFREERTOS_PORT=GCC_ARM_CM4F")
endif()

# Available port options:
#
# BCC_16BIT_DOS_FLSH186            - Compiller: BCC           Target: 16 bit DOS Flsh186
# BCC_16BIT_DOS_PC                 - Compiller: BCC           Target: 16 bit DOS PC
# CCS_ARM_CM3                      - Compiller: CCS           Target: ARM Cortex-M3
# CCS_ARM_CM4F                     - Compiller: CCS           Target: ARM Cortex-M4 with FPU
# CCS_ARM_CR4                      - Compiller: CCS           Target: ARM Cortex-R4
# CCS_MSP430X                      - Compiller: CCS           Target: MSP430X
# CODEWARRIOR_COLDFIRE_V1          - Compiller: CoreWarrior   Target: ColdFire V1
# CODEWARRIOR_COLDFIRE_V2          - Compiller: CoreWarrior   Target: ColdFire V2
# CODEWARRIOR_HCS12                - Compiller: CoreWarrior   Target: HCS12
# GCC_ARM_CA9                      - Compiller: GCC           Target: ARM Cortex-A9
# GCC_ARM_CA53_64_BIT              - Compiller: GCC           Target: ARM Cortex-A53 64 bit
# GCC_ARM_CA53_64_BIT_SRE          - Compiller: GCC           Target: ARM Cortex-A53 64 bit SRE
# GCC_ARM_CM0                      - Compiller: GCC           Target: ARM Cortex-M0
# GCC_ARM_CM3                      - Compiller: GCC           Target: ARM Cortex-M3
# GCC_ARM_CM3_MPU                  - Compiller: GCC           Target: ARM Cortex-M3 with MPU
# GCC_ARM_CM4_MPU                  - Compiller: GCC           Target: ARM Cortex-M4 with MPU
# GCC_ARM_CM4F                     - Compiller: GCC           Target: ARM Cortex-M4 with FPU
# GCC_ARM_CM7                      - Compiller: GCC           Target: ARM Cortex-M7
# GCC_ARM_CM23_NONSECURE           - Compiller: GCC           Target: ARM Cortex-M23 non-secure
# GCC_ARM_CM23_SECURE              - Compiller: GCC           Target: ARM Cortex-M23 secure
# GCC_ARM_CM23_NTZ_NONSECURE       - Compiller: GCC           Target: ARM Cortex-M23 non-trustzone non-secure
# GCC_ARM_CM33_NONSECURE           - Compiller: GCC           Target: ARM Cortex-M33 non-secure
# GCC_ARM_CM33_SECURE              - Compiller: GCC           Target: ARM Cortex-M33 secure
# GCC_ARM_CM33_NTZ_NONSECURE       - Compiller: GCC           Target: ARM Cortex-M33 non-trustzone non-secure
# GCC_ARM_CR5                      - Compiller: GCC           Target: ARM Cortex-R5
# GCC_ARM_CRX_NOGIC                - Compiller: GCC           Target: ARM Cortex-Rx no GIC
# GCC_ARM7_AT91FR40008             - Compiller: GCC           Target: ARM7 Atmel AT91R40008
# GCC_ARM7_AT91SAM7S               - Compiller: GCC           Target: ARM7 Atmel AT91SAM7S
# GCC_ARM7_LPC2000                 - Compiller: GCC           Target: ARM7 LPC2000
# GCC_ARM7_LPC23XX                 - Compiller: GCC           Target: ARM7 LPC23xx
# GCC_ATMEGA323                    - Compiller: GCC           Target: ATMega323
# GCC_AVR32_UC3                    - Compiller: GCC           Target: AVR32 UC3
# GCC_COLDFIRE_V2                  - Compiller: GCC           Target: ColdFire V2
# GCC_CORTUS_APS3                  - Compiller: GCC           Target: CORTUS APS3
# GCC_H8S2329                      - Compiller: GCC           Target: H8S2329
# GCC_HCS12                        - Compiller: GCC           Target: HCS12
# GCC_IA32_FLAT                    - Compiller: GCC           Target: IA32 flat
# GCC_MICROBLAZE                   - Compiller: GCC           Target: MicroBlaze
# GCC_MICROBLAZE_V8                - Compiller: GCC           Target: MicroBlaze V8
# GCC_MICROBLAZE_V9                - Compiller: GCC           Target: MicroBlaze V9
# GCC_MSP430F449                   - Compiller: GCC           Target: MSP430F449
# GCC_NIOSII                       - Compiller: GCC           Target: NiosII
# GCC_PPC405_XILINX                - Compiller: GCC           Target: Xilinx PPC405
# GCC_PPC440_XILINX                - Compiller: GCC           Target: Xilinx PPC440
# GCC_RISC_V                       - Compiller: GCC           Target: RISC-V
# GCC_RISC_V_PULPINO_VEGA_RV32M1RM - Compiller: GCC           Target: RISC-V Pulpino Vega RV32M1RM
# GCC_RL78                         - Compiller: GCC           Target: Renesas RL78
# GCC_RX100                        - Compiller: GCC           Target: Renesas RX100
# GCC_RX200                        - Compiller: GCC           Target: Renesas RX200
# GCC_RX600                        - Compiller: GCC           Target: Renesas RX600
# GCC_RX600_V2                     - Compiller: GCC           Target: Renesas RX600 v2
# GCC_RX700_V3_DPFPU               - Compiller: GCC           Target: Renesas RX700 v3 with DPFPU
# GCC_STR75X                       - Compiller: GCC           Target: STR75x
# GCC_TRICORE_1782                 - Compiller: GCC           Target: TriCore 1782
# GCC_ARC_EM_HS                    - Compiller: GCC           Target: DesignWare ARC EM HS
# GCC_ARC_V1                       - Compiller: GCC           Target: DesignWare ARC v1
# GCC_ARM_CM33_TFM                 - Compiller: GCC           Target: ARM Cortex-M33 trusted firmware
# GCC_ATMEGA                       - Compiller: GCC           Target: ATmega
# GCC_POSIX                        - Compiller: GCC           Target: Posix
# GCC_RP2040                       - Compiller: GCC           Target: RP2040 ARM Cortex-M0+
# GCC_XTENSA_ESP32                 - Compiller: GCC           Target: Xtensa ESP32
# GCC_AVRDX                        - Compiller: GCC           Target: AVRDx
# GCC_AVR_MEGA0                    - Compiller: GCC           Target: AVR Mega0
# IAR_78K0K                        - Compiller: IAR           Target: Renesas 78K0K
# IAR_ARM_CA5_NOGIC                - Compiller: IAR           Target: ARM Cortex-A5 no GIC
# IAR_ARM_CA9                      - Compiller: IAR           Target: ARM Cortex-A9
# IAR_ARM_CM0                      - Compiller: IAR           Target: ARM Cortex-M0
# IAR_ARM_CM3                      - Compiller: IAR           Target: ARM Cortex-M3
# IAR_ARM_CM4F                     - Compiller: IAR           Target: ARM Cortex-M4 with FPU
# IAR_ARM_CM4F_MPU                 - Compiller: IAR           Target: ARM Cortex-M4 with FPU and MPU
# IAR_ARM_CM7                      - Compiller: IAR           Target: ARM Cortex-M7
# IAR_ARM_CM23_NONSECURE           - Compiller: IAR           Target: ARM Cortex-M23 non-secure
# IAR_ARM_CM23_SECURE              - Compiller: IAR           Target: ARM Cortex-M23 secure
# IAR_ARM_CM23_NTZ_NONSECURE       - Compiller: IAR           Target: ARM Cortex-M23 non-trustzone non-secure
# IAR_ARM_CM33_NONSECURE           - Compiller: IAR           Target: ARM Cortex-M33 non-secure
# IAR_ARM_CM33_SECURE              - Compiller: IAR           Target: ARM Cortex-M33 secure
# IAR_ARM_CM33_NTZ_NONSECURE       - Compiller: IAR           Target: ARM Cortex-M33 non-trustzone non-secure
# IAR_ARM_CRX_NOGIC                - Compiller: IAR           Target: ARM Cortex-Rx no GIC
# IAR_ATMEGA323                    - Compiller: IAR           Target: ATMega323
# IAR_ATMEL_SAM7S64                - Compiller: IAR           Target: Atmel SAM7S64
# IAR_ATMEL_SAM9XE                 - Compiller: IAR           Target: Atmel SAM9XE
# IAR_AVR_AVRDX                    - Compiller: IAR           Target: AVRDx
# IAR_AVR_MEGA0                    - Compiller: IAR           Target: AVR Mega0
# IAR_AVR32_UC3                    - Compiller: IAR           Target: AVR32 UC3
# IAR_LPC2000                      - Compiller: IAR           Target: LPC2000
# IAR_MSP430                       - Compiller: IAR           Target: MSP430
# IAR_MSP430X                      - Compiller: IAR           Target: MSP430X
# IAR_RISC_V                       - Compiller: IAR           Target: RISC-V
# IAR_RL78                         - Compiller: IAR           Target: Renesas RL78
# IAR_RX100                        - Compiller: IAR           Target: Renesas RX100
# IAR_RX600                        - Compiller: IAR           Target: Renesas RX600
# IAR_RX700_V3_DPFPU               - Compiller: IAR           Target: Renesas RX700 v3 with DPFPU
# IAR_RX_V2                        - Compiller: IAR           Target: Renesas RX v2
# IAR_STR71X                       - Compiller: IAR           Target: STR71x
# IAR_STR75X                       - Compiller: IAR           Target: STR75x
# IAR_STR91X                       - Compiller: IAR           Target: STR91x
# IAR_V850ES_FX3                   - Compiller: IAR           Target: Renesas V850ES/Fx3
# IAR_V850ES_HX3                   - Compiller: IAR           Target: Renesas V850ES/Hx3
# MIKROC_ARM_CM4F                  - Compiller: MikroC        Target: ARM Cortex-M4 with FPU
# MPLAB_PIC18F                     - Compiller: MPLAB         Target: PIC18F
# MPLAB_PIC24                      - Compiller: MPLAB         Target: PIC24
# MPLAB_PIC32MEC14XX               - Compiller: MPLAB         Target: PIC32MEC14xx
# MPLAB_PIC32MX                    - Compiller: MPLAB         Target: PIC32MX
# MPLAB_PIC32MZ                    - Compiller: MPLAB         Target: PIC32MZ
# MSVC_MINGW                       - Compiller: MSVC or MinGW Target: x86
# OWATCOM_16BIT_DOS_FLSH186        - Compiller: Open Watcom   Target: 16 bit DOS Flsh186
# OWATCOM_16BIT_DOS_PC             - Compiller: Open Watcom   Target: 16 bit DOS PC
# PARADIGM_TERN_EE_LARGE           - Compiller: Paradigm      Target: Tern EE large
# PARADIGM_TERN_EE_SMALL           - Compiller: Paradigm      Target: Tern EE small
# RENESAS_RX100                    - Compiller: Renesas       Target: RX100
# RENESAS_RX200                    - Compiller: Renesas       Target: RX200
# RENESAS_RX600                    - Compiller: Renesas       Target: RX600
# RENESAS_RX600_V2                 - Compiller: Renesas       Target: RX600 v2
# RENESAS_RX700_V3_DPFPU           - Compiller: Renesas       Target: RX700 v3 with DPFPU
# RENESAS_SH2A_FPU                 - Compiller: Renesas       Target: SH2A with FPU
# ROWLEY_MSP430F449                - Compiller: Rowley        Target: MSP430F449
# RVDS_ARM_CA9                     - Compiller: RVDS          Target: ARM Cortex-A9
# RVDS_ARM_CM0                     - Compiller: RVDS          Target: ARM Cortex-M0
# RVDS_ARM_CM3                     - Compiller: RVDS          Target: ARM Cortex-M3
# RVDS_ARM_CM4_MPU                 - Compiller: RVDS          Target: ARM Cortex-M4 with MPU
# RVDS_ARM_CM4F                    - Compiller: RVDS          Target: ARM Cortex-M4 with FPU
# RVDS_ARM_CM7                     - Compiller: RVDS          Target: ARM Cortex-M7
# RVDS_ARM7_LPC21XX                - Compiller: RVDS          Target: ARM7 LPC21xx
# SDCC_CYGNAL                      - Compiller: SDCC          Target: Cygnal
# SOFTUNE_MB91460                  - Compiller: Softune       Target: MB91460
# SOFTUNE_MB96340                  - Compiller: Softune       Target: MB96340
# TASKING_ARM_CM4F                 - Compiller: Tasking       Target: ARM Cortex-M4 with FPU
# CDK_THEAD_CK802                  - Compiller: CDK           Target: T-head CK802
# XCC_XTENSA                       - Compiller: XCC           Target: Xtensa
# WIZC_PIC18                       - Compiller: WizC          Target: PIC18

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

    $<$<STREQUAL:${FREERTOS_PORT},BCC_16BIT_DOS_FLSH186>:portable/BCC/16BitDOS/common/portcomn.c;portable/BCC/16BitDOS/Flsh186/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},BCC_16BIT_DOS_PC>:portable/BCC/16BitDOS/common/portcomn.c;portable/BCC/16BitDOS/PC/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},CCS_ARM_CM3>:portable/CCS/ARM_CM3/port.c;portable/CCS/ARM_CM3/portasm.asm>
    $<$<STREQUAL:${FREERTOS_PORT},CCS_ARM_CM4F>:portable/CCS/ARM_CM4F/port.c;portable/CCS/ARM_CM4F/portasm.asm>
    $<$<STREQUAL:${FREERTOS_PORT},CCS_ARM_CR4>:portable/CCS/ARM_Cortex-R4/port.c;portable/CCS/ARM_Cortex-R4/portASM.asm>
    $<$<STREQUAL:${FREERTOS_PORT},CCS_MSP430X>:portable/CCS/MSP430X/port.c;portable/CCS/MSP430X/portext.asm>
    $<$<STREQUAL:${FREERTOS_PORT},CODEWARRIOR_COLDFIRE_V1>:portable/CodeWarrior/ColdFire_V1/port.c;portable/CodeWarrior/ColdFire_V1/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},CODEWARRIOR_COLDFIRE_V2>:portable/CodeWarrior/ColdFire_V2/port.c;portable/CodeWarrior/ColdFire_V2/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},CODEWARRIOR_HCS12>:portable/CodeWarrior/HCS12/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CA9>:portable/GCC/ARM_CA9/port.c;portable/GCC/ARM_CA9/portASM.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CA53_64_BIT>:portable/GCC/ARM_CA53_64_BIT/port.c;portable/GCC/ARM_CA53_64_BIT/portASM.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CA53_64_BIT_SRE>:portable/GCC/ARM_CA53_64_BIT_SRE/port.c;portable/GCC/ARM_CA53_64_BIT_SRE/portASM.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM0>:portable/GCC/ARM_CM0/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM3>:portable/GCC/ARM_CM3/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM3_MPU>:portable/GCC/ARM_CM3_MPU/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM4_MPU>:portable/GCC/ARM_CM4_MPU/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM4F>:portable/GCC/ARM_CM4F/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM7>:portable/GCC/ARM_CM7/r0p1/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM23_NONSECURE>:portable/GCC/ARM_CM23/non_secure/port.c;portable/GCC/ARM_CM23/non_secure/portasm.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM23_SECURE>:portable/GCC/ARM_CM23/secure/secure_context_port.c;portable/GCC/ARM_CM23/secure/secure_context.c;portable/GCC/ARM_CM23/secure/secure_heap.c;portable/GCC/ARM_CM23/secure/secure_init.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM23_NTZ_NONSECURE>:portable/GCC/ARM_CM23_NTZ/non_secure/port.c;portable/GCC/ARM_CM23_NTZ/non_secure/portasm.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM33_NONSECURE>:portable/GCC/ARM_CM33/non_secure/port.c;portable/GCC/ARM_CM33/non_secure/portasm.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM33_SECURE>:portable/GCC/ARM_CM33/secure/secure_context_port.c;portable/GCC/ARM_CM33/secure/secure_context.c;portable/GCC/ARM_CM33/secure/secure_heap.c;portable/GCC/ARM_CM33/secure/secure_init.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM33_NTZ_NONSECURE>:portable/GCC/ARM_CM33_NTZ/non_secure/port.c;portable/GCC/ARM_CM33_NTZ/non_secure/portasm.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CR5>:portable/GCC/ARM_CR5/port.c;portable/GCC/ARM_CR5/portASM.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CRX_NOGIC>:portable/GCC/ARM_CRx_No_GIC/port.c;portable/GCC/ARM_CRx_No_GIC/portASM.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM7_AT91FR40008>:portable/GCC/ARM7_AT91FR40008/port.c;portable/GCC/ARM7_AT91FR40008/portISR.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM7_AT91SAM7S>:portable/GCC/ARM7_AT91SAM7S/lib_AT91SAM7X256.c;portable/GCC/ARM7_AT91SAM7S/port.c;portable/GCC/ARM7_AT91SAM7S/portISR.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM7_LPC2000>:portable/GCC/ARM7_LPC2000/port.c;portable/GCC/ARM7_LPC2000/portISR.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM7_LPC23XX>:portable/GCC/ARM7_LPC23xx/port.c;portable/GCC/ARM7_LPC23xx/portISR.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ATMEGA323>:portable/GCC/ATMega323/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_AVR32_UC3>:portable/GCC/AVR32_UC3/exception.S;portable/GCC/AVR32_UC3/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_COLDFIRE_V2>:portable/GCC/ColdFire_V2/port.c;portable/GCC/ColdFire_V2/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_CORTUS_APS3>:portable/GCC/CORTUS_APS3/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_H8S2329>:portable/GCC/H8S2329/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_HCS12>:portable/GCC/HCS12/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_IA32_FLAT>:portable/GCC/IA32_flat/port.c;portable/GCC/IA32_flat/portASM.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_MICROBLAZE>:portable/GCC/MicroBlaze/port.c;portable/GCC/MicroBlaze/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_MICROBLAZE_V8>:portable/GCC/MicroBlazeV8/port.c;portable/GCC/MicroBlazeV8/port_exceptions.c;portable/GCC/MicroBlazeV8/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_MICROBLAZE_V9>:portable/GCC/MicroBlazeV9/port.c;portable/GCC/MicroBlazeV9/port_exceptions.c;portable/GCC/MicroBlazeV9/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_MSP430F449>:portable/GCC/MSP430F449/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_NIOSII>:portable/GCC/NiosII/port.c;portable/GCC/NiosII/port_asm.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_PPC405_XILINX>:portable/GCC/PPC405_Xilinx/port.c;portable/GCC/PPC405_Xilinx/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_PPC440_XILINX>:portable/GCC/PPC440_Xilinx/port.c;portable/GCC/PPC440_Xilinx/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RISC_V>:portable/GCC/RISC-V/port.c;portable/GCC/RISC-V/portASM.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RISC_V_PULPINO_VEGA_RV32M1RM>:portable/GCC/RISC-V/port.c;portable/GCC/RISC-V/portASM.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RL78>:portable/GCC/RL78/port.c;portable/GCC/RL78/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RX100>:portable/GCC/RX100/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RX200>:portable/GCC/RX200/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RX600>:portable/GCC/RX600/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RX600_V2>:portable/GCC/RX600v2/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RX700_V3_DPFPU>:portable/GCC/RX700v3_DPFPU/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_STR75X>:portable/GCC/STR75x/port.c;portable/GCC/STR75x/portISR.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_TRICORE_1782>:portable/GCC/TriCore_1782/port.c;portable/GCC/TriCore_1782/porttrap.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARC_EM_HS>:portable/ThirdParty/GCC/ARC_EM_HS/arc_freertos_exceptions.c;portable/ThirdParty/GCC/ARC_EM_HS/arc_support.s;portable/ThirdParty/GCC/ARC_EM_HS/freertos_tls.c;portable/ThirdParty/GCC/ARC_EM_HS/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARC_V1>:portable/ThirdParty/GCC/ARC_v1/arc_freertos_exceptions.c;portable/ThirdParty/GCC/ARC_v1/arc_support.s;portable/ThirdParty/GCC/ARC_v1/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM33_TFM>:portable/ThirdParty/GCC/ARM_CM33_TFM/os_wrapper_freertos.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_ATMEGA>:portable/ThirdParty/GCC/ATmega/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_POSIX>:portable/ThirdParty/GCC/Posix/port.c;portable/ThirdParty/GCC/Posix/utils/wait_for_event.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_RP2040>:portable/ThirdParty/GCC/RP2040/idle_task_static_memory.c;portable/ThirdParty/GCC/RP2040/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_XTENSA_ESP32>:portable/ThirdParty/GCC/Xtensa_ESP32/FreeRTOS-openocd.c;portable/ThirdParty/GCC/Xtensa_ESP32/port.c;portable/ThirdParty/GCC/Xtensa_ESP32/portasm.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_context.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_init.c;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_intr_asm.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_intr.c;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_loadstore_handler.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_overlay_os_hook.c;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_vector_defaults.S;portable/ThirdParty/GCC/Xtensa_ESP32/xtensa_vectors.S>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_AVRDX>:portable/ThirdParty/Partner-Supported-Ports/GCC/AVR_AVRDx/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},GCC_AVR_MEGA0>:portable/ThirdParty/Partner-Supported-Ports/GCC/AVR_Mega0/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_78K0K>:portable/IAR/78K0R/port.c;portable/IAR/78K0R/portasm.s26>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CA5_NOGIC>:portable/IAR/ARM_CA5_No_GIC/port.c;portable/IAR/ARM_CA5_No_GIC/portASM.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CA9>:portable/IAR/ARM_CA9/port.c;portable/IAR/ARM_CA9/portASM.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM0>:portable/IAR/ARM_CM0/port.c;portable/IAR/ARM_CM0/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM3>:portable/IAR/ARM_CM3/port.c;portable/IAR/ARM_CM3/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM4F>:portable/IAR/ARM_CM4F/port.c;portable/IAR/ARM_CM4F/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM4F_MPU>:portable/IAR/ARM_CM4F_MPU/port.c;portable/IAR/ARM_CM4F_MPU/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM7>:portable/IAR/ARM_CM7/r0p1/port.c;portable/IAR/ARM_CM7/r0p1/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM23_NONSECURE>:portable/IAR/ARM_CM23/non_secure/port.c;portable/IAR/ARM_CM23/non_secure/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM23_SECURE>:portable/IAR/ARM_CM23/secure/secure_context_port_asm.s;portable/IAR/ARM_CM23/secure/secure_context.c;portable/IAR/ARM_CM23/secure/secure_heap.c;portable/IAR/ARM_CM23/secure/secure_init.c>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM23_NTZ_NONSECURE>:portable/IAR/ARM_CM23_NTZ/non_secure/port.c;portable/IAR/ARM_CM23_NTZ/non_secure/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM33_NONSECURE>:portable/IAR/ARM_CM33/non_secure/port.c;portable/IAR/ARM_CM33/non_secure/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM33_SECURE>:portable/IAR/ARM_CM33/secure/secure_context_port_asm.s;portable/IAR/ARM_CM33/secure/secure_context.c;portable/IAR/ARM_CM33/secure/secure_heap.c;portable/IAR/ARM_CM33/secure/secure_init.c>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM33_NTZ_NONSECURE>:portable/IAR/ARM_CM33_NTZ/non_secure/port.c;portable/IAR/ARM_CM33_NTZ/non_secure/portasm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CRX_NOGIC>:portable/IAR/ARM_CRx_No_GIC/port.c;portable/IAR/ARM_CRx_No_GIC/portASM.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ATMEGA323>:portable/IAR/ATMega323/port.c;portable/IAR/ATMega323/portmacro.s90>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ATMEL_SAM7S64>:portable/IAR/AtmelSAM7S64/port.c;portable/IAR/AtmelSAM7S64/portasm.s79>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_ATMEL_SAM9XE>:portable/IAR/AtmelSAM9XE/port.c;portable/IAR/AtmelSAM9XE/portasm.s79>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_AVR_AVRDX>:portable/IAR/AVR_AVRDx/port.c;portable/IAR/AVR_AVRDx/portmacro.s90>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_AVR_MEGA0>:portable/IAR/AVR_Mega0/port.c;portable/IAR/AVR_Mega0/portmacro.s90>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_AVR32_UC3>:portable/IAR/AVR32_UC3/exception.s82;portable/IAR/AVR32_UC3/port.c;portable/IAR/AVR32_UC3/read.c;portable/IAR/AVR32_UC3/write.c>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_LPC2000>:portable/IAR/LPC2000/port.c;portable/IAR/LPC2000/portasm.s79>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_MSP430>:portable/IAR/MSP430/port.c;portable/IAR/MSP430/portext.s43>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_MSP430X>:portable/IAR/MSP430X/port.c;portable/IAR/MSP430X/portext.s43>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_RISC_V>:portable/IAR/RISC-V/port.c;portable/IAR/RISC-V/portASM.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_RL78>:portable/IAR/RL78/port.c;portable/IAR/RL78/portasm.s87>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_RX100>:portable/IAR/RX100/port.c;portable/IAR/RX100/port_asm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_RX600>:portable/IAR/RX600/port.c;portable/IAR/RX600/port_asm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_RX700_V3_DPFPU>:portable/IAR/RX700v3_DPFPU/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_RX_V2>:portable/IAR/RXv2/port.c;portable/IAR/RXv2/port_asm.s>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_STR71X>:portable/IAR/STR71x/port.c;portable/IAR/STR71x/portasm.s79>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_STR75X>:portable/IAR/STR75x/port.c;portable/IAR/STR75x/portasm.s79>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_STR91X>:portable/IAR/STR91x/port.c;portable/IAR/STR91x/portasm.s79>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_V850ES_FX3>:portable/IAR/V850ES/port.c;portable/IAR/V850ES/portasm_Fx3.s85>
    $<$<STREQUAL:${FREERTOS_PORT},IAR_V850ES_HX3>:portable/IAR/V850ES/port.c;portable/IAR/V850ES/portasm_Hx2.s85>
    $<$<STREQUAL:${FREERTOS_PORT},MIKROC_ARM_CM4F>:portable/MikroC/ARM_CM4F/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC18F>:portable/MPLAB/PIC18F/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC24>:portable/MPLAB/PIC24_dsPIC/port.c;portable/MPLAB/PIC24_dsPIC/portasm_PIC24.S> # TODO: What to do with portasm_dsPIC.S ?
    $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC32MEC14XX>:portable/MPLAB/PIC32MEC14xx/port.c;portable/MPLAB/PIC32MEC14xx/port_asm.S>
    $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC32MX>:portable/MPLAB/PIC32MX/port.c;portable/MPLAB/PIC32MX/port_asm.S>
    $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC32MZ>:portable/MPLAB/PIC32MZ/port.c;portable/MPLAB/PIC32MZ/port_asm.S>
    $<$<STREQUAL:${FREERTOS_PORT},MSVC_MINGW>:portable/MSVC-MingW/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},OWATCOM_16BIT_DOS_FLSH186>:portable/oWatcom/16BitDOS/common/portcomn.c;portable/oWatcom/16BitDOS/Flsh186/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},OWATCOM_16BIT_DOS_PC>:portable/oWatcom/16BitDOS/common/portcomn.c;portable/oWatcom/16BitDOS/PC/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},PARADIGM_TERN_EE_LARGE>:portable/Paradigm/Tern_EE/large_untested/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},PARADIGM_TERN_EE_SMALL>:portable/Paradigm/Tern_EE/small/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX100>:portable/Renesas/RX100/port.c;portable/Renesas/RX100/port_asm.src>
    $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX200>:portable/Renesas/RX200/port.c;portable/Renesas/RX200/port_asm.src>
    $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX600>:portable/Renesas/RX600/port.c;portable/Renesas/RX600/port_asm.src>
    $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX600_V2>:portable/Renesas/RX600v2/port.c;portable/Renesas/RX600v2/port_asm.src>
    $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX700_V3_DPFPU>:portable/Renesas/RX700v3_DPFPU/port.c;portable/Renesas/RX700v3_DPFPU/port_asm.src>
    $<$<STREQUAL:${FREERTOS_PORT},RENESAS_SH2A_FPU>:portable/Renesas/SH2A_FPU/port.c;portable/Renesas/SH2A_FPU/portasm.src>
    $<$<STREQUAL:${FREERTOS_PORT},ROWLEY_MSP430F449>:portable/Rowley/MSP430F449/port.c;portable/Rowley/MSP430F449/portext.asm>
    $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CA9>:portable/RVDS/ARM_CA9/port.c;portable/RVDS/ARM_CA9/portASM.s>
    $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM0>:portable/RVDS/ARM_CM0/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM3>:portable/RVDS/ARM_CM3/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM4_MPU>:portable/RVDS/ARM_CM4_MPU/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM4F>:portable/RVDS/ARM_CM4F/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM7>:portable/RVDS/ARM_CM7/r0p1/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM7_LPC21XX>:portable/RVDS/ARM7_LPC21xx/port.c;portable/RVDS/ARM7_LPC21xx/portASM.s>
    $<$<STREQUAL:${FREERTOS_PORT},SDCC_CYGNAL>:portable/SDCC/Cygnal/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},SOFTUNE_MB91460>:portable/Softune/MB91460/__STD_LIB_sbrk.c;portable/Softune/MB91460/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},SOFTUNE_MB96340>:portable/Softune/MB96340/__STD_LIB_sbrk.c;portable/Softune/MB96340/port.c>
    $<$<STREQUAL:${FREERTOS_PORT},TASKING_ARM_CM4F>:portable/Tasking/ARM_CM4F/port.c;portable/Tasking/ARM_CM4F/port_asm.asm>
    $<$<STREQUAL:${FREERTOS_PORT},CDK_THEAD_CK802>:portable/ThirdParty/CDK/T-HEAD_CK802/port.c;portable/ThirdParty/CDK/T-HEAD_CK802/portasm.S>
    $<$<STREQUAL:${FREERTOS_PORT},XCC_XTENSA>:portable/ThirdParty/XCC/Xtensa/port.c;portable/ThirdParty/XCC/Xtensa/portasm.S;portable/ThirdParty/XCC/Xtensa/portclib.c;portable/ThirdParty/XCC/Xtensa/xtensa_context.S;portable/ThirdParty/XCC/Xtensa/xtensa_init.c;portable/ThirdParty/XCC/Xtensa/xtensa_intr_asm.S;portable/ThirdParty/XCC/Xtensa/xtensa_intr.c;portable/ThirdParty/XCC/Xtensa/xtensa_overlay_os_hook.c;portable/ThirdParty/XCC/Xtensa/xtensa_vectors.S>
    $<$<STREQUAL:${FREERTOS_PORT},WIZC_PIC18>:portable/WizC/PIC18/port.c;portable/WizC/PIC18/Drivers/Tick/isrTick.c;portable/WizC/PIC18/Drivers/Tick/Tick.c>
)

target_include_directories(freertos_kernel
    PUBLIC
        include
        ${FREERTOS_CONFIG_FILE_DIRECTORY}
        $<$<STREQUAL:${FREERTOS_PORT},BCC_16BIT_DOS_FLSH186>:${CMAKE_CURRENT_LIST_DIR}/portable/BCC/16BitDOS/common;${CMAKE_CURRENT_LIST_DIR}/portable/BCC/16BitDOS/Flsh186>
        $<$<STREQUAL:${FREERTOS_PORT},BCC_16BIT_DOS_PC>:${CMAKE_CURRENT_LIST_DIR}/portable/BCC/16BitDOS/common;${CMAKE_CURRENT_LIST_DIR}/portable/BCC/16BitDOS/PC>
        $<$<STREQUAL:${FREERTOS_PORT},CCS_ARM_CM3>:${CMAKE_CURRENT_LIST_DIR}/portable/CCS/ARM_CM3>
        $<$<STREQUAL:${FREERTOS_PORT},CCS_ARM_CM4F>:${CMAKE_CURRENT_LIST_DIR}/portable/CCS/ARM_CM4F>
        $<$<STREQUAL:${FREERTOS_PORT},CCS_ARM_CR4>:${CMAKE_CURRENT_LIST_DIR}/portable/CCS/ARM_Cortex-R4>
        $<$<STREQUAL:${FREERTOS_PORT},CCS_MSP430X>:${CMAKE_CURRENT_LIST_DIR}/portable/CCS/MSP430X>
        $<$<STREQUAL:${FREERTOS_PORT},CODEWARRIOR_COLDFIRE_V1>:${CMAKE_CURRENT_LIST_DIR}/portable/CodeWarrior/ColdFire_V1>
        $<$<STREQUAL:${FREERTOS_PORT},CODEWARRIOR_COLDFIRE_V2>:${CMAKE_CURRENT_LIST_DIR}/portable/CodeWarrior/ColdFire_V2>
        $<$<STREQUAL:${FREERTOS_PORT},CODEWARRIOR_HCS12>:${CMAKE_CURRENT_LIST_DIR}/portable/CodeWarrior/HCS12>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CA9>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CA9>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CA53_64_BIT>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CA53_64_BIT>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CA53_64_BIT_SRE>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CA53_64_BIT_SRE>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM0>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM0>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM3>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM3>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM3_MPU>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM3_MPU>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM4_MPU>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM4_MPU>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM4F>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM4F>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM7>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM7/r0p1>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM23_NONSECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM23/non_secure>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM23_SECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM23/secure>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM23_NTZ_NONSECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM23_NTZ/non_secure>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM33_NONSECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM33/non_secure>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM33_SECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM33/secure>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CM33_NTZ_NONSECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CM33_NTZ/non_secure>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CR5>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CR5>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM_CRX_NOGIC>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM_CRx_No_GIC>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM7_AT91FR40008>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM7_AT91FR40008>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM7_AT91SAM7S>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM7_AT91SAM7S>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM7_LPC2000>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM7_LPC2000>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARM7_LPC23XX>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ARM7_LPC23xx>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ATMEGA323>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ATMega323>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_AVR32_UC3>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/AVR32_UC3>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_COLDFIRE_V2>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/ColdFire_V2>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_CORTUS_APS3>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/CORTUS_APS3>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_H8S2329>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/H8S2329>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_HCS12>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/HCS12>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_IA32_FLAT>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/IA32_flat>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_MICROBLAZE>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/MicroBlaze>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_MICROBLAZE_V8>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/MicroBlazeV8>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_MICROBLAZE_V9>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/MicroBlazeV9>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_MSP430F449>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/MSP430F449>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_NIOSII>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/NiosII>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_PPC405_XILINX>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/PPC405_Xilinx>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_PPC440_XILINX>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/PPC440_Xilinx>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RISC_V>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RISC-V;${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RISC-V/chip_specific_extensions/RISCV_MTIME_CLINT_no_extensions>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RISC_V_PULPINO_VEGA_RV32M1RM>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RISC-V;${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RISC-V/chip_specific_extensions/Pulpino_Vega_RV32M1RM>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RL78>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RL78>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RX100>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX100>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RX200>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX200>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RX600>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX600>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RX600_V2>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX600v2>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RX700_V3_DPFPU>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/RX700v3_DPFPU>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_STR75X>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/STR75x>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_TRICORE_1782>:${CMAKE_CURRENT_LIST_DIR}/portable/GCC/TriCore_1782>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARC_EM_HS>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/ARC_EM_HS>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ARC_V1>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/ARC_v1>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_ATMEGA>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/ATmega>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_POSIX>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/Posix;${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/Posix/utils>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RP2040>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/RP2040/include>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_XTENSA_ESP32>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/Xtensa_ESP32;${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/GCC/Xtensa_ESP32/include>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_AVRDX>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/Partner-Supported-Ports/GCC/AVR_AVRDx>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_AVR_MEGA0>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/Partner-Supported-Ports/GCC/AVR_Mega0>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_78K0K>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/78K0R>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CA5_NOGIC>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CA5_No_GIC>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CA9>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CA9>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM0>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM0>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM3>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM3>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM4F>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM4F>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM4F_MPU>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM4F_MPU>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM7>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM7/r0p1>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM23_NONSECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM23/non_secure>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM23_SECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM23/secure>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM23_NTZ_NONSECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM23_NTZ/non_secure>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM33_NONSECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM33/non_secure>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM33_SECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM33/secure>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CM33_NTZ_NONSECURE>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CM33_NTZ/non_secure>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ARM_CRX_NOGIC>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ARM_CRx_No_GIC>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ATMEGA323>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/ATMega323>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ATMEL_SAM7S64>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AtmelSAM7S64>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_ATMEL_SAM9XE>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AtmelSAM9XE>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_AVR_AVRDX>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AVR_AVRDx>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_AVR_MEGA0>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AVR_Mega0>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_AVR32_UC3>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/AVR32_UC3>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_LPC2000>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/LPC2000>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_MSP430>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/MSP430>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_MSP430X>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/MSP430X>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_RISC_V>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RISC-V;${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RISC-V/chip_specific_extensions/RV32I_CLINT_no_extensions>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_RL78>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RL78>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_RX100>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RX100>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_RX600>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RX600>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_RX700_V3_DPFPU>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RX700v3_DPFPU>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_RX_V2>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/RXv2>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_STR71X>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/STR71x>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_STR75X>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/STR75x>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_STR91X>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/STR91x>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_V850ES_FX3>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/V850ES>
        $<$<STREQUAL:${FREERTOS_PORT},IAR_V850ES_HX3>:${CMAKE_CURRENT_LIST_DIR}/portable/IAR/V850ES>
        $<$<STREQUAL:${FREERTOS_PORT},MIKROC_ARM_CM4F>:${CMAKE_CURRENT_LIST_DIR}/portable/MikroC/ARM_CM4F>
        $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC18F>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC18F>
        $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC24>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC24_dsPIC>
        $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC32MEC14XX>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC32MEC14xx>
        $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC32MX>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC32MX>
        $<$<STREQUAL:${FREERTOS_PORT},MPLAB_PIC32MZ>:${CMAKE_CURRENT_LIST_DIR}/portable/MPLAB/PIC32MZ>
        $<$<STREQUAL:${FREERTOS_PORT},MSVC_MINGW>:${CMAKE_CURRENT_LIST_DIR}/portable/MSVC-MingW>
        $<$<STREQUAL:${FREERTOS_PORT},OWATCOM_16BIT_DOS_FLSH186>:${CMAKE_CURRENT_LIST_DIR}/portable/oWatcom/16BitDOS/common;${CMAKE_CURRENT_LIST_DIR}/portable/oWatcom/16BitDOS/Flsh186>
        $<$<STREQUAL:${FREERTOS_PORT},OWATCOM_16BIT_DOS_PC>:${CMAKE_CURRENT_LIST_DIR}/portable/oWatcom/16BitDOS/common;${CMAKE_CURRENT_LIST_DIR}/portable/oWatcom/16BitDOS/PC>
        $<$<STREQUAL:${FREERTOS_PORT},PARADIGM_TERN_EE_LARGE>:${CMAKE_CURRENT_LIST_DIR}/portable/Paradigm/Tern_EE/large_untested>
        $<$<STREQUAL:${FREERTOS_PORT},PARADIGM_TERN_EE_SMALL>:${CMAKE_CURRENT_LIST_DIR}/portable/Paradigm/Tern_EE/small>
        $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX100>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX100>
        $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX200>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX200>
        $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX600>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX600>
        $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX600_V2>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX600v2>
        $<$<STREQUAL:${FREERTOS_PORT},RENESAS_RX700_V3_DPFPU>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/RX700v3_DPFPU>
        $<$<STREQUAL:${FREERTOS_PORT},RENESAS_SH2A_FPU>:${CMAKE_CURRENT_LIST_DIR}/portable/Renesas/SH2A_FPU>
        $<$<STREQUAL:${FREERTOS_PORT},ROWLEY_MSP430F449>:${CMAKE_CURRENT_LIST_DIR}/portable/Rowley/MSP430F449>
        $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CA9>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CA9>
        $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM0>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM0>
        $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM3>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM3>
        $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM4_MPU>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM4_MPU>
        $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM4F>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM4F>
        $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM_CM7>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM_CM7/r0p1>
        $<$<STREQUAL:${FREERTOS_PORT},RVDS_ARM7_LPC21XX>:${CMAKE_CURRENT_LIST_DIR}/portable/RVDS/ARM7_LPC21xx>
        $<$<STREQUAL:${FREERTOS_PORT},SDCC_CYGNAL>:${CMAKE_CURRENT_LIST_DIR}/portable/SDCC/Cygnal>
        $<$<STREQUAL:${FREERTOS_PORT},SOFTUNE_MB91460>:${CMAKE_CURRENT_LIST_DIR}/portable/Softune/MB91460>
        $<$<STREQUAL:${FREERTOS_PORT},SOFTUNE_MB96340>:${CMAKE_CURRENT_LIST_DIR}/portable/Softune/MB96340>
        $<$<STREQUAL:${FREERTOS_PORT},TASKING_ARM_CM4F>:${CMAKE_CURRENT_LIST_DIR}/portable/Tasking/ARM_CM4F>
        $<$<STREQUAL:${FREERTOS_PORT},CDK_THEAD_CK802>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/CDK/T-HEAD_CK802>
        $<$<STREQUAL:${FREERTOS_PORT},XCC_XTENSA>:${CMAKE_CURRENT_LIST_DIR}/portable/ThirdParty/XCC/Xtensa>
        $<$<STREQUAL:${FREERTOS_PORT},WIZC_PIC18>:${CMAKE_CURRENT_LIST_DIR}/portable/WizC/PIC18>
)

target_link_libraries(freertos_kernel
    PUBLIC
        $<$<STREQUAL:${FREERTOS_PORT},GCC_RP2040>:pico_base_headers>
        $<$<STREQUAL:${FREERTOS_PORT},GCC_XTENSA_ESP32>:idf::esp32>
    PRIVATE
        "$<$<STREQUAL:${FREERTOS_PORT},GCC_RP2040>:hardware_clocks;hardware_exception>"
        $<$<STREQUAL:${FREERTOS_PORT},MSVC_MINGW>:winmm> # Windows library which implements timers
)
