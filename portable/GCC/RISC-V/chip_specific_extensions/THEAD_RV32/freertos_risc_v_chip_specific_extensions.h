/*
 * FreeRTOS Kernel V10.4.0
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
 * 1 tab == 4 spaces!
 */

/*
 * The FreeRTOS kernel's RISC-V port is split between the the code that is
 * common across all currently supported RISC-V chips (implementations of the
 * RISC-V ISA), and code that tailors the port to a specific RISC-V chip:
 *
 * + FreeRTOS\Source\portable\GCC\RISC-V-RV32\portASM.S contains the code that
 *   is common to all currently supported RISC-V chips.  There is only one
 *   portASM.S file because the same file is built for all RISC-V target chips.
 *
 * + Header files called freertos_risc_v_chip_specific_extensions.h contain the
 *   code that tailors the FreeRTOS kernel's RISC-V port to a specific RISC-V
 *   chip.  There are multiple freertos_risc_v_chip_specific_extensions.h files
 *   as there are multiple RISC-V chip implementations.
 *
 * !!!NOTE!!!
 * TAKE CARE TO INCLUDE THE CORRECT freertos_risc_v_chip_specific_extensions.h
 * HEADER FILE FOR THE CHIP IN USE.  This is done using the assembler's (not the
 * compiler's!) include path.  For example, if the chip in use includes a core
 * local interrupter (CLINT) and does not include any chip specific register
 * extensions then add the path below to the assembler's include path:
 * FreeRTOS\Source\portable\GCC\RISC-V-RV32\chip_specific_extensions\RV32I_CLINT_no_extensions
 *
 */


#ifndef __FREERTOS_RISC_V_EXTENSIONS_H__
#define __FREERTOS_RISC_V_EXTENSIONS_H__

#define portasmHANDLE_INTERRUPT Default_IRQHandler
#define portasmHAS_SIFIVE_CLINT 1
#define portasmHAS_MTIME 0
#define portasmADDITIONAL_CONTEXT_SIZE 0 /* Must be even number on 32-bit cores. */

.macro portasmSAVE_ADDITIONAL_REGISTERS
	/* save float registers */
#if __riscv_flen == 64
        addi    sp,  sp, -(128+128)

        fsd     f31, (0  + 0 )(sp)
        fsd     f30, (4  + 4 )(sp)
        fsd     f29, (8  + 8 )(sp)
        fsd     f28, (12 + 12)(sp)
        fsd     f27, (16 + 16)(sp)
        fsd     f26, (20 + 20)(sp)
        fsd     f25, (24 + 24)(sp)
        fsd     f24, (28 + 28)(sp)
        fsd     f23, (32 + 32)(sp)
        fsd     f22, (36 + 36)(sp)
        fsd     f21, (40 + 40)(sp)
        fsd     f20, (44 + 44)(sp)
        fsd     f19, (48 + 48)(sp)
        fsd     f18, (52 + 52)(sp)
        fsd     f17, (56 + 56)(sp)
        fsd     f16, (60 + 60)(sp)
        fsd     f15, (64 + 64)(sp)
        fsd     f14, (68 + 68)(sp)
        fsd     f13, (72 + 72)(sp)
        fsd     f12, (76 + 76)(sp)
        fsd     f11, (80 + 80)(sp)
        fsd     f10, (84 + 84)(sp)
        fsd     f9,  (88 + 88)(sp)
        fsd     f8,  (92 + 92)(sp)
        fsd     f7,  (96 + 96)(sp)
        fsd     f6,  (100+100)(sp)
        fsd     f5,  (104+104)(sp)
        fsd     f4,  (108+108)(sp)
        fsd     f3,  (112+112)(sp)
        fsd     f2,  (116+116)(sp)
        fsd     f1,  (120+120)(sp)
        fsd     f0,  (124+124)(sp)
#elif __riscv_flen == 32
        addi    sp,  sp, -(128)

        fsw     f31, (0  )(sp)
        fsw     f30, (4  )(sp)
        fsw     f29, (8  )(sp)
        fsw     f28, (12 )(sp)
        fsw     f27, (16 )(sp)
        fsw     f26, (20 )(sp)
        fsw     f25, (24 )(sp)
        fsw     f24, (28 )(sp)
        fsw     f23, (32 )(sp)
        fsw     f22, (36 )(sp)
        fsw     f21, (40 )(sp)
        fsw     f20, (44 )(sp)
        fsw     f19, (48 )(sp)
        fsw     f18, (52 )(sp)
        fsw     f17, (56 )(sp)
        fsw     f16, (60 )(sp)
        fsw     f15, (64 )(sp)
        fsw     f14, (68 )(sp)
        fsw     f13, (72 )(sp)
        fsw     f12, (76 )(sp)
        fsw     f11, (80 )(sp)
        fsw     f10, (84 )(sp)
        fsw     f9,  (88 )(sp)
        fsw     f8,  (92 )(sp)
        fsw     f7,  (96 )(sp)
        fsw     f6,  (100)(sp)
        fsw     f5,  (104)(sp)
        fsw     f4,  (108)(sp)
        fsw     f3,  (112)(sp)
        fsw     f2,  (116)(sp)
        fsw     f1,  (120)(sp)
        fsw     f0,  (124)(sp)
#endif
	.endm

.macro portasmRESTORE_ADDITIONAL_REGISTERS
	/* load float registers */
#if __riscv_flen == 64
        fld     f31, (0  + 0 )(sp)
        fld     f30, (4  + 4 )(sp)
        fld     f29, (8  + 8 )(sp)
        fld     f28, (12 + 12)(sp)
        fld     f27, (16 + 16)(sp)
        fld     f26, (20 + 20)(sp)
        fld     f25, (24 + 24)(sp)
        fld     f24, (28 + 28)(sp)
        fld     f23, (32 + 32)(sp)
        fld     f22, (36 + 36)(sp)
        fld     f21, (40 + 40)(sp)
        fld     f20, (44 + 44)(sp)
        fld     f19, (48 + 48)(sp)
        fld     f18, (52 + 52)(sp)
        fld     f17, (56 + 56)(sp)
        fld     f16, (60 + 60)(sp)
        fld     f15, (64 + 64)(sp)
        fld     f14, (68 + 68)(sp)
        fld     f13, (72 + 72)(sp)
        fld     f12, (76 + 76)(sp)
        fld     f11, (80 + 80)(sp)
        fld     f10, (84 + 84)(sp)
        fld     f9,  (88 + 88)(sp)
        fld     f8,  (92 + 92)(sp)
        fld     f7,  (96 + 96)(sp)
        fld     f6,  (100+100)(sp)
        fld     f5,  (104+104)(sp)
        fld     f4,  (108+108)(sp)
        fld     f3,  (112+112)(sp)
        fld     f2,  (116+116)(sp)
        fld     f1,  (120+120)(sp)
        fld     f0,  (124+124)(sp)

        addi    sp, sp, (128+128)
#elif __riscv_flen == 32
        flw     f31, (0  )(sp)
        flw     f30, (4  )(sp)
        flw     f29, (8  )(sp)
        flw     f28, (12 )(sp)
        flw     f27, (16 )(sp)
        flw     f26, (20 )(sp)
        flw     f25, (24 )(sp)
        flw     f24, (28 )(sp)
        flw     f23, (32 )(sp)
        flw     f22, (36 )(sp)
        flw     f21, (40 )(sp)
        flw     f20, (44 )(sp)
        flw     f19, (48 )(sp)
        flw     f18, (52 )(sp)
        flw     f17, (56 )(sp)
        flw     f16, (60 )(sp)
        flw     f15, (64 )(sp)
        flw     f14, (68 )(sp)
        flw     f13, (72 )(sp)
        flw     f12, (76 )(sp)
        flw     f11, (80 )(sp)
        flw     f10, (84 )(sp)
        flw     f9,  (88 )(sp)
        flw     f8,  (92 )(sp)
        flw     f7,  (96 )(sp)
        flw     f6,  (100)(sp)
        flw     f5,  (104)(sp)
        flw     f4,  (108)(sp)
        flw     f3,  (112)(sp)
        flw     f2,  (116)(sp)
        flw     f1,  (120)(sp)
        flw     f0,  (124)(sp)

        addi    sp, sp, (128)
#endif
	.endm
#endif /* __FREERTOS_RISC_V_EXTENSIONS_H__ */
