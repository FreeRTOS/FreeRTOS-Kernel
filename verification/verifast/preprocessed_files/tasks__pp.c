// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
// # 1 "<built-in>" 1
// # 1 "<built-in>" 3
// # 400 "<built-in>" 3
// # 1 "<command line>" 1
// # 1 "<built-in>" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */


    /* Ghost header include must occur before any non-ghost includes or other
     * non-ghost code. Otherwise VeriFast will report an unspecific parse error.
     */

    //@ #include <bitops.gh>



/* Standard includes. */
// # 1 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stdlib.h" 1



// # 1 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stdbool.h" 1
// # 5 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stdlib.h" 2
// # 1 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/malloc.h" 1



// # 1 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stddef.h" 1



typedef uintptr_t size_t;
typedef intptr_t ptrdiff_t;
typedef intptr_t ssize_t;
// # 5 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/malloc.h" 2

/*@

// In Standard C, freeing a null pointer is allowed and is a no-op.
lemma_auto void malloc_block_null();
    requires emp;
    ensures malloc_block(0, 0);

lemma void malloc_block_limits(void *array);
    requires [?f]malloc_block(array, ?size);
    ensures [f]malloc_block(array, size) &*& (void *)0 <= array &*& 0 <= size &*& array + size <= (void *)UINTPTR_MAX;

@*/

void *malloc(size_t size);
    //@ requires true;
    /*@
    ensures
        result == 0 ?
            emp
        :
            chars_(result, size, _) &*& malloc_block(result, size) &*&
            (char *)0 < result && result + size <= (char *)UINTPTR_MAX; // one-past-end does not overflow
    @*/
    //@ terminates;

void *calloc(size_t nmemb, size_t size);
    //@ requires true;
    /*@
    ensures
        result == 0 ?
            emp
        :
            chars(result, nmemb * size, ?cs) &*& malloc_block(result, nmemb * size) &*& all_eq(cs, 0) == true &*&
            (char *)0 < result && result + nmemb * size <= (char *)UINTPTR_MAX; // one-past-end does not overflow
    @*/
    //@ terminates;

void free(void *array);
    //@ requires malloc_block(array, ?size) &*& chars_(array, size, ?cs);
    //@ ensures emp;
    //@ terminates;

void *realloc(void *array, size_t newSize);
    //@ requires malloc_block(array, ?size) &*& chars(array, size, ?cs);
    /*@
    ensures
        result == 0 ?
            malloc_block(array, size) &*& chars(array, size, cs)
        :
            malloc_block(result, newSize) &*&
            newSize <= size ?
                chars(result, _, take(newSize, cs))
            :
                chars(result, _, cs) &*& chars(result + size, newSize - size, _);
    @*/
    //@ terminates;
// # 6 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stdlib.h" 2

void abort();
    //@ requires true;
    //@ ensures false;
    //@ terminates;

void exit(int status);
    //@ requires true;
    //@ ensures false;
    //@ terminates;

int abs(int x);
    //@ requires INT_MIN < x;
    //@ ensures result == abs(x);
    //@ terminates;

long labs(long x);
    //@ requires LONG_MIN < x;
    //@ ensures result == abs(x);
    //@ terminates;

long long llabs(long long x);
    //@ requires LLONG_MIN < x;
    //@ ensures result == abs(x);
    //@ terminates;
// # 38 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/string.h" 1





char *strcpy(char *d, char *s);
    //@ requires [?f]string(s, ?cs) &*& chars(d, length(cs) + 1, _);
    //@ ensures [f]string(s, cs) &*& chars(d, length(cs) + 1, append(cs, {0})) &*& result == d;

void memcpy(void *array, void *array0, size_t count);
    //@ requires chars_(array, count, _) &*& [?f]chars(array0, count, ?cs0);
    //@ ensures chars(array, count, cs0) &*& [f]chars(array0, count, cs0);

void memmove(void *dest, void *src, size_t count);
    /*@
    requires
        chars(src, count, ?cs) &*&
        dest <= src ?
            chars(dest, src - dest, _)
        :
            chars(src + count, dest - src, _);
    @*/
    /*@
    ensures
        chars(dest, count, cs) &*&
        dest <= src ?
            chars(dest + count, src - dest, _)
        :
            chars(src, dest - src, _);
    @*/

size_t strlen(char *string);
    //@ requires [?f]string(string, ?cs);
    //@ ensures [f]string(string, cs) &*& result == length(cs);

int memcmp(char *array, char *array0, size_t count);
    //@ requires [?f]chars(array, ?n, ?cs) &*& [?f0]chars(array0, ?n0, ?cs0) &*& count <= n &*& count <= n0;
    //@ ensures [f]chars(array, n, cs) &*& [f0]chars(array0, n0, cs0) &*& (result == 0) == (take(count, cs) == take(count, cs0));

int strcmp(char *s1, char *s2);
    //@ requires [?f1]string(s1, ?cs1) &*& [?f2]string(s2, ?cs2);
    //@ ensures [f1]string(s1, cs1) &*& [f2]string(s2, cs2) &*& (result == 0) == (cs1 == cs2);

char *memchr(char *array, char c, size_t count);
    //@ requires [?f]chars(array, count, ?cs);
    //@ ensures [f]chars(array, count, cs) &*& result == 0 ? mem(c, cs) == false : mem(c, cs) == true &*& result == array + index_of(c, cs);

char* strchr(char *str, char c);
    //@ requires [?f]string(str, ?cs);
    /*@ ensures
            [f]string(str, cs) &*&
            c == 0 ? 
                result == str + length(cs)
            : 
                result == 0 ?
                    mem(c, cs) == false
                :
                    mem(c, cs) == true &*& result == str + index_of(c, cs);
    @*/

void* memset(void *array, char value, size_t size);
    //@ requires chars_(array, size, _);
    //@ ensures chars(array, size, ?cs1) &*& all_eq(cs1, value) == true &*& result == array;

char *strdup(char *string);
    //@ requires [?f]string(string, ?cs);
    //@ ensures [f]string(string, cs) &*& result == 0 ? true : string(result, cs) &*& malloc_block_chars(result, length(cs) + 1);
// # 39 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
 * all the API functions to use the MPU wrappers.  That should only be done when
 * task.h is included from an application file. */


/* FreeRTOS includes. */
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */




/*
 * Include the generic headers required for the FreeRTOS port being used.
 */


/*
 * If stdint.h cannot be located then:
 *   + If using GCC ensure the -nostdint options is *not* being used.
 *   + Ensure the project's include path includes the directory in which your
 *     compiler stores stdint.h.
 *   + Set any compiler options necessary for it to support C99, as technically
 *     stdint.h is only mandatory with C99 (FreeRTOS does not require C99 in any
 *     other way).
 *   + The FreeRTOS download includes a simple stdint.h definition that can be
 *     used in cases where none is provided by the compiler.  The files only
 *     contains the typedefs required to build FreeRTOS.  Read the instructions
 *     in FreeRTOS/source/stdint.readme for more information.
 */
// # 1 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stdint.h" 1
// # 18 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stdint.h"
typedef __int8 int8_t;
typedef __int16 int16_t;
typedef __int32 int32_t;
typedef __int64 int64_t;
typedef __int128 int128_t;

typedef unsigned __int8 uint8_t;
typedef unsigned __int16 uint16_t;
typedef unsigned __int32 uint32_t;
typedef unsigned __int64 uint64_t;
typedef unsigned __int128 uint128_t;
// # 49 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h" 2

/* *INDENT-OFF* */



/* *INDENT-ON* */

/* Application specific configuration options. */
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/FreeRTOSConfig.h" 1
/* This is a stub used for the VeriFast proof. */

/*
 * FreeRTOS V202107.00
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */




/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 *
 * See http://www.freertos.org/a00110.html
 *----------------------------------------------------------*/

/* Scheduler Related */
// # 57 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/FreeRTOSConfig.h"
/* Synchronization Related */
// # 69 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/FreeRTOSConfig.h"
/* System */



/* Memory allocation related definitions. */





/* Hook function related definitions. */




/* Run time and task stats gathering related definitions. */




/* Co-routine related definitions. */



/* Software timer related definitions. */





/* Interrupt nesting behaviour configuration. */
/*
// #define configKERNEL_INTERRUPT_PRIORITY         [dependent of processor]
// #define configMAX_SYSCALL_INTERRUPT_PRIORITY    [dependent on processor and application]
// #define configMAX_API_CALL_INTERRUPT_PRIORITY   [dependent on processor and application]
*/

/* SMP port only */




/* RP2040 specific */







/* Define to trap errors during development. */


/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */
// # 141 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/FreeRTOSConfig.h"
/* A header file that defines trace macro can be included here. */
// # 58 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h" 2

/* Basic FreeRTOS definitions. */
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/projdefs.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */




/*
 * Defines the prototype to which task functions must conform.  Defined in this
 * file to ensure the type is known before portable.h is included.
 */
typedef void (* TaskFunction_t)( void * );

/* Converts a time in milliseconds to a time in ticks.  This macro can be
 * overridden by a macro of the same name defined in FreeRTOSConfig.h in case the
 * definition here is not suitable for your application. */
// # 51 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/projdefs.h"
/* FreeRTOS error definitions. */




/* Macros used for basic data corruption checks. */
// # 67 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/projdefs.h"
/* The following errno values are used by FreeRTOS+ components, not FreeRTOS
 * itself. */
// # 110 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/projdefs.h"
/* The following endian values are used by FreeRTOS+ components, not FreeRTOS
 * itself. */



/* Re-defining endian values for generic naming. */
// # 61 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h" 2

/* Definitions specific to the port being used. */
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */

/*-----------------------------------------------------------
* Portable layer API.  Each function must be defined for each port.
*----------------------------------------------------------*/




/* Each FreeRTOS port has a unique portmacro.h header file.  Originally a
 * pre-processor definition was used to ensure the pre-processor found the correct
 * portmacro.h file for the port being used.  That scheme was deprecated in favour
 * of setting the compiler's include path such that it found the correct
 * portmacro.h file - removing the need for the constant and allowing the
 * portmacro.h file to be located anywhere in relation to the port being used.
 * Purely for reasons of backward compatibility the old method is still valid, but
 * to make it clear that new projects should not use it, support for the port
 * specific constants has been moved into the deprecated_definitions.h header
 * file. */
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/deprecated_definitions.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */





/* Each FreeRTOS port has a unique portmacro.h header file.  Originally a
 * pre-processor definition was used to ensure the pre-processor found the correct
 * portmacro.h file for the port being used.  That scheme was deprecated in favour
 * of setting the compiler's include path such that it found the correct
 * portmacro.h file - removing the need for the constant and allowing the
 * portmacro.h file to be located anywhere in relation to the port being used.  The
 * definitions below remain in the code for backward compatibility only.  New
 * projects should not use them. */
// # 45 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h" 2

/* If portENTER_CRITICAL is not defined then including deprecated_definitions.h
 * did not result in a portmacro.h header file being included - and it should be
 * included here.  In this case the path to the correct portmacro.h header file
 * must be set in the compiler's include path. */

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Copyright (c) 2021 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: MIT AND BSD-3-Clause
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
// # 37 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h"
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */




/** \file pico.h
 *  \defgroup pico_base pico_base
 *
 * Core types and macros for the Raspberry Pi Pico SDK. This header is intended to be included by all source code
 * as it includes configuration headers and overrides in the correct order
 *
 * This header may be included by assembly code
*/




// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/types.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */






// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/assert.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */




// # 1 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stdbool.h" 1
// # 11 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/assert.h" 2







// # 1 "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/assert.h" 1 3 4
/*-
 * Copyright (c) 1992, 1993
 *	The Regents of the University of California.  All rights reserved.
 * (c) UNIX System Laboratories, Inc.
 * All or some portions of this file are derived from material licensed
 * to the University of California by American Telephone and Telegraph
 * Co. or Unix System Laboratories, Inc. and are reproduced herein with
 * the permission of UNIX System Laboratories, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)assert.h	8.2 (Berkeley) 1/21/94
 * $FreeBSD: src/include/assert.h,v 1.4 2002/03/23 17:24:53 imp Exp $
 */

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 1 3 4
/* This is a stub used for the VeriFast proof. */

/*
 * Copyright (c) 2000-2018 Apple Inc. All rights reserved.
 *
 * @APPLE_OSREFERENCE_LICENSE_HEADER_START@
 *
 * This file contains Original Code and/or Modifications of Original Code
 * as defined in and that are subject to the Apple Public Source License
 * Version 2.0 (the 'License'). You may not use this file except in
 * compliance with the License. The rights granted to you under the License
 * may not be used to create, or enable the creation or redistribution of,
 * unlawful or unlicensed copies of an Apple operating system, or to
 * circumvent, violate, or enable the circumvention or violation of, any
 * terms of an Apple operating system software license agreement.
 *
 * Please obtain a copy of the License at
 * http://www.opensource.apple.com/apsl/ and read it before using this file.
 *
 * The Original Code and all software distributed under the License are
 * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
 * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
 * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
 * Please see the License for the specific language governing rights and
 * limitations under the License.
 *
 * @APPLE_OSREFERENCE_LICENSE_HEADER_END@
 */
/* Copyright 1995 NeXT Computer, Inc. All rights reserved. */
/*
 * Copyright (c) 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Berkeley Software Design, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)cdefs.h	8.8 (Berkeley) 1/9/95
 */




/* Verifast proof setup */

    /*
     * The proof setup header is already included at the top of the proof target,
     * e.g., `tasks.c`. But it seems like the contained defines are not propagated
     * to this file.
     */
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/verifast_proof_defs.h" 1 3 4
/*
 * This file contains defines to configure the VeriFast proof setup.
 *
 */



    // Delete keywords VeriFast canot parse (in some contexts)



    /* `projdefs.h` defines `pdFALSE` and `pdTRUE` as 0 and 1 of type
     * `BaseType_t`. Both are assigned to variables smaller or
     * unsigned types. While that's safe in practice, it is not
     * type safe. Hence we define 
     */
// # 80 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 2 3 4
// # 90 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/* This SDK is designed to work with clang and specific versions of
 * gcc >= 4.0 with Apple's patch sets */




/*
 * Compatibility with compilers and environments that don't support compiler
 * feature checking function-like macros.
 */
// # 116 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * The __CONCAT macro is used to concatenate parts of symbol names, e.g.
 * with "#define OLD(foo) __CONCAT(old,foo)", OLD(foo) produces oldfoo.
 * The __CONCAT macro is a bit tricky -- make sure you don't put spaces
 * in between its arguments.  __CONCAT can also concatenate double-quoted
 * strings produced by the __STRING macro, but this only works with ANSI C.
 */
// # 167 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * __pure2 can be used for functions that are only a function of their scalar
 * arguments (meaning they can't dereference pointers).
 *
 * __stateful_pure can be used for functions that have no side effects,
 * but depend on the state of the memory.
 */




/* __unused denotes variables and functions that may not be used, preventing
 * the compiler from warning about it if not used.
 */


/* __used forces variables and functions to be included even if it appears
 * to the compiler that they are not used (and would thust be discarded).
 */


/* __cold marks code used for debugging or that is rarely taken
 * and tells the compiler to optimize for size and outline code.
 */






/* __exported denotes symbols that should be exported even when symbols
 * are hidden by default.
 * __exported_push/_exported_pop are pragmas used to delimit a range of
 *  symbols that should be exported even when symbols are hidden by default.
 */




/* __deprecated causes the compiler to produce a warning when encountering
 * code using the deprecated functionality.
 * __deprecated_msg() does the same, and compilers that support it will print
 * a message along with the deprecation warning.
 * This may require turning on such warning with the -Wdeprecated flag.
 * __deprecated_enum_msg() should be used on enums, and compilers that support
 * it will print the deprecation warning.
 * __kpi_deprecated() specifically indicates deprecation of kernel programming
 * interfaces in Kernel.framework used by KEXTs.
 */
// # 233 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/* __unavailable causes the compiler to error out when encountering
 * code using the tagged function
 */
// # 250 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/* Delete pseudo-keywords wherever they are not available or needed. */





/*
 * We use `__restrict' as a way to define the `restrict' type qualifier
 * without disturbing older software that is unaware of C99 keywords.
 */






/* Compatibility with compilers and environments that don't support the
 * nullability feature.
 */
// # 291 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * __disable_tail_calls causes the compiler to not perform tail call
 * optimization inside the marked function.
 */






/*
 * __not_tail_called causes the compiler to prevent tail call optimization
 * on statically bound calls to the function.  It has no effect on indirect
 * calls.  Virtual functions, objective-c methods, and functions marked as
 * "always_inline" cannot be marked as __not_tail_called.
 */






/*
 * __result_use_check warns callers of a function that not using the function
 * return value is a bug, i.e. dismissing malloc() return value results in a
 * memory leak.
 */






/*
 * __swift_unavailable causes the compiler to mark a symbol as specifically
 * unavailable in Swift, regardless of any other availability in C.
 */






/*
 * __abortlike is the attribute to put on functions like abort() that are
 * typically used to mark assertions. These optimize the codegen
 * for outlining while still maintaining debugability.
 */




/* Declaring inline functions within headers is error-prone due to differences
 * across various versions of the C language and extensions.  __header_inline
 * can be used to declare inline functions within system headers.  In cases
 * where you want to force inlining instead of letting the compiler make
 * the decision, you can use __header_always_inline.
 *
 * Be aware that using inline for functions which compilers may also provide
 * builtins can behave differently under various compilers.  If you intend to
 * provide an inline version of such a function, you may want to use a macro
 * instead.
 *
 * The check for !__GNUC__ || __clang__ is because gcc doesn't correctly
 * support c99 inline in some cases:
 * http://gcc.gnu.org/bugzilla/show_bug.cgi?id=55965
 */
// # 384 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * Compiler-dependent macros that bracket portions of code where the
 * "-Wunreachable-code" warning should be ignored. Please use sparingly.
 */
// # 405 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * Compiler-dependent macros to declare that functions take printf-like
 * or scanf-like arguments.  They are null except for versions of gcc
 * that are known to support the features properly.  Functions declared
 * with these attributes will cause compilation warnings if there is a
 * mismatch between the format string and subsequent function parameter
 * types.
 */
// # 440 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/* Source compatibility only, ID string not emitted in object file */
// # 457 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * __alloc_size can be used to label function arguments that represent the
 * size of memory that the function allocates and returns. The one-argument
 * form labels a single argument that gives the allocation size (where the
 * arguments are numbered from 1):
 *
 * void	*malloc(size_t __size) __alloc_size(1);
 *
 * The two-argument form handles the case where the size is calculated as the
 * product of two arguments:
 *
 * void	*calloc(size_t __count, size_t __size) __alloc_size(1,2);
 */
// # 478 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * COMPILATION ENVIRONMENTS -- see compat(5) for additional detail
 *
 * DEFAULT	By default newly complied code will get POSIX APIs plus
 *		Apple API extensions in scope.
 *
 *		Most users will use this compilation environment to avoid
 *		behavioral differences between 32 and 64 bit code.
 *
 * LEGACY	Defining _NONSTD_SOURCE will get pre-POSIX APIs plus Apple
 *		API extensions in scope.
 *
 *		This is generally equivalent to the Tiger release compilation
 *		environment, except that it cannot be applied to 64 bit code;
 *		its use is discouraged.
 *
 *		We expect this environment to be deprecated in the future.
 *
 * STRICT	Defining _POSIX_C_SOURCE or _XOPEN_SOURCE restricts the
 *		available APIs to exactly the set of APIs defined by the
 *		corresponding standard, based on the value defined.
 *
 *		A correct, portable definition for _POSIX_C_SOURCE is 200112L.
 *		A correct, portable definition for _XOPEN_SOURCE is 600L.
 *
 *		Apple API extensions are not visible in this environment,
 *		which can cause Apple specific code to fail to compile,
 *		or behave incorrectly if prototypes are not in scope or
 *		warnings about missing prototypes are not enabled or ignored.
 *
 * In any compilation environment, for correct symbol resolution to occur,
 * function prototypes must be in scope.  It is recommended that all Apple
 * tools users add either the "-Wall" or "-Wimplicit-function-declaration"
 * compiler flags to their projects to be warned when a function is being
 * used without a prototype in scope.
 */

/* These settings are particular to each product. */
// # 526 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * The __DARWIN_ALIAS macros are used to do symbol renaming; they allow
 * legacy code to use the old symbol, thus maintaining binary compatibility
 * while new code can use a standards compliant version of the same function.
 *
 * __DARWIN_ALIAS is used by itself if the function signature has not
 * changed, it is used along with a #ifdef check for __DARWIN_UNIX03
 * if the signature has changed.  Because the __LP64__ environment
 * only supports UNIX03 semantics it causes __DARWIN_UNIX03 to be
 * defined, but causes __DARWIN_ALIAS to do no symbol mangling.
 *
 * As a special case, when XCode is used to target a specific version of the
 * OS, the manifest constant __ENVIRONMENT_MAC_OS_X_VERSION_MIN_REQUIRED__
 * will be defined by the compiler, with the digits representing major version
 * time 100 + minor version times 10 (e.g. 10.5 := 1050).  If we are targeting
 * pre-10.5, and it is the default compilation environment, revert the
 * compilation environment to pre-__DARWIN_UNIX03.
 */
// # 560 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * symbol suffixes used for symbol versioning
 */
// # 605 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * symbol versioning macros
 */
// # 623 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * symbol release macros
 */



/*
 * POSIX.1 requires that the macros we test be defined before any standard
 * header file is included.  This permits us to convert values for feature
 * testing, as necessary, using only _POSIX_C_SOURCE.
 *
 * Here's a quick run-down of the versions:
 *  defined(_POSIX_SOURCE)		1003.1-1988
 *  _POSIX_C_SOURCE == 1L		1003.1-1990
 *  _POSIX_C_SOURCE == 2L		1003.2-1992 C Language Binding Option
 *  _POSIX_C_SOURCE == 199309L		1003.1b-1993
 *  _POSIX_C_SOURCE == 199506L		1003.1c-1995, 1003.1i-1995,
 *					and the omnibus ISO/IEC 9945-1: 1996
 *  _POSIX_C_SOURCE == 200112L		1003.1-2001
 *  _POSIX_C_SOURCE == 200809L		1003.1-2008
 *
 * In addition, the X/Open Portability Guide, which is now the Single UNIX
 * Specification, defines a feature-test macro which indicates the version of
 * that specification, and which subsumes _POSIX_C_SOURCE.
 */

/* Deal with IEEE Std. 1003.1-1990, in which _POSIX_C_SOURCE == 1L. */





/* Deal with IEEE Std. 1003.2-1992, in which _POSIX_C_SOURCE == 2L. */





/* Deal with various X/Open Portability Guides and Single UNIX Spec. */
// # 675 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * Deal with all versions of POSIX.  The ordering relative to the tests above is
 * important.
 */




/* POSIX C deprecation macros */


/*
 * Set a single macro which will always be defined and can be used to determine
 * the appropriate namespace.  For POSIX, these values will correspond to
 * _POSIX_C_SOURCE value.  Currently there are two additional levels corresponding
 * to ANSI (_ANSI_SOURCE) and Darwin extensions (_DARWIN_C_SOURCE)
 */
// # 703 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/* If the developer has neither requested a strict language mode nor a version
 * of POSIX, turn on functionality provided by __STDC_WANT_LIB_EXT1__ as part
 * of __DARWIN_C_FULL.
 */




/*
 * long long is not supported in c89 (__STRICT_ANSI__), but g++ -ansi and
 * c99 still want long longs.  While not perfect, we allow long longs for
 * g++.
 */






/*****************************************
*  Public darwin-specific feature macros
*****************************************/

/*
 * _DARWIN_FEATURE_64_BIT_INODE indicates that the ino_t type is 64-bit, and
 * structures modified for 64-bit inodes (like struct stat) will be used.
 */




/*
 * _DARWIN_FEATURE_64_ONLY_BIT_INODE indicates that the ino_t type may only
 * be 64-bit; there is no support for 32-bit ino_t when this macro is defined
 * (and non-zero).  There is no struct stat64 either, as the regular
 * struct stat will already be the 64-bit version.
 */




/*
 * _DARWIN_FEATURE_ONLY_VERS_1050 indicates that only those APIs updated
 * in 10.5 exists; no pre-10.5 variants are available.
 */




/*
 * _DARWIN_FEATURE_ONLY_UNIX_CONFORMANCE indicates only UNIX conforming API
 * are available (the legacy BSD APIs are not available)
 */




/*
 * _DARWIN_FEATURE_UNIX_CONFORMANCE indicates whether UNIX conformance is on,
 * and specifies the conformance level (3 is SUSv3)
 */





/*
 * This macro casts away the qualifier from the variable
 *
 * Note: use at your own risk, removing qualifiers can result in
 * catastrophic run-time failures.
 */




/*
 * __XNU_PRIVATE_EXTERN is a linkage decoration indicating that a symbol can be
 * used from other compilation units, but not other libraries or executables.
 */







/*
 * We intentionally define to nothing pointer attributes which do not have an
 * impact on the ABI. __indexable and __bidi_indexable are not defined because
 * of the ABI incompatibility that makes the diagnostic preferable.
 */







/*
 * Similarly, we intentionally define to nothing the
 * __ptrcheck_abi_assume_single and __ptrcheck_abi_assume_unsafe_indexable
 * macros because they do not lead to an ABI incompatibility. However, we do not
 * define the indexable and unsafe_indexable ones because the diagnostic is
 * better than the silent ABI break.
 */



/* __unsafe_forge intrinsics are defined as regular C casts. */



/* decay operates normally; attribute is meaningless without pointer checks. */
// # 831 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * Architecture validation for current SDK
 */
// # 843 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * Check if __probable and __improbable have already been defined elsewhere.
 * These macros inform the compiler (and humans) about which branches are likely
 * to be taken.
 */
// # 875 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/sys/cdefs.h" 3 4
/*
 * Similar to OS_ENUM/OS_CLOSED_ENUM/OS_OPTIONS/OS_CLOSED_OPTIONS
 *
 * This provides more advanced type checking on compilers supporting
 * the proper extensions, even in C.
 */
// # 43 "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/assert.h" 2 3 4




/*
 * Unlike other ANSI header files, <assert.h> may usefully be included
 * multiple times, with and without NDEBUG defined.
 */
// # 82 "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/assert.h" 3 4
void __assert_rtn(const char *, const char *, int, const char *)   ;
// # 92 "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/assert.h" 3 4
/* 8462256: modified __assert_rtn() replaces deprecated __eprintf() */
// # 19 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/assert.h" 2


// PICO_CONFIG: PARAM_ASSERTIONS_ENABLE_ALL, Global assert enable, type=bool, default=0, group=pico_base
// PICO_CONFIG: PARAM_ASSERTIONS_DISABLE_ALL, Global assert disable, type=bool, default=0, group=pico_base
// # 35 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/assert.h"
    /* Reason for rewrite: 
     * Verifast cannot parse statements non-empty block statements wrapped in parentheses,
     * i.e., it can parse `{stmt;}` but not `( {stmt;} )`.
     */
// # 13 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/types.h" 2


// # 1 "/Users/reitobia/programs/verifast-21.04-83-gfae956f7/bin/stdbool.h" 1
// # 16 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/types.h" 2


typedef unsigned int uint;

/*! \typedef absolute_time_t
    \brief An opaque 64 bit timestamp in microseconds

    The type is used instead of a raw uint64_t to prevent accidentally passing relative times or times in the wrong
    time units where an absolute time is required. It is equivalent to uint64_t in release builds.

    \see to_us_since_boot()
    \see update_us_since_boot()
    \ingroup timestamp
*/



typedef struct {
    uint64_t _private_us_since_boot;
} absolute_time_t;


/*! fn to_us_since_boot
 * \brief convert an absolute_time_t into a number of microseconds since boot.
 * \param t the absolute time to convert
 * \return a number of microseconds since boot, equivalent to t
 * \ingroup timestamp
 */
static uint64_t to_us_since_boot(absolute_time_t t) {



    return t._private_us_since_boot;

}

/*! fn update_us_since_boot
 * \brief update an absolute_time_t value to represent a given number of microseconds since boot
 * \param t the absolute time value to update
 * \param us_since_boot the number of microseconds since boot to represent. Note this should be representable
 *                      as a signed 64 bit integer
 * \ingroup timestamp
 */
static void update_us_since_boot(absolute_time_t *t, uint64_t us_since_boot) {



    (__builtin_expect(!(us_since_boot <= 9223372036854775807), 0) ? __assert_rtn ((const char *)-1L, "types.h", 63, "us_since_boot <= INT64_MAX") : (void)0);
    t->_private_us_since_boot = us_since_boot;

}







/** \struct datetime_t
 *  \ingroup util_datetime
 *  \brief Structure containing date and time information
 *
 *    When setting an RTC alarm, set a field to -1 tells
 *    the RTC to not match on this field
 */
typedef struct {
    int16_t year; ///< 0..4095
    int8_t month; ///< 1..12, 1 is January
    int8_t day; ///< 1..28,29,30,31 depending on month
    int8_t dotw; ///< 0..6, 0 is Sunday
    int8_t hour; ///< 0..23
    int8_t min; ///< 0..59
    int8_t sec; ///< 0..59
} datetime_t;
// # 23 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico.h" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Demo/CORTEX_M0+_RP2040/build/generated/pico_base/pico/version.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ---------------------------------------
// THIS FILE IS AUTOGENERATED; DO NOT EDIT
// ---------------------------------------
// # 24 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico.h" 2

// PICO_CONFIG: PICO_CONFIG_HEADER, unquoted path to header include in place of the default pico/config.h which may be desirable for build systems which can't easily generate the config_autogen header, group=pico_base



// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/config.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */




// -----------------------------------------------------
// NOTE: THIS HEADER IS ALSO INCLUDED BY ASSEMBLY CODE SO
//       SHOULD ONLY CONSIST OF PREPROCESSOR DIRECTIVES
//       OR USE #ifndef __ASSEMBLER__ guards
// -------------

// PICO_CONFIG_HEADER_FILES and then PICO_SDK_<PLATFORM>_CONFIG_INCLUDE_FILES
// entries are dumped in order at build time into this generated header

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Demo/CORTEX_M0+_RP2040/build/generated/pico_base/pico/config_autogen.h" 1
// AUTOGENERATED FROM PICO_CONFIG_HEADER_FILES and then PICO_<PLATFORM>_CONFIG_HEADER_FILES
// DO NOT EDIT!


// based on PICO_CONFIG_HEADER_FILES:

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/portable/ThirdParty/GCC/RP2040/include/freertos_sdk_config.h" 1
/*
 * FreeRTOS Kernel V10.4.3
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Copyright (c) 2021 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
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
 */






// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/portable/ThirdParty/GCC/RP2040/include/rp2040_config.h" 1
/*
 * FreeRTOS Kernel V10.4.3
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Copyright (c) 2021 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: MIT AND BSD-3-Clause
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
 */
// # 36 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/portable/ThirdParty/GCC/RP2040/include/rp2040_config.h"
/* configUSE_DYNAMIC_EXCEPTION_HANDLERS == 1 means set the exception handlers dynamically on cores
 * that need them in case the user has set up distinct vector table offsets per core
 */
// # 47 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/portable/ThirdParty/GCC/RP2040/include/rp2040_config.h"
/* configSUPPORT_PICO_SYNC_INTEROP == 1 means that SDK pico_sync
 * sem/mutex/queue etc. will work correctly when called from FreeRTOS tasks
 */






/* configSUPPORT_PICO_SYNC_INTEROP == 1 means that SDK pico_time
 * sleep_ms/sleep_us/sleep_until will work correctly when called from FreeRTOS
 * tasks, and will actually block at the FreeRTOS level
 */
// # 74 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/portable/ThirdParty/GCC/RP2040/include/rp2040_config.h"
/* This SMP port requires two spin locks, which are claimed from the SDK.
 * the spin lock numbers to be used are defined statically and defaulted here
 * to the values nominally set aside for RTOS by the SDK */
// # 35 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/portable/ThirdParty/GCC/RP2040/include/freertos_sdk_config.h" 2


        // increase the amount of time it may reasonably take to wake us up





        extern uint32_t ulPortLockGetCurrentOwnerId(void);



        struct lock_core;

        extern void vPortLockInternalSpinUnlockWithWait( struct lock_core *pxLock, uint32_t ulSave);




        extern void vPortLockInternalSpinUnlockWithNotify( struct lock_core *pxLock, uint32_t save);




        extern bool xPortLockInternalSpinUnlockWithBestEffortWaitOrTimeout( struct lock_core *pxLock, uint32_t ulSave, absolute_time_t uxUntil);






        extern void xPortSyncInternalYieldUntilBefore(absolute_time_t t);
// # 8 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Demo/CORTEX_M0+_RP2040/build/generated/pico_base/pico/config_autogen.h" 2
// # 1 "/Users/reitobia/programs/pico-sdk/src/boards/include/boards/pico.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

// -----------------------------------------------------
// NOTE: THIS HEADER IS ALSO INCLUDED BY ASSEMBLER SO
//       SHOULD ONLY CONSIST OF PREPROCESSOR DIRECTIVES
// -----------------------------------------------------

// This header may be included by other board headers as "boards/pico.h"




// For board detection


// --- UART ---
// # 31 "/Users/reitobia/programs/pico-sdk/src/boards/include/boards/pico.h"
// --- LED ---



// no PICO_DEFAULT_WS2812_PIN

// --- I2C ---
// # 48 "/Users/reitobia/programs/pico-sdk/src/boards/include/boards/pico.h"
// --- SPI ---
// # 65 "/Users/reitobia/programs/pico-sdk/src/boards/include/boards/pico.h"
// --- FLASH ---
// # 77 "/Users/reitobia/programs/pico-sdk/src/boards/include/boards/pico.h"
// Drive high to force power supply into PWM mode (lower ripple on 3V3 at light loads)
// # 9 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Demo/CORTEX_M0+_RP2040/build/generated/pico_base/pico/config_autogen.h" 2

// based on PICO_RP2040_CONFIG_HEADER_FILES:

// # 1 "/Users/reitobia/programs/pico-sdk/src/rp2_common/cmsis/include/cmsis/rename_exceptions.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */
// # 12 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Demo/CORTEX_M0+_RP2040/build/generated/pico_base/pico/config_autogen.h" 2
// # 20 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/config.h" 2

// PICO_CONFIG: PICO_CONFIG_RTOS_ADAPTER_HEADER, unquoted path to header include in the default pico/config.h for RTOS integration defines that must be included in all sources, group=pico_base
// # 30 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico.h" 2

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/pico_platform/include/pico/platform.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */




/** \file platform.h
 *  \defgroup pico_platform pico_platform
 *
 * Macros and definitions (and functions when included by non assembly code) for the RP2 family device / architecture
 * to provide a common abstraction over low level compiler / platform specifics.
 *
 * This header may be included by assembly code
 */

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2040/hardware_regs/include/hardware/platform_defs.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */




// This header is included from C and assembler - intended mostly for #defines; guard other stuff with #ifdef __ASSEMBLER__
// # 40 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2040/hardware_regs/include/hardware/platform_defs.h"
// PICO_CONFIG: XOSC_MHZ, The crystal oscillator frequency in Mhz, type=int, default=12, advanced=true, group=hardware_base
// # 20 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/pico_platform/include/pico/platform.h" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2040/hardware_regs/include/hardware/regs/addressmap.h" 1
/**
 * Copyright (c) 2021 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */





// Register address offsets for atomic RMW aliases
// # 21 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/pico_platform/include/pico/platform.h" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2040/hardware_regs/include/hardware/regs/sio.h" 1
/**
 * Copyright (c) 2022 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */
// =============================================================================
// Register block : SIO
// Version        : 1
// Bus type       : apb
// Description    : Single-cycle IO block
//                  Provides core-local and inter-core hardware for the two
//                  processors, with single-cycle access.
// =============================================================================


// =============================================================================
// Register    : SIO_CPUID
// Description : Processor core identifier
//               Value is 0 when read from processor core 0, and 1 when read
//               from processor core 1.






// =============================================================================
// Register    : SIO_GPIO_IN
// Description : Input value for GPIO pins
//               Input value for GPIO0...29






// =============================================================================
// Register    : SIO_GPIO_HI_IN
// Description : Input value for QSPI pins
//               Input value on QSPI IO in order 0..5: SCLK, SSn, SD0, SD1, SD2,
//               SD3






// =============================================================================
// Register    : SIO_GPIO_OUT
// Description : GPIO output value
//               Set output level (1/0 -> high/low) for GPIO0...29.
//               Reading back gives the last value written, NOT the input value
//               from the pins.
//               If core 0 and core 1 both write to GPIO_OUT simultaneously (or
//               to a SET/CLR/XOR alias),
//               the result is as though the write from core 0 took place first,
//               and the write from core 1 was then applied to that intermediate
//               result.






// =============================================================================
// Register    : SIO_GPIO_OUT_SET
// Description : GPIO output value set
//               Perform an atomic bit-set on GPIO_OUT, i.e. `GPIO_OUT |= wdata`






// =============================================================================
// Register    : SIO_GPIO_OUT_CLR
// Description : GPIO output value clear
//               Perform an atomic bit-clear on GPIO_OUT, i.e. `GPIO_OUT &=
//               ~wdata`






// =============================================================================
// Register    : SIO_GPIO_OUT_XOR
// Description : GPIO output value XOR
//               Perform an atomic bitwise XOR on GPIO_OUT, i.e. `GPIO_OUT ^=
//               wdata`






// =============================================================================
// Register    : SIO_GPIO_OE
// Description : GPIO output enable
//               Set output enable (1/0 -> output/input) for GPIO0...29.
//               Reading back gives the last value written.
//               If core 0 and core 1 both write to GPIO_OE simultaneously (or
//               to a SET/CLR/XOR alias),
//               the result is as though the write from core 0 took place first,
//               and the write from core 1 was then applied to that intermediate
//               result.






// =============================================================================
// Register    : SIO_GPIO_OE_SET
// Description : GPIO output enable set
//               Perform an atomic bit-set on GPIO_OE, i.e. `GPIO_OE |= wdata`






// =============================================================================
// Register    : SIO_GPIO_OE_CLR
// Description : GPIO output enable clear
//               Perform an atomic bit-clear on GPIO_OE, i.e. `GPIO_OE &=
//               ~wdata`






// =============================================================================
// Register    : SIO_GPIO_OE_XOR
// Description : GPIO output enable XOR
//               Perform an atomic bitwise XOR on GPIO_OE, i.e. `GPIO_OE ^=
//               wdata`






// =============================================================================
// Register    : SIO_GPIO_HI_OUT
// Description : QSPI output value
//               Set output level (1/0 -> high/low) for QSPI IO0...5.
//               Reading back gives the last value written, NOT the input value
//               from the pins.
//               If core 0 and core 1 both write to GPIO_HI_OUT simultaneously
//               (or to a SET/CLR/XOR alias),
//               the result is as though the write from core 0 took place first,
//               and the write from core 1 was then applied to that intermediate
//               result.






// =============================================================================
// Register    : SIO_GPIO_HI_OUT_SET
// Description : QSPI output value set
//               Perform an atomic bit-set on GPIO_HI_OUT, i.e. `GPIO_HI_OUT |=
//               wdata`






// =============================================================================
// Register    : SIO_GPIO_HI_OUT_CLR
// Description : QSPI output value clear
//               Perform an atomic bit-clear on GPIO_HI_OUT, i.e. `GPIO_HI_OUT
//               &= ~wdata`






// =============================================================================
// Register    : SIO_GPIO_HI_OUT_XOR
// Description : QSPI output value XOR
//               Perform an atomic bitwise XOR on GPIO_HI_OUT, i.e. `GPIO_HI_OUT
//               ^= wdata`






// =============================================================================
// Register    : SIO_GPIO_HI_OE
// Description : QSPI output enable
//               Set output enable (1/0 -> output/input) for QSPI IO0...5.
//               Reading back gives the last value written.
//               If core 0 and core 1 both write to GPIO_HI_OE simultaneously
//               (or to a SET/CLR/XOR alias),
//               the result is as though the write from core 0 took place first,
//               and the write from core 1 was then applied to that intermediate
//               result.






// =============================================================================
// Register    : SIO_GPIO_HI_OE_SET
// Description : QSPI output enable set
//               Perform an atomic bit-set on GPIO_HI_OE, i.e. `GPIO_HI_OE |=
//               wdata`






// =============================================================================
// Register    : SIO_GPIO_HI_OE_CLR
// Description : QSPI output enable clear
//               Perform an atomic bit-clear on GPIO_HI_OE, i.e. `GPIO_HI_OE &=
//               ~wdata`






// =============================================================================
// Register    : SIO_GPIO_HI_OE_XOR
// Description : QSPI output enable XOR
//               Perform an atomic bitwise XOR on GPIO_HI_OE, i.e. `GPIO_HI_OE
//               ^= wdata`






// =============================================================================
// Register    : SIO_FIFO_ST
// Description : Status register for inter-core FIFOs (mailboxes).
//               There is one FIFO in the core 0 -> core 1 direction, and one
//               core 1 -> core 0. Both are 32 bits wide and 8 words deep.
//               Core 0 can see the read side of the 1->0 FIFO (RX), and the
//               write side of 0->1 FIFO (TX).
//               Core 1 can see the read side of the 0->1 FIFO (RX), and the
//               write side of 1->0 FIFO (TX).
//               The SIO IRQ for each core is the logical OR of the VLD, WOF and
//               ROE fields of its FIFO_ST register.



// -----------------------------------------------------------------------------
// Field       : SIO_FIFO_ST_ROE
// Description : Sticky flag indicating the RX FIFO was read when empty. This
//               read was ignored by the FIFO.





// -----------------------------------------------------------------------------
// Field       : SIO_FIFO_ST_WOF
// Description : Sticky flag indicating the TX FIFO was written when full. This
//               write was ignored by the FIFO.





// -----------------------------------------------------------------------------
// Field       : SIO_FIFO_ST_RDY
// Description : Value is 1 if this core's TX FIFO is not full (i.e. if FIFO_WR
//               is ready for more data)





// -----------------------------------------------------------------------------
// Field       : SIO_FIFO_ST_VLD
// Description : Value is 1 if this core's RX FIFO is not empty (i.e. if FIFO_RD
//               is valid)





// =============================================================================
// Register    : SIO_FIFO_WR
// Description : Write access to this core's TX FIFO






// =============================================================================
// Register    : SIO_FIFO_RD
// Description : Read access to this core's RX FIFO






// =============================================================================
// Register    : SIO_SPINLOCK_ST
// Description : Spinlock state
//               A bitmap containing the state of all 32 spinlocks (1=locked).
//               Mainly intended for debugging.






// =============================================================================
// Register    : SIO_DIV_UDIVIDEND
// Description : Divider unsigned dividend
//               Write to the DIVIDEND operand of the divider, i.e. the p in `p
//               / q`.
//               Any operand write starts a new calculation. The results appear
//               in QUOTIENT, REMAINDER.
//               UDIVIDEND/SDIVIDEND are aliases of the same internal register.
//               The U alias starts an
//               unsigned calculation, and the S alias starts a signed
//               calculation.






// =============================================================================
// Register    : SIO_DIV_UDIVISOR
// Description : Divider unsigned divisor
//               Write to the DIVISOR operand of the divider, i.e. the q in `p /
//               q`.
//               Any operand write starts a new calculation. The results appear
//               in QUOTIENT, REMAINDER.
//               UDIVISOR/SDIVISOR are aliases of the same internal register.
//               The U alias starts an
//               unsigned calculation, and the S alias starts a signed
//               calculation.






// =============================================================================
// Register    : SIO_DIV_SDIVIDEND
// Description : Divider signed dividend
//               The same as UDIVIDEND, but starts a signed calculation, rather
//               than unsigned.






// =============================================================================
// Register    : SIO_DIV_SDIVISOR
// Description : Divider signed divisor
//               The same as UDIVISOR, but starts a signed calculation, rather
//               than unsigned.






// =============================================================================
// Register    : SIO_DIV_QUOTIENT
// Description : Divider result quotient
//               The result of `DIVIDEND / DIVISOR` (division). Contents
//               undefined while CSR_READY is low.
//               For signed calculations, QUOTIENT is negative when the signs of
//               DIVIDEND and DIVISOR differ.
//               This register can be written to directly, for context
//               save/restore purposes. This halts any
//               in-progress calculation and sets the CSR_READY and CSR_DIRTY
//               flags.
//               Reading from QUOTIENT clears the CSR_DIRTY flag, so should read
//               results in the order
//               REMAINDER, QUOTIENT if CSR_DIRTY is used.






// =============================================================================
// Register    : SIO_DIV_REMAINDER
// Description : Divider result remainder
//               The result of `DIVIDEND % DIVISOR` (modulo). Contents undefined
//               while CSR_READY is low.
//               For signed calculations, REMAINDER is negative only when
//               DIVIDEND is negative.
//               This register can be written to directly, for context
//               save/restore purposes. This halts any
//               in-progress calculation and sets the CSR_READY and CSR_DIRTY
//               flags.






// =============================================================================
// Register    : SIO_DIV_CSR
// Description : Control and status register for divider.



// -----------------------------------------------------------------------------
// Field       : SIO_DIV_CSR_DIRTY
// Description : Changes to 1 when any register is written, and back to 0 when
//               QUOTIENT is read.
//               Software can use this flag to make save/restore more efficient
//               (skip if not DIRTY).
//               If the flag is used in this way, it's recommended to either
//               read QUOTIENT only,
//               or REMAINDER and then QUOTIENT, to prevent data loss on context
//               switch.





// -----------------------------------------------------------------------------
// Field       : SIO_DIV_CSR_READY
// Description : Reads as 0 when a calculation is in progress, 1 otherwise.
//               Writing an operand (xDIVIDEND, xDIVISOR) will immediately start
//               a new calculation, no
//               matter if one is already in progress.
//               Writing to a result register will immediately terminate any
//               in-progress calculation
//               and set the READY and DIRTY flags.





// =============================================================================
// Register    : SIO_INTERP0_ACCUM0
// Description : Read/write access to accumulator 0






// =============================================================================
// Register    : SIO_INTERP0_ACCUM1
// Description : Read/write access to accumulator 1






// =============================================================================
// Register    : SIO_INTERP0_BASE0
// Description : Read/write access to BASE0 register.






// =============================================================================
// Register    : SIO_INTERP0_BASE1
// Description : Read/write access to BASE1 register.






// =============================================================================
// Register    : SIO_INTERP0_BASE2
// Description : Read/write access to BASE2 register.






// =============================================================================
// Register    : SIO_INTERP0_POP_LANE0
// Description : Read LANE0 result, and simultaneously write lane results to
//               both accumulators (POP).






// =============================================================================
// Register    : SIO_INTERP0_POP_LANE1
// Description : Read LANE1 result, and simultaneously write lane results to
//               both accumulators (POP).






// =============================================================================
// Register    : SIO_INTERP0_POP_FULL
// Description : Read FULL result, and simultaneously write lane results to both
//               accumulators (POP).






// =============================================================================
// Register    : SIO_INTERP0_PEEK_LANE0
// Description : Read LANE0 result, without altering any internal state (PEEK).






// =============================================================================
// Register    : SIO_INTERP0_PEEK_LANE1
// Description : Read LANE1 result, without altering any internal state (PEEK).






// =============================================================================
// Register    : SIO_INTERP0_PEEK_FULL
// Description : Read FULL result, without altering any internal state (PEEK).






// =============================================================================
// Register    : SIO_INTERP0_CTRL_LANE0
// Description : Control register for lane 0



// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_OVERF
// Description : Set if either OVERF0 or OVERF1 is set.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_OVERF1
// Description : Indicates if any masked-off MSBs in ACCUM1 are set.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_OVERF0
// Description : Indicates if any masked-off MSBs in ACCUM0 are set.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_BLEND
// Description : Only present on INTERP0 on each core. If BLEND mode is enabled:
//               - LANE1 result is a linear interpolation between BASE0 and
//               BASE1, controlled
//               by the 8 LSBs of lane 1 shift and mask value (a fractional
//               number between
//               0 and 255/256ths)
//               - LANE0 result does not have BASE0 added (yields only the 8
//               LSBs of lane 1 shift+mask value)
//               - FULL result does not have lane 1 shift+mask value added
//               (BASE2 + lane 0 shift+mask)
//               LANE1 SIGNED flag controls whether the interpolation is signed
//               or unsigned.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_FORCE_MSB
// Description : ORed into bits 29:28 of the lane result presented to the
//               processor on the bus.
//               No effect on the internal 32-bit datapath. Handy for using a
//               lane to generate sequence
//               of pointers into flash or SRAM.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_ADD_RAW
// Description : If 1, mask + shift is bypassed for LANE0 result. This does not
//               affect FULL result.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_CROSS_RESULT
// Description : If 1, feed the opposite lane's result into this lane's
//               accumulator on POP.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_CROSS_INPUT
// Description : If 1, feed the opposite lane's accumulator into this lane's
//               shift + mask hardware.
//               Takes effect even if ADD_RAW is set (the CROSS_INPUT mux is
//               before the shift+mask bypass)





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_SIGNED
// Description : If SIGNED is set, the shifted and masked accumulator value is
//               sign-extended to 32 bits
//               before adding to BASE0, and LANE0 PEEK/POP appear extended to
//               32 bits when read by processor.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_MASK_MSB
// Description : The most-significant bit allowed to pass by the mask
//               (inclusive)
//               Setting MSB < LSB may cause chip to turn inside-out





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_MASK_LSB
// Description : The least-significant bit allowed to pass by the mask
//               (inclusive)





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE0_SHIFT
// Description : Logical right-shift applied to accumulator before masking





// =============================================================================
// Register    : SIO_INTERP0_CTRL_LANE1
// Description : Control register for lane 1



// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE1_FORCE_MSB
// Description : ORed into bits 29:28 of the lane result presented to the
//               processor on the bus.
//               No effect on the internal 32-bit datapath. Handy for using a
//               lane to generate sequence
//               of pointers into flash or SRAM.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE1_ADD_RAW
// Description : If 1, mask + shift is bypassed for LANE1 result. This does not
//               affect FULL result.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE1_CROSS_RESULT
// Description : If 1, feed the opposite lane's result into this lane's
//               accumulator on POP.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE1_CROSS_INPUT
// Description : If 1, feed the opposite lane's accumulator into this lane's
//               shift + mask hardware.
//               Takes effect even if ADD_RAW is set (the CROSS_INPUT mux is
//               before the shift+mask bypass)





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE1_SIGNED
// Description : If SIGNED is set, the shifted and masked accumulator value is
//               sign-extended to 32 bits
//               before adding to BASE1, and LANE1 PEEK/POP appear extended to
//               32 bits when read by processor.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE1_MASK_MSB
// Description : The most-significant bit allowed to pass by the mask
//               (inclusive)
//               Setting MSB < LSB may cause chip to turn inside-out





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE1_MASK_LSB
// Description : The least-significant bit allowed to pass by the mask
//               (inclusive)





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP0_CTRL_LANE1_SHIFT
// Description : Logical right-shift applied to accumulator before masking





// =============================================================================
// Register    : SIO_INTERP0_ACCUM0_ADD
// Description : Values written here are atomically added to ACCUM0
//               Reading yields lane 0's raw shift and mask value (BASE0 not
//               added).






// =============================================================================
// Register    : SIO_INTERP0_ACCUM1_ADD
// Description : Values written here are atomically added to ACCUM1
//               Reading yields lane 1's raw shift and mask value (BASE1 not
//               added).






// =============================================================================
// Register    : SIO_INTERP0_BASE_1AND0
// Description : On write, the lower 16 bits go to BASE0, upper bits to BASE1
//               simultaneously.
//               Each half is sign-extended to 32 bits if that lane's SIGNED
//               flag is set.






// =============================================================================
// Register    : SIO_INTERP1_ACCUM0
// Description : Read/write access to accumulator 0






// =============================================================================
// Register    : SIO_INTERP1_ACCUM1
// Description : Read/write access to accumulator 1






// =============================================================================
// Register    : SIO_INTERP1_BASE0
// Description : Read/write access to BASE0 register.






// =============================================================================
// Register    : SIO_INTERP1_BASE1
// Description : Read/write access to BASE1 register.






// =============================================================================
// Register    : SIO_INTERP1_BASE2
// Description : Read/write access to BASE2 register.






// =============================================================================
// Register    : SIO_INTERP1_POP_LANE0
// Description : Read LANE0 result, and simultaneously write lane results to
//               both accumulators (POP).






// =============================================================================
// Register    : SIO_INTERP1_POP_LANE1
// Description : Read LANE1 result, and simultaneously write lane results to
//               both accumulators (POP).






// =============================================================================
// Register    : SIO_INTERP1_POP_FULL
// Description : Read FULL result, and simultaneously write lane results to both
//               accumulators (POP).






// =============================================================================
// Register    : SIO_INTERP1_PEEK_LANE0
// Description : Read LANE0 result, without altering any internal state (PEEK).






// =============================================================================
// Register    : SIO_INTERP1_PEEK_LANE1
// Description : Read LANE1 result, without altering any internal state (PEEK).






// =============================================================================
// Register    : SIO_INTERP1_PEEK_FULL
// Description : Read FULL result, without altering any internal state (PEEK).






// =============================================================================
// Register    : SIO_INTERP1_CTRL_LANE0
// Description : Control register for lane 0



// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_OVERF
// Description : Set if either OVERF0 or OVERF1 is set.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_OVERF1
// Description : Indicates if any masked-off MSBs in ACCUM1 are set.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_OVERF0
// Description : Indicates if any masked-off MSBs in ACCUM0 are set.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_CLAMP
// Description : Only present on INTERP1 on each core. If CLAMP mode is enabled:
//               - LANE0 result is shifted and masked ACCUM0, clamped by a lower
//               bound of
//               BASE0 and an upper bound of BASE1.
//               - Signedness of these comparisons is determined by
//               LANE0_CTRL_SIGNED





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_FORCE_MSB
// Description : ORed into bits 29:28 of the lane result presented to the
//               processor on the bus.
//               No effect on the internal 32-bit datapath. Handy for using a
//               lane to generate sequence
//               of pointers into flash or SRAM.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_ADD_RAW
// Description : If 1, mask + shift is bypassed for LANE0 result. This does not
//               affect FULL result.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_CROSS_RESULT
// Description : If 1, feed the opposite lane's result into this lane's
//               accumulator on POP.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_CROSS_INPUT
// Description : If 1, feed the opposite lane's accumulator into this lane's
//               shift + mask hardware.
//               Takes effect even if ADD_RAW is set (the CROSS_INPUT mux is
//               before the shift+mask bypass)





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_SIGNED
// Description : If SIGNED is set, the shifted and masked accumulator value is
//               sign-extended to 32 bits
//               before adding to BASE0, and LANE0 PEEK/POP appear extended to
//               32 bits when read by processor.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_MASK_MSB
// Description : The most-significant bit allowed to pass by the mask
//               (inclusive)
//               Setting MSB < LSB may cause chip to turn inside-out





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_MASK_LSB
// Description : The least-significant bit allowed to pass by the mask
//               (inclusive)





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE0_SHIFT
// Description : Logical right-shift applied to accumulator before masking





// =============================================================================
// Register    : SIO_INTERP1_CTRL_LANE1
// Description : Control register for lane 1



// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE1_FORCE_MSB
// Description : ORed into bits 29:28 of the lane result presented to the
//               processor on the bus.
//               No effect on the internal 32-bit datapath. Handy for using a
//               lane to generate sequence
//               of pointers into flash or SRAM.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE1_ADD_RAW
// Description : If 1, mask + shift is bypassed for LANE1 result. This does not
//               affect FULL result.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE1_CROSS_RESULT
// Description : If 1, feed the opposite lane's result into this lane's
//               accumulator on POP.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE1_CROSS_INPUT
// Description : If 1, feed the opposite lane's accumulator into this lane's
//               shift + mask hardware.
//               Takes effect even if ADD_RAW is set (the CROSS_INPUT mux is
//               before the shift+mask bypass)





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE1_SIGNED
// Description : If SIGNED is set, the shifted and masked accumulator value is
//               sign-extended to 32 bits
//               before adding to BASE1, and LANE1 PEEK/POP appear extended to
//               32 bits when read by processor.





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE1_MASK_MSB
// Description : The most-significant bit allowed to pass by the mask
//               (inclusive)
//               Setting MSB < LSB may cause chip to turn inside-out





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE1_MASK_LSB
// Description : The least-significant bit allowed to pass by the mask
//               (inclusive)





// -----------------------------------------------------------------------------
// Field       : SIO_INTERP1_CTRL_LANE1_SHIFT
// Description : Logical right-shift applied to accumulator before masking





// =============================================================================
// Register    : SIO_INTERP1_ACCUM0_ADD
// Description : Values written here are atomically added to ACCUM0
//               Reading yields lane 0's raw shift and mask value (BASE0 not
//               added).






// =============================================================================
// Register    : SIO_INTERP1_ACCUM1_ADD
// Description : Values written here are atomically added to ACCUM1
//               Reading yields lane 1's raw shift and mask value (BASE1 not
//               added).






// =============================================================================
// Register    : SIO_INTERP1_BASE_1AND0
// Description : On write, the lower 16 bits go to BASE0, upper bits to BASE1
//               simultaneously.
//               Each half is sign-extended to 32 bits if that lane's SIGNED
//               flag is set.






// =============================================================================
// Register    : SIO_SPINLOCK0
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK1
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK2
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK3
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK4
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK5
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK6
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK7
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK8
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK9
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK10
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK11
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK12
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK13
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK14
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK15
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK16
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK17
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK18
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK19
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK20
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK21
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK22
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK23
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK24
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK25
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK26
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK27
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK28
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK29
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK30
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// Register    : SIO_SPINLOCK31
// Description : Reading from a spinlock address will:
//               - Return 0 if lock is already locked
//               - Otherwise return nonzero, and simultaneously claim the lock
//
//               Writing (any value) releases the lock.
//               If core 0 and core 1 attempt to claim the same lock
//               simultaneously, core 0 wins.
//               The value returned on success is 0x1 << lock number.






// =============================================================================
// # 22 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/pico_platform/include/pico/platform.h" 2

// Marker for builds targeting the RP2040


// PICO_CONFIG: PICO_STACK_SIZE, Stack Size, min=0x100, default=0x800, advanced=true, group=pico_platform




// PICO_CONFIG: PICO_HEAP_SIZE, Heap size to reserve, min=0x100, default=0x800, advanced=true, group=pico_platform




// PICO_CONFIG: PICO_NO_RAM_VECTOR_TABLE, Enable/disable the RAM vector table, type=bool, default=0, advanced=true, group=pico_platform




// PICO_CONFIG: PICO_RP2040_B0_SUPPORTED, Whether to include any specific software support for RP2040 B0 revision, type=bool, default=1, advanced=true, group=pico_platform




// PICO_CONFIG: PICO_FLOAT_SUPPORT_ROM_V1, Include float support code for RP2040 B0 when that chip revision is supported , type=bool, default=1, advanced=true, group=pico_platform




// PICO_CONFIG: PICO_DOUBLE_SUPPORT_ROM_V1, Include double support code for RP2040 B0 when that chip revision is supported , type=bool, default=1, advanced=true, group=pico_platform





// PICO_CONFIG: PICO_RP2040_B1_SUPPORTED, Whether to include any specific software support for RP2040 B1 revision, type=bool, default=1, advanced=true, group=pico_platform




// PICO_CONFIG: PICO_RP2040_B2_SUPPORTED, Whether to include any specific software support for RP2040 B2 revision, type=bool, default=1, advanced=true, group=pico_platform




// --- remainder of file is not included by assembly code ---
// # 78 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/pico_platform/include/pico/platform.h"
/*! \brief Marker for an interrupt handler
 *  \ingroup pico_platform
 * For example an IRQ handler function called my_interrupt_handler:
 *
 *     void __isr my_interrupt_handler(void) {
 */


/*! \brief Section attribute macro for placement in RAM after the `.data` section
 *  \ingroup pico_platform
 *
 * For example a 400 element `uint32_t` array placed after the .data section
 *
 *     uint32_t __after_data("my_group_name") a_big_array[400];
 *
 * The section attribute is `.after_data.<group>`
 *
 * \param group a string suffix to use in the section name to distinguish groups that can be linker
 *              garbage-collected independently
 */


/*! \brief Section attribute macro for placement not in flash (i.e in RAM)
 *  \ingroup pico_platform
 *
 * For example a 3 element `uint32_t` array placed in RAM (even though it is `static const`)
 *
 *     static const uint32_t __not_in_flash("my_group_name") an_array[3];
 *
 * The section attribute is `.time_critical.<group>`
 *
 * \param group a string suffix to use in the section name to distinguish groups that can be linker
 *              garbage-collected independently
 */


/*! \brief Section attribute macro for placement in the SRAM bank 4 (known as "scratch X")
 *  \ingroup pico_platform
 *
 * Scratch X is commonly used for critical data and functions accessed only by one core (when only
 * one core is accessing the RAM bank, there is no opportunity for stalls)
 *
 * For example a `uint32_t` variable placed in "scratch X"
 *
 *     uint32_t __scratch_x("my_group_name") foo = 23;
 *
 * The section attribute is `.scratch_x.<group>`
 *
 * \param group a string suffix to use in the section name to distinguish groups that can be linker
 *              garbage-collected independently
 */


/*! \brief Section attribute macro for placement in the SRAM bank 5 (known as "scratch Y")
 *  \ingroup pico_platform
 *
 * Scratch Y is commonly used for critical data and functions accessed only by one core (when only
 * one core is accessing the RAM bank, there is no opportunity for stalls)
 *
 * For example a `uint32_t` variable placed in "scratch Y"
 *
 *     uint32_t __scratch_y("my_group_name") foo = 23;
 *
 * The section attribute is `.scratch_y.<group>`
 *
 * \param group a string suffix to use in the section name to distinguish groups that can be linker
 *              garbage-collected independently
 */


/*! \brief Section attribute macro for data that is to be left uninitialized
 *  \ingroup pico_platform
 *
 * Data marked this way will retain its value across a reset (normally uninitialized data - in the .bss
 * section) is initialized to zero during runtime initialization
 *
 * For example a `uint32_t` foo that will retain its value if the program is restarted by reset.
 *
 *     uint32_t __uninitialized_ram("my_group_name") foo;
 *
 * The section attribute is `.uninitialized_ram.<group>`
 *
 * \param group a string suffix to use in the section name to distinguish groups that can be linker
 *              garbage-collected independently
 */


/*! \brief Section attribute macro for placement in flash even in a COPY_TO_RAM binary
 *  \ingroup pico_platform
 *
 * For example a `uint32_t` variable explicitly placed in flash (it will hard fault if you attempt to write it!)
 *
 *     uint32_t __in_flash("my_group_name") foo = 23;
 *
 * The section attribute is `.flashdata.<group>`
 *
 * \param group a string suffix to use in the section name to distinguish groups that can be linker
 *              garbage-collected independently
 */


/*! \brief Indicates a function should not be stored in flash
 *  \ingroup pico_platform
 *
 * Decorates a function name, such that the function will execute from RAM (assuming it is not inlined
 * into a flash function by the compiler)
 *
 * For example a function called my_func taking an int parameter:
 *
 *     void __not_in_flash_func(my_func)(int some_arg) {
 *
 * The function is placed in the `.time_critical.<func_name>` linker section
 *
 * \see __no_inline_not_in_flash_func
 */


/*! \brief Indicates a function is time/latency critical and should not run from flash
 *  \ingroup pico_platform
 *
 * Decorates a function name, such that the function will execute from RAM (assuming it is not inlined
 * into a flash function by the compiler) to avoid possible flash latency. Currently this macro is identical
 * in implementation to `__not_in_flash_func`, however the semantics are distinct and a `__time_critical_func`
 * may in the future be treated more specially to reduce the overhead when calling such function from a flash
 * function.
 *
 * For example a function called my_func taking an int parameter:
 *
 *     void __time_critical(my_func)(int some_arg) {
 *
 * The function is placed in the `.time_critical.<func_name>` linker section
 *
 * \see __not_in_flash_func
 */


/*! \brief Indicate a function should not be stored in flash and should not be inlined
 *  \ingroup pico_platform
 *
 * Decorates a function name, such that the function will execute from RAM, explicitly marking it as
 * noinline to prevent it being inlined into a flash function by the compiler
 *
 * For example a function called my_func taking an int parameter:
 *
 *     void __no_inline_not_in_flash_func(my_func)(int some_arg) {
 *
 * The function is placed in the `.time_critical.<func_name>` linker section
 */





    /* Reason for rewrite:
     * Verifast cannot parse ths define for and unknown reason.
     *
     * VF-TODO: What causes the parse error?
     */
// # 253 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/pico_platform/include/pico/platform.h"
/*! \brief Macro to determine the number of elements in an array
 *  \ingroup pico_platform
 */




/*! \brief Macro to return the maximum of two comparable values
 *  \ingroup pico_platform
 */




/*! \brief Macro to return the minimum of two comparable values
 *  \ingroup pico_platform
 */




/*! \brief Execute a breakpoint instruction
 *  \ingroup pico_platform
 */
static void __breakpoint(void) {
    __asm__("bkpt #0");
}

/*! \brief Ensure that the compiler does not move memory access across this method call
 *  \ingroup pico_platform
 *
 *  For example in the following code:
 *
 *      *some_memory_location = var_a;
 *      __compiler_memory_barrier();
 *      uint32_t var_b = *some_other_memory_location
 *
 * The compiler will not move the load from `some_other_memory_location` above the memory barrier (which it otherwise
 * might - even above the memory store!)
 */

    /* Reason for rewrite: VeriFast cannot parse:
     * - `__force_inline`
     * - the function body
     */
    static void __compiler_memory_barrier(void);







/*! \brief Macro for converting memory addresses to 32 bit addresses suitable for DMA
 *  \ingroup pico_platform
 *
 *  This is just a cast to `uintptr_t` on the RP2040, however you may want to use this when developing code
 *  that also runs in "host" mode. If the host mode is 64 bit and you are embedding data pointers
 *  in other data (e.g. DMA chaining), then there is a need in "host" mode to convert a 64 bit native
 *  pointer to a 32 bit value for storage, which can be done using this macro.
 */




/*! \brief Panics with the message "Unsupported"
 *  \ingroup pico_platform
 *  \see panic
 */

    /* Reason for rewrite: VeriFast cannot parse ``. */
    void panic_unsupported(void);




/*! \brief Displays a panic message and halts execution
 *  \ingroup pico_platform
 *
 * An attempt is made to output the message to all registered STDOUT drivers
 * after which this method executes a BKPT instruction.
 *
 * @param fmt format string (printf-like)
 * @param ...  printf-like arguments
 */

    /* Reason for rewrite: VeriFast cannot parse ``. */
    void panic(const char *fmt, ...);




// PICO_CONFIG: PICO_NO_FPGA_CHECK, Remove the FPGA platform check for small code size reduction, type=bool, default=0, advanced=true, group=pico_runtime







bool running_on_fpga(void);


/*! \brief Returns the RP2040 chip revision number
 *  \ingroup pico_platform
 * @return the RP2040 chip revision number (1 for B0/B1, 2 for B2)
 */
uint8_t rp2040_chip_version(void);

/*! \brief Returns the RP2040 rom version number
 *  \ingroup pico_platform
 * @return the RP2040 rom version number (1 for RP2040-B0, 2 for RP2040-B1, 3 for RP2040-B2)
 */
static uint8_t rp2040_rom_version(void) {

        /* Reason for rewrite: VeriFast cannot parse GCC pragmas */
            return *(uint8_t*)0x13;






}

/*! \brief No-op function for the body of tight loops
 *  \ingroup pico_platform
 *
 * No-op function intended to be called by any tight hardware polling loop. Using this ubiquitously
 * makes it much easier to find tight loops, but also in the future \#ifdef-ed support for lockup
 * debugging might be added
 */

    /* Reason for rewrite: VeriFast cannot parse `__force_inline`. */
    static void tight_loop_contents(void) {}





/*! \brief Multiply two integers using an assembly `MUL` instruction
 *  \ingroup pico_platform
 *
 * This multiplies a by b using multiply instruction using the ARM mul instruction regardless of values (the compiler
 * might otherwise choose to perform shifts/adds), i.e. this is a 1 cycle operation.
 *
 * \param a the first operand
 * \param b the second operand
 * \return a * b
 */

    /* Reason for rewrite: VeriFast cannot parse:
     * - `__force_inline`
     * - function body
     */
    static int32_t __mul_instruction(int32_t a, int32_t b);







/*! \brief multiply two integer values using the fastest method possible
 *  \ingroup pico_platform
 *
 * Efficiently multiplies value a by possibly constant value b.
 *
 * If b is known to be constant and not zero or a power of 2, then a mul instruction is used rather than gcc's default
 * which is often a slow combination of shifts and adds. If b is a power of 2 then a single shift is of course preferable
 * and will be used
 *
 * \param a the first operand
 * \param b the second operand
 * \return a * b
 */




/*! \brief Utility macro to assert two types are equivalent.
 *  \ingroup pico_platform
 *
 *  This macro can be useful in other macros along with `typeof` to assert that two parameters are of equivalent type
 *  (or that a single parameter is of an expected type)
 */


/*! \brief Get the current exception level on this core
 *  \ingroup pico_platform
 *
 * \return the exception number if the CPU is handling an exception, or 0 otherwise
 */
uint __get_current_exception(void);
// # 455 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/pico_platform/include/pico/platform.h"
/*! \brief Helper method to busy-wait for at least the given number of cycles
 *  \ingroup pico_platform
 *
 * This method is useful for introducing very short delays.
 *
 * This method busy-waits in a tight loop for the given number of system clock cycles. The total wait time is only accurate to within 2 cycles,
 * and this method uses a loop counter rather than a hardware timer, so the method will always take longer than expected if an
 * interrupt is handled on the calling core during the busy-wait; you can of course disable interrupts to prevent this.
 *
 * You can use \ref clock_get_hz(clk_sys) to determine the number of clock cycles per second if you want to convert an actual
 * time duration to a number of cycles.
 *
 * \param minimum_cycles the minimum number of system clock cycles to delay for
 */

    /* Reason for rewrite: VeriFast cannot parse function body. */
    static void busy_wait_at_least_cycles(uint32_t minimum_cycles);
// # 483 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/pico_platform/include/pico/platform.h"
/*! \brief Get the current core number
 *  \ingroup pico_platform
 *
 * \return The core number the call was made from
 */

    /* Reason for rewrite: VeriFast cannot parse `__force_inline`. */
    static uint get_core_num(void)



{
    return (*(uint32_t *) (0xd0000000u + 0x00000000u));
}
// # 32 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico.h" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico/error.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */






/*!
 * \brief Common return codes from pico_sdk methods that return a status
 * \ingroup pico_base
 */

    /* Reason for rewrite: 
     * VeriFast's parser does not expect a colon after 
     * an enum's last element.
     */
    enum pico_error_codes {
        PICO_OK = 0,
        PICO_ERROR_NONE = 0,
        PICO_ERROR_TIMEOUT = -1,
        PICO_ERROR_GENERIC = -2,
        PICO_ERROR_NO_DATA = -3,
        PICO_ERROR_NOT_PERMITTED = -4,
        PICO_ERROR_INVALID_ARG = -5,
        PICO_ERROR_IO = -6
    };
// # 33 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/common/pico_base/include/pico.h" 2
// # 38 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/hardware_sync/include/hardware/sync.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */





// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/hardware_base/include/hardware/address_mapped.h" 1
/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */







/** \file address_mapped.h
 *  \defgroup hardware_base hardware_base
 *
 *  Low-level types and (atomic) accessors for memory-mapped hardware registers
 *
 *  `hardware_base` defines the low level types and access functions for memory mapped hardware registers. It is included
 *  by default by all other hardware libraries.
 *
 *  The following register access typedefs codify the access type (read/write) and the bus size (8/16/32) of the hardware register.
 *  The register type names are formed by concatenating one from each of the 3 parts A, B, C

 *   A    | B | C | Meaning
 *  ------|---|---|--------
 *  io_   |   |   | A Memory mapped IO register
 *  &nbsp;|ro_|   | read-only access
 *  &nbsp;|rw_|   | read-write access
 *  &nbsp;|wo_|   | write-only access (can't actually be enforced via C API)
 *  &nbsp;|   |  8| 8-bit wide access
 *  &nbsp;|   | 16| 16-bit wide access
 *  &nbsp;|   | 32| 32-bit wide access
 *
 *  When dealing with these types, you will always use a pointer, i.e. `io_rw_32 *some_reg` is a pointer to a read/write
 *  32 bit register that you can write with `*some_reg = value`, or read with `value = *some_reg`.
 *
 *  RP2040 hardware is also aliased to provide atomic setting, clear or flipping of a subset of the bits within
 *  a hardware register so that concurrent access by two cores is always consistent with one atomic operation
 *  being performed first, followed by the second.
 *
 *  See hw_set_bits(), hw_clear_bits() and hw_xor_bits() provide for atomic access via a pointer to a 32 bit register
 *
 *  Additionally given a pointer to a structure representing a piece of hardware (e.g. `dma_hw_t *dma_hw` for the DMA controller), you can
 *  get an alias to the entire structure such that writing any member (register) within the structure is equivalent
 *  to an atomic operation via hw_set_alias(), hw_clear_alias() or hw_xor_alias()...
 *
 *  For example `hw_set_alias(dma_hw)->inte1 = 0x80;` will set bit 7 of the INTE1 register of the DMA controller,
 *  leaving the other bits unchanged.
 */
// # 58 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/hardware_base/include/hardware/address_mapped.h"
// PICO_CONFIG: PARAM_ASSERTIONS_ENABLED_ADDRESS_ALIAS, Enable/disable assertions in memory address aliasing macros, type=bool, default=0, group=hardware_base




typedef volatile uint32_t io_rw_32;
typedef const volatile uint32_t io_ro_32;
typedef volatile uint32_t io_wo_32;
typedef volatile uint16_t io_rw_16;
typedef const volatile uint16_t io_ro_16;
typedef volatile uint16_t io_wo_16;
typedef volatile uint8_t io_rw_8;
typedef const volatile uint8_t io_ro_8;
typedef volatile uint8_t io_wo_8;

typedef volatile uint8_t *const ioptr;
typedef ioptr const const_ioptr;

// A non-functional (empty) helper macro to help IDEs follow links from the autogenerated
// hardware struct headers in hardware/structs/xxx.h to the raw register definitions
// in hardware/regs/xxx.h. A preprocessor define such as TIMER_TIMEHW_OFFSET (a timer register offset)
// is not generally clickable (in an IDE) if placed in a C comment, so _REG_(TIMER_TIMEHW_OFFSET) is
// included outside of a comment instead


// Helper method used by hw_alias macros to optionally check input validity

// can't use the following impl as it breaks existing static declarations using hw_alias, so would be a backwards incompatibility
//static __force_inline uint32_t hw_alias_check_addr(volatile void *addr) {
//    uint32_t rc = (uintptr_t)addr;
//    invalid_params_if(ADDRESS_ALIAS, rc < 0x40000000); // catch likely non HW pointer types
//    return rc;
//}

// Helper method used by xip_alias macros to optionally check input validity
static uint32_t xip_alias_check_addr(const void *addr) {
    uint32_t rc = (uintptr_t)addr;
    {if (((0 || 0) && !0)) (__builtin_expect(!(rc >= 0x10000000u && rc < 0x11000000u), 0) ? __assert_rtn ((const char *)-1L, "address_mapped.h", 95, "rc >= 0x10000000u && rc < 0x11000000u") : (void)0);};
    return rc;
}

// Untyped conversion alias pointer generation macros







// Typed conversion alias pointer generation macros







/*! \brief Atomically set the specified bits to 1 in a HW register
 *  \ingroup hardware_base
 *
 * \param addr Address of writable register
 * \param mask Bit-mask specifying bits to set
 */
               static void hw_set_bits(io_rw_32 *addr, uint32_t mask) {
    *(io_rw_32 *) ((void *)((0x2u << 12u) | ((uintptr_t)((volatile void *) addr)))) = mask;
}

/*! \brief Atomically clear the specified bits to 0 in a HW register
 *  \ingroup hardware_base
 *
 * \param addr Address of writable register
 * \param mask Bit-mask specifying bits to clear
 */
               static void hw_clear_bits(io_rw_32 *addr, uint32_t mask) {
    *(io_rw_32 *) ((void *)((0x3u << 12u) | ((uintptr_t)((volatile void *) addr)))) = mask;
}

/*! \brief Atomically flip the specified bits in a HW register
 *  \ingroup hardware_base
 *
 * \param addr Address of writable register
 * \param mask Bit-mask specifying bits to invert
 */
               static void hw_xor_bits(io_rw_32 *addr, uint32_t mask) {
    *(io_rw_32 *) ((void *)((0x1u << 12u) | ((uintptr_t)((volatile void *) addr)))) = mask;
}

/*! \brief Set new values for a sub-set of the bits in a HW register
 *  \ingroup hardware_base
 *
 * Sets destination bits to values specified in \p values, if and only if corresponding bit in \p write_mask is set
 *
 * Note: this method allows safe concurrent modification of *different* bits of
 * a register, but multiple concurrent access to the same bits is still unsafe.
 *
 * \param addr Address of writable register
 * \param values Bits values
 * \param write_mask Mask of bits to change
 */
               static void hw_write_masked(io_rw_32 *addr, uint32_t values, uint32_t write_mask) {
    hw_xor_bits(addr, (*addr ^ values) & write_mask);
}
// # 12 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/hardware_sync/include/hardware/sync.h" 2






/** \file hardware/sync.h
 *  \defgroup hardware_sync hardware_sync
 *
 * Low level hardware spin locks, barrier and processor event APIs
 *
 * Spin Locks
 * ----------
 *
 * The RP2040 provides 32 hardware spin locks, which can be used to manage mutually-exclusive access to shared software
 * and hardware resources.
 *
 * Generally each spin lock itself is a shared resource,
 * i.e. the same hardware spin lock can be used by multiple higher level primitives (as long as the spin locks are neither held for long periods, nor
 * held concurrently with other spin locks by the same core - which could lead to deadlock). A hardware spin lock that is exclusively owned can be used
 * individually without more flexibility and without regard to other software. Note that no hardware spin lock may
 * be acquired re-entrantly (i.e. hardware spin locks are not on their own safe for use by both thread code and IRQs) however the default spinlock related
 * methods here (e.g. \ref spin_lock_blocking) always disable interrupts while the lock is held as use by IRQ handlers and user code is common/desirable,
 * and spin locks are only expected to be held for brief periods.
 *
 * The SDK uses the following default spin lock assignments, classifying which spin locks are reserved for exclusive/special purposes
 * vs those suitable for more general shared use:
 *
 * Number (ID) | Description
 * :---------: | -----------
 * 0-13        | Currently reserved for exclusive use by the SDK and other libraries. If you use these spin locks, you risk breaking SDK or other library functionality. Each reserved spin lock used individually has its own PICO_SPINLOCK_ID so you can search for those.
 * 14,15       | (\ref PICO_SPINLOCK_ID_OS1 and \ref PICO_SPINLOCK_ID_OS2). Currently reserved for exclusive use by an operating system (or other system level software) co-existing with the SDK.
 * 16-23       | (\ref PICO_SPINLOCK_ID_STRIPED_FIRST - \ref PICO_SPINLOCK_ID_STRIPED_LAST). Spin locks from this range are assigned in a round-robin fashion via \ref next_striped_spin_lock_num(). These spin locks are shared, but assigning numbers from a range reduces the probability that two higher level locking primitives using _striped_ spin locks will actually be using the same spin lock.
 * 24-31       | (\ref PICO_SPINLOCK_ID_CLAIM_FREE_FIRST - \ref PICO_SPINLOCK_ID_CLAIM_FREE_LAST). These are reserved for exclusive use and are allocated on a first come first served basis at runtime via \ref spin_lock_claim_unused()
 */

// PICO_CONFIG: PARAM_ASSERTIONS_ENABLED_SYNC, Enable/disable assertions in the HW sync module, type=bool, default=0, group=hardware_sync




/** \brief A spin lock identifier
 * \ingroup hardware_sync
 */
typedef volatile uint32_t spin_lock_t;

// PICO_CONFIG: PICO_SPINLOCK_ID_IRQ, Spinlock ID for IRQ protection, min=0, max=31, default=9, group=hardware_sync




// PICO_CONFIG: PICO_SPINLOCK_ID_TIMER, Spinlock ID for Timer protection, min=0, max=31, default=10, group=hardware_sync




// PICO_CONFIG: PICO_SPINLOCK_ID_HARDWARE_CLAIM, Spinlock ID for Hardware claim protection, min=0, max=31, default=11, group=hardware_sync




// PICO_CONFIG: PICO_SPINLOCK_ID_OS1, First Spinlock ID reserved for use by low level OS style software, min=0, max=31, default=14, group=hardware_sync




// PICO_CONFIG: PICO_SPINLOCK_ID_OS2, Second Spinlock ID reserved for use by low level OS style software, min=0, max=31, default=15, group=hardware_sync




// PICO_CONFIG: PICO_SPINLOCK_ID_STRIPED_FIRST, Lowest Spinlock ID in the 'striped' range, min=0, max=31, default=16, group=hardware_sync




// PICO_CONFIG: PICO_SPINLOCK_ID_STRIPED_LAST, Highest Spinlock ID in the 'striped' range, min=0, max=31, default=23, group=hardware_sync




// PICO_CONFIG: PICO_SPINLOCK_ID_CLAIM_FREE_FIRST, Lowest Spinlock ID in the 'claim free' range, min=0, max=31, default=24, group=hardware_sync








// PICO_CONFIG: PICO_SPINLOCK_ID_CLAIM_FREE_LAST, Highest Spinlock ID in the 'claim free' range, min=0, max=31, default=31, group=hardware_sync




/*! \brief Insert a SEV instruction in to the code path.
 *  \ingroup hardware_sync

 * The SEV (send event) instruction sends an event to both cores.
 */

    /* Reason for rewrite: VeriFast cannot handle inline assembler. */
                   static void __sev(void) ;






/*! \brief Insert a WFE instruction in to the code path.
 *  \ingroup hardware_sync
 *
 * The WFE (wait for event) instruction waits until one of a number of
 * events occurs, including events signalled by the SEV instruction on either core.
 */

    /* Reason for rewrite: VeriFast cannot handle inline assembler. */
                   static void __wfe(void) ;






/*! \brief Insert a WFI instruction in to the code path.
  *  \ingroup hardware_sync
*
 * The WFI (wait for interrupt) instruction waits for a interrupt to wake up the core.
 */

    /* Reason for rewrite: VeriFast cannot handle inline assembler. */
                   static void __wfi(void) ;






/*! \brief Insert a DMB instruction in to the code path.
 *  \ingroup hardware_sync
 *
 * The DMB (data memory barrier) acts as a memory barrier, all memory accesses prior to this
 * instruction will be observed before any explicit access after the instruction.
 */

    /* Reason for rewrite: VeriFast cannot handle inline assembler. */
                   static void __dmb(void) ;






/*! \brief Insert a DSB instruction in to the code path.
 *  \ingroup hardware_sync
 *
 * The DSB (data synchronization barrier) acts as a special kind of data
 * memory barrier (DMB). The DSB operation completes when all explicit memory
 * accesses before this instruction complete.
 */

    /* Reason for rewrite: VeriFast cannot handle inline assembler. */
                   static void __dsb(void) ;






/*! \brief Insert a ISB instruction in to the code path.
 *  \ingroup hardware_sync
 *
 * ISB acts as an instruction synchronization barrier. It flushes the pipeline of the processor,
 * so that all instructions following the ISB are fetched from cache or memory again, after
 * the ISB instruction has been completed.
 */

    /* Reason for rewrite: VeriFast cannot handle inline assembler. */
                   static void __isb(void) ;






/*! \brief Acquire a memory fence
 *  \ingroup hardware_sync
 */
               static void __mem_fence_acquire(void) {
    // the original code below makes it hard for us to be included from C++ via a header
    // which itself is in an extern "C", so just use __dmb instead, which is what
    // is required on Cortex M0+
    __dmb();
//#ifndef __cplusplus
//    atomic_thread_fence(memory_order_acquire);
//#else
//    std::atomic_thread_fence(std::memory_order_acquire);
//#endif
}

/*! \brief Release a memory fence
 *  \ingroup hardware_sync
 *
 */
               static void __mem_fence_release(void) {
    // the original code below makes it hard for us to be included from C++ via a header
    // which itself is in an extern "C", so just use __dmb instead, which is what
    // is required on Cortex M0+
    __dmb();
//#ifndef __cplusplus
//    atomic_thread_fence(memory_order_release);
//#else
//    std::atomic_thread_fence(std::memory_order_release);
//#endif
}

/*! \brief Save and disable interrupts
 *  \ingroup hardware_sync
 *
 * \return The prior interrupt enable status for restoration later via restore_interrupts()
 */

    /* Reason for rewrite: VeriFast cannot handle inline assembler. */
                   static uint32_t save_and_disable_interrupts(void);
// # 246 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/sdks/pico-sdk/src/rp2_common/hardware_sync/include/hardware/sync.h"
/*! \brief Restore interrupts to a specified state
 *  \ingroup hardware_sync
 *
 * \param status Previous interrupt status from save_and_disable_interrupts()
  */

    /* Reason for rewrite: VeriFast cannot handle inline assembler. */
                   static void restore_interrupts(uint32_t status) ;






/*! \brief Get HW Spinlock instance from number
 *  \ingroup hardware_sync
 *
 * \param lock_num Spinlock ID
 * \return The spinlock instance
 */
               static spin_lock_t *spin_lock_instance(uint lock_num) {
    {if (((0 || 0) && !0)) (__builtin_expect(!(!(lock_num >= 32u)), 0) ? __assert_rtn ((const char *)-1L, "sync.h", 267, "!(lock_num >= 32u)") : (void)0);};
    return (spin_lock_t *) (0xd0000000u + 0x00000100u + lock_num * 4);
}

/*! \brief Get HW Spinlock number from instance
 *  \ingroup hardware_sync
 *
 * \param lock The Spinlock instance
 * \return The Spinlock ID
 */
               static uint spin_lock_get_num(spin_lock_t *lock) {
    {if (((0 || 0) && !0)) (__builtin_expect(!(!((uint) lock < 0xd0000000u + 0x00000100u || (uint) lock >= 32u * sizeof(spin_lock_t) + 0xd0000000u + 0x00000100u || ((uint) lock - 0xd0000000u + 0x00000100u) % sizeof(spin_lock_t) != 0)), 0) ? __assert_rtn ((const char *)-1L, "sync.h", 280, "!((uint) lock < 0xd0000000u + 0x00000100u || (uint) lock >= 32u * sizeof(spin_lock_t) + 0xd0000000u + 0x00000100u || ((uint) lock - 0xd0000000u + 0x00000100u) % sizeof(spin_lock_t) != 0)") : (void)0);};


    return (uint) (lock - (spin_lock_t *) (0xd0000000u + 0x00000100u));
}

/*! \brief Acquire a spin lock without disabling interrupts (hence unsafe)
 *  \ingroup hardware_sync
 *
 * \param lock Spinlock instance
 */
               static void spin_lock_unsafe_blocking(spin_lock_t *lock) {
    // Note we don't do a wfe or anything, because by convention these spin_locks are VERY SHORT LIVED and NEVER BLOCK and run
    // with INTERRUPTS disabled (to ensure that)... therefore nothing on our core could be blocking us, so we just need to wait on another core
    // anyway which should be finished soon
    while (__builtin_expect(!*lock, 0));
    __mem_fence_acquire();
}

/*! \brief Release a spin lock without re-enabling interrupts
 *  \ingroup hardware_sync
 *
 * \param lock Spinlock instance
 */
               static void spin_unlock_unsafe(spin_lock_t *lock) {
    __mem_fence_release();
    *lock = 0;
}

/*! \brief Acquire a spin lock safely
 *  \ingroup hardware_sync
 *
 * This function will disable interrupts prior to acquiring the spinlock
 *
 * \param lock Spinlock instance
 * \return interrupt status to be used when unlocking, to restore to original state
 */
               static uint32_t spin_lock_blocking(spin_lock_t *lock) {
    uint32_t save = save_and_disable_interrupts();
    spin_lock_unsafe_blocking(lock);
    return save;
}

/*! \brief Check to see if a spinlock is currently acquired elsewhere.
 *  \ingroup hardware_sync
 *
 * \param lock Spinlock instance
 */

    /* Reason for rewrite: 
     * VeriFast's parser does not accept `inline` as first token in a function
     * declaration.
     */
    static bool is_spin_locked(spin_lock_t *lock)



{
    _Static_assert(sizeof(spin_lock_t) == (4), "hw size mismatch");
    uint lock_num = spin_lock_get_num(lock);
    return 0 != (*(io_ro_32 *) (0xd0000000u + 0x0000005cu) & (1u << lock_num));
}

/*! \brief Release a spin lock safely
 *  \ingroup hardware_sync
 *
 * This function will re-enable interrupts according to the parameters.
 *
 * \param lock Spinlock instance
 * \param saved_irq Return value from the \ref spin_lock_blocking() function.
 * \return interrupt status to be used when unlocking, to restore to original state
 *
 * \sa spin_lock_blocking()
 */
               static void spin_unlock(spin_lock_t *lock, uint32_t saved_irq) {
    spin_unlock_unsafe(lock);
    restore_interrupts(saved_irq);
}

/*! \brief Initialise a spin lock
 *  \ingroup hardware_sync
 *
 * The spin lock is initially unlocked
 *
 * \param lock_num The spin lock number
 * \return The spin lock instance
 */
spin_lock_t *spin_lock_init(uint lock_num);

/*! \brief Release all spin locks
 *  \ingroup hardware_sync
 */
void spin_locks_reset(void);

/*! \brief Return a spin lock number from the _striped_ range
 *  \ingroup hardware_sync
 *
 * Returns a spin lock number in the range PICO_SPINLOCK_ID_STRIPED_FIRST to PICO_SPINLOCK_ID_STRIPED_LAST
 * in a round robin fashion. This does not grant the caller exclusive access to the spin lock, so the caller
 * must:
 *
 * -# Abide (with other callers) by the contract of only holding this spin lock briefly (and with IRQs disabled - the default via \ref spin_lock_blocking()),
 * and not whilst holding other spin locks.
 * -# Be OK with any contention caused by the - brief due to the above requirement - contention with other possible users of the spin lock.
 *
 * \return lock_num a spin lock number the caller may use (non exclusively)
 * \see PICO_SPINLOCK_ID_STRIPED_FIRST
 * \see PICO_SPINLOCK_ID_STRIPED_LAST
 */
uint next_striped_spin_lock_num(void);

/*! \brief Mark a spin lock as used
 *  \ingroup hardware_sync
 *
 * Method for cooperative claiming of hardware. Will cause a panic if the spin lock
 * is already claimed. Use of this method by libraries detects accidental
 * configurations that would fail in unpredictable ways.
 *
 * \param lock_num the spin lock number
 */
void spin_lock_claim(uint lock_num);

/*! \brief Mark multiple spin locks as used
 *  \ingroup hardware_sync
 *
 * Method for cooperative claiming of hardware. Will cause a panic if any of the spin locks
 * are already claimed. Use of this method by libraries detects accidental
 * configurations that would fail in unpredictable ways.
 *
 * \param lock_num_mask Bitfield of all required spin locks to claim (bit 0 == spin lock 0, bit 1 == spin lock 1 etc)
 */
void spin_lock_claim_mask(uint32_t lock_num_mask);

/*! \brief Mark a spin lock as no longer used
 *  \ingroup hardware_sync
 *
 * Method for cooperative claiming of hardware.
 *
 * \param lock_num the spin lock number to release
 */
void spin_lock_unclaim(uint lock_num);

/*! \brief Claim a free spin lock
 *  \ingroup hardware_sync
 *
 * \param required if true the function will panic if none are available
 * \return the spin lock number or -1 if required was false, and none were free
 */
int spin_lock_claim_unused(bool required);

/*! \brief Determine if a spin lock is claimed
 *  \ingroup hardware_sync
 *
 * \param lock_num the spin lock number
 * \return true if claimed, false otherwise
 * \see spin_lock_claim
 * \see spin_lock_claim_mask
 */
bool spin_lock_is_claimed(uint lock_num);
// # 39 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h" 2

/*-----------------------------------------------------------
 * Port specific definitions.
 *
 * The settings in this file configure FreeRTOS correctly for the
 * given hardware and compiler.
 *
 * These settings should not be altered.
 *-----------------------------------------------------------
 */

/* Type definitions. */
// # 59 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h"
    typedef uint32_t StackType_t;
    typedef int32_t BaseType_t;
    typedef uint32_t UBaseType_t;





        typedef uint32_t TickType_t;


/* 32-bit tick type on a 32-bit architecture, so reads of the tick count do
 * not need to be guarded with a critical section. */


/*-----------------------------------------------------------*/

/* Architecture specifics. */




        /* Reason for rewrite: VeriFast does not support the attriibute `used`. 
         */




    /* We have to use PICO_DIVIDER_DISABLE_INTERRUPTS as the source of truth rathern than our config,
     * as our FreeRTOSConfig.h header cannot be included by ASM code - which is what this affects in the SDK */





/*-----------------------------------------------------------*/


/* Scheduler utilities. */
    extern void vPortYield( void );






/*-----------------------------------------------------------*/

/* Exception handlers */







/*-----------------------------------------------------------*/

/* Multi-core */






    /* Requires for SMP */


    /*-----------------------------------------------------------*/


    /* Check validity of number of cores specified in config */
// # 139 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h"
    /* FreeRTOS core id is always zero based, so always 0 if we're running on only one core */
// # 151 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h"
    void vYieldCore(int xCoreID);



/*-----------------------------------------------------------*/

/* Critical section management. */
// # 168 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h"
    extern void vPortEnableInterrupts();


    void vTaskEnterCritical(void);
    void vTaskExitCritical(void);





    /* Note this is a single method with uxAcquire parameter since we have
     * static vars, the method is always called with a compile time constant for
     * uxAcquire, and the compiler should dothe right thing! */

        /* Reason for rewrite: VeriFast does not support local static variables.
         */
// # 226 "/Users/reitobia/repos2/FreeRTOS-Kernel/portable/ThirdParty/GCC/RP2040/include/portmacro.h"
/*-----------------------------------------------------------*/

/* Tickless idle/low power functionality. */

        extern void vPortSuppressTicksAndSleep( TickType_t xExpectedIdleTime );


/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
// # 52 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h" 2
// # 94 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h"
/* *INDENT-OFF* */



/* *INDENT-ON* */

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/mpu_wrappers.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */




/* This file redefines API functions to be called through a wrapper macro, but
 * only for ports that are using the MPU. */
// # 101 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h" 2

/*
 * Setup the stack of a new task so it is ready to be placed under the
 * scheduler control.  The registers have to be placed on the stack in
 * the order that the port expects to find them.
 *
 */
// # 128 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h"
        StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                             TaskFunction_t pxCode,
                                             void * pvParameters ) ;
        ///@ requires true;
        ///@ ensures true;



/* Used by heap_5.c to define the start address and size of each memory region
 * that together comprise the total FreeRTOS heap space. */
typedef struct HeapRegion
{
    uint8_t * pucStartAddress;
    size_t xSizeInBytes;
} HeapRegion_t;

/* Used to pass information about the heap out of vPortGetHeapStats(). */
typedef struct xHeapStats
{
    size_t xAvailableHeapSpaceInBytes; /* The total heap size currently available - this is the sum of all the free blocks, not the largest block that can be allocated. */
    size_t xSizeOfLargestFreeBlockInBytes; /* The maximum size, in bytes, of all the free blocks within the heap at the time vPortGetHeapStats() is called. */
    size_t xSizeOfSmallestFreeBlockInBytes; /* The minimum size, in bytes, of all the free blocks within the heap at the time vPortGetHeapStats() is called. */
    size_t xNumberOfFreeBlocks; /* The number of free memory blocks within the heap at the time vPortGetHeapStats() is called. */
    size_t xMinimumEverFreeBytesRemaining; /* The minimum amount of total free memory (sum of all free blocks) there has been in the heap since the system booted. */
    size_t xNumberOfSuccessfulAllocations; /* The number of calls to pvPortMalloc() that have returned a valid memory block. */
    size_t xNumberOfSuccessfulFrees; /* The number of calls to vPortFree() that has successfully freed a block of memory. */
} HeapStats_t;

/*
 * Used to define multiple heap regions for use by heap_5.c.  This function
 * must be called before any calls to pvPortMalloc() - not creating a task,
 * queue, semaphore, mutex, software timer, event group, etc. will result in
 * pvPortMalloc being called.
 *
 * pxHeapRegions passes in an array of HeapRegion_t structures - each of which
 * defines a region of memory that can be used as the heap.  The array is
 * terminated by a HeapRegions_t structure that has a size of 0.  The region
 * with the lowest start address must appear first in the array.
 */
void vPortDefineHeapRegions( const HeapRegion_t * pxHeapRegions ) ;

/*
 * Returns a HeapStats_t structure filled with information about the current
 * heap state.
 */
void vPortGetHeapStats( HeapStats_t * pxHeapStats );


    /* Reason for rewrite:
     * VeriFast treats the `malloc` and `free` functions specially,
     * in a particular built-in way that cannot be axiomatized within
     * VeriFast's specification language. 
     * 
     * When `malloc( sizeof(struct S) )` is called for a user defined
     * struct `S`, VeriFast instantiates the corresponding
     * `malloc_block_S(...)` predicate as well as points-to chunks
     * for its fields.
     * Reversely, calling `free` cleans up all the predicates instantiated
     * by `malloc`.
     */
// # 199 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h"
void vPortInitialiseBlocks( void ) ;
size_t xPortGetFreeHeapSize( void ) ;
size_t xPortGetMinimumEverFreeHeapSize( void ) ;
// # 211 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h"
/*
 * Setup the hardware ready for the scheduler to take control.  This generally
 * sets up a tick interrupt and sets timers for the correct tick frequency.
 */
BaseType_t xPortStartScheduler( void ) ;

/*
 * Undo any hardware/ISR setup that was performed by xPortStartScheduler() so
 * the hardware is left in its original condition after the scheduler stops
 * executing.
 */
void vPortEndScheduler( void ) ;

/*
 * The structures and methods of manipulating the MPU are contained within the
 * port layer.
 *
 * Fills the xMPUSettings structure with the memory region information
 * contained in xRegions.
 */
// # 239 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/portable.h"
/* *INDENT-OFF* */



/* *INDENT-ON* */
// # 64 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h" 2

/* Must be defaulted before configUSE_NEWLIB_REENTRANT is used below. */




/* Required if struct _reent is used. */
// # 83 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/*
 * Check all the required application specific macros have been defined.
 * These macros are application specific and (as downloaded) are defined
 * within FreeRTOSConfig.h.
 */
// # 148 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
        /* If INCLUDE_vTaskDelayUntil is set but INCLUDE_xTaskDelayUntil is not then
         * the project's FreeRTOSConfig.h probably pre-dates the introduction of
         * xTaskDelayUntil and setting INCLUDE_xTaskDelayUntil to whatever
         * INCLUDE_vTaskDelayUntil is set to will ensure backward compatibility.
         */
// # 282 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/* configPRECONDITION should be defined as configASSERT.
 * The CBMC proofs need a way to track assumptions and assertions.
 * A configPRECONDITION statement should express an implicit invariant or
 * assumption made.  A configASSERT statement should express an invariant that must
 * hold explicit before calling the code. */
// # 311 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/* The timers module relies on xTaskGetSchedulerState(). */
// # 366 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/* Remove any unused trace macros. */


/* Used to perform any necessary initialisation - for example, open a file
 * into which trace is to be written. */





/* Use to close a trace, for example close a file into which trace has been
 * written. */





/* Called after a task has been selected to run.  pxCurrentTCB holds a pointer
 * to the task control block of the selected task. */





/* Called before stepping the tick count after waking from tickless idle
 * sleep. */




    /* Called immediately before entering tickless idle. */




    /* Called when returning to the Idle task after a tickless idle. */





/* Called before a task has been selected to run.  pxCurrentTCB holds a pointer
 * to the task control block of the task being switched out. */





/* Called when a task attempts to take a mutex that is already held by a
 * lower priority task.  pxTCBOfMutexHolder is a pointer to the TCB of the task
 * that holds the mutex.  uxInheritedPriority is the priority the mutex holder
 * will inherit (the priority of the task that is attempting to obtain the
 * muted. */





/* Called when a task releases a mutex, the holding of which had resulted in
 * the task inheriting the priority of a higher priority task.
 * pxTCBOfMutexHolder is a pointer to the TCB of the task that is releasing the
 * mutex.  uxOriginalPriority is the task's configured (base) priority. */





/* Task is about to block because it cannot read from a
 * queue/mutex/semaphore.  pxQueue is a pointer to the queue/mutex/semaphore
 * upon which the read was attempted.  pxCurrentTCB points to the TCB of the
 * task that attempted the read. */





/* Task is about to block because it cannot read from a
 * queue/mutex/semaphore.  pxQueue is a pointer to the queue/mutex/semaphore
 * upon which the read was attempted.  pxCurrentTCB points to the TCB of the
 * task that attempted the read. */





/* Task is about to block because it cannot write to a
 * queue/mutex/semaphore.  pxQueue is a pointer to the queue/mutex/semaphore
 * upon which the write was attempted.  pxCurrentTCB points to the TCB of the
 * task that attempted the write. */
// # 470 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/* The following event macros are embedded in the kernel API calls. */
// # 925 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
    /* Defaults to 0 for backward compatibility. */
// # 944 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/* Sanity check the configuration. */
// # 986 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/* The tick type can be read atomically, so critical sections used when the
 * tick count is returned can be defined away. */






/* Definitions to allow backward compatibility with FreeRTOS versions prior to
 * V8 if desired. */






/* configPRINTF() was not defined, so define it away to nothing.  To use
 * configPRINTF() then define it as follows (where MyPrintFunction() is
 * provided by the application writer):
 *
 * void MyPrintFunction(const char *pcFormat, ... );
 #define configPRINTF( X )   MyPrintFunction X
 *
 * Then call like a standard printf() function, but placing brackets around
 * all parameters so they are passed as a single parameter.  For example:
 * configPRINTF( ("Value = %d", MyVariable) ); */





/* The application writer has not provided their own MAX macro, so define
 * the following generic implementation. */





/* The application writer has not provided their own MIN macro, so define
 * the following generic implementation. */
// # 1067 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/* Set configUSE_TASK_FPU_SUPPORT to 0 to omit floating point support even
 * if floating point hardware is otherwise supported by the FreeRTOS port in use.
 * This constant is not supported by all FreeRTOS ports that include floating
 * point support. */




/* Set configENABLE_MPU to 1 to enable MPU support and 0 to disable it. This is
 * currently used in ARMv8M ports. */




/* Set configENABLE_FPU to 1 to enable FPU support and 0 to disable it. This is
 * currently used in ARMv8M ports. */




/* Set configENABLE_TRUSTZONE to 1 enable TrustZone support and 0 to disable it.
 * This is currently used in ARMv8M ports. */




/* Set configRUN_FREERTOS_SECURE_ONLY to 1 to run the FreeRTOS ARMv8M port on
 * the Secure Side only. */




/* Sometimes the FreeRTOSConfig.h settings only allow a task to be created using
 * dynamically allocated RAM, in which case when any task is deleted it is known
 * that both the task's stack and TCB need to be freed.  Sometimes the
 * FreeRTOSConfig.h settings only allow a task to be created using statically
 * allocated RAM, in which case when any task is deleted it is known that neither
 * the task's stack or TCB should be freed.  Sometimes the FreeRTOSConfig.h
 * settings allow a task to be created using either statically or dynamically
 * allocated RAM, in which case a member of the TCB is used to record whether the
 * stack and/or TCB were allocated statically or dynamically, so when a task is
 * deleted the RAM that was allocated dynamically is freed again and no attempt is
 * made to free the RAM that was allocated statically.
 * tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE is only true if it is possible for a
 * task to be created using either statically or dynamically allocated RAM.  Note
 * that if portUSING_MPU_WRAPPERS is 1 then a protected task can be created with
 * a statically allocated stack and a dynamically allocated TCB.
 *
 * The following table lists various combinations of portUSING_MPU_WRAPPERS,
 * configSUPPORT_DYNAMIC_ALLOCATION and configSUPPORT_STATIC_ALLOCATION and
 * when it is possible to have both static and dynamic allocation:
 *  +-----+---------+--------+-----------------------------+-----------------------------------+------------------+-----------+
 * | MPU | Dynamic | Static |     Available Functions     |       Possible Allocations        | Both Dynamic and | Need Free |
 * |     |         |        |                             |                                   | Static Possible  |           |
 * +-----+---------+--------+-----------------------------+-----------------------------------+------------------+-----------+
 * | 0   | 0       | 1      | xTaskCreateStatic           | TCB - Static, Stack - Static      | No               | No        |
 * +-----|---------|--------|-----------------------------|-----------------------------------|------------------|-----------|
 * | 0   | 1       | 0      | xTaskCreate                 | TCB - Dynamic, Stack - Dynamic    | No               | Yes       |
 * +-----|---------|--------|-----------------------------|-----------------------------------|------------------|-----------|
 * | 0   | 1       | 1      | xTaskCreate,                | 1. TCB - Dynamic, Stack - Dynamic | Yes              | Yes       |
 * |     |         |        | xTaskCreateStatic           | 2. TCB - Static, Stack - Static   |                  |           |
 * +-----|---------|--------|-----------------------------|-----------------------------------|------------------|-----------|
 * | 1   | 0       | 1      | xTaskCreateStatic,          | TCB - Static, Stack - Static      | No               | No        |
 * |     |         |        | xTaskCreateRestrictedStatic |                                   |                  |           |
 * +-----|---------|--------|-----------------------------|-----------------------------------|------------------|-----------|
 * | 1   | 1       | 0      | xTaskCreate,                | 1. TCB - Dynamic, Stack - Dynamic | Yes              | Yes       |
 * |     |         |        | xTaskCreateRestricted       | 2. TCB - Dynamic, Stack - Static  |                  |           |
 * +-----|---------|--------|-----------------------------|-----------------------------------|------------------|-----------|
 * | 1   | 1       | 1      | xTaskCreate,                | 1. TCB - Dynamic, Stack - Dynamic | Yes              | Yes       |
 * |     |         |        | xTaskCreateStatic,          | 2. TCB - Dynamic, Stack - Static  |                  |           |
 * |     |         |        | xTaskCreateRestricted,      | 3. TCB - Static, Stack - Static   |                  |           |
 * |     |         |        | xTaskCreateRestrictedStatic |                                   |                  |           |
 * +-----+---------+--------+-----------------------------+-----------------------------------+------------------+-----------+
 */




/*
 * In line with software engineering best practice, FreeRTOS implements a strict
 * data hiding policy, so the real structures used by FreeRTOS to maintain the
 * state of tasks, queues, semaphores, etc. are not accessible to the application
 * code.  However, if the application writer wants to statically allocate such
 * an object then the size of the object needs to be known.  Dummy structures
 * that are guaranteed to have the same size and alignment requirements of the
 * real objects are used for this purpose.  The dummy list and list item
 * structures below are used for inclusion in such a dummy structure.
 */
struct xSTATIC_LIST_ITEM
{



    TickType_t xDummy2;
    void * pvDummy3[ 4 ];



};
typedef struct xSTATIC_LIST_ITEM StaticListItem_t;

/* See the comments above the struct xSTATIC_LIST_ITEM definition. */
struct xSTATIC_MINI_LIST_ITEM
{



    TickType_t xDummy2;
    void * pvDummy3[ 2 ];
};
typedef struct xSTATIC_MINI_LIST_ITEM StaticMiniListItem_t;

/* See the comments above the struct xSTATIC_LIST_ITEM definition. */
typedef struct xSTATIC_LIST
{



    UBaseType_t uxDummy2;
    void * pvDummy3;
    StaticMiniListItem_t xDummy4;



} StaticList_t;

/*
 * In line with software engineering best practice, especially when supplying a
 * library that is likely to change in future versions, FreeRTOS implements a
 * strict data hiding policy.  This means the Task structure used internally by
 * FreeRTOS is not accessible to application code.  However, if the application
 * writer wants to statically allocate the memory required to create a task then
 * the size of the task object needs to be known.  The StaticTask_t structure
 * below is provided for this purpose.  Its sizes and alignment requirements are
 * guaranteed to match those of the genuine structure, no matter which
 * architecture is being used, and no matter how the values in FreeRTOSConfig.h
 * are set.  Its contents are somewhat obfuscated in the hope users will
 * recognise that it would be unwise to make direct use of the structure members.
 */
typedef struct xSTATIC_TCB
{
    void * pxDummy1;






    StaticListItem_t xDummy3[ 2 ];
    UBaseType_t uxDummy5;
    void * pxDummy6;
    BaseType_t xDummy23[ 2 ];
    uint8_t ucDummy7[ 16 ];







        UBaseType_t uxDummy9;


        UBaseType_t uxDummy10[ 2 ];


        UBaseType_t uxDummy12[ 2 ];





        void * pvDummy15[ 5 ];
// # 1248 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
        uint32_t ulDummy18[ 1 ];
        uint8_t ucDummy19[ 1 ];






        uint8_t ucDummy21;




} StaticTask_t;

/*
 * In line with software engineering best practice, especially when supplying a
 * library that is likely to change in future versions, FreeRTOS implements a
 * strict data hiding policy.  This means the Queue structure used internally by
 * FreeRTOS is not accessible to application code.  However, if the application
 * writer wants to statically allocate the memory required to create a queue
 * then the size of the queue object needs to be known.  The StaticQueue_t
 * structure below is provided for this purpose.  Its sizes and alignment
 * requirements are guaranteed to match those of the genuine structure, no
 * matter which architecture is being used, and no matter how the values in
 * FreeRTOSConfig.h are set.  Its contents are somewhat obfuscated in the hope
 * users will recognise that it would be unwise to make direct use of the
 * structure members.
 */
// # 1311 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/FreeRTOS.h"
/*
 * In line with software engineering best practice, especially when supplying a
 * library that is likely to change in future versions, FreeRTOS implements a
 * strict data hiding policy.  This means the event group structure used
 * internally by FreeRTOS is not accessible to application code.  However, if
 * the application writer wants to statically allocate the memory required to
 * create an event group then the size of the event group object needs to be
 * know.  The StaticEventGroup_t structure below is provided for this purpose.
 * Its sizes and alignment requirements are guaranteed to match those of the
 * genuine structure, no matter which architecture is being used, and no matter
 * how the values in FreeRTOSConfig.h are set.  Its contents are somewhat
 * obfuscated in the hope users will recognise that it would be unwise to make
 * direct use of the structure members.
 */
typedef struct xSTATIC_EVENT_GROUP
{
    TickType_t xDummy1;
    StaticList_t xDummy2;


        UBaseType_t uxDummy3;





} StaticEventGroup_t;

/*
 * In line with software engineering best practice, especially when supplying a
 * library that is likely to change in future versions, FreeRTOS implements a
 * strict data hiding policy.  This means the software timer structure used
 * internally by FreeRTOS is not accessible to application code.  However, if
 * the application writer wants to statically allocate the memory required to
 * create a software timer then the size of the queue object needs to be known.
 * The StaticTimer_t structure below is provided for this purpose.  Its sizes
 * and alignment requirements are guaranteed to match those of the genuine
 * structure, no matter which architecture is being used, and no matter how the
 * values in FreeRTOSConfig.h are set.  Its contents are somewhat obfuscated in
 * the hope users will recognise that it would be unwise to make direct use of
 * the structure members.
 */
typedef struct xSTATIC_TIMER
{
    void * pvDummy1;
    StaticListItem_t xDummy2;
    TickType_t xDummy3;
    void * pvDummy5;
    TaskFunction_t pvDummy6;

        UBaseType_t uxDummy7;

    uint8_t ucDummy8;
} StaticTimer_t;

/*
 * In line with software engineering best practice, especially when supplying a
 * library that is likely to change in future versions, FreeRTOS implements a
 * strict data hiding policy.  This means the stream buffer structure used
 * internally by FreeRTOS is not accessible to application code.  However, if
 * the application writer wants to statically allocate the memory required to
 * create a stream buffer then the size of the stream buffer object needs to be
 * known.  The StaticStreamBuffer_t structure below is provided for this
 * purpose.  Its size and alignment requirements are guaranteed to match those
 * of the genuine structure, no matter which architecture is being used, and
 * no matter how the values in FreeRTOSConfig.h are set.  Its contents are
 * somewhat obfuscated in the hope users will recognise that it would be unwise
 * to make direct use of the structure members.
 */
typedef struct xSTATIC_STREAM_BUFFER
{
    size_t uxDummy1[ 4 ];
    void * pvDummy2[ 3 ];
    uint8_t ucDummy3;

        UBaseType_t uxDummy4;

} StaticStreamBuffer_t;

/* Message buffers are built on stream buffers. */
typedef StaticStreamBuffer_t StaticMessageBuffer_t;

/* *INDENT-OFF* */



/* *INDENT-ON* */
// # 47 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */






    /* Reason for rewrite:
     * VeriFast bug:
     * Both `#ifdef INC_FREERTOS_H` and its negation `#ifdef INC_FREERTOS_H`
     * evaluate to true. See minimal example `define_name`.
     */

    /* Remember that this header is included by `tasks.c` after it includes
     * `FreeRTOS.h`.
     */
    // TODO: Remove this work-around once VF has been fixed.



/* Remark: 
 * Note that the following VF section renders the previous one obsolete.
 * However, we keep the above as a reminder until the corresponding bug
 * has been fixed.
 */

    /* Reason for rewrite:
     * Even though in the current verification setup, `FreeRTOS.h` is always
     * included before this file is processed, VeriFast does not consider this
     * context when processing this file. VeriFast forbids macro expansions to
     * depend on a potentially variable context, e.g, `configSTACK_DEPTH_TYPE` 
     * which expands to 'uint16_t' if and only if `FreeRTOS.h` has been 
     * included.
     */







// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/list.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */

/*
 * This is the list implementation used by the scheduler.  While it is tailored
 * heavily for the schedulers needs, it is also available for use by
 * application code.
 *
 * list_ts can only store pointers to list_item_ts.  Each ListItem_t contains a
 * numeric value (xItemValue).  Most of the time the lists are sorted in
 * descending item value order.
 *
 * Lists are created already containing one list item.  The value of this
 * item is the maximum possible that can be stored, it is therefore always at
 * the end of the list and acts as a marker.  The list member pxHead always
 * points to this marker - even though it is at the tail of the list.  This
 * is because the tail contains a wrap back pointer to the true head of
 * the list.
 *
 * In addition to it's value, each list item contains a pointer to the next
 * item in the list (pxNext), a pointer to the list it is in (pxContainer)
 * and a pointer to back to the object that contains it.  These later two
 * pointers are included for efficiency of list manipulation.  There is
 * effectively a two way link between the object containing the list item and
 * the list item itself.
 *
 *
 * \page ListIntroduction List Implementation
 * \ingroup FreeRTOSIntro
 */







    /* Reason for rewrite:
     * VeriFast bug:
     * Both `#ifdef INC_FREERTOS_H` and its negation `#ifdef INC_FREERTOS_H`
     * evaluate to true. See minimal example `define_name`.
     */

    /* Remember that this header is included indirectly `tasks.c` after it
     * includes `FreeRTOS.h`.
     */
    // TODO: Remove this work-around once VF has been fixed.







    /* Reason for rewrite:
     * VeriFast's normal and context-free preprocessor consume different
     * numbers of tokens when expanding `PRIVILEGED_FUNCTION` in this file.
     */

    // TODO: Figure out why the preprocessors consume different amounts of
    //       of tokens. This most likely has to do with the path/context
    //       from which this header is included.


/*
 * The list structure members are modified from within interrupts, and therefore
 * by rights should be declared volatile.  However, they are only modified in a
 * functionally atomic way (within critical sections of with the scheduler
 * suspended) and are either passed by reference into a function or indexed via
 * a volatile variable.  Therefore, in all use cases tested so far, the volatile
 * qualifier can be omitted in order to provide a moderate performance
 * improvement without adversely affecting functional behaviour.  The assembly
 * instructions generated by the IAR, ARM and GCC compilers when the respective
 * compiler's options were set for maximum optimisation has been inspected and
 * deemed to be as intended.  That said, as compiler technology advances, and
 * especially if aggressive cross module optimisation is used (a use case that
 * has not been exercised to any great extend) then it is feasible that the
 * volatile qualifier will be needed for correct optimisation.  It is expected
 * that a compiler removing essential code because, without the volatile
 * qualifier on the list structure members and with aggressive cross module
 * optimisation, the compiler deemed the code unnecessary will result in
 * complete and obvious failure of the scheduler.  If this is ever experienced
 * then the volatile qualifier can be inserted in the relevant places within the
 * list structures by simply defining configLIST_VOLATILE to volatile in
 * FreeRTOSConfig.h (as per the example at the bottom of this comment block).
 * If configLIST_VOLATILE is not defined then the preprocessor directives below
 * will simply #define configLIST_VOLATILE away completely.
 *
 * To use volatile list structure members then add the following line to
 * FreeRTOSConfig.h (without the quotes):
 * "#define configLIST_VOLATILE volatile"
 */




/* *INDENT-OFF* */



/* *INDENT-ON* */

/* Macros that can be used to place known values within the list structures,
 * then check that the known values do not get corrupted during the execution of
 * the application.   These may catch the list data structures being overwritten in
 * memory.  They will not catch data errors caused by incorrect configuration or
 * use of FreeRTOS.*/

    /* Define the macros to do nothing. */
// # 163 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/list.h"
/*
 * Definition of the only type of object that a list can contain.
 */
struct xLIST;
struct xLIST_ITEM
{
                                                            /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
                        TickType_t xItemValue; /*< The value being listed.  In most cases this is used to sort the list in descending order. */
    struct xLIST_ITEM * pxNext; /*< Pointer to the next ListItem_t in the list. */
    struct xLIST_ITEM * pxPrevious; /*< Pointer to the previous ListItem_t in the list. */
    void * pvOwner; /*< Pointer to the object (normally a TCB) that contains the list item.  There is therefore a two way link between the object containing the list item and the list item itself. */
    struct xLIST * pxContainer; /*< Pointer to the list in which this list item is placed (if any). */
                                                            /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
};
typedef struct xLIST_ITEM ListItem_t; /* For some reason lint wants this as two separate definitions. */

struct xMINI_LIST_ITEM
{
                                                  /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
                        TickType_t xItemValue;
    struct xLIST_ITEM * pxNext;
    struct xLIST_ITEM * pxPrevious;
};
typedef struct xMINI_LIST_ITEM MiniListItem_t;

/*
 * Definition of the type of queue used by the scheduler.
 */
typedef struct xLIST
{
                                                  /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    volatile UBaseType_t uxNumberOfItems;
    ListItem_t * pxIndex; /*< Used to walk through the list.  Points to the last item returned by a call to listGET_OWNER_OF_NEXT_ENTRY (). */
    MiniListItem_t xListEnd; /*< List item that contains the maximum possible item value meaning it is always at the end of the list and is therefore used as a marker. */
                                                  /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
} List_t;

/*
 * Access macro to set the owner of a list item.  The owner of a list item
 * is the object (usually a TCB) that contains the list item.
 *
 * \page listSET_LIST_ITEM_OWNER listSET_LIST_ITEM_OWNER
 * \ingroup LinkedList
 */


/*
 * Access macro to get the owner of a list item.  The owner of a list item
 * is the object (usually a TCB) that contains the list item.
 *
 * \page listGET_LIST_ITEM_OWNER listSET_LIST_ITEM_OWNER
 * \ingroup LinkedList
 */


/*
 * Access macro to set the value of the list item.  In most cases the value is
 * used to sort the list in descending order.
 *
 * \page listSET_LIST_ITEM_VALUE listSET_LIST_ITEM_VALUE
 * \ingroup LinkedList
 */


/*
 * Access macro to retrieve the value of the list item.  The value can
 * represent anything - for example the priority of a task, or the time at
 * which a task should be unblocked.
 *
 * \page listGET_LIST_ITEM_VALUE listGET_LIST_ITEM_VALUE
 * \ingroup LinkedList
 */


/*
 * Access macro to retrieve the value of the list item at the head of a given
 * list.
 *
 * \page listGET_LIST_ITEM_VALUE listGET_LIST_ITEM_VALUE
 * \ingroup LinkedList
 */


/*
 * Return the list item at the head of the list.
 *
 * \page listGET_HEAD_ENTRY listGET_HEAD_ENTRY
 * \ingroup LinkedList
 */


/*
 * Return the next list item.
 *
 * \page listGET_NEXT listGET_NEXT
 * \ingroup LinkedList
 */


/*
 * Return the list item that marks the end of the list
 *
 * \page listGET_END_MARKER listGET_END_MARKER
 * \ingroup LinkedList
 */


/*
 * Access macro to determine if a list contains any items.  The macro will
 * only have the value true if the list is empty.
 *
 * \page listLIST_IS_EMPTY listLIST_IS_EMPTY
 * \ingroup LinkedList
 */


/*
 * Access macro to return the number of items in the list.
 */


/*
 * Access function to obtain the owner of the next entry in a list.
 *
 * The list member pxIndex is used to walk through a list.  Calling
 * listGET_OWNER_OF_NEXT_ENTRY increments pxIndex to the next item in the list
 * and returns that entry's pxOwner parameter.  Using multiple calls to this
 * function it is therefore possible to move through every item contained in
 * a list.
 *
 * The pxOwner parameter of a list item is a pointer to the object that owns
 * the list item.  In the scheduler this is normally a task control block.
 * The pxOwner parameter effectively creates a two way link between the list
 * item and its owner.
 *
 * @param pxTCB pxTCB is set to the address of the owner of the next list item.
 * @param pxList The list from which the next item owner is to be returned.
 *
 * \page listGET_OWNER_OF_NEXT_ENTRY listGET_OWNER_OF_NEXT_ENTRY
 * \ingroup LinkedList
 */

    /* Reason for rewrite:
     * VeriFast does not support const pointers.
     */
// # 337 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/list.h"
/*
 * Access function to obtain the owner of the first entry in a list.  Lists
 * are normally sorted in ascending item value order.
 *
 * This function returns the pxOwner member of the first item in the list.
 * The pxOwner parameter of a list item is a pointer to the object that owns
 * the list item.  In the scheduler this is normally a task control block.
 * The pxOwner parameter effectively creates a two way link between the list
 * item and its owner.
 *
 * @param pxList The list from which the owner of the head item is to be
 * returned.
 *
 * \page listGET_OWNER_OF_HEAD_ENTRY listGET_OWNER_OF_HEAD_ENTRY
 * \ingroup LinkedList
 */


/*
 * Check to see if a list item is within a list.  The list item maintains a
 * "container" pointer that points to the list it is in.  All this macro does
 * is check to see if the container and the list match.
 *
 * @param pxList The list we want to know if the list item is within.
 * @param pxListItem The list item we want to know if is in the list.
 * @return pdTRUE if the list item is in the list, otherwise pdFALSE.
 */


/*
 * Return the list a list item is contained within (referenced from).
 *
 * @param pxListItem The list item being queried.
 * @return A pointer to the List_t object that references the pxListItem
 */


/*
 * This provides a crude means of knowing if a list has been initialised, as
 * pxList->xListEnd.xItemValue is set to portMAX_DELAY by the vListInitialise()
 * function.
 */


/*
 * Must be called before a list is used!  This initialises all the members
 * of the list structure and inserts the xListEnd item into the list as a
 * marker to the back of the list.
 *
 * @param pxList Pointer to the list being initialised.
 *
 * \page vListInitialise vListInitialise
 * \ingroup LinkedList
 */
void vListInitialise( List_t * pxList ) ;

/*
 * Must be called before a list item is used.  This sets the list container to
 * null so the item does not think that it is already contained in a list.
 *
 * @param pxItem Pointer to the list item being initialised.
 *
 * \page vListInitialiseItem vListInitialiseItem
 * \ingroup LinkedList
 */
void vListInitialiseItem( ListItem_t * pxItem ) ;
//@ requires true;
//@ ensures true;

/*
 * Insert a list item into a list.  The item will be inserted into the list in
 * a position determined by its item value (descending item value order).
 *
 * @param pxList The list into which the item is to be inserted.
 *
 * @param pxNewListItem The item that is to be placed in the list.
 *
 * \page vListInsert vListInsert
 * \ingroup LinkedList
 */
void vListInsert( List_t * pxList,
                  ListItem_t * pxNewListItem ) ;

/*
 * Insert a list item into a list.  The item will be inserted in a position
 * such that it will be the last item within the list returned by multiple
 * calls to listGET_OWNER_OF_NEXT_ENTRY.
 *
 * The list member pxIndex is used to walk through a list.  Calling
 * listGET_OWNER_OF_NEXT_ENTRY increments pxIndex to the next item in the list.
 * Placing an item in a list using vListInsertEnd effectively places the item
 * in the list position pointed to by pxIndex.  This means that every other
 * item within the list will be returned by listGET_OWNER_OF_NEXT_ENTRY before
 * the pxIndex parameter again points to the item being inserted.
 *
 * @param pxList The list into which the item is to be inserted.
 *
 * @param pxNewListItem The list item to be inserted into the list.
 *
 * \page vListInsertEnd vListInsertEnd
 * \ingroup LinkedList
 */
void vListInsertEnd( List_t * pxList,
                     ListItem_t * pxNewListItem ) ;

/*
 * Remove an item from a list.  The list item has a pointer to the list that
 * it is in, so only the list item need be passed into the function.
 *
 * @param uxListRemove The item to be removed.  The item will remove itself from
 * the list pointed to by it's pxContainer parameter.
 *
 * @return The number of items that remain in the list after the list item has
 * been removed.
 *
 * \page uxListRemove uxListRemove
 * \ingroup LinkedList
 */
UBaseType_t uxListRemove( ListItem_t * pxItemToRemove ) ;

/* *INDENT-OFF* */



/* *INDENT-ON* */
// # 67 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h" 2

/* *INDENT-OFF* */



/* *INDENT-ON* */

/*-----------------------------------------------------------
* MACROS AND DEFINITIONS
*----------------------------------------------------------*/






/* MPU region parameters passed in ulParameters
 * of MemoryRegion_t struct. */






/* The direct to task notification feature used to have only a single notification
 * per task.  Now there is an array of notifications per task that is dimensioned by
 * configTASK_NOTIFICATION_ARRAY_ENTRIES.  For backward compatibility, any use of the
 * original direct to task notification defaults to using the first index in the
 * array. */


/**
 * task. h
 *
 * Type by which tasks are referenced.  For example, a call to xTaskCreate
 * returns (via a pointer parameter) an TaskHandle_t variable that can then
 * be used as a parameter to vTaskDelete to delete the task.
 *
 * \defgroup TaskHandle_t TaskHandle_t
 * \ingroup Tasks
 */
struct tskTaskControlBlock; /* The old naming convention is used to prevent breaking kernel aware debuggers. */
typedef struct tskTaskControlBlock * TaskHandle_t;

/*
 * Defines the prototype to which the application task hook function must
 * conform.
 */
typedef BaseType_t (* TaskHookFunction_t)( void * );

/* Task states returned by eTaskGetState. */
typedef enum
{
    eRunning = 0, /* A task is querying the state of itself, so must be running. */
    eReady, /* The task being queried is in a ready or pending ready list. */
    eBlocked, /* The task being queried is in the Blocked state. */
    eSuspended, /* The task being queried is in the Suspended state, or is in the Blocked state with an infinite time out. */
    eDeleted, /* The task being queried has been deleted, but its TCB has not yet been freed. */
    eInvalid /* Used as an 'invalid state' value. */
} eTaskState;

/* Actions that can be performed when vTaskNotify() is called. */
typedef enum
{
    eNoAction = 0, /* Notify the task without updating its notify value. */
    eSetBits, /* Set bits in the task's notification value. */
    eIncrement, /* Increment the task's notification value. */
    eSetValueWithOverwrite, /* Set the task's notification value to a specific value even if the previous value has not yet been read by the task. */
    eSetValueWithoutOverwrite /* Set the task's notification value if the previous value has been read by the task. */
} eNotifyAction;

/*
 * Used internally only.
 */
typedef struct xTIME_OUT
{
    BaseType_t xOverflowCount;
    TickType_t xTimeOnEntering;
} TimeOut_t;

/*
 * Defines the memory ranges allocated to the task when an MPU is used.
 */
typedef struct xMEMORY_REGION
{
    void * pvBaseAddress;
    uint32_t ulLengthInBytes;
    uint32_t ulParameters;
} MemoryRegion_t;

/*
 * Parameters required to create an MPU protected task.
 */
typedef struct xTASK_PARAMETERS
{
    TaskFunction_t pvTaskCode;
    const char * pcName; /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
    uint32_t usStackDepth;
    void * pvParameters;
    UBaseType_t uxPriority;
    StackType_t * puxStackBuffer;
    MemoryRegion_t xRegions[ 1 ];



} TaskParameters_t;

/* Used with the uxTaskGetSystemState() function to return the state of each task
 * in the system. */
typedef struct xTASK_STATUS
{
    TaskHandle_t xHandle; /* The handle of the task to which the rest of the information in the structure relates. */
    const char * pcTaskName; /* A pointer to the task's name.  This value will be invalid if the task was deleted since the structure was populated! */ /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
    UBaseType_t xTaskNumber; /* A number unique to the task. */
    eTaskState eCurrentState; /* The state in which the task existed when the structure was populated. */
    UBaseType_t uxCurrentPriority; /* The priority at which the task was running (may be inherited) when the structure was populated. */
    UBaseType_t uxBasePriority; /* The priority to which the task will return if the task's current priority has been inherited to avoid unbounded priority inversion when obtaining a mutex.  Only valid if configUSE_MUTEXES is defined as 1 in FreeRTOSConfig.h. */
    uint32_t ulRunTimeCounter; /* The total run time allocated to the task so far, as defined by the run time stats clock.  See https://www.FreeRTOS.org/rtos-run-time-stats.html.  Only valid when configGENERATE_RUN_TIME_STATS is defined as 1 in FreeRTOSConfig.h. */
    StackType_t * pxStackBase; /* Points to the lowest address of the task's stack area. */
    uint32_t usStackHighWaterMark; /* The minimum amount of stack space that has remained for the task since the task was created.  The closer this value is to zero the closer the task has come to overflowing its stack. */
} TaskStatus_t;

/* Possible return values for eTaskConfirmSleepModeStatus(). */
typedef enum
{
    eAbortSleep = 0, /* A task has been made ready or a context switch pended since portSUPPRESS_TICKS_AND_SLEEP() was called - abort entering a sleep mode. */
    eStandardSleep, /* Enter a sleep mode that will not last any longer than the expected idle time. */
    eNoTasksWaitingTimeout /* No tasks are waiting for a timeout so it is safe to enter a sleep mode that can only be exited by an external interrupt. */
} eSleepModeStatus;

/**
 * Defines the priority used by the idle task.  This must not be modified.
 *
 * \ingroup TaskUtils
 */


/**
 * Defines affinity to all available cores.
 *
 */




/**
 * task. h
 *
 * Macro for forcing a context switch.
 *
 * \defgroup taskYIELD taskYIELD
 * \ingroup SchedulerControl
 */


/**
 * task. h
 *
 * Macro to mark the start of a critical code region.  Preemptive context
 * switches cannot occur when in a critical region.
 *
 * NOTE: This may alter the stack (depending on the portable implementation)
 * so must be used with care!
 *
 * \defgroup taskENTER_CRITICAL taskENTER_CRITICAL
 * \ingroup SchedulerControl
 */



/**
 * task. h
 *
 * Macro to mark the end of a critical code region.  Preemptive context
 * switches cannot occur when in a critical region.
 *
 * NOTE: This may alter the stack (depending on the portable implementation)
 * so must be used with care!
 *
 * \defgroup taskEXIT_CRITICAL taskEXIT_CRITICAL
 * \ingroup SchedulerControl
 */



/**
 * task. h
 *
 * Macro to disable all maskable interrupts.
 * This also returns what the interrupt state was
 * upon being called. This state may subsequently
 * be passed to taskRESTORE_INTERRUPTS().
 *
 * \defgroup taskDISABLE_INTERRUPTS taskDISABLE_INTERRUPTS
 * \ingroup SchedulerControl
 */


/**
 * task. h
 *
 * Macro to enable microcontroller interrupts.
 *
 * \defgroup taskENABLE_INTERRUPTS taskENABLE_INTERRUPTS
 * \ingroup SchedulerControl
 */


/**
 * task. h
 *
 * Macro to restore microcontroller interrupts to
 * a previous state.
 *
 * \defgroup taskRESTORE_INTERRUPTS taskRESTORE_INTERRUPTS
 * \ingroup SchedulerControl
 */


/**
 * task. h
 *
 * Macro that determines if it is being called from within an ISR
 * or a task. Returns non-zero if it is in an ISR.
 *
 * \defgroup taskCHECK_IF_IN_ISR taskCHECK_IF_IN_ISR
 * \ingroup SchedulerControl
 */


/* Definitions returned by xTaskGetSchedulerState().  taskSCHEDULER_SUSPENDED is
 * 0 to generate more optimal code when configASSERT() is defined as the constant
 * is used in assert() statements. */




/* Check if core value is valid */


/*-----------------------------------------------------------
* TASK CREATION API
*----------------------------------------------------------*/

/**
 * task. h
 * <pre>
 * BaseType_t xTaskCreate(
 *                            TaskFunction_t pxTaskCode,
 *                            const char *pcName,
 *                            configSTACK_DEPTH_TYPE usStackDepth,
 *                            void *pvParameters,
 *                            UBaseType_t uxPriority,
 *                            TaskHandle_t *pxCreatedTask
 *                        );
 * </pre>
 *
 * Create a new task and add it to the list of tasks that are ready to run.
 *
 * Internally, within the FreeRTOS implementation, tasks use two blocks of
 * memory.  The first block is used to hold the task's data structures.  The
 * second block is used by the task as its stack.  If a task is created using
 * xTaskCreate() then both blocks of memory are automatically dynamically
 * allocated inside the xTaskCreate() function.  (see
 * https://www.FreeRTOS.org/a00111.html).  If a task is created using
 * xTaskCreateStatic() then the application writer must provide the required
 * memory.  xTaskCreateStatic() therefore allows a task to be created without
 * using any dynamic memory allocation.
 *
 * See xTaskCreateStatic() for a version that does not use any dynamic memory
 * allocation.
 *
 * xTaskCreate() can only be used to create a task that has unrestricted
 * access to the entire microcontroller memory map.  Systems that include MPU
 * support can alternatively create an MPU constrained task using
 * xTaskCreateRestricted().
 *
 * @param pxTaskCode Pointer to the task entry function.  Tasks
 * must be implemented to never return (i.e. continuous loop).
 *
 * @param pcName A descriptive name for the task.  This is mainly used to
 * facilitate debugging.  Max length defined by configMAX_TASK_NAME_LEN - default
 * is 16.
 *
 * @param usStackDepth The size of the task stack specified as the number of
 * variables the stack can hold - not the number of bytes.  For example, if
 * the stack is 16 bits wide and usStackDepth is defined as 100, 200 bytes
 * will be allocated for stack storage.
 *
 * @param pvParameters Pointer that will be used as the parameter for the task
 * being created.
 *
 * @param uxPriority The priority at which the task should run.  Systems that
 * include MPU support can optionally create tasks in a privileged (system)
 * mode by setting bit portPRIVILEGE_BIT of the priority parameter.  For
 * example, to create a privileged task at priority 2 the uxPriority parameter
 * should be set to ( 2 | portPRIVILEGE_BIT ).
 *
 * @param pxCreatedTask Used to pass back a handle by which the created task
 * can be referenced.
 *
 * @return pdPASS if the task was successfully created and added to a ready
 * list, otherwise an error code defined in the file projdefs.h
 *
 * Example usage:
 * <pre>
 * // Task to be created.
 * void vTaskCode( void * pvParameters )
 * {
 *   for( ;; )
 *   {
 *       // Task code goes here.
 *   }
 * }
 *
 * // Function that creates a task.
 * void vOtherFunction( void )
 * {
 * static uint8_t ucParameterToPass;
 * TaskHandle_t xHandle = NULL;
 *
 *   // Create the task, storing the handle.  Note that the passed parameter ucParameterToPass
 *   // must exist for the lifetime of the task, so in this case is declared static.  If it was just an
 *   // an automatic stack variable it might no longer exist, or at least have been corrupted, by the time
 *   // the new task attempts to access it.
 *   xTaskCreate( vTaskCode, "NAME", STACK_SIZE, &ucParameterToPass, tskIDLE_PRIORITY, &xHandle );
 *   configASSERT( xHandle );
 *
 *   // Use the handle to delete the task.
 *   if( xHandle != NULL )
 *   {
 *      vTaskDelete( xHandle );
 *   }
 * }
 * </pre>
 * \defgroup xTaskCreate xTaskCreate
 * \ingroup Tasks
 */

    BaseType_t xTaskCreate( TaskFunction_t pxTaskCode,
                            const char * pcName, /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
                            const uint32_t usStackDepth,
                            void * pvParameters,
                            UBaseType_t uxPriority,
                            TaskHandle_t * pxCreatedTask ) ;
// # 424 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h"
/**
 * task. h
 * <pre>
* TaskHandle_t xTaskCreateStatic( TaskFunction_t pxTaskCode,
 *                               const char *pcName,
 *                               uint32_t ulStackDepth,
 *                               void *pvParameters,
 *                               UBaseType_t uxPriority,
 *                               StackType_t *puxStackBuffer,
 *                               StaticTask_t *pxTaskBuffer );
 * </pre>
 *
 * Create a new task and add it to the list of tasks that are ready to run.
 *
 * Internally, within the FreeRTOS implementation, tasks use two blocks of
 * memory.  The first block is used to hold the task's data structures.  The
 * second block is used by the task as its stack.  If a task is created using
 * xTaskCreate() then both blocks of memory are automatically dynamically
 * allocated inside the xTaskCreate() function.  (see
 * https://www.FreeRTOS.org/a00111.html).  If a task is created using
 * xTaskCreateStatic() then the application writer must provide the required
 * memory.  xTaskCreateStatic() therefore allows a task to be created without
 * using any dynamic memory allocation.
 *
 * @param pxTaskCode Pointer to the task entry function.  Tasks
 * must be implemented to never return (i.e. continuous loop).
 *
 * @param pcName A descriptive name for the task.  This is mainly used to
 * facilitate debugging.  The maximum length of the string is defined by
 * configMAX_TASK_NAME_LEN in FreeRTOSConfig.h.
 *
 * @param ulStackDepth The size of the task stack specified as the number of
 * variables the stack can hold - not the number of bytes.  For example, if
 * the stack is 32-bits wide and ulStackDepth is defined as 100 then 400 bytes
 * will be allocated for stack storage.
 *
 * @param pvParameters Pointer that will be used as the parameter for the task
 * being created.
 *
 * @param uxPriority The priority at which the task will run.
 *
 * @param puxStackBuffer Must point to a StackType_t array that has at least
 * ulStackDepth indexes - the array will then be used as the task's stack,
 * removing the need for the stack to be allocated dynamically.
 *
 * @param pxTaskBuffer Must point to a variable of type StaticTask_t, which will
 * then be used to hold the task's data structures, removing the need for the
 * memory to be allocated dynamically.
 *
 * @return If neither puxStackBuffer nor pxTaskBuffer are NULL, then the task
 * will be created and a handle to the created task is returned.  If either
 * puxStackBuffer or pxTaskBuffer are NULL then the task will not be created and
 * NULL is returned.
 *
 * Example usage:
 * <pre>
 *
 *  // Dimensions of the buffer that the task being created will use as its stack.
 *  // NOTE:  This is the number of words the stack will hold, not the number of
 *  // bytes.  For example, if each stack item is 32-bits, and this is set to 100,
 *  // then 400 bytes (100 * 32-bits) will be allocated.
 #define STACK_SIZE 200
 *
 *  // Structure that will hold the TCB of the task being created.
 *  StaticTask_t xTaskBuffer;
 *
 *  // Buffer that the task being created will use as its stack.  Note this is
 *  // an array of StackType_t variables.  The size of StackType_t is dependent on
 *  // the RTOS port.
 *  StackType_t xStack[ STACK_SIZE ];
 *
 *  // Function that implements the task being created.
 *  void vTaskCode( void * pvParameters )
 *  {
 *      // The parameter value is expected to be 1 as 1 is passed in the
 *      // pvParameters value in the call to xTaskCreateStatic().
 *      configASSERT( ( uint32_t ) pvParameters == 1UL );
 *
 *      for( ;; )
 *      {
 *          // Task code goes here.
 *      }
 *  }
 *
 *  // Function that creates a task.
 *  void vOtherFunction( void )
 *  {
 *      TaskHandle_t xHandle = NULL;
 *
 *      // Create the task without using any dynamic memory allocation.
 *      xHandle = xTaskCreateStatic(
 *                    vTaskCode,       // Function that implements the task.
 *                    "NAME",          // Text name for the task.
 *                    STACK_SIZE,      // Stack size in words, not bytes.
 *                    ( void * ) 1,    // Parameter passed into the task.
 *                    tskIDLE_PRIORITY,// Priority at which the task is created.
 *                    xStack,          // Array to use as the task's stack.
 *                    &xTaskBuffer );  // Variable to hold the task's data structure.
 *
 *      // puxStackBuffer and pxTaskBuffer were not NULL, so the task will have
 *      // been created, and xHandle will be the task's handle.  Use the handle
 *      // to suspend the task.
 *      vTaskSuspend( xHandle );
 *  }
 * </pre>
 * \defgroup xTaskCreateStatic xTaskCreateStatic
 * \ingroup Tasks
 */
// # 553 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h"
/**
 * task. h
 * <pre>
 * BaseType_t xTaskCreateRestricted( TaskParameters_t *pxTaskDefinition, TaskHandle_t *pxCreatedTask );
 * </pre>
 *
 * Only available when configSUPPORT_DYNAMIC_ALLOCATION is set to 1.
 *
 * xTaskCreateRestricted() should only be used in systems that include an MPU
 * implementation.
 *
 * Create a new task and add it to the list of tasks that are ready to run.
 * The function parameters define the memory regions and associated access
 * permissions allocated to the task.
 *
 * See xTaskCreateRestrictedStatic() for a version that does not use any
 * dynamic memory allocation.
 *
 * @param pxTaskDefinition Pointer to a structure that contains a member
 * for each of the normal xTaskCreate() parameters (see the xTaskCreate() API
 * documentation) plus an optional stack buffer and the memory region
 * definitions.
 *
 * @param pxCreatedTask Used to pass back a handle by which the created task
 * can be referenced.
 *
 * @return pdPASS if the task was successfully created and added to a ready
 * list, otherwise an error code defined in the file projdefs.h
 *
 * Example usage:
 * <pre>
 * // Create an TaskParameters_t structure that defines the task to be created.
 * static const TaskParameters_t xCheckTaskParameters =
 * {
 *  vATask,     // pvTaskCode - the function that implements the task.
 *  "ATask",    // pcName - just a text name for the task to assist debugging.
 *  100,        // usStackDepth - the stack size DEFINED IN WORDS.
 *  NULL,       // pvParameters - passed into the task function as the function parameters.
 *  ( 1UL | portPRIVILEGE_BIT ),// uxPriority - task priority, set the portPRIVILEGE_BIT if the task should run in a privileged state.
 *  cStackBuffer,// puxStackBuffer - the buffer to be used as the task stack.
 *
 *  // xRegions - Allocate up to three separate memory regions for access by
 *  // the task, with appropriate access permissions.  Different processors have
 *  // different memory alignment requirements - refer to the FreeRTOS documentation
 *  // for full information.
 *  {
 *      // Base address                 Length  Parameters
 *      { cReadWriteArray,              32,     portMPU_REGION_READ_WRITE },
 *      { cReadOnlyArray,               32,     portMPU_REGION_READ_ONLY },
 *      { cPrivilegedOnlyAccessArray,   128,    portMPU_REGION_PRIVILEGED_READ_WRITE }
 *  }
 * };
 *
 * int main( void )
 * {
 * TaskHandle_t xHandle;
 *
 *  // Create a task from the const structure defined above.  The task handle
 *  // is requested (the second parameter is not NULL) but in this case just for
 *  // demonstration purposes as its not actually used.
 *  xTaskCreateRestricted( &xRegTest1Parameters, &xHandle );
 *
 *  // Start the scheduler.
 *  vTaskStartScheduler();
 *
 *  // Will only get here if there was insufficient memory to create the idle
 *  // and/or timer task.
 *  for( ;; );
 * }
 * </pre>
 * \defgroup xTaskCreateRestricted xTaskCreateRestricted
 * \ingroup Tasks
 */
// # 637 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h"
/**
 * task. h
 * <pre>
 * BaseType_t xTaskCreateRestrictedStatic( TaskParameters_t *pxTaskDefinition, TaskHandle_t *pxCreatedTask );
 * </pre>
 *
 * Only available when configSUPPORT_STATIC_ALLOCATION is set to 1.
 *
 * xTaskCreateRestrictedStatic() should only be used in systems that include an
 * MPU implementation.
 *
 * Internally, within the FreeRTOS implementation, tasks use two blocks of
 * memory.  The first block is used to hold the task's data structures.  The
 * second block is used by the task as its stack.  If a task is created using
 * xTaskCreateRestricted() then the stack is provided by the application writer,
 * and the memory used to hold the task's data structure is automatically
 * dynamically allocated inside the xTaskCreateRestricted() function.  If a task
 * is created using xTaskCreateRestrictedStatic() then the application writer
 * must provide the memory used to hold the task's data structures too.
 * xTaskCreateRestrictedStatic() therefore allows a memory protected task to be
 * created without using any dynamic memory allocation.
 *
 * @param pxTaskDefinition Pointer to a structure that contains a member
 * for each of the normal xTaskCreate() parameters (see the xTaskCreate() API
 * documentation) plus an optional stack buffer and the memory region
 * definitions.  If configSUPPORT_STATIC_ALLOCATION is set to 1 the structure
 * contains an additional member, which is used to point to a variable of type
 * StaticTask_t - which is then used to hold the task's data structure.
 *
 * @param pxCreatedTask Used to pass back a handle by which the created task
 * can be referenced.
 *
 * @return pdPASS if the task was successfully created and added to a ready
 * list, otherwise an error code defined in the file projdefs.h
 *
 * Example usage:
 * <pre>
 * // Create an TaskParameters_t structure that defines the task to be created.
 * // The StaticTask_t variable is only included in the structure when
 * // configSUPPORT_STATIC_ALLOCATION is set to 1.  The PRIVILEGED_DATA macro can
 * // be used to force the variable into the RTOS kernel's privileged data area.
 * static PRIVILEGED_DATA StaticTask_t xTaskBuffer;
 * static const TaskParameters_t xCheckTaskParameters =
 * {
 *  vATask,     // pvTaskCode - the function that implements the task.
 *  "ATask",    // pcName - just a text name for the task to assist debugging.
 *  100,        // usStackDepth - the stack size DEFINED IN WORDS.
 *  NULL,       // pvParameters - passed into the task function as the function parameters.
 *  ( 1UL | portPRIVILEGE_BIT ),// uxPriority - task priority, set the portPRIVILEGE_BIT if the task should run in a privileged state.
 *  cStackBuffer,// puxStackBuffer - the buffer to be used as the task stack.
 *
 *  // xRegions - Allocate up to three separate memory regions for access by
 *  // the task, with appropriate access permissions.  Different processors have
 *  // different memory alignment requirements - refer to the FreeRTOS documentation
 *  // for full information.
 *  {
 *      // Base address                 Length  Parameters
 *      { cReadWriteArray,              32,     portMPU_REGION_READ_WRITE },
 *      { cReadOnlyArray,               32,     portMPU_REGION_READ_ONLY },
 *      { cPrivilegedOnlyAccessArray,   128,    portMPU_REGION_PRIVILEGED_READ_WRITE }
 *  }
 *
 *  &xTaskBuffer; // Holds the task's data structure.
 * };
 *
 * int main( void )
 * {
 * TaskHandle_t xHandle;
 *
 *  // Create a task from the const structure defined above.  The task handle
 *  // is requested (the second parameter is not NULL) but in this case just for
 *  // demonstration purposes as its not actually used.
 *  xTaskCreateRestricted( &xRegTest1Parameters, &xHandle );
 *
 *  // Start the scheduler.
 *  vTaskStartScheduler();
 *
 *  // Will only get here if there was insufficient memory to create the idle
 *  // and/or timer task.
 *  for( ;; );
 * }
 * </pre>
 * \defgroup xTaskCreateRestrictedStatic xTaskCreateRestrictedStatic
 * \ingroup Tasks
 */
// # 733 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h"
/**
 * task. h
 * <pre>
 * void vTaskAllocateMPURegions( TaskHandle_t xTask, const MemoryRegion_t * pxRegions );
 * </pre>
 *
 * Memory regions are assigned to a restricted task when the task is created by
 * a call to xTaskCreateRestricted().  These regions can be redefined using
 * vTaskAllocateMPURegions().
 *
 * @param xTask The handle of the task being updated.
 *
 * @param xRegions A pointer to a MemoryRegion_t structure that contains the
 * new memory region definitions.
 *
 * Example usage:
 * <pre>
 * // Define an array of MemoryRegion_t structures that configures an MPU region
 * // allowing read/write access for 1024 bytes starting at the beginning of the
 * // ucOneKByte array.  The other two of the maximum 3 definable regions are
 * // unused so set to zero.
 * static const MemoryRegion_t xAltRegions[ portNUM_CONFIGURABLE_REGIONS ] =
 * {
 *  // Base address     Length      Parameters
 *  { ucOneKByte,       1024,       portMPU_REGION_READ_WRITE },
 *  { 0,                0,          0 },
 *  { 0,                0,          0 }
 * };
 *
 * void vATask( void *pvParameters )
 * {
 *  // This task was created such that it has access to certain regions of
 *  // memory as defined by the MPU configuration.  At some point it is
 *  // desired that these MPU regions are replaced with that defined in the
 *  // xAltRegions const struct above.  Use a call to vTaskAllocateMPURegions()
 *  // for this purpose.  NULL is used as the task handle to indicate that this
 *  // function should modify the MPU regions of the calling task.
 *  vTaskAllocateMPURegions( NULL, xAltRegions );
 *
 *  // Now the task can continue its function, but from this point on can only
 *  // access its stack and the ucOneKByte array (unless any other statically
 *  // defined or shared regions have been declared elsewhere).
 * }
 * </pre>
 * \defgroup xTaskCreateRestricted xTaskCreateRestricted
 * \ingroup Tasks
 */
void vTaskAllocateMPURegions( TaskHandle_t xTask,
                              const MemoryRegion_t * pxRegions ) ;

/**
 * task. h
 * <pre>
 * void vTaskDelete( TaskHandle_t xTaskToDelete );
 * </pre>
 *
 * INCLUDE_vTaskDelete must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Remove a task from the RTOS real time kernel's management.  The task being
 * deleted will be removed from all ready, blocked, suspended and event lists.
 *
 * NOTE:  The idle task is responsible for freeing the kernel allocated
 * memory from tasks that have been deleted.  It is therefore important that
 * the idle task is not starved of microcontroller processing time if your
 * application makes any calls to vTaskDelete ().  Memory allocated by the
 * task code is not automatically freed, and should be freed before the task
 * is deleted.
 *
 * See the demo application file death.c for sample code that utilises
 * vTaskDelete ().
 *
 * @param xTaskToDelete The handle of the task to be deleted.  Passing NULL will
 * cause the calling task to be deleted.
 *
 * Example usage:
 * <pre>
 * void vOtherFunction( void )
 * {
 * TaskHandle_t xHandle;
 *
 *   // Create the task, storing the handle.
 *   xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );
 *
 *   // Use the handle to delete the task.
 *   vTaskDelete( xHandle );
 * }
 * </pre>
 * \defgroup vTaskDelete vTaskDelete
 * \ingroup Tasks
 */
void vTaskDelete( TaskHandle_t xTaskToDelete ) ;

/*-----------------------------------------------------------
* TASK CONTROL API
*----------------------------------------------------------*/

/**
 * task. h
 * <pre>
 * void vTaskDelay( const TickType_t xTicksToDelay );
 * </pre>
 *
 * Delay a task for a given number of ticks.  The actual time that the
 * task remains blocked depends on the tick rate.  The constant
 * portTICK_PERIOD_MS can be used to calculate real time from the tick
 * rate - with the resolution of one tick period.
 *
 * INCLUDE_vTaskDelay must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 *
 * vTaskDelay() specifies a time at which the task wishes to unblock relative to
 * the time at which vTaskDelay() is called.  For example, specifying a block
 * period of 100 ticks will cause the task to unblock 100 ticks after
 * vTaskDelay() is called.  vTaskDelay() does not therefore provide a good method
 * of controlling the frequency of a periodic task as the path taken through the
 * code, as well as other task and interrupt activity, will effect the frequency
 * at which vTaskDelay() gets called and therefore the time at which the task
 * next executes.  See xTaskDelayUntil() for an alternative API function designed
 * to facilitate fixed frequency execution.  It does this by specifying an
 * absolute time (rather than a relative time) at which the calling task should
 * unblock.
 *
 * @param xTicksToDelay The amount of time, in tick periods, that
 * the calling task should block.
 *
 * Example usage:
 *
 * void vTaskFunction( void * pvParameters )
 * {
 * // Block for 500ms.
 * TickType_t xDelay = 500 / portTICK_PERIOD_MS;
 *
 *   for( ;; )
 *   {
 *       // Simply toggle the LED every 500ms, blocking between each toggle.
 *       vToggleLED();
 *       vTaskDelay( xDelay );
 *   }
 * }
 *
 * \defgroup vTaskDelay vTaskDelay
 * \ingroup TaskCtrl
 */
void vTaskDelay( const TickType_t xTicksToDelay ) ;

/**
 * task. h
 * <pre>
 * BaseType_t xTaskDelayUntil( TickType_t *pxPreviousWakeTime, const TickType_t xTimeIncrement );
 * </pre>
 *
 * INCLUDE_xTaskDelayUntil must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Delay a task until a specified time.  This function can be used by periodic
 * tasks to ensure a constant execution frequency.
 *
 * This function differs from vTaskDelay () in one important aspect:  vTaskDelay () will
 * cause a task to block for the specified number of ticks from the time vTaskDelay () is
 * called.  It is therefore difficult to use vTaskDelay () by itself to generate a fixed
 * execution frequency as the time between a task starting to execute and that task
 * calling vTaskDelay () may not be fixed [the task may take a different path though the
 * code between calls, or may get interrupted or preempted a different number of times
 * each time it executes].
 *
 * Whereas vTaskDelay () specifies a wake time relative to the time at which the function
 * is called, xTaskDelayUntil () specifies the absolute (exact) time at which it wishes to
 * unblock.
 *
 * The macro pdMS_TO_TICKS() can be used to calculate the number of ticks from a
 * time specified in milliseconds with a resolution of one tick period.
 *
 * @param pxPreviousWakeTime Pointer to a variable that holds the time at which the
 * task was last unblocked.  The variable must be initialised with the current time
 * prior to its first use (see the example below).  Following this the variable is
 * automatically updated within xTaskDelayUntil ().
 *
 * @param xTimeIncrement The cycle time period.  The task will be unblocked at
 * time *pxPreviousWakeTime + xTimeIncrement.  Calling xTaskDelayUntil with the
 * same xTimeIncrement parameter value will cause the task to execute with
 * a fixed interface period.
 *
 * @return Value which can be used to check whether the task was actually delayed.
 * Will be pdTRUE if the task way delayed and pdFALSE otherwise.  A task will not
 * be delayed if the next expected wake time is in the past.
 *
 * Example usage:
 * <pre>
 * // Perform an action every 10 ticks.
 * void vTaskFunction( void * pvParameters )
 * {
 * TickType_t xLastWakeTime;
 * TickType_t xFrequency = 10;
 * BaseType_t xWasDelayed;
 *
 *     // Initialise the xLastWakeTime variable with the current time.
 *     xLastWakeTime = xTaskGetTickCount ();
 *     for( ;; )
 *     {
 *         // Wait for the next cycle.
 *         xWasDelayed = xTaskDelayUntil( &xLastWakeTime, xFrequency );
 *
 *         // Perform action here. xWasDelayed value can be used to determine
 *         // whether a deadline was missed if the code here took too long.
 *     }
 * }
 * </pre>
 * \defgroup xTaskDelayUntil xTaskDelayUntil
 * \ingroup TaskCtrl
 */
BaseType_t xTaskDelayUntil( TickType_t * pxPreviousWakeTime,
                            const TickType_t xTimeIncrement ) ;

/*
 * vTaskDelayUntil() is the older version of xTaskDelayUntil() and does not
 * return a value.
 */






/**
 * task. h
 * <pre>
 * BaseType_t xTaskAbortDelay( TaskHandle_t xTask );
 * </pre>
 *
 * INCLUDE_xTaskAbortDelay must be defined as 1 in FreeRTOSConfig.h for this
 * function to be available.
 *
 * A task will enter the Blocked state when it is waiting for an event.  The
 * event it is waiting for can be a temporal event (waiting for a time), such
 * as when vTaskDelay() is called, or an event on an object, such as when
 * xQueueReceive() or ulTaskNotifyTake() is called.  If the handle of a task
 * that is in the Blocked state is used in a call to xTaskAbortDelay() then the
 * task will leave the Blocked state, and return from whichever function call
 * placed the task into the Blocked state.
 *
 * There is no 'FromISR' version of this function as an interrupt would need to
 * know which object a task was blocked on in order to know which actions to
 * take.  For example, if the task was blocked on a queue the interrupt handler
 * would then need to know if the queue was locked.
 *
 * @param xTask The handle of the task to remove from the Blocked state.
 *
 * @return If the task referenced by xTask was not in the Blocked state then
 * pdFAIL is returned.  Otherwise pdPASS is returned.
 *
 * \defgroup xTaskAbortDelay xTaskAbortDelay
 * \ingroup TaskCtrl
 */
BaseType_t xTaskAbortDelay( TaskHandle_t xTask ) ;

/**
 * task. h
 * <pre>
 * UBaseType_t uxTaskPriorityGet( const TaskHandle_t xTask );
 * </pre>
 *
 * INCLUDE_uxTaskPriorityGet must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Obtain the priority of any task.
 *
 * @param xTask Handle of the task to be queried.  Passing a NULL
 * handle results in the priority of the calling task being returned.
 *
 * @return The priority of xTask.
 *
 * Example usage:
 * <pre>
 * void vAFunction( void )
 * {
 * TaskHandle_t xHandle;
 *
 *   // Create a task, storing the handle.
 *   xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );
 *
 *   // ...
 *
 *   // Use the handle to obtain the priority of the created task.
 *   // It was created with tskIDLE_PRIORITY, but may have changed
 *   // it itself.
 *   if( uxTaskPriorityGet( xHandle ) != tskIDLE_PRIORITY )
 *   {
 *       // The task has changed it's priority.
 *   }
 *
 *   // ...
 *
 *   // Is our priority higher than the created task?
 *   if( uxTaskPriorityGet( xHandle ) < uxTaskPriorityGet( NULL ) )
 *   {
 *       // Our priority (obtained using NULL handle) is higher.
 *   }
 * }
 * </pre>
 * \defgroup uxTaskPriorityGet uxTaskPriorityGet
 * \ingroup TaskCtrl
 */
UBaseType_t uxTaskPriorityGet( const TaskHandle_t xTask ) ;

/**
 * task. h
 * <pre>
 * UBaseType_t uxTaskPriorityGetFromISR( const TaskHandle_t xTask );
 * </pre>
 *
 * A version of uxTaskPriorityGet() that can be used from an ISR.
 */
UBaseType_t uxTaskPriorityGetFromISR( const TaskHandle_t xTask ) ;

/**
 * task. h
 * <pre>
 * eTaskState eTaskGetState( TaskHandle_t xTask );
 * </pre>
 *
 * INCLUDE_eTaskGetState must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Obtain the state of any task.  States are encoded by the eTaskState
 * enumerated type.
 *
 * @param xTask Handle of the task to be queried.
 *
 * @return The state of xTask at the time the function was called.  Note the
 * state of the task might change between the function being called, and the
 * functions return value being tested by the calling task.
 */
eTaskState eTaskGetState( TaskHandle_t xTask ) ;

/**
 * task. h
 * <pre>
 * void vTaskGetInfo( TaskHandle_t xTask, TaskStatus_t *pxTaskStatus, BaseType_t xGetFreeStackSpace, eTaskState eState );
 * </pre>
 *
 * configUSE_TRACE_FACILITY must be defined as 1 for this function to be
 * available.  See the configuration section for more information.
 *
 * Populates a TaskStatus_t structure with information about a task.
 *
 * @param xTask Handle of the task being queried.  If xTask is NULL then
 * information will be returned about the calling task.
 *
 * @param pxTaskStatus A pointer to the TaskStatus_t structure that will be
 * filled with information about the task referenced by the handle passed using
 * the xTask parameter.
 *
 * @xGetFreeStackSpace The TaskStatus_t structure contains a member to report
 * the stack high water mark of the task being queried.  Calculating the stack
 * high water mark takes a relatively long time, and can make the system
 * temporarily unresponsive - so the xGetFreeStackSpace parameter is provided to
 * allow the high water mark checking to be skipped.  The high watermark value
 * will only be written to the TaskStatus_t structure if xGetFreeStackSpace is
 * not set to pdFALSE;
 *
 * @param eState The TaskStatus_t structure contains a member to report the
 * state of the task being queried.  Obtaining the task state is not as fast as
 * a simple assignment - so the eState parameter is provided to allow the state
 * information to be omitted from the TaskStatus_t structure.  To obtain state
 * information then set eState to eInvalid - otherwise the value passed in
 * eState will be reported as the task state in the TaskStatus_t structure.
 *
 * Example usage:
 * <pre>
 * void vAFunction( void )
 * {
 * TaskHandle_t xHandle;
 * TaskStatus_t xTaskDetails;
 *
 *  // Obtain the handle of a task from its name.
 *  xHandle = xTaskGetHandle( "Task_Name" );
 *
 *  // Check the handle is not NULL.
 *  configASSERT( xHandle );
 *
 *  // Use the handle to obtain further information about the task.
 *  vTaskGetInfo( xHandle,
 *                &xTaskDetails,
 *                pdTRUE, // Include the high water mark in xTaskDetails.
 *                eInvalid ); // Include the task state in xTaskDetails.
 * }
 * </pre>
 * \defgroup vTaskGetInfo vTaskGetInfo
 * \ingroup TaskCtrl
 */
void vTaskGetInfo( TaskHandle_t xTask,
                   TaskStatus_t * pxTaskStatus,
                   BaseType_t xGetFreeStackSpace,
                   eTaskState eState ) ;

/**
 * task. h
 * <pre>
 * void vTaskPrioritySet( TaskHandle_t xTask, UBaseType_t uxNewPriority );
 * </pre>
 *
 * INCLUDE_vTaskPrioritySet must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Set the priority of any task.
 *
 * A context switch will occur before the function returns if the priority
 * being set is higher than the currently executing task.
 *
 * @param xTask Handle to the task for which the priority is being set.
 * Passing a NULL handle results in the priority of the calling task being set.
 *
 * @param uxNewPriority The priority to which the task will be set.
 *
 * Example usage:
 * <pre>
 * void vAFunction( void )
 * {
 * TaskHandle_t xHandle;
 *
 *   // Create a task, storing the handle.
 *   xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );
 *
 *   // ...
 *
 *   // Use the handle to raise the priority of the created task.
 *   vTaskPrioritySet( xHandle, tskIDLE_PRIORITY + 1 );
 *
 *   // ...
 *
 *   // Use a NULL handle to raise our priority to the same value.
 *   vTaskPrioritySet( NULL, tskIDLE_PRIORITY + 1 );
 * }
 * </pre>
 * \defgroup vTaskPrioritySet vTaskPrioritySet
 * \ingroup TaskCtrl
 */
void vTaskPrioritySet( TaskHandle_t xTask,
                       UBaseType_t uxNewPriority ) ;

/**
 * task. h
 * <pre>
 * void vTaskSuspend( TaskHandle_t xTaskToSuspend );
 * </pre>
 *
 * INCLUDE_vTaskSuspend must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Suspend any task.  When suspended a task will never get any microcontroller
 * processing time, no matter what its priority.
 *
 * Calls to vTaskSuspend are not accumulative -
 * i.e. calling vTaskSuspend () twice on the same task still only requires one
 * call to vTaskResume () to ready the suspended task.
 *
 * @param xTaskToSuspend Handle to the task being suspended.  Passing a NULL
 * handle will cause the calling task to be suspended.
 *
 * Example usage:
 * <pre>
 * void vAFunction( void )
 * {
 * TaskHandle_t xHandle;
 *
 *   // Create a task, storing the handle.
 *   xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );
 *
 *   // ...
 *
 *   // Use the handle to suspend the created task.
 *   vTaskSuspend( xHandle );
 *
 *   // ...
 *
 *   // The created task will not run during this period, unless
 *   // another task calls vTaskResume( xHandle ).
 *
 *   //...
 *
 *
 *   // Suspend ourselves.
 *   vTaskSuspend( NULL );
 *
 *   // We cannot get here unless another task calls vTaskResume
 *   // with our handle as the parameter.
 * }
 * </pre>
 * \defgroup vTaskSuspend vTaskSuspend
 * \ingroup TaskCtrl
 */
void vTaskSuspend( TaskHandle_t xTaskToSuspend ) ;

/**
 * task. h
 * <pre>
 * void vTaskResume( TaskHandle_t xTaskToResume );
 * </pre>
 *
 * INCLUDE_vTaskSuspend must be defined as 1 for this function to be available.
 * See the configuration section for more information.
 *
 * Resumes a suspended task.
 *
 * A task that has been suspended by one or more calls to vTaskSuspend ()
 * will be made available for running again by a single call to
 * vTaskResume ().
 *
 * @param xTaskToResume Handle to the task being readied.
 *
 * Example usage:
 * <pre>
 * void vAFunction( void )
 * {
 * TaskHandle_t xHandle;
 *
 *   // Create a task, storing the handle.
 *   xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, &xHandle );
 *
 *   // ...
 *
 *   // Use the handle to suspend the created task.
 *   vTaskSuspend( xHandle );
 *
 *   // ...
 *
 *   // The created task will not run during this period, unless
 *   // another task calls vTaskResume( xHandle ).
 *
 *   //...
 *
 *
 *   // Resume the suspended task ourselves.
 *   vTaskResume( xHandle );
 *
 *   // The created task will once again get microcontroller processing
 *   // time in accordance with its priority within the system.
 * }
 * </pre>
 * \defgroup vTaskResume vTaskResume
 * \ingroup TaskCtrl
 */
void vTaskResume( TaskHandle_t xTaskToResume ) ;

/**
 * task. h
 * <pre>
 * void xTaskResumeFromISR( TaskHandle_t xTaskToResume );
 * </pre>
 *
 * INCLUDE_xTaskResumeFromISR must be defined as 1 for this function to be
 * available.  See the configuration section for more information.
 *
 * An implementation of vTaskResume() that can be called from within an ISR.
 *
 * A task that has been suspended by one or more calls to vTaskSuspend ()
 * will be made available for running again by a single call to
 * xTaskResumeFromISR ().
 *
 * xTaskResumeFromISR() should not be used to synchronise a task with an
 * interrupt if there is a chance that the interrupt could arrive prior to the
 * task being suspended - as this can lead to interrupts being missed. Use of a
 * semaphore as a synchronisation mechanism would avoid this eventuality.
 *
 * @param xTaskToResume Handle to the task being readied.
 *
 * @return pdTRUE if resuming the task should result in a context switch,
 * otherwise pdFALSE. This is used by the ISR to determine if a context switch
 * may be required following the ISR.
 *
 * \defgroup vTaskResumeFromISR vTaskResumeFromISR
 * \ingroup TaskCtrl
 */
BaseType_t xTaskResumeFromISR( TaskHandle_t xTaskToResume ) ;
// # 1397 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h"
/**
 * @brief Disables preemption for a task.
 *
 * @param xTask The handle of the task to disable preemption. Passing NULL
 * disables preemption for the calling task.
 *
 * Example usage:
 *
 * void vTaskCode( void *pvParameters )
 * {
 *     // Silence warnings about unused parameters.
 *     ( void ) pvParameters;
 *
 *     for( ;; )
 *     {
 *         // ... Perform some function here.
 *
 *         // Disable preemption for this task.
 *         vTaskPreemptionDisable( NULL );
 *
 *         // The task will not be preempted when it is executing in this portion ...
 *
 *         // ... until the preemption is enabled again.
 *         vTaskPreemptionEnable( NULL );
 *
 *         // The task can be preempted when it is executing in this portion.
 *     }
 * }
 */
void vTaskPreemptionDisable( const TaskHandle_t xTask );

/**
 * @brief Enables preemption for a task.
 *
 * @param xTask The handle of the task to enable preemption. Passing NULL
 * enables preemption for the calling task.
 *
 * Example usage:
 *
 * void vTaskCode( void *pvParameters )
 * {
 *     // Silence warnings about unused parameters.
 *     ( void ) pvParameters;
 *
 *     for( ;; )
 *     {
 *         // ... Perform some function here.
 *
 *         // Disable preemption for this task.
 *         vTaskPreemptionDisable( NULL );
 *
 *         // The task will not be preempted when it is executing in this portion ...
 *
 *         // ... until the preemption is enabled again.
 *         vTaskPreemptionEnable( NULL );
 *
 *         // The task can be preempted when it is executing in this portion.
 *     }
 * }
 */
void vTaskPreemptionEnable( const TaskHandle_t xTask );

/*-----------------------------------------------------------
* SCHEDULER CONTROL
*----------------------------------------------------------*/

/**
 * task. h
 * <pre>
 * void vTaskStartScheduler( void );
 * </pre>
 *
 * Starts the real time kernel tick processing.  After calling the kernel
 * has control over which tasks are executed and when.
 *
 * See the demo application file main.c for an example of creating
 * tasks and starting the kernel.
 *
 * Example usage:
 * <pre>
 * void vAFunction( void )
 * {
 *   // Create at least one task before starting the kernel.
 *   xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
 *
 *   // Start the real time kernel with preemption.
 *   vTaskStartScheduler ();
 *
 *   // Will not get here unless a task calls vTaskEndScheduler ()
 * }
 * </pre>
 *
 * \defgroup vTaskStartScheduler vTaskStartScheduler
 * \ingroup SchedulerControl
 */
void vTaskStartScheduler( void ) ;

/**
 * task. h
 * <pre>
 * void vTaskEndScheduler( void );
 * </pre>
 *
 * NOTE:  At the time of writing only the x86 real mode port, which runs on a PC
 * in place of DOS, implements this function.
 *
 * Stops the real time kernel tick.  All created tasks will be automatically
 * deleted and multitasking (either preemptive or cooperative) will
 * stop.  Execution then resumes from the point where vTaskStartScheduler ()
 * was called, as if vTaskStartScheduler () had just returned.
 *
 * See the demo application file main. c in the demo/PC directory for an
 * example that uses vTaskEndScheduler ().
 *
 * vTaskEndScheduler () requires an exit function to be defined within the
 * portable layer (see vPortEndScheduler () in port. c for the PC port).  This
 * performs hardware specific operations such as stopping the kernel tick.
 *
 * vTaskEndScheduler () will cause all of the resources allocated by the
 * kernel to be freed - but will not free resources allocated by application
 * tasks.
 *
 * Example usage:
 * <pre>
 * void vTaskCode( void * pvParameters )
 * {
 *   for( ;; )
 *   {
 *       // Task code goes here.
 *
 *       // At some point we want to end the real time kernel processing
 *       // so call ...
 *       vTaskEndScheduler ();
 *   }
 * }
 *
 * void vAFunction( void )
 * {
 *   // Create at least one task before starting the kernel.
 *   xTaskCreate( vTaskCode, "NAME", STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
 *
 *   // Start the real time kernel with preemption.
 *   vTaskStartScheduler ();
 *
 *   // Will only get here when the vTaskCode () task has called
 *   // vTaskEndScheduler ().  When we get here we are back to single task
 *   // execution.
 * }
 * </pre>
 *
 * \defgroup vTaskEndScheduler vTaskEndScheduler
 * \ingroup SchedulerControl
 */
void vTaskEndScheduler( void ) ;

/**
 * task. h
 * <pre>
 * void vTaskSuspendAll( void );
 * </pre>
 *
 * Suspends the scheduler without disabling interrupts.  Context switches will
 * not occur while the scheduler is suspended.
 *
 * After calling vTaskSuspendAll () the calling task will continue to execute
 * without risk of being swapped out until a call to xTaskResumeAll () has been
 * made.
 *
 * API functions that have the potential to cause a context switch (for example,
 * xTaskDelayUntil(), xQueueSend(), etc.) must not be called while the scheduler
 * is suspended.
 *
 * Example usage:
 * <pre>
 * void vTask1( void * pvParameters )
 * {
 *   for( ;; )
 *   {
 *       // Task code goes here.
 *
 *       // ...
 *
 *       // At some point the task wants to perform a long operation during
 *       // which it does not want to get swapped out.  It cannot use
 *       // taskENTER_CRITICAL ()/taskEXIT_CRITICAL () as the length of the
 *       // operation may cause interrupts to be missed - including the
 *       // ticks.
 *
 *       // Prevent the real time kernel swapping out the task.
 *       vTaskSuspendAll ();
 *
 *       // Perform the operation here.  There is no need to use critical
 *       // sections as we have all the microcontroller processing time.
 *       // During this time interrupts will still operate and the kernel
 *       // tick count will be maintained.
 *
 *       // ...
 *
 *       // The operation is complete.  Restart the kernel.
 *       xTaskResumeAll ();
 *   }
 * }
 * </pre>
 * \defgroup vTaskSuspendAll vTaskSuspendAll
 * \ingroup SchedulerControl
 */
void vTaskSuspendAll( void ) ;

/**
 * task. h
 * <pre>
 * BaseType_t xTaskResumeAll( void );
 * </pre>
 *
 * Resumes scheduler activity after it was suspended by a call to
 * vTaskSuspendAll().
 *
 * xTaskResumeAll() only resumes the scheduler.  It does not unsuspend tasks
 * that were previously suspended by a call to vTaskSuspend().
 *
 * @return If resuming the scheduler caused a context switch then pdTRUE is
 *         returned, otherwise pdFALSE is returned.
 *
 * Example usage:
 * <pre>
 * void vTask1( void * pvParameters )
 * {
 *   for( ;; )
 *   {
 *       // Task code goes here.
 *
 *       // ...
 *
 *       // At some point the task wants to perform a long operation during
 *       // which it does not want to get swapped out.  It cannot use
 *       // taskENTER_CRITICAL ()/taskEXIT_CRITICAL () as the length of the
 *       // operation may cause interrupts to be missed - including the
 *       // ticks.
 *
 *       // Prevent the real time kernel swapping out the task.
 *       vTaskSuspendAll ();
 *
 *       // Perform the operation here.  There is no need to use critical
 *       // sections as we have all the microcontroller processing time.
 *       // During this time interrupts will still operate and the real
 *       // time kernel tick count will be maintained.
 *
 *       // ...
 *
 *       // The operation is complete.  Restart the kernel.  We want to force
 *       // a context switch - but there is no point if resuming the scheduler
 *       // caused a context switch already.
 *       if( !xTaskResumeAll () )
 *       {
 *            taskYIELD ();
 *       }
 *   }
 * }
 * </pre>
 * \defgroup xTaskResumeAll xTaskResumeAll
 * \ingroup SchedulerControl
 */
BaseType_t xTaskResumeAll( void ) ;

/*-----------------------------------------------------------
* TASK UTILITIES
*----------------------------------------------------------*/

/**
 * task. h
 * <PRE>TickType_t xTaskGetTickCount( void );</PRE>
 *
 * @return The count of ticks since vTaskStartScheduler was called.
 *
 * \defgroup xTaskGetTickCount xTaskGetTickCount
 * \ingroup TaskUtils
 */
TickType_t xTaskGetTickCount( void ) ;

/**
 * task. h
 * <PRE>TickType_t xTaskGetTickCountFromISR( void );</PRE>
 *
 * @return The count of ticks since vTaskStartScheduler was called.
 *
 * This is a version of xTaskGetTickCount() that is safe to be called from an
 * ISR - provided that TickType_t is the natural word size of the
 * microcontroller being used or interrupt nesting is either not supported or
 * not being used.
 *
 * \defgroup xTaskGetTickCountFromISR xTaskGetTickCountFromISR
 * \ingroup TaskUtils
 */
TickType_t xTaskGetTickCountFromISR( void ) ;

/**
 * task. h
 * <PRE>uint16_t uxTaskGetNumberOfTasks( void );</PRE>
 *
 * @return The number of tasks that the real time kernel is currently managing.
 * This includes all ready, blocked and suspended tasks.  A task that
 * has been deleted but not yet freed by the idle task will also be
 * included in the count.
 *
 * \defgroup uxTaskGetNumberOfTasks uxTaskGetNumberOfTasks
 * \ingroup TaskUtils
 */
UBaseType_t uxTaskGetNumberOfTasks( void ) ;

/**
 * task. h
 * <PRE>char *pcTaskGetName( TaskHandle_t xTaskToQuery );</PRE>
 *
 * @return The text (human readable) name of the task referenced by the handle
 * xTaskToQuery.  A task can query its own name by either passing in its own
 * handle, or by setting xTaskToQuery to NULL.
 *
 * \defgroup pcTaskGetName pcTaskGetName
 * \ingroup TaskUtils
 */
char * pcTaskGetName( TaskHandle_t xTaskToQuery ) ; /*lint !e971 Unqualified char types are allowed for strings and single characters only. */

/**
 * task. h
 * <PRE>TaskHandle_t xTaskGetHandle( const char *pcNameToQuery );</PRE>
 *
 * NOTE:  This function takes a relatively long time to complete and should be
 * used sparingly.
 *
 * @return The handle of the task that has the human readable name pcNameToQuery.
 * NULL is returned if no matching name is found.  INCLUDE_xTaskGetHandle
 * must be set to 1 in FreeRTOSConfig.h for pcTaskGetHandle() to be available.
 *
 * \defgroup pcTaskGetHandle pcTaskGetHandle
 * \ingroup TaskUtils
 */
TaskHandle_t xTaskGetHandle( const char * pcNameToQuery ) ; /*lint !e971 Unqualified char types are allowed for strings and single characters only. */

/**
 * task.h
 * <PRE>UBaseType_t uxTaskGetStackHighWaterMark( TaskHandle_t xTask );</PRE>
 *
 * INCLUDE_uxTaskGetStackHighWaterMark must be set to 1 in FreeRTOSConfig.h for
 * this function to be available.
 *
 * Returns the high water mark of the stack associated with xTask.  That is,
 * the minimum free stack space there has been (in words, so on a 32 bit machine
 * a value of 1 means 4 bytes) since the task started.  The smaller the returned
 * number the closer the task has come to overflowing its stack.
 *
 * uxTaskGetStackHighWaterMark() and uxTaskGetStackHighWaterMark2() are the
 * same except for their return type.  Using configSTACK_DEPTH_TYPE allows the
 * user to determine the return type.  It gets around the problem of the value
 * overflowing on 8-bit types without breaking backward compatibility for
 * applications that expect an 8-bit return type.
 *
 * @param xTask Handle of the task associated with the stack to be checked.
 * Set xTask to NULL to check the stack of the calling task.
 *
 * @return The smallest amount of free stack space there has been (in words, so
 * actual spaces on the stack rather than bytes) since the task referenced by
 * xTask was created.
 */
UBaseType_t uxTaskGetStackHighWaterMark( TaskHandle_t xTask ) ;

/**
 * task.h
 * <PRE>configSTACK_DEPTH_TYPE uxTaskGetStackHighWaterMark2( TaskHandle_t xTask );</PRE>
 *
 * INCLUDE_uxTaskGetStackHighWaterMark2 must be set to 1 in FreeRTOSConfig.h for
 * this function to be available.
 *
 * Returns the high water mark of the stack associated with xTask.  That is,
 * the minimum free stack space there has been (in words, so on a 32 bit machine
 * a value of 1 means 4 bytes) since the task started.  The smaller the returned
 * number the closer the task has come to overflowing its stack.
 *
 * uxTaskGetStackHighWaterMark() and uxTaskGetStackHighWaterMark2() are the
 * same except for their return type.  Using configSTACK_DEPTH_TYPE allows the
 * user to determine the return type.  It gets around the problem of the value
 * overflowing on 8-bit types without breaking backward compatibility for
 * applications that expect an 8-bit return type.
 *
 * @param xTask Handle of the task associated with the stack to be checked.
 * Set xTask to NULL to check the stack of the calling task.
 *
 * @return The smallest amount of free stack space there has been (in words, so
 * actual spaces on the stack rather than bytes) since the task referenced by
 * xTask was created.
 */
uint32_t uxTaskGetStackHighWaterMark2( TaskHandle_t xTask ) ;

/* When using trace macros it is sometimes necessary to include task.h before
 * FreeRTOS.h.  When this is done TaskHookFunction_t will not yet have been defined,
 * so the following two prototypes will cause a compilation error.  This can be
 * fixed by simply guarding against the inclusion of these two prototypes unless
 * they are explicitly required by the configUSE_APPLICATION_TASK_TAG configuration
 *ant. */
// # 1838 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h"
/* Each task contains an array of pointers that is dimensioned by the
 * configNUM_THREAD_LOCAL_STORAGE_POINTERS setting in FreeRTOSConfig.h.  The
 * kernel does not use the pointers itself, so the application writer can use
 * the pointers for any purpose they wish.  The following two functions are
 * used to set and query a pointer respectively. */
    void vTaskSetThreadLocalStoragePointer( TaskHandle_t xTaskToSet,
                                            BaseType_t xIndex,
                                            void * pvValue ) ;
    void * pvTaskGetThreadLocalStoragePointer( TaskHandle_t xTaskToQuery,
                                               BaseType_t xIndex ) ;





     /**
      * task.h
      * <pre>void vApplicationStackOverflowHook( TaskHandle_t xTask char *pcTaskName); </pre>
      *
      * The application stack overflow hook is called when a stack overflow is detected for a task.
      *
      * Details on stack overflow detection can be found here: https://www.FreeRTOS.org/Stacks-and-stack-overflow-checking.html
      *
      * @param xTask the task that just exceeded its stack boundaries.
      * @param pcTaskName A character string containing the name of the offending task.
      */
     void vApplicationStackOverflowHook( TaskHandle_t xTask,
                                               char * pcTaskName );




    /**
     *  task.h
     *  <pre>void vApplicationTickHook( void ); </pre>
     *
     * This hook function is called in the system tick handler after any OS work is completed.
     */
    void vApplicationTickHook( void ); /*lint !e526 Symbol not defined as it is an application callback. */
// # 1897 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/task.h"
/**
 * task.h
 * <pre>
 * BaseType_t xTaskCallApplicationTaskHook( TaskHandle_t xTask, void *pvParameter );
 * </pre>
 *
 * Calls the hook function associated with xTask.  Passing xTask as NULL has
 * the effect of calling the Running tasks (the calling task) hook function.
 *
 * pvParameter is passed to the hook function for the task to interpret as it
 * wants.  The return value is the value returned by the task hook function
 * registered by the user.
 */
BaseType_t xTaskCallApplicationTaskHook( TaskHandle_t xTask,
                                         void * pvParameter ) ;

/**
 * xTaskGetIdleTaskHandle() is only available if
 * INCLUDE_xTaskGetIdleTaskHandle is set to 1 in FreeRTOSConfig.h.
 *
 * Simply returns a pointer to the array of idle task handles.
 * It is not valid to call xTaskGetIdleTaskHandle() before the scheduler has been started.
 */
TaskHandle_t *xTaskGetIdleTaskHandle( void ) ;

/**
 * configUSE_TRACE_FACILITY must be defined as 1 in FreeRTOSConfig.h for
 * uxTaskGetSystemState() to be available.
 *
 * uxTaskGetSystemState() populates an TaskStatus_t structure for each task in
 * the system.  TaskStatus_t structures contain, among other things, members
 * for the task handle, task name, task priority, task state, and total amount
 * of run time consumed by the task.  See the TaskStatus_t structure
 * definition in this file for the full member list.
 *
 * NOTE:  This function is intended for debugging use only as its use results in
 * the scheduler remaining suspended for an extended period.
 *
 * @param pxTaskStatusArray A pointer to an array of TaskStatus_t structures.
 * The array must contain at least one TaskStatus_t structure for each task
 * that is under the control of the RTOS.  The number of tasks under the control
 * of the RTOS can be determined using the uxTaskGetNumberOfTasks() API function.
 *
 * @param uxArraySize The size of the array pointed to by the pxTaskStatusArray
 * parameter.  The size is specified as the number of indexes in the array, or
 * the number of TaskStatus_t structures contained in the array, not by the
 * number of bytes in the array.
 *
 * @param pulTotalRunTime If configGENERATE_RUN_TIME_STATS is set to 1 in
 * FreeRTOSConfig.h then *pulTotalRunTime is set by uxTaskGetSystemState() to the
 * total run time (as defined by the run time stats clock, see
 * https://www.FreeRTOS.org/rtos-run-time-stats.html) since the target booted.
 * pulTotalRunTime can be set to NULL to omit the total run time information.
 *
 * @return The number of TaskStatus_t structures that were populated by
 * uxTaskGetSystemState().  This should equal the number returned by the
 * uxTaskGetNumberOfTasks() API function, but will be zero if the value passed
 * in the uxArraySize parameter was too small.
 *
 * Example usage:
 * <pre>
 *  // This example demonstrates how a human readable table of run time stats
 *  // information is generated from raw data provided by uxTaskGetSystemState().
 *  // The human readable table is written to pcWriteBuffer
 *  void vTaskGetRunTimeStats( char *pcWriteBuffer )
 *  {
 *  TaskStatus_t *pxTaskStatusArray;
 *  volatile UBaseType_t uxArraySize, x;
 *  uint32_t ulTotalRunTime, ulStatsAsPercentage;
 *
 *      // Make sure the write buffer does not contain a string.
 * pcWriteBuffer = 0x00;
 *
 *      // Take a snapshot of the number of tasks in case it changes while this
 *      // function is executing.
 *      uxArraySize = uxTaskGetNumberOfTasks();
 *
 *      // Allocate a TaskStatus_t structure for each task.  An array could be
 *      // allocated statically at compile time.
 *      pxTaskStatusArray = pvPortMalloc( uxArraySize * sizeof( TaskStatus_t ) );
 *
 *      if( pxTaskStatusArray != NULL )
 *      {
 *          // Generate raw status information about each task.
 *          uxArraySize = uxTaskGetSystemState( pxTaskStatusArray, uxArraySize, &ulTotalRunTime );
 *
 *          // For percentage calculations.
 *          ulTotalRunTime /= 100UL;
 *
 *          // Avoid divide by zero errors.
 *          if( ulTotalRunTime > 0 )
 *          {
 *              // For each populated position in the pxTaskStatusArray array,
 *              // format the raw data as human readable ASCII data
 *              for( x = 0; x < uxArraySize; x++ )
 *              {
 *                  // What percentage of the total run time has the task used?
 *                  // This will always be rounded down to the nearest integer.
 *                  // ulTotalRunTimeDiv100 has already been divided by 100.
 *                  ulStatsAsPercentage = pxTaskStatusArray[ x ].ulRunTimeCounter / ulTotalRunTime;
 *
 *                  if( ulStatsAsPercentage > 0UL )
 *                  {
 *                      sprintf( pcWriteBuffer, "%s\t\t%lu\t\t%lu%%\r\n", pxTaskStatusArray[ x ].pcTaskName, pxTaskStatusArray[ x ].ulRunTimeCounter, ulStatsAsPercentage );
 *                  }
 *                  else
 *                  {
 *                      // If the percentage is zero here then the task has
 *                      // consumed less than 1% of the total run time.
 *                      sprintf( pcWriteBuffer, "%s\t\t%lu\t\t<1%%\r\n", pxTaskStatusArray[ x ].pcTaskName, pxTaskStatusArray[ x ].ulRunTimeCounter );
 *                  }
 *
 *                  pcWriteBuffer += strlen( ( char * ) pcWriteBuffer );
 *              }
 *          }
 *
 *          // The array is no longer needed, free the memory it consumes.
 *          vPortFree( pxTaskStatusArray );
 *      }
 *  }
 *  </pre>
 */
UBaseType_t uxTaskGetSystemState( TaskStatus_t * pxTaskStatusArray,
                                  const UBaseType_t uxArraySize,
                                  uint32_t * pulTotalRunTime ) ;

/**
 * task. h
 * <PRE>void vTaskList( char *pcWriteBuffer );</PRE>
 *
 * configUSE_TRACE_FACILITY and configUSE_STATS_FORMATTING_FUNCTIONS must
 * both be defined as 1 for this function to be available.  See the
 * configuration section of the FreeRTOS.org website for more information.
 *
 * NOTE 1: This function will disable interrupts for its duration.  It is
 * not intended for normal application runtime use but as a debug aid.
 *
 * Lists all the current tasks, along with their current state and stack
 * usage high water mark.
 *
 * Tasks are reported as blocked ('B'), ready ('R'), deleted ('D') or
 * suspended ('S').
 *
 * PLEASE NOTE:
 *
 * This function is provided for convenience only, and is used by many of the
 * demo applications.  Do not consider it to be part of the scheduler.
 *
 * vTaskList() calls uxTaskGetSystemState(), then formats part of the
 * uxTaskGetSystemState() output into a human readable table that displays task:
 * names, states, priority, stack usage and task number.
 * Stack usage specified as the number of unused StackType_t words stack can hold
 * on top of stack - not the number of bytes.
 *
 * vTaskList() has a dependency on the sprintf() C library function that might
 * bloat the code size, use a lot of stack, and provide different results on
 * different platforms.  An alternative, tiny, third party, and limited
 * functionality implementation of sprintf() is provided in many of the
 * FreeRTOS/Demo sub-directories in a file called printf-stdarg.c (note
 * printf-stdarg.c does not provide a full snprintf() implementation!).
 *
 * It is recommended that production systems call uxTaskGetSystemState()
 * directly to get access to raw stats data, rather than indirectly through a
 * call to vTaskList().
 *
 * @param pcWriteBuffer A buffer into which the above mentioned details
 * will be written, in ASCII form.  This buffer is assumed to be large
 * enough to contain the generated report.  Approximately 40 bytes per
 * task should be sufficient.
 *
 * \defgroup vTaskList vTaskList
 * \ingroup TaskUtils
 */
void vTaskList( char * pcWriteBuffer ) ; /*lint !e971 Unqualified char types are allowed for strings and single characters only. */

/**
 * task. h
 * <PRE>void vTaskGetRunTimeStats( char *pcWriteBuffer );</PRE>
 *
 * configGENERATE_RUN_TIME_STATS and configUSE_STATS_FORMATTING_FUNCTIONS
 * must both be defined as 1 for this function to be available.  The application
 * must also then provide definitions for
 * portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() and portGET_RUN_TIME_COUNTER_VALUE()
 * to configure a peripheral timer/counter and return the timers current count
 * value respectively.  The counter should be at least 10 times the frequency of
 * the tick count.
 *
 * NOTE 1: This function will disable interrupts for its duration.  It is
 * not intended for normal application runtime use but as a debug aid.
 *
 * Setting configGENERATE_RUN_TIME_STATS to 1 will result in a total
 * accumulated execution time being stored for each task.  The resolution
 * of the accumulated time value depends on the frequency of the timer
 * configured by the portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() macro.
 * Calling vTaskGetRunTimeStats() writes the total execution time of each
 * task into a buffer, both as an absolute count value and as a percentage
 * of the total system execution time.
 *
 * NOTE 2:
 *
 * This function is provided for convenience only, and is used by many of the
 * demo applications.  Do not consider it to be part of the scheduler.
 *
 * vTaskGetRunTimeStats() calls uxTaskGetSystemState(), then formats part of the
 * uxTaskGetSystemState() output into a human readable table that displays the
 * amount of time each task has spent in the Running state in both absolute and
 * percentage terms.
 *
 * vTaskGetRunTimeStats() has a dependency on the sprintf() C library function
 * that might bloat the code size, use a lot of stack, and provide different
 * results on different platforms.  An alternative, tiny, third party, and
 * limited functionality implementation of sprintf() is provided in many of the
 * FreeRTOS/Demo sub-directories in a file called printf-stdarg.c (note
 * printf-stdarg.c does not provide a full snprintf() implementation!).
 *
 * It is recommended that production systems call uxTaskGetSystemState() directly
 * to get access to raw stats data, rather than indirectly through a call to
 * vTaskGetRunTimeStats().
 *
 * @param pcWriteBuffer A buffer into which the execution times will be
 * written, in ASCII form.  This buffer is assumed to be large enough to
 * contain the generated report.  Approximately 40 bytes per task should
 * be sufficient.
 *
 * \defgroup vTaskGetRunTimeStats vTaskGetRunTimeStats
 * \ingroup TaskUtils
 */
void vTaskGetRunTimeStats( char * pcWriteBuffer ) ; /*lint !e971 Unqualified char types are allowed for strings and single characters only. */

/**
 * task. h
 * <PRE>uint32_t ulTaskGetIdleRunTimeCounter( void );</PRE>
 *
 * configGENERATE_RUN_TIME_STATS and configUSE_STATS_FORMATTING_FUNCTIONS
 * must both be defined as 1 for this function to be available.  The application
 * must also then provide definitions for
 * portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() and portGET_RUN_TIME_COUNTER_VALUE()
 * to configure a peripheral timer/counter and return the timers current count
 * value respectively.  The counter should be at least 10 times the frequency of
 * the tick count.
 *
 * Setting configGENERATE_RUN_TIME_STATS to 1 will result in a total
 * accumulated execution time being stored for each task.  The resolution
 * of the accumulated time value depends on the frequency of the timer
 * configured by the portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() macro.
 * While uxTaskGetSystemState() and vTaskGetRunTimeStats() writes the total
 * execution time of each task into a buffer, ulTaskGetIdleRunTimeCounter()
 * returns the total execution time of just the idle task.
 *
 * @return The total run time of the idle task.  This is the amount of time the
 * idle task has actually been executing.  The unit of time is dependent on the
 * frequency configured using the portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() and
 * portGET_RUN_TIME_COUNTER_VALUE() macros.
 *
 * \defgroup ulTaskGetIdleRunTimeCounter ulTaskGetIdleRunTimeCounter
 * \ingroup TaskUtils
 */
uint32_t ulTaskGetIdleRunTimeCounter( void ) ;

/**
 * task. h
 * <PRE>BaseType_t xTaskNotifyIndexed( TaskHandle_t xTaskToNotify, UBaseType_t uxIndexToNotify, uint32_t ulValue, eNotifyAction eAction );</PRE>
 * <PRE>BaseType_t xTaskNotify( TaskHandle_t xTaskToNotify, uint32_t ulValue, eNotifyAction eAction );</PRE>
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for details.
 *
 * configUSE_TASK_NOTIFICATIONS must be undefined or defined as 1 for these
 * functions to be available.
 *
 * Sends a direct to task notification to a task, with an optional value and
 * action.
 *
 * Each task has a private array of "notification values" (or 'notifications'),
 * each of which is a 32-bit unsigned integer (uint32_t).  The constant
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the
 * array, and (for backward compatibility) defaults to 1 if left undefined.
 * Prior to FreeRTOS V10.4.0 there was only one notification value per task.
 *
 * Events can be sent to a task using an intermediary object.  Examples of such
 * objects are queues, semaphores, mutexes and event groups.  Task notifications
 * are a method of sending an event directly to a task without the need for such
 * an intermediary object.
 *
 * A notification sent to a task can optionally perform an action, such as
 * update, overwrite or increment one of the task's notification values.  In
 * that way task notifications can be used to send data to a task, or be used as
 * light weight and fast binary or counting semaphores.
 *
 * A task can use xTaskNotifyWaitIndexed() or ulTaskNotifyTakeIndexed() to
 * [optionally] block to wait for a notification to be pending.  The task does
 * not consume any CPU time while it is in the Blocked state.
 *
 * A notification sent to a task will remain pending until it is cleared by the
 * task calling xTaskNotifyWaitIndexed() or ulTaskNotifyTakeIndexed() (or their
 * un-indexed equivalents).  If the task was already in the Blocked state to
 * wait for a notification when the notification arrives then the task will
 * automatically be removed from the Blocked state (unblocked) and the
 * notification cleared.
 *
 * **NOTE** Each notification within the array operates independently - a task
 * can only block on one notification within the array at a time and will not be
 * unblocked by a notification sent to any other array index.
 *
 * Backward compatibility information:
 * Prior to FreeRTOS V10.4.0 each task had a single "notification value", and
 * all task notification API functions operated on that value. Replacing the
 * single notification value with an array of notification values necessitated a
 * new set of API functions that could address specific notifications within the
 * array.  xTaskNotify() is the original API function, and remains backward
 * compatible by always operating on the notification value at index 0 in the
 * array. Calling xTaskNotify() is equivalent to calling xTaskNotifyIndexed()
 * with the uxIndexToNotify parameter set to 0.
 *
 * @param xTaskToNotify The handle of the task being notified.  The handle to a
 * task can be returned from the xTaskCreate() API function used to create the
 * task, and the handle of the currently running task can be obtained by calling
 * xTaskGetCurrentTaskHandle().
 *
 * @param uxIndexToNotify The index within the target task's array of
 * notification values to which the notification is to be sent.  uxIndexToNotify
 * must be less than configTASK_NOTIFICATION_ARRAY_ENTRIES.  xTaskNotify() does
 * not have this parameter and always sends notifications to index 0.
 *
 * @param ulValue Data that can be sent with the notification.  How the data is
 * used depends on the value of the eAction parameter.
 *
 * @param eAction Specifies how the notification updates the task's notification
 * value, if at all.  Valid values for eAction are as follows:
 *
 * eSetBits -
 * The target notification value is bitwise ORed with ulValue.
 * xTaskNotifyIndexed() always returns pdPASS in this case.
 *
 * eIncrement -
 * The target notification value is incremented.  ulValue is not used and
 * xTaskNotifyIndexed() always returns pdPASS in this case.
 *
 * eSetValueWithOverwrite -
 * The target notification value is set to the value of ulValue, even if the
 * task being notified had not yet processed the previous notification at the
 * same array index (the task already had a notification pending at that index).
 * xTaskNotifyIndexed() always returns pdPASS in this case.
 *
 * eSetValueWithoutOverwrite -
 * If the task being notified did not already have a notification pending at the
 * same array index then the target notification value is set to ulValue and
 * xTaskNotifyIndexed() will return pdPASS.  If the task being notified already
 * had a notification pending at the same array index then no action is
 * performed and pdFAIL is returned.
 *
 * eNoAction -
 * The task receives a notification at the specified array index without the
 * notification value at that index being updated.  ulValue is not used and
 * xTaskNotifyIndexed() always returns pdPASS in this case.
 *
 * pulPreviousNotificationValue -
 * Can be used to pass out the subject task's notification value before any
 * bits are modified by the notify function.
 *
 * @return Dependent on the value of eAction.  See the description of the
 * eAction parameter.
 *
 * \defgroup xTaskNotifyIndexed xTaskNotifyIndexed
 * \ingroup TaskNotifications
 */
BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
                               UBaseType_t uxIndexToNotify,
                               uint32_t ulValue,
                               eNotifyAction eAction,
                               uint32_t * pulPreviousNotificationValue ) ;





/**
 * task. h
 * <PRE>BaseType_t xTaskNotifyAndQueryIndexed( TaskHandle_t xTaskToNotify, UBaseType_t uxIndexToNotify, uint32_t ulValue, eNotifyAction eAction, uint32_t *pulPreviousNotifyValue );</PRE>
 * <PRE>BaseType_t xTaskNotifyAndQuery( TaskHandle_t xTaskToNotify, uint32_t ulValue, eNotifyAction eAction, uint32_t *pulPreviousNotifyValue );</PRE>
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for details.
 *
 * xTaskNotifyAndQueryIndexed() performs the same operation as
 * xTaskNotifyIndexed() with the addition that it also returns the subject
 * task's prior notification value (the notification value at the time the
 * function is called rather than when the function returns) in the additional
 * pulPreviousNotifyValue parameter.
 *
 * xTaskNotifyAndQuery() performs the same operation as xTaskNotify() with the
 * addition that it also returns the subject task's prior notification value
 * (the notification value as it was at the time the function is called, rather
 * than when the function returns) in the additional pulPreviousNotifyValue
 * parameter.
 *
 * \defgroup xTaskNotifyAndQueryIndexed xTaskNotifyAndQueryIndexed
 * \ingroup TaskNotifications
 */





/**
 * task. h
 * <PRE>BaseType_t xTaskNotifyIndexedFromISR( TaskHandle_t xTaskToNotify, UBaseType_t uxIndexToNotify, uint32_t ulValue, eNotifyAction eAction, BaseType_t *pxHigherPriorityTaskWoken );</PRE>
 * <PRE>BaseType_t xTaskNotifyFromISR( TaskHandle_t xTaskToNotify, uint32_t ulValue, eNotifyAction eAction, BaseType_t *pxHigherPriorityTaskWoken );</PRE>
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for details.
 *
 * configUSE_TASK_NOTIFICATIONS must be undefined or defined as 1 for these
 * functions to be available.
 *
 * A version of xTaskNotifyIndexed() that can be used from an interrupt service
 * routine (ISR).
 *
 * Each task has a private array of "notification values" (or 'notifications'),
 * each of which is a 32-bit unsigned integer (uint32_t).  The constant
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the
 * array, and (for backward compatibility) defaults to 1 if left undefined.
 * Prior to FreeRTOS V10.4.0 there was only one notification value per task.
 *
 * Events can be sent to a task using an intermediary object.  Examples of such
 * objects are queues, semaphores, mutexes and event groups.  Task notifications
 * are a method of sending an event directly to a task without the need for such
 * an intermediary object.
 *
 * A notification sent to a task can optionally perform an action, such as
 * update, overwrite or increment one of the task's notification values.  In
 * that way task notifications can be used to send data to a task, or be used as
 * light weight and fast binary or counting semaphores.
 *
 * A task can use xTaskNotifyWaitIndexed() to [optionally] block to wait for a
 * notification to be pending, or ulTaskNotifyTakeIndexed() to [optionally] block
 * to wait for a notification value to have a non-zero value.  The task does
 * not consume any CPU time while it is in the Blocked state.
 *
 * A notification sent to a task will remain pending until it is cleared by the
 * task calling xTaskNotifyWaitIndexed() or ulTaskNotifyTakeIndexed() (or their
 * un-indexed equivalents).  If the task was already in the Blocked state to
 * wait for a notification when the notification arrives then the task will
 * automatically be removed from the Blocked state (unblocked) and the
 * notification cleared.
 *
 * **NOTE** Each notification within the array operates independently - a task
 * can only block on one notification within the array at a time and will not be
 * unblocked by a notification sent to any other array index.
 *
 * Backward compatibility information:
 * Prior to FreeRTOS V10.4.0 each task had a single "notification value", and
 * all task notification API functions operated on that value. Replacing the
 * single notification value with an array of notification values necessitated a
 * new set of API functions that could address specific notifications within the
 * array.  xTaskNotifyFromISR() is the original API function, and remains
 * backward compatible by always operating on the notification value at index 0
 * within the array. Calling xTaskNotifyFromISR() is equivalent to calling
 * xTaskNotifyIndexedFromISR() with the uxIndexToNotify parameter set to 0.
 *
 * @param uxIndexToNotify The index within the target task's array of
 * notification values to which the notification is to be sent.  uxIndexToNotify
 * must be less than configTASK_NOTIFICATION_ARRAY_ENTRIES.  xTaskNotifyFromISR()
 * does not have this parameter and always sends notifications to index 0.
 *
 * @param xTaskToNotify The handle of the task being notified.  The handle to a
 * task can be returned from the xTaskCreate() API function used to create the
 * task, and the handle of the currently running task can be obtained by calling
 * xTaskGetCurrentTaskHandle().
 *
 * @param ulValue Data that can be sent with the notification.  How the data is
 * used depends on the value of the eAction parameter.
 *
 * @param eAction Specifies how the notification updates the task's notification
 * value, if at all.  Valid values for eAction are as follows:
 *
 * eSetBits -
 * The task's notification value is bitwise ORed with ulValue.  xTaskNotify()
 * always returns pdPASS in this case.
 *
 * eIncrement -
 * The task's notification value is incremented.  ulValue is not used and
 * xTaskNotify() always returns pdPASS in this case.
 *
 * eSetValueWithOverwrite -
 * The task's notification value is set to the value of ulValue, even if the
 * task being notified had not yet processed the previous notification (the
 * task already had a notification pending).  xTaskNotify() always returns
 * pdPASS in this case.
 *
 * eSetValueWithoutOverwrite -
 * If the task being notified did not already have a notification pending then
 * the task's notification value is set to ulValue and xTaskNotify() will
 * return pdPASS.  If the task being notified already had a notification
 * pending then no action is performed and pdFAIL is returned.
 *
 * eNoAction -
 * The task receives a notification without its notification value being
 * updated.  ulValue is not used and xTaskNotify() always returns pdPASS in
 * this case.
 *
 * @param pxHigherPriorityTaskWoken  xTaskNotifyFromISR() will set
 * *pxHigherPriorityTaskWoken to pdTRUE if sending the notification caused the
 * task to which the notification was sent to leave the Blocked state, and the
 * unblocked task has a priority higher than the currently running task.  If
 * xTaskNotifyFromISR() sets this value to pdTRUE then a context switch should
 * be requested before the interrupt is exited.  How a context switch is
 * requested from an ISR is dependent on the port - see the documentation page
 * for the port in use.
 *
 * @return Dependent on the value of eAction.  See the description of the
 * eAction parameter.
 *
 * \defgroup xTaskNotifyIndexedFromISR xTaskNotifyIndexedFromISR
 * \ingroup TaskNotifications
 */
BaseType_t xTaskGenericNotifyFromISR( TaskHandle_t xTaskToNotify,
                                      UBaseType_t uxIndexToNotify,
                                      uint32_t ulValue,
                                      eNotifyAction eAction,
                                      uint32_t * pulPreviousNotificationValue,
                                      BaseType_t * pxHigherPriorityTaskWoken ) ;





/**
 * task. h
 * <PRE>BaseType_t xTaskNotifyAndQueryIndexedFromISR( TaskHandle_t xTaskToNotify, UBaseType_t uxIndexToNotify, uint32_t ulValue, eNotifyAction eAction, uint32_t *pulPreviousNotificationValue, BaseType_t *pxHigherPriorityTaskWoken );</PRE>
 * <PRE>BaseType_t xTaskNotifyAndQueryFromISR( TaskHandle_t xTaskToNotify, uint32_t ulValue, eNotifyAction eAction, uint32_t *pulPreviousNotificationValue, BaseType_t *pxHigherPriorityTaskWoken );</PRE>
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for details.
 *
 * xTaskNotifyAndQueryIndexedFromISR() performs the same operation as
 * xTaskNotifyIndexedFromISR() with the addition that it also returns the
 * subject task's prior notification value (the notification value at the time
 * the function is called rather than at the time the function returns) in the
 * additional pulPreviousNotifyValue parameter.
 *
 * xTaskNotifyAndQueryFromISR() performs the same operation as
 * xTaskNotifyFromISR() with the addition that it also returns the subject
 * task's prior notification value (the notification value at the time the
 * function is called rather than at the time the function returns) in the
 * additional pulPreviousNotifyValue parameter.
 *
 * \defgroup xTaskNotifyAndQueryIndexedFromISR xTaskNotifyAndQueryIndexedFromISR
 * \ingroup TaskNotifications
 */





/**
 * task. h
 * <pre>
 * BaseType_t xTaskNotifyWaitIndexed( UBaseType_t uxIndexToWaitOn, uint32_t ulBitsToClearOnEntry, uint32_t ulBitsToClearOnExit, uint32_t *pulNotificationValue, TickType_t xTicksToWait );
 *
 * BaseType_t xTaskNotifyWait( uint32_t ulBitsToClearOnEntry, uint32_t ulBitsToClearOnExit, uint32_t *pulNotificationValue, TickType_t xTicksToWait );
 * </pre>
 *
 * Waits for a direct to task notification to be pending at a given index within
 * an array of direct to task notifications.
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for details.
 *
 * configUSE_TASK_NOTIFICATIONS must be undefined or defined as 1 for this
 * function to be available.
 *
 * Each task has a private array of "notification values" (or 'notifications'),
 * each of which is a 32-bit unsigned integer (uint32_t).  The constant
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the
 * array, and (for backward compatibility) defaults to 1 if left undefined.
 * Prior to FreeRTOS V10.4.0 there was only one notification value per task.
 *
 * Events can be sent to a task using an intermediary object.  Examples of such
 * objects are queues, semaphores, mutexes and event groups.  Task notifications
 * are a method of sending an event directly to a task without the need for such
 * an intermediary object.
 *
 * A notification sent to a task can optionally perform an action, such as
 * update, overwrite or increment one of the task's notification values.  In
 * that way task notifications can be used to send data to a task, or be used as
 * light weight and fast binary or counting semaphores.
 *
 * A notification sent to a task will remain pending until it is cleared by the
 * task calling xTaskNotifyWaitIndexed() or ulTaskNotifyTakeIndexed() (or their
 * un-indexed equivalents).  If the task was already in the Blocked state to
 * wait for a notification when the notification arrives then the task will
 * automatically be removed from the Blocked state (unblocked) and the
 * notification cleared.
 *
 * A task can use xTaskNotifyWaitIndexed() to [optionally] block to wait for a
 * notification to be pending, or ulTaskNotifyTakeIndexed() to [optionally] block
 * to wait for a notification value to have a non-zero value.  The task does
 * not consume any CPU time while it is in the Blocked state.
 *
 * **NOTE** Each notification within the array operates independently - a task
 * can only block on one notification within the array at a time and will not be
 * unblocked by a notification sent to any other array index.
 *
 * Backward compatibility information:
 * Prior to FreeRTOS V10.4.0 each task had a single "notification value", and
 * all task notification API functions operated on that value. Replacing the
 * single notification value with an array of notification values necessitated a
 * new set of API functions that could address specific notifications within the
 * array.  xTaskNotifyWait() is the original API function, and remains backward
 * compatible by always operating on the notification value at index 0 in the
 * array. Calling xTaskNotifyWait() is equivalent to calling
 * xTaskNotifyWaitIndexed() with the uxIndexToWaitOn parameter set to 0.
 *
 * @param uxIndexToWaitOn The index within the calling task's array of
 * notification values on which the calling task will wait for a notification to
 * be received.  uxIndexToWaitOn must be less than
 * configTASK_NOTIFICATION_ARRAY_ENTRIES.  xTaskNotifyWait() does
 * not have this parameter and always waits for notifications on index 0.
 *
 * @param ulBitsToClearOnEntry Bits that are set in ulBitsToClearOnEntry value
 * will be cleared in the calling task's notification value before the task
 * checks to see if any notifications are pending, and optionally blocks if no
 * notifications are pending.  Setting ulBitsToClearOnEntry to ULONG_MAX (if
 * limits.h is included) or 0xffffffffUL (if limits.h is not included) will have
 * the effect of resetting the task's notification value to 0.  Setting
 * ulBitsToClearOnEntry to 0 will leave the task's notification value unchanged.
 *
 * @param ulBitsToClearOnExit If a notification is pending or received before
 * the calling task exits the xTaskNotifyWait() function then the task's
 * notification value (see the xTaskNotify() API function) is passed out using
 * the pulNotificationValue parameter.  Then any bits that are set in
 * ulBitsToClearOnExit will be cleared in the task's notification value (note
 * *pulNotificationValue is set before any bits are cleared).  Setting
 * ulBitsToClearOnExit to ULONG_MAX (if limits.h is included) or 0xffffffffUL
 * (if limits.h is not included) will have the effect of resetting the task's
 * notification value to 0 before the function exits.  Setting
 * ulBitsToClearOnExit to 0 will leave the task's notification value unchanged
 * when the function exits (in which case the value passed out in
 * pulNotificationValue will match the task's notification value).
 *
 * @param pulNotificationValue Used to pass the task's notification value out
 * of the function.  Note the value passed out will not be effected by the
 * clearing of any bits caused by ulBitsToClearOnExit being non-zero.
 *
 * @param xTicksToWait The maximum amount of time that the task should wait in
 * the Blocked state for a notification to be received, should a notification
 * not already be pending when xTaskNotifyWait() was called.  The task
 * will not consume any processing time while it is in the Blocked state.  This
 * is specified in kernel ticks, the macro pdMS_TO_TICKS( value_in_ms ) can be
 * used to convert a time specified in milliseconds to a time specified in
 * ticks.
 *
 * @return If a notification was received (including notifications that were
 * already pending when xTaskNotifyWait was called) then pdPASS is
 * returned.  Otherwise pdFAIL is returned.
 *
 * \defgroup xTaskNotifyWaitIndexed xTaskNotifyWaitIndexed
 * \ingroup TaskNotifications
 */
BaseType_t xTaskGenericNotifyWait( UBaseType_t uxIndexToWaitOn,
                                   uint32_t ulBitsToClearOnEntry,
                                   uint32_t ulBitsToClearOnExit,
                                   uint32_t * pulNotificationValue,
                                   TickType_t xTicksToWait ) ;





/**
 * task. h
 * <PRE>BaseType_t xTaskNotifyGiveIndexed( TaskHandle_t xTaskToNotify, UBaseType_t uxIndexToNotify );</PRE>
 * <PRE>BaseType_t xTaskNotifyGive( TaskHandle_t xTaskToNotify );</PRE>
 *
 * Sends a direct to task notification to a particular index in the target
 * task's notification array in a manner similar to giving a counting semaphore.
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for more details.
 *
 * configUSE_TASK_NOTIFICATIONS must be undefined or defined as 1 for these
 * macros to be available.
 *
 * Each task has a private array of "notification values" (or 'notifications'),
 * each of which is a 32-bit unsigned integer (uint32_t).  The constant
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the
 * array, and (for backward compatibility) defaults to 1 if left undefined.
 * Prior to FreeRTOS V10.4.0 there was only one notification value per task.
 *
 * Events can be sent to a task using an intermediary object.  Examples of such
 * objects are queues, semaphores, mutexes and event groups.  Task notifications
 * are a method of sending an event directly to a task without the need for such
 * an intermediary object.
 *
 * A notification sent to a task can optionally perform an action, such as
 * update, overwrite or increment one of the task's notification values.  In
 * that way task notifications can be used to send data to a task, or be used as
 * light weight and fast binary or counting semaphores.
 *
 * xTaskNotifyGiveIndexed() is a helper macro intended for use when task
 * notifications are used as light weight and faster binary or counting
 * semaphore equivalents.  Actual FreeRTOS semaphores are given using the
 * xSemaphoreGive() API function, the equivalent action that instead uses a task
 * notification is xTaskNotifyGiveIndexed().
 *
 * When task notifications are being used as a binary or counting semaphore
 * equivalent then the task being notified should wait for the notification
 * using the ulTaskNotificationTakeIndexed() API function rather than the
 * xTaskNotifyWaitIndexed() API function.
 *
 * **NOTE** Each notification within the array operates independently - a task
 * can only block on one notification within the array at a time and will not be
 * unblocked by a notification sent to any other array index.
 *
 * Backward compatibility information:
 * Prior to FreeRTOS V10.4.0 each task had a single "notification value", and
 * all task notification API functions operated on that value. Replacing the
 * single notification value with an array of notification values necessitated a
 * new set of API functions that could address specific notifications within the
 * array.  xTaskNotifyGive() is the original API function, and remains backward
 * compatible by always operating on the notification value at index 0 in the
 * array. Calling xTaskNotifyGive() is equivalent to calling
 * xTaskNotifyGiveIndexed() with the uxIndexToNotify parameter set to 0.
 *
 * @param xTaskToNotify The handle of the task being notified.  The handle to a
 * task can be returned from the xTaskCreate() API function used to create the
 * task, and the handle of the currently running task can be obtained by calling
 * xTaskGetCurrentTaskHandle().
 *
 * @param uxIndexToNotify The index within the target task's array of
 * notification values to which the notification is to be sent.  uxIndexToNotify
 * must be less than configTASK_NOTIFICATION_ARRAY_ENTRIES.  xTaskNotifyGive()
 * does not have this parameter and always sends notifications to index 0.
 *
 * @return xTaskNotifyGive() is a macro that calls xTaskNotify() with the
 * eAction parameter set to eIncrement - so pdPASS is always returned.
 *
 * \defgroup xTaskNotifyGiveIndexed xTaskNotifyGiveIndexed
 * \ingroup TaskNotifications
 */





/**
 * task. h
 * <PRE>void vTaskNotifyGiveIndexedFromISR( TaskHandle_t xTaskHandle, UBaseType_t uxIndexToNotify, BaseType_t *pxHigherPriorityTaskWoken );</PRE>
 * <PRE>void vTaskNotifyGiveFromISR( TaskHandle_t xTaskHandle, BaseType_t *pxHigherPriorityTaskWoken );</PRE>
 *
 * A version of xTaskNotifyGiveIndexed() that can be called from an interrupt
 * service routine (ISR).
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for more details.
 *
 * configUSE_TASK_NOTIFICATIONS must be undefined or defined as 1 for this macro
 * to be available.
 *
 * Each task has a private array of "notification values" (or 'notifications'),
 * each of which is a 32-bit unsigned integer (uint32_t).  The constant
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the
 * array, and (for backward compatibility) defaults to 1 if left undefined.
 * Prior to FreeRTOS V10.4.0 there was only one notification value per task.
 *
 * Events can be sent to a task using an intermediary object.  Examples of such
 * objects are queues, semaphores, mutexes and event groups.  Task notifications
 * are a method of sending an event directly to a task without the need for such
 * an intermediary object.
 *
 * A notification sent to a task can optionally perform an action, such as
 * update, overwrite or increment one of the task's notification values.  In
 * that way task notifications can be used to send data to a task, or be used as
 * light weight and fast binary or counting semaphores.
 *
 * vTaskNotifyGiveIndexedFromISR() is intended for use when task notifications
 * are used as light weight and faster binary or counting semaphore equivalents.
 * Actual FreeRTOS semaphores are given from an ISR using the
 * xSemaphoreGiveFromISR() API function, the equivalent action that instead uses
 * a task notification is vTaskNotifyGiveIndexedFromISR().
 *
 * When task notifications are being used as a binary or counting semaphore
 * equivalent then the task being notified should wait for the notification
 * using the ulTaskNotificationTakeIndexed() API function rather than the
 * xTaskNotifyWaitIndexed() API function.
 *
 * **NOTE** Each notification within the array operates independently - a task
 * can only block on one notification within the array at a time and will not be
 * unblocked by a notification sent to any other array index.
 *
 * Backward compatibility information:
 * Prior to FreeRTOS V10.4.0 each task had a single "notification value", and
 * all task notification API functions operated on that value. Replacing the
 * single notification value with an array of notification values necessitated a
 * new set of API functions that could address specific notifications within the
 * array.  xTaskNotifyFromISR() is the original API function, and remains
 * backward compatible by always operating on the notification value at index 0
 * within the array. Calling xTaskNotifyGiveFromISR() is equivalent to calling
 * xTaskNotifyGiveIndexedFromISR() with the uxIndexToNotify parameter set to 0.
 *
 * @param xTaskToNotify The handle of the task being notified.  The handle to a
 * task can be returned from the xTaskCreate() API function used to create the
 * task, and the handle of the currently running task can be obtained by calling
 * xTaskGetCurrentTaskHandle().
 *
 * @param uxIndexToNotify The index within the target task's array of
 * notification values to which the notification is to be sent.  uxIndexToNotify
 * must be less than configTASK_NOTIFICATION_ARRAY_ENTRIES.
 * xTaskNotifyGiveFromISR() does not have this parameter and always sends
 * notifications to index 0.
 *
 * @param pxHigherPriorityTaskWoken  vTaskNotifyGiveFromISR() will set
 * *pxHigherPriorityTaskWoken to pdTRUE if sending the notification caused the
 * task to which the notification was sent to leave the Blocked state, and the
 * unblocked task has a priority higher than the currently running task.  If
 * vTaskNotifyGiveFromISR() sets this value to pdTRUE then a context switch
 * should be requested before the interrupt is exited.  How a context switch is
 * requested from an ISR is dependent on the port - see the documentation page
 * for the port in use.
 *
 * \defgroup vTaskNotifyGiveIndexedFromISR vTaskNotifyGiveIndexedFromISR
 * \ingroup TaskNotifications
 */
void vTaskGenericNotifyGiveFromISR( TaskHandle_t xTaskToNotify,
                                    UBaseType_t uxIndexToNotify,
                                    BaseType_t * pxHigherPriorityTaskWoken ) ;





/**
 * task. h
 * <pre>
 * uint32_t ulTaskNotifyTakeIndexed( UBaseType_t uxIndexToWaitOn, BaseType_t xClearCountOnExit, TickType_t xTicksToWait );
 *
 * uint32_t ulTaskNotifyTake( BaseType_t xClearCountOnExit, TickType_t xTicksToWait );
 * </pre>
 *
 * Waits for a direct to task notification on a particular index in the calling
 * task's notification array in a manner similar to taking a counting semaphore.
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for details.
 *
 * configUSE_TASK_NOTIFICATIONS must be undefined or defined as 1 for this
 * function to be available.
 *
 * Each task has a private array of "notification values" (or 'notifications'),
 * each of which is a 32-bit unsigned integer (uint32_t).  The constant
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the
 * array, and (for backward compatibility) defaults to 1 if left undefined.
 * Prior to FreeRTOS V10.4.0 there was only one notification value per task.
 *
 * Events can be sent to a task using an intermediary object.  Examples of such
 * objects are queues, semaphores, mutexes and event groups.  Task notifications
 * are a method of sending an event directly to a task without the need for such
 * an intermediary object.
 *
 * A notification sent to a task can optionally perform an action, such as
 * update, overwrite or increment one of the task's notification values.  In
 * that way task notifications can be used to send data to a task, or be used as
 * light weight and fast binary or counting semaphores.
 *
 * ulTaskNotifyTakeIndexed() is intended for use when a task notification is
 * used as a faster and lighter weight binary or counting semaphore alternative.
 * Actual FreeRTOS semaphores are taken using the xSemaphoreTake() API function,
 * the equivalent action that instead uses a task notification is
 * ulTaskNotifyTakeIndexed().
 *
 * When a task is using its notification value as a binary or counting semaphore
 * other tasks should send notifications to it using the xTaskNotifyGiveIndexed()
 * macro, or xTaskNotifyIndex() function with the eAction parameter set to
 * eIncrement.
 *
 * ulTaskNotifyTakeIndexed() can either clear the task's notification value at
 * the array index specified by the uxIndexToWaitOn parameter to zero on exit,
 * in which case the notification value acts like a binary semaphore, or
 * decrement the notification value on exit, in which case the notification
 * value acts like a counting semaphore.
 *
 * A task can use ulTaskNotifyTakeIndexed() to [optionally] block to wait for
 * a notification.  The task does not consume any CPU time while it is in the
 * Blocked state.
 *
 * Where as xTaskNotifyWaitIndexed() will return when a notification is pending,
 * ulTaskNotifyTakeIndexed() will return when the task's notification value is
 * not zero.
 *
 * **NOTE** Each notification within the array operates independently - a task
 * can only block on one notification within the array at a time and will not be
 * unblocked by a notification sent to any other array index.
 *
 * Backward compatibility information:
 * Prior to FreeRTOS V10.4.0 each task had a single "notification value", and
 * all task notification API functions operated on that value. Replacing the
 * single notification value with an array of notification values necessitated a
 * new set of API functions that could address specific notifications within the
 * array.  ulTaskNotifyTake() is the original API function, and remains backward
 * compatible by always operating on the notification value at index 0 in the
 * array. Calling ulTaskNotifyTake() is equivalent to calling
 * ulTaskNotifyTakeIndexed() with the uxIndexToWaitOn parameter set to 0.
 *
 * @param uxIndexToWaitOn The index within the calling task's array of
 * notification values on which the calling task will wait for a notification to
 * be non-zero.  uxIndexToWaitOn must be less than
 * configTASK_NOTIFICATION_ARRAY_ENTRIES.  xTaskNotifyTake() does
 * not have this parameter and always waits for notifications on index 0.
 *
 * @param xClearCountOnExit if xClearCountOnExit is pdFALSE then the task's
 * notification value is decremented when the function exits.  In this way the
 * notification value acts like a counting semaphore.  If xClearCountOnExit is
 * not pdFALSE then the task's notification value is cleared to zero when the
 * function exits.  In this way the notification value acts like a binary
 * semaphore.
 *
 * @param xTicksToWait The maximum amount of time that the task should wait in
 * the Blocked state for the task's notification value to be greater than zero,
 * should the count not already be greater than zero when
 * ulTaskNotifyTake() was called.  The task will not consume any processing
 * time while it is in the Blocked state.  This is specified in kernel ticks,
 * the macro pdMS_TO_TICKS( value_in_ms ) can be used to convert a time
 * specified in milliseconds to a time specified in ticks.
 *
 * @return The task's notification count before it is either cleared to zero or
 * decremented (see the xClearCountOnExit parameter).
 *
 * \defgroup ulTaskNotifyTakeIndexed ulTaskNotifyTakeIndexed
 * \ingroup TaskNotifications
 */
uint32_t ulTaskGenericNotifyTake( UBaseType_t uxIndexToWaitOn,
                                  BaseType_t xClearCountOnExit,
                                  TickType_t xTicksToWait ) ;





/**
 * task. h
 * <pre>
 * BaseType_t xTaskNotifyStateClearIndexed( TaskHandle_t xTask, UBaseType_t uxIndexToCLear );
 *
 * BaseType_t xTaskNotifyStateClear( TaskHandle_t xTask );
 * </pre>
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for details.
 *
 * configUSE_TASK_NOTIFICATIONS must be undefined or defined as 1 for these
 * functions to be available.
 *
 * Each task has a private array of "notification values" (or 'notifications'),
 * each of which is a 32-bit unsigned integer (uint32_t).  The constant
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the
 * array, and (for backward compatibility) defaults to 1 if left undefined.
 * Prior to FreeRTOS V10.4.0 there was only one notification value per task.
 *
 * If a notification is sent to an index within the array of notifications then
 * the notification at that index is said to be 'pending' until it is read or
 * explicitly cleared by the receiving task.  xTaskNotifyStateClearIndexed()
 * is the function that clears a pending notification without reading the
 * notification value.  The notification value at the same array index is not
 * altered.  Set xTask to NULL to clear the notification state of the calling
 * task.
 *
 * Backward compatibility information:
 * Prior to FreeRTOS V10.4.0 each task had a single "notification value", and
 * all task notification API functions operated on that value. Replacing the
 * single notification value with an array of notification values necessitated a
 * new set of API functions that could address specific notifications within the
 * array.  xTaskNotifyStateClear() is the original API function, and remains
 * backward compatible by always operating on the notification value at index 0
 * within the array. Calling xTaskNotifyStateClear() is equivalent to calling
 * xTaskNotifyStateClearIndexed() with the uxIndexToNotify parameter set to 0.
 *
 * @param xTask The handle of the RTOS task that will have a notification state
 * cleared.  Set xTask to NULL to clear a notification state in the calling
 * task.  To obtain a task's handle create the task using xTaskCreate() and
 * make use of the pxCreatedTask parameter, or create the task using
 * xTaskCreateStatic() and store the returned value, or use the task's name in
 * a call to xTaskGetHandle().
 *
 * @param uxIndexToClear The index within the target task's array of
 * notification values to act upon.  For example, setting uxIndexToClear to 1
 * will clear the state of the notification at index 1 within the array.
 * uxIndexToClear must be less than configTASK_NOTIFICATION_ARRAY_ENTRIES.
 * ulTaskNotifyStateClear() does not have this parameter and always acts on the
 * notification at index 0.
 *
 * @return pdTRUE if the task's notification state was set to
 * eNotWaitingNotification, otherwise pdFALSE.
 *
 * \defgroup xTaskNotifyStateClearIndexed xTaskNotifyStateClearIndexed
 * \ingroup TaskNotifications
 */
BaseType_t xTaskGenericNotifyStateClear( TaskHandle_t xTask,
                                         UBaseType_t uxIndexToClear ) ;





/**
 * task. h
 * <pre>
 * uint32_t ulTaskNotifyValueClearIndexed( TaskHandle_t xTask, UBaseType_t uxIndexToClear, uint32_t ulBitsToClear );
 *
 * uint32_t ulTaskNotifyValueClear( TaskHandle_t xTask, uint32_t ulBitsToClear );
 * </pre>
 *
 * See https://www.FreeRTOS.org/RTOS-task-notifications.html for details.
 *
 * configUSE_TASK_NOTIFICATIONS must be undefined or defined as 1 for these
 * functions to be available.
 *
 * Each task has a private array of "notification values" (or 'notifications'),
 * each of which is a 32-bit unsigned integer (uint32_t).  The constant
 * configTASK_NOTIFICATION_ARRAY_ENTRIES sets the number of indexes in the
 * array, and (for backward compatibility) defaults to 1 if left undefined.
 * Prior to FreeRTOS V10.4.0 there was only one notification value per task.
 *
 * ulTaskNotifyValueClearIndexed() clears the bits specified by the
 * ulBitsToClear bit mask in the notification value at array index uxIndexToClear
 * of the task referenced by xTask.
 *
 * Backward compatibility information:
 * Prior to FreeRTOS V10.4.0 each task had a single "notification value", and
 * all task notification API functions operated on that value. Replacing the
 * single notification value with an array of notification values necessitated a
 * new set of API functions that could address specific notifications within the
 * array.  ulTaskNotifyValueClear() is the original API function, and remains
 * backward compatible by always operating on the notification value at index 0
 * within the array. Calling ulTaskNotifyValueClear() is equivalent to calling
 * ulTaskNotifyValueClearIndexed() with the uxIndexToClear parameter set to 0.
 *
 * @param xTask The handle of the RTOS task that will have bits in one of its
 * notification values cleared. Set xTask to NULL to clear bits in a
 * notification value of the calling task.  To obtain a task's handle create the
 * task using xTaskCreate() and make use of the pxCreatedTask parameter, or
 * create the task using xTaskCreateStatic() and store the returned value, or
 * use the task's name in a call to xTaskGetHandle().
 *
 * @param uxIndexToClear The index within the target task's array of
 * notification values in which to clear the bits.  uxIndexToClear
 * must be less than configTASK_NOTIFICATION_ARRAY_ENTRIES.
 * ulTaskNotifyValueClear() does not have this parameter and always clears bits
 * in the notification value at index 0.
 *
 * @param ulBitsToClear Bit mask of the bits to clear in the notification value of
 * xTask. Set a bit to 1 to clear the corresponding bits in the task's notification
 * value. Set ulBitsToClear to 0xffffffff (UINT_MAX on 32-bit architectures) to clear
 * the notification value to 0.  Set ulBitsToClear to 0 to query the task's
 * notification value without clearing any bits.
 *
 *
 * @return The value of the target task's notification value before the bits
 * specified by ulBitsToClear were cleared.
 * \defgroup ulTaskNotifyValueClear ulTaskNotifyValueClear
 * \ingroup TaskNotifications
 */
uint32_t ulTaskGenericNotifyValueClear( TaskHandle_t xTask,
                                        UBaseType_t uxIndexToClear,
                                        uint32_t ulBitsToClear ) ;





/**
 * task.h
 * <pre>
 * void vTaskSetTimeOutState( TimeOut_t * pxTimeOut );
 * </pre>
 *
 * Capture the current time for future use with xTaskCheckForTimeOut().
 *
 * @param pxTimeOut Pointer to a timeout object into which the current time
 * is to be captured.  The captured time includes the tick count and the number
 * of times the tick count has overflowed since the system first booted.
 * \defgroup vTaskSetTimeOutState vTaskSetTimeOutState
 * \ingroup TaskCtrl
 */
void vTaskSetTimeOutState( TimeOut_t * pxTimeOut ) ;

/**
 * task.h
 * <pre>
 * BaseType_t xTaskCheckForTimeOut( TimeOut_t * pxTimeOut, TickType_t * pxTicksToWait );
 * </pre>
 *
 * Determines if pxTicksToWait ticks has passed since a time was captured
 * using a call to vTaskSetTimeOutState().  The captured time includes the tick
 * count and the number of times the tick count has overflowed.
 *
 * @param pxTimeOut The time status as captured previously using
 * vTaskSetTimeOutState. If the timeout has not yet occurred, it is updated
 * to reflect the current time status.
 * @param pxTicksToWait The number of ticks to check for timeout i.e. if
 * pxTicksToWait ticks have passed since pxTimeOut was last updated (either by
 * vTaskSetTimeOutState() or xTaskCheckForTimeOut()), the timeout has occurred.
 * If the timeout has not occurred, pxTicksToWait is updated to reflect the
 * number of remaining ticks.
 *
 * @return If timeout has occurred, pdTRUE is returned. Otherwise pdFALSE is
 * returned and pxTicksToWait is updated to reflect the number of remaining
 * ticks.
 *
 * @see https://www.FreeRTOS.org/xTaskCheckForTimeOut.html
 *
 * Example Usage:
 * <pre>
 *  // Driver library function used to receive uxWantedBytes from an Rx buffer
 *  // that is filled by a UART interrupt. If there are not enough bytes in the
 *  // Rx buffer then the task enters the Blocked state until it is notified that
 *  // more data has been placed into the buffer. If there is still not enough
 *  // data then the task re-enters the Blocked state, and xTaskCheckForTimeOut()
 *  // is used to re-calculate the Block time to ensure the total amount of time
 *  // spent in the Blocked state does not exceed MAX_TIME_TO_WAIT. This
 *  // continues until either the buffer contains at least uxWantedBytes bytes,
 *  // or the total amount of time spent in the Blocked state reaches
 *  // MAX_TIME_TO_WAIT – at which point the task reads however many bytes are
 *  // available up to a maximum of uxWantedBytes.
 *
 *  size_t xUART_Receive( uint8_t *pucBuffer, size_t uxWantedBytes )
 *  {
 *  size_t uxReceived = 0;
 *  TickType_t xTicksToWait = MAX_TIME_TO_WAIT;
 *  TimeOut_t xTimeOut;
 *
 *      // Initialize xTimeOut.  This records the time at which this function
 *      // was entered.
 *      vTaskSetTimeOutState( &xTimeOut );
 *
 *      // Loop until the buffer contains the wanted number of bytes, or a
 *      // timeout occurs.
 *      while( UART_bytes_in_rx_buffer( pxUARTInstance ) < uxWantedBytes )
 *      {
 *          // The buffer didn't contain enough data so this task is going to
 *          // enter the Blocked state. Adjusting xTicksToWait to account for
 *          // any time that has been spent in the Blocked state within this
 *          // function so far to ensure the total amount of time spent in the
 *          // Blocked state does not exceed MAX_TIME_TO_WAIT.
 *          if( xTaskCheckForTimeOut( &xTimeOut, &xTicksToWait ) != pdFALSE )
 *          {
 *              //Timed out before the wanted number of bytes were available,
 *              // exit the loop.
 *              break;
 *          }
 *
 *          // Wait for a maximum of xTicksToWait ticks to be notified that the
 *          // receive interrupt has placed more data into the buffer.
 *          ulTaskNotifyTake( pdTRUE, xTicksToWait );
 *      }
 *
 *      // Attempt to read uxWantedBytes from the receive buffer into pucBuffer.
 *      // The actual number of bytes read (which might be less than
 *      // uxWantedBytes) is returned.
 *      uxReceived = UART_read_from_receive_buffer( pxUARTInstance,
 *                                                  pucBuffer,
 *                                                  uxWantedBytes );
 *
 *      return uxReceived;
 *  }
 * </pre>
 * \defgroup xTaskCheckForTimeOut xTaskCheckForTimeOut
 * \ingroup TaskCtrl
 */
BaseType_t xTaskCheckForTimeOut( TimeOut_t * pxTimeOut,
                                 TickType_t * pxTicksToWait ) ;

/**
 * task.h
 * <pre>
 * BaseType_t xTaskCatchUpTicks( TickType_t xTicksToCatchUp );
 * </pre>
 *
 * This function corrects the tick count value after the application code has held
 * interrupts disabled for an extended period resulting in tick interrupts having
 * been missed.
 *
 * This function is similar to vTaskStepTick(), however, unlike
 * vTaskStepTick(), xTaskCatchUpTicks() may move the tick count forward past a
 * time at which a task should be removed from the blocked state.  That means
 * tasks may have to be removed from the blocked state as the tick count is
 * moved.
 *
 * @param xTicksToCatchUp The number of tick interrupts that have been missed due to
 * interrupts being disabled.  Its value is not computed automatically, so must be
 * computed by the application writer.
 *
 * @return pdTRUE if moving the tick count forward resulted in a task leaving the
 * blocked state and a context switch being performed.  Otherwise pdFALSE.
 *
 * \defgroup xTaskCatchUpTicks xTaskCatchUpTicks
 * \ingroup TaskCtrl
 */
BaseType_t xTaskCatchUpTicks( TickType_t xTicksToCatchUp ) ;


/*-----------------------------------------------------------
* SCHEDULER INTERNALS AVAILABLE FOR PORTING PURPOSES
*----------------------------------------------------------*/

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS ONLY
 * INTENDED FOR USE WHEN IMPLEMENTING A PORT OF THE SCHEDULER AND IS
 * AN INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * Called from the real time kernel tick (either preemptive or cooperative),
 * this increments the tick count and checks if any tasks that are blocked
 * for a finite period required removing from a blocked list and placing on
 * a ready list.  If a non-zero value is returned then a context switch is
 * required because either:
 *   + A task was removed from a blocked list because its timeout had expired,
 *     or
 *   + Time slicing is in use and there is a task of equal priority to the
 *     currently running task.
 */
BaseType_t xTaskIncrementTick( void ) ;

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS AN
 * INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED.
 *
 * Removes the calling task from the ready list and places it both
 * on the list of tasks waiting for a particular event, and the
 * list of delayed tasks.  The task will be removed from both lists
 * and replaced on the ready list should either the event occur (and
 * there be no higher priority tasks waiting on the same event) or
 * the delay period expires.
 *
 * The 'unordered' version replaces the event list item value with the
 * xItemValue value, and inserts the list item at the end of the list.
 *
 * The 'ordered' version uses the existing event list item value (which is the
 * owning task's priority) to insert the list item into the event list in task
 * priority order.
 *
 * @param pxEventList The list containing tasks that are blocked waiting
 * for the event to occur.
 *
 * @param xItemValue The item value to use for the event list item when the
 * event list is not ordered by task priority.
 *
 * @param xTicksToWait The maximum amount of time that the task should wait
 * for the event to occur.  This is specified in kernel ticks, the constant
 * portTICK_PERIOD_MS can be used to convert kernel ticks into a real time
 * period.
 */
void vTaskPlaceOnEventList( List_t * pxEventList,
                            const TickType_t xTicksToWait ) ;
void vTaskPlaceOnUnorderedEventList( List_t * pxEventList,
                                     const TickType_t xItemValue,
                                     const TickType_t xTicksToWait ) ;

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS AN
 * INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED.
 *
 * This function performs nearly the same function as vTaskPlaceOnEventList().
 * The difference being that this function does not permit tasks to block
 * indefinitely, whereas vTaskPlaceOnEventList() does.
 *
 */
void vTaskPlaceOnEventListRestricted( List_t * pxEventList,
                                      TickType_t xTicksToWait,
                                      const BaseType_t xWaitIndefinitely ) ;

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS AN
 * INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * THIS FUNCTION MUST BE CALLED WITH INTERRUPTS DISABLED.
 *
 * Removes a task from both the specified event list and the list of blocked
 * tasks, and places it on a ready queue.
 *
 * xTaskRemoveFromEventList()/vTaskRemoveFromUnorderedEventList() will be called
 * if either an event occurs to unblock a task, or the block timeout period
 * expires.
 *
 * xTaskRemoveFromEventList() is used when the event list is in task priority
 * order.  It removes the list item from the head of the event list as that will
 * have the highest priority owning task of all the tasks on the event list.
 * vTaskRemoveFromUnorderedEventList() is used when the event list is not
 * ordered and the event list items hold something other than the owning tasks
 * priority.  In this case the event list item value is updated to the value
 * passed in the xItemValue parameter.
 *
 * @return pdTRUE if the task being removed has a higher priority than the task
 * making the call, otherwise pdFALSE.
 */
BaseType_t xTaskRemoveFromEventList( const List_t * pxEventList ) ;
void vTaskRemoveFromUnorderedEventList( ListItem_t * pxEventListItem,
                                        const TickType_t xItemValue ) ;

/*
 * THIS FUNCTION MUST NOT BE USED FROM APPLICATION CODE.  IT IS ONLY
 * INTENDED FOR USE WHEN IMPLEMENTING A PORT OF THE SCHEDULER AND IS
 * AN INTERFACE WHICH IS FOR THE EXCLUSIVE USE OF THE SCHEDULER.
 *
 * Sets the pointer to the current TCB to the TCB of the highest priority task
 * that is ready to run.
 */
                 void vTaskSwitchContext( BaseType_t xCoreID ) ;

/*
 * THESE FUNCTIONS MUST NOT BE USED FROM APPLICATION CODE.  THEY ARE USED BY
 * THE EVENT BITS MODULE.
 */
TickType_t uxTaskResetEventItemValue( void ) ;

/*
 * Return the handle of the calling task.
 */
TaskHandle_t xTaskGetCurrentTaskHandle( void ) ;

/*
 * Return the handle of the task running on specified core.
 */
TaskHandle_t xTaskGetCurrentTaskHandleCPU( UBaseType_t xCoreID ) ;

/*
 * Shortcut used by the queue implementation to prevent unnecessary call to
 * taskYIELD();
 */
void vTaskMissedYield( void ) ;

/*
 * Returns the scheduler state as taskSCHEDULER_RUNNING,
 * taskSCHEDULER_NOT_STARTED or taskSCHEDULER_SUSPENDED.
 */
BaseType_t xTaskGetSchedulerState( void ) ;

/*
 * Raises the priority of the mutex holder to that of the calling task should
 * the mutex holder have a priority less than the calling task.
 */
BaseType_t xTaskPriorityInherit( TaskHandle_t const pxMutexHolder ) ;

/*
 * Set the priority of a task back to its proper priority in the case that it
 * inherited a higher priority while it was holding a semaphore.
 */
BaseType_t xTaskPriorityDisinherit( TaskHandle_t const pxMutexHolder ) ;

/*
 * If a higher priority task attempting to obtain a mutex caused a lower
 * priority task to inherit the higher priority task's priority - but the higher
 * priority task then timed out without obtaining the mutex, then the lower
 * priority task will disinherit the priority again - but only down as far as
 * the highest priority task that is still waiting for the mutex (if there were
 * more than one task waiting for the mutex).
 */
void vTaskPriorityDisinheritAfterTimeout( TaskHandle_t const pxMutexHolder,
                                          UBaseType_t uxHighestPriorityWaitingTask ) ;

/*
 * Get the uxTCBNumber assigned to the task referenced by the xTask parameter.
 */
UBaseType_t uxTaskGetTaskNumber( TaskHandle_t xTask ) ;

/*
 * Set the uxTaskNumber of the task referenced by the xTask parameter to
 * uxHandle.
 */
void vTaskSetTaskNumber( TaskHandle_t xTask,
                         const UBaseType_t uxHandle ) ;

/*
 * Only available when configUSE_TICKLESS_IDLE is set to 1.
 * If tickless mode is being used, or a low power mode is implemented, then
 * the tick interrupt will not execute during idle periods.  When this is the
 * case, the tick count value maintained by the scheduler needs to be kept up
 * to date with the actual execution time by being skipped forward by a time
 * equal to the idle period.
 */
void vTaskStepTick( const TickType_t xTicksToJump ) ;

/*
 * Only available when configUSE_TICKLESS_IDLE is set to 1.
 * Provided for use within portSUPPRESS_TICKS_AND_SLEEP() to allow the port
 * specific sleep function to determine if it is ok to proceed with the sleep,
 * and if it is ok to proceed, if it is ok to sleep indefinitely.
 *
 * This function is necessary because portSUPPRESS_TICKS_AND_SLEEP() is only
 * called with the scheduler suspended, not from within a critical section.  It
 * is therefore possible for an interrupt to request a context switch between
 * portSUPPRESS_TICKS_AND_SLEEP() and the low power mode actually being
 * entered.  eTaskConfirmSleepModeStatus() should be called from a short
 * critical section between the timer being stopped and the sleep mode being
 * entered to ensure it is ok to proceed into the sleep mode.
 */
eSleepModeStatus eTaskConfirmSleepModeStatus( void ) ;

/*
 * For internal use only.  Increment the mutex held count when a mutex is
 * taken and return the handle of the task that has taken the mutex.
 */
TaskHandle_t pvTaskIncrementMutexHeldCount( void ) ;

/*
 * For internal use only.  Same as vTaskSetTimeOutState(), but without a critical
 * section.
 */
void vTaskInternalSetTimeOutState( TimeOut_t * pxTimeOut ) ;

/*
 * For internal use only. Same as portYIELD_WITHIN_API() in single core FreeRTOS.
 * For SMP this is not defined by the port.
 */
void vTaskYieldWithinAPI( void );

/* *INDENT-OFF* */



/* *INDENT-ON* */
// # 48 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/timers.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */







    /* Reason for rewrite:
     * VeriFast bug:
     * Both `#ifdef INC_FREERTOS_H` and its negation `#ifdef INC_FREERTOS_H`
     * evaluate to true. See minimal example `define_name`.
     */

    /* Remember that this header is included indirectly `tasks.c` after it
     * includes `FreeRTOS.h`.
     */
    // TODO: Remove this work-around once VF has been fixed.






/*lint -save -e537 This headers are only multiply included if the application code
 * happens to also be including task.h. */

/*lint -restore */

/* *INDENT-OFF* */



/* *INDENT-ON* */

/*-----------------------------------------------------------
* MACROS AND DEFINITIONS
*----------------------------------------------------------*/

/* IDs for commands that can be sent/received on the timer queue.  These are to
 * be used solely through the macros that make up the public software timer API,
 * as defined below.  The commands that are sent from interrupts must use the
 * highest numbers as tmrFIRST_FROM_ISR_COMMAND is used to determine if the task
 * or interrupt version of the queue send function should be used. */
// # 85 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/timers.h"
/**
 * Type by which software timers are referenced.  For example, a call to
 * xTimerCreate() returns an TimerHandle_t variable that can then be used to
 * reference the subject timer in calls to other software timer API functions
 * (for example, xTimerStart(), xTimerReset(), etc.).
 */
struct tmrTimerControl; /* The old naming convention is used to prevent breaking kernel aware debuggers. */
typedef struct tmrTimerControl * TimerHandle_t;

/*
 * Defines the prototype to which timer callback functions must conform.
 */
typedef void (* TimerCallbackFunction_t)( TimerHandle_t xTimer );

/*
 * Defines the prototype to which functions used with the
 * xTimerPendFunctionCallFromISR() function must conform.
 */
typedef void (* PendedFunction_t)( void *,
                                   uint32_t );

/**
 * TimerHandle_t xTimerCreate(  const char * pcTimerName,
 *                              TickType_t xTimerPeriodInTicks,
 *                              UBaseType_t uxAutoReload,
 *                              void * pvTimerID,
 *                              TimerCallbackFunction_t pxCallbackFunction );
 *
 * Creates a new software timer instance, and returns a handle by which the
 * created software timer can be referenced.
 *
 * Internally, within the FreeRTOS implementation, software timers use a block
 * of memory, in which the timer data structure is stored.  If a software timer
 * is created using xTimerCreate() then the required memory is automatically
 * dynamically allocated inside the xTimerCreate() function.  (see
 * https://www.FreeRTOS.org/a00111.html).  If a software timer is created using
 * xTimerCreateStatic() then the application writer must provide the memory that
 * will get used by the software timer.  xTimerCreateStatic() therefore allows a
 * software timer to be created without using any dynamic memory allocation.
 *
 * Timers are created in the dormant state.  The xTimerStart(), xTimerReset(),
 * xTimerStartFromISR(), xTimerResetFromISR(), xTimerChangePeriod() and
 * xTimerChangePeriodFromISR() API functions can all be used to transition a
 * timer into the active state.
 *
 * @param pcTimerName A text name that is assigned to the timer.  This is done
 * purely to assist debugging.  The kernel itself only ever references a timer
 * by its handle, and never by its name.
 *
 * @param xTimerPeriodInTicks The timer period.  The time is defined in tick
 * periods so the constant portTICK_PERIOD_MS can be used to convert a time that
 * has been specified in milliseconds.  For example, if the timer must expire
 * after 100 ticks, then xTimerPeriodInTicks should be set to 100.
 * Alternatively, if the timer must expire after 500ms, then xPeriod can be set
 * to ( 500 / portTICK_PERIOD_MS ) provided configTICK_RATE_HZ is less than or
 * equal to 1000.  Time timer period must be greater than 0.
 *
 * @param uxAutoReload If uxAutoReload is set to pdTRUE then the timer will
 * expire repeatedly with a frequency set by the xTimerPeriodInTicks parameter.
 * If uxAutoReload is set to pdFALSE then the timer will be a one-shot timer and
 * enter the dormant state after it expires.
 *
 * @param pvTimerID An identifier that is assigned to the timer being created.
 * Typically this would be used in the timer callback function to identify which
 * timer expired when the same callback function is assigned to more than one
 * timer.
 *
 * @param pxCallbackFunction The function to call when the timer expires.
 * Callback functions must have the prototype defined by TimerCallbackFunction_t,
 * which is "void vCallbackFunction( TimerHandle_t xTimer );".
 *
 * @return If the timer is successfully created then a handle to the newly
 * created timer is returned.  If the timer cannot be created because there is
 * insufficient FreeRTOS heap remaining to allocate the timer
 * structures then NULL is returned.
 *
 * Example usage:
 * @verbatim
 * #define NUM_TIMERS 5
 *
 * // An array to hold handles to the created timers.
 * TimerHandle_t xTimers[ NUM_TIMERS ];
 *
 * // An array to hold a count of the number of times each timer expires.
 * int32_t lExpireCounters[ NUM_TIMERS ] = { 0 };
 *
 * // Define a callback function that will be used by multiple timer instances.
 * // The callback function does nothing but count the number of times the
 * // associated timer expires, and stop the timer once the timer has expired
 * // 10 times.
 * void vTimerCallback( TimerHandle_t pxTimer )
 * {
 * int32_t lArrayIndex;
 * int32_t xMaxExpiryCountBeforeStopping = 10;
 *
 *     // Optionally do something if the pxTimer parameter is NULL.
 *     configASSERT( pxTimer );
 *
 *     // Which timer expired?
 *     lArrayIndex = ( int32_t ) pvTimerGetTimerID( pxTimer );
 *
 *     // Increment the number of times that pxTimer has expired.
 *     lExpireCounters[ lArrayIndex ] += 1;
 *
 *     // If the timer has expired 10 times then stop it from running.
 *     if( lExpireCounters[ lArrayIndex ] == xMaxExpiryCountBeforeStopping )
 *     {
 *         // Do not use a block time if calling a timer API function from a
 *         // timer callback function, as doing so could cause a deadlock!
 *         xTimerStop( pxTimer, 0 );
 *     }
 * }
 *
 * void main( void )
 * {
 * int32_t x;
 *
 *     // Create then start some timers.  Starting the timers before the scheduler
 *     // has been started means the timers will start running immediately that
 *     // the scheduler starts.
 *     for( x = 0; x < NUM_TIMERS; x++ )
 *     {
 *         xTimers[ x ] = xTimerCreate(    "Timer",       // Just a text name, not used by the kernel.
 *                                         ( 100 * x ),   // The timer period in ticks.
 *                                         pdTRUE,        // The timers will auto-reload themselves when they expire.
 *                                         ( void * ) x,  // Assign each timer a unique id equal to its array index.
 *                                         vTimerCallback // Each timer calls the same callback when it expires.
 *                                     );
 *
 *         if( xTimers[ x ] == NULL )
 *         {
 *             // The timer was not created.
 *         }
 *         else
 *         {
 *             // Start the timer.  No block time is specified, and even if one was
 *             // it would be ignored because the scheduler has not yet been
 *             // started.
 *             if( xTimerStart( xTimers[ x ], 0 ) != pdPASS )
 *             {
 *                 // The timer could not be set into the Active state.
 *             }
 *         }
 *     }
 *
 *     // ...
 *     // Create tasks here.
 *     // ...
 *
 *     // Starting the scheduler will start the timers running as they have already
 *     // been set into the active state.
 *     vTaskStartScheduler();
 *
 *     // Should not reach here.
 *     for( ;; );
 * }
 * @endverbatim
 */

    TimerHandle_t xTimerCreate( const char * pcTimerName, /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
                                const TickType_t xTimerPeriodInTicks,
                                const UBaseType_t uxAutoReload,
                                void * pvTimerID,
                                TimerCallbackFunction_t pxCallbackFunction ) ;


/**
 * TimerHandle_t xTimerCreateStatic(const char * pcTimerName,
 *                                  TickType_t xTimerPeriodInTicks,
 *                                  UBaseType_t uxAutoReload,
 *                                  void * pvTimerID,
 *                                  TimerCallbackFunction_t pxCallbackFunction,
 *                                  StaticTimer_t *pxTimerBuffer );
 *
 * Creates a new software timer instance, and returns a handle by which the
 * created software timer can be referenced.
 *
 * Internally, within the FreeRTOS implementation, software timers use a block
 * of memory, in which the timer data structure is stored.  If a software timer
 * is created using xTimerCreate() then the required memory is automatically
 * dynamically allocated inside the xTimerCreate() function.  (see
 * https://www.FreeRTOS.org/a00111.html).  If a software timer is created using
 * xTimerCreateStatic() then the application writer must provide the memory that
 * will get used by the software timer.  xTimerCreateStatic() therefore allows a
 * software timer to be created without using any dynamic memory allocation.
 *
 * Timers are created in the dormant state.  The xTimerStart(), xTimerReset(),
 * xTimerStartFromISR(), xTimerResetFromISR(), xTimerChangePeriod() and
 * xTimerChangePeriodFromISR() API functions can all be used to transition a
 * timer into the active state.
 *
 * @param pcTimerName A text name that is assigned to the timer.  This is done
 * purely to assist debugging.  The kernel itself only ever references a timer
 * by its handle, and never by its name.
 *
 * @param xTimerPeriodInTicks The timer period.  The time is defined in tick
 * periods so the constant portTICK_PERIOD_MS can be used to convert a time that
 * has been specified in milliseconds.  For example, if the timer must expire
 * after 100 ticks, then xTimerPeriodInTicks should be set to 100.
 * Alternatively, if the timer must expire after 500ms, then xPeriod can be set
 * to ( 500 / portTICK_PERIOD_MS ) provided configTICK_RATE_HZ is less than or
 * equal to 1000.  The timer period must be greater than 0.
 *
 * @param uxAutoReload If uxAutoReload is set to pdTRUE then the timer will
 * expire repeatedly with a frequency set by the xTimerPeriodInTicks parameter.
 * If uxAutoReload is set to pdFALSE then the timer will be a one-shot timer and
 * enter the dormant state after it expires.
 *
 * @param pvTimerID An identifier that is assigned to the timer being created.
 * Typically this would be used in the timer callback function to identify which
 * timer expired when the same callback function is assigned to more than one
 * timer.
 *
 * @param pxCallbackFunction The function to call when the timer expires.
 * Callback functions must have the prototype defined by TimerCallbackFunction_t,
 * which is "void vCallbackFunction( TimerHandle_t xTimer );".
 *
 * @param pxTimerBuffer Must point to a variable of type StaticTimer_t, which
 * will be then be used to hold the software timer's data structures, removing
 * the need for the memory to be allocated dynamically.
 *
 * @return If the timer is created then a handle to the created timer is
 * returned.  If pxTimerBuffer was NULL then NULL is returned.
 *
 * Example usage:
 * @verbatim
 *
 * // The buffer used to hold the software timer's data structure.
 * static StaticTimer_t xTimerBuffer;
 *
 * // A variable that will be incremented by the software timer's callback
 * // function.
 * UBaseType_t uxVariableToIncrement = 0;
 *
 * // A software timer callback function that increments a variable passed to
 * // it when the software timer was created.  After the 5th increment the
 * // callback function stops the software timer.
 * static void prvTimerCallback( TimerHandle_t xExpiredTimer )
 * {
 * UBaseType_t *puxVariableToIncrement;
 * BaseType_t xReturned;
 *
 *     // Obtain the address of the variable to increment from the timer ID.
 *     puxVariableToIncrement = ( UBaseType_t * ) pvTimerGetTimerID( xExpiredTimer );
 *
 *     // Increment the variable to show the timer callback has executed.
 *     ( *puxVariableToIncrement )++;
 *
 *     // If this callback has executed the required number of times, stop the
 *     // timer.
 *     if( *puxVariableToIncrement == 5 )
 *     {
 *         // This is called from a timer callback so must not block.
 *         xTimerStop( xExpiredTimer, staticDONT_BLOCK );
 *     }
 * }
 *
 *
 * void main( void )
 * {
 *     // Create the software time.  xTimerCreateStatic() has an extra parameter
 *     // than the normal xTimerCreate() API function.  The parameter is a pointer
 *     // to the StaticTimer_t structure that will hold the software timer
 *     // structure.  If the parameter is passed as NULL then the structure will be
 *     // allocated dynamically, just as if xTimerCreate() had been called.
 *     xTimer = xTimerCreateStatic( "T1",             // Text name for the task.  Helps debugging only.  Not used by FreeRTOS.
 *                                  xTimerPeriod,     // The period of the timer in ticks.
 *                                  pdTRUE,           // This is an auto-reload timer.
 *                                  ( void * ) &uxVariableToIncrement,    // A variable incremented by the software timer's callback function
 *                                  prvTimerCallback, // The function to execute when the timer expires.
 *                                  &xTimerBuffer );  // The buffer that will hold the software timer structure.
 *
 *     // The scheduler has not started yet so a block time is not used.
 *     xReturned = xTimerStart( xTimer, 0 );
 *
 *     // ...
 *     // Create tasks here.
 *     // ...
 *
 *     // Starting the scheduler will start the timers running as they have already
 *     // been set into the active state.
 *     vTaskStartScheduler();
 *
 *     // Should not reach here.
 *     for( ;; );
 * }
 * @endverbatim
 */
// # 382 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/timers.h"
/**
 * void *pvTimerGetTimerID( TimerHandle_t xTimer );
 *
 * Returns the ID assigned to the timer.
 *
 * IDs are assigned to timers using the pvTimerID parameter of the call to
 * xTimerCreated() that was used to create the timer, and by calling the
 * vTimerSetTimerID() API function.
 *
 * If the same callback function is assigned to multiple timers then the timer
 * ID can be used as time specific (timer local) storage.
 *
 * @param xTimer The timer being queried.
 *
 * @return The ID assigned to the timer being queried.
 *
 * Example usage:
 *
 * See the xTimerCreate() API function example usage scenario.
 */
void * pvTimerGetTimerID( const TimerHandle_t xTimer ) ;

/**
 * void vTimerSetTimerID( TimerHandle_t xTimer, void *pvNewID );
 *
 * Sets the ID assigned to the timer.
 *
 * IDs are assigned to timers using the pvTimerID parameter of the call to
 * xTimerCreated() that was used to create the timer.
 *
 * If the same callback function is assigned to multiple timers then the timer
 * ID can be used as time specific (timer local) storage.
 *
 * @param xTimer The timer being updated.
 *
 * @param pvNewID The ID to assign to the timer.
 *
 * Example usage:
 *
 * See the xTimerCreate() API function example usage scenario.
 */
void vTimerSetTimerID( TimerHandle_t xTimer,
                       void * pvNewID ) ;

/**
 * BaseType_t xTimerIsTimerActive( TimerHandle_t xTimer );
 *
 * Queries a timer to see if it is active or dormant.
 *
 * A timer will be dormant if:
 *     1) It has been created but not started, or
 *     2) It is an expired one-shot timer that has not been restarted.
 *
 * Timers are created in the dormant state.  The xTimerStart(), xTimerReset(),
 * xTimerStartFromISR(), xTimerResetFromISR(), xTimerChangePeriod() and
 * xTimerChangePeriodFromISR() API functions can all be used to transition a timer into the
 * active state.
 *
 * @param xTimer The timer being queried.
 *
 * @return pdFALSE will be returned if the timer is dormant.  A value other than
 * pdFALSE will be returned if the timer is active.
 *
 * Example usage:
 * @verbatim
 * // This function assumes xTimer has already been created.
 * void vAFunction( TimerHandle_t xTimer )
 * {
 *     if( xTimerIsTimerActive( xTimer ) != pdFALSE ) // or more simply and equivalently "if( xTimerIsTimerActive( xTimer ) )"
 *     {
 *         // xTimer is active, do something.
 *     }
 *     else
 *     {
 *         // xTimer is not active, do something else.
 *     }
 * }
 * @endverbatim
 */
BaseType_t xTimerIsTimerActive( TimerHandle_t xTimer ) ;

/**
 * TaskHandle_t xTimerGetTimerDaemonTaskHandle( void );
 *
 * Simply returns the handle of the timer service/daemon task.  It it not valid
 * to call xTimerGetTimerDaemonTaskHandle() before the scheduler has been started.
 */
TaskHandle_t xTimerGetTimerDaemonTaskHandle( void ) ;

/**
 * BaseType_t xTimerStart( TimerHandle_t xTimer, TickType_t xTicksToWait );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * through a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerStart() starts a timer that was previously created using the
 * xTimerCreate() API function.  If the timer had already been started and was
 * already in the active state, then xTimerStart() has equivalent functionality
 * to the xTimerReset() API function.
 *
 * Starting a timer ensures the timer is in the active state.  If the timer
 * is not stopped, deleted, or reset in the mean time, the callback function
 * associated with the timer will get called 'n' ticks after xTimerStart() was
 * called, where 'n' is the timers defined period.
 *
 * It is valid to call xTimerStart() before the scheduler has been started, but
 * when this is done the timer will not actually start until the scheduler is
 * started, and the timers expiry time will be relative to when the scheduler is
 * started, not relative to when xTimerStart() was called.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for xTimerStart()
 * to be available.
 *
 * @param xTimer The handle of the timer being started/restarted.
 *
 * @param xTicksToWait Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the start command to be successfully
 * sent to the timer command queue, should the queue already be full when
 * xTimerStart() was called.  xTicksToWait is ignored if xTimerStart() is called
 * before the scheduler is started.
 *
 * @return pdFAIL will be returned if the start command could not be sent to
 * the timer command queue even after xTicksToWait ticks had passed.  pdPASS will
 * be returned if the command was successfully sent to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system, although the
 * timers expiry time is relative to when xTimerStart() is actually called.  The
 * timer service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 *
 * See the xTimerCreate() API function example usage scenario.
 *
 */



/**
 * BaseType_t xTimerStop( TimerHandle_t xTimer, TickType_t xTicksToWait );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * through a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerStop() stops a timer that was previously started using either of the
 * The xTimerStart(), xTimerReset(), xTimerStartFromISR(), xTimerResetFromISR(),
 * xTimerChangePeriod() or xTimerChangePeriodFromISR() API functions.
 *
 * Stopping a timer ensures the timer is not in the active state.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for xTimerStop()
 * to be available.
 *
 * @param xTimer The handle of the timer being stopped.
 *
 * @param xTicksToWait Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the stop command to be successfully
 * sent to the timer command queue, should the queue already be full when
 * xTimerStop() was called.  xTicksToWait is ignored if xTimerStop() is called
 * before the scheduler is started.
 *
 * @return pdFAIL will be returned if the stop command could not be sent to
 * the timer command queue even after xTicksToWait ticks had passed.  pdPASS will
 * be returned if the command was successfully sent to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system.  The timer
 * service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 *
 * See the xTimerCreate() API function example usage scenario.
 *
 */



/**
 * BaseType_t xTimerChangePeriod(   TimerHandle_t xTimer,
 *                                  TickType_t xNewPeriod,
 *                                  TickType_t xTicksToWait );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * through a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerChangePeriod() changes the period of a timer that was previously
 * created using the xTimerCreate() API function.
 *
 * xTimerChangePeriod() can be called to change the period of an active or
 * dormant state timer.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for
 * xTimerChangePeriod() to be available.
 *
 * @param xTimer The handle of the timer that is having its period changed.
 *
 * @param xNewPeriod The new period for xTimer. Timer periods are specified in
 * tick periods, so the constant portTICK_PERIOD_MS can be used to convert a time
 * that has been specified in milliseconds.  For example, if the timer must
 * expire after 100 ticks, then xNewPeriod should be set to 100.  Alternatively,
 * if the timer must expire after 500ms, then xNewPeriod can be set to
 * ( 500 / portTICK_PERIOD_MS ) provided configTICK_RATE_HZ is less than
 * or equal to 1000.
 *
 * @param xTicksToWait Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the change period command to be
 * successfully sent to the timer command queue, should the queue already be
 * full when xTimerChangePeriod() was called.  xTicksToWait is ignored if
 * xTimerChangePeriod() is called before the scheduler is started.
 *
 * @return pdFAIL will be returned if the change period command could not be
 * sent to the timer command queue even after xTicksToWait ticks had passed.
 * pdPASS will be returned if the command was successfully sent to the timer
 * command queue.  When the command is actually processed will depend on the
 * priority of the timer service/daemon task relative to other tasks in the
 * system.  The timer service/daemon task priority is set by the
 * configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This function assumes xTimer has already been created.  If the timer
 * // referenced by xTimer is already active when it is called, then the timer
 * // is deleted.  If the timer referenced by xTimer is not active when it is
 * // called, then the period of the timer is set to 500ms and the timer is
 * // started.
 * void vAFunction( TimerHandle_t xTimer )
 * {
 *     if( xTimerIsTimerActive( xTimer ) != pdFALSE ) // or more simply and equivalently "if( xTimerIsTimerActive( xTimer ) )"
 *     {
 *         // xTimer is already active - delete it.
 *         xTimerDelete( xTimer );
 *     }
 *     else
 *     {
 *         // xTimer is not active, change its period to 500ms.  This will also
 *         // cause the timer to start.  Block for a maximum of 100 ticks if the
 *         // change period command cannot immediately be sent to the timer
 *         // command queue.
 *         if( xTimerChangePeriod( xTimer, 500 / portTICK_PERIOD_MS, 100 ) == pdPASS )
 *         {
 *             // The command was successfully sent.
 *         }
 *         else
 *         {
 *             // The command could not be sent, even after waiting for 100 ticks
 *             // to pass.  Take appropriate action here.
 *         }
 *     }
 * }
 * @endverbatim
 */



/**
 * BaseType_t xTimerDelete( TimerHandle_t xTimer, TickType_t xTicksToWait );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * through a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerDelete() deletes a timer that was previously created using the
 * xTimerCreate() API function.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for
 * xTimerDelete() to be available.
 *
 * @param xTimer The handle of the timer being deleted.
 *
 * @param xTicksToWait Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the delete command to be
 * successfully sent to the timer command queue, should the queue already be
 * full when xTimerDelete() was called.  xTicksToWait is ignored if xTimerDelete()
 * is called before the scheduler is started.
 *
 * @return pdFAIL will be returned if the delete command could not be sent to
 * the timer command queue even after xTicksToWait ticks had passed.  pdPASS will
 * be returned if the command was successfully sent to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system.  The timer
 * service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 *
 * See the xTimerChangePeriod() API function example usage scenario.
 */



/**
 * BaseType_t xTimerReset( TimerHandle_t xTimer, TickType_t xTicksToWait );
 *
 * Timer functionality is provided by a timer service/daemon task.  Many of the
 * public FreeRTOS timer API functions send commands to the timer service task
 * through a queue called the timer command queue.  The timer command queue is
 * private to the kernel itself and is not directly accessible to application
 * code.  The length of the timer command queue is set by the
 * configTIMER_QUEUE_LENGTH configuration constant.
 *
 * xTimerReset() re-starts a timer that was previously created using the
 * xTimerCreate() API function.  If the timer had already been started and was
 * already in the active state, then xTimerReset() will cause the timer to
 * re-evaluate its expiry time so that it is relative to when xTimerReset() was
 * called.  If the timer was in the dormant state then xTimerReset() has
 * equivalent functionality to the xTimerStart() API function.
 *
 * Resetting a timer ensures the timer is in the active state.  If the timer
 * is not stopped, deleted, or reset in the mean time, the callback function
 * associated with the timer will get called 'n' ticks after xTimerReset() was
 * called, where 'n' is the timers defined period.
 *
 * It is valid to call xTimerReset() before the scheduler has been started, but
 * when this is done the timer will not actually start until the scheduler is
 * started, and the timers expiry time will be relative to when the scheduler is
 * started, not relative to when xTimerReset() was called.
 *
 * The configUSE_TIMERS configuration constant must be set to 1 for xTimerReset()
 * to be available.
 *
 * @param xTimer The handle of the timer being reset/started/restarted.
 *
 * @param xTicksToWait Specifies the time, in ticks, that the calling task should
 * be held in the Blocked state to wait for the reset command to be successfully
 * sent to the timer command queue, should the queue already be full when
 * xTimerReset() was called.  xTicksToWait is ignored if xTimerReset() is called
 * before the scheduler is started.
 *
 * @return pdFAIL will be returned if the reset command could not be sent to
 * the timer command queue even after xTicksToWait ticks had passed.  pdPASS will
 * be returned if the command was successfully sent to the timer command queue.
 * When the command is actually processed will depend on the priority of the
 * timer service/daemon task relative to other tasks in the system, although the
 * timers expiry time is relative to when xTimerStart() is actually called.  The
 * timer service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 * @verbatim
 * // When a key is pressed, an LCD back-light is switched on.  If 5 seconds pass
 * // without a key being pressed, then the LCD back-light is switched off.  In
 * // this case, the timer is a one-shot timer.
 *
 * TimerHandle_t xBacklightTimer = NULL;
 *
 * // The callback function assigned to the one-shot timer.  In this case the
 * // parameter is not used.
 * void vBacklightTimerCallback( TimerHandle_t pxTimer )
 * {
 *     // The timer expired, therefore 5 seconds must have passed since a key
 *     // was pressed.  Switch off the LCD back-light.
 *     vSetBacklightState( BACKLIGHT_OFF );
 * }
 *
 * // The key press event handler.
 * void vKeyPressEventHandler( char cKey )
 * {
 *     // Ensure the LCD back-light is on, then reset the timer that is
 *     // responsible for turning the back-light off after 5 seconds of
 *     // key inactivity.  Wait 10 ticks for the command to be successfully sent
 *     // if it cannot be sent immediately.
 *     vSetBacklightState( BACKLIGHT_ON );
 *     if( xTimerReset( xBacklightTimer, 100 ) != pdPASS )
 *     {
 *         // The reset command was not executed successfully.  Take appropriate
 *         // action here.
 *     }
 *
 *     // Perform the rest of the key processing here.
 * }
 *
 * void main( void )
 * {
 * int32_t x;
 *
 *     // Create then start the one-shot timer that is responsible for turning
 *     // the back-light off if no keys are pressed within a 5 second period.
 *     xBacklightTimer = xTimerCreate( "BacklightTimer",           // Just a text name, not used by the kernel.
 *                                     ( 5000 / portTICK_PERIOD_MS), // The timer period in ticks.
 *                                     pdFALSE,                    // The timer is a one-shot timer.
 *                                     0,                          // The id is not used by the callback so can take any value.
 *                                     vBacklightTimerCallback     // The callback function that switches the LCD back-light off.
 *                                   );
 *
 *     if( xBacklightTimer == NULL )
 *     {
 *         // The timer was not created.
 *     }
 *     else
 *     {
 *         // Start the timer.  No block time is specified, and even if one was
 *         // it would be ignored because the scheduler has not yet been
 *         // started.
 *         if( xTimerStart( xBacklightTimer, 0 ) != pdPASS )
 *         {
 *             // The timer could not be set into the Active state.
 *         }
 *     }
 *
 *     // ...
 *     // Create tasks here.
 *     // ...
 *
 *     // Starting the scheduler will start the timer running as it has already
 *     // been set into the active state.
 *     vTaskStartScheduler();
 *
 *     // Should not reach here.
 *     for( ;; );
 * }
 * @endverbatim
 */



/**
 * BaseType_t xTimerStartFromISR(   TimerHandle_t xTimer,
 *                                  BaseType_t *pxHigherPriorityTaskWoken );
 *
 * A version of xTimerStart() that can be called from an interrupt service
 * routine.
 *
 * @param xTimer The handle of the timer being started/restarted.
 *
 * @param pxHigherPriorityTaskWoken The timer service/daemon task spends most
 * of its time in the Blocked state, waiting for messages to arrive on the timer
 * command queue.  Calling xTimerStartFromISR() writes a message to the timer
 * command queue, so has the potential to transition the timer service/daemon
 * task out of the Blocked state.  If calling xTimerStartFromISR() causes the
 * timer service/daemon task to leave the Blocked state, and the timer service/
 * daemon task has a priority equal to or greater than the currently executing
 * task (the task that was interrupted), then *pxHigherPriorityTaskWoken will
 * get set to pdTRUE internally within the xTimerStartFromISR() function.  If
 * xTimerStartFromISR() sets this value to pdTRUE then a context switch should
 * be performed before the interrupt exits.
 *
 * @return pdFAIL will be returned if the start command could not be sent to
 * the timer command queue.  pdPASS will be returned if the command was
 * successfully sent to the timer command queue.  When the command is actually
 * processed will depend on the priority of the timer service/daemon task
 * relative to other tasks in the system, although the timers expiry time is
 * relative to when xTimerStartFromISR() is actually called.  The timer
 * service/daemon task priority is set by the configTIMER_TASK_PRIORITY
 * configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This scenario assumes xBacklightTimer has already been created.  When a
 * // key is pressed, an LCD back-light is switched on.  If 5 seconds pass
 * // without a key being pressed, then the LCD back-light is switched off.  In
 * // this case, the timer is a one-shot timer, and unlike the example given for
 * // the xTimerReset() function, the key press event handler is an interrupt
 * // service routine.
 *
 * // The callback function assigned to the one-shot timer.  In this case the
 * // parameter is not used.
 * void vBacklightTimerCallback( TimerHandle_t pxTimer )
 * {
 *     // The timer expired, therefore 5 seconds must have passed since a key
 *     // was pressed.  Switch off the LCD back-light.
 *     vSetBacklightState( BACKLIGHT_OFF );
 * }
 *
 * // The key press interrupt service routine.
 * void vKeyPressEventInterruptHandler( void )
 * {
 * BaseType_t xHigherPriorityTaskWoken = pdFALSE;
 *
 *     // Ensure the LCD back-light is on, then restart the timer that is
 *     // responsible for turning the back-light off after 5 seconds of
 *     // key inactivity.  This is an interrupt service routine so can only
 *     // call FreeRTOS API functions that end in "FromISR".
 *     vSetBacklightState( BACKLIGHT_ON );
 *
 *     // xTimerStartFromISR() or xTimerResetFromISR() could be called here
 *     // as both cause the timer to re-calculate its expiry time.
 *     // xHigherPriorityTaskWoken was initialised to pdFALSE when it was
 *     // declared (in this function).
 *     if( xTimerStartFromISR( xBacklightTimer, &xHigherPriorityTaskWoken ) != pdPASS )
 *     {
 *         // The start command was not executed successfully.  Take appropriate
 *         // action here.
 *     }
 *
 *     // Perform the rest of the key processing here.
 *
 *     // If xHigherPriorityTaskWoken equals pdTRUE, then a context switch
 *     // should be performed.  The syntax required to perform a context switch
 *     // from inside an ISR varies from port to port, and from compiler to
 *     // compiler.  Inspect the demos for the port you are using to find the
 *     // actual syntax required.
 *     if( xHigherPriorityTaskWoken != pdFALSE )
 *     {
 *         // Call the interrupt safe yield function here (actual function
 *         // depends on the FreeRTOS port being used).
 *     }
 * }
 * @endverbatim
 */



/**
 * BaseType_t xTimerStopFromISR(    TimerHandle_t xTimer,
 *                                  BaseType_t *pxHigherPriorityTaskWoken );
 *
 * A version of xTimerStop() that can be called from an interrupt service
 * routine.
 *
 * @param xTimer The handle of the timer being stopped.
 *
 * @param pxHigherPriorityTaskWoken The timer service/daemon task spends most
 * of its time in the Blocked state, waiting for messages to arrive on the timer
 * command queue.  Calling xTimerStopFromISR() writes a message to the timer
 * command queue, so has the potential to transition the timer service/daemon
 * task out of the Blocked state.  If calling xTimerStopFromISR() causes the
 * timer service/daemon task to leave the Blocked state, and the timer service/
 * daemon task has a priority equal to or greater than the currently executing
 * task (the task that was interrupted), then *pxHigherPriorityTaskWoken will
 * get set to pdTRUE internally within the xTimerStopFromISR() function.  If
 * xTimerStopFromISR() sets this value to pdTRUE then a context switch should
 * be performed before the interrupt exits.
 *
 * @return pdFAIL will be returned if the stop command could not be sent to
 * the timer command queue.  pdPASS will be returned if the command was
 * successfully sent to the timer command queue.  When the command is actually
 * processed will depend on the priority of the timer service/daemon task
 * relative to other tasks in the system.  The timer service/daemon task
 * priority is set by the configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This scenario assumes xTimer has already been created and started.  When
 * // an interrupt occurs, the timer should be simply stopped.
 *
 * // The interrupt service routine that stops the timer.
 * void vAnExampleInterruptServiceRoutine( void )
 * {
 * BaseType_t xHigherPriorityTaskWoken = pdFALSE;
 *
 *     // The interrupt has occurred - simply stop the timer.
 *     // xHigherPriorityTaskWoken was set to pdFALSE where it was defined
 *     // (within this function).  As this is an interrupt service routine, only
 *     // FreeRTOS API functions that end in "FromISR" can be used.
 *     if( xTimerStopFromISR( xTimer, &xHigherPriorityTaskWoken ) != pdPASS )
 *     {
 *         // The stop command was not executed successfully.  Take appropriate
 *         // action here.
 *     }
 *
 *     // If xHigherPriorityTaskWoken equals pdTRUE, then a context switch
 *     // should be performed.  The syntax required to perform a context switch
 *     // from inside an ISR varies from port to port, and from compiler to
 *     // compiler.  Inspect the demos for the port you are using to find the
 *     // actual syntax required.
 *     if( xHigherPriorityTaskWoken != pdFALSE )
 *     {
 *         // Call the interrupt safe yield function here (actual function
 *         // depends on the FreeRTOS port being used).
 *     }
 * }
 * @endverbatim
 */



/**
 * BaseType_t xTimerChangePeriodFromISR( TimerHandle_t xTimer,
 *                                       TickType_t xNewPeriod,
 *                                       BaseType_t *pxHigherPriorityTaskWoken );
 *
 * A version of xTimerChangePeriod() that can be called from an interrupt
 * service routine.
 *
 * @param xTimer The handle of the timer that is having its period changed.
 *
 * @param xNewPeriod The new period for xTimer. Timer periods are specified in
 * tick periods, so the constant portTICK_PERIOD_MS can be used to convert a time
 * that has been specified in milliseconds.  For example, if the timer must
 * expire after 100 ticks, then xNewPeriod should be set to 100.  Alternatively,
 * if the timer must expire after 500ms, then xNewPeriod can be set to
 * ( 500 / portTICK_PERIOD_MS ) provided configTICK_RATE_HZ is less than
 * or equal to 1000.
 *
 * @param pxHigherPriorityTaskWoken The timer service/daemon task spends most
 * of its time in the Blocked state, waiting for messages to arrive on the timer
 * command queue.  Calling xTimerChangePeriodFromISR() writes a message to the
 * timer command queue, so has the potential to transition the timer service/
 * daemon task out of the Blocked state.  If calling xTimerChangePeriodFromISR()
 * causes the timer service/daemon task to leave the Blocked state, and the
 * timer service/daemon task has a priority equal to or greater than the
 * currently executing task (the task that was interrupted), then
 * *pxHigherPriorityTaskWoken will get set to pdTRUE internally within the
 * xTimerChangePeriodFromISR() function.  If xTimerChangePeriodFromISR() sets
 * this value to pdTRUE then a context switch should be performed before the
 * interrupt exits.
 *
 * @return pdFAIL will be returned if the command to change the timers period
 * could not be sent to the timer command queue.  pdPASS will be returned if the
 * command was successfully sent to the timer command queue.  When the command
 * is actually processed will depend on the priority of the timer service/daemon
 * task relative to other tasks in the system.  The timer service/daemon task
 * priority is set by the configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This scenario assumes xTimer has already been created and started.  When
 * // an interrupt occurs, the period of xTimer should be changed to 500ms.
 *
 * // The interrupt service routine that changes the period of xTimer.
 * void vAnExampleInterruptServiceRoutine( void )
 * {
 * BaseType_t xHigherPriorityTaskWoken = pdFALSE;
 *
 *     // The interrupt has occurred - change the period of xTimer to 500ms.
 *     // xHigherPriorityTaskWoken was set to pdFALSE where it was defined
 *     // (within this function).  As this is an interrupt service routine, only
 *     // FreeRTOS API functions that end in "FromISR" can be used.
 *     if( xTimerChangePeriodFromISR( xTimer, &xHigherPriorityTaskWoken ) != pdPASS )
 *     {
 *         // The command to change the timers period was not executed
 *         // successfully.  Take appropriate action here.
 *     }
 *
 *     // If xHigherPriorityTaskWoken equals pdTRUE, then a context switch
 *     // should be performed.  The syntax required to perform a context switch
 *     // from inside an ISR varies from port to port, and from compiler to
 *     // compiler.  Inspect the demos for the port you are using to find the
 *     // actual syntax required.
 *     if( xHigherPriorityTaskWoken != pdFALSE )
 *     {
 *         // Call the interrupt safe yield function here (actual function
 *         // depends on the FreeRTOS port being used).
 *     }
 * }
 * @endverbatim
 */



/**
 * BaseType_t xTimerResetFromISR(   TimerHandle_t xTimer,
 *                                  BaseType_t *pxHigherPriorityTaskWoken );
 *
 * A version of xTimerReset() that can be called from an interrupt service
 * routine.
 *
 * @param xTimer The handle of the timer that is to be started, reset, or
 * restarted.
 *
 * @param pxHigherPriorityTaskWoken The timer service/daemon task spends most
 * of its time in the Blocked state, waiting for messages to arrive on the timer
 * command queue.  Calling xTimerResetFromISR() writes a message to the timer
 * command queue, so has the potential to transition the timer service/daemon
 * task out of the Blocked state.  If calling xTimerResetFromISR() causes the
 * timer service/daemon task to leave the Blocked state, and the timer service/
 * daemon task has a priority equal to or greater than the currently executing
 * task (the task that was interrupted), then *pxHigherPriorityTaskWoken will
 * get set to pdTRUE internally within the xTimerResetFromISR() function.  If
 * xTimerResetFromISR() sets this value to pdTRUE then a context switch should
 * be performed before the interrupt exits.
 *
 * @return pdFAIL will be returned if the reset command could not be sent to
 * the timer command queue.  pdPASS will be returned if the command was
 * successfully sent to the timer command queue.  When the command is actually
 * processed will depend on the priority of the timer service/daemon task
 * relative to other tasks in the system, although the timers expiry time is
 * relative to when xTimerResetFromISR() is actually called.  The timer service/daemon
 * task priority is set by the configTIMER_TASK_PRIORITY configuration constant.
 *
 * Example usage:
 * @verbatim
 * // This scenario assumes xBacklightTimer has already been created.  When a
 * // key is pressed, an LCD back-light is switched on.  If 5 seconds pass
 * // without a key being pressed, then the LCD back-light is switched off.  In
 * // this case, the timer is a one-shot timer, and unlike the example given for
 * // the xTimerReset() function, the key press event handler is an interrupt
 * // service routine.
 *
 * // The callback function assigned to the one-shot timer.  In this case the
 * // parameter is not used.
 * void vBacklightTimerCallback( TimerHandle_t pxTimer )
 * {
 *     // The timer expired, therefore 5 seconds must have passed since a key
 *     // was pressed.  Switch off the LCD back-light.
 *     vSetBacklightState( BACKLIGHT_OFF );
 * }
 *
 * // The key press interrupt service routine.
 * void vKeyPressEventInterruptHandler( void )
 * {
 * BaseType_t xHigherPriorityTaskWoken = pdFALSE;
 *
 *     // Ensure the LCD back-light is on, then reset the timer that is
 *     // responsible for turning the back-light off after 5 seconds of
 *     // key inactivity.  This is an interrupt service routine so can only
 *     // call FreeRTOS API functions that end in "FromISR".
 *     vSetBacklightState( BACKLIGHT_ON );
 *
 *     // xTimerStartFromISR() or xTimerResetFromISR() could be called here
 *     // as both cause the timer to re-calculate its expiry time.
 *     // xHigherPriorityTaskWoken was initialised to pdFALSE when it was
 *     // declared (in this function).
 *     if( xTimerResetFromISR( xBacklightTimer, &xHigherPriorityTaskWoken ) != pdPASS )
 *     {
 *         // The reset command was not executed successfully.  Take appropriate
 *         // action here.
 *     }
 *
 *     // Perform the rest of the key processing here.
 *
 *     // If xHigherPriorityTaskWoken equals pdTRUE, then a context switch
 *     // should be performed.  The syntax required to perform a context switch
 *     // from inside an ISR varies from port to port, and from compiler to
 *     // compiler.  Inspect the demos for the port you are using to find the
 *     // actual syntax required.
 *     if( xHigherPriorityTaskWoken != pdFALSE )
 *     {
 *         // Call the interrupt safe yield function here (actual function
 *         // depends on the FreeRTOS port being used).
 *     }
 * }
 * @endverbatim
 */




/**
 * BaseType_t xTimerPendFunctionCallFromISR( PendedFunction_t xFunctionToPend,
 *                                          void *pvParameter1,
 *                                          uint32_t ulParameter2,
 *                                          BaseType_t *pxHigherPriorityTaskWoken );
 *
 *
 * Used from application interrupt service routines to defer the execution of a
 * function to the RTOS daemon task (the timer service task, hence this function
 * is implemented in timers.c and is prefixed with 'Timer').
 *
 * Ideally an interrupt service routine (ISR) is kept as short as possible, but
 * sometimes an ISR either has a lot of processing to do, or needs to perform
 * processing that is not deterministic.  In these cases
 * xTimerPendFunctionCallFromISR() can be used to defer processing of a function
 * to the RTOS daemon task.
 *
 * A mechanism is provided that allows the interrupt to return directly to the
 * task that will subsequently execute the pended callback function.  This
 * allows the callback function to execute contiguously in time with the
 * interrupt - just as if the callback had executed in the interrupt itself.
 *
 * @param xFunctionToPend The function to execute from the timer service/
 * daemon task.  The function must conform to the PendedFunction_t
 * prototype.
 *
 * @param pvParameter1 The value of the callback function's first parameter.
 * The parameter has a void * type to allow it to be used to pass any type.
 * For example, unsigned longs can be cast to a void *, or the void * can be
 * used to point to a structure.
 *
 * @param ulParameter2 The value of the callback function's second parameter.
 *
 * @param pxHigherPriorityTaskWoken As mentioned above, calling this function
 * will result in a message being sent to the timer daemon task.  If the
 * priority of the timer daemon task (which is set using
 * configTIMER_TASK_PRIORITY in FreeRTOSConfig.h) is higher than the priority of
 * the currently running task (the task the interrupt interrupted) then
 * *pxHigherPriorityTaskWoken will be set to pdTRUE within
 * xTimerPendFunctionCallFromISR(), indicating that a context switch should be
 * requested before the interrupt exits.  For that reason
 * *pxHigherPriorityTaskWoken must be initialised to pdFALSE.  See the
 * example code below.
 *
 * @return pdPASS is returned if the message was successfully sent to the
 * timer daemon task, otherwise pdFALSE is returned.
 *
 * Example usage:
 * @verbatim
 *
 *  // The callback function that will execute in the context of the daemon task.
 *  // Note callback functions must all use this same prototype.
 *  void vProcessInterface( void *pvParameter1, uint32_t ulParameter2 )
 *  {
 *      BaseType_t xInterfaceToService;
 *
 *      // The interface that requires servicing is passed in the second
 *      // parameter.  The first parameter is not used in this case.
 *      xInterfaceToService = ( BaseType_t ) ulParameter2;
 *
 *      // ...Perform the processing here...
 *  }
 *
 *  // An ISR that receives data packets from multiple interfaces
 *  void vAnISR( void )
 *  {
 *      BaseType_t xInterfaceToService, xHigherPriorityTaskWoken;
 *
 *      // Query the hardware to determine which interface needs processing.
 *      xInterfaceToService = prvCheckInterfaces();
 *
 *      // The actual processing is to be deferred to a task.  Request the
 *      // vProcessInterface() callback function is executed, passing in the
 *      // number of the interface that needs processing.  The interface to
 *      // service is passed in the second parameter.  The first parameter is
 *      // not used in this case.
 *      xHigherPriorityTaskWoken = pdFALSE;
 *      xTimerPendFunctionCallFromISR( vProcessInterface, NULL, ( uint32_t ) xInterfaceToService, &xHigherPriorityTaskWoken );
 *
 *      // If xHigherPriorityTaskWoken is now set to pdTRUE then a context
 *      // switch should be requested.  The macro used is port specific and will
 *      // be either portYIELD_FROM_ISR() or portEND_SWITCHING_ISR() - refer to
 *      // the documentation page for the port being used.
 *      portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
 *
 *  }
 * @endverbatim
 */
BaseType_t xTimerPendFunctionCallFromISR( PendedFunction_t xFunctionToPend,
                                          void * pvParameter1,
                                          uint32_t ulParameter2,
                                          BaseType_t * pxHigherPriorityTaskWoken ) ;

/**
 * BaseType_t xTimerPendFunctionCall( PendedFunction_t xFunctionToPend,
 *                                    void *pvParameter1,
 *                                    uint32_t ulParameter2,
 *                                    TickType_t xTicksToWait );
 *
 *
 * Used to defer the execution of a function to the RTOS daemon task (the timer
 * service task, hence this function is implemented in timers.c and is prefixed
 * with 'Timer').
 *
 * @param xFunctionToPend The function to execute from the timer service/
 * daemon task.  The function must conform to the PendedFunction_t
 * prototype.
 *
 * @param pvParameter1 The value of the callback function's first parameter.
 * The parameter has a void * type to allow it to be used to pass any type.
 * For example, unsigned longs can be cast to a void *, or the void * can be
 * used to point to a structure.
 *
 * @param ulParameter2 The value of the callback function's second parameter.
 *
 * @param xTicksToWait Calling this function will result in a message being
 * sent to the timer daemon task on a queue.  xTicksToWait is the amount of
 * time the calling task should remain in the Blocked state (so not using any
 * processing time) for space to become available on the timer queue if the
 * queue is found to be full.
 *
 * @return pdPASS is returned if the message was successfully sent to the
 * timer daemon task, otherwise pdFALSE is returned.
 *
 */
BaseType_t xTimerPendFunctionCall( PendedFunction_t xFunctionToPend,
                                   void * pvParameter1,
                                   uint32_t ulParameter2,
                                   TickType_t xTicksToWait ) ;

/**
 * char * pcTimerGetName( TimerHandle_t xTimer );
 *
 * Returns the name that was assigned to a timer when the timer was created.
 *
 * @param xTimer The handle of the timer being queried.
 *
 * @return The name assigned to the timer specified by the xTimer parameter.
 */
const char * pcTimerGetName( TimerHandle_t xTimer ) ; /*lint !e971 Unqualified char types are allowed for strings and single characters only. */

/**
 * void vTimerSetReloadMode( TimerHandle_t xTimer, const UBaseType_t uxAutoReload );
 *
 * Updates a timer to be either an auto-reload timer, in which case the timer
 * automatically resets itself each time it expires, or a one-shot timer, in
 * which case the timer will only expire once unless it is manually restarted.
 *
 * @param xTimer The handle of the timer being updated.
 *
 * @param uxAutoReload If uxAutoReload is set to pdTRUE then the timer will
 * expire repeatedly with a frequency set by the timer's period (see the
 * xTimerPeriodInTicks parameter of the xTimerCreate() API function).  If
 * uxAutoReload is set to pdFALSE then the timer will be a one-shot timer and
 * enter the dormant state after it expires.
 */
void vTimerSetReloadMode( TimerHandle_t xTimer,
                          const UBaseType_t uxAutoReload ) ;

/**
 * UBaseType_t uxTimerGetReloadMode( TimerHandle_t xTimer );
 *
 * Queries a timer to determine if it is an auto-reload timer, in which case the timer
 * automatically resets itself each time it expires, or a one-shot timer, in
 * which case the timer will only expire once unless it is manually restarted.
 *
 * @param xTimer The handle of the timer being queried.
 *
 * @return If the timer is an auto-reload timer then pdTRUE is returned, otherwise
 * pdFALSE is returned.
 */
UBaseType_t uxTimerGetReloadMode( TimerHandle_t xTimer ) ;

/**
 * TickType_t xTimerGetPeriod( TimerHandle_t xTimer );
 *
 * Returns the period of a timer.
 *
 * @param xTimer The handle of the timer being queried.
 *
 * @return The period of the timer in ticks.
 */
TickType_t xTimerGetPeriod( TimerHandle_t xTimer ) ;

/**
 * TickType_t xTimerGetExpiryTime( TimerHandle_t xTimer );
 *
 * Returns the time in ticks at which the timer will expire.  If this is less
 * than the current tick count then the expiry time has overflowed from the
 * current time.
 *
 * @param xTimer The handle of the timer being queried.
 *
 * @return If the timer is running then the time in ticks at which the timer
 * will next expire is returned.  If the timer is not running then the return
 * value is undefined.
 */
TickType_t xTimerGetExpiryTime( TimerHandle_t xTimer ) ;

/*
 * Functions beyond this part are not part of the public API and are intended
 * for use by the kernel only.
 */
BaseType_t xTimerCreateTimerTask( void ) ;

/*
 * Splitting the xTimerGenericCommand into two sub functions and making it a macro
 * removes a recursion path when called from ISRs. This is primarily for the XCore
 * XCC port which detects the recursion path and throws an error during compilation
 * when this is not split.
 */
BaseType_t xTimerGenericCommandFromTask( TimerHandle_t xTimer,
                                         const BaseType_t xCommandID,
                                         const TickType_t xOptionalValue,
                                         BaseType_t * pxHigherPriorityTaskWoken,
                                         const TickType_t xTicksToWait ) ;

BaseType_t xTimerGenericCommandFromISR( TimerHandle_t xTimer,
                                        const BaseType_t xCommandID,
                                        const TickType_t xOptionalValue,
                                        BaseType_t * pxHigherPriorityTaskWoken,
                                        const TickType_t xTicksToWait ) ;







    void vTimerSetTimerNumber( TimerHandle_t xTimer,
                               UBaseType_t uxTimerNumber ) ;
    UBaseType_t uxTimerGetTimerNumber( TimerHandle_t xTimer ) ;
// # 1378 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/timers.h"
/* *INDENT-OFF* */



/* *INDENT-ON* */
// # 49 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/stack_macros.h" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */




/*
 * Call the stack overflow hook function if the stack of the task being swapped
 * out is currently overflowed, or looks like it might have overflowed in the
 * past.
 *
 * Setting configCHECK_FOR_STACK_OVERFLOW to 1 will cause the macro to check
 * the current stack state only - comparing the current top of stack value to
 * the stack limit.  Setting configCHECK_FOR_STACK_OVERFLOW to greater than 1
 * will also cause the last few stack bytes to be checked to ensure the value
 * to which the bytes were set when the task was created have not been
 * overwritten.  Note this second test does not guarantee that an overflowed
 * stack will always be recognised.
 */

/*-----------------------------------------------------------*/

/*
 * portSTACK_LIMIT_PADDING is a number of extra words to consider to be in
 * use on the stack.
 */
// # 67 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/stack_macros.h"
/*-----------------------------------------------------------*/
// # 83 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/stack_macros.h"
/*-----------------------------------------------------------*/
// # 102 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/stack_macros.h"
/*-----------------------------------------------------------*/
// # 126 "/Users/reitobia/repos2/FreeRTOS-Kernel/include/stack_macros.h"
/*-----------------------------------------------------------*/

/* Remove stack overflow macro if not being used. */
// # 50 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2

/* Verifast proof setup 
 * 
 * Note that redefinitions of macros must be included after
 * original ones have been included.
 */

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/verifast_proof_defs.h" 1
/*
 * This file contains defines to configure the VeriFast proof setup.
 *
 */



    // Delete keywords VeriFast canot parse (in some contexts)



    /* `projdefs.h` defines `pdFALSE` and `pdTRUE` as 0 and 1 of type
     * `BaseType_t`. Both are assigned to variables smaller or
     * unsigned types. While that's safe in practice, it is not
     * type safe. Hence we define 
     */
// # 58 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof/stack_predicates.h" 1




/*@
// Represents a stack that grows down (cf. RP2040 stack)
predicate stack_p_2(StackType_t * pxStack, 
                    uint32_t ulStackDepth, 
                    StackType_t * pxTopOfStack, 
                    uint32_t ulFreeBytes,
                    uint32_t ulUsedCells,
                    uint32_t ulUnalignedBytes) =
    malloc_block_chars((char*) pxStack, ulStackDepth * sizeof(StackType_t)) &*&
    // Free stack cells. The size of this memory block is not necessarily a 
    // multiple of sizeof(StackType_t), due to bitvector arithmetic.
    // At least, we cannot prove it.
    chars((char*) pxStack, ulFreeBytes, _) &*&
    //integer_(pxTopOfStack + sizeof(StackType_t), sizeof(StackType_t), false, _) &*&;

    // If there is any free memory left in this stack,
    // pxTopOfStack points to the last sizeof(StackType_t) number of bytes.
    (char*) pxStack + ulFreeBytes == (char*) pxTopOfStack + sizeof(StackType_t) &*&
    // Used stack cells
    integers_(pxTopOfStack + 1, sizeof(StackType_t), false, ulUsedCells, _) &*&
    // Unaligned rest
    unalignedRestOfStack_p((char*) pxStack + ulFreeBytes + sizeof(StackType_t) * ulUsedCells, 
                           ulUnalignedBytes);

predicate unalignedRestOfStack_p(char* p, uint32_t ulUnalignedBytes) =
    chars(p, ulUnalignedBytes, _);
@*/

/*@
// Represents a stack that grows down (cf. RP2040 stack)
predicate stack_p(StackType_t * pxStack, uint32_t ulStackDepth, StackType_t * pxTopOfStack, uint32_t freeCells) =
	integers_(pxStack, sizeof(StackType_t), false, ulStackDepth, _) &*&
    ulStackDepth > 0 &*&
    freeCells >= 0 &*&
    pxTopOfStack == pxStack + freeCells -1 &*&
    0 <= freeCells &*& freeCells <= ulStackDepth;
//	usedMem == pxStack - pxTopOfStack
//	freeMem == ulStackDepth - usedMem
	//freeCells * sizeof(StackType_t) == ulStackDepth * sizeof(StackType_t) - ((char*) pxStack - (char*) pxTopOfStack) &*&
//	usedCells * sizeof(StackType_t) == ((char*) pxStack - (char*) pxTopOfStack);
@*/

/*/@
lemma void split_stack(StackType_t * pxStack, int offset)
requires stack_p(pxStack,?ulStackDepth, ?pxTopOfStack, ?freeMem, _) &*& 0 <= offset &*& 
                offset * sizeof(StackType_t) < ulStackDepth;
ensures integers_(pxStack, sizeof(StackType_t), true, offset * sizeof(StackType_t), _) &*&
                integers_(pxStack + offset * sizeof(StackType_t), sizeof(StackType_t), true, ulStackDepth - offset * sizeof(StackType_t), _) ;
{
	open stack_p(_, _, _, _);
	integers__split(pxStack, offset * sizeof(StackType_t) );
}
@*/

/*@
// TODO: Do we need this lemma or is it usually cleaner to split stack manually?
lemma void getTopOfStack(StackType_t* pxStack, StackType_t* pxTopOfStack)
requires stack_p(pxStack,?ulStackDepth, pxTopOfStack, ?freeCells) &*&
                 freeCells > 0;
ensures // free cells minus top cell
        integers_(pxStack, sizeof(StackType_t), false, freeCells-1, _)	&*&
        // top stack cell
		integer_(pxStack + freeCells-1, sizeof(StackType_t), false, _) &*&
        // used stack cells
		integers_(pxStack + freeCells, sizeof(StackType_t), false, 
                  ulStackDepth - freeCells, _) &*&
        // stack contraints necessary to close `stack_p` again
        ulStackDepth > 0 &*&
        freeCells >= 0 &*&
        pxTopOfStack == pxStack + freeCells -1 &*&
        0 <= freeCells &*& freeCells <= ulStackDepth;
{
    open stack_p(_, _, _, _);
    integers__split(pxStack, freeCells-1);
    open integers_(pxStack + (freeCells-1), _, _, _, _);
}
@*/
// # 59 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof/task_predicates.h" 1




// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof/nathan/list_predicates.h" 1




/*
 * The code below has been taken from:
 * pull request:
 * https://github.com/FreeRTOS/FreeRTOS/pull/836
 * file:
 * FreeRTOS/Test/VeriFast/include/proof/list.h
 *
 */

/*@
predicate xLIST_ITEM(
	struct xLIST_ITEM *n,
	TickType_t xItemValue,
	struct xLIST_ITEM *pxNext,
	struct xLIST_ITEM *pxPrevious,
	struct xLIST *pxContainer;) =
	n->xItemValue |-> xItemValue &*&
	n->pxNext |-> pxNext &*&
	n->pxPrevious |-> pxPrevious &*&
	n->pvOwner |-> _ &*&
	n->pxContainer |-> pxContainer;
@*/
// # 6 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof/task_predicates.h" 2


/*@
// This predicate represents the memory corresponding to an
// uninitialised instance of type `TCB_t` aka `tskTaskControlBlock`.
predicate uninit_TCB_p(TCB_t * tcb, int stackSize) =
    malloc_block_tskTaskControlBlock(tcb) &*&
    tcb->pxTopOfStack |-> _ &*&

    xLIST_ITEM(&tcb->xStateListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xStateListItem) &*&
    xLIST_ITEM(&tcb->xEventListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xEventListItem) &*&
    
    tcb->uxPriority |-> _ &*&

    tcb->pxStack |-> ?stackPtr &*&
    stackPtr != 0 &*&
    (char*) stackPtr + stackSize <=  (char*) UINTPTR_MAX &*&
    chars_((char*) stackPtr, stackSize, _) &*&
    malloc_block_chars((char*) stackPtr, stackSize) &*&

    tcb->xTaskRunState |-> _ &*&
    tcb->xIsIdle |-> _ &*&
    
    // Assumes macro `configMAX_TASK_NAME_LEN` evaluates to 16.
    chars_(tcb->pcTaskName, 16, _) &*&

    tcb->uxCriticalNesting |-> _ &*&
    tcb->uxTCBNumber |-> _ &*&
    tcb->uxTaskNumber |-> _ &*&
    tcb->uxBasePriority |-> _ &*&
    tcb->uxMutexesHeld |-> _ &*&

    // void * pvThreadLocalStoragePointers[ 5 ];
    pointers_(tcb->pvThreadLocalStoragePointers, 5, _) &*&

    // We assume that the macro `configTASK_NOTIFICATION_ARRAY_ENTRIES`
    // evaluates to 1.
    integers__(tcb->ulNotifiedValue, 4, false, 1, _) &*&
    uchars_(tcb->ucNotifyState, 1, _) &*&

    tcb->ucDelayAborted |-> _;
@*/


/*@
// This predicate represents the memory corresponding to an
// initialised instance of type `TCB_t` aka `tskTaskControlBlock`.
predicate TCB_p(TCB_t * tcb, uint32_t ulFreeBytesOnStack) =
    malloc_block_tskTaskControlBlock(tcb) &*&
    tcb->pxStack |-> ?stackPtr &*&
    tcb->pxTopOfStack |-> ?topPtr &*&
    stack_p_2(stackPtr, ?ulStackDepth, topPtr, 
              ulFreeBytesOnStack, ?ulUsedCells, ?ulUnalignedBytes) &*&

    xLIST_ITEM(&tcb->xStateListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xStateListItem) &*&
    xLIST_ITEM(&tcb->xEventListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xEventListItem) &*&
    
    tcb->uxPriority |-> _ &*&

    tcb->xTaskRunState |-> _ &*&
    tcb->xIsIdle |-> _ &*&
    
    // Assumes macro `configMAX_TASK_NAME_LEN` evaluates to 16.
    chars_(tcb->pcTaskName, 16, _) &*&

    tcb->uxCriticalNesting |-> _ &*&
    tcb->uxTCBNumber |-> _ &*&
    tcb->uxTaskNumber |-> _ &*&
    tcb->uxBasePriority |-> _ &*&
    tcb->uxMutexesHeld |-> _ &*&

    // void * pvThreadLocalStoragePointers[ 5 ];
    pointers(tcb->pvThreadLocalStoragePointers, 5, _) &*&

    // We assume that the macro `configTASK_NOTIFICATION_ARRAY_ENTRIES`
    // evaluates to 1.
    integers_(tcb->ulNotifiedValue, 4, false, 1, _) &*&
    uchars(tcb->ucNotifyState, 1, _) &*&

    tcb->ucDelayAborted |-> _;
@*/
// # 60 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/verifast_RP2040_axioms.h" 1





/*
 * The lemmas in this file axiomatize that the RP2040 architecture uses
 * 32bit pointers.
 */

/*@
// Axiomatizes that: 0 <= ptr <= 2^32 - 1
lemma void ptr_range<t>(t* ptr);
requires true;
ensures 0 <= (int) ptr &*& (int) ptr <= 4294967295;
@*/
// # 61 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof/verifast_prelude_extended.h" 1



/* This file contains axioms that would naturally fit into prelude.h
 * but are missing.
 */

/* Reminder:

predicate chars_(char *array, int count; list<option<char> > cs) =
    count == 0 ?
        cs == nil
    :
        char_(array, ?c) &*& chars_(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

predicate chars(char *array, int count; list<char> cs) =
    count == 0 ?
        cs == nil
    :
        character(array, ?c) &*& chars(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);


lemma_auto void chars__to_chars(char *array);
    requires [?f]chars_(array, ?count, ?cs) &*& cs == map(some, map(the, cs));
    ensures [f]chars(array, count, map(the, cs));



predicate integers__(void *p, int size, bool signed_, int count; list<option<int> > vs) =
    count == 0 ?
        vs == nil
    :
        integer__(p, size, signed_, ?v0) &*& integers__(p + size, size, signed_, count - 1, ?vs0) &*& vs == cons(v0, vs0);

predicate integers_(void *p, int size, bool signed_, int count; list<int> vs) =
    count == 0 ?
        vs == nil
    :
        integer_(p, size, signed_, ?v0) &*& integers_(p + size, size, signed_, count - 1, ?vs0) &*& vs == cons(v0, vs0);


 */




/*@
lemma_auto void integers___to_integers_(void *p);
    requires [?f]integers__(p, ?size, ?signed_, ?count, _);
    ensures [f]integers_(p, size, signed_, count, _);
@*/


/*@
lemma void chars_split_at(char* start_ptr, char* split_ptr)
requires chars(start_ptr, ?count, ?vs) &*& 
         start_ptr <= split_ptr &*& split_ptr < start_ptr + count;
ensures  chars(start_ptr, ?c1, ?vs1) &*&
         chars(split_ptr, ?c2, ?vs2) &*&
         start_ptr + c1 == split_ptr &*&
         c1 + c2 == count;
{
    if( start_ptr == split_ptr ) 
    {
        close chars(start_ptr, 0, nil);
    } else
    {
        open chars(start_ptr, _, _);
        chars_split_at(start_ptr+1, split_ptr);
        assert( chars(start_ptr+1, ?c1, _) );
        close chars(start_ptr, c1+1, _);
    }
}
@*/


/*@
lemma void division_remainder_def(int l, int r);
requires l >= 0 &*& r > 0 &*& r < l;
ensures l == (l % r) + (l / r) * r &*&
0 <= (l % r) &*&
(l % r) < r;
@*/

/*@
lemma void chars_to_max_integers__suffix(char* startPtr, int intSize, bool signed_)
requires chars(startPtr, ?count, ?vs) &*& intSize > 0 &*& count > intSize;
ensures  chars(startPtr, ?cc, _) &*&
         integers_(?intStartPtr, intSize, signed_, ?ci, _) &*&
         count == cc + ci * intSize &*&
         intStartPtr == startPtr + cc &*&
         cc < intSize &*&
         ci == count / intSize;
{
    int rem = count % intSize;
    int ci = count / intSize;
    
    division_remainder_def(count, intSize);
    chars_split(startPtr, rem);
    chars_to_integers_(startPtr + rem, intSize, signed_, ci);

}
@*/
// # 62 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof/verifast_bitops_extended.h" 1



/*@
// TODO: Can we remove this?
lemma void bitand_idempotent_right(int l, int r);
requires true;
ensures (l & r) == ((l & r) & r);
@*/
// # 63 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2
// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof_setup/verifast_asm.h" 1



/* VeriFast does not support inline assembler.
 * The following definitions replace macros that would normally evaluate to
 * inline assember by failing assertions.
 */

/* VeriFast treats `assert` as keyword and does not support calling it
 * in many contexts where function calls are permitted. */
bool assert_fct(bool b, const char*)
{
    assert(b);
    return b;
}

// Port macros were originally defined in `portmacro.h`.




/* Additional reason for rewrite:
 * VeriFast does not support embedding block statements that consist of
 * multiple elemts in expression contexts, e.g., `({e1; e2})`.
 */
// # 64 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2

    //#include "verifast_lock_predicates.h"

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof/snippets/rp2040_port_c_snippets.c" 1
/*
 * This file contains code snippets from:
 * portable/ThirdParty/GCC/RP2040/port.c
 */



// Note currently we support configNUM_CORES == 1 with SMP, thought it isn't 100% clear why you wouldn't
// just use the non SMP version; keeping around for now in case the code bases are merged.


/* Constants required to manipulate the NVIC. */
// # 27 "/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/proof/snippets/rp2040_port_c_snippets.c"
/* Constants required to set up the initial stack. */


/* The systick is a 24-bit counter. */


/* A fiddle factor to estimate the number of SysTick counts that would have
 * occurred while the SysTick counter is stopped during tickless idle
 * calculations. */




/* Let the user override the pre-loading of the initial LR with the address of
 * prvTaskExitError() in case it messes up unwinding of the stack in the
 * debugger. */






/*
 * Setup the timer to generate the tick interrupts.  The implementation in this
 * file is weak to allow application writers to change the timer used to
 * generate the tick interrupt.
 */
void vPortSetupTimerInterrupt( void );

/*
 * Exception handlers.
 */
void xPortPendSVHandler( void ) ;
void xPortSysTickHandler( void );
void vPortSVCHandler( void );

/*
 * Start first task is a separate function so it can be tested in isolation.
 */
static void vPortStartFirstTask( void ) ;

/*
 * Used to catch tasks that attempt to return from their implementing function.
 */
static void prvTaskExitError( void );




// -------------------------------------------------
// Validate stack predicate

/* Simulates creation and initialisation of a stack that grows down as on RP2040.
 */
StackType_t* test_stack_pred(uint32_t depth)
/*@ requires depth * sizeof(StackType_t) <= UINTPTR_MAX &*&
             depth <= UINT_MAX &*&
             depth > 0;
 @*/
/*@ ensures result == 0 ? true : stack_p(result, depth, ?top, depth) &*&
            malloc_block_chars((char*) result, depth * sizeof(StackType_t));
@*/
{
 StackType_t * stack;


    /* Allocate space for the stack used by the task being created. */
    stack = (StackType_t*) malloc( ( ( ( size_t ) depth ) * sizeof( StackType_t ) ) );
    if(stack == 0) return 0;

    memset(stack, 0, (unsigned int ) depth * sizeof(StackType_t));

    StackType_t* top = stack + depth -1;

    //@ chars_to_integers_(stack, sizeof(StackType_t), false, depth); 
    //@ close stack_p(stack, depth, top, depth);
    // integers_(stack0, 4, false, depth, _)
    return stack;
}
// -------------------------------------------------

/*
 * See header file for description.
 */
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
/*@ requires pxTopOfStack > 0 &*&
             stack_p_2(?pxStack, ?ulStackDepth, pxTopOfStack, ?ulFreeBytes, 
                       ?ulUsedCells, ?ulUnalignedBytes) &*&
             ulFreeBytes > 17 * sizeof(StackType_t) &*&
             pxStack > 0;
  @*/
/*@ ensures stack_p_2(pxStack, ulStackDepth, result, 
                      ulFreeBytes - sizeof(StackType_t) * 16, 
                      ulUsedCells + 16, 
                      ulUnalignedBytes) &*&
            result == pxTopOfStack - 16;
@*/
{
    //@ StackType_t* gOldTop = pxTopOfStack;
    //@ char* gcStack = (char*) pxStack;
    //@ open stack_p_2(_, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + ulFreeBytes - sizeof(StackType_t) );
    //@ assert( (char*) pxStack + ulFreeBytes == (char*) pxTopOfStack + sizeof(StackType_t) );

    // skip stack cell #0
    //@ chars_split(gcStack, ulFreeBytes - sizeof(StackType_t));
    //@ chars_to_integers_(gOldTop, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop);
    /* Simulate the stack frame as it would be created by a context switch
     * interrupt. */
    pxTopOfStack--; /* Offset added to account for the way the MCU uses the stack on entry/exit of interrupts. */

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 1, ulUsedCells + 1, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 2) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 1) == (char*) pxTopOfStack + sizeof(StackType_t) );

    // make stack cell #1 available
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 2));
    //@ chars_to_integers_(gOldTop-1, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop-1);
    *pxTopOfStack = ( 0x01000000 ); /* xPSR */
    //@ close integers_(gOldTop-1, sizeof(StackType_t), false, ulUsedCells+2, _);
    pxTopOfStack--;

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 2, ulUsedCells + 2, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 3) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 2) == (char*) pxTopOfStack + sizeof(StackType_t) );

    // prevent overflow
    //@ ptr_range<void>(pxCode);
    // make stack cell #2 available
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 3));
    //@ chars_to_integers_(gOldTop-2, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop-2);
    *pxTopOfStack = ( StackType_t ) pxCode; /* PC */
    //@ close integers_(gOldTop-2, sizeof(StackType_t), false, ulUsedCells+3, _);
    pxTopOfStack--;

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 3, ulUsedCells + 3, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 4) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 3) == (char*) pxTopOfStack + sizeof(StackType_t) );

    // prevent underflow
    //@ ptr_range<void>(prvTaskExitError);
    // make stack cell #3 available
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 4));
    //@ chars_to_integers_(gOldTop-3, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop-3);
    *pxTopOfStack = ( StackType_t ) prvTaskExitError; /* LR */
    //@ close integers_(gOldTop-3, sizeof(StackType_t), false, ulUsedCells+4, _);

    pxTopOfStack -= 5; /* R12, R3, R2 and R1. */

    // jump to stack cell #7
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 8));
    //@ chars_to_integers_(gOldTop-7, sizeof(StackType_t), false, 4);
    //@ integers__join(gOldTop-7);

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 8, ulUsedCells + 8, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 9) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 8) == (char*) pxTopOfStack + sizeof(StackType_t) );

    // prevent overflow
    //@ ptr_range<void>(pvParameters);

    // make stack cell #8 available
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 9));
    //@ chars_to_integers_(gOldTop-8, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop-8);
    *pxTopOfStack = ( StackType_t ) pvParameters; /* R0 */
    //@ close integers_(gOldTop-8, sizeof(StackType_t), false, ulUsedCells+9, _);

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack-1, ulFreeBytes - sizeof(StackType_t) * 9, ulUsedCells + 9, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);


    // skip stack cells #9 - #15, leave #16 unused
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 16));
    //@ chars_to_integers_(gOldTop-15, sizeof(StackType_t), false, 7);
    //@ integers__join(gOldTop-15);
    pxTopOfStack -= 8; /* R11..R4. */

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 16, ulUsedCells + 16, ulUnalignedBytes);
    //@ assert( stack_p_2(pxStack, ulStackDepth, gOldTop-16, ulFreeBytes - sizeof(StackType_t) * 16, ulUsedCells + 16, ulUnalignedBytes) );

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 17) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 16) == (char*) pxTopOfStack + sizeof(StackType_t) );

    return pxTopOfStack;
}
// # 68 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2

// # 1 "/Users/reitobia/repos2/FreeRTOS-Kernel/list.c" 1
/*
 * FreeRTOS SMP Kernel V202110.00
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
 */




/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
 * all the API functions to use the MPU wrappers.  That should only be done when
 * task.h is included from an application file. */





/* Lint e9021, e961 and e750 are suppressed as a MISRA exception justified
 * because the MPU ports require MPU_WRAPPERS_INCLUDED_FROM_API_FILE to be
 * defined for the header files above, but not in this file, in order to
 * generate the correct privileged Vs unprivileged linkage and placement. */


/*-----------------------------------------------------------
* PUBLIC LIST API documented in list.h
*----------------------------------------------------------*/

void vListInitialise( List_t * pxList )
{
    /* The list structure contains a list item which is used to mark the
     * end of the list.  To initialise the list the list end is inserted
     * as the only list entry. */
    pxList->pxIndex = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    /* The list end value is the highest possible value in the list to
     * ensure it remains at the end of the list. */
    pxList->xListEnd.xItemValue = ( TickType_t ) 0xffffffffUL;

    /* The list end next and previous pointers point to itself so we know
     * when the list is empty. */
    pxList->xListEnd.pxNext = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */
    pxList->xListEnd.pxPrevious = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;

    /* Write known values into the list if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
                                                  ;
                                                  ;
}
/*-----------------------------------------------------------*/

void vListInitialiseItem( ListItem_t * pxItem )
{
    /* Make sure the list item is not recorded as being on a list. */
    pxItem->pxContainer = 0;

    /* Write known values into the list item if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
                                                           ;
                                                            ;
}
/*-----------------------------------------------------------*/

void vListInsertEnd( List_t * pxList,
                     ListItem_t * pxNewListItem )
{
    ListItem_t * pxIndex = pxList->pxIndex;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
                                     ;
                                                 ;

    /* Insert a new list item into pxList, but rather than sort the list,
     * makes the new list item the last item to be removed by a call to
     * listGET_OWNER_OF_NEXT_ENTRY(). */
    pxNewListItem->pxNext = pxIndex;
    pxNewListItem->pxPrevious = pxIndex->pxPrevious;

    /* Only used during decision coverage testing. */
                           ;

    pxIndex->pxPrevious->pxNext = pxNewListItem;
    pxIndex->pxPrevious = pxNewListItem;

    /* Remember which list the item is in. */
    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;
}
/*-----------------------------------------------------------*/

void vListInsert( List_t * pxList,
                  ListItem_t * pxNewListItem )
{
    ListItem_t * pxIterator;
    const TickType_t xValueOfInsertion = pxNewListItem->xItemValue;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
                                     ;
                                                 ;

    /* Insert the new list item into the list, sorted in xItemValue order.
     *
     * If the list already contains a list item with the same item value then the
     * new list item should be placed after it.  This ensures that TCBs which are
     * stored in ready lists (all of which have the same xItemValue value) get a
     * share of the CPU.  However, if the xItemValue is the same as the back marker
     * the iteration loop below will not end.  Therefore the value is checked
     * first, and the algorithm slightly modified if necessary. */
    if( xValueOfInsertion == ( TickType_t ) 0xffffffffUL )
    {
        pxIterator = pxList->xListEnd.pxPrevious;
    }
    else
    {
        /* *** NOTE ***********************************************************
        *  If you find your application is crashing here then likely causes are
        *  listed below.  In addition see https://www.FreeRTOS.org/FAQHelp.html for
        *  more tips, and ensure configASSERT() is defined!
        *  https://www.FreeRTOS.org/a00110.html#configASSERT
        *
        *   1) Stack overflow -
        *      see https://www.FreeRTOS.org/Stacks-and-stack-overflow-checking.html
        *   2) Incorrect interrupt priority assignment, especially on Cortex-M
        *      parts where numerically high priority values denote low actual
        *      interrupt priorities, which can seem counter intuitive.  See
        *      https://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html and the definition
        *      of configMAX_SYSCALL_INTERRUPT_PRIORITY on
        *      https://www.FreeRTOS.org/a00110.html
        *   3) Calling an API function from within a critical section or when
        *      the scheduler is suspended, or calling an API function that does
        *      not end in "FromISR" from an interrupt.
        *   4) Using a queue or semaphore before it has been initialised or
        *      before the scheduler has been started (are interrupts firing
        *      before vTaskStartScheduler() has been called?).
        *   5) If the FreeRTOS port supports interrupt nesting then ensure that
        *      the priority of the tick interrupt is at or below
        *      configMAX_SYSCALL_INTERRUPT_PRIORITY.
        **********************************************************************/

        for( pxIterator = ( ListItem_t * ) &( pxList->xListEnd ); pxIterator->pxNext->xItemValue <= xValueOfInsertion; pxIterator = pxIterator->pxNext ) /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. *//*lint !e440 The iterator moves to a different value, not xValueOfInsertion. */
        {
            /* There is nothing to do here, just iterating to the wanted
             * insertion position. */
        }
    }

    pxNewListItem->pxNext = pxIterator->pxNext;
    pxNewListItem->pxNext->pxPrevious = pxNewListItem;
    pxNewListItem->pxPrevious = pxIterator;
    pxIterator->pxNext = pxNewListItem;

    /* Remember which list the item is in.  This allows fast removal of the
     * item later. */
    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;
}
/*-----------------------------------------------------------*/

UBaseType_t uxListRemove( ListItem_t * pxItemToRemove )
{
/* The list item knows which list it is in.  Obtain the list from the list
 * item. */
    List_t * pxList = pxItemToRemove->pxContainer;

    pxItemToRemove->pxNext->pxPrevious = pxItemToRemove->pxPrevious;
    pxItemToRemove->pxPrevious->pxNext = pxItemToRemove->pxNext;

    /* Only used during decision coverage testing. */
                           ;

    /* Make sure the index is left pointing to a valid item. */
    if( pxList->pxIndex == pxItemToRemove )
    {
        pxList->pxIndex = pxItemToRemove->pxPrevious;
    }
    else
    {
                                ;
    }

    pxItemToRemove->pxContainer = 0;
    ( pxList->uxNumberOfItems )--;

    return pxList->uxNumberOfItems;
}
/*-----------------------------------------------------------*/
// # 70 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c" 2


/* Lint e9021, e961 and e750 are suppressed as a MISRA exception justified
 * because the MPU ports require MPU_WRAPPERS_INCLUDED_FROM_API_FILE to be defined
 * for the header files above, but not in this file, in order to generate the
 * correct privileged Vs unprivileged linkage and placement. */


/* Set configUSE_STATS_FORMATTING_FUNCTIONS to 2 to include the stats formatting
 * functions but without including stdio.h here. */
// # 98 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/* Values that can be assigned to the ucNotifyState member of the TCB. */




/*
 * The value used to fill the stack of a task when the task is created.  This
 * is used purely for checking the high water mark for tasks.
 */


/* Bits used to record how a task's stack and TCB were allocated. */




/* If any of the following are set then task stacks are filled with a known
 * value so the high water mark can be determined.  If none of the following are
 * set then don't fill the stack so there is no unnecessary dependency on memset. */






/*
 * Macros used by vListTask to indicate which state a task is in.
 */






/*
 * Some kernel aware debuggers require the data the debugger needs access to to
 * be global, rather than file scope.
 */




/* The name allocated to the Idle task.  This can be overridden by defining
 * configIDLE_TASK_NAME in FreeRTOSConfig.h. */






/* If configUSE_PORT_OPTIMISED_TASK_SELECTION is 0 then task selection is
 * performed in a generic way that is not optimised to any particular
 * microcontroller architecture. */

/* uxTopReadyPriority holds the priority of the highest priority ready
 * state task. */
// # 162 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    /*-----------------------------------------------------------*/

/* Define away taskRESET_READY_PRIORITY() and portRESET_READY_PRIORITY() as
 * they are only required when a port optimised method of task selection is
 * being used. */
// # 196 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/

/* pxDelayedTaskList and pxOverflowDelayedTaskList are switched when the tick
 * count overflows. */
// # 214 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/

/*
 * Place the task represented by pxTCB into the appropriate ready list for
 * the task.  It is inserted at the end of the list.
 */





/*-----------------------------------------------------------*/

/*
 * Several functions take a TaskHandle_t parameter that can optionally be NULL,
 * where NULL is used to indicate that the handle of the currently executing
 * task should be used in place of the parameter.  This macro simply checks to
 * see if the parameter is NULL and returns a pointer to the appropriate TCB.
 */


/* The item value of the event list item is normally used to hold the priority
 * of the task to which it belongs (coded to allow it to be held in reverse
 * priority order).  However, it is occasionally borrowed for other purposes.  It
 * is important its value is not updated due to a task priority change while it is
 * being used for another purpose.  The following bit definition is used to inform
 * the scheduler that the value should not be changed - in which case it is the
 * responsibility of whichever module is using the value to ensure it gets set back
 * to its original value when it is released. */






/* Indicates that the task is not actively running on any core. */


/* Indicates that the task is actively running but scheduled to yield. */


/* Returns pdTRUE if the task is actively running and not scheduled to yield. */


typedef BaseType_t TaskRunning_t;

/*
 * Task control block.  A task control block (TCB) is allocated for each task,
 * and stores task state information, including a pointer to the task's context
 * (the task's run time environment, including register values)
 */
typedef struct tskTaskControlBlock /* The old naming convention is used to prevent breaking kernel aware debuggers. */
{
    volatile StackType_t * pxTopOfStack; /*< Points to the location of the last item placed on the tasks stack.  THIS MUST BE THE FIRST MEMBER OF THE TCB STRUCT. */
// # 277 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    ListItem_t xStateListItem; /*< The list that the state list item of a task is reference from denotes the state of that task (Ready, Blocked, Suspended ). */
    ListItem_t xEventListItem; /*< Used to reference a task from an event list. */
    UBaseType_t uxPriority; /*< The priority of the task.  0 is the lowest priority. */
    StackType_t * pxStack; /*< Points to the start of the stack. */
    volatile TaskRunning_t xTaskRunState; /*< Used to identify the core the task is running on, if any. */
    BaseType_t xIsIdle; /*< Used to identify the idle tasks. */
    char pcTaskName[ 16 ]; /*< Descriptive name given to the task when created.  Facilitates debugging only. */ /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
// # 294 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        UBaseType_t uxCriticalNesting; /*< Holds the critical section nesting depth for ports that do not maintain their own count in the port layer. */



        UBaseType_t uxTCBNumber; /*< Stores a number that increments each time a TCB is created.  It allows debuggers to determine when a task has been deleted and then recreated. */
        UBaseType_t uxTaskNumber; /*< Stores a number specifically for use by third party trace code. */



        UBaseType_t uxBasePriority; /*< The priority last assigned to the task - used by the priority inheritance mechanism. */
        UBaseType_t uxMutexesHeld;







        void * pvThreadLocalStoragePointers[ 5 ];
// # 334 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        volatile uint32_t ulNotifiedValue[ 1 ];
        volatile uint8_t ucNotifyState[ 1 ];


    /* See the comments in FreeRTOS.h with the definition of
     * tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE. */





        uint8_t ucDelayAborted;





} tskTCB;

/* The old tskTCB name is maintained above then typedefed to the new TCB_t name
 * below to enable the use of older kernel aware debuggers. */
typedef tskTCB TCB_t;

/*lint -save -e956 A manual analysis and inspection has been used to determine
 * which static variables must be declared volatile. */
                TCB_t * volatile pxCurrentTCBs[ 1 ] = { 0 };


/* Lists for ready and blocked tasks. --------------------
 * xDelayedTaskList1 and xDelayedTaskList2 could be moved to function scope but
 * doing so breaks some kernel aware debuggers and debuggers that rely on removing
 * the static qualifier. */
                static List_t pxReadyTasksLists[ 32 ]; /*< Prioritised ready tasks. */
                static List_t xDelayedTaskList1; /*< Delayed tasks. */
                static List_t xDelayedTaskList2; /*< Delayed tasks (two lists are used - one for delays that have overflowed the current tick count. */
                static List_t * volatile pxDelayedTaskList; /*< Points to the delayed task list currently being used. */
                static List_t * volatile pxOverflowDelayedTaskList; /*< Points to the delayed task list currently being used to hold tasks that have overflowed the current tick count. */
                static List_t xPendingReadyList; /*< Tasks that have been readied while the scheduler was suspended.  They will be moved to the ready list when the scheduler is resumed. */



                    static List_t xTasksWaitingTermination; /*< Tasks that have been deleted - but their memory not yet freed. */
                    static volatile UBaseType_t uxDeletedTasksWaitingCleanUp = ( UBaseType_t ) 0U;





                    static List_t xSuspendedTaskList; /*< Tasks that are currently suspended. */



/* Global POSIX errno. Its value is changed upon context switching to match
 * the errno of the currently running task. */




/* Other file private variables. --------------------------------*/
                static volatile UBaseType_t uxCurrentNumberOfTasks = ( UBaseType_t ) 0U;
                static volatile TickType_t xTickCount = ( TickType_t ) 0;
                static volatile UBaseType_t uxTopReadyPriority = ( ( UBaseType_t ) 0U );
                static volatile BaseType_t xSchedulerRunning = ( ( char ) 0 );
                static volatile TickType_t xPendedTicks = ( TickType_t ) 0U;
                static volatile BaseType_t xYieldPendings[ 1 ] = { ( ( char ) 0 ) };
                static volatile BaseType_t xNumOfOverflows = ( BaseType_t ) 0;
                static UBaseType_t uxTaskNumber = ( UBaseType_t ) 0U;
                static volatile TickType_t xNextTaskUnblockTime = ( TickType_t ) 0U; /* Initialised to portMAX_DELAY before the scheduler starts. */
                static TaskHandle_t xIdleTaskHandle[ 1 ] = { 0 }; /*< Holds the handle of the idle task.  The idle task is created automatically when the scheduler is started. */



/* Improve support for OpenOCD. The kernel tracks Ready tasks via priority lists.
 * For tracking the state of remote threads, OpenOCD uses uxTopUsedPriority
 * to determine the number of priority lists to read back from the remote target. */
const volatile UBaseType_t uxTopUsedPriority = 32 - 1U;

/* Context switches are held pending while the scheduler is suspended.  Also,
 * interrupts must not manipulate the xStateListItem of a TCB, or any of the
 * lists the xStateListItem can be referenced from, if the scheduler is suspended.
 * If an interrupt needs to unblock a task while the scheduler is suspended then it
 * moves the task's event list item into the xPendingReadyList, ready for the
 * kernel to move the task from the pending ready list into the real ready list
 * when the scheduler is unsuspended.  The pending ready list itself can only be
 * accessed from a critical section.
 *
 * Updates to uxSchedulerSuspended must be protected by both the task and ISR locks and
 * must not be done by an ISR. Reads must be protected by either lock and may be done by
 * either an ISR or a task. */
                static volatile UBaseType_t uxSchedulerSuspended = ( UBaseType_t ) ( ( char ) 0 );
// # 434 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*lint -restore */

/*-----------------------------------------------------------*/

/* File private functions. --------------------------------*/

/*
 * Creates the idle tasks during scheduler start
 */
static BaseType_t prvCreateIdleTasks( void );

/*
 * Returns the yield pending count for the calling core.
 */
static BaseType_t prvGetCurrentYieldPending( void );

/*
 * Checks to see if another task moved the current task out of the ready
 * list while it was waiting to enter a critical section and yields if so.
 */
static void prvCheckForRunStateChange( void );

/*
 * Yields the given core.
 */
static void prvYieldCore( BaseType_t xCoreID );

/*
 * Yields a core, or cores if multiple priorities are not allowed to run
 * simultaneously, to allow the task pxTCB to run.
 */
static void prvYieldForTask( TCB_t * pxTCB,
                             const BaseType_t xPreemptEqualPriority );

/*
 * Selects the highest priority available task
 */
static BaseType_t prvSelectHighestPriorityTask( const BaseType_t xCoreID );

/**
 * Utility task that simply returns pdTRUE if the task referenced by xTask is
 * currently in the Suspended state, or pdFALSE if the task referenced by xTask
 * is in any other state.
 */


    static BaseType_t prvTaskIsTaskSuspended( const TaskHandle_t xTask ) ;



/*
 * Utility to ready all the lists used by the scheduler.  This is called
 * automatically upon the creation of the first task.
 */
static void prvInitialiseTaskLists( void ) ;

/*
 * The idle task, which as all tasks is implemented as a never ending loop.
 * The idle task is automatically created and added to the ready lists upon
 * creation of the first user task.
 *
 */
static void prvIdleTask( void * pvParameters ) ;




/*
 * Utility to free all memory allocated by the scheduler to hold a TCB,
 * including the stack pointed to by the TCB.
 *
 * This does not free memory allocated by the task itself (i.e. memory
 * allocated by calls to pvPortMalloc from within the tasks application code).
 */


    static void prvDeleteTCB( TCB_t * pxTCB ) ;



/*
 * Used only by the idle task.  This checks to see if anything has been placed
 * in the list of tasks waiting to be deleted.  If so the task is cleaned up
 * and its TCB deleted.
 */
static void prvCheckTasksWaitingTermination( void ) ;

/*
 * The currently executing task is entering the Blocked state.  Add the task to
 * either the current or the overflow delayed task list.
 */
static void prvAddCurrentTaskToDelayedList( TickType_t xTicksToWait,
                                            const BaseType_t xCanBlockIndefinitely ) ;

/*
 * Fills an TaskStatus_t structure with information on each task that is
 * referenced from the pxList list (which may be a ready list, a delayed list,
 * a suspended list, etc.).
 *
 * THIS FUNCTION IS INTENDED FOR DEBUGGING ONLY, AND SHOULD NOT BE CALLED FROM
 * NORMAL APPLICATION CODE.
 */


    static UBaseType_t prvListTasksWithinSingleList( TaskStatus_t * pxTaskStatusArray,
                                                     List_t * pxList,
                                                     eTaskState eState ) ;



/*
 * Searches pxList for a task with name pcNameToQuery - returning a handle to
 * the task if it is found, or NULL if the task is not found.
 */


    static TCB_t * prvSearchForNameWithinSingleList( List_t * pxList,
                                                     const char pcNameToQuery[] ) ;



/*
 * When a task is created, the stack of the task is filled with a known value.
 * This function determines the 'high water mark' of the task stack by
 * determining how much of the stack remains at the original preset value.
 */


    static uint32_t prvTaskCheckFreeStackSpace( const uint8_t * pucStackByte ) ;



/*
 * Return the amount of time, in ticks, that will pass before the kernel will
 * next move a task from the Blocked state to the Running state.
 *
 * This conditional compilation should use inequality to 0, not equality to 1.
 * This is to ensure portSUPPRESS_TICKS_AND_SLEEP() can be called when user
 * defined low power mode implementations require configUSE_TICKLESS_IDLE to be
 * set to a value other than 1.
 */






/*
 * Set xNextTaskUnblockTime to the time at which the next Blocked state task
 * will exit the Blocked state.
 */
static void prvResetNextTaskUnblockTime( void ) ;
// # 598 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*
 * Called after a Task_t structure has been allocated either statically or
 * dynamically to fill in the structure's members.
 */
static void prvInitialiseNewTask( TaskFunction_t pxTaskCode,
                                  const char * pcName, /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
                                  const uint32_t ulStackDepth,
                                  void * pvParameters,
                                  UBaseType_t uxPriority,
                                  TaskHandle_t * pxCreatedTask,
                                  TCB_t * pxNewTCB,
                                  const MemoryRegion_t * xRegions ) ;

/*
 * Called after a new task has been created and initialised to place the task
 * under the control of the scheduler.
 */
static void prvAddNewTaskToReadyList( TCB_t * pxNewTCB ) ;

/*
 * freertos_tasks_c_additions_init() should only be called if the user definable
 * macro FREERTOS_TASKS_C_ADDITIONS_INIT() is defined, as that is the only macro
 * called by the function.
 */






/*-----------------------------------------------------------*/
// # 648 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 731 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/

static void prvYieldCore( BaseType_t xCoreID )
{
    /* This must be called from a critical section and
     * xCoreID must be valid. */

    if( assert_fct(false, "portCHECK_IF_IN_ISR") && ( xCoreID == 0 ) )
    {
        xYieldPendings[ xCoreID ] = ( ( char ) 1 );
    }
    else if( pxCurrentTCBs[ xCoreID ]->xTaskRunState != ( TaskRunning_t ) ( -2 ) )
    {
        if( xCoreID == 0 )
        {
            xYieldPendings[ xCoreID ] = ( ( char ) 1 );
        }







    }
}

/*-----------------------------------------------------------*/

static void prvYieldForTask( TCB_t * pxTCB,
                             const BaseType_t xPreemptEqualPriority )
{
    BaseType_t xLowestPriority;
    BaseType_t xTaskPriority;
    BaseType_t xLowestPriorityCore = -1;
    BaseType_t xYieldCount = 0;
    BaseType_t x;
    TaskRunning_t xTaskRunState;

    /* THIS FUNCTION MUST BE CALLED FROM A CRITICAL SECTION */

    assert(xTaskGetCurrentTaskHandle()->uxCriticalNesting > 0U);
// # 785 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    xLowestPriority = ( BaseType_t ) pxTCB->uxPriority;

    if( xPreemptEqualPriority == ( ( char ) 0 ) )
    {
        /* xLowestPriority will be decremented to -1 if the priority of pxTCB
         * is 0. This is ok as we will give system idle tasks a priority of -1 below. */
        --xLowestPriority;
    }

    for( x = ( BaseType_t ) 0; x < ( BaseType_t ) 1; x++ )
    {
        /* System idle tasks are being assigned a priority of tskIDLE_PRIORITY - 1 here */
        xTaskPriority = ( BaseType_t ) pxCurrentTCBs[ x ]->uxPriority - pxCurrentTCBs[ x ]->xIsIdle;
        xTaskRunState = pxCurrentTCBs[ x ]->xTaskRunState;

        if( ( ( ( 0 <= xTaskRunState ) && ( xTaskRunState < 1 ) ) != ( ( char ) 0 ) ) && ( xYieldPendings[ x ] == ( ( char ) 0 ) ) )
        {
            if( xTaskPriority <= xLowestPriority )
            {





                {



                    {
                        xLowestPriority = xTaskPriority;
                        xLowestPriorityCore = x;
                    }
                }
            }
            else
            {
                                        ;
            }
// # 839 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        }
        else
        {
                                    ;
        }
    }

    if( ( xYieldCount == 0 ) && ( ( BaseType_t ) ( ( 0 <= xLowestPriorityCore ) && ( xLowestPriorityCore < 1 ) ) ) )
    {
        prvYieldCore( xLowestPriorityCore );
        xYieldCount++;
    }
// # 859 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
}
/*-----------------------------------------------------------*/



    static BaseType_t prvSelectHighestPriorityTask( const BaseType_t xCoreID )
    {
        UBaseType_t uxCurrentPriority = uxTopReadyPriority;
        BaseType_t xTaskScheduled = ( ( char ) 0 );
        BaseType_t xDecrementTopPriority = ( ( char ) 1 );
// # 877 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        while( xTaskScheduled == ( ( char ) 0 ) )
        {
// # 891 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            if( ( ( ( &( pxReadyTasksLists[ uxCurrentPriority ] ) )->uxNumberOfItems == ( UBaseType_t ) 0 ) ? ( ( char ) 1 ) : ( ( char ) 0 ) ) == ( ( char ) 0 ) )
            {

                    /* Reason for rewrite: 
                     * VeriFast does not support const pointers.
                     */
                    List_t * pxReadyList = &( pxReadyTasksLists[ uxCurrentPriority ] );




                ListItem_t * pxLastTaskItem = pxReadyList->pxIndex->pxPrevious;
                ListItem_t * pxTaskItem = pxLastTaskItem;

                if( ( void * ) pxLastTaskItem == ( void * ) &( pxReadyList->xListEnd ) )
                {
                    pxLastTaskItem = pxLastTaskItem->pxPrevious;
                }

                /* The ready task list for uxCurrentPriority is not empty, so uxTopReadyPriority
                 * must not be decremented any further */
                xDecrementTopPriority = ( ( char ) 0 );

                do
                {
                    TCB_t * pxTCB;

                    pxTaskItem = pxTaskItem->pxNext;

                    if( ( void * ) pxTaskItem == ( void * ) &( pxReadyList->xListEnd ) )
                    {
                        pxTaskItem = pxTaskItem->pxNext;
                    }

                    pxTCB = pxTaskItem->pvOwner;

                    /*debug_printf("Attempting to schedule %s on core %d\n", pxTCB->pcTaskName, portGET_CORE_ID() ); */
// # 944 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
                    if( pxTCB->xTaskRunState == ( TaskRunning_t ) ( -1 ) )
                    {





                        {
                            /* If the task is not being executed by any core swap it in */
                            pxCurrentTCBs[ xCoreID ]->xTaskRunState = ( TaskRunning_t ) ( -1 );



                            pxTCB->xTaskRunState = ( TaskRunning_t ) xCoreID;
                            pxCurrentTCBs[ xCoreID ] = pxTCB;
                            xTaskScheduled = ( ( char ) 1 );
                        }
                    }
                    else if( pxTCB == pxCurrentTCBs[ xCoreID ] )
                    {
                        assert(( pxTCB->xTaskRunState == xCoreID ) || ( pxTCB->xTaskRunState == ( TaskRunning_t ) ( -2 ) ));





                        {
                            /* The task is already running on this core, mark it as scheduled */
                            pxTCB->xTaskRunState = ( TaskRunning_t ) xCoreID;
                            xTaskScheduled = ( ( char ) 1 );
                        }
                    }

                    if( xTaskScheduled != ( ( char ) 0 ) )
                    {
                        /* Once a task has been selected to run on this core,
                         * move it to the end of the ready task list. */
                        uxListRemove( pxTaskItem );
                        vListInsertEnd( pxReadyList, pxTaskItem );
                        break;
                    }
                } while( pxTaskItem != pxLastTaskItem );
            }
            else
            {
                if( xDecrementTopPriority != ( ( char ) 0 ) )
                {
                    uxTopReadyPriority--;





                }
            }

            /* This function can get called by vTaskSuspend() before the scheduler is started.
             * In that case, since the idle tasks have not yet been created it is possible that we
             * won't find a new task to schedule. Return pdFALSE in this case. */
            if( ( xSchedulerRunning == ( ( char ) 0 ) ) && ( uxCurrentPriority == ( ( UBaseType_t ) 0U ) ) && ( xTaskScheduled == ( ( char ) 0 ) ) )
            {
                return ( ( char ) 0 );
            }

            assert(( uxCurrentPriority > ( ( UBaseType_t ) 0U ) ) || ( xTaskScheduled == ( ( char ) 1 ) ));
            uxCurrentPriority--;
        }

        assert(( ( 0 <= pxCurrentTCBs[ xCoreID ]->xTaskRunState ) && ( pxCurrentTCBs[ xCoreID ]->xTaskRunState < 1 ) ));
// # 1088 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        return ( ( char ) 1 );
    }
// # 1104 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 1182 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 1245 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 1311 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/



    BaseType_t xTaskCreate( TaskFunction_t pxTaskCode,
                            const char * pcName, /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
                            const uint32_t usStackDepth,
                            void * pvParameters,
                            UBaseType_t uxPriority,
                            TaskHandle_t * pxCreatedTask )
    /*@ requires usStackDepth * sizeof( StackType_t ) < UINTPTR_MAX &*&
                 usStackDepth > 18 &*&
                 // We assume that macro `configMAX_TASK_NAME_LEN` evaluates to 16.
                 chars(pcName, 16, _) &*&
                 *pxCreatedTask |-> _;
     @*/
    //@ ensures true;
// # 1341 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    {
        TCB_t * pxNewTCB;
        BaseType_t xReturn;

        /* If the stack grows down then allocate the stack then the TCB so the stack
         * does not grow into the TCB.  Likewise if the stack grows up then allocate
         * the TCB then the stack. */
// # 1371 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            {
                StackType_t * pxStack;

                /* Allocate space for the stack used by the task being created. */
                pxStack = malloc( ( ( ( size_t ) usStackDepth ) * sizeof( StackType_t ) ) ); /*lint !e9079 All values returned by pvPortMalloc() have at least the alignment required by the MCU's stack and this allocation is the stack. */

                if( pxStack != 0 )
                {
                    /* Allocate space for the TCB. */
                    pxNewTCB = ( TCB_t * ) malloc( sizeof( TCB_t ) ); /*lint !e9087 !e9079 All values returned by pvPortMalloc() have at least the alignment required by the MCU's stack, and the first member of TCB_t is always a pointer to the task's stack. */

                    if( pxNewTCB != 0 )
                    {
                        /* Store the stack location in the TCB. */
                        pxNewTCB->pxStack = pxStack;
                        //@ close xLIST_ITEM(&pxNewTCB->xStateListItem, _, _, _, _);
                        //@ close xLIST_ITEM(&pxNewTCB->xEventListItem, _, _, _, _);
                        //@ chars__limits((char*) pxNewTCB->pxStack);
                        //@ assert( pxNewTCB->pxStack + (size_t) usStackDepth <= (StackType_t*) UINTPTR_MAX );
                        //@ close uninit_TCB_p(pxNewTCB, ((size_t) usStackDepth) * sizeof(StackType_t)); 
                    }
                    else
                    {
                        /* The stack cannot be used as the TCB was not created.  Free
                         * it again. */
                        free( (void*) pxStack);
                    }
                }
                else
                {
                    pxNewTCB = 0;
                }
            }


        if( pxNewTCB != 0 )
        {
// # 1416 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            prvInitialiseNewTask( pxTaskCode, pcName, ( uint32_t ) usStackDepth, pvParameters, uxPriority, pxCreatedTask, pxNewTCB, 0 );
// # 1425 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            prvAddNewTaskToReadyList( pxNewTCB );
            xReturn = ( ( ( char ) 1 ) );
        }
        else
        {
            xReturn = ( -1 );
        }

        //@ assume(false);
        // TODO: Remove!
        // Allows us to focus on verifying called functions.
        return xReturn;
    }


/*-----------------------------------------------------------*/

static void prvInitialiseNewTask( TaskFunction_t pxTaskCode,
                                  const char * pcName, /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
                                  const uint32_t ulStackDepth,
                                  void * pvParameters,
                                  UBaseType_t uxPriority,
                                  TaskHandle_t * pxCreatedTask,
                                  TCB_t * pxNewTCB,
                                  const MemoryRegion_t * xRegions )
/*@ requires uninit_TCB_p(pxNewTCB, ?stackSize) &*&
             stackSize == ulStackDepth * sizeof(StackType_t) &*&
             stackSize <= UINTPTR_MAX &*&
             ulStackDepth > 18 &*&
             // We assume that macro `configMAX_TASK_NAME_LEN` evaluates to 16.
             chars(pcName, 16, _) &*&
             *pxCreatedTask |-> _;
 @*/
/*@ ensures TCB_p(pxNewTCB, ?freeBytes) &*&
            chars(pcName, 16, _) &*&
            *pxCreatedTask |-> _; 
 @*/
{
    StackType_t * pxTopOfStack;
    UBaseType_t x;
// # 1482 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    //@ open uninit_TCB_p(_,_);

    /* Avoid dependency on memset() if it is not required. */

        {
            /* Fill the stack with a known value to assist debugging. */

                /* Reason for rewrite:
                 * - VeriFast does not support casts involving side-effectful
                 *   expressions.
                 * - VeriFast report type mismatch because 
                 *   `( int ) tskSTACK_FILL_BYTE` is passed for a char argument.
                 * 
                 * Note: The only affect of void casts is to surpress compiler
                 *       warnings.
                 * 
                 * TODO: Is the type mismatch a real error?
                 */
                memset( pxNewTCB->pxStack, ( char ) ( 0xa5U ), ( size_t ) ulStackDepth * sizeof( StackType_t ) );



        }


    /* Calculate the top of stack address.  This depends on whether the stack
     * grows from high memory to low (as per the 80x86) or vice versa.
     * portSTACK_GROWTH is used to make the result positive or negative as required
     * by the port. */

        {
            pxTopOfStack = &( pxNewTCB->pxStack[ ulStackDepth - ( uint32_t ) 1 ] );
            //@ StackType_t* gOldTop = pxTopOfStack;
            //@ char* gcStack = (char*) pxNewTCB->pxStack;

            /* Set the following flag to skip and expensive part of this proof:
             * `VERIFAST_SKIP_BITVECTOR_PROOF__STACK_ALIGNMENT`
             *
             * For VeriFast bit vector proofs are very computation intensive.
             * Hence, reasoning about the stack alignment below takes relatively 
             * long.
             */
// # 1540 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
                /* Axiomatise that no over- or underflow occurs. 
                * We further assume that `portPOINTER_SIZE_TYPE` evaluates to 
                * `uint32_t`.
                */
                //@ ptr_range<void>(pxTopOfStack);
                /*@ assume( ( StackType_t * ) ( ( ( uint32_t ) pxTopOfStack ) 
                                & ( ~( ( uint32_t ) ( 0x0007 ) ) ) ) 
                            > 0 );
                @*/
                /*@ assume( ( StackType_t * ) ( ( ( uint32_t ) pxTopOfStack ) 
                                & ( ~( ( uint32_t ) ( 0x0007 ) ) ) ) 
                            <= (StackType_t*) UINTPTR_MAX );
                @*/


            pxTopOfStack = ( StackType_t * ) ( ( ( uint32_t ) pxTopOfStack ) & ( ~( ( uint32_t ) ( 0x0007 ) ) ) ); /*lint !e923 !e9033 !e9078 MISRA exception.  Avoiding casts between pointers and integers is not practical.  Size differences accounted for using portPOINTER_SIZE_TYPE type.  Checked by assert(). */
// # 1568 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
                /* Axiomatize that alignmet check succeeds. 
                 * We further assume that `portPOINTER_SIZE_TYPE` evaluates to 
                 * `uint32_t`*/
                //@ ptr_range<void>(pxTopOfStack);
                /*@ assume( ( ( uint32_t ) pxTopOfStack & ( uint32_t ) ( 0x0007 ) ) == 0UL );
                 @*/


            /* Check the alignment of the calculated top of stack is correct. */
            assert(( ( ( uint32_t ) pxTopOfStack & ( uint32_t ) ( 0x0007 ) ) == 0UL ));
// # 1590 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
                /* Axiomatize that bit vector operations did not change stack
                 * pointer.
                 */
                /* TODO: Can we simplify the axiomatizations here and above
                 *       by assuming that the top pointer was already aligned?
                 */
                //@ assume( pxTopOfStack == gOldTop );
                //@ int gUnalignedBytes = 0;


            //@ assert( chars(gcStack, ?gFreeBytes, _) );
            //@ char* gUnalignedPtr = (char*) pxNewTCB->pxStack +  gFreeBytes;
            //@ close unalignedRestOfStack_p(gUnalignedPtr, gUnalignedBytes);
            //@ close stack_p_2(pxNewTCB->pxStack, ulStackDepth, pxTopOfStack, gFreeBytes, 0, gUnalignedBytes);        
// # 1613 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        }
// # 1627 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    /* Store the task name in the TCB. */
    if( pcName != 0 )
    {
        for( x = ( UBaseType_t ) 0; x < ( UBaseType_t ) 16; x++ )
        /*@ invariant chars_(pxNewTCB->pcTaskName, 16, _) &*&
                      chars(pcName, 16, _);
         @*/
        {
            pxNewTCB->pcTaskName[ x ] = pcName[ x ];

            /* Don't copy all configMAX_TASK_NAME_LEN if the string is shorter than
             * configMAX_TASK_NAME_LEN characters just in case the memory after the
             * string is not accessible (extremely unlikely). */
            if( pcName[ x ] == ( char ) 0x00 )
            {
                break;
            }
            else
            {
                                        ;
            }
        }

        /* Ensure the name string is terminated in the case that the string length
         * was greater or equal to configMAX_TASK_NAME_LEN. */
        pxNewTCB->pcTaskName[ 16 - 1 ] = '\0';
    }
    else
    {
        /* The task has not been given a name, so just ensure there is a NULL
         * terminator when it is read out. */
        pxNewTCB->pcTaskName[ 0 ] = 0x00;
    }

    /* This is used as an array index so must ensure it's not too large.  First
     * remove the privilege bit if one is present. */
    if( uxPriority >= ( UBaseType_t ) 32 )
    {
        uxPriority = ( UBaseType_t ) 32 - ( UBaseType_t ) 1U;
    }
    else
    {
                                ;
    }

    pxNewTCB->uxPriority = uxPriority;

        {
            pxNewTCB->uxBasePriority = uxPriority;
            pxNewTCB->uxMutexesHeld = 0;
        }


    // TODO: Add contract
    // TODO: Why does VeriFast not complain?
    vListInitialiseItem( &( pxNewTCB->xStateListItem ) );
    //@ assert(false);
    vListInitialiseItem( &( pxNewTCB->xEventListItem ) );


    /* Set the pxNewTCB as a link back from the ListItem_t.  This is so we can get
     * back to  the containing TCB from a generic item in a list. */
    ( ( &( pxNewTCB->xStateListItem ) )->pvOwner = ( void * ) ( pxNewTCB ) );

    /* Event lists are always in priority order. */
    ( ( &( pxNewTCB->xEventListItem ) )->xItemValue = ( ( TickType_t ) 32 - ( TickType_t ) uxPriority ) ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */
    ( ( &( pxNewTCB->xEventListItem ) )->pvOwner = ( void * ) ( pxNewTCB ) );

    // Closing predicates early simplifies the symbolic heap and proof debugging.
    //@ close xLIST_ITEM(&pxNewTCB->xStateListItem, _, _, _, _);
    //@ close xLIST_ITEM(&pxNewTCB->xEventListItem, _, _, _, _);


        {
            pxNewTCB->uxCriticalNesting = ( UBaseType_t ) 0U;
        }
// # 1722 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        {
            /* Avoid compiler warning about unreferenced parameter. */
            ( void ) xRegions;
        }



        {
            //@ pointers__to_chars_(pxNewTCB->pvThreadLocalStoragePointers);
            //@ assert(chars_((char*) pxNewTCB->pvThreadLocalStoragePointers, _, _));
            //@ assert(chars_(_, sizeof( pxNewTCB->pvThreadLocalStoragePointers ), _));
            memset( ( void * ) &( pxNewTCB->pvThreadLocalStoragePointers[ 0 ] ), 0x00, sizeof( pxNewTCB->pvThreadLocalStoragePointers ) );
        }



        {
            ///@ assert( integers__(pxNewTCB->ulNotifiedValue, _, _, 1, _) );
            ///@ integers___to_integers_(pxNewTCB->ulNotifiedValue);
         ///@ integers__to_chars(pxNewTCB->ulNotifiedValue);
            //@integers___to_integers_(pxNewTCB->ulNotifiedValue);
            //@ integers__to_chars(pxNewTCB->ulNotifiedValue);
            memset( ( void * ) &( pxNewTCB->ulNotifiedValue[ 0 ] ), 0x00, sizeof( pxNewTCB->ulNotifiedValue ) );
            //@ uchars__to_chars_(pxNewTCB->ucNotifyState);
            memset( ( void * ) &( pxNewTCB->ucNotifyState[ 0 ] ), 0x00, sizeof( pxNewTCB->ucNotifyState ) );
            //@ chars_to_uchars(pxNewTCB->ucNotifyState);
        }
// # 1761 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        {

                /* Reason for rewrite: Assignment not type safe. */
                pxNewTCB->ucDelayAborted = ( ( unsigned char ) ( ( char ) 0 ) );



        }
// # 1784 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    /* Initialize the TCB stack to look as if the task was already running,
     * but had been interrupted by the scheduler.  The return address is set
     * to the start of the task function. Once the stack has been initialised
     * the top of stack variable is updated. */
// # 1812 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        {
            /* If the port has capability to detect stack overflow,
             * pass the stack end address to the stack initialization
             * function as well. */
// # 1829 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
                {
                    pxNewTCB->pxTopOfStack = pxPortInitialiseStack( pxTopOfStack, pxTaskCode, pvParameters );
                }

        }


    /* Initialize to not running */
    pxNewTCB->xTaskRunState = ( TaskRunning_t ) ( -1 );

    /* Is this an idle task? */
    if( pxTaskCode == prvIdleTask )
    {
        pxNewTCB->xIsIdle = ( ( char ) 1 );
    }







    else
    {
        pxNewTCB->xIsIdle = ( ( char ) 0 );
    }

    if( pxCreatedTask != 0 )
    {
        /* Pass the handle out in an anonymous way.  The handle can be used to
         * change the created task's priority, delete the created task, etc.*/
        *pxCreatedTask = ( TaskHandle_t ) pxNewTCB;
    }
    else
    {
                                ;
    }

    //@ assert( stack_p_2(_, _, _, ?gFreeBytes, _, _) );
    //@ close TCB_p(pxNewTCB, gFreeBytes);
}
/*-----------------------------------------------------------*/

static void prvAddNewTaskToReadyList( TCB_t * pxNewTCB )
/*@ requires true; 
  @*/
/*@ ensures true; 
  @*/
{
    /* Ensure interrupts don't access the task lists while the lists are being
     * updated. */
    vTaskEnterCritical();
    {
        uxCurrentNumberOfTasks++;

        if( xSchedulerRunning == ( ( char ) 0 ) )
        {
            if( uxCurrentNumberOfTasks == ( UBaseType_t ) 1 )
            {
                /* This is the first task to be created so do the preliminary
                 * initialisation required.  We will not recover if this call
                 * fails, but we will report the failure. */
                prvInitialiseTaskLists();
            }
            else
            {
                                        ;
            }

            if( pxNewTCB->xIsIdle != ( ( char ) 0 ) )
            {
                BaseType_t xCoreID;

                /* Check if a core is free. */
                for( xCoreID = ( UBaseType_t ) 0; xCoreID < ( UBaseType_t ) 1; xCoreID++ )
                {
                    if( pxCurrentTCBs[ xCoreID ] == 0 )
                    {
                        pxNewTCB->xTaskRunState = xCoreID;
                        pxCurrentTCBs[ xCoreID ] = pxNewTCB;
                        break;
                    }
                }
            }
        }
        else
        {
                                    ;
        }

        uxTaskNumber++;


            {
                /* Add a counter into the TCB for tracing only. */
                pxNewTCB->uxTCBNumber = uxTaskNumber;
            }

                                    ;

        ; { if( ( ( pxNewTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxNewTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxNewTCB )->uxPriority ] ), &( ( pxNewTCB )->xStateListItem ) ); ;

        ( void ) pxNewTCB;

        if( xSchedulerRunning != ( ( char ) 0 ) )
        {
            /* If the created task is of a higher priority than another
             * currently running task and preemption is on then it should
             * run now. */

                prvYieldForTask( pxNewTCB, ( ( char ) 0 ) );

        }
        else
        {
                                    ;
        }
    }
    vTaskExitCritical();
}
/*-----------------------------------------------------------*/



    void vTaskDelete( TaskHandle_t xTaskToDelete )
    {
        TCB_t * pxTCB;
        TaskRunning_t xTaskRunningOnCore;

        vTaskEnterCritical();
        {
            /* If null is passed in here then it is the calling task that is
             * being deleted. */
            pxTCB = ( ( ( xTaskToDelete ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTaskToDelete ) );

            xTaskRunningOnCore = pxTCB->xTaskRunState;

            /* Remove task from the ready/delayed list. */
            if( uxListRemove( &( pxTCB->xStateListItem ) ) == ( UBaseType_t ) 0 )
            {
                                                             ;
            }
            else
            {
                                        ;
            }

            /* Is the task waiting on an event also? */
            if( ( ( &( pxTCB->xEventListItem ) )->pxContainer ) != 0 )
            {
                ( void ) uxListRemove( &( pxTCB->xEventListItem ) );
            }
            else
            {
                                        ;
            }

            /* Increment the uxTaskNumber also so kernel aware debuggers can
             * detect that the task lists need re-generating.  This is done before
             * portPRE_TASK_DELETE_HOOK() as in the Windows port that macro will
             * not return. */
            uxTaskNumber++;

            /* If the task is running (or yielding), we must add it to the
             * termination list so that an idle task can delete it when it is
             * no longer running. */
            if( xTaskRunningOnCore != ( TaskRunning_t ) ( -1 ) )
            {
                /* A running task is being deleted.  This cannot complete within the
                 * task itself, as a context switch to another task is required.
                 * Place the task in the termination list.  The idle task will
                 * check the termination list and free up any memory allocated by
                 * the scheduler for the TCB and stack of the deleted task. */
                vListInsertEnd( &xTasksWaitingTermination, &( pxTCB->xStateListItem ) );

                /* Increment the ucTasksDeleted variable so the idle task knows
                 * there is a task that has been deleted and that it should therefore
                 * check the xTasksWaitingTermination list. */
                ++uxDeletedTasksWaitingCleanUp;

                /* Call the delete hook before portPRE_TASK_DELETE_HOOK() as
                 * portPRE_TASK_DELETE_HOOK() does not return in the Win32 port. */
                                         ;

                /* The pre-delete hook is primarily for the Windows simulator,
                 * in which Windows specific clean up operations are performed,
                 * after which it is not possible to yield away from this task -
                 * hence xYieldPending is used to latch that a context switch is
                 * required. */
                                                                                          ;
            }
            else
            {
                --uxCurrentNumberOfTasks;
                                         ;
                prvDeleteTCB( pxTCB );

                /* Reset the next expected unblock time in case it referred to
                 * the task that has just been deleted. */
                prvResetNextTaskUnblockTime();
            }

            /* Force a reschedule if the task that has just been deleted was running. */
            if( ( xSchedulerRunning != ( ( char ) 0 ) ) && ( ( ( 0 <= xTaskRunningOnCore ) && ( xTaskRunningOnCore < 1 ) ) ) )
            {
                BaseType_t xCoreID;

                xCoreID = 0;

                if( xTaskRunningOnCore == xCoreID )
                {
                    assert(uxSchedulerSuspended == 0);
                    vTaskYieldWithinAPI();
                }
                else
                {
                    prvYieldCore( xTaskRunningOnCore );
                }
            }
        }
        vTaskExitCritical();
    }


/*-----------------------------------------------------------*/



    BaseType_t xTaskDelayUntil( TickType_t * pxPreviousWakeTime,
                                const TickType_t xTimeIncrement )
    {
        TickType_t xTimeToWake;
        BaseType_t xAlreadyYielded, xShouldDelay = ( ( char ) 0 );

        assert(pxPreviousWakeTime);
        assert(( xTimeIncrement > 0U ));

        vTaskSuspendAll();
        {
            assert(uxSchedulerSuspended == 1);

            /* Minor optimisation.  The tick count cannot change in this
             * block. */
            const TickType_t xConstTickCount = xTickCount;

            /* Generate the tick time at which the task wants to wake. */
            xTimeToWake = *pxPreviousWakeTime + xTimeIncrement;

            if( xConstTickCount < *pxPreviousWakeTime )
            {
                /* The tick count has overflowed since this function was
                 * lasted called.  In this case the only time we should ever
                 * actually delay is if the wake time has also  overflowed,
                 * and the wake time is greater than the tick time.  When this
                 * is the case it is as if neither time had overflowed. */
                if( ( xTimeToWake < *pxPreviousWakeTime ) && ( xTimeToWake > xConstTickCount ) )
                {
                    xShouldDelay = ( ( char ) 1 );
                }
                else
                {
                                            ;
                }
            }
            else
            {
                /* The tick time has not overflowed.  In this case we will
                 * delay if either the wake time has overflowed, and/or the
                 * tick time is less than the wake time. */
                if( ( xTimeToWake < *pxPreviousWakeTime ) || ( xTimeToWake > xConstTickCount ) )
                {
                    xShouldDelay = ( ( char ) 1 );
                }
                else
                {
                                            ;
                }
            }

            /* Update the wake time ready for the next call. */
            *pxPreviousWakeTime = xTimeToWake;

            if( xShouldDelay != ( ( char ) 0 ) )
            {
                                                    ;

                /* prvAddCurrentTaskToDelayedList() needs the block time, not
                 * the time to wake, so subtract the current tick count. */
                prvAddCurrentTaskToDelayedList( xTimeToWake - xConstTickCount, ( ( char ) 0 ) );
            }
            else
            {
                                        ;
            }
        }
        xAlreadyYielded = xTaskResumeAll();

        /* Force a reschedule if xTaskResumeAll has not already done so, we may
         * have put ourselves to sleep. */
        if( xAlreadyYielded == ( ( char ) 0 ) )
        {
            vTaskYieldWithinAPI();
        }
        else
        {
                                    ;
        }

        return xShouldDelay;
    }


/*-----------------------------------------------------------*/



    void vTaskDelay( const TickType_t xTicksToDelay )
    {
        BaseType_t xAlreadyYielded = ( ( char ) 0 );

        /* A delay time of zero just forces a reschedule. */
        if( xTicksToDelay > ( TickType_t ) 0U )
        {
            vTaskSuspendAll();
            {
                assert(uxSchedulerSuspended == 1);
                                 ;

                /* A task that is removed from the event list while the
                 * scheduler is suspended will not get placed in the ready
                 * list or removed from the blocked list until the scheduler
                 * is resumed.
                 *
                 * This task cannot be in an event list as it is the currently
                 * executing task. */
                prvAddCurrentTaskToDelayedList( xTicksToDelay, ( ( char ) 0 ) );
            }
            xAlreadyYielded = xTaskResumeAll();
        }
        else
        {
                                    ;
        }

        /* Force a reschedule if xTaskResumeAll has not already done so, we may
         * have put ourselves to sleep. */
        if( xAlreadyYielded == ( ( char ) 0 ) )
        {
            vTaskYieldWithinAPI();
        }
        else
        {
                                    ;
        }
    }


/*-----------------------------------------------------------*/



    eTaskState eTaskGetState( TaskHandle_t xTask )
    {
        eTaskState eReturn;

            /* Reason for rewrite:
             * VeriFast does not support the following:
             * - const pointers
             * - multiple pointer declarations to user-defined types in single
             *   statement (i.e., `A p1, p2;` is ok, `A *p1, *p2;` fails)
             */
            List_t * pxStateList;
            List_t * pxDelayedList;
            List_t * pxOverflowedDelayedList;



        const TCB_t * pxTCB = xTask;

        assert(pxTCB);

        vTaskEnterCritical();
        {
            pxStateList = ( ( &( pxTCB->xStateListItem ) )->pxContainer );
            pxDelayedList = pxDelayedTaskList;
            pxOverflowedDelayedList = pxOverflowDelayedTaskList;
        }
        vTaskExitCritical();

        if( ( pxStateList == pxDelayedList ) || ( pxStateList == pxOverflowedDelayedList ) )
        {
            /* The task being queried is referenced from one of the Blocked
             * lists. */
            eReturn = eBlocked;
        }


            else if( pxStateList == &xSuspendedTaskList )
            {
                /* The task being queried is referenced from the suspended
                 * list.  Is it genuinely suspended or is it blocked
                 * indefinitely? */
                if( ( ( &( pxTCB->xEventListItem ) )->pxContainer ) == 0 )
                {

                        {
                            BaseType_t x;

                            /* The task does not appear on the event list item of
                             * and of the RTOS objects, but could still be in the
                             * blocked state if it is waiting on its notification
                             * rather than waiting on an object.  If not, is
                             * suspended. */
                            eReturn = eSuspended;

                            for( x = 0; x < 1; x++ )
                            {
                                if( pxTCB->ucNotifyState[ x ] == ( ( uint8_t ) 1 ) )
                                {
                                    eReturn = eBlocked;
                                    break;
                                }
                            }
                        }





                }
                else
                {
                    eReturn = eBlocked;
                }
            }



            else if( ( pxStateList == &xTasksWaitingTermination ) || ( pxStateList == 0 ) )
            {
                /* The task being queried is referenced from the deleted
                 * tasks list, or it is not referenced from any lists at
                 * all. */
                eReturn = eDeleted;
            }


        else /*lint !e525 Negative indentation is intended to make use of pre-processor clearer. */
        {
            /* If the task is not in any other state, it must be in the
             * Ready (including pending ready) state. */
            if( ( ( 0 <= pxTCB->xTaskRunState ) && ( pxTCB->xTaskRunState < 1 ) ) )
            {
                /* Is it actively running on a core? */
                eReturn = eRunning;
            }
            else
            {
                eReturn = eReady;
            }
        }

        return eReturn;
    } /*lint !e818 xTask cannot be a pointer to const because it is a typedef. */


/*-----------------------------------------------------------*/



    UBaseType_t uxTaskPriorityGet( const TaskHandle_t xTask )
    {

            /* Reason for rewrite:
             * VeriFast does not support const pointers.
             */
            TCB_t * pxTCB;



        UBaseType_t uxReturn;

        vTaskEnterCritical();
        {
            /* If null is passed in here then it is the priority of the task
             * that called uxTaskPriorityGet() that is being queried. */
            pxTCB = ( ( ( xTask ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTask ) );
            uxReturn = pxTCB->uxPriority;
        }
        vTaskExitCritical();

        return uxReturn;
    }


/*-----------------------------------------------------------*/



    UBaseType_t uxTaskPriorityGetFromISR( const TaskHandle_t xTask )
    {

            /* Reason for rewrite:
            * VeriFast does not support const pointers.
            */
           TCB_t * pxTCB;



        UBaseType_t uxReturn, uxSavedInterruptState;

        /* RTOS ports that support interrupt nesting have the concept of a
         * maximum  system call (or maximum API call) interrupt priority.
         * Interrupts that are  above the maximum system call priority are keep
         * permanently enabled, even when the RTOS kernel is in a critical section,
         * but cannot make any calls to FreeRTOS API functions.  If configASSERT()
         * is defined in FreeRTOSConfig.h then
         * portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will result in an assertion
         * failure if a FreeRTOS API function is called from an interrupt that has
         * been assigned a priority above the configured maximum system call
         * priority.  Only FreeRTOS functions that end in FromISR can be called
         * from interrupts  that have been assigned a priority at or (logically)
         * below the maximum system call interrupt priority.  FreeRTOS maintains a
         * separate interrupt safe API to ensure interrupt entry is as fast and as
         * simple as possible.  More information (albeit Cortex-M specific) is
         * provided on the following link:
         * https://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html */
                                                  ;

        uxSavedInterruptState = assert_fct(false, "portSET_INTERRUPT_MASK_FROM_ISR");
        {
            /* If null is passed in here then it is the priority of the calling
             * task that is being queried. */
            pxTCB = ( ( ( xTask ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTask ) );
            uxReturn = pxTCB->uxPriority;
        }
        do { vTaskExitCritical(); assert_fct(false, "portRESTORE_INTERRUPTS"); } while (0);

        return uxReturn;
    }


/*-----------------------------------------------------------*/



    void vTaskPrioritySet( TaskHandle_t xTask,
                           UBaseType_t uxNewPriority )
    {
        TCB_t * pxTCB;
        UBaseType_t uxCurrentBasePriority, uxPriorityUsedOnEntry;
        BaseType_t xYieldRequired = ( ( char ) 0 );
        BaseType_t xYieldForTask = ( ( char ) 0 );
        BaseType_t xCoreID;

        assert(( uxNewPriority < 32 ));

        /* Ensure the new priority is valid. */
        if( uxNewPriority >= ( UBaseType_t ) 32 )
        {
            uxNewPriority = ( UBaseType_t ) 32 - ( UBaseType_t ) 1U;
        }
        else
        {
                                    ;
        }

        vTaskEnterCritical();
        {
            /* If null is passed in here then it is the priority of the calling
             * task that is being changed. */
            pxTCB = ( ( ( xTask ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTask ) );

                                                          ;


                {
                    uxCurrentBasePriority = pxTCB->uxBasePriority;
                }






            if( uxCurrentBasePriority != uxNewPriority )
            {
                /* The priority change may have readied a task of higher
                 * priority than a running task. */
                if( uxNewPriority > uxCurrentBasePriority )
                {
                    /* The priority of a task is being raised so
                     * perform a yield for this task later. */
                    xYieldForTask = ( ( char ) 1 );
                }
                else if( ( ( 0 <= pxTCB->xTaskRunState ) && ( pxTCB->xTaskRunState < 1 ) ) )
                {
                    /* Setting the priority of a running task down means
                     * there may now be another task of higher priority that
                     * is ready to execute. */



                    {
                        xCoreID = ( BaseType_t ) pxTCB->xTaskRunState;
                        xYieldRequired = ( ( char ) 1 );
                    }
                }
                else
                {
                    /* Setting the priority of any other task down does not
                     * require a yield as the running task must be above the
                     * new priority of the task being modified. */
                }

                /* Remember the ready list the task might be referenced from
                 * before its uxPriority member is changed so the
                 * taskRESET_READY_PRIORITY() macro can function correctly. */
                uxPriorityUsedOnEntry = pxTCB->uxPriority;


                    {
                        /* Only change the priority being used if the task is not
                         * currently using an inherited priority. */
                        if( pxTCB->uxBasePriority == pxTCB->uxPriority )
                        {
                            pxTCB->uxPriority = uxNewPriority;
                        }
                        else
                        {
                                                    ;
                        }

                        /* The base priority gets set whatever. */
                        pxTCB->uxBasePriority = uxNewPriority;
                    }






                /* Only reset the event list item value if the value is not
                 * being used for anything else. */
                if( ( ( ( &( pxTCB->xEventListItem ) )->xItemValue ) & 0x80000000UL ) == 0UL )
                {
                    ( ( &( pxTCB->xEventListItem ) )->xItemValue = ( ( ( TickType_t ) 32 - ( TickType_t ) uxNewPriority ) ) ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */
                }
                else
                {
                                            ;
                }

                /* If the task is in the blocked or suspended list we need do
                 * nothing more than change its priority variable. However, if
                 * the task is in a ready list it needs to be removed and placed
                 * in the list appropriate to its new priority. */
                if( ( ( ( &( pxTCB->xStateListItem ) )->pxContainer == ( &( pxReadyTasksLists[ uxPriorityUsedOnEntry ] ) ) ) ? ( ( ( char ) 1 ) ) : ( ( ( char ) 0 ) ) ) != ( ( char ) 0 ) )
                {
                    /* The task is currently in its ready list - remove before
                     * adding it to its new ready list.  As we are in a critical
                     * section we can do this even if the scheduler is suspended. */
                    if( uxListRemove( &( pxTCB->xStateListItem ) ) == ( UBaseType_t ) 0 )
                    {
                        /* It is known that the task is in its ready list so
                         * there is no need to check again and the port level
                         * reset macro can be called directly. */
                                                                                             ;
                    }
                    else
                    {
                                                ;
                    }

                    ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;
                }
                else
                {
                    /* It's possible that xYieldForTask was already set to pdTRUE because
                     * its priority is being raised. However, since it is not in a ready list
                     * we don't actually need to yield for it. */
                    xYieldForTask = ( ( char ) 0 );
                }


                    if( xYieldRequired != ( ( char ) 0 ) )
                    {
                        prvYieldCore( xCoreID );
                    }
                    else if( xYieldForTask != ( ( char ) 0 ) )
                    {
                        prvYieldForTask( pxTCB, ( ( char ) 1 ) );
                    }
                    else
                    {
                                                ;
                    }


                /* Remove compiler warning about unused variables when the port
                 * optimised task selection is not being used. */
                ( void ) uxPriorityUsedOnEntry;
            }
        }
        vTaskExitCritical();
    }


/*-----------------------------------------------------------*/
// # 2572 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 2595 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 2613 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 2641 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/



    void vTaskSuspend( TaskHandle_t xTaskToSuspend )
    {
        TCB_t * pxTCB;
        TaskRunning_t xTaskRunningOnCore;

        vTaskEnterCritical();
        {
            /* If null is passed in here then it is the running task that is
             * being suspended. */
            pxTCB = ( ( ( xTaskToSuspend ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTaskToSuspend ) );

                                      ;

            xTaskRunningOnCore = pxTCB->xTaskRunState;

            /* Remove task from the ready/delayed list and place in the
             * suspended list. */
            if( uxListRemove( &( pxTCB->xStateListItem ) ) == ( UBaseType_t ) 0 )
            {
                                                             ;
            }
            else
            {
                                        ;
            }

            /* Is the task waiting on an event also? */
            if( ( ( &( pxTCB->xEventListItem ) )->pxContainer ) != 0 )
            {
                ( void ) uxListRemove( &( pxTCB->xEventListItem ) );
            }
            else
            {
                                        ;
            }

            vListInsertEnd( &xSuspendedTaskList, &( pxTCB->xStateListItem ) );


                {
                    BaseType_t x;

                    for( x = 0; x < 1; x++ )
                    {
                        if( pxTCB->ucNotifyState[ x ] == ( ( uint8_t ) 1 ) )
                        {
                            /* The task was blocked to wait for a notification, but is
                             * now suspended, so no notification was received. */
                            pxTCB->ucNotifyState[ x ] = ( ( uint8_t ) 0 );
                        }
                    }
                }


            if( xSchedulerRunning != ( ( char ) 0 ) )
            {
                /* Reset the next expected unblock time in case it referred to the
                 * task that is now in the Suspended state. */
                prvResetNextTaskUnblockTime();
            }
            else
            {
                                        ;
            }

            if( ( ( 0 <= xTaskRunningOnCore ) && ( xTaskRunningOnCore < 1 ) ) )
            {
                if( xSchedulerRunning != ( ( char ) 0 ) )
                {
                    if( xTaskRunningOnCore == 0 )
                    {
                        /* The current task has just been suspended. */
                        assert(uxSchedulerSuspended == 0);
                        vTaskYieldWithinAPI();
                    }
                    else
                    {
                        prvYieldCore( xTaskRunningOnCore );
                    }

                    vTaskExitCritical();
                }
                else
                {
                    vTaskExitCritical();

                    assert(pxTCB == pxCurrentTCBs[ xTaskRunningOnCore ]);

                    /* The scheduler is not running, but the task that was pointed
                     * to by pxCurrentTCB has just been suspended and pxCurrentTCB
                     * must be adjusted to point to a different task. */
                    if( ( ( &xSuspendedTaskList )->uxNumberOfItems ) == uxCurrentNumberOfTasks ) /*lint !e931 Right has no side effect, just volatile. */
                    {
                        /* No other tasks are ready, so set the core's TCB back to
                         * NULL so when the next task is created the core's TCB will
                         * be able to be set to point to it no matter what its relative
                         * priority is. */
                        pxTCB->xTaskRunState = ( TaskRunning_t ) ( -1 );
                        pxCurrentTCBs[ xTaskRunningOnCore ] = 0;
                    }
                    else
                    {
                        /* Attempt to switch in a new task. This could fail since the idle tasks
                         * haven't been created yet. If it does then set the core's TCB back to
                         * NULL. */
                        if( prvSelectHighestPriorityTask( xTaskRunningOnCore ) == ( ( char ) 0 ) )
                        {
                            pxTCB->xTaskRunState = ( TaskRunning_t ) ( -1 );
                            pxCurrentTCBs[ xTaskRunningOnCore ] = 0;
                        }
                    }
                }
            }
            else
            {
                vTaskExitCritical();
            }
        } /* taskEXIT_CRITICAL() - already exited in one of three cases above */
    }


/*-----------------------------------------------------------*/



    static BaseType_t prvTaskIsTaskSuspended( const TaskHandle_t xTask )
    {
        BaseType_t xReturn = ( ( char ) 0 );
        const TCB_t * pxTCB = xTask;

        /* Accesses xPendingReadyList so must be called from a critical section. */

        /* It does not make sense to check if the calling task is suspended. */
        assert(xTask);

        /* Is the task being resumed actually in the suspended list? */
        if( ( ( ( &( pxTCB->xStateListItem ) )->pxContainer == ( &xSuspendedTaskList ) ) ? ( ( ( char ) 1 ) ) : ( ( ( char ) 0 ) ) ) != ( ( char ) 0 ) )
        {
            /* Has the task already been resumed from within an ISR? */
            if( ( ( ( &( pxTCB->xEventListItem ) )->pxContainer == ( &xPendingReadyList ) ) ? ( ( ( char ) 1 ) ) : ( ( ( char ) 0 ) ) ) == ( ( char ) 0 ) )
            {
                /* Is it in the suspended list because it is in the Suspended
                 * state, or because is is blocked with no timeout? */
                if( ( ( ( &( pxTCB->xEventListItem ) )->pxContainer == ( 0 ) ) ? ( ( ( char ) 1 ) ) : ( ( ( char ) 0 ) ) ) != ( ( char ) 0 ) ) /*lint !e961.  The cast is only redundant when NULL is used. */
                {
                    xReturn = ( ( char ) 1 );
                }
                else
                {
                                            ;
                }
            }
            else
            {
                                        ;
            }
        }
        else
        {
                                    ;
        }

        return xReturn;
    } /*lint !e818 xTask cannot be a pointer to const because it is a typedef. */


/*-----------------------------------------------------------*/



    void vTaskResume( TaskHandle_t xTaskToResume )
    {

            /* Reason for rewrite:
            * VeriFast does not support const pointers.
            */
            TCB_t * pxTCB = xTaskToResume;




        /* It does not make sense to resume the calling task. */
        assert(xTaskToResume);

        /* The parameter cannot be NULL as it is impossible to resume the
         * currently executing task. It is also impossible to resume a task
         * that is actively running on another core but it is too dangerous
         * to check their run state here. Safer to get into a critical section
         * and check if it is actually suspended or not below. */
        if( pxTCB != 0 )
        {
            vTaskEnterCritical();
            {
                if( prvTaskIsTaskSuspended( pxTCB ) != ( ( char ) 0 ) )
                {
                                             ;

                    /* The ready list can be accessed even if the scheduler is
                     * suspended because this is inside a critical section. */
                    ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
                    ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;

                    /* A higher priority task may have just been resumed. */

                        {
                            prvYieldForTask( pxTCB, ( ( char ) 1 ) );
                        }

                }
                else
                {
                                            ;
                }
            }
            vTaskExitCritical();
        }
        else
        {
                                    ;
        }
    }



/*-----------------------------------------------------------*/



    BaseType_t xTaskResumeFromISR( TaskHandle_t xTaskToResume )
    {
        BaseType_t xYieldRequired = ( ( char ) 0 );

            /* Reason for rewrite:
            * VeriFast does not support const pointers.
            */
           TCB_t * pxTCB = xTaskToResume;



        UBaseType_t uxSavedInterruptStatus;

        assert(xTaskToResume);

        /* RTOS ports that support interrupt nesting have the concept of a
         * maximum  system call (or maximum API call) interrupt priority.
         * Interrupts that are  above the maximum system call priority are keep
         * permanently enabled, even when the RTOS kernel is in a critical section,
         * but cannot make any calls to FreeRTOS API functions.  If configASSERT()
         * is defined in FreeRTOSConfig.h then
         * portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will result in an assertion
         * failure if a FreeRTOS API function is called from an interrupt that has
         * been assigned a priority above the configured maximum system call
         * priority.  Only FreeRTOS functions that end in FromISR can be called
         * from interrupts  that have been assigned a priority at or (logically)
         * below the maximum system call interrupt priority.  FreeRTOS maintains a
         * separate interrupt safe API to ensure interrupt entry is as fast and as
         * simple as possible.  More information (albeit Cortex-M specific) is
         * provided on the following link:
         * https://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html */
                                                  ;

        uxSavedInterruptStatus = assert_fct(false, "portSET_INTERRUPT_MASK_FROM_ISR");
        {
            if( prvTaskIsTaskSuspended( pxTCB ) != ( ( char ) 0 ) )
            {
                                                  ;

                /* Check the ready lists can be accessed. */
                if( uxSchedulerSuspended == ( UBaseType_t ) ( ( char ) 0 ) )
                {
                    /* Ready lists can be accessed so move the task from the
                     * suspended list to the ready list directly. */

                    ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
                    ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;
                }
                else
                {
                    /* The delayed or ready lists cannot be accessed so the task
                     * is held in the pending ready list until the scheduler is
                     * unsuspended. */
                    vListInsertEnd( &( xPendingReadyList ), &( pxTCB->xEventListItem ) );
                }


                    prvYieldForTask( pxTCB, ( ( char ) 1 ) );

                    if( xYieldPendings[ 0 ] != ( ( char ) 0 ) )
                    {
                        xYieldRequired = ( ( char ) 1 );
                    }

            }
            else
            {
                                        ;
            }
        }
        do { vTaskExitCritical(); assert_fct(false, "portRESTORE_INTERRUPTS"); } while (0);

        return xYieldRequired;
    }


/*-----------------------------------------------------------*/

static BaseType_t prvCreateIdleTasks( void )
{
    BaseType_t xReturn = ( ( ( char ) 1 ) );
    BaseType_t xCoreID;
    char cIdleName[ 16 ];

    /* Add each idle task at the lowest priority. */
    for( xCoreID = ( BaseType_t ) 0; xCoreID < ( BaseType_t ) 1; xCoreID++ )
    {
        BaseType_t x;

        if( xReturn == ( ( ( char ) 0 ) ) )
        {
            break;
        }
        else
        {
                                    ;
        }

        for( x = ( BaseType_t ) 0; x < ( BaseType_t ) 16; x++ )
        {
            cIdleName[ x ] = "IDLE"[ x ];

            /* Don't copy all configMAX_TASK_NAME_LEN if the string is shorter than
             * configMAX_TASK_NAME_LEN characters just in case the memory after the
             * string is not accessible (extremely unlikely). */
            if( cIdleName[ x ] == ( char ) 0x00 )
            {
                break;
            }
            else
            {
                                        ;
            }
        }

        /* Append the idle task number to the end of the name if there is space */
        if( x < 16 )
        {
            cIdleName[ x++ ] = xCoreID + '0';

            /* And append a null character if there is space */
            if( x < 16 )
            {
                cIdleName[ x ] = '\0';
            }
            else
            {
                                        ;
            }
        }
        else
        {
                                    ;
        }
// # 3054 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            {
                if( xCoreID == 0 )
                {
                    /* The Idle task is being created using dynamically allocated RAM. */
                    xReturn = xTaskCreate( prvIdleTask,
                                           cIdleName,
                                           ( uint32_t ) 256,
                                           ( void * ) 0,
                                           ( ( UBaseType_t ) 0x00 ), /* In effect ( tskIDLE_PRIORITY | portPRIVILEGE_BIT ), but tskIDLE_PRIORITY is zero. */
                                           &xIdleTaskHandle[ xCoreID ] ); /*lint !e961 MISRA exception, justified as it is not a redundant explicit cast to all supported compilers. */
                }
// # 3077 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            }

    }

    return xReturn;
}

void vTaskStartScheduler( void )
{
    BaseType_t xReturn;


        {
            xReturn = xTimerCreateTimerTask();
        }


    xReturn = prvCreateIdleTasks();

    if( xReturn == ( ( ( char ) 1 ) ) )
    {
        /* freertos_tasks_c_additions_init() should only be called if the user
         * definable macro FREERTOS_TASKS_C_ADDITIONS_INIT() is defined, as that is
         * the only macro called by the function. */






        /* Interrupts are turned off here, to ensure a tick does not occur
         * before or during the call to xPortStartScheduler().  The stacks of
         * the created tasks contain a status word with interrupts switched on
         * so interrupts will automatically get re-enabled when the first task
         * starts to run. */
        assert_fct(false, "portDISABLE_INTERRUPTS");
// # 3127 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        xNextTaskUnblockTime = ( TickType_t ) 0xffffffffUL;
        xSchedulerRunning = ( ( char ) 1 );
        xTickCount = ( TickType_t ) 0;

        /* If configGENERATE_RUN_TIME_STATS is defined then the following
         * macro must be defined to configure the timer/counter used to generate
         * the run time counter time base.   NOTE:  If configGENERATE_RUN_TIME_STATS
         * is set to 0 and the following line fails to build then ensure you do not
         * have portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() defined in your
         * FreeRTOSConfig.h file. */
                                                ;

                               ;

        /* Setting up the timer tick is hardware specific and thus in the
         * portable interface. */
        if( xPortStartScheduler() != ( ( char ) 0 ) )
        {
            /* Should not reach here as if the scheduler is running the
             * function will not return. */
        }
        else
        {
            /* Should only reach here if a task calls xTaskEndScheduler(). */
        }
    }
    else
    {
        /* This line will only be reached if the kernel could not be started,
         * because there was not enough FreeRTOS heap to create the idle task
         * or the timer task. */
        assert(xReturn != ( -1 ));
    }

    /* Prevent compiler warnings if INCLUDE_xTaskGetIdleTaskHandle is set to 0,
     * meaning xIdleTaskHandle is not used anywhere else. */
    ( void ) xIdleTaskHandle;

    /* OpenOCD makes use of uxTopUsedPriority for thread debugging. Prevent uxTopUsedPriority
     * from getting optimized out as it is no longer used by the kernel. */
    ( void ) uxTopUsedPriority;
}
/*-----------------------------------------------------------*/

void vTaskEndScheduler( void )
{
    /* Stop the scheduler interrupts and call the portable scheduler end
     * routine so the original ISRs can be restored if necessary.  The port
     * layer must ensure interrupts enable  bit is left in the correct state. */
    assert_fct(false, "portDISABLE_INTERRUPTS");
    xSchedulerRunning = ( ( char ) 0 );
    vPortEndScheduler();
}
/*----------------------------------------------------------*/

void vTaskSuspendAll( void )
{
    UBaseType_t ulState;

    /* This must only be called from within a task */
                          ;

    if( xSchedulerRunning != ( ( char ) 0 ) )
    {
        /* writes to uxSchedulerSuspended must be protected by both the task AND ISR locks.
         * We must disable interrupts before we grab the locks in the event that this task is
         * interrupted and switches context before incrementing uxSchedulerSuspended.
         * It is safe to re-enable interrupts after releasing the ISR lock and incrementing
         * uxSchedulerSuspended since that will prevent context switches. */
        ulState = assert_fct(false, "portDISABLE_INTERRUPTS");

        /* portSOFRWARE_BARRIER() is only implemented for emulated/simulated ports that
         * do not otherwise exhibit real time behaviour. */
                              ;

        vPortRecursiveLock(1, spin_lock_instance(15), ( ( char ) 1 ));
        vPortRecursiveLock(0, spin_lock_instance(14), ( ( char ) 1 ));

        /* The scheduler is suspended if uxSchedulerSuspended is non-zero.  An increment
         * is used to allow calls to vTaskSuspendAll() to nest. */
        ++uxSchedulerSuspended;
        vPortRecursiveLock(0, spin_lock_instance(14), ( ( char ) 0 ));

        if( ( uxSchedulerSuspended == 1U ) && ( xTaskGetCurrentTaskHandle()->uxCriticalNesting == 0U ) )
        {
            prvCheckForRunStateChange();
        }

        assert_fct(false, "portRESTORE_INTERRUPTS");
    }
    else
    {
                                ;
    }
}
/*----------------------------------------------------------*/
// # 3285 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*----------------------------------------------------------*/

BaseType_t xTaskResumeAll( void )
{
    TCB_t * pxTCB = 0;
    BaseType_t xAlreadyYielded = ( ( char ) 0 );

    if( xSchedulerRunning != ( ( char ) 0 ) )
    {
        /* It is possible that an ISR caused a task to be removed from an event
         * list while the scheduler was suspended.  If this was the case then the
         * removed task will have been added to the xPendingReadyList.  Once the
         * scheduler has been resumed it is safe to move all the pending ready
         * tasks from this list into their appropriate ready list. */
        vTaskEnterCritical();
        {
            BaseType_t xCoreID;

            xCoreID = 0;

            /* If uxSchedulerSuspended is zero then this function does not match a
             * previous call to vTaskSuspendAll(). */
            assert(uxSchedulerSuspended);

            --uxSchedulerSuspended;
            vPortRecursiveLock(1, spin_lock_instance(15), ( ( char ) 0 ));

            if( uxSchedulerSuspended == ( UBaseType_t ) ( ( char ) 0 ) )
            {
                if( uxCurrentNumberOfTasks > ( UBaseType_t ) 0U )
                {
                    /* Move any readied tasks from the pending list into the
                     * appropriate ready list. */
                    while( ( ( ( &xPendingReadyList )->uxNumberOfItems == ( UBaseType_t ) 0 ) ? ( ( char ) 1 ) : ( ( char ) 0 ) ) == ( ( char ) 0 ) )
                    {
                        pxTCB = ( ( &( ( ( &xPendingReadyList ) )->xListEnd ) )->pxNext->pvOwner ); /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */
                        ( void ) uxListRemove( &( pxTCB->xEventListItem ) );
                        ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
                        ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;

                        /* All appropriate tasks yield at the moment a task is added to xPendingReadyList.
                         * If the current core yielded then vTaskSwitchContext() has already been called
                         * which sets xYieldPendings for the current core to pdTRUE. */
                    }

                    if( pxTCB != 0 )
                    {
                        /* A task was unblocked while the scheduler was suspended,
                         * which may have prevented the next unblock time from being
                         * re-calculated, in which case re-calculate it now.  Mainly
                         * important for low power tickless implementations, where
                         * this can prevent an unnecessary exit from low power
                         * state. */
                        prvResetNextTaskUnblockTime();
                    }

                    /* If any ticks occurred while the scheduler was suspended then
                     * they should be processed now.  This ensures the tick count does
                     * not	slip, and that any delayed tasks are resumed at the correct
                     * time.
                     *
                     * It should be safe to call xTaskIncrementTick here from any core
                     * since we are in a critical section and xTaskIncrementTick itself
                     * protects itself within a critical section. Suspending the scheduler
                     * from any core causes xTaskIncrementTick to increment uxPendedCounts.*/
                    {
                        TickType_t xPendedCounts = xPendedTicks; /* Non-volatile copy. */

                        if( xPendedCounts > ( TickType_t ) 0U )
                        {
                            do
                            {
                                if( xTaskIncrementTick() != ( ( char ) 0 ) )
                                {
                                    /* other cores are interrupted from
                                     * within xTaskIncrementTick(). */
                                    xYieldPendings[ xCoreID ] = ( ( char ) 1 );
                                }
                                else
                                {
                                                            ;
                                }

                                --xPendedCounts;
                            } while( xPendedCounts > ( TickType_t ) 0U );

                            xPendedTicks = 0;
                        }
                        else
                        {
                                                    ;
                        }
                    }

                    if( xYieldPendings[ xCoreID ] != ( ( char ) 0 ) )
                    {
                        /* If xYieldPendings is true then taskEXIT_CRITICAL()
                         * will yield, so make sure we return true to let the
                         * caller know a yield has already happened. */
                        xAlreadyYielded = ( ( char ) 1 );
                    }
                }
            }
            else
            {
                                        ;
            }
        }
        vTaskExitCritical();
    }
    else
    {
                                ;
    }

    return xAlreadyYielded;
}
/*-----------------------------------------------------------*/

TickType_t xTaskGetTickCount( void )
{
    TickType_t xTicks;

    /* Critical section required if running on a 16 bit processor. */
                                  ;
    {
        xTicks = xTickCount;
    }
                                 ;

    return xTicks;
}
/*-----------------------------------------------------------*/

TickType_t xTaskGetTickCountFromISR( void )
{
    TickType_t xReturn;
    UBaseType_t uxSavedInterruptStatus;

    /* RTOS ports that support interrupt nesting have the concept of a maximum
     * system call (or maximum API call) interrupt priority.  Interrupts that are
     * above the maximum system call priority are kept permanently enabled, even
     * when the RTOS kernel is in a critical section, but cannot make any calls to
     * FreeRTOS API functions.  If configASSERT() is defined in FreeRTOSConfig.h
     * then portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will result in an assertion
     * failure if a FreeRTOS API function is called from an interrupt that has been
     * assigned a priority above the configured maximum system call priority.
     * Only FreeRTOS functions that end in FromISR can be called from interrupts
     * that have been assigned a priority at or (logically) below the maximum
     * system call  interrupt priority.  FreeRTOS maintains a separate interrupt
     * safe API to ensure interrupt entry is as fast and as simple as possible.
     * More information (albeit Cortex-M specific) is provided on the following
     * link: https://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html */
                                              ;

    uxSavedInterruptStatus = 0;
    {
        xReturn = xTickCount;
    }
    ( void ) uxSavedInterruptStatus;

    return xReturn;
}
/*-----------------------------------------------------------*/

UBaseType_t uxTaskGetNumberOfTasks( void )
{
    /* A critical section is not required because the variables are of type
     * BaseType_t. */
    return uxCurrentNumberOfTasks;
}
/*-----------------------------------------------------------*/

char * pcTaskGetName( TaskHandle_t xTaskToQuery ) /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
{
    TCB_t * pxTCB;

    /* If null is passed in here then the name of the calling task is being
     * queried. */
    pxTCB = ( ( ( xTaskToQuery ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTaskToQuery ) );
    assert(pxTCB);
    return &( pxTCB->pcTaskName[ 0 ] );
}
/*-----------------------------------------------------------*/



    static TCB_t * prvSearchForNameWithinSingleList( List_t * pxList,
                                                     const char pcNameToQuery[] )
    {

    /* Reason for rewrite:
    * VeriFast does not support multiple pointer declarations to 
    * user-defined types in single statement 
    * (i.e., `A p1, p2;` is ok, `A *p1, *p2;` fails)
    */
        TCB_t * pxNextTCB;
        TCB_t * pxFirstTCB;
        TCB_t * pxReturn = 0;



        UBaseType_t x;
        char cNextChar;
        BaseType_t xBreakLoop;

        /* This function is called with the scheduler suspended. */

        if( ( ( pxList )->uxNumberOfItems ) > ( UBaseType_t ) 0 )
        {
            { List_t * pxConstList = ( pxList ); ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext; if( ( void * ) ( pxConstList )->pxIndex == ( void * ) &( ( pxConstList )->xListEnd ) ) { ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext; } ( pxFirstTCB ) = ( pxConstList )->pxIndex->pvOwner; }; /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */

            do
            {
                { List_t * pxConstList = ( pxList ); ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext; if( ( void * ) ( pxConstList )->pxIndex == ( void * ) &( ( pxConstList )->xListEnd ) ) { ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext; } ( pxNextTCB ) = ( pxConstList )->pxIndex->pvOwner; }; /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */

                /* Check each character in the name looking for a match or
                 * mismatch. */
                xBreakLoop = ( ( char ) 0 );

                for( x = ( UBaseType_t ) 0; x < ( UBaseType_t ) 16; x++ )
                {
                    cNextChar = pxNextTCB->pcTaskName[ x ];

                    if( cNextChar != pcNameToQuery[ x ] )
                    {
                        /* Characters didn't match. */
                        xBreakLoop = ( ( char ) 1 );
                    }
                    else if( cNextChar == ( char ) 0x00 )
                    {
                        /* Both strings terminated, a match must have been
                         * found. */
                        pxReturn = pxNextTCB;
                        xBreakLoop = ( ( char ) 1 );
                    }
                    else
                    {
                                                ;
                    }

                    if( xBreakLoop != ( ( char ) 0 ) )
                    {
                        break;
                    }
                }

                if( pxReturn != 0 )
                {
                    /* The handle has been found. */
                    break;
                }
            } while( pxNextTCB != pxFirstTCB );
        }
        else
        {
                                    ;
        }

        return pxReturn;
    }


/*-----------------------------------------------------------*/



    TaskHandle_t xTaskGetHandle( const char * pcNameToQuery ) /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
    {
        UBaseType_t uxQueue = 32;
        TCB_t * pxTCB;

        /* Task names will be truncated to configMAX_TASK_NAME_LEN - 1 bytes. */
        assert(strlen( pcNameToQuery ) < 16);

        vTaskSuspendAll();
        {
            /* Search the ready lists. */
            do
            {
                uxQueue--;
                pxTCB = prvSearchForNameWithinSingleList( ( List_t * ) &( pxReadyTasksLists[ uxQueue ] ), pcNameToQuery );

                if( pxTCB != 0 )
                {
                    /* Found the handle. */
                    break;
                }
            } while( uxQueue > ( UBaseType_t ) ( ( UBaseType_t ) 0U ) ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

            /* Search the delayed lists. */
            if( pxTCB == 0 )
            {
                pxTCB = prvSearchForNameWithinSingleList( ( List_t * ) pxDelayedTaskList, pcNameToQuery );
            }

            if( pxTCB == 0 )
            {
                pxTCB = prvSearchForNameWithinSingleList( ( List_t * ) pxOverflowDelayedTaskList, pcNameToQuery );
            }


                {
                    if( pxTCB == 0 )
                    {
                        /* Search the suspended list. */
                        pxTCB = prvSearchForNameWithinSingleList( &xSuspendedTaskList, pcNameToQuery );
                    }
                }



                {
                    if( pxTCB == 0 )
                    {
                        /* Search the deleted list. */
                        pxTCB = prvSearchForNameWithinSingleList( &xTasksWaitingTermination, pcNameToQuery );
                    }
                }

        }
        ( void ) xTaskResumeAll();

        return pxTCB;
    }


/*-----------------------------------------------------------*/



    UBaseType_t uxTaskGetSystemState( TaskStatus_t * pxTaskStatusArray,
                                      const UBaseType_t uxArraySize,
                                      uint32_t * pulTotalRunTime )
    {
        UBaseType_t uxTask = 0, uxQueue = 32;

        vTaskSuspendAll();
        {
            /* Is there a space in the array for each task in the system? */
            if( uxArraySize >= uxCurrentNumberOfTasks )
            {
                /* Fill in an TaskStatus_t structure with information on each
                 * task in the Ready state. */
                do
                {
                    uxQueue--;
                    uxTask += prvListTasksWithinSingleList( &( pxTaskStatusArray[ uxTask ] ), &( pxReadyTasksLists[ uxQueue ] ), eReady );
                } while( uxQueue > ( UBaseType_t ) ( ( UBaseType_t ) 0U ) ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

                /* Fill in an TaskStatus_t structure with information on each
                 * task in the Blocked state. */
                uxTask += prvListTasksWithinSingleList( &( pxTaskStatusArray[ uxTask ] ), ( List_t * ) pxDelayedTaskList, eBlocked );
                uxTask += prvListTasksWithinSingleList( &( pxTaskStatusArray[ uxTask ] ), ( List_t * ) pxOverflowDelayedTaskList, eBlocked );


                    {
                        /* Fill in an TaskStatus_t structure with information on
                         * each task that has been deleted but not yet cleaned up. */
                        uxTask += prvListTasksWithinSingleList( &( pxTaskStatusArray[ uxTask ] ), &xTasksWaitingTermination, eDeleted );
                    }



                    {
                        /* Fill in an TaskStatus_t structure with information on
                         * each task in the Suspended state. */
                        uxTask += prvListTasksWithinSingleList( &( pxTaskStatusArray[ uxTask ] ), &xSuspendedTaskList, eSuspended );
                    }
// # 3668 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
                    {
                        if( pulTotalRunTime != 0 )
                        {
                            *pulTotalRunTime = 0;
                        }
                    }

            }
            else
            {
                                        ;
            }
        }
        ( void ) xTaskResumeAll();

        return uxTask;
    }


/*----------------------------------------------------------*/



    TaskHandle_t * xTaskGetIdleTaskHandle( void )
    {
        /* If xTaskGetIdleTaskHandle() is called before the scheduler has been
         * started, then xIdleTaskHandle will be NULL. */
        assert(( xIdleTaskHandle != 0 ));
        return &( xIdleTaskHandle[ 0 ] );
    }


/*----------------------------------------------------------*/

/* This conditional compilation should use inequality to 0, not equality to 1.
 * This is to ensure vTaskStepTick() is available when user defined low power mode
 * implementations require configUSE_TICKLESS_IDLE to be set to a value other than
 * 1. */
// # 3719 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*----------------------------------------------------------*/

BaseType_t xTaskCatchUpTicks( TickType_t xTicksToCatchUp )
{
    BaseType_t xYieldOccurred;

    /* Must not be called with the scheduler suspended as the implementation
     * relies on xPendedTicks being wound down to 0 in xTaskResumeAll(). */
    assert(uxSchedulerSuspended == 0);

    /* Use xPendedTicks to mimic xTicksToCatchUp number of ticks occurring when
     * the scheduler is suspended so the ticks are executed in xTaskResumeAll(). */
    vTaskSuspendAll();
    xPendedTicks += xTicksToCatchUp;
    xYieldOccurred = xTaskResumeAll();

    return xYieldOccurred;
}
/*----------------------------------------------------------*/



    BaseType_t xTaskAbortDelay( TaskHandle_t xTask )
    {
        TCB_t * pxTCB = xTask;
        BaseType_t xReturn;

        assert(pxTCB);

        vTaskSuspendAll();
        {
            /* A task can only be prematurely removed from the Blocked state if
             * it is actually in the Blocked state. */
            if( eTaskGetState( xTask ) == eBlocked )
            {
                xReturn = ( ( ( char ) 1 ) );

                /* Remove the reference to the task from the blocked list.  An
                 * interrupt won't touch the xStateListItem because the
                 * scheduler is suspended. */
                ( void ) uxListRemove( &( pxTCB->xStateListItem ) );

                /* Is the task waiting on an event also?  If so remove it from
                 * the event list too.  Interrupts can touch the event list item,
                 * even though the scheduler is suspended, so a critical section
                 * is used. */
                vTaskEnterCritical();
                {
                    if( ( ( &( pxTCB->xEventListItem ) )->pxContainer ) != 0 )
                    {
                        ( void ) uxListRemove( &( pxTCB->xEventListItem ) );

                        /* This lets the task know it was forcibly removed from the
                         * blocked state so it should not re-evaluate its block time and
                         * then block again. */
                        pxTCB->ucDelayAborted = ( ( char ) 1 );
                    }
                    else
                    {
                                                ;
                    }
                }
                vTaskExitCritical();

                /* Place the unblocked task into the appropriate ready list. */
                ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;

                /* A task being unblocked cannot cause an immediate context
                 * switch if preemption is turned off. */

                    {
                        vTaskEnterCritical();
                        {
                            prvYieldForTask( pxTCB, ( ( char ) 0 ) );
                        }
                        vTaskExitCritical();
                    }

            }
            else
            {
                xReturn = ( ( ( char ) 0 ) );
            }
        }
        ( void ) xTaskResumeAll();

        return xReturn;
    }


/*----------------------------------------------------------*/

BaseType_t xTaskIncrementTick( void )
{
    TCB_t * pxTCB;
    TickType_t xItemValue;
    BaseType_t xSwitchRequired = ( ( char ) 0 );


        UBaseType_t x;
        BaseType_t xCoreYieldList[ 1 ] = { ( ( char ) 0 ) };


    vTaskEnterCritical();
    {
        /* Called by the portable layer each time a tick interrupt occurs.
         * Increments the tick then checks to see if the new tick value will cause any
         * tasks to be unblocked. */
                                              ;

        /* Tick increment should occur on every kernel timer event. Core 0 has the
         * responsibility to increment the tick, or increment the pended ticks if the
         * scheduler is suspended.  If pended ticks is greater than zero, the core that
         * calls xTaskResumeAll has the responsibility to increment the tick. */
        if( uxSchedulerSuspended == ( UBaseType_t ) ( ( char ) 0 ) )
        {
            /* Minor optimisation.  The tick count cannot change in this
             * block. */
            const TickType_t xConstTickCount = xTickCount + ( TickType_t ) 1;

            /* Increment the RTOS tick, switching the delayed and overflowed
             * delayed lists if it wraps to 0. */
            xTickCount = xConstTickCount;

            if( xConstTickCount == ( TickType_t ) 0U ) /*lint !e774 'if' does not always evaluate to false as it is looking for an overflow. */
            {
                { List_t * pxTemp; assert(( ( ( ( pxDelayedTaskList )->uxNumberOfItems == ( UBaseType_t ) 0 ) ? ( ( char ) 1 ) : ( ( char ) 0 ) ) )); pxTemp = pxDelayedTaskList; pxDelayedTaskList = pxOverflowDelayedTaskList; pxOverflowDelayedTaskList = pxTemp; xNumOfOverflows++; prvResetNextTaskUnblockTime(); };
            }
            else
            {
                                        ;
            }

            /* See if this tick has made a timeout expire.  Tasks are stored in
             * the	queue in the order of their wake time - meaning once one task
             * has been found whose block time has not expired there is no need to
             * look any further down the list. */
            if( xConstTickCount >= xNextTaskUnblockTime )
            {
                for( ; ; )
                {
                    if( ( ( ( pxDelayedTaskList )->uxNumberOfItems == ( UBaseType_t ) 0 ) ? ( ( char ) 1 ) : ( ( char ) 0 ) ) != ( ( char ) 0 ) )
                    {
                        /* The delayed list is empty.  Set xNextTaskUnblockTime
                         * to the maximum possible value so it is extremely
                         * unlikely that the
                         * if( xTickCount >= xNextTaskUnblockTime ) test will pass
                         * next time through. */
                        xNextTaskUnblockTime = ( TickType_t ) 0xffffffffUL; /*lint !e961 MISRA exception as the casts are only redundant for some ports. */
                        break;
                    }
                    else
                    {
                        /* The delayed list is not empty, get the value of the
                         * item at the head of the delayed list.  This is the time
                         * at which the task at the head of the delayed list must
                         * be removed from the Blocked state. */
                        pxTCB = ( ( &( ( pxDelayedTaskList )->xListEnd ) )->pxNext->pvOwner ); /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */
                        xItemValue = ( ( &( pxTCB->xStateListItem ) )->xItemValue );

                        if( xConstTickCount < xItemValue )
                        {
                            /* It is not time to unblock this item yet, but the
                             * item value is the time at which the task at the head
                             * of the blocked list must be removed from the Blocked
                             * state -	so record the item value in
                             * xNextTaskUnblockTime. */
                            xNextTaskUnblockTime = xItemValue;
                            break; /*lint !e9011 Code structure here is deemed easier to understand with multiple breaks. */
                        }
                        else
                        {
                                                    ;
                        }

                        /* It is time to remove the item from the Blocked state. */
                        ( void ) uxListRemove( &( pxTCB->xStateListItem ) );

                        /* Is the task waiting on an event also?  If so remove
                         * it from the event list. */
                        if( ( ( &( pxTCB->xEventListItem ) )->pxContainer ) != 0 )
                        {
                            ( void ) uxListRemove( &( pxTCB->xEventListItem ) );
                        }
                        else
                        {
                                                    ;
                        }

                        /* Place the unblocked task into the appropriate ready
                         * list. */
                        ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;

                        /* A task being unblocked cannot cause an immediate
                         * context switch if preemption is turned off. */

                            {
                                prvYieldForTask( pxTCB, ( ( char ) 1 ) );
                            }

                    }
                }
            }

            /* Tasks of equal priority to the currently running task will share
             * processing time (time slice) if preemption is on, and the application
             * writer has not explicitly turned time slicing off. */

                {
                    /* TODO: If there are fewer "non-IDLE" READY tasks than cores, do not
                     * force a context switch that would just shuffle tasks around cores */
                    /* TODO: There are certainly better ways of doing this that would reduce
                     * the number of interrupts and also potentially help prevent tasks from
                     * moving between cores as often. This, however, works for now. */
                    for( x = ( UBaseType_t ) 0; x < ( UBaseType_t ) 1; x++ )
                    {
                        if( ( ( &( pxReadyTasksLists[ pxCurrentTCBs[ x ]->uxPriority ] ) )->uxNumberOfItems ) > ( UBaseType_t ) 1 )
                        {
                            xCoreYieldList[ x ] = ( ( char ) 1 );
                        }
                        else
                        {
                                                    ;
                        }
                    }
                }



                {
                    /* Guard against the tick hook being called when the pended tick
                     * count is being unwound (when the scheduler is being unlocked). */
                    if( xPendedTicks == ( TickType_t ) 0 )
                    {
                        vApplicationTickHook();
                    }
                    else
                    {
                                                ;
                    }
                }



                {
                    for( x = ( UBaseType_t ) 0; x < ( UBaseType_t ) 1; x++ )
                    {
                        if( xYieldPendings[ x ] != ( ( char ) 0 ) )
                        {
                            xCoreYieldList[ x ] = ( ( char ) 1 );
                        }
                        else
                        {
                                                    ;
                        }
                    }
                }



                {
                    BaseType_t xCoreID;

                    xCoreID = 0;

                    for( x = ( UBaseType_t ) 0; x < ( UBaseType_t ) 1; x++ )
                    {



                        {
                            if( xCoreYieldList[ x ] != ( ( char ) 0 ) )
                            {
                                if( x == xCoreID )
                                {
                                    xSwitchRequired = ( ( char ) 1 );
                                }
                                else
                                {
                                    prvYieldCore( x );
                                }
                            }
                            else
                            {
                                                        ;
                            }
                        }
                    }
                }

        }
        else
        {
            ++xPendedTicks;

            /* The tick hook gets called at regular intervals, even if the
             * scheduler is locked. */

                {
                    vApplicationTickHook();
                }

        }
    }
    vTaskExitCritical();

    return xSwitchRequired;
}
/*-----------------------------------------------------------*/
// # 4057 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 4081 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 4106 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 4139 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/

void vTaskSwitchContext( BaseType_t xCoreID )
{
    /* Acquire both locks:
     * - The ISR lock protects the ready list from simultaneous access by
     *  both other ISRs and tasks.
     * - We also take the task lock to pause here in case another core has
     *  suspended the scheduler. We don't want to simply set xYieldPending
     *  and move on if another core suspended the scheduler. We should only
     *  do that if the current core has suspended the scheduler. */

    vPortRecursiveLock(1, spin_lock_instance(15), ( ( char ) 1 )); /* Must always acquire the task lock first */
    vPortRecursiveLock(0, spin_lock_instance(14), ( ( char ) 1 ));
    {
        /* vTaskSwitchContext() must never be called from within a critical section.
         * This is not necessarily true for vanilla FreeRTOS, but it is for this SMP port. */
        assert(xTaskGetCurrentTaskHandle()->uxCriticalNesting == 0);

        if( uxSchedulerSuspended != ( UBaseType_t ) ( ( char ) 0 ) )
        {
            /* The scheduler is currently suspended - do not allow a context
             * switch. */
            xYieldPendings[ xCoreID ] = ( ( char ) 1 );
        }
        else
        {
            xYieldPendings[ xCoreID ] = ( ( char ) 0 );
                                    ;
// # 4197 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            /* Check for stack overflow, if configured. */
            { const uint32_t * pulStack = ( uint32_t * ) xTaskGetCurrentTaskHandle()->pxStack; const uint32_t ulCheckValue = ( uint32_t ) 0xa5a5a5a5; if( ( pulStack[ 0 ] != ulCheckValue ) || ( pulStack[ 1 ] != ulCheckValue ) || ( pulStack[ 2 ] != ulCheckValue ) || ( pulStack[ 3 ] != ulCheckValue ) ) { vApplicationStackOverflowHook( ( TaskHandle_t ) xTaskGetCurrentTaskHandle(), xTaskGetCurrentTaskHandle()->pcTaskName ); } };

            /* Before the currently running task is switched out, save its errno. */






            /* Select a new task to run using either the generic C or port
             * optimised asm code. */
            ( void ) prvSelectHighestPriorityTask( xCoreID );
                                   ;

            /* After the new task is switched in, update the global errno. */
// # 4231 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        }
    }
    vPortRecursiveLock(0, spin_lock_instance(14), ( ( char ) 0 ));
    vPortRecursiveLock(1, spin_lock_instance(15), ( ( char ) 0 ));
}
/*-----------------------------------------------------------*/

void vTaskPlaceOnEventList( List_t * pxEventList,
                            const TickType_t xTicksToWait )
{
    assert(pxEventList);

    /* THIS FUNCTION MUST BE CALLED WITH EITHER INTERRUPTS DISABLED OR THE
     * SCHEDULER SUSPENDED AND THE QUEUE BEING ACCESSED LOCKED. */

    /* Place the event list item of the TCB in the appropriate event list.
     * This is placed in the list in priority order so the highest priority task
     * is the first to be woken by the event.  The queue that contains the event
     * list is locked, preventing simultaneous access from interrupts. */
    vListInsert( pxEventList, &( xTaskGetCurrentTaskHandle()->xEventListItem ) );

    prvAddCurrentTaskToDelayedList( xTicksToWait, ( ( char ) 1 ) );
}
/*-----------------------------------------------------------*/

void vTaskPlaceOnUnorderedEventList( List_t * pxEventList,
                                     const TickType_t xItemValue,
                                     const TickType_t xTicksToWait )
{
    assert(pxEventList);

    /* THIS FUNCTION MUST BE CALLED WITH THE SCHEDULER SUSPENDED.  It is used by
     * the event groups implementation. */
    assert(uxSchedulerSuspended != 0);

    /* Store the item value in the event list item.  It is safe to access the
     * event list item here as interrupts won't access the event list item of a
     * task that is not in the Blocked state. */
    ( ( &( xTaskGetCurrentTaskHandle()->xEventListItem ) )->xItemValue = ( xItemValue | 0x80000000UL ) );

    /* Place the event list item of the TCB at the end of the appropriate event
     * list.  It is safe to access the event list here because it is part of an
     * event group implementation - and interrupts don't access event groups
     * directly (instead they access them indirectly by pending function calls to
     * the task level). */
    vListInsertEnd( pxEventList, &( xTaskGetCurrentTaskHandle()->xEventListItem ) );

    prvAddCurrentTaskToDelayedList( xTicksToWait, ( ( char ) 1 ) );
}
/*-----------------------------------------------------------*/



    void vTaskPlaceOnEventListRestricted( List_t * pxEventList,
                                          TickType_t xTicksToWait,
                                          const BaseType_t xWaitIndefinitely )
    {
        assert(pxEventList);

        /* This function should not be called by application code hence the
         * 'Restricted' in its name.  It is not part of the public API.  It is
         * designed for use by kernel code, and has special calling requirements -
         * it should be called with the scheduler suspended. */


        /* Place the event list item of the TCB in the appropriate event list.
         * In this case it is assume that this is the only task that is going to
         * be waiting on this event list, so the faster vListInsertEnd() function
         * can be used in place of vListInsert. */
        vListInsertEnd( pxEventList, &( xTaskGetCurrentTaskHandle()->xEventListItem ) );

        /* If the task should block indefinitely then set the block time to a
         * value that will be recognised as an indefinite delay inside the
         * prvAddCurrentTaskToDelayedList() function. */
        if( xWaitIndefinitely != ( ( char ) 0 ) )
        {
            xTicksToWait = ( TickType_t ) 0xffffffffUL;
        }

                                                              ;
        prvAddCurrentTaskToDelayedList( xTicksToWait, xWaitIndefinitely );
    }


/*-----------------------------------------------------------*/

BaseType_t xTaskRemoveFromEventList( const List_t * pxEventList )
{
    TCB_t * pxUnblockedTCB;
    BaseType_t xReturn;

    /* THIS FUNCTION MUST BE CALLED FROM A CRITICAL SECTION.  It can also be
     * called from a critical section within an ISR. */

    /* The event list is sorted in priority order, so the first in the list can
     * be removed as it is known to be the highest priority.  Remove the TCB from
     * the delayed list, and add it to the ready list.
     *
     * If an event is for a queue that is locked then this function will never
     * get called - the lock count on the queue will get modified instead.  This
     * means exclusive access to the event list is guaranteed here.
     *
     * This function assumes that a check has already been made to ensure that
     * pxEventList is not empty. */
    pxUnblockedTCB = ( ( &( ( pxEventList )->xListEnd ) )->pxNext->pvOwner ); /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */
    assert(pxUnblockedTCB);
    ( void ) uxListRemove( &( pxUnblockedTCB->xEventListItem ) );

    if( uxSchedulerSuspended == ( UBaseType_t ) ( ( char ) 0 ) )
    {
        ( void ) uxListRemove( &( pxUnblockedTCB->xStateListItem ) );
        ; { if( ( ( pxUnblockedTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxUnblockedTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxUnblockedTCB )->uxPriority ] ), &( ( pxUnblockedTCB )->xStateListItem ) ); ;
// # 4357 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    }
    else
    {
        /* The delayed and ready lists cannot be accessed, so hold this task
         * pending until the scheduler is resumed. */
        vListInsertEnd( &( xPendingReadyList ), &( pxUnblockedTCB->xEventListItem ) );
    }

    xReturn = ( ( char ) 0 );

        prvYieldForTask( pxUnblockedTCB, ( ( char ) 0 ) );

        if( xYieldPendings[ 0 ] != ( ( char ) 0 ) )
        {
            xReturn = ( ( char ) 1 );
        }


    return xReturn;
}
/*-----------------------------------------------------------*/

void vTaskRemoveFromUnorderedEventList( ListItem_t * pxEventListItem,
                                        const TickType_t xItemValue )
{
    TCB_t * pxUnblockedTCB;

    /* THIS FUNCTION MUST BE CALLED WITH THE SCHEDULER SUSPENDED.  It is used by
     * the event flags implementation. */
    assert(uxSchedulerSuspended != ( ( char ) 0 ));

    /* Store the new item value in the event list. */
    ( ( pxEventListItem )->xItemValue = ( xItemValue | 0x80000000UL ) );

    /* Remove the event list form the event flag.  Interrupts do not access
     * event flags. */
    pxUnblockedTCB = ( ( pxEventListItem )->pvOwner ); /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */
    assert(pxUnblockedTCB);
    ( void ) uxListRemove( pxEventListItem );
// # 4411 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    /* Remove the task from the delayed list and add it to the ready list.  The
     * scheduler is suspended so interrupts will not be accessing the ready
     * lists. */
    ( void ) uxListRemove( &( pxUnblockedTCB->xStateListItem ) );
    ; { if( ( ( pxUnblockedTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxUnblockedTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxUnblockedTCB )->uxPriority ] ), &( ( pxUnblockedTCB )->xStateListItem ) ); ;


        vTaskEnterCritical();
        {
            prvYieldForTask( pxUnblockedTCB, ( ( char ) 0 ) );
        }
        vTaskExitCritical();

}
/*-----------------------------------------------------------*/

void vTaskSetTimeOutState( TimeOut_t * pxTimeOut )
{
    assert(pxTimeOut);
    vTaskEnterCritical();
    {
        pxTimeOut->xOverflowCount = xNumOfOverflows;
        pxTimeOut->xTimeOnEntering = xTickCount;
    }
    vTaskExitCritical();
}
/*-----------------------------------------------------------*/

void vTaskInternalSetTimeOutState( TimeOut_t * pxTimeOut )
{
    /* For internal use only as it does not use a critical section. */
    pxTimeOut->xOverflowCount = xNumOfOverflows;
    pxTimeOut->xTimeOnEntering = xTickCount;
}
/*-----------------------------------------------------------*/

BaseType_t xTaskCheckForTimeOut( TimeOut_t * pxTimeOut,
                                 TickType_t * pxTicksToWait )
{
    BaseType_t xReturn;

    assert(pxTimeOut);
    assert(pxTicksToWait);

    vTaskEnterCritical();
    {
        /* Minor optimisation.  The tick count cannot change in this block. */
        const TickType_t xConstTickCount = xTickCount;
        const TickType_t xElapsedTime = xConstTickCount - pxTimeOut->xTimeOnEntering;


            if( xTaskGetCurrentTaskHandle()->ucDelayAborted != ( uint8_t ) ( ( char ) 0 ) )
            {
                /* The delay was aborted, which is not the same as a time out,
                 * but has the same result. */
                xTaskGetCurrentTaskHandle()->ucDelayAborted = ( ( char ) 0 );
                xReturn = ( ( char ) 1 );
            }
            else



            if( *pxTicksToWait == ( TickType_t ) 0xffffffffUL )
            {
                /* If INCLUDE_vTaskSuspend is set to 1 and the block time
                 * specified is the maximum block time then the task should block
                 * indefinitely, and therefore never time out. */
                xReturn = ( ( char ) 0 );
            }
            else


        if( ( xNumOfOverflows != pxTimeOut->xOverflowCount ) && ( xConstTickCount >= pxTimeOut->xTimeOnEntering ) ) /*lint !e525 Indentation preferred as is to make code within pre-processor directives clearer. */
        {
            /* The tick count is greater than the time at which
             * vTaskSetTimeout() was called, but has also overflowed since
             * vTaskSetTimeOut() was called.  It must have wrapped all the way
             * around and gone past again. This passed since vTaskSetTimeout()
             * was called. */
            xReturn = ( ( char ) 1 );
            *pxTicksToWait = ( TickType_t ) 0;
        }
        else if( xElapsedTime < *pxTicksToWait ) /*lint !e961 Explicit casting is only redundant with some compilers, whereas others require it to prevent integer conversion errors. */
        {
            /* Not a genuine timeout. Adjust parameters for time remaining. */
            *pxTicksToWait -= xElapsedTime;
            vTaskInternalSetTimeOutState( pxTimeOut );
            xReturn = ( ( char ) 0 );
        }
        else
        {
            *pxTicksToWait = ( TickType_t ) 0;
            xReturn = ( ( char ) 1 );
        }
    }
    vTaskExitCritical();

    return xReturn;
}
/*-----------------------------------------------------------*/

void vTaskMissedYield( void )
{
    /* Must be called from within a critical section */
    xYieldPendings[ 0 ] = ( ( char ) 1 );
}
/*-----------------------------------------------------------*/



    UBaseType_t uxTaskGetTaskNumber( TaskHandle_t xTask )
    {
        UBaseType_t uxReturn;

            /* Reason for rewrite:
            * VeriFast does not support const pointers.
            */
           TCB_t * pxTCB;




        if( xTask != 0 )
        {
            pxTCB = xTask;
            uxReturn = pxTCB->uxTaskNumber;
        }
        else
        {
            uxReturn = 0U;
        }

        return uxReturn;
    }


/*-----------------------------------------------------------*/



    void vTaskSetTaskNumber( TaskHandle_t xTask,
                             const UBaseType_t uxHandle )
    {
        TCB_t * pxTCB;

        if( xTask != 0 )
        {
            pxTCB = xTask;
            pxTCB->uxTaskNumber = uxHandle;
        }
    }



/*
 * -----------------------------------------------------------
 * The MinimalIdle task.
 * ----------------------------------------------------------
 *
 * The minimal idle task is used for all the additional Cores in a SMP system.
 * There must be only 1 idle task and the rest are minimal idle tasks.
 *
 * @todo additional conditional compiles to remove this function.
 */
// # 4635 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*
 * -----------------------------------------------------------
 * The Idle task.
 * ----------------------------------------------------------
 *
 *
 */
static void prvIdleTask( void * pvParameters )
{
    /* Stop warnings. */
    ( void ) pvParameters;

    /** THIS IS THE RTOS IDLE TASK - WHICH IS CREATED AUTOMATICALLY WHEN THE
     * SCHEDULER IS STARTED. **/

    /* In case a task that has a secure context deletes itself, in which case
     * the idle task is responsible for deleting the task's secure context, if
     * any. */
                                                                  ;

    /* All cores start up in the idle task. This initial yield gets the application
     * tasks started. */
    vPortYield();

    for( ; ; )
    {
        /* See if any tasks have deleted themselves - if so then the idle task
         * is responsible for freeing the deleted task's TCB and stack. */
        prvCheckTasksWaitingTermination();
// # 4676 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            {
                /* When using preemption tasks of equal priority will be
                 * timesliced.  If a task that is sharing the idle priority is ready
                 * to run then the idle task should yield before the end of the
                 * timeslice.
                 *
                 * A critical region is not required here as we are just reading from
                 * the list, and an occasional incorrect value will not matter.  If
                 * the ready list at the idle priority contains one more task than the
                 * number of idle tasks, which is equal to the configured numbers of cores
                 * then a task other than the idle task is ready to execute. */
                if( ( ( &( pxReadyTasksLists[ ( ( UBaseType_t ) 0U ) ] ) )->uxNumberOfItems ) > ( UBaseType_t ) 1 )
                {
                    vPortYield();
                }
                else
                {
                                            ;
                }
            }
// # 4712 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
        /* This conditional compilation should use inequality to 0, not equality
         * to 1.  This is to ensure portSUPPRESS_TICKS_AND_SLEEP() is called when
         * user defined low power mode  implementations require
         * configUSE_TICKLESS_IDLE to be set to a value other than 1. */
// # 4777 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    }
}
/*-----------------------------------------------------------*/
// # 4827 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/



    void vTaskSetThreadLocalStoragePointer( TaskHandle_t xTaskToSet,
                                            BaseType_t xIndex,
                                            void * pvValue )
    {
        TCB_t * pxTCB;

        if( xIndex < 5 )
        {
            pxTCB = ( ( ( xTaskToSet ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTaskToSet ) );
            assert(pxTCB != 0);
            pxTCB->pvThreadLocalStoragePointers[ xIndex ] = pvValue;
        }
    }


/*-----------------------------------------------------------*/



    void * pvTaskGetThreadLocalStoragePointer( TaskHandle_t xTaskToQuery,
                                               BaseType_t xIndex )
    {
        void * pvReturn = 0;
        TCB_t * pxTCB;

        if( xIndex < 5 )
        {
            pxTCB = ( ( ( xTaskToQuery ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTaskToQuery ) );
            pvReturn = pxTCB->pvThreadLocalStoragePointers[ xIndex ];
        }
        else
        {
            pvReturn = 0;
        }

        return pvReturn;
    }


/*-----------------------------------------------------------*/
// # 4887 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/

static void prvInitialiseTaskLists( void )
{
    UBaseType_t uxPriority;

    for( uxPriority = ( UBaseType_t ) 0U; uxPriority < ( UBaseType_t ) 32; uxPriority++ )
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }

    vListInitialise( &xDelayedTaskList1 );
    vListInitialise( &xDelayedTaskList2 );
    vListInitialise( &xPendingReadyList );


        {
            vListInitialise( &xTasksWaitingTermination );
        }



        {
            vListInitialise( &xSuspendedTaskList );
        }


    /* Start with pxDelayedTaskList using list1 and the pxOverflowDelayedTaskList
     * using list2. */
    pxDelayedTaskList = &xDelayedTaskList1;
    pxOverflowDelayedTaskList = &xDelayedTaskList2;
}
/*-----------------------------------------------------------*/

static void prvCheckTasksWaitingTermination( void )
{
    /** THIS FUNCTION IS CALLED FROM THE RTOS IDLE TASK **/


        {
            TCB_t * pxTCB;

            /* uxDeletedTasksWaitingCleanUp is used to prevent taskENTER_CRITICAL()
             * being called too often in the idle task. */
            while( uxDeletedTasksWaitingCleanUp > ( UBaseType_t ) 0U )
            {
                vTaskEnterCritical();
                {
                    /* Since we are SMP, multiple idles can be running simultaneously
                     * and we need to check that other idles did not cleanup while we were
                     * waiting to enter the critical section */
                    if( uxDeletedTasksWaitingCleanUp > ( UBaseType_t ) 0U )
                    {
                        pxTCB = ( ( &( ( ( &xTasksWaitingTermination ) )->xListEnd ) )->pxNext->pvOwner ); /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */

                        if( pxTCB->xTaskRunState == ( TaskRunning_t ) ( -1 ) )
                        {
                            ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
                            --uxCurrentNumberOfTasks;
                            --uxDeletedTasksWaitingCleanUp;
                            prvDeleteTCB( pxTCB );
                        }
                        else
                        {
                            /* The TCB to be deleted still has not yet been switched out
                             * by the scheduler, so we will just exit this loop early and
                             * try again next time. */
                            vTaskExitCritical();
                            break;
                        }
                    }
                }
                vTaskExitCritical();
            }
        }

}
/*-----------------------------------------------------------*/



    void vTaskGetInfo( TaskHandle_t xTask,
                       TaskStatus_t * pxTaskStatus,
                       BaseType_t xGetFreeStackSpace,
                       eTaskState eState )
    {
        TCB_t * pxTCB;

        /* xTask is NULL then get the state of the calling task. */
        pxTCB = ( ( ( xTask ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTask ) );

        pxTaskStatus->xHandle = ( TaskHandle_t ) pxTCB;
        pxTaskStatus->pcTaskName = ( const char * ) &( pxTCB->pcTaskName[ 0 ] );
        pxTaskStatus->uxCurrentPriority = pxTCB->uxPriority;
        pxTaskStatus->pxStackBase = pxTCB->pxStack;
        pxTaskStatus->xTaskNumber = pxTCB->uxTCBNumber;


            {
                pxTaskStatus->uxBasePriority = pxTCB->uxBasePriority;
            }
// # 4999 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
            {
                pxTaskStatus->ulRunTimeCounter = 0;
            }


        /* Obtaining the task state is a little fiddly, so is only done if the
         * value of eState passed into this function is eInvalid - otherwise the
         * state is just set to whatever is passed in. */
        if( eState != eInvalid )
        {
            if( ( ( 0 <= pxTCB->xTaskRunState ) && ( pxTCB->xTaskRunState < 1 ) ) )
            {
                pxTaskStatus->eCurrentState = eRunning;
            }
            else
            {
                pxTaskStatus->eCurrentState = eState;


                    {
                        /* If the task is in the suspended list then there is a
                         *  chance it is actually just blocked indefinitely - so really
                         *  it should be reported as being in the Blocked state. */
                        if( eState == eSuspended )
                        {
                            vTaskSuspendAll();
                            {
                                if( ( ( &( pxTCB->xEventListItem ) )->pxContainer ) != 0 )
                                {
                                    pxTaskStatus->eCurrentState = eBlocked;
                                }
                            }
                            ( void ) xTaskResumeAll();
                        }
                    }

            }
        }
        else
        {
            pxTaskStatus->eCurrentState = eTaskGetState( pxTCB );
        }

        /* Obtaining the stack space takes some time, so the xGetFreeStackSpace
         * parameter is provided to allow it to be skipped. */
        if( xGetFreeStackSpace != ( ( char ) 0 ) )
        {





                {
                    pxTaskStatus->usStackHighWaterMark = prvTaskCheckFreeStackSpace( ( uint8_t * ) pxTCB->pxStack );
                }

        }
        else
        {
            pxTaskStatus->usStackHighWaterMark = 0;
        }
    }


/*-----------------------------------------------------------*/



    static UBaseType_t prvListTasksWithinSingleList( TaskStatus_t * pxTaskStatusArray,
                                                     List_t * pxList,
                                                     eTaskState eState )
    {

            /* Reason for rewrite:
            * VeriFast does not support multiple pointer declarations to 
            * user-defined types in single statement 
            * (i.e., `A p1, p2;` is ok, `A *p1, *p2;` fails)
            */
                               TCB_t * pxNextTCB;
                               TCB_t * pxFirstTCB;



        UBaseType_t uxTask = 0;

        if( ( ( pxList )->uxNumberOfItems ) > ( UBaseType_t ) 0 )
        {
            { List_t * pxConstList = ( pxList ); ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext; if( ( void * ) ( pxConstList )->pxIndex == ( void * ) &( ( pxConstList )->xListEnd ) ) { ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext; } ( pxFirstTCB ) = ( pxConstList )->pxIndex->pvOwner; }; /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */

            /* Populate an TaskStatus_t structure within the
             * pxTaskStatusArray array for each task that is referenced from
             * pxList.  See the definition of TaskStatus_t in task.h for the
             * meaning of each TaskStatus_t structure member. */
            do
            {
                { List_t * pxConstList = ( pxList ); ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext; if( ( void * ) ( pxConstList )->pxIndex == ( void * ) &( ( pxConstList )->xListEnd ) ) { ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext; } ( pxNextTCB ) = ( pxConstList )->pxIndex->pvOwner; }; /*lint !e9079 void * is used as this macro is used with timers and co-routines too.  Alignment is known to be fine as the type of the pointer stored and retrieved is the same. */
                vTaskGetInfo( ( TaskHandle_t ) pxNextTCB, &( pxTaskStatusArray[ uxTask ] ), ( ( char ) 1 ), eState );
                uxTask++;
            } while( pxNextTCB != pxFirstTCB );
        }
        else
        {
                                    ;
        }

        return uxTask;
    }


/*-----------------------------------------------------------*/



    static uint32_t prvTaskCheckFreeStackSpace( const uint8_t * pucStackByte )
    {
        uint32_t ulCount = 0U;

        while( *pucStackByte == ( uint8_t ) ( 0xa5U ) )
        {
            pucStackByte -= ( -1 );
            ulCount++;
        }

        ulCount /= ( uint32_t ) sizeof( StackType_t ); /*lint !e961 Casting is not redundant on smaller architectures. */

        return ( uint32_t ) ulCount;
    }


/*-----------------------------------------------------------*/
// # 5168 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/



    UBaseType_t uxTaskGetStackHighWaterMark( TaskHandle_t xTask )
    {
        TCB_t * pxTCB;
        uint8_t * pucEndOfStack;
        UBaseType_t uxReturn;

        pxTCB = ( ( ( xTask ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTask ) );


            {
                pucEndOfStack = ( uint8_t * ) pxTCB->pxStack;
            }






        uxReturn = ( UBaseType_t ) prvTaskCheckFreeStackSpace( pucEndOfStack );

        return uxReturn;
    }


/*-----------------------------------------------------------*/



    static void prvDeleteTCB( TCB_t * pxTCB )
    {
        /* This call is required specifically for the TriCore port.  It must be
         * above the vPortFree() calls.  The call is also used by ports/demos that
         * want to allocate and clean RAM statically. */
        ( void ) pxTCB;

        /* Free up the memory allocated by the scheduler for the task.  It is up
         * to the task to free any memory allocated at the application level.
         * See the third party link http://www.nadler.com/embedded/newlibAndFreeRTOS.html
         * for additional information. */







            {
                /* The task can only have been allocated dynamically - free both
                 * the stack and TCB. */
                free( (void*) pxTCB->pxStack);
                free( (void*) pxTCB);
            }
// # 5251 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
    }


/*-----------------------------------------------------------*/

static void prvResetNextTaskUnblockTime( void )
{
    if( ( ( ( pxDelayedTaskList )->uxNumberOfItems == ( UBaseType_t ) 0 ) ? ( ( char ) 1 ) : ( ( char ) 0 ) ) != ( ( char ) 0 ) )
    {
        /* The new current delayed list is empty.  Set xNextTaskUnblockTime to
         * the maximum possible value so it is  extremely unlikely that the
         * if( xTickCount >= xNextTaskUnblockTime ) test will pass until
         * there is an item in the delayed list. */
        xNextTaskUnblockTime = ( TickType_t ) 0xffffffffUL;
    }
    else
    {
        /* The new current delayed list is not empty, get the value of
         * the item at the head of the delayed list.  This is the time at
         * which the task at the head of the delayed list should be removed
         * from the Blocked state. */
        xNextTaskUnblockTime = ( ( ( pxDelayedTaskList )->xListEnd ).pxNext->xItemValue );
    }
}
/*-----------------------------------------------------------*/



    TaskHandle_t xTaskGetCurrentTaskHandle( void )
    {
        TaskHandle_t xReturn;
        uint32_t ulState;

        ulState = assert_fct(false, "portDISABLE_INTERRUPTS");
        xReturn = pxCurrentTCBs[ 0 ];
        assert_fct(false, "portRESTORE_INTERRUPTS");

        return xReturn;
    }

    TaskHandle_t xTaskGetCurrentTaskHandleCPU( UBaseType_t xCoreID )
    {
        TaskHandle_t xReturn = 0;

        if( ( ( BaseType_t ) ( ( 0 <= xCoreID ) && ( xCoreID < 1 ) ) ) != ( ( char ) 0 ) )
        {
            xReturn = pxCurrentTCBs[ xCoreID ];
        }

        return xReturn;
    }


/*-----------------------------------------------------------*/



    BaseType_t xTaskGetSchedulerState( void )
    {
        BaseType_t xReturn;

        if( xSchedulerRunning == ( ( char ) 0 ) )
        {
            xReturn = ( ( BaseType_t ) 1 );
        }
        else
        {
            vTaskEnterCritical();
            {
                if( uxSchedulerSuspended == ( UBaseType_t ) ( ( char ) 0 ) )
                {
                    xReturn = ( ( BaseType_t ) 2 );
                }
                else
                {
                    xReturn = ( ( BaseType_t ) 0 );
                }
            }
            vTaskExitCritical();
        }

        return xReturn;
    }


/*-----------------------------------------------------------*/



    BaseType_t xTaskPriorityInherit( TaskHandle_t const pxMutexHolder )
    {

            /* Reason for rewrite:
            * VeriFast does not support const pointers.
            */
           TCB_t * pxMutexHolderTCB = pxMutexHolder;



        BaseType_t xReturn = ( ( char ) 0 );

        /* If the mutex was given back by an interrupt while the queue was
         * locked then the mutex holder might now be NULL.  _RB_ Is this still
         * needed as interrupts can no longer use mutexes? */
        if( pxMutexHolder != 0 )
        {
            /* If the holder of the mutex has a priority below the priority of
             * the task attempting to obtain the mutex then it will temporarily
             * inherit the priority of the task attempting to obtain the mutex. */
            if( pxMutexHolderTCB->uxPriority < xTaskGetCurrentTaskHandle()->uxPriority )
            {
                /* Adjust the mutex holder state to account for its new
                 * priority.  Only reset the event list item value if the value is
                 * not being used for anything else. */
                if( ( ( ( &( pxMutexHolderTCB->xEventListItem ) )->xItemValue ) & 0x80000000UL ) == 0UL )
                {
                    ( ( &( pxMutexHolderTCB->xEventListItem ) )->xItemValue = ( ( TickType_t ) 32 - ( TickType_t ) xTaskGetCurrentTaskHandle()->uxPriority ) ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */
                }
                else
                {
                                            ;
                }

                /* If the task being modified is in the ready state it will need
                 * to be moved into a new list. */
                if( ( ( ( &( pxMutexHolderTCB->xStateListItem ) )->pxContainer == ( &( pxReadyTasksLists[ pxMutexHolderTCB->uxPriority ] ) ) ) ? ( ( ( char ) 1 ) ) : ( ( ( char ) 0 ) ) ) != ( ( char ) 0 ) )
                {
                    if( uxListRemove( &( pxMutexHolderTCB->xStateListItem ) ) == ( UBaseType_t ) 0 )
                    {
                        /* It is known that the task is in its ready list so
                         * there is no need to check again and the port level
                         * reset macro can be called directly. */
                                                                                                    ;
                    }
                    else
                    {
                                                ;
                    }

                    /* Inherit the priority before being moved into the new list. */
                    pxMutexHolderTCB->uxPriority = xTaskGetCurrentTaskHandle()->uxPriority;
                    ; { if( ( ( pxMutexHolderTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxMutexHolderTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxMutexHolderTCB )->uxPriority ] ), &( ( pxMutexHolderTCB )->xStateListItem ) ); ;
                }
                else
                {
                    /* Just inherit the priority. */
                    pxMutexHolderTCB->uxPriority = xTaskGetCurrentTaskHandle()->uxPriority;
                }

                                                                                        ;

                /* Inheritance occurred. */
                xReturn = ( ( char ) 1 );
            }
            else
            {
                if( pxMutexHolderTCB->uxBasePriority < xTaskGetCurrentTaskHandle()->uxPriority )
                {
                    /* The base priority of the mutex holder is lower than the
                     * priority of the task attempting to take the mutex, but the
                     * current priority of the mutex holder is not lower than the
                     * priority of the task attempting to take the mutex.
                     * Therefore the mutex holder must have already inherited a
                     * priority, but inheritance would have occurred if that had
                     * not been the case. */
                    xReturn = ( ( char ) 1 );
                }
                else
                {
                                            ;
                }
            }
        }
        else
        {
                                    ;
        }

        return xReturn;
    }


/*-----------------------------------------------------------*/



    BaseType_t xTaskPriorityDisinherit( TaskHandle_t const pxMutexHolder )
    {

            /* Reason for rewrite:
            * VeriFast does not support const pointers.
            */
           TCB_t * pxTCB = pxMutexHolder;



        BaseType_t xReturn = ( ( char ) 0 );

        if( pxMutexHolder != 0 )
        {
            /* A task can only have an inherited priority if it holds the mutex.
             * If the mutex is held by a task then it cannot be given from an
             * interrupt, and if a mutex is given by the holding task then it must
             * be the running state task. */
            assert(pxTCB == xTaskGetCurrentTaskHandle());
            assert(pxTCB->uxMutexesHeld);
            ( pxTCB->uxMutexesHeld )--;

            /* Has the holder of the mutex inherited the priority of another
             * task? */
            if( pxTCB->uxPriority != pxTCB->uxBasePriority )
            {
                /* Only disinherit if no other mutexes are held. */
                if( pxTCB->uxMutexesHeld == ( UBaseType_t ) 0 )
                {
                    /* A task can only have an inherited priority if it holds
                     * the mutex.  If the mutex is held by a task then it cannot be
                     * given from an interrupt, and if a mutex is given by the
                     * holding task then it must be the running state task.  Remove
                     * the holding task from the ready list. */
                    if( uxListRemove( &( pxTCB->xStateListItem ) ) == ( UBaseType_t ) 0 )
                    {
                                                                                         ;
                    }
                    else
                    {
                                                ;
                    }

                    /* Disinherit the priority before adding the task into the
                     * new  ready list. */
                                                                                 ;
                    pxTCB->uxPriority = pxTCB->uxBasePriority;

                    /* Reset the event list item value.  It cannot be in use for
                     * any other purpose if this task is running, and it must be
                     * running to give back the mutex. */
                    ( ( &( pxTCB->xEventListItem ) )->xItemValue = ( ( TickType_t ) 32 - ( TickType_t ) pxTCB->uxPriority ) ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */
                    ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;

                    /* Return true to indicate that a context switch is required.
                     * This is only actually required in the corner case whereby
                     * multiple mutexes were held and the mutexes were given back
                     * in an order different to that in which they were taken.
                     * If a context switch did not occur when the first mutex was
                     * returned, even if a task was waiting on it, then a context
                     * switch should occur when the last mutex is returned whether
                     * a task is waiting on it or not. */
                    xReturn = ( ( char ) 1 );
                }
                else
                {
                                            ;
                }
            }
            else
            {
                                        ;
            }
        }
        else
        {
                                    ;
        }

        return xReturn;
    }


/*-----------------------------------------------------------*/



    void vTaskPriorityDisinheritAfterTimeout( TaskHandle_t const pxMutexHolder,
                                              UBaseType_t uxHighestPriorityWaitingTask )
    {

            /* Reason for rewrite:
            * VeriFast does not support const pointers.
            */
           TCB_t * pxTCB = pxMutexHolder;



        UBaseType_t uxPriorityUsedOnEntry, uxPriorityToUse;
        const UBaseType_t uxOnlyOneMutexHeld = ( UBaseType_t ) 1;

        if( pxMutexHolder != 0 )
        {
            /* If pxMutexHolder is not NULL then the holder must hold at least
             * one mutex. */
            assert(pxTCB->uxMutexesHeld);

            /* Determine the priority to which the priority of the task that
             * holds the mutex should be set.  This will be the greater of the
             * holding task's base priority and the priority of the highest
             * priority task that is waiting to obtain the mutex. */
            if( pxTCB->uxBasePriority < uxHighestPriorityWaitingTask )
            {
                uxPriorityToUse = uxHighestPriorityWaitingTask;
            }
            else
            {
                uxPriorityToUse = pxTCB->uxBasePriority;
            }

            /* Does the priority need to change? */
            if( pxTCB->uxPriority != uxPriorityToUse )
            {
                /* Only disinherit if no other mutexes are held.  This is a
                 * simplification in the priority inheritance implementation.  If
                 * the task that holds the mutex is also holding other mutexes then
                 * the other mutexes may have caused the priority inheritance. */
                if( pxTCB->uxMutexesHeld == uxOnlyOneMutexHeld )
                {
                    /* If a task has timed out because it already holds the
                     * mutex it was trying to obtain then it cannot of inherited
                     * its own priority. */
                    assert(pxTCB != xTaskGetCurrentTaskHandle());

                    /* Disinherit the priority, remembering the previous
                     * priority to facilitate determining the subject task's
                     * state. */
                                                                           ;
                    uxPriorityUsedOnEntry = pxTCB->uxPriority;
                    pxTCB->uxPriority = uxPriorityToUse;

                    /* Only reset the event list item value if the value is not
                     * being used for anything else. */
                    if( ( ( ( &( pxTCB->xEventListItem ) )->xItemValue ) & 0x80000000UL ) == 0UL )
                    {
                        ( ( &( pxTCB->xEventListItem ) )->xItemValue = ( ( TickType_t ) 32 - ( TickType_t ) uxPriorityToUse ) ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */
                    }
                    else
                    {
                                                ;
                    }

                    /* If the running task is not the task that holds the mutex
                     * then the task that holds the mutex could be in either the
                     * Ready, Blocked or Suspended states.  Only remove the task
                     * from its current state list if it is in the Ready state as
                     * the task's priority is going to change and there is one
                     * Ready list per priority. */
                    if( ( ( ( &( pxTCB->xStateListItem ) )->pxContainer == ( &( pxReadyTasksLists[ uxPriorityUsedOnEntry ] ) ) ) ? ( ( ( char ) 1 ) ) : ( ( ( char ) 0 ) ) ) != ( ( char ) 0 ) )
                    {
                        if( uxListRemove( &( pxTCB->xStateListItem ) ) == ( UBaseType_t ) 0 )
                        {
                            /* It is known that the task is in its ready list so
                             * there is no need to check again and the port level
                             * reset macro can be called directly. */
                                                                                             ;
                        }
                        else
                        {
                                                    ;
                        }

                        ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;
                    }
                    else
                    {
                                                ;
                    }
                }
                else
                {
                                            ;
                }
            }
            else
            {
                                        ;
            }
        }
        else
        {
                                    ;
        }
    }


/*-----------------------------------------------------------*/

/*
 * If not in a critical section then yield immediately.
 * Otherwise set xYieldPending to true to wait to
 * yield until exiting the critical section.
 */
void vTaskYieldWithinAPI( void )
{
    if( xTaskGetCurrentTaskHandle()->uxCriticalNesting == 0U )
    {
        vPortYield();
    }
    else
    {
        xYieldPendings[ 0 ] = ( ( char ) 1 );
    }
}
/*-----------------------------------------------------------*/



    void vTaskEnterCritical( void )
    //@ requires false;
    //@ ensures false;
    {
        assert_fct(false, "portDISABLE_INTERRUPTS");

        if( xSchedulerRunning != ( ( char ) 0 ) )
        {
            if( xTaskGetCurrentTaskHandle()->uxCriticalNesting == 0U )
            {
                if( assert_fct(false, "portCHECK_IF_IN_ISR") == ( ( char ) 0 ) )
                {
                    vPortRecursiveLock(1, spin_lock_instance(15), ( ( char ) 1 ));
                }

                vPortRecursiveLock(0, spin_lock_instance(14), ( ( char ) 1 ));
            }

            ( xTaskGetCurrentTaskHandle()->uxCriticalNesting )++;

            /* This should now be interrupt safe. The only time there would be
             * a problem is if this is called before a context switch and
             * vTaskExitCritical() is called after pxCurrentTCB changes. Therefore
             * this should not be used within vTaskSwitchContext(). */

            if( ( uxSchedulerSuspended == 0U ) && ( xTaskGetCurrentTaskHandle()->uxCriticalNesting == 1U ) )
            {
                prvCheckForRunStateChange();
            }
        }
        else
        {
                                    ;
        }
    }


/*-----------------------------------------------------------*/



    void vTaskExitCritical( void )
    {
        if( xSchedulerRunning != ( ( char ) 0 ) )
        {
            /* If pxCurrentTCB->uxCriticalNesting is zero then this function
             * does not match a previous call to vTaskEnterCritical(). */
            assert(xTaskGetCurrentTaskHandle()->uxCriticalNesting > 0U);

            if( xTaskGetCurrentTaskHandle()->uxCriticalNesting > 0U )
            {
                ( xTaskGetCurrentTaskHandle()->uxCriticalNesting )--;

                if( xTaskGetCurrentTaskHandle()->uxCriticalNesting == 0U )
                {
                    vPortRecursiveLock(0, spin_lock_instance(14), ( ( char ) 0 ));

                    if( assert_fct(false, "portCHECK_IF_IN_ISR") == ( ( char ) 0 ) )
                    {
                        vPortRecursiveLock(1, spin_lock_instance(15), ( ( char ) 0 ));
                        vPortEnableInterrupts();

                        /* When a task yields in a critical section it just sets
                         * xYieldPending to true. So now that we have exited the
                         * critical section check if xYieldPending is true, and
                         * if so yield. */
                        if( prvGetCurrentYieldPending() != ( ( char ) 0 ) )
                        {
                            vPortYield();
                        }
                    }
                    else
                    {
                        /* In an ISR we don't hold the task lock and don't
                         * need to yield. Yield will happen if necessary when
                         * the application ISR calls portEND_SWITCHING_ISR() */
                                                ;
                    }
                }
                else
                {
                                            ;
                }
            }
            else
            {
                                        ;
            }
        }
        else
        {
                                    ;
        }
    }


/*-----------------------------------------------------------*/
// # 5778 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/
// # 5884 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*----------------------------------------------------------*/
// # 6011 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/

TickType_t uxTaskResetEventItemValue( void )
{
    TickType_t uxReturn;

    uxReturn = ( ( &( xTaskGetCurrentTaskHandle()->xEventListItem ) )->xItemValue );

    /* Reset the event list item to its normal value - so it can be used with
     * queues and semaphores. */
    ( ( &( xTaskGetCurrentTaskHandle()->xEventListItem ) )->xItemValue = ( ( ( TickType_t ) 32 - ( TickType_t ) xTaskGetCurrentTaskHandle()->uxPriority ) ) ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    return uxReturn;
}
/*-----------------------------------------------------------*/



    TaskHandle_t pvTaskIncrementMutexHeldCount( void )
    {
        /* If xSemaphoreCreateMutex() is called before any tasks have been created
         * then pxCurrentTCB will be NULL. */
        if( xTaskGetCurrentTaskHandle() != 0 )
        {
            ( xTaskGetCurrentTaskHandle()->uxMutexesHeld )++;
        }

        return xTaskGetCurrentTaskHandle();
    }


/*-----------------------------------------------------------*/



    uint32_t ulTaskGenericNotifyTake( UBaseType_t uxIndexToWait,
                                      BaseType_t xClearCountOnExit,
                                      TickType_t xTicksToWait )
    {
        uint32_t ulReturn;

        assert(uxIndexToWait < 1);

        vTaskEnterCritical();
        {
            /* Only block if the notification count is not already non-zero. */
            if( xTaskGetCurrentTaskHandle()->ulNotifiedValue[ uxIndexToWait ] == 0UL )
            {
                /* Mark this task as waiting for a notification. */
                xTaskGetCurrentTaskHandle()->ucNotifyState[ uxIndexToWait ] = ( ( uint8_t ) 1 );

                if( xTicksToWait > ( TickType_t ) 0 )
                {
                    prvAddCurrentTaskToDelayedList( xTicksToWait, ( ( char ) 1 ) );
                                                                ;

                    /* All ports are written to allow a yield in a critical
                     * section (some will yield immediately, others wait until the
                     * critical section exits) - but it is not something that
                     * application code should ever do. */
                    vTaskYieldWithinAPI();
                }
                else
                {
                                            ;
                }
            }
            else
            {
                                        ;
            }
        }
        vTaskExitCritical();

        vTaskEnterCritical();
        {
                                                  ;
            ulReturn = xTaskGetCurrentTaskHandle()->ulNotifiedValue[ uxIndexToWait ];

            if( ulReturn != 0UL )
            {
                if( xClearCountOnExit != ( ( char ) 0 ) )
                {
                    xTaskGetCurrentTaskHandle()->ulNotifiedValue[ uxIndexToWait ] = 0UL;
                }
                else
                {
                    xTaskGetCurrentTaskHandle()->ulNotifiedValue[ uxIndexToWait ] = ulReturn - ( uint32_t ) 1;
                }
            }
            else
            {
                                        ;
            }

            xTaskGetCurrentTaskHandle()->ucNotifyState[ uxIndexToWait ] = ( ( uint8_t ) 0 );
        }
        vTaskExitCritical();

        return ulReturn;
    }


/*-----------------------------------------------------------*/



    BaseType_t xTaskGenericNotifyWait( UBaseType_t uxIndexToWait,
                                       uint32_t ulBitsToClearOnEntry,
                                       uint32_t ulBitsToClearOnExit,
                                       uint32_t * pulNotificationValue,
                                       TickType_t xTicksToWait )
    {
        BaseType_t xReturn;

        assert(uxIndexToWait < 1);

        vTaskEnterCritical();
        {
            /* Only block if a notification is not already pending. */
            if( xTaskGetCurrentTaskHandle()->ucNotifyState[ uxIndexToWait ] != ( ( uint8_t ) 2 ) )
            {
                /* Clear bits in the task's notification value as bits may get
                 * set  by the notifying task or interrupt.  This can be used to
                 * clear the value to zero. */
                xTaskGetCurrentTaskHandle()->ulNotifiedValue[ uxIndexToWait ] &= ~ulBitsToClearOnEntry;

                /* Mark this task as waiting for a notification. */
                xTaskGetCurrentTaskHandle()->ucNotifyState[ uxIndexToWait ] = ( ( uint8_t ) 1 );

                if( xTicksToWait > ( TickType_t ) 0 )
                {
                    prvAddCurrentTaskToDelayedList( xTicksToWait, ( ( char ) 1 ) );
                                                                ;

                    /* All ports are written to allow a yield in a critical
                     * section (some will yield immediately, others wait until the
                     * critical section exits) - but it is not something that
                     * application code should ever do. */
                    vTaskYieldWithinAPI();
                }
                else
                {
                                            ;
                }
            }
            else
            {
                                        ;
            }
        }
        vTaskExitCritical();

        vTaskEnterCritical();
        {
                                                  ;

            if( pulNotificationValue != 0 )
            {
                /* Output the current notification value, which may or may not
                 * have changed. */
                *pulNotificationValue = xTaskGetCurrentTaskHandle()->ulNotifiedValue[ uxIndexToWait ];
            }

            /* If ucNotifyValue is set then either the task never entered the
             * blocked state (because a notification was already pending) or the
             * task unblocked because of a notification.  Otherwise the task
             * unblocked because of a timeout. */
            if( xTaskGetCurrentTaskHandle()->ucNotifyState[ uxIndexToWait ] != ( ( uint8_t ) 2 ) )
            {
                /* A notification was not received. */
                xReturn = ( ( char ) 0 );
            }
            else
            {
                /* A notification was already pending or a notification was
                 * received while the task was waiting. */
                xTaskGetCurrentTaskHandle()->ulNotifiedValue[ uxIndexToWait ] &= ~ulBitsToClearOnExit;
                xReturn = ( ( char ) 1 );
            }

            xTaskGetCurrentTaskHandle()->ucNotifyState[ uxIndexToWait ] = ( ( uint8_t ) 0 );
        }
        vTaskExitCritical();

        return xReturn;
    }


/*-----------------------------------------------------------*/



    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
                                   UBaseType_t uxIndexToNotify,
                                   uint32_t ulValue,
                                   eNotifyAction eAction,
                                   uint32_t * pulPreviousNotificationValue )
    {
        TCB_t * pxTCB;
        BaseType_t xReturn = ( ( ( char ) 1 ) );
        uint8_t ucOriginalNotifyState;

        assert(uxIndexToNotify < 1);
        assert(xTaskToNotify);
        pxTCB = xTaskToNotify;

        vTaskEnterCritical();
        {
            if( pulPreviousNotificationValue != 0 )
            {
                *pulPreviousNotificationValue = pxTCB->ulNotifiedValue[ uxIndexToNotify ];
            }

            ucOriginalNotifyState = pxTCB->ucNotifyState[ uxIndexToNotify ];

            pxTCB->ucNotifyState[ uxIndexToNotify ] = ( ( uint8_t ) 2 );

            switch( eAction )
            {
                case eSetBits:
                    pxTCB->ulNotifiedValue[ uxIndexToNotify ] |= ulValue;
                    break;

                case eIncrement:
                    ( pxTCB->ulNotifiedValue[ uxIndexToNotify ] )++;
                    break;

                case eSetValueWithOverwrite:
                    pxTCB->ulNotifiedValue[ uxIndexToNotify ] = ulValue;
                    break;

                case eSetValueWithoutOverwrite:

                    if( ucOriginalNotifyState != ( ( uint8_t ) 2 ) )
                    {
                        pxTCB->ulNotifiedValue[ uxIndexToNotify ] = ulValue;
                    }
                    else
                    {
                        /* The value could not be written to the task. */
                        xReturn = ( ( ( char ) 0 ) );
                    }

                    break;

                case eNoAction:

                    /* The task is being notified without its notify value being
                     * updated. */
                    break;

                default:

                    /* Should not get here if all enums are handled.
                     * Artificially force an assert by testing a value the
                     * compiler can't assume is const. */
                    assert(xTickCount == ( TickType_t ) 0);

                    break;
            }

                                               ;

            /* If the task is in the blocked state specifically to wait for a
             * notification then unblock it now. */
            if( ucOriginalNotifyState == ( ( uint8_t ) 1 ) )
            {
                ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
                ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;

                /* The task should not have been on an event list. */
                assert(( ( &( pxTCB->xEventListItem ) )->pxContainer ) == 0);
// # 6302 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
                    {
                        prvYieldForTask( pxTCB, ( ( char ) 0 ) );
                    }

            }
            else
            {
                                        ;
            }
        }
        vTaskExitCritical();

        return xReturn;
    }


/*-----------------------------------------------------------*/



    BaseType_t xTaskGenericNotifyFromISR( TaskHandle_t xTaskToNotify,
                                          UBaseType_t uxIndexToNotify,
                                          uint32_t ulValue,
                                          eNotifyAction eAction,
                                          uint32_t * pulPreviousNotificationValue,
                                          BaseType_t * pxHigherPriorityTaskWoken )
    {
        TCB_t * pxTCB;
        uint8_t ucOriginalNotifyState;
        BaseType_t xReturn = ( ( ( char ) 1 ) );
        UBaseType_t uxSavedInterruptStatus;

        assert(xTaskToNotify);
        assert(uxIndexToNotify < 1);

        /* RTOS ports that support interrupt nesting have the concept of a
         * maximum  system call (or maximum API call) interrupt priority.
         * Interrupts that are  above the maximum system call priority are keep
         * permanently enabled, even when the RTOS kernel is in a critical section,
         * but cannot make any calls to FreeRTOS API functions.  If configASSERT()
         * is defined in FreeRTOSConfig.h then
         * portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will result in an assertion
         * failure if a FreeRTOS API function is called from an interrupt that has
         * been assigned a priority above the configured maximum system call
         * priority.  Only FreeRTOS functions that end in FromISR can be called
         * from interrupts  that have been assigned a priority at or (logically)
         * below the maximum system call interrupt priority.  FreeRTOS maintains a
         * separate interrupt safe API to ensure interrupt entry is as fast and as
         * simple as possible.  More information (albeit Cortex-M specific) is
         * provided on the following link:
         * https://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html */
                                                  ;

        pxTCB = xTaskToNotify;

        uxSavedInterruptStatus = assert_fct(false, "portSET_INTERRUPT_MASK_FROM_ISR");
        {
            if( pulPreviousNotificationValue != 0 )
            {
                *pulPreviousNotificationValue = pxTCB->ulNotifiedValue[ uxIndexToNotify ];
            }

            ucOriginalNotifyState = pxTCB->ucNotifyState[ uxIndexToNotify ];
            pxTCB->ucNotifyState[ uxIndexToNotify ] = ( ( uint8_t ) 2 );

            switch( eAction )
            {
                case eSetBits:
                    pxTCB->ulNotifiedValue[ uxIndexToNotify ] |= ulValue;
                    break;

                case eIncrement:
                    ( pxTCB->ulNotifiedValue[ uxIndexToNotify ] )++;
                    break;

                case eSetValueWithOverwrite:
                    pxTCB->ulNotifiedValue[ uxIndexToNotify ] = ulValue;
                    break;

                case eSetValueWithoutOverwrite:

                    if( ucOriginalNotifyState != ( ( uint8_t ) 2 ) )
                    {
                        pxTCB->ulNotifiedValue[ uxIndexToNotify ] = ulValue;
                    }
                    else
                    {
                        /* The value could not be written to the task. */
                        xReturn = ( ( ( char ) 0 ) );
                    }

                    break;

                case eNoAction:

                    /* The task is being notified without its notify value being
                     * updated. */
                    break;

                default:

                    /* Should not get here if all enums are handled.
                     * Artificially force an assert by testing a value the
                     * compiler can't assume is const. */
                    assert(xTickCount == ( TickType_t ) 0);
                    break;
            }

                                                        ;

            /* If the task is in the blocked state specifically to wait for a
             * notification then unblock it now. */
            if( ucOriginalNotifyState == ( ( uint8_t ) 1 ) )
            {
                /* The task should not have been on an event list. */
                assert(( ( &( pxTCB->xEventListItem ) )->pxContainer ) == 0);

                if( uxSchedulerSuspended == ( UBaseType_t ) ( ( char ) 0 ) )
                {
                    ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
                    ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;
                }
                else
                {
                    /* The delayed and ready lists cannot be accessed, so hold
                     * this task pending until the scheduler is resumed. */
                    vListInsertEnd( &( xPendingReadyList ), &( pxTCB->xEventListItem ) );
                }


                    prvYieldForTask( pxTCB, ( ( char ) 0 ) );

                    if( xYieldPendings[ 0 ] == ( ( char ) 1 ) )
                    {
                        if( pxHigherPriorityTaskWoken != 0 )
                        {
                            *pxHigherPriorityTaskWoken = ( ( char ) 1 );
                        }
                    }

            }
        }
        do { vTaskExitCritical(); assert_fct(false, "portRESTORE_INTERRUPTS"); } while (0);

        return xReturn;
    }


/*-----------------------------------------------------------*/



    void vTaskGenericNotifyGiveFromISR( TaskHandle_t xTaskToNotify,
                                        UBaseType_t uxIndexToNotify,
                                        BaseType_t * pxHigherPriorityTaskWoken )
    {
        TCB_t * pxTCB;
        uint8_t ucOriginalNotifyState;
        UBaseType_t uxSavedInterruptStatus;

        assert(xTaskToNotify);
        assert(uxIndexToNotify < 1);

        /* RTOS ports that support interrupt nesting have the concept of a
         * maximum  system call (or maximum API call) interrupt priority.
         * Interrupts that are  above the maximum system call priority are keep
         * permanently enabled, even when the RTOS kernel is in a critical section,
         * but cannot make any calls to FreeRTOS API functions.  If configASSERT()
         * is defined in FreeRTOSConfig.h then
         * portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will result in an assertion
         * failure if a FreeRTOS API function is called from an interrupt that has
         * been assigned a priority above the configured maximum system call
         * priority.  Only FreeRTOS functions that end in FromISR can be called
         * from interrupts  that have been assigned a priority at or (logically)
         * below the maximum system call interrupt priority.  FreeRTOS maintains a
         * separate interrupt safe API to ensure interrupt entry is as fast and as
         * simple as possible.  More information (albeit Cortex-M specific) is
         * provided on the following link:
         * https://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html */
                                                  ;

        pxTCB = xTaskToNotify;

        uxSavedInterruptStatus = assert_fct(false, "portSET_INTERRUPT_MASK_FROM_ISR");
        {
            ucOriginalNotifyState = pxTCB->ucNotifyState[ uxIndexToNotify ];
            pxTCB->ucNotifyState[ uxIndexToNotify ] = ( ( uint8_t ) 2 );

            /* 'Giving' is equivalent to incrementing a count in a counting
             * semaphore. */
            ( pxTCB->ulNotifiedValue[ uxIndexToNotify ] )++;

                                                             ;

            /* If the task is in the blocked state specifically to wait for a
             * notification then unblock it now. */
            if( ucOriginalNotifyState == ( ( uint8_t ) 1 ) )
            {
                /* The task should not have been on an event list. */
                assert(( ( &( pxTCB->xEventListItem ) )->pxContainer ) == 0);

                if( uxSchedulerSuspended == ( UBaseType_t ) ( ( char ) 0 ) )
                {
                    ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
                    ; { if( ( ( pxTCB )->uxPriority ) > uxTopReadyPriority ) { uxTopReadyPriority = ( ( pxTCB )->uxPriority ); } }; vListInsertEnd( &( pxReadyTasksLists[ ( pxTCB )->uxPriority ] ), &( ( pxTCB )->xStateListItem ) ); ;
                }
                else
                {
                    /* The delayed and ready lists cannot be accessed, so hold
                     * this task pending until the scheduler is resumed. */
                    vListInsertEnd( &( xPendingReadyList ), &( pxTCB->xEventListItem ) );
                }


                    prvYieldForTask( pxTCB, ( ( char ) 0 ) );

                    if( xYieldPendings[ 0 ] == ( ( char ) 1 ) )
                    {
                        if( pxHigherPriorityTaskWoken != 0 )
                        {
                            *pxHigherPriorityTaskWoken = ( ( char ) 1 );
                        }
                    }

            }
        }
        do { vTaskExitCritical(); assert_fct(false, "portRESTORE_INTERRUPTS"); } while (0);
    }


/*-----------------------------------------------------------*/



    BaseType_t xTaskGenericNotifyStateClear( TaskHandle_t xTask,
                                             UBaseType_t uxIndexToClear )
    {
        TCB_t * pxTCB;
        BaseType_t xReturn;

        assert(uxIndexToClear < 1);

        /* If null is passed in here then it is the calling task that is having
         * its notification state cleared. */
        pxTCB = ( ( ( xTask ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTask ) );

        vTaskEnterCritical();
        {
            if( pxTCB->ucNotifyState[ uxIndexToClear ] == ( ( uint8_t ) 2 ) )
            {
                pxTCB->ucNotifyState[ uxIndexToClear ] = ( ( uint8_t ) 0 );
                xReturn = ( ( ( char ) 1 ) );
            }
            else
            {
                xReturn = ( ( ( char ) 0 ) );
            }
        }
        vTaskExitCritical();

        return xReturn;
    }


/*-----------------------------------------------------------*/



    uint32_t ulTaskGenericNotifyValueClear( TaskHandle_t xTask,
                                            UBaseType_t uxIndexToClear,
                                            uint32_t ulBitsToClear )
    {
        TCB_t * pxTCB;
        uint32_t ulReturn;

        /* If null is passed in here then it is the calling task that is having
         * its notification state cleared. */
        pxTCB = ( ( ( xTask ) == 0 ) ? xTaskGetCurrentTaskHandle() : ( xTask ) );

        vTaskEnterCritical();
        {
            /* Return the notification as it was before the bits were cleared,
             * then clear the bit mask. */
            ulReturn = pxTCB->ulNotifiedValue[ uxIndexToClear ];
            pxTCB->ulNotifiedValue[ uxIndexToClear ] &= ~ulBitsToClear;
        }
        vTaskExitCritical();

        return ulReturn;
    }


/*-----------------------------------------------------------*/
// # 6611 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
/*-----------------------------------------------------------*/

static void prvAddCurrentTaskToDelayedList( TickType_t xTicksToWait,
                                            const BaseType_t xCanBlockIndefinitely )
{
    TickType_t xTimeToWake;
    const TickType_t xConstTickCount = xTickCount;


        {
            /* About to enter a delayed list, so ensure the ucDelayAborted flag is
             * reset to pdFALSE so it can be detected as having been set to pdTRUE
             * when the task leaves the Blocked state. */
            xTaskGetCurrentTaskHandle()->ucDelayAborted = ( ( char ) 0 );
        }


    /* Remove the task from the ready list before adding it to the blocked list
     * as the same list item is used for both lists. */
    if( uxListRemove( &( xTaskGetCurrentTaskHandle()->xStateListItem ) ) == ( UBaseType_t ) 0 )
    {
        /* The current task must be in a ready list, so there is no need to
         * check, and the port reset macro can be called directly. */
                                                                                ; /*lint !e931 pxCurrentTCB cannot change as it is the calling task.  pxCurrentTCB->uxPriority and uxTopReadyPriority cannot change as called with scheduler suspended or in a critical section. */
    }
    else
    {
                                ;
    }


        {
            if( ( xTicksToWait == ( TickType_t ) 0xffffffffUL ) && ( xCanBlockIndefinitely != ( ( char ) 0 ) ) )
            {
                /* Add the task to the suspended task list instead of a delayed task
                 * list to ensure it is not woken by a timing event.  It will block
                 * indefinitely. */
                vListInsertEnd( &xSuspendedTaskList, &( xTaskGetCurrentTaskHandle()->xStateListItem ) );
            }
            else
            {
                /* Calculate the time at which the task should be woken if the event
                 * does not occur.  This may overflow but this doesn't matter, the
                 * kernel will manage it correctly. */
                xTimeToWake = xConstTickCount + xTicksToWait;

                /* The list item will be inserted in wake time order. */
                ( ( &( xTaskGetCurrentTaskHandle()->xStateListItem ) )->xItemValue = ( xTimeToWake ) );

                if( xTimeToWake < xConstTickCount )
                {
                    /* Wake time has overflowed.  Place this item in the overflow
                     * list. */
                    vListInsert( pxOverflowDelayedTaskList, &( xTaskGetCurrentTaskHandle()->xStateListItem ) );
                }
                else
                {
                    /* The wake time has not overflowed, so the current block list
                     * is used. */
                    vListInsert( pxDelayedTaskList, &( xTaskGetCurrentTaskHandle()->xStateListItem ) );

                    /* If the task entering the blocked state was placed at the
                     * head of the list of blocked tasks then xNextTaskUnblockTime
                     * needs to be updated too. */
                    if( xTimeToWake < xNextTaskUnblockTime )
                    {
                        xNextTaskUnblockTime = xTimeToWake;
                    }
                    else
                    {
                                                ;
                    }
                }
            }
        }
// # 6723 "/Users/reitobia/repos2/FreeRTOS-Kernel/tasks.c"
}

/* Code below here allows additional code to be inserted into this source file,
 * especially where access to file scope functions and data is needed (for example
 * when performing module tests). */
