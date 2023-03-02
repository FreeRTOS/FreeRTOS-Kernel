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

#ifndef INC_PICOLIBC_FREERTOS_H
#define INC_PICOLIBC_FREERTOS_H

/* Use picolibc TLS support to allocate space for __thread variables,
 * initialize them at thread creation and set the TLS context at
 * thread switch time.
 *
 * See the picolibc TLS docs:
 * https://github.com/picolibc/picolibc/blob/main/doc/tls.md
 * for additional information. */

#include <picotls.h>

#define configUSE_C_RUNTIME_TLS_SUPPORT    1

#define configTLS_BLOCK_TYPE               void *

/* Allocate thread local storage block off the end of the
* stack. The _tls_size() function returns the size (in
* bytes) of the total TLS area used by the application */
#if ( portSTACK_GROWTH < 0 )
    #define configINIT_TLS_BLOCK( xTLSBlock, pxTopOfStack )                                            \
    do {                                                                                               \
        pxTopOfStack = ( StackType_t * ) ( ( ( portPOINTER_SIZE_TYPE ) pxTopOfStack ) - _tls_size() ); \
        xTLSBlock = pxTopOfStack;                                                                      \
        _init_tls( xTLSBlock );                                                                        \
    } while( 0 )
#else /* portSTACK_GROWTH */
    #define configINIT_TLS_BLOCK( xTLSBlock, pxTopOfStack )                                            \
    do {                                                                                               \
        xTLSBlock = pxTopOfStack;                                                                      \
        pxTopOfStack = ( StackType_t * ) ( ( ( portPOINTER_SIZE_TYPE ) pxTopOfStack ) + _tls_size() ); \
        _init_tls( xTLSBlock );                                                                        \
    } while( 0 )
#endif /* portSTACK_GROWTH */

#define configSET_TLS_BLOCK( xTLSBlock )    _set_tls( xTLSBlock )

#define configDEINIT_TLS_BLOCK( xTLSBlock )

#endif /* INC_PICOLIBC_FREERTOS_H */
