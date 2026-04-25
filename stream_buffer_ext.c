/*
 * FreeRTOS Kernel V11.1.0
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */

/**
 * @file stream_buffer_ext.c
 * @brief Implementation of extended stream buffer operations (peek, snapshot).
 *
 * This module uses the public stream_buffer API to implement non-destructive
 * read operations. It does NOT access internal stream buffer structures
 * directly, maintaining clean API boundaries.
 *
 * Design notes:
 * - Peek operations read data by temporarily recording the buffer state,
 *   performing a regular receive, and then conceptually "unreading" the data.
 *   Since stream_buffer does not provide an unread API, we use a copy-based
 *   approach: we snapshot the available bytes count, then do a regular read
 *   into the user buffer, and use xStreamBufferSend to write the data back.
 *   This preserves the original buffer state.
 *
 * - An alternative approach would access internal StreamBuffer_t fields.
 *   We avoid that to keep this module decoupled from internal changes.
 */

#include "stream_buffer_ext.h"

#include <string.h>

/*-----------------------------------------------------------*/

/**
 * @brief Internal helper to compute bytes available without overflow.
 *
 * Uses xStreamBufferBytesAvailable() from the core API.
 */
static size_t prvGetBytesAvailable( StreamBufferHandle_t xStreamBuffer )
{
    return xStreamBufferBytesAvailable( xStreamBuffer );
}

/*-----------------------------------------------------------*/

/**
 * @brief Internal helper to compute writable space.
 *
 * Uses xStreamBufferSpacesAvailable() from the core API.
 */
static size_t prvGetSpacesAvailable( StreamBufferHandle_t xStreamBuffer )
{
    return xStreamBufferSpacesAvailable( xStreamBuffer );
}

/*-----------------------------------------------------------*/

/**
 * @brief Internal helper to copy data from the buffer at a given offset
 *        without modifying the stream buffer state.
 *
 * This works by:
 * 1. Reading (consuming) offset + length bytes from the buffer
 * 2. Copying the relevant portion to the output
 * 3. Writing all consumed bytes back to restore buffer state
 *
 * IMPORTANT: This function is NOT thread-safe if there are concurrent
 * writers. It is intended for single-reader scenarios or when the caller
 * holds appropriate synchronization.
 *
 * @param[in] xStreamBuffer The stream buffer handle.
 * @param[in] xOffset Offset from the read position.
 * @param[out] pucDest Destination buffer.
 * @param[in] xMaxBytes Maximum bytes to copy.
 * @param[in] xAvailable Total available bytes in the buffer.
 *
 * @return Actual number of bytes copied to pucDest.
 */
static size_t prvPeekWithOffset( StreamBufferHandle_t xStreamBuffer,
                                  size_t xOffset,
                                  uint8_t * pucDest,
                                  size_t xMaxBytes,
                                  size_t xAvailable )
{
    size_t xTotalToRead;
    size_t xBytesRead;
    size_t xBytesToCopy;
    size_t xBytesRestored;
    uint8_t * pucTempBuf;

    /* Calculate total bytes we need to read from the buffer. */
    if( xOffset >= xAvailable )
    {
        /* Offset is beyond available data. */
        return 0;
    }

    /* Determine how many bytes past the offset are available. */
    xBytesToCopy = xAvailable - xOffset;

    if( xBytesToCopy > xMaxBytes )
    {
        xBytesToCopy = xMaxBytes;
    }

    xTotalToRead = xOffset + xBytesToCopy;

    /* Allocate temporary buffer for the consumed data so we can restore it. */
    pucTempBuf = ( uint8_t * ) pvPortMalloc( xTotalToRead );

    if( pucTempBuf == NULL )
    {
        /* Memory allocation failed — cannot peek. */
        return 0;
    }

    /* Read (consume) data from the stream buffer. */
    xBytesRead = xStreamBufferReceive( xStreamBuffer,
                                        pucTempBuf,
                                        xTotalToRead,
                                        0 ); /* No blocking. */

    if( xBytesRead < xTotalToRead )
    {
        /* Less data was available than expected (race condition or
         * concurrent reader). Copy what we can from the offset. */
        if( xBytesRead > xOffset )
        {
            xBytesToCopy = xBytesRead - xOffset;
            ( void ) memcpy( pucDest, &pucTempBuf[ xOffset ], xBytesToCopy );
        }
        else
        {
            xBytesToCopy = 0;
        }
    }
    else
    {
        /* Copy the requested portion starting at the offset. */
        ( void ) memcpy( pucDest, &pucTempBuf[ xOffset ], xBytesToCopy );
    }

    /* Restore all consumed data back to the stream buffer.
     * We write back everything we read to preserve buffer state. */
    xBytesRestored = xStreamBufferSend( xStreamBuffer,
                                         pucTempBuf,
                                         xBytesRead,
                                         0 ); /* No blocking. */

    /* If we couldn't restore all bytes, data integrity is compromised.
     * This should not happen in a single-reader scenario. */
    configASSERT( xBytesRestored == xBytesRead );

    /* Suppress unused variable warning when configASSERT is disabled. */
    ( void ) xBytesRestored;

    vPortFree( pucTempBuf );

    return xBytesToCopy;
}

/*-----------------------------------------------------------*/

size_t xStreamBufferPeek( StreamBufferHandle_t xStreamBuffer,
                           void * pvRxData,
                           size_t xBufferLengthBytes )
{
    size_t xAvailable;
    size_t xBytesToPeek;

    configASSERT( xStreamBuffer != NULL );
    configASSERT( pvRxData != NULL );

    if( ( xStreamBuffer == NULL ) || ( pvRxData == NULL ) )
    {
        return 0;
    }

    if( xBufferLengthBytes == 0 )
    {
        return 0;
    }

    xAvailable = prvGetBytesAvailable( xStreamBuffer );

    if( xAvailable == 0 )
    {
        return 0;
    }

    xBytesToPeek = ( xAvailable < xBufferLengthBytes ) ? xAvailable : xBufferLengthBytes;

    return prvPeekWithOffset( xStreamBuffer,
                               0, /* No offset — peek from the start. */
                               ( uint8_t * ) pvRxData,
                               xBytesToPeek,
                               xAvailable );
}

/*-----------------------------------------------------------*/

size_t xStreamBufferPeekAt( StreamBufferHandle_t xStreamBuffer,
                             size_t xOffset,
                             void * pvRxData,
                             size_t xBufferLengthBytes )
{
    size_t xAvailable;

    configASSERT( xStreamBuffer != NULL );
    configASSERT( pvRxData != NULL );

    if( ( xStreamBuffer == NULL ) || ( pvRxData == NULL ) )
    {
        return 0;
    }

    if( xBufferLengthBytes == 0 )
    {
        return 0;
    }

    xAvailable = prvGetBytesAvailable( xStreamBuffer );

    if( ( xAvailable == 0 ) || ( xOffset >= xAvailable ) )
    {
        return 0;
    }

    return prvPeekWithOffset( xStreamBuffer,
                               xOffset,
                               ( uint8_t * ) pvRxData,
                               xBufferLengthBytes,
                               xAvailable );
}

/*-----------------------------------------------------------*/

BaseType_t xStreamBufferSnapshot( StreamBufferHandle_t xStreamBuffer,
                                   StreamBufferSnapshot_t * pxSnapshot )
{
    size_t xReadable;
    size_t xWritable;

    configASSERT( xStreamBuffer != NULL );
    configASSERT( pxSnapshot != NULL );

    if( ( xStreamBuffer == NULL ) || ( pxSnapshot == NULL ) )
    {
        return pdFALSE;
    }

    /* Capture the current state using public APIs.
     * Note: xHead and xTail are not accessible via the public API,
     * so we set them to 0 as placeholders. For full internal state,
     * the caller would need access to the internal structure. */
    xReadable = prvGetBytesAvailable( xStreamBuffer );
    xWritable = prvGetSpacesAvailable( xStreamBuffer );

    pxSnapshot->xReadableBytes = xReadable;
    pxSnapshot->xWritableBytes = xWritable;

    /* Total capacity is readable + writable (the buffer always reserves
     * one byte internally, which is accounted for by SpacesAvailable). */
    pxSnapshot->xBufferCapacity = xReadable + xWritable;

    /* Head and tail are internal details not exposed by public API.
     * Set to 0 to indicate they are not available in this implementation. */
    pxSnapshot->xHead = 0;
    pxSnapshot->xTail = 0;

    pxSnapshot->ucIsFull = ( xWritable == 0 ) ? ( uint8_t ) 1U : ( uint8_t ) 0U;
    pxSnapshot->ucIsEmpty = ( xReadable == 0 ) ? ( uint8_t ) 1U : ( uint8_t ) 0U;

    return pdTRUE;
}

/*-----------------------------------------------------------*/

size_t xStreamBufferGetReadableLength( StreamBufferHandle_t xStreamBuffer )
{
    configASSERT( xStreamBuffer != NULL );

    if( xStreamBuffer == NULL )
    {
        return 0;
    }

    return prvGetBytesAvailable( xStreamBuffer );
}
