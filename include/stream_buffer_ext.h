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
 * @file stream_buffer_ext.h
 * @brief Extended stream buffer operations: peek, snapshot, and inspection
 *        without consuming data from the buffer.
 *
 * These functions are designed to work alongside the core stream_buffer API
 * and provide read-only inspection capabilities.
 */

#ifndef STREAM_BUFFER_EXT_H
#define STREAM_BUFFER_EXT_H

#include "FreeRTOS.h"
#include "stream_buffer.h"

#if defined( __cplusplus )
    extern "C" {
#endif

/**
 * @brief Opaque snapshot of stream buffer state at a point in time.
 */
typedef struct StreamBufferSnapshot
{
    size_t xReadableBytes;     /**< Number of bytes available to read. */
    size_t xWritableBytes;     /**< Number of bytes available to write. */
    size_t xBufferCapacity;    /**< Total capacity of the buffer. */
    size_t xHead;              /**< Write index at snapshot time. */
    size_t xTail;              /**< Read index at snapshot time. */
    uint8_t ucIsFull;          /**< 1 if buffer was full at snapshot time. */
    uint8_t ucIsEmpty;         /**< 1 if buffer was empty at snapshot time. */
} StreamBufferSnapshot_t;

/**
 * @brief Peek at data in the stream buffer without consuming it.
 *
 * Copies up to xBufferLengthBytes from the stream buffer into pvRxData
 * without advancing the read pointer. The data remains in the buffer
 * for subsequent peek or receive operations.
 *
 * @param[in] xStreamBuffer The handle of the stream buffer.
 * @param[out] pvRxData Pointer to the buffer into which data is copied.
 * @param[in] xBufferLengthBytes Maximum number of bytes to peek.
 *
 * @return The number of bytes actually copied into pvRxData.
 */
size_t xStreamBufferPeek( StreamBufferHandle_t xStreamBuffer,
                           void * pvRxData,
                           size_t xBufferLengthBytes );

/**
 * @brief Peek at data starting from a specific offset within the buffer.
 *
 * Similar to xStreamBufferPeek(), but starts reading from xOffset bytes
 * past the current read pointer. Useful for inspecting data deeper in
 * the buffer without reading preceding bytes.
 *
 * @param[in] xStreamBuffer The handle of the stream buffer.
 * @param[in] xOffset Byte offset from the current read position.
 * @param[out] pvRxData Buffer to copy data into.
 * @param[in] xBufferLengthBytes Maximum bytes to copy.
 *
 * @return The number of bytes actually copied. Returns 0 if xOffset
 *         exceeds the available data.
 */
size_t xStreamBufferPeekAt( StreamBufferHandle_t xStreamBuffer,
                             size_t xOffset,
                             void * pvRxData,
                             size_t xBufferLengthBytes );

/**
 * @brief Take a consistent snapshot of the stream buffer's current state.
 *
 * Captures readable/writable byte counts, head/tail positions, and
 * full/empty status atomically (with respect to single-reader/writer).
 *
 * @param[in] xStreamBuffer The handle of the stream buffer.
 * @param[out] pxSnapshot Pointer to the snapshot structure to fill.
 *
 * @return pdTRUE if the snapshot was taken successfully, pdFALSE if
 *         any parameter is NULL.
 */
BaseType_t xStreamBufferSnapshot( StreamBufferHandle_t xStreamBuffer,
                                   StreamBufferSnapshot_t * pxSnapshot );

/**
 * @brief Get the number of bytes available to read without consuming them.
 *
 * This is equivalent to xStreamBufferBytesAvailable() but implemented
 * in the extension module for consistency.
 *
 * @param[in] xStreamBuffer The handle of the stream buffer.
 *
 * @return The number of readable bytes in the buffer.
 */
size_t xStreamBufferGetReadableLength( StreamBufferHandle_t xStreamBuffer );

#if defined( __cplusplus )
    }
#endif

#endif /* STREAM_BUFFER_EXT_H */
