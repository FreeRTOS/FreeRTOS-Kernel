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
 * @file stream_buffer_ext_utest.c
 * @brief Unit tests for the stream buffer extension API (peek, snapshot).
 */

#include "unity.h"
#include "stream_buffer_ext.h"
#include "FreeRTOS.h"
#include "stream_buffer.h"

#include <string.h>

/* ========================== DEFINES ============================== */

#define TEST_BUFFER_SIZE       ( ( size_t ) 64 )
#define TEST_TRIGGER_LEVEL     ( ( size_t ) 1 )
#define TEST_DATA_SIZE         ( ( size_t ) 16 )

/* ========================== GLOBALS ============================== */

static StreamBufferHandle_t xTestBuffer = NULL;
static uint8_t ucTestData[ TEST_BUFFER_SIZE ];
static uint8_t ucReceiveBuf[ TEST_BUFFER_SIZE ];

/* ======================== Unity Fixtures ========================= */

void setUp( void )
{
    size_t i;

    xTestBuffer = xStreamBufferCreate( TEST_BUFFER_SIZE, TEST_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xTestBuffer );

    for( i = 0; i < TEST_BUFFER_SIZE; i++ )
    {
        ucTestData[ i ] = ( uint8_t ) ( i & 0xFF );
    }

    memset( ucReceiveBuf, 0, sizeof( ucReceiveBuf ) );
}

void tearDown( void )
{
    if( xTestBuffer != NULL )
    {
        vStreamBufferDelete( xTestBuffer );
        xTestBuffer = NULL;
    }
}

/* ========================== TESTS ================================ */

/**
 * @brief Peek returns data without consuming it.
 */
void test_xStreamBufferPeek_DataNotConsumed( void )
{
    size_t xSent;
    size_t xPeeked;
    size_t xAvailable;

    xSent = xStreamBufferSend( xTestBuffer, ucTestData, TEST_DATA_SIZE, 0 );
    TEST_ASSERT_EQUAL( TEST_DATA_SIZE, xSent );

    xPeeked = xStreamBufferPeek( xTestBuffer, ucReceiveBuf, TEST_DATA_SIZE );
    TEST_ASSERT_EQUAL( TEST_DATA_SIZE, xPeeked );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( ucTestData, ucReceiveBuf, TEST_DATA_SIZE );

    /* Verify data is still in the buffer. */
    xAvailable = xStreamBufferBytesAvailable( xTestBuffer );
    TEST_ASSERT_EQUAL( TEST_DATA_SIZE, xAvailable );
}

/**
 * @brief Peek on empty buffer returns 0.
 */
void test_xStreamBufferPeek_EmptyBuffer( void )
{
    size_t xPeeked;

    xPeeked = xStreamBufferPeek( xTestBuffer, ucReceiveBuf, TEST_DATA_SIZE );
    TEST_ASSERT_EQUAL( 0, xPeeked );
}

/**
 * @brief Peek with request larger than available returns only available.
 */
void test_xStreamBufferPeek_RequestMoreThanAvailable( void )
{
    size_t xSent;
    size_t xPeeked;

    xSent = xStreamBufferSend( xTestBuffer, ucTestData, 4, 0 );
    TEST_ASSERT_EQUAL( 4, xSent );

    xPeeked = xStreamBufferPeek( xTestBuffer, ucReceiveBuf, TEST_BUFFER_SIZE );
    TEST_ASSERT_EQUAL( 4, xPeeked );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( ucTestData, ucReceiveBuf, 4 );
}

/**
 * @brief Peek with zero length returns 0.
 */
void test_xStreamBufferPeek_ZeroLength( void )
{
    size_t xPeeked;

    xStreamBufferSend( xTestBuffer, ucTestData, TEST_DATA_SIZE, 0 );
    xPeeked = xStreamBufferPeek( xTestBuffer, ucReceiveBuf, 0 );
    TEST_ASSERT_EQUAL( 0, xPeeked );
}

/**
 * @brief Multiple peeks return the same data.
 */
void test_xStreamBufferPeek_MultiplePeeksConsistent( void )
{
    uint8_t ucBuf1[ TEST_DATA_SIZE ];
    uint8_t ucBuf2[ TEST_DATA_SIZE ];
    size_t xPeeked1, xPeeked2;

    xStreamBufferSend( xTestBuffer, ucTestData, TEST_DATA_SIZE, 0 );

    xPeeked1 = xStreamBufferPeek( xTestBuffer, ucBuf1, TEST_DATA_SIZE );
    xPeeked2 = xStreamBufferPeek( xTestBuffer, ucBuf2, TEST_DATA_SIZE );

    TEST_ASSERT_EQUAL( xPeeked1, xPeeked2 );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( ucBuf1, ucBuf2, xPeeked1 );
}

/**
 * @brief PeekAt with offset skips initial bytes.
 */
void test_xStreamBufferPeekAt_WithOffset( void )
{
    size_t xSent;
    size_t xPeeked;

    xSent = xStreamBufferSend( xTestBuffer, ucTestData, TEST_DATA_SIZE, 0 );
    TEST_ASSERT_EQUAL( TEST_DATA_SIZE, xSent );

    /* Peek starting at offset 4 — should get bytes 4..15. */
    xPeeked = xStreamBufferPeekAt( xTestBuffer, 4, ucReceiveBuf, TEST_DATA_SIZE );
    TEST_ASSERT_EQUAL( TEST_DATA_SIZE - 4, xPeeked );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( &ucTestData[ 4 ], ucReceiveBuf, xPeeked );
}

/**
 * @brief PeekAt with offset >= available returns 0.
 */
void test_xStreamBufferPeekAt_OffsetBeyondAvailable( void )
{
    size_t xPeeked;

    xStreamBufferSend( xTestBuffer, ucTestData, 4, 0 );

    xPeeked = xStreamBufferPeekAt( xTestBuffer, 10, ucReceiveBuf, TEST_DATA_SIZE );
    TEST_ASSERT_EQUAL( 0, xPeeked );
}

/**
 * @brief PeekAt with zero offset behaves like Peek.
 */
void test_xStreamBufferPeekAt_ZeroOffsetLikePeek( void )
{
    uint8_t ucBufPeek[ TEST_DATA_SIZE ];
    uint8_t ucBufPeekAt[ TEST_DATA_SIZE ];
    size_t xPeekResult, xPeekAtResult;

    xStreamBufferSend( xTestBuffer, ucTestData, TEST_DATA_SIZE, 0 );

    xPeekResult = xStreamBufferPeek( xTestBuffer, ucBufPeek, TEST_DATA_SIZE );
    xPeekAtResult = xStreamBufferPeekAt( xTestBuffer, 0, ucBufPeekAt, TEST_DATA_SIZE );

    TEST_ASSERT_EQUAL( xPeekResult, xPeekAtResult );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( ucBufPeek, ucBufPeekAt, xPeekResult );
}

/**
 * @brief Snapshot captures correct state for empty buffer.
 */
void test_xStreamBufferSnapshot_EmptyBuffer( void )
{
    StreamBufferSnapshot_t xSnap;
    BaseType_t xResult;

    xResult = xStreamBufferSnapshot( xTestBuffer, &xSnap );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( 0, xSnap.xReadableBytes );
    TEST_ASSERT_EQUAL( 1, xSnap.ucIsEmpty );
    TEST_ASSERT_EQUAL( 0, xSnap.ucIsFull );
    TEST_ASSERT_TRUE( xSnap.xWritableBytes > 0 );
}

/**
 * @brief Snapshot captures correct state for partially filled buffer.
 */
void test_xStreamBufferSnapshot_PartiallyFilled( void )
{
    StreamBufferSnapshot_t xSnap;

    xStreamBufferSend( xTestBuffer, ucTestData, 10, 0 );

    xStreamBufferSnapshot( xTestBuffer, &xSnap );
    TEST_ASSERT_EQUAL( 10, xSnap.xReadableBytes );
    TEST_ASSERT_EQUAL( 0, xSnap.ucIsEmpty );
    TEST_ASSERT_EQUAL( 0, xSnap.ucIsFull );
}

/**
 * @brief Snapshot captures full buffer correctly.
 */
void test_xStreamBufferSnapshot_FullBuffer( void )
{
    StreamBufferSnapshot_t xSnap;
    size_t xCapacity;

    /* Fill the buffer to capacity. */
    xCapacity = xStreamBufferSpacesAvailable( xTestBuffer );
    xStreamBufferSend( xTestBuffer, ucTestData, xCapacity, 0 );

    xStreamBufferSnapshot( xTestBuffer, &xSnap );
    TEST_ASSERT_EQUAL( 1, xSnap.ucIsFull );
    TEST_ASSERT_EQUAL( 0, xSnap.ucIsEmpty );
    TEST_ASSERT_EQUAL( 0, xSnap.xWritableBytes );
}

/**
 * @brief Snapshot with NULL parameters returns pdFALSE.
 */
void test_xStreamBufferSnapshot_NullParams( void )
{
    StreamBufferSnapshot_t xSnap;

    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferSnapshot( NULL, &xSnap ) );
    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferSnapshot( xTestBuffer, NULL ) );
}

/**
 * @brief GetReadableLength returns correct count.
 */
void test_xStreamBufferGetReadableLength( void )
{
    size_t xLen;

    xLen = xStreamBufferGetReadableLength( xTestBuffer );
    TEST_ASSERT_EQUAL( 0, xLen );

    xStreamBufferSend( xTestBuffer, ucTestData, 8, 0 );
    xLen = xStreamBufferGetReadableLength( xTestBuffer );
    TEST_ASSERT_EQUAL( 8, xLen );
}

/**
 * @brief GetReadableLength with NULL returns 0.
 */
void test_xStreamBufferGetReadableLength_Null( void )
{
    TEST_ASSERT_EQUAL( 0, xStreamBufferGetReadableLength( NULL ) );
}

/**
 * @brief Peek followed by receive gets the same data.
 */
void test_xStreamBufferPeek_ThenReceive_SameData( void )
{
    uint8_t ucPeekBuf[ TEST_DATA_SIZE ];
    uint8_t ucRecvBuf[ TEST_DATA_SIZE ];
    size_t xPeeked, xReceived;

    xStreamBufferSend( xTestBuffer, ucTestData, TEST_DATA_SIZE, 0 );

    xPeeked = xStreamBufferPeek( xTestBuffer, ucPeekBuf, TEST_DATA_SIZE );
    xReceived = xStreamBufferReceive( xTestBuffer, ucRecvBuf, TEST_DATA_SIZE, 0 );

    TEST_ASSERT_EQUAL( xPeeked, xReceived );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( ucPeekBuf, ucRecvBuf, xPeeked );

    /* Buffer should now be empty. */
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xTestBuffer ) );
}

/**
 * @brief Peek single byte from the buffer.
 */
void test_xStreamBufferPeek_SingleByte( void )
{
    uint8_t ucByte = 0;

    xStreamBufferSend( xTestBuffer, ucTestData, TEST_DATA_SIZE, 0 );

    TEST_ASSERT_EQUAL( 1, xStreamBufferPeek( xTestBuffer, &ucByte, 1 ) );
    TEST_ASSERT_EQUAL( ucTestData[ 0 ], ucByte );
}
