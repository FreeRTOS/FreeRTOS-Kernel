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

/*
 * Blocking buffers are used to send a continuous blocking of data from one task or
 * interrupt to another.  Their implementation is light weight, making them
 * particularly suited for interrupt to task and core to core communication
 * scenarios.
 *
 * ***NOTE***:  Uniquely among FreeRTOS objects, the blocking buffer
 * implementation (so also the message buffer implementation, as message buffers
 * are built on top of blocking buffers) assumes there is only one task or
 * interrupt that will write to the buffer (the writer), and only one task or
 * interrupt that will read from the buffer (the reader).  It is safe for the
 * writer and reader to be different tasks or interrupts, but, unlike other
 * FreeRTOS objects, it is not safe to have multiple different writers or
 * multiple different readers.  If there are to be multiple different writers
 * then the application writer must place each call to a writing API function
 * (such as xBlockingBufferSend()) inside a critical section and set the send
 * block time to 0.  Likewise, if there are to be multiple different readers
 * then the application writer must place each call to a reading API function
 * (such as xBlockingBufferReceive()) inside a critical section section and set the
 * receive block time to 0.
 *
 */

#ifndef BLOCKING_BUFFER_H
#define BLOCKING_BUFFER_H

#ifndef INC_FREERTOS_H
    #error "include FreeRTOS.h must appear in source files before include blocking_buffer.h"
#endif

/* *INDENT-OFF* */
#if defined( __cplusplus )
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * Type by which blocking buffers are referenced.  For example, a call to
 * xBlockingBufferCreate() returns an BlockingBufferHandle_t variable that can
 * then be used as a parameter to xBlockingBufferSend(), xBlockingBufferReceive(),
 * etc.
 */
struct BlockingBufferDef_t;
typedef struct BlockingBufferDef_t * BlockingBufferHandle_t;

/**
 *  Type used as a blocking buffer's optional callback.
 */
typedef void (* BlockingBufferCallbackFunction_t)( BlockingBufferHandle_t xBlockingBuffer,
                                                   BaseType_t xIsInsideISR,
                                                   BaseType_t * const pxHigherPriorityTaskWoken );

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BlockingBufferHandle_t xBlockingBufferCreate( size_t xBufferSizeBytes, size_t xTriggerLevelBytes );
 * @endcode
 *
 * Creates a new blocking buffer using dynamically allocated memory.  See
 * xBlockingBufferCreateStatic() for a version that uses statically allocated
 * memory (memory that is allocated at compile time).
 *
 * configSUPPORT_DYNAMIC_ALLOCATION must be set to 1 or left undefined in
 * FreeRTOSConfig.h for xBlockingBufferCreate() to be available.
 *
 * @param xBufferSizeBytes The total number of bytes the blocking buffer will be
 * able to hold at any one time.
 *
 * @param xTriggerLevelBytes The number of bytes that must be in the blocking
 * buffer before a task that is blocked on the blocking buffer to wait for data is
 * moved out of the blocked state.  For example, if a task is blocked on a read
 * of an empty blocking buffer that has a trigger level of 1 then the task will be
 * unblocked when a single byte is written to the buffer or the task's block
 * time expires.  As another example, if a task is blocked on a read of an empty
 * blocking buffer that has a trigger level of 10 then the task will not be
 * unblocked until the blocking buffer contains at least 10 bytes or the task's
 * block time expires.  If a reading task's block time expires before the
 * trigger level is reached then the task will still receive however many bytes
 * are actually available.  Setting a trigger level of 0 will result in a
 * trigger level of 1 being used.  It is not valid to specify a trigger level
 * that is greater than the buffer size.
 *
 * @param pxSendCompletedCallback Callback invoked when number of bytes at least equal to
 * trigger level is sent to the blocking buffer. If the parameter is NULL, it will use the default
 * implementation provided by sbSEND_COMPLETED macro. To enable the callback,
 * configUSE_SB_COMPLETED_CALLBACK must be set to 1 in FreeRTOSConfig.h.
 *
 * @param pxReceiveCompletedCallback Callback invoked when more than zero bytes are read from a
 * blocking buffer. If the parameter is NULL, it will use the default
 * implementation provided by sbRECEIVE_COMPLETED macro. To enable the callback,
 * configUSE_SB_COMPLETED_CALLBACK must be set to 1 in FreeRTOSConfig.h.
 *
 * @return If NULL is returned, then the blocking buffer cannot be created
 * because there is insufficient heap memory available for FreeRTOS to allocate
 * the blocking buffer data structures and storage area.  A non-NULL value being
 * returned indicates that the blocking buffer has been created successfully -
 * the returned value should be stored as the handle to the created blocking
 * buffer.
 *
 * Example use:
 * @code{c}
 *
 * void vAFunction( void )
 * {
 * BlockingBufferHandle_t xBlockingBuffer;
 * const size_t xBlockingBufferSizeBytes = 100, xTriggerLevel = 10;
 *
 *  // Create a blocking buffer that can hold 100 bytes.  The memory used to hold
 *  // both the blocking buffer structure and the data in the blocking buffer is
 *  // allocated dynamically.
 *  xBlockingBuffer = xBlockingBufferCreate( xBlockingBufferSizeBytes, xTriggerLevel );
 *
 *  if( xBlockingBuffer == NULL )
 *  {
 *      // There was not enough heap memory space available to create the
 *      // blocking buffer.
 *  }
 *  else
 *  {
 *      // The blocking buffer was created successfully and can now be used.
 *  }
 * }
 * @endcode
 * \defgroup xBlockingBufferCreate xBlockingBufferCreate
 * \ingroup BlockingBufferManagement
 */

#define xBlockingBufferCreate( xBufferSizeBytes, xTriggerLevelBytes ) \
    xBlockingBufferGenericCreate( ( xBufferSizeBytes ), ( xTriggerLevelBytes ), pdFALSE, pdTRUE, NULL, NULL )

#if ( configUSE_SB_COMPLETED_CALLBACK == 1 )
    #define xBlockingBufferCreateWithCallback( xBufferSizeBytes, xTriggerLevelBytes, pxSendCompletedCallback, pxReceiveCompletedCallback ) \
    xBlockingBufferGenericCreate( ( xBufferSizeBytes ), ( xTriggerLevelBytes ), pdFALSE, ( pxSendCompletedCallback ), ( pxReceiveCompletedCallback ) )
#endif

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BlockingBufferHandle_t xBlockingBufferCreateStatic( size_t xBufferSizeBytes,
 *                                              size_t xTriggerLevelBytes,
 *                                              uint8_t *pucBlockingBufferStorageArea,
 *                                              StaticBlockingBuffer_t *pxStaticBlockingBuffer );
 * @endcode
 * Creates a new blocking buffer using statically allocated memory.  See
 * xBlockingBufferCreate() for a version that uses dynamically allocated memory.
 *
 * configSUPPORT_STATIC_ALLOCATION must be set to 1 in FreeRTOSConfig.h for
 * xBlockingBufferCreateStatic() to be available.
 *
 * @param xBufferSizeBytes The size, in bytes, of the buffer pointed to by the
 * pucBlockingBufferStorageArea parameter.
 *
 * @param xTriggerLevelBytes The number of bytes that must be in the blocking
 * buffer before a task that is blocked on the blocking buffer to wait for data is
 * moved out of the blocked state.  For example, if a task is blocked on a read
 * of an empty blocking buffer that has a trigger level of 1 then the task will be
 * unblocked when a single byte is written to the buffer or the task's block
 * time expires.  As another example, if a task is blocked on a read of an empty
 * blocking buffer that has a trigger level of 10 then the task will not be
 * unblocked until the blocking buffer contains at least 10 bytes or the task's
 * block time expires.  If a reading task's block time expires before the
 * trigger level is reached then the task will still receive however many bytes
 * are actually available.  Setting a trigger level of 0 will result in a
 * trigger level of 1 being used.  It is not valid to specify a trigger level
 * that is greater than the buffer size.
 *
 * @param pucBlockingBufferStorageArea Must point to a uint8_t array that is at
 * least xBufferSizeBytes big.  This is the array to which blockings are
 * copied when they are written to the blocking buffer.
 *
 * @param pxStaticBlockingBuffer Must point to a variable of type
 * StaticBlockingBuffer_t, which will be used to hold the blocking buffer's data
 * structure.
 *
 * @param pxSendCompletedCallback Callback invoked when number of bytes at least equal to
 * trigger level is sent to the blocking buffer. If the parameter is NULL, it will use the default
 * implementation provided by sbSEND_COMPLETED macro. To enable the callback,
 * configUSE_SB_COMPLETED_CALLBACK must be set to 1 in FreeRTOSConfig.h.
 *
 * @param pxReceiveCompletedCallback Callback invoked when more than zero bytes are read from a
 * blocking buffer. If the parameter is NULL, it will use the default
 * implementation provided by sbRECEIVE_COMPLETED macro. To enable the callback,
 * configUSE_SB_COMPLETED_CALLBACK must be set to 1 in FreeRTOSConfig.h.
 *
 * @return If the blocking buffer is created successfully then a handle to the
 * created blocking buffer is returned. If either pucBlockingBufferStorageArea or
 * pxStaticblockingBuffer are NULL then NULL is returned.
 *
 * Example use:
 * @code{c}
 *
 * // Used to dimension the array used to hold the blockings.  The available space
 * // will actually be one less than this, so 999.
 #define STORAGE_SIZE_BYTES 1000
 *
 * // Defines the memory that will actually hold the blockings within the blocking
 * // buffer.
 * static uint8_t ucStorageBuffer[ STORAGE_SIZE_BYTES ];
 *
 * // The variable used to hold the blocking buffer structure.
 * StaticBlockingBuffer_t xBlockingBufferStruct;
 *
 * void MyFunction( void )
 * {
 * BlockingBufferHandle_t xBlockingBuffer;
 * const size_t xTriggerLevel = 1;
 *
 *  xBlockingBuffer = xBlockingBufferCreateStatic( sizeof( ucStorageBuffer ),
 *                                             xTriggerLevel,
 *                                             ucStorageBuffer,
 *                                             &xBlockingBufferStruct );
 *
 *  // As neither the pucBlockingBufferStorageArea or pxStaticBlockingBuffer
 *  // parameters were NULL, xBlockingBuffer will not be NULL, and can be used to
 *  // reference the created blocking buffer in other blocking buffer API calls.
 *
 *  // Other code that uses the blocking buffer can go here.
 * }
 *
 * @endcode
 * \defgroup xBlockingBufferCreateStatic xBlockingBufferCreateStatic
 * \ingroup BlockingBufferManagement
 */

#define xBlockingBufferCreateStatic( xBufferSizeBytes, xTriggerLevelBytes, pucBlockingBufferStorageArea, pxStaticBlockingBuffer ) \
    xBlockingBufferGenericCreateStatic( ( xBufferSizeBytes ), ( xTriggerLevelBytes ), pdFALSE, ( pucBlockingBufferStorageArea ), ( pxStaticBlockingBuffer ), NULL, NULL )

#if ( configUSE_SB_COMPLETED_CALLBACK == 1 )
    #define xBlockingBufferCreateStaticWithCallback( xBufferSizeBytes, xTriggerLevelBytes, pucBlockingBufferStorageArea, pxStaticBlockingBuffer, pxSendCompletedCallback, pxReceiveCompletedCallback ) \
    xBlockingBufferGenericCreateStatic( ( xBufferSizeBytes ), ( xTriggerLevelBytes ), pdFALSE, ( pucBlockingBufferStorageArea ), ( pxStaticBlockingBuffer ), ( pxSendCompletedCallback ), ( pxReceiveCompletedCallback ) )
#endif

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BaseType_t xBlockingBufferGetStaticBuffers( BlockingBufferHandle_t xBlockingBuffer,
 *                                           uint8_t ** ppucBlockingBufferStorageArea,
 *                                           StaticBlockingBuffer_t ** ppxStaticBlockingBuffer );
 * @endcode
 *
 * Retrieve pointers to a statically created blocking buffer's data structure
 * buffer and storage area buffer. These are the same buffers that are supplied
 * at the time of creation.
 *
 * @param xBlockingBuffer The blocking buffer for which to retrieve the buffers.
 *
 * @param ppucBlockingBufferStorageArea Used to return a pointer to the blocking
 * buffer's storage area buffer.
 *
 * @param ppxStaticBlockingBuffer Used to return a pointer to the blocking
 * buffer's data structure buffer.
 *
 * @return pdTRUE if buffers were retrieved, pdFALSE otherwise.
 *
 * \defgroup xBlockingBufferGetStaticBuffers xBlockingBufferGetStaticBuffers
 * \ingroup BlockingBufferManagement
 */
#if ( configSUPPORT_STATIC_ALLOCATION == 1 )
    BaseType_t xBlockingBufferGetStaticBuffers( BlockingBufferHandle_t xBlockingBuffer,
                                                uint8_t ** ppucBlockingBufferStorageArea,
                                                StaticBlockingBuffer_t ** ppxStaticBlockingBuffer ) PRIVILEGED_FUNCTION;
#endif /* configSUPPORT_STATIC_ALLOCATION */

/**
 * blocking_buffer.h
 *
 * @code{c}
 * size_t xBlockingBufferSend( BlockingBufferHandle_t xBlockingBuffer,
 *                        const void *pvTxData,
 *                        size_t xDataLengthBytes,
 *                        TickType_t xTicksToWait );
 * @endcode
 *
 * Sends bytes to a blocking buffer.  The bytes are copied into the blocking buffer.
 *
 * ***NOTE***:  Uniquely among FreeRTOS objects, the blocking buffer
 * implementation (so also the message buffer implementation, as message buffers
 * are built on top of blocking buffers) assumes there is only one task or
 * interrupt that will write to the buffer (the writer), and only one task or
 * interrupt that will read from the buffer (the reader).  It is safe for the
 * writer and reader to be different tasks or interrupts, but, unlike other
 * FreeRTOS objects, it is not safe to have multiple different writers or
 * multiple different readers.  If there are to be multiple different writers
 * then the application writer must place each call to a writing API function
 * (such as xBlockingBufferSend()) inside a critical section and set the send
 * block time to 0.  Likewise, if there are to be multiple different readers
 * then the application writer must place each call to a reading API function
 * (such as xBlockingBufferReceive()) inside a critical section and set the receive
 * block time to 0.
 *
 * Use xBlockingBufferSend() to write to a blocking buffer from a task.  Use
 * xBlockingBufferSendFromISR() to write to a blocking buffer from an interrupt
 * service routine (ISR).
 *
 * @param xBlockingBuffer The handle of the blocking buffer to which a blocking is
 * being sent.
 *
 * @param pvTxData A pointer to the buffer that holds the bytes to be copied
 * into the blocking buffer.
 *
 * @param xDataLengthBytes   The maximum number of bytes to copy from pvTxData
 * into the blocking buffer.
 *
 * @param xTicksToWait The maximum amount of time the task should remain in the
 * Blocked state to wait for enough space to become available in the blocking
 * buffer, should the blocking buffer contain too little space to hold the
 * another xDataLengthBytes bytes.  The block time is specified in tick periods,
 * so the absolute time it represents is dependent on the tick frequency.  The
 * macro pdMS_TO_TICKS() can be used to convert a time specified in milliseconds
 * into a time specified in ticks.  Setting xTicksToWait to portMAX_DELAY will
 * cause the task to wait indefinitely (without timing out), provided
 * INCLUDE_vTaskSuspend is set to 1 in FreeRTOSConfig.h.  If a task times out
 * before it can write all xDataLengthBytes into the buffer it will still write
 * as many bytes as possible.  A task does not use any CPU time when it is in
 * the blocked state.
 *
 * @return The number of bytes written to the blocking buffer.  If a task times
 * out before it can write all xDataLengthBytes into the buffer it will still
 * write as many bytes as possible.
 *
 * Example use:
 * @code{c}
 * void vAFunction( BlockingBufferHandle_t xBlockingBuffer )
 * {
 * size_t xBytesSent;
 * uint8_t ucArrayToSend[] = { 0, 1, 2, 3 };
 * char *pcStringToSend = "String to send";
 * const TickType_t x100ms = pdMS_TO_TICKS( 100 );
 *
 *  // Send an array to the blocking buffer, blocking for a maximum of 100ms to
 *  // wait for enough space to be available in the blocking buffer.
 *  xBytesSent = xBlockingBufferSend( xBlockingBuffer, ( void * ) ucArrayToSend, sizeof( ucArrayToSend ), x100ms );
 *
 *  if( xBytesSent != sizeof( ucArrayToSend ) )
 *  {
 *      // The call to xBlockingBufferSend() times out before there was enough
 *      // space in the buffer for the data to be written, but it did
 *      // successfully write xBytesSent bytes.
 *  }
 *
 *  // Send the string to the blocking buffer.  Return immediately if there is not
 *  // enough space in the buffer.
 *  xBytesSent = xBlockingBufferSend( xBlockingBuffer, ( void * ) pcStringToSend, strlen( pcStringToSend ), 0 );
 *
 *  if( xBytesSent != strlen( pcStringToSend ) )
 *  {
 *      // The entire string could not be added to the blocking buffer because
 *      // there was not enough free space in the buffer, but xBytesSent bytes
 *      // were sent.  Could try again to send the remaining bytes.
 *  }
 * }
 * @endcode
 * \defgroup xBlockingBufferSend xBlockingBufferSend
 * \ingroup BlockingBufferManagement
 */
size_t xBlockingBufferSend( BlockingBufferHandle_t xBlockingBuffer,
                            const void * pvTxData,
                            size_t xDataLengthBytes,
                            TickType_t xTicksToWait ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * size_t xBlockingBufferSendFromISR( BlockingBufferHandle_t xBlockingBuffer,
 *                               const void *pvTxData,
 *                               size_t xDataLengthBytes,
 *                               BaseType_t *pxHigherPriorityTaskWoken );
 * @endcode
 *
 * Interrupt safe version of the API function that sends a blocking of bytes to
 * the blocking buffer.
 *
 * ***NOTE***:  Uniquely among FreeRTOS objects, the blocking buffer
 * implementation (so also the message buffer implementation, as message buffers
 * are built on top of blocking buffers) assumes there is only one task or
 * interrupt that will write to the buffer (the writer), and only one task or
 * interrupt that will read from the buffer (the reader).  It is safe for the
 * writer and reader to be different tasks or interrupts, but, unlike other
 * FreeRTOS objects, it is not safe to have multiple different writers or
 * multiple different readers.  If there are to be multiple different writers
 * then the application writer must place each call to a writing API function
 * (such as xBlockingBufferSend()) inside a critical section and set the send
 * block time to 0.  Likewise, if there are to be multiple different readers
 * then the application writer must place each call to a reading API function
 * (such as xBlockingBufferReceive()) inside a critical section and set the receive
 * block time to 0.
 *
 * Use xBlockingBufferSend() to write to a blocking buffer from a task.  Use
 * xBlockingBufferSendFromISR() to write to a blocking buffer from an interrupt
 * service routine (ISR).
 *
 * @param xBlockingBuffer The handle of the blocking buffer to which a blocking is
 * being sent.
 *
 * @param pvTxData A pointer to the data that is to be copied into the blocking
 * buffer.
 *
 * @param xDataLengthBytes The maximum number of bytes to copy from pvTxData
 * into the blocking buffer.
 *
 * @param pxHigherPriorityTaskWoken  It is possible that a blocking buffer will
 * have a task blocked on it waiting for data.  Calling
 * xBlockingBufferSendFromISR() can make data available, and so cause a task that
 * was waiting for data to leave the Blocked state.  If calling
 * xBlockingBufferSendFromISR() causes a task to leave the Blocked state, and the
 * unblocked task has a priority higher than the currently executing task (the
 * task that was interrupted), then, internally, xBlockingBufferSendFromISR()
 * will set *pxHigherPriorityTaskWoken to pdTRUE.  If
 * xBlockingBufferSendFromISR() sets this value to pdTRUE, then normally a
 * context switch should be performed before the interrupt is exited.  This will
 * ensure that the interrupt returns directly to the highest priority Ready
 * state task.  *pxHigherPriorityTaskWoken should be set to pdFALSE before it
 * is passed into the function.  See the example code below for an example.
 *
 * @return The number of bytes actually written to the blocking buffer, which will
 * be less than xDataLengthBytes if the blocking buffer didn't have enough free
 * space for all the bytes to be written.
 *
 * Example use:
 * @code{c}
 * // A blocking buffer that has already been created.
 * BlockingBufferHandle_t xBlockingBuffer;
 *
 * void vAnInterruptServiceRoutine( void )
 * {
 * size_t xBytesSent;
 * char *pcStringToSend = "String to send";
 * BaseType_t xHigherPriorityTaskWoken = pdFALSE; // Initialised to pdFALSE.
 *
 *  // Attempt to send the string to the blocking buffer.
 *  xBytesSent = xBlockingBufferSendFromISR( xBlockingBuffer,
 *                                         ( void * ) pcStringToSend,
 *                                         strlen( pcStringToSend ),
 *                                         &xHigherPriorityTaskWoken );
 *
 *  if( xBytesSent != strlen( pcStringToSend ) )
 *  {
 *      // There was not enough free space in the blocking buffer for the entire
 *      // string to be written, ut xBytesSent bytes were written.
 *  }
 *
 *  // If xHigherPriorityTaskWoken was set to pdTRUE inside
 *  // xBlockingBufferSendFromISR() then a task that has a priority above the
 *  // priority of the currently executing task was unblocked and a context
 *  // switch should be performed to ensure the ISR returns to the unblocked
 *  // task.  In most FreeRTOS ports this is done by simply passing
 *  // xHigherPriorityTaskWoken into portYIELD_FROM_ISR(), which will test the
 *  // variables value, and perform the context switch if necessary.  Check the
 *  // documentation for the port in use for port specific instructions.
 *  portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
 * }
 * @endcode
 * \defgroup xBlockingBufferSendFromISR xBlockingBufferSendFromISR
 * \ingroup BlockingBufferManagement
 */
size_t xBlockingBufferSendFromISR( BlockingBufferHandle_t xBlockingBuffer,
                                   const void * pvTxData,
                                   size_t xDataLengthBytes,
                                   BaseType_t * const pxHigherPriorityTaskWoken ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * size_t xBlockingBufferReceive( BlockingBufferHandle_t xBlockingBuffer,
 *                           void *pvRxData,
 *                           size_t xBufferLengthBytes,
 *                           TickType_t xTicksToWait );
 * @endcode
 *
 * Receives bytes from a blocking buffer.
 *
 * ***NOTE***:  Uniquely among FreeRTOS objects, the blocking buffer
 * implementation (so also the message buffer implementation, as message buffers
 * are built on top of blocking buffers) assumes there is only one task or
 * interrupt that will write to the buffer (the writer), and only one task or
 * interrupt that will read from the buffer (the reader).  It is safe for the
 * writer and reader to be different tasks or interrupts, but, unlike other
 * FreeRTOS objects, it is not safe to have multiple different writers or
 * multiple different readers.  If there are to be multiple different writers
 * then the application writer must place each call to a writing API function
 * (such as xBlockingBufferSend()) inside a critical section and set the send
 * block time to 0.  Likewise, if there are to be multiple different readers
 * then the application writer must place each call to a reading API function
 * (such as xBlockingBufferReceive()) inside a critical section and set the receive
 * block time to 0.
 *
 * Use xBlockingBufferReceive() to read from a blocking buffer from a task.  Use
 * xBlockingBufferReceiveFromISR() to read from a blocking buffer from an
 * interrupt service routine (ISR).
 *
 * @param xBlockingBuffer The handle of the blocking buffer from which bytes are to
 * be received.
 *
 * @param pvRxData A pointer to the buffer into which the received bytes will be
 * copied.
 *
 * @param xBufferLengthBytes The length of the buffer pointed to by the
 * pvRxData parameter.  This sets the maximum number of bytes to receive in one
 * call.  xBlockingBufferReceive will return as many bytes as possible up to a
 * maximum set by xBufferLengthBytes.
 *
 * @param xTicksToWait The maximum amount of time the task should remain in the
 * Blocked state to wait for data to become available if the blocking buffer is
 * empty.  xBlockingBufferReceive() will return immediately if xTicksToWait is
 * zero.  The block time is specified in tick periods, so the absolute time it
 * represents is dependent on the tick frequency.  The macro pdMS_TO_TICKS() can
 * be used to convert a time specified in milliseconds into a time specified in
 * ticks.  Setting xTicksToWait to portMAX_DELAY will cause the task to wait
 * indefinitely (without timing out), provided INCLUDE_vTaskSuspend is set to 1
 * in FreeRTOSConfig.h.  A task does not use any CPU time when it is in the
 * Blocked state.
 *
 * @return The number of bytes actually read from the blocking buffer, which will
 * be less than xBufferLengthBytes if the call to xBlockingBufferReceive() timed
 * out before xBufferLengthBytes were available.
 *
 * Example use:
 * @code{c}
 * void vAFunction( BlockingBuffer_t xBlockingBuffer )
 * {
 * uint8_t ucRxData[ 20 ];
 * size_t xReceivedBytes;
 * const TickType_t xBlockTime = pdMS_TO_TICKS( 20 );
 *
 *  // Receive up to another sizeof( ucRxData ) bytes from the blocking buffer.
 *  // Wait in the Blocked state (so not using any CPU processing time) for a
 *  // maximum of 100ms for the full sizeof( ucRxData ) number of bytes to be
 *  // available.
 *  xReceivedBytes = xBlockingBufferReceive( xBlockingBuffer,
 *                                         ( void * ) ucRxData,
 *                                         sizeof( ucRxData ),
 *                                         xBlockTime );
 *
 *  if( xReceivedBytes > 0 )
 *  {
 *      // A ucRxData contains another xReceivedBytes bytes of data, which can
 *      // be processed here....
 *  }
 * }
 * @endcode
 * \defgroup xBlockingBufferReceive xBlockingBufferReceive
 * \ingroup BlockingBufferManagement
 */
size_t xBlockingBufferReceive( BlockingBufferHandle_t xBlockingBuffer,
                               void * pvRxData,
                               size_t xBufferLengthBytes,
                               TickType_t xTicksToWait ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * size_t xBlockingBufferReceiveFromISR( BlockingBufferHandle_t xBlockingBuffer,
 *                                  void *pvRxData,
 *                                  size_t xBufferLengthBytes,
 *                                  BaseType_t *pxHigherPriorityTaskWoken );
 * @endcode
 *
 * An interrupt safe version of the API function that receives bytes from a
 * blocking buffer.
 *
 * Use xBlockingBufferReceive() to read bytes from a blocking buffer from a task.
 * Use xBlockingBufferReceiveFromISR() to read bytes from a blocking buffer from an
 * interrupt service routine (ISR).
 *
 * @param xBlockingBuffer The handle of the blocking buffer from which a blocking
 * is being received.
 *
 * @param pvRxData A pointer to the buffer into which the received bytes are
 * copied.
 *
 * @param xBufferLengthBytes The length of the buffer pointed to by the
 * pvRxData parameter.  This sets the maximum number of bytes to receive in one
 * call.  xBlockingBufferReceive will return as many bytes as possible up to a
 * maximum set by xBufferLengthBytes.
 *
 * @param pxHigherPriorityTaskWoken  It is possible that a blocking buffer will
 * have a task blocked on it waiting for space to become available.  Calling
 * xBlockingBufferReceiveFromISR() can make space available, and so cause a task
 * that is waiting for space to leave the Blocked state.  If calling
 * xBlockingBufferReceiveFromISR() causes a task to leave the Blocked state, and
 * the unblocked task has a priority higher than the currently executing task
 * (the task that was interrupted), then, internally,
 * xBlockingBufferReceiveFromISR() will set *pxHigherPriorityTaskWoken to pdTRUE.
 * If xBlockingBufferReceiveFromISR() sets this value to pdTRUE, then normally a
 * context switch should be performed before the interrupt is exited.  That will
 * ensure the interrupt returns directly to the highest priority Ready state
 * task.  *pxHigherPriorityTaskWoken should be set to pdFALSE before it is
 * passed into the function.  See the code example below for an example.
 *
 * @return The number of bytes read from the blocking buffer, if any.
 *
 * Example use:
 * @code{c}
 * // A blocking buffer that has already been created.
 * BlockingBuffer_t xBlockingBuffer;
 *
 * void vAnInterruptServiceRoutine( void )
 * {
 * uint8_t ucRxData[ 20 ];
 * size_t xReceivedBytes;
 * BaseType_t xHigherPriorityTaskWoken = pdFALSE;  // Initialised to pdFALSE.
 *
 *  // Receive the next blocking from the blocking buffer.
 *  xReceivedBytes = xBlockingBufferReceiveFromISR( xBlockingBuffer,
 *                                                ( void * ) ucRxData,
 *                                                sizeof( ucRxData ),
 *                                                &xHigherPriorityTaskWoken );
 *
 *  if( xReceivedBytes > 0 )
 *  {
 *      // ucRxData contains xReceivedBytes read from the blocking buffer.
 *      // Process the blocking here....
 *  }
 *
 *  // If xHigherPriorityTaskWoken was set to pdTRUE inside
 *  // xBlockingBufferReceiveFromISR() then a task that has a priority above the
 *  // priority of the currently executing task was unblocked and a context
 *  // switch should be performed to ensure the ISR returns to the unblocked
 *  // task.  In most FreeRTOS ports this is done by simply passing
 *  // xHigherPriorityTaskWoken into portYIELD_FROM_ISR(), which will test the
 *  // variables value, and perform the context switch if necessary.  Check the
 *  // documentation for the port in use for port specific instructions.
 *  portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
 * }
 * @endcode
 * \defgroup xBlockingBufferReceiveFromISR xBlockingBufferReceiveFromISR
 * \ingroup BlockingBufferManagement
 */
size_t xBlockingBufferReceiveFromISR( BlockingBufferHandle_t xBlockingBuffer,
                                      void * pvRxData,
                                      size_t xBufferLengthBytes,
                                      BaseType_t * const pxHigherPriorityTaskWoken ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * void vBlockingBufferDelete( BlockingBufferHandle_t xBlockingBuffer );
 * @endcode
 *
 * Deletes a blocking buffer that was previously created using a call to
 * xBlockingBufferCreate() or xBlockingBufferCreateStatic().  If the blocking
 * buffer was created using dynamic memory (that is, by xBlockingBufferCreate()),
 * then the allocated memory is freed.
 *
 * A blocking buffer handle must not be used after the blocking buffer has been
 * deleted.
 *
 * @param xBlockingBuffer The handle of the blocking buffer to be deleted.
 *
 * \defgroup vBlockingBufferDelete vBlockingBufferDelete
 * \ingroup BlockingBufferManagement
 */
void vBlockingBufferDelete( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BaseType_t xBlockingBufferIsFull( BlockingBufferHandle_t xBlockingBuffer );
 * @endcode
 *
 * Queries a blocking buffer to see if it is full.  A blocking buffer is full if it
 * does not have any free space, and therefore cannot accept any more data.
 *
 * @param xBlockingBuffer The handle of the blocking buffer being queried.
 *
 * @return If the blocking buffer is full then pdTRUE is returned.  Otherwise
 * pdFALSE is returned.
 *
 * \defgroup xBlockingBufferIsFull xBlockingBufferIsFull
 * \ingroup BlockingBufferManagement
 */
BaseType_t xBlockingBufferIsFull( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BaseType_t xBlockingBufferIsEmpty( BlockingBufferHandle_t xBlockingBuffer );
 * @endcode
 *
 * Queries a blocking buffer to see if it is empty.  A blocking buffer is empty if
 * it does not contain any data.
 *
 * @param xBlockingBuffer The handle of the blocking buffer being queried.
 *
 * @return If the blocking buffer is empty then pdTRUE is returned.  Otherwise
 * pdFALSE is returned.
 *
 * \defgroup xBlockingBufferIsEmpty xBlockingBufferIsEmpty
 * \ingroup BlockingBufferManagement
 */
BaseType_t xBlockingBufferIsEmpty( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BaseType_t xBlockingBufferReset( BlockingBufferHandle_t xBlockingBuffer );
 * @endcode
 *
 * Resets a blocking buffer to its initial, empty, state.  Any data that was in
 * the blocking buffer is discarded.  A blocking buffer can only be reset if there
 * are no tasks blocked waiting to either send to or receive from the blocking
 * buffer.
 *
 * @param xBlockingBuffer The handle of the blocking buffer being reset.
 *
 * @return If the blocking buffer is reset then pdPASS is returned.  If there was
 * a task blocked waiting to send to or read from the blocking buffer then the
 * blocking buffer is not reset and pdFAIL is returned.
 *
 * \defgroup xBlockingBufferReset xBlockingBufferReset
 * \ingroup BlockingBufferManagement
 */
BaseType_t xBlockingBufferReset( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * size_t xBlockingBufferSpacesAvailable( BlockingBufferHandle_t xBlockingBuffer );
 * @endcode
 *
 * Queries a blocking buffer to see how much free space it contains, which is
 * equal to the amount of data that can be sent to the blocking buffer before it
 * is full.
 *
 * @param xBlockingBuffer The handle of the blocking buffer being queried.
 *
 * @return The number of bytes that can be written to the blocking buffer before
 * the blocking buffer would be full.
 *
 * \defgroup xBlockingBufferSpacesAvailable xBlockingBufferSpacesAvailable
 * \ingroup BlockingBufferManagement
 */
size_t xBlockingBufferSpacesAvailable( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * size_t xBlockingBufferBytesAvailable( BlockingBufferHandle_t xBlockingBuffer );
 * @endcode
 *
 * Queries a blocking buffer to see how much data it contains, which is equal to
 * the number of bytes that can be read from the blocking buffer before the blocking
 * buffer would be empty.
 *
 * @param xBlockingBuffer The handle of the blocking buffer being queried.
 *
 * @return The number of bytes that can be read from the blocking buffer before
 * the blocking buffer would be empty.
 *
 * \defgroup xBlockingBufferBytesAvailable xBlockingBufferBytesAvailable
 * \ingroup BlockingBufferManagement
 */
size_t xBlockingBufferBytesAvailable( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BaseType_t xBlockingBufferSetTriggerLevel( BlockingBufferHandle_t xBlockingBuffer, size_t xTriggerLevel );
 * @endcode
 *
 * A blocking buffer's trigger level is the number of bytes that must be in the
 * blocking buffer before a task that is blocked on the blocking buffer to
 * wait for data is moved out of the blocked state.  For example, if a task is
 * blocked on a read of an empty blocking buffer that has a trigger level of 1
 * then the task will be unblocked when a single byte is written to the buffer
 * or the task's block time expires.  As another example, if a task is blocked
 * on a read of an empty blocking buffer that has a trigger level of 10 then the
 * task will not be unblocked until the blocking buffer contains at least 10 bytes
 * or the task's block time expires.  If a reading task's block time expires
 * before the trigger level is reached then the task will still receive however
 * many bytes are actually available.  Setting a trigger level of 0 will result
 * in a trigger level of 1 being used.  It is not valid to specify a trigger
 * level that is greater than the buffer size.
 *
 * A trigger level is set when the blocking buffer is created, and can be modified
 * using xBlockingBufferSetTriggerLevel().
 *
 * @param xBlockingBuffer The handle of the blocking buffer being updated.
 *
 * @param xTriggerLevel The new trigger level for the blocking buffer.
 *
 * @return If xTriggerLevel was less than or equal to the blocking buffer's length
 * then the trigger level will be updated and pdTRUE is returned.  Otherwise
 * pdFALSE is returned.
 *
 * \defgroup xBlockingBufferSetTriggerLevel xBlockingBufferSetTriggerLevel
 * \ingroup BlockingBufferManagement
 */
BaseType_t xBlockingBufferSetTriggerLevel( BlockingBufferHandle_t xBlockingBuffer,
                                           size_t xTriggerLevel ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BaseType_t xBlockingBufferSendCompletedFromISR( BlockingBufferHandle_t xBlockingBuffer, BaseType_t *pxHigherPriorityTaskWoken );
 * @endcode
 *
 * For advanced users only.
 *
 * The sbSEND_COMPLETED() macro is called from within the FreeRTOS APIs when
 * data is sent to a message buffer or blocking buffer.  If there was a task that
 * was blocked on the message or blocking buffer waiting for data to arrive then
 * the sbSEND_COMPLETED() macro sends a notification to the task to remove it
 * from the Blocked state.  xBlockingBufferSendCompletedFromISR() does the same
 * thing.  It is provided to enable application writers to implement their own
 * version of sbSEND_COMPLETED(), and MUST NOT BE USED AT ANY OTHER TIME.
 *
 * See the example implemented in FreeRTOS/Demo/Minimal/MessageBufferAMP.c for
 * additional information.
 *
 * @param xBlockingBuffer The handle of the blocking buffer to which data was
 * written.
 *
 * @param pxHigherPriorityTaskWoken *pxHigherPriorityTaskWoken should be
 * initialised to pdFALSE before it is passed into
 * xBlockingBufferSendCompletedFromISR().  If calling
 * xBlockingBufferSendCompletedFromISR() removes a task from the Blocked state,
 * and the task has a priority above the priority of the currently running task,
 * then *pxHigherPriorityTaskWoken will get set to pdTRUE indicating that a
 * context switch should be performed before exiting the ISR.
 *
 * @return If a task was removed from the Blocked state then pdTRUE is returned.
 * Otherwise pdFALSE is returned.
 *
 * \defgroup xBlockingBufferSendCompletedFromISR xBlockingBufferSendCompletedFromISR
 * \ingroup BlockingBufferManagement
 */
BaseType_t xBlockingBufferSendCompletedFromISR( BlockingBufferHandle_t xBlockingBuffer,
                                                BaseType_t * pxHigherPriorityTaskWoken ) PRIVILEGED_FUNCTION;

/**
 * blocking_buffer.h
 *
 * @code{c}
 * BaseType_t xBlockingBufferReceiveCompletedFromISR( BlockingBufferHandle_t xBlockingBuffer, BaseType_t *pxHigherPriorityTaskWoken );
 * @endcode
 *
 * For advanced users only.
 *
 * The sbRECEIVE_COMPLETED() macro is called from within the FreeRTOS APIs when
 * data is read out of a message buffer or blocking buffer.  If there was a task
 * that was blocked on the message or blocking buffer waiting for data to arrive
 * then the sbRECEIVE_COMPLETED() macro sends a notification to the task to
 * remove it from the Blocked state.  xBlockingBufferReceiveCompletedFromISR()
 * does the same thing.  It is provided to enable application writers to
 * implement their own version of sbRECEIVE_COMPLETED(), and MUST NOT BE USED AT
 * ANY OTHER TIME.
 *
 * See the example implemented in FreeRTOS/Demo/Minimal/MessageBufferAMP.c for
 * additional information.
 *
 * @param xBlockingBuffer The handle of the blocking buffer from which data was
 * read.
 *
 * @param pxHigherPriorityTaskWoken *pxHigherPriorityTaskWoken should be
 * initialised to pdFALSE before it is passed into
 * xBlockingBufferReceiveCompletedFromISR().  If calling
 * xBlockingBufferReceiveCompletedFromISR() removes a task from the Blocked state,
 * and the task has a priority above the priority of the currently running task,
 * then *pxHigherPriorityTaskWoken will get set to pdTRUE indicating that a
 * context switch should be performed before exiting the ISR.
 *
 * @return If a task was removed from the Blocked state then pdTRUE is returned.
 * Otherwise pdFALSE is returned.
 *
 * \defgroup xBlockingBufferReceiveCompletedFromISR xBlockingBufferReceiveCompletedFromISR
 * \ingroup BlockingBufferManagement
 */
BaseType_t xBlockingBufferReceiveCompletedFromISR( BlockingBufferHandle_t xBlockingBuffer,
                                                   BaseType_t * pxHigherPriorityTaskWoken ) PRIVILEGED_FUNCTION;

/* Functions below here are not part of the public API. */
BlockingBufferHandle_t xBlockingBufferGenericCreate( size_t xBufferSizeBytes,
                                                     size_t xTriggerLevelBytes,
                                                     BaseType_t xIsMessageBuffer,
                                                     BaseType_t xIsBlockingBuffer,
                                                     BlockingBufferCallbackFunction_t pxSendCompletedCallback,
                                                     BlockingBufferCallbackFunction_t pxReceiveCompletedCallback ) PRIVILEGED_FUNCTION;


BlockingBufferHandle_t xBlockingBufferGenericCreateStatic( size_t xBufferSizeBytes,
                                                           size_t xTriggerLevelBytes,
                                                           BaseType_t xIsMessageBuffer,
                                                           uint8_t * const pucBlockingBufferStorageArea,
                                                           StaticBlockingBuffer_t * const pxStaticBlockingBuffer,
                                                           BlockingBufferCallbackFunction_t pxSendCompletedCallback,
                                                           BlockingBufferCallbackFunction_t pxReceiveCompletedCallback ) PRIVILEGED_FUNCTION;

size_t xBlockingBufferNextMessageLengthBytes( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;

#if ( configUSE_TRACE_FACILITY == 1 )
    void vBlockingBufferSetBlockingBufferNumber( BlockingBufferHandle_t xBlockingBuffer,
                                                 UBaseType_t uxBlockingBufferNumber ) PRIVILEGED_FUNCTION;
    UBaseType_t uxBlockingBufferGetBlockingBufferNumber( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;
    uint8_t ucBlockingBufferGetBlockingBufferType( BlockingBufferHandle_t xBlockingBuffer ) PRIVILEGED_FUNCTION;
#endif

/* *INDENT-OFF* */
#if defined( __cplusplus )
    }
#endif
/* *INDENT-ON* */

#endif /* !defined( STREAM_BUFFER_H ) */
