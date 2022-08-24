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


#include <stdlib.h>

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
 * all the API functions to use the MPU wrappers.  That should only be done when
 * task.h is included from an application file. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#include "FreeRTOS.h"
#include "old_list.h"

/* Lint e9021, e961 and e750 are suppressed as a MISRA exception justified
 * because the MPU ports require MPU_WRAPPERS_INCLUDED_FROM_API_FILE to be
 * defined for the header files above, but not in this file, in order to
 * generate the correct privileged Vs unprivileged linkage and placement. */
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE /*lint !e961 !e750 !e9021. */

/*-----------------------------------------------------------
* PUBLIC old_LIST API documented in old_list.h
*----------------------------------------------------------*/

void vold_ListInitialise( old_List_t * const pxold_List )
{
    /* The old_list structure contains a old_list item which is used to mark the
     * end of the old_list.  To initialise the old_list the old_list end is inserted
     * as the only old_list entry. */
    pxold_List->pxIndex = ( old_ListItem_t * ) &( pxold_List->xold_ListEnd ); /*lint !e826 !e740 !e9087 The mini old_list structure is used as the old_list end to save RAM.  This is checked and valid. */

    old_listSET_FIRST_old_LIST_ITEM_INTEGRITY_CHECK_VALUE( &( pxold_List->xold_ListEnd ) );

    /* The old_list end value is the highest possible value in the old_list to
     * ensure it remains at the end of the old_list. */
    pxold_List->xold_ListEnd.xItemValue = portMAX_DELAY;

    /* The old_list end next and previous pointers point to itself so we know
     * when the old_list is empty. */
    pxold_List->xold_ListEnd.pxNext = ( old_ListItem_t * ) &( pxold_List->xold_ListEnd );     /*lint !e826 !e740 !e9087 The mini old_list structure is used as the old_list end to save RAM.  This is checked and valid. */
    pxold_List->xold_ListEnd.pxPrevious = ( old_ListItem_t * ) &( pxold_List->xold_ListEnd ); /*lint !e826 !e740 !e9087 The mini old_list structure is used as the old_list end to save RAM.  This is checked and valid. */

    /* Initialize the remaining fields of xold_ListEnd when it is a proper old_ListItem_t */
    #if ( configUSE_MINI_old_LIST_ITEM == 0 )
    {
        pxold_List->xold_ListEnd.pvOwner = NULL;
        pxold_List->xold_ListEnd.pxContainer = NULL;
        old_listSET_SECOND_old_LIST_ITEM_INTEGRITY_CHECK_VALUE( &( pxold_List->xold_ListEnd ) );
    }
    #endif

    pxold_List->uxNumberOfItems = ( UBaseType_t ) 0U;

    /* Write known values into the old_list if
     * configUSE_old_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    old_listSET_old_LIST_INTEGRITY_CHECK_1_VALUE( pxold_List );
    old_listSET_old_LIST_INTEGRITY_CHECK_2_VALUE( pxold_List );
}
/*-----------------------------------------------------------*/

void vold_ListInitialiseItem( old_ListItem_t * const pxItem )
{
    /* Make sure the old_list item is not recorded as being on a old_list. */
    pxItem->pxContainer = NULL;

    /* Write known values into the old_list item if
     * configUSE_old_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    old_listSET_FIRST_old_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem );
    old_listSET_SECOND_old_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem );
}
/*-----------------------------------------------------------*/

void vold_ListInsertEnd( old_List_t * const pxold_List,
                     old_ListItem_t * const pxNewold_ListItem )
{
    old_ListItem_t * const pxIndex = pxold_List->pxIndex;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the old_list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    old_listTEST_old_LIST_INTEGRITY( pxold_List );
    old_listTEST_old_LIST_ITEM_INTEGRITY( pxNewold_ListItem );

    /* Insert a new old_list item into pxold_List, but rather than sort the old_list,
     * makes the new old_list item the last item to be removed by a call to
     * old_listGET_OWNER_OF_NEXT_ENTRY(). */
    pxNewold_ListItem->pxNext = pxIndex;
    pxNewold_ListItem->pxPrevious = pxIndex->pxPrevious;

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    pxIndex->pxPrevious->pxNext = pxNewold_ListItem;
    pxIndex->pxPrevious = pxNewold_ListItem;

    /* Remember which old_list the item is in. */
    pxNewold_ListItem->pxContainer = pxold_List;

    ( pxold_List->uxNumberOfItems )++;
}
/*-----------------------------------------------------------*/

void vold_ListInsert( old_List_t * const pxold_List,
                  old_ListItem_t * const pxNewold_ListItem )
{
    old_ListItem_t * pxIterator;
    const TickType_t xValueOfInsertion = pxNewold_ListItem->xItemValue;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the old_list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    old_listTEST_old_LIST_INTEGRITY( pxold_List );
    old_listTEST_old_LIST_ITEM_INTEGRITY( pxNewold_ListItem );

    /* Insert the new old_list item into the old_list, sorted in xItemValue order.
     *
     * If the old_list already contains a old_list item with the same item value then the
     * new old_list item should be placed after it.  This ensures that TCBs which are
     * stored in ready old_lists (all of which have the same xItemValue value) get a
     * share of the CPU.  However, if the xItemValue is the same as the back marker
     * the iteration loop below will not end.  Therefore the value is checked
     * first, and the algorithm slightly modified if necessary. */
    if( xValueOfInsertion == portMAX_DELAY )
    {
        pxIterator = pxold_List->xold_ListEnd.pxPrevious;
    }
    else
    {
        /* *** NOTE ***********************************************************
        *  If you find your application is crashing here then likely causes are
        *  old_listed below.  In addition see https://www.FreeRTOS.org/FAQHelp.html for
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

        for( pxIterator = ( old_ListItem_t * ) &( pxold_List->xold_ListEnd ); pxIterator->pxNext->xItemValue <= xValueOfInsertion; pxIterator = pxIterator->pxNext ) /*lint !e826 !e740 !e9087 The mini old_list structure is used as the old_list end to save RAM.  This is checked and valid. *//*lint !e440 The iterator moves to a different value, not xValueOfInsertion. */
        {
            /* There is nothing to do here, just iterating to the wanted
             * insertion position. */
        }
    }

    pxNewold_ListItem->pxNext = pxIterator->pxNext;
    pxNewold_ListItem->pxNext->pxPrevious = pxNewold_ListItem;
    pxNewold_ListItem->pxPrevious = pxIterator;
    pxIterator->pxNext = pxNewold_ListItem;

    /* Remember which old_list the item is in.  This allows fast removal of the
     * item later. */
    pxNewold_ListItem->pxContainer = pxold_List;

    ( pxold_List->uxNumberOfItems )++;
}
/*-----------------------------------------------------------*/

UBaseType_t uxold_ListRemove( old_ListItem_t * const pxItemToRemove )
{
/* The old_list item knows which old_list it is in.  Obtain the old_list from the old_list
 * item. */
    old_List_t * const pxold_List = pxItemToRemove->pxContainer;

    pxItemToRemove->pxNext->pxPrevious = pxItemToRemove->pxPrevious;
    pxItemToRemove->pxPrevious->pxNext = pxItemToRemove->pxNext;

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    /* Make sure the index is left pointing to a valid item. */
    if( pxold_List->pxIndex == pxItemToRemove )
    {
        pxold_List->pxIndex = pxItemToRemove->pxPrevious;
    }
    else
    {
        mtCOVERAGE_TEST_MARKER();
    }

    pxItemToRemove->pxContainer = NULL;
    ( pxold_List->uxNumberOfItems )--;

    return pxold_List->uxNumberOfItems;
}
/*-----------------------------------------------------------*/
