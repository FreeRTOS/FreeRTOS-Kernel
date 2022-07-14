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
#include "list.h"

/* Lint e9021, e961 and e750 are suppressed as a MISRA exception justified
 * because the MPU ports require MPU_WRAPPERS_INCLUDED_FROM_API_FILE to be
 * defined for the header files above, but not in this file, in order to
 * generate the correct privileged Vs unprivileged linkage and placement. */
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE /*lint !e961 !e750 !e9021. */


/*-----------------------------------------------------------
* PUBLIC LIST API documented in list.h
*----------------------------------------------------------*/

void vListInitialise( List_t * const pxList )
{
    pxList->pxIndex = ( UBaseType_t ) 0U; 
    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;
    
    // We ideally need to replace 'numElements' with 'configLIST_SIZE',
    // but the workaround below is necessary to deal with the performance
    // problem from this issue (https://github.com/diffblue/cbmc/issues/7012)
    // Can perhaps change it once the issue gets resolved.
    UBaseType_t numElements;
    pxList->xListData = (ListItem_t **) pvPortMalloc(numElements * sizeof(*(pxList->xListData)));
    if (pxList->xListData==NULL){
        // TOOD: error handling
        exit(1);
    }
    __CPROVER_assume(numElements == configLIST_SIZE);

    /* Write known values into the list if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    listSET_LIST_INTEGRITY_CHECK_1_VALUE( pxList );
    listSET_LIST_INTEGRITY_CHECK_2_VALUE( pxList );
}
/*-----------------------------------------------------------*/

void vListInitialiseItem( ListItem_t * const pxItem )
{
    /* Make sure the list item is not recorded as being on a list. */
    pxItem->pxContainer = NULL;

    /* Write known values into the list item if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    listSET_FIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem );
    listSET_SECOND_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem );
}
/*-----------------------------------------------------------*/

void vListinsertAtIndex ( List_t * const pxList, UBaseType_t index, ListItem_t * const pxNewListItem )
{
    // Copy all the elements beyond index to one position on the right.
    for ( UBaseType_t i = pxList->uxNumberOfItems ; i > index ; i--)
    __CPROVER_assigns (i,__CPROVER_POINTER_OBJECT(pxList->xListData))
    __CPROVER_loop_invariant (i >= index && i<=pxList->uxNumberOfItems)
    __CPROVER_decreases (i-index)
    {
        pxList->xListData[i] = pxList->xListData[i-1];
    }
    pxList->xListData[index] = pxNewListItem;
}

void vListInsertEnd( List_t * const pxList,
                     ListItem_t * const pxNewListItem )
{
    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );

    if (pxList->uxNumberOfItems >= configLIST_SIZE){  // can't add beyond capacity.
        // TODO: Add error handling?
        exit(1);
    }
    /* Insert a new list item into pxList, but rather than sort the list,
     * makes the new list item the last item to be removed by a call to
     * listGET_OWNER_OF_NEXT_ENTRY(). */
    vListinsertAtIndex(pxList, pxList->pxIndex,pxNewListItem);
    // Adjust the number of items and pxIndex
    if (pxList->uxNumberOfItems > 0){
        pxList->pxIndex++;
    }
    ( pxList->uxNumberOfItems )++;

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    /* Remember which list the item is in. */
    pxNewListItem->pxContainer = pxList;
}
/*-----------------------------------------------------------*/



void vListInsert( List_t * const pxList,
                  ListItem_t * const pxNewListItem )
{
    const TickType_t xValueOfInsertion = pxNewListItem->xItemValue;

    if (pxList->uxNumberOfItems >= configLIST_SIZE){  // can't add beyond capacity.
        // TODO: Add error handling?
        exit(1);
    }

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );

    /* Insert the new list item into the list, sorted in xItemValue order.
     *
     * If the list already contains a list item with the same item value then the
     * new list item should be placed after it.  This ensures that TCBs which are
     * stored in ready lists (all of which have the same xItemValue value) get a
     * share of the CPU.   */

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
    UBaseType_t i = 0;
    for( ; i < pxList->uxNumberOfItems && pxList->xListData[i]->xItemValue <= xValueOfInsertion; i++)  /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. *//*lint !e440 The iterator moves to a different value, not xValueOfInsertion. */
    __CPROVER_loop_invariant (i >= 0 && i <= pxList->uxNumberOfItems)
    __CPROVER_decreases (pxList->uxNumberOfItems - i)
    {
        /* There is nothing to do here, just iterating to the wanted
        * insertion position. */
    }
    vListinsertAtIndex(pxList,i,pxNewListItem);
    // Adjust the number of items and pxIndex
    if (pxList->uxNumberOfItems > 0 && pxList->pxIndex >= i)
    { 
        pxList->pxIndex++;
    }
    ( pxList->uxNumberOfItems )++;
    /* Remember which list the item is in.  This allows fast removal of the
     * item later. */
    pxNewListItem->pxContainer = pxList;
}
/*-----------------------------------------------------------*/

UBaseType_t uxListRemove( ListItem_t * const pxItemToRemove )
{
    // The list item knows which list it is in.  Obtain the list from 
    // the list item.
    List_t * const pxList = pxItemToRemove->pxContainer;

    // Find the index to delete
    UBaseType_t indexToDelete;
    int found = 0;
    for (UBaseType_t i = 0 ; i < pxList->uxNumberOfItems ; i++ )
    __CPROVER_loop_invariant (i >= 0 && i <= pxList->uxNumberOfItems)
    __CPROVER_decreases (pxList->uxNumberOfItems - i)
    {
        if (pxList->xListData[i] == pxItemToRemove){
            indexToDelete = i;
            found = 1;
            break;
        }
    }
    if (found == 0){  // element not found. something is wrong.
        /* TODO: need to give an error message? */
        mtCOVERAGE_TEST_MARKER();
        exit(1);
    }

    // Move all the elements ahead of the index back by 1.
    for (UBaseType_t i = indexToDelete + 1; i < pxList->uxNumberOfItems ; i++)
    __CPROVER_assigns (i,__CPROVER_POINTER_OBJECT(pxList->xListData))
    __CPROVER_loop_invariant (i >= indexToDelete + 1 && i <= pxList->uxNumberOfItems)
    __CPROVER_decreases (pxList->uxNumberOfItems - i)
    {
        pxList->xListData[i-1] = pxList->xListData[i];
    }

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    // Update pxIndex, size and container.
    pxItemToRemove->pxContainer = NULL;
    ( pxList->uxNumberOfItems )--;
    if (pxList->uxNumberOfItems==0)
    {
        pxList->pxIndex = 0;
    }
    else
    {
        if (pxList->pxIndex >= indexToDelete)
        {  
            if (pxList->pxIndex == 0){
                pxList->pxIndex = pxList->uxNumberOfItems - 1;
            } 
            else
            {
                pxList->pxIndex--;
            }           
        }
    }
    return pxList->uxNumberOfItems;
}
/*-----------------------------------------------------------*/
