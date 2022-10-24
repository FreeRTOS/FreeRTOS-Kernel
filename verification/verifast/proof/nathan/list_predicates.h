#ifndef LIST_PREDICATES_H

#define LIST_PREDICATES_H

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

#endif /* LIST_PREDICATES_H */