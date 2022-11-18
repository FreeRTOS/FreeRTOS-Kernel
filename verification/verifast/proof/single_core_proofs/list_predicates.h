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
	struct xLIST *pxContainer;) 
	=
	n->xItemValue |-> xItemValue &*&
	n->pxNext |-> pxNext &*&
	n->pxPrevious |-> pxPrevious &*&
	n->pvOwner |-> _ &*&
	n->pxContainer |-> pxContainer;

// by Tobias Reinhard
predicate xList_gen(struct xLIST *l) =
	l->uxNumberOfItems |-> _ &*&
	l->pxIndex |-> _;

predicate List_p(List_t* l);
@*/


/* Ferreira et al. (STTT'14) doubly-linked list segment (DLS). */
/* @
predicate DLS(
	struct xLIST_ITEM *n,
	struct xLIST_ITEM *nprev,
	struct xLIST_ITEM *mnext,
	struct xLIST_ITEM *m,
	list<struct xLIST_ITEM * > cells,
	list<TickType_t > vals,
	struct xLIST *pxContainer) =
	n == m
		? cells == cons(n, nil) &*&
			vals == cons(?v, nil) &*&
			xLIST_ITEM(n, v, mnext, nprev, pxContainer)
		: cells == cons(n, ?cells0) &*&
			vals == cons(?v, ?vals0) &*&
			xLIST_ITEM(n, v, ?o, nprev, pxContainer) &*& DLS(o, n, mnext, m, cells0, vals0, pxContainer);
@*/


/* @
predicate xLIST(
	struct xLIST *l,
	int uxNumberOfItems,
	struct xLIST_ITEM *pxIndex,
	struct xLIST_ITEM *xListEnd,
	list<struct xLIST_ITEM *>cells,
	list<TickType_t >vals) =
	l->uxNumberOfItems |-> uxNumberOfItems &*&
	l->pxIndex |-> pxIndex &*&
	mem(pxIndex, cells) == true &*&
	xListEnd == &(l->xListEnd) &*&
	xListEnd == head(cells) &*&
	portMAX_DELAY == head(vals) &*&
	struct_xLIST_ITEM_padding(&l->xListEnd) &*&
	length(cells) == length(vals) &*&
	uxNumberOfItems + 1 == length(cells) &*&
	DLS(xListEnd, ?endprev, xListEnd, endprev, cells, vals, l);
@*/

#endif /* LIST_PREDICATES_H */