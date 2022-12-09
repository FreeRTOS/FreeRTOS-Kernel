This directory contains the bulk of VeriFast formalizations and proofs.





# Directory Structure
```
├── *.h files
│   Headers containing VeriFast formalizations and proofs.
│
├── README.md
│   Contains more details about the proof.
│
├── single_core_proofs
│   Contains the old list formalization and proofs written by
│   Aalok Thakkar and Nathan Chong in 2020 for the single-core 
│   setup.
│   │
│   ├── scp_common.h
│   │   Contains auxiliary definitions and lemmas.
│   │
│   └── scp_list_predicates.h
│       Contains the formalizaton of doubly linked lists and list items.
│
└── single_core_proofs_extended
    Contains new proofs extending the single-core list
    formalization.
```





# Reusing the Single-Core List Formalization and Proofs
We reuse the list formalization and proofs written by Aalok Thakkar and Nathan
Chong in 2020. However, due to new challenges that arise in the code we verify,
we have to extend and adapt the existing formalization.
The single-core list formalization defines two main predicates:
- ```
  predicate xLIST_ITEM(struct xLIST_ITEM *n,
                       TickType_t xItemValue,
                       struct xLIST_ITEM *pxNext,
                       struct xLIST_ITEM *pxPrevious,
                       struct xLIST *pxContainer;)
  ```
  Represents a list item of type `xLIST_ITEM`. The arguments have the following
  semantics:
  - `n`: A pointer to the node whose memory the predicate represents.
  - `xItemValue`: The value stored in node `n`.
  - `pxNext`: The node's "next" pointer, i.e., `n->pxNext`.
  - `pxPrevious`: The node's "previous" pointer, i.e., `n->pxPrevious`.
  - `pxContainer`: The doubly linked list containing this node.
- ```
  predicate DLS(struct xLIST_ITEM *n,
                struct xLIST_ITEM *nprev,
                struct xLIST_ITEM *mnext,
                struct xLIST_ITEM *m,
                list<struct xLIST_ITEM * > cells,
                list<TickType_t > vals,
                struct xLIST *pxContainer)
  ```
  Represents a non-empty doubly linked list segment. The semantics of the
  arguments are as follows:
  - `n`: The left-most node in the segment.
  - `nPrev`: The left-most node's "previous" pointer, i.e., `n->pxPrevious`.
  - `mNext`: The right-most node's "next" pointer, i.e., `m->pxNext`.
  - `m`: The right-most node.
  - `cells`: A VeriFast list storing pointers to all nodes the list contains.
  - `vals`: A VeriFast list storing the list nodes' values.
  - `pxContainer`: A pointer to list struct.

  The single-core formalization also uses `DLS` not just to represent list
  segments but also to express unsegmented cyclic linked lists. In FreeRTOS 
  lists start with a sentinel, called "end". Using the `DLS` predicate, a
  cyclic list has the form:
  `DLS(end, endPrev, end, endPrev, cells, vals, list)`





# Iterating through a DLS

We verify `vTaskSwitchContext` which internally calls 
`prvSelectHighestPriorityTask` to select the task that will be scheduled next.
The function `prvSelectHighestPriorityTask` iterates through the ready lists. 
Hence, reasoning about it requires us to reason about iteration through memory 
described as a DLS predicate instance. Consider the following scenario:
We have a DLS predicate representing our cyclic ready list and a task item 
pointer `pxTaskItem` which points to an element of this list.

- `DLS(end, endPrev, end, endPrev, cells, vals, readyList)`
- `mem(pxTaskItem, cells) == true`

Suppose we want to move the task pointer forward

- `pxTaskItem2 = pxTaskItem->pxNext`

In order to verify this line we have to do two things:

1. Justify the heap access to `pxTaskItem->pxNext`
2. Prove that `pxTaskItem2` points to an element of the list. This is 
   necessary to reason about any code that uses `pxTaskItem2`.

We can do this by opening the recursive predicate at the nodes for `pxTaskItem` 
and `pxTaskItem->next`, for which we can reuse the existing list proof lemmas. 
When the right parts of the predicate are exposed, we can prove (1) and (2). 
Afterwards, we have to close the predicate again.





# Issue 1: DLS iteration proofs are hard because of many case splits

Proving (1) and (2) forces us to consider many different cases, which leads to 
complicated proofs. 
The position of `pxTaskItem` in the list determines how we should open the `DLS` 
(either by using the existing `split` lemma or with VeriFast’s `open` command) 
and also how we have to close it at the end of the proof.
Accessing `pxTaskItem->pxNext` introduces more case splits that complicate the 
proof. 
Again, closing the predicate has to account for all the introduced cases.

Note that proofs for forward iteration cannot be reused for backwards iteration 
but requires separate proofs.





# Issue 2: Checking DLS iteration proofs has bad performance

As explained above, reasoning about about a single statement that moves the item pointer forward or backward introduces many case splits. `prvSelectHighestPriorityTask` contains multiple statements that manipulate the item pointer. From VeriFast’s perspective, each consecutive proof of such an iteration statement splits up the proof tree further. This is the case even though this part of the code we reason about is linear.

Introducing lemmas for opening and closing shortens the consecutive iteration proofs significantly, but does not eliminate the case splits. The reason for this is that the `DLS` predicate cannot express empty segments and depending of the current proof path, the number of predicate on the symbolic heap after opening the `DLS` changes.

Hence, we cannot unify the proof state representation of the proof state as long as we stick to the `DLS` predicate. Instead the opening lemma’s postcondition and the closing lemma’s precondition must reflect the case split. Consequently, applying the lemmas in a proof introduces the case splits anyway and consecutive iteration statements/ lemma applications increase the number of proof paths exponentially. VeriFast requires ~20 min to reason about 4 iteration statements.





# Solution: Introduce new representation for opened DLS 


The only way to eliminate the case splits in `prvSelectHighestPriorityTask` is to unify the proof state of an opened `DLS` accross all proof paths. We introduce two new predicates that express potentially empty prefixes and suffixes of opened cyclic `DLS`. With that, we can formalize an opened list in a unified way as

- `DLS_prefix(....) &*& xLIST_ITEM(pxTaskItem, ...) &*& DLS_suffix(...)`

Additionally, we write opening and closing lemmas that transform the a DLS predicate instance into our new representation and back. The proof state we get after opening the list does not force VeriFast to consider any case splits. 

Eliminating these case splits reduces verification time from ~20min to ~1min 10s. 

The old opening and closing lemmas required Z3, because they required heavier reasoning about applications of `list<t>` fixpoint functions and the shape of the inductive `list<t>` datatype. VeriFast offers limited capabilities to reason about fixpoint functions (apart from axiomatizing) and the standard SMT solver often has problems reasoning about the shape of results, e.g., assertions of the form `drop(i, vals) == cons(_, _)`. The new lemma proofs don’t require Z3. Hence, we can switch back to VeriFast’s standard SMT solver. This reduces verification time further to an instant.

Note that the lemmas still have to consider every possible case internally. That is, the opening and closing lemmas remain complicated.
