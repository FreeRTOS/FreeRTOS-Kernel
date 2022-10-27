#ifndef STACK_PREDICATES
#define STACK_PREDICATES


/*@
// Represents a stack that grows down (cf. RP2040 stack)
predicate stack_p(StackType_t * pxStack, uint32_t ulStackDepth, StackType_t * pxTopOfStack, uint32_t freeCells) =
	integers_(pxStack, sizeof(StackType_t), false, ulStackDepth, _) &*&
    ulStackDepth > 0 &*&
    freeCells >= 0 &*&
    pxTopOfStack == pxStack + freeCells -1 &*&
    0 <= freeCells &*& freeCells <= ulStackDepth;
//	usedMem == pxStack - pxTopOfStack
//	freeMem == ulStackDepth - usedMem
	//freeCells * sizeof(StackType_t) == ulStackDepth * sizeof(StackType_t) - ((char*) pxStack - (char*) pxTopOfStack) &*&
//	usedCells * sizeof(StackType_t) == ((char*) pxStack - (char*) pxTopOfStack);
@*/

/*/@
lemma void split_stack(StackType_t * pxStack, int offset)
requires stack_p(pxStack,?ulStackDepth, ?pxTopOfStack, ?freeMem, _) &*& 0 <= offset &*& 
                offset * sizeof(StackType_t) < ulStackDepth;
ensures integers_(pxStack, sizeof(StackType_t), true, offset * sizeof(StackType_t), _) &*&
                integers_(pxStack + offset * sizeof(StackType_t), sizeof(StackType_t), true, ulStackDepth - offset * sizeof(StackType_t), _) ;
{
	open stack_p(_, _, _, _);
	integers__split(pxStack, offset * sizeof(StackType_t) );
}
@*/

/*@
// TODO: Do we need this lemma or is it usually cleaner to split stack manually?
lemma void getTopOfStack(StackType_t* pxStack, StackType_t* pxTopOfStack)
requires stack_p(pxStack,?ulStackDepth, pxTopOfStack, ?freeCells) &*&
                 freeCells > 0;
ensures // free cells minus top cell
        integers_(pxStack, sizeof(StackType_t), false, freeCells-1, _)	&*&
        // top stack cell
		integer_(pxStack + freeCells-1, sizeof(StackType_t), false, _) &*&
        // used stack cells
		integers_(pxStack + freeCells, sizeof(StackType_t), false, 
                  ulStackDepth - freeCells, _) &*&
        // stack contraints necessary to close `stack_p` again
        ulStackDepth > 0 &*&
        freeCells >= 0 &*&
        pxTopOfStack == pxStack + freeCells -1 &*&
        0 <= freeCells &*& freeCells <= ulStackDepth;
{
    open stack_p(_, _, _, _);
    integers__split(pxStack, freeCells-1);
    open integers_(pxStack + (freeCells-1), _, _, _, _);
}
@*/


#endif /* STACK_PREDICATES */