#ifndef VERIFAST_LISTS_EXTENDED_H
#define VERIFAST_LISTS_EXTENDED_H

/* This file contains lemmas that would fit `list.gh` which is part
 * of VeriFast's standard library.
 */

// TODO: prove
/*@
lemma void mem_suffix_implies_mem<t>(t x, list<t> xs, int i);
requires mem(x, drop(i, xs)) == true;
ensures  mem(x, xs) == true;
@*/

#endif /* VERIFAST_LISTS_EXTENDED_H */