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


// TODO: prove
/*@
lemma void head_drop_n_equals_nths<t>(list<t> xs, int n)
requires n >= 0;
ensures head(drop(n, xs)) == nth(n, xs);
{
    // Will prove later. For now, we only validate with an example. 
    
    list<int> _xs = cons(1, cons(2, cons(3, cons(4, cons(5, cons(6, cons(7, nil)))))));
    int _n = 4;

    list<int> dn = drop(_n, _xs);
    int hdn = head(dn);
    int nthn = nth(_n, _xs);
    
    assert( hdn == head(drop(_n, _xs)) );
    assert( nthn == nth(_n, _xs ));
    assert( head(drop(_n, _xs)) == nth(_n, _xs) );

    
    // ADMIT LEMMA, PROVE LATER
    assume(false);
}
@*/

#endif /* VERIFAST_LISTS_EXTENDED_H */