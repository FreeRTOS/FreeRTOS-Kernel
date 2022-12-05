#ifndef VERIFAST_LISTS_EXTENDED_H
#define VERIFAST_LISTS_EXTENDED_H

/* This file contains lemmas that would fit `list.gh` which is part
 * of VeriFast's standard library.
 */




// TODO: Can we prove this in VeriFast or do we have to axiomatise?
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

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void drop_index_equals_singleton_implies_last_element<t>(list<t> xs, t x)
requires drop(index_of(x, xs), xs) == cons(x, nil);
ensures index_of(x, xs) == length(xs) - 1;
{
    // Will prove later. For now, we only validate with an example. 
    list<int> _xs = cons(1, cons(2, cons(3, cons(4, cons(5, cons(6, cons(7, nil)))))));
    int _x = 7;

    int i = index_of(_x, _xs);
    list<int> d = drop(index_of(x, xs), _xs);

    assert( index_of(_x, _xs) == length(_xs) - 1 );

    // ADMIT LEMMA, PROVE LATER
    assume(false);
}

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
// Can we replace this by standard lemma `drop_n_plus_one`?
lemma void drop_cons<t>(list<t> xs, int n)
requires n < length(xs);
ensures drop(n, xs) == cons(nth(n, xs), drop(n+1, xs));
{
    // Will prove later. For now, we only validate with an example. 
    list<int> _xs = cons(1, cons(2, cons(3, cons(4, cons(5, cons(6, cons(7, nil)))))));
    int _n = 3;

    list<int> dn = drop(_n, _xs);
    int nthn = nth(_n, _xs);
    list<int> dnp1 = drop(_n + 1, _xs);

    assert( drop(_n, _xs) == cons(nth(_n, _xs), drop(_n+1, _xs)) );

    // ADMIT LEMMA, PROVE LATER
    assume(false);
}

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void nth_index<t>(list<t> xs, t x)
requires mem(x, xs) == true;
ensures nth(index_of(x, xs), xs) == x;
{
    // Will prove later. For now, we only validate with an example. 
    list<int> _xs = cons(1, cons(2, cons(3, cons(4, cons(5, cons(6, cons(7, nil)))))));
    int _x = 4;

    int i = index_of(_x, _xs);
    int nthi = nth(index_of(_x, _xs), _xs);

    assert( nth(index_of(_x, _xs), _xs) == _x );

    // ADMIT LEMMA, PROVE LATER
    assume(false);
}

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void mem_prefix_implies_mem<t>(t x, list<t> xs, int n);
requires mem(x, take(n, xs)) == true;
ensures mem(x, xs) == true;

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void mem_suffix_implies_mem<t>(t x, list<t> xs, int n);
requires mem(x, drop(n, xs)) == true;
ensures mem(x, xs) == true;

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void drop_n_plus_m<t>(list<t> xs, int n, int m);
requires true;
ensures drop(n, drop(m, xs)) == drop(n + m, xs);


// Can use `forall_mem` from `listex.gh` instead
// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void forall_instantiate<t>(t x, list<t> xs, fixpoint(t, bool) f);
requires forall(xs, f) == true &*& mem(x, xs) == true;
ensures forall(xs, f) == true &*& f(x) == true;


// Can use `neq_mem_remove` from `listex.gh` instead
// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void mem_after_remove<t>(t x, list<t> xs, t r);
requires true;
ensures mem(x, remove(r, xs)) == (mem(x, xs) && x != r);


fixpoint bool superset<t>(list<t> super, list<t> sub) {
    return subset(sub, super);
}


// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void update_out_of_bounds<t>(int index, t x, list<t> xs)
requires (index < 0 || index >= length(xs));
ensures update(index, x, xs) == xs;
{
    switch(xs) {
        case nil:   // nothing to do
        case cons(h, rest): {
            update_out_of_bounds(index-1, x, rest);
        }
    }
}


lemma void index_of_different<t>(t x1, t x2, list<t> xs)
requires x1 != x2 &*& mem(x1, xs) == true &*& mem(x2, xs) == true;
ensures index_of(x1, xs) != index_of(x2, xs);
{
    switch(xs) {
        case nil: 
        case cons(h, rest):
            if(h != x1 && h != x2) {
                index_of_different(x1, x2, rest);
            }
    }
}

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void subset_cons_tail<t>(list<t> xs);
requires xs == cons(?h, ?t);
ensures subset(t, xs) == true;

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void remove_result_subset<t>(t x, list<t> xs);
requires true;
ensures subset(remove(x, xs), xs) == true;
// TODO: Revisit this lemma
// {
//     switch(xs) {
//         case nil: 
//         case cons(h, t):
//             remove_result_subset(x, t);
//             if(h == x) {
//                 assert( remove(x, xs) == t );
//                 subset_cons_tail(xs);
//                 assert( subset(t, cons(x, t) ) == true );
//             } else {
//                 ;
//             }
//     }
// }

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
// Special case of `nth_update` from `listex.gh`.
lemma void update_preserves_rest<t>(int i, int u, t v, list<t> xs);
requires 0 <= i && i < length(xs) && 0 <= u && u < length(xs) && i != u;
ensures  nth(i, update(u, v, xs)) == nth(i, xs);

// TODO: Can we prove this in VeriFast or do we have to axiomatise?
lemma void append_take_nth_drop<t>(int n, list<t> xs);
requires 0 <= n &*& n < length(xs);
ensures xs == append( take(n, xs), cons(nth(n, xs), drop(n+1, xs)) );
@*/



#endif /* VERIFAST_LISTS_EXTENDED_H */