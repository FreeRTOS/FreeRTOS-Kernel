#ifndef VERIFAST_PRELUDE_EXTENDED_H
#define VERIFAST_PRELUDE_EXTENDED_H

/* This file contains axioms that would naturally fit into prelude.h
 * but are missing.
 */

/* Reminder:

predicate chars_(char *array, int count; list<option<char> > cs) =
    count == 0 ?
        cs == nil
    :
        char_(array, ?c) &*& chars_(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);

predicate chars(char *array, int count; list<char> cs) =
    count == 0 ?
        cs == nil
    :
        character(array, ?c) &*& chars(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);


lemma_auto void chars__to_chars(char *array);
    requires [?f]chars_(array, ?count, ?cs) &*& cs == map(some, map(the, cs));
    ensures [f]chars(array, count, map(the, cs));



predicate integers__(void *p, int size, bool signed_, int count; list<option<int> > vs) =
    count == 0 ?
        vs == nil
    :
        integer__(p, size, signed_, ?v0) &*& integers__(p + size, size, signed_, count - 1, ?vs0) &*& vs == cons(v0, vs0);

predicate integers_(void *p, int size, bool signed_, int count; list<int> vs) =
    count == 0 ?
        vs == nil
    :
        integer_(p, size, signed_, ?v0) &*& integers_(p + size, size, signed_, count - 1, ?vs0) &*& vs == cons(v0, vs0);


 */




/*@
lemma_auto void integers___to_integers_(void *p);
    requires [?f]integers__(p, ?size, ?signed_, ?count, _);
    ensures [f]integers_(p, size, signed_, count, _);
@*/

#endif /* VERIFAST_PRELUDE_EXTENDED_H */