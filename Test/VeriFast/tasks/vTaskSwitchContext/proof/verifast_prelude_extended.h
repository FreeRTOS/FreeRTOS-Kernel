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


/*@
lemma void chars_split_at(char* start_ptr, char* split_ptr)
requires chars(start_ptr, ?count, ?vs) &*& 
         start_ptr <= split_ptr &*& split_ptr < start_ptr + count;
ensures  chars(start_ptr, ?c1, ?vs1) &*&
         chars(split_ptr, ?c2, ?vs2) &*&
         start_ptr + c1 == split_ptr &*&
         c1 + c2 == count;
{
    if( start_ptr == split_ptr ) 
    {
        close chars(start_ptr, 0, nil);
    } else
    {
        assert( start_ptr < split_ptr );    // Will fail when pointer provenance checks are turned on
        open chars(start_ptr, _, _);
        chars_split_at(start_ptr+1, split_ptr);
        assert( chars(start_ptr+1, ?c1, _) );
        close chars(start_ptr, c1+1, _);
    }
}
@*/


/*@
lemma void division_remainder_def(int l, int r);
requires l >= 0 &*& r > 0 &*& r < l;
ensures l == (l % r) + (l / r) * r &*&
0 <= (l % r) &*&
(l % r) < r;
@*/

/*@
lemma void chars_to_max_integers__suffix(char* startPtr, int intSize, bool signed_)
requires chars(startPtr, ?count, ?vs) &*& intSize > 0 &*& count > intSize;
ensures  chars(startPtr, ?cc, _) &*&
         integers_(?intStartPtr, intSize, signed_, ?ci, _) &*&
         count == cc + ci * intSize &*&
         intStartPtr == startPtr + cc &*&
         cc < intSize &*&
         ci == count / intSize;
{
    int rem = count % intSize;
    int ci = count / intSize;
    
    division_remainder_def(count, intSize);
    chars_split(startPtr, rem);
    chars_to_integers_(startPtr + rem, intSize, signed_, ci);

}
@*/


#endif /* VERIFAST_PRELUDE_EXTENDED_H */