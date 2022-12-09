// Problem: Both branches branch conditions evaluate to true.

/* `main.c` included this header after including `defining_header.h`.
 * Hence, `#ifdef ABC` should evaluate to true and `#ifndef ABC should
 * evaluate to false.
 */

/*
#ifdef ABC			// ok: evaluates to true.
    #error "ABC defined"	
#endif
*/


#ifndef ABC			// bug: evaluates to true
    #error "ABC defined"
#endif