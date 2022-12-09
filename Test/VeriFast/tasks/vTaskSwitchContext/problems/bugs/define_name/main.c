/* Bug:
 * The header `defining_header.h` defines the constant `ABC` and
 * the header `testing_header.h` checks whether `ABC` has been defined.
 * In `testing_header.h` both checks `#ifdef ABC` and its negation
 * `#ifndef ABC` evaluate to true.
 */

#include "defining_header.h"


/*
#ifdef ABC			// ok: evaluates to true
    #error "ABC defined"		
#else				// ok: evaluates to false
    #error "ABC not defined"
#endif
*/


#include "testing_header.h"