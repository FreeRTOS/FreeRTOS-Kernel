#ifndef VERIFAST_RP2040_AXIOMS_H
#define VERIFAST_RP2040_AXIOMS_H

#include "stdint.h"

/*
 * The lemmas in this file axiomatize that the RP2040 architecture uses
 * 32bit pointers.
 */

/*@
// Axiomatizes that: 0 <= ptr <= 2^32 - 1
lemma void ptr_range(void* ptr);
requires true;
ensures (void*) 0 <= ptr &*& ptr <= (void*) 4294967295;
@*/


#endif