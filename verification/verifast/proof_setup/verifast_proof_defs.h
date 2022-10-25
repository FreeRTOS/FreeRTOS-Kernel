/*
 * This file contains defines to configure the VeriFast proof setup.
 *
 */


#ifndef VERIFAST_DEFS_H
    // Delete keywords VeriFast canot parse (in some contexts)
    #define inline
    #define __always_inline

    #undef assert
    #define assert(x) BLUB(x)
#endif /* VERIFAST_DEFS_H */
