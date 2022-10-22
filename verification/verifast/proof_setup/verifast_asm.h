#ifndef VERIFAST_ASM_H
#define VERIFAST_ASM_H

/* VeriFast does not support inline assembler.
 * The following definitions replace macros that would normally evaluate to
 * inline assember by failing assertions.
 */

/* VeriFast treats `assert` as keyword and does not support calling it
 * in many contexts where function calls are permitted. */
bool assert_fct(bool b) 
{
    assert(b);
    return b;
}


#undef portCHECK_IF_IN_ISR
#define portCHECK_IF_IN_ISR()  assert_fct(false)

/* Additional reason for rewrite:
 * VeriFast does not support embedding block statements that consist of
 * multiple elemts in expression contexts, e.g., `({e1; e2})`.
 */
#undef portSET_INTERRUPT_MASK_FROM_ISR
#define portSET_INTERRUPT_MASK_FROM_ISR()   assert_fct(false)

#undef portRESTORE_INTERRUPTS
#define portRESTORE_INTERRUPTS(ulState) assert_fct(false)

#endif /* VERIFAST_ASM_H */