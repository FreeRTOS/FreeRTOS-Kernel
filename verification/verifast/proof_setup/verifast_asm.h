#ifndef VERIFAST_ASM_H
#define VERIFAST_ASM_H

bool assert_fct(bool b) 
{
    assert(b);
    return b;
}
#undef portCHECK_IF_IN_ISR
#define portCHECK_IF_IN_ISR()  assert_fct(false)

#endif /* VERIFAST_ASM_H */