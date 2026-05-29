module

public import Langlib.Classes.ContextFree.Closure.Quotient
public import Langlib.Classes.DeterministicContextFree.Examples.A2nBnPosStar
public import Langlib.Classes.DeterministicContextFree.Examples.BnAnPosStarB
public import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
public import Langlib.Utilities.ClosurePredicates

/-!
# Deterministic Context-Free Right Quotients

This file proves that deterministic context-free languages are not closed under
right quotient.  The witness is the same quotient used for CFL non-closure:

* `quotientNumerator = {a^(2n)b^n | n >= 1}*`
* `quotientDenominator = {b^n a^n | n >= 1}* {b}`

Both witness languages are deterministic context-free, by the DPDAs in
`DeterministicContextFree/Examples`.  If DCFLs were closed under right quotient,
their quotient would be a DCFL and therefore context-free, contradicting the
CFL pumping argument already proved in `ContextFree/Closure/Quotient`.
-/

open Language

/-- Deterministic context-free languages are not closed under right quotient. -/
public theorem DCF_notClosedUnderRightQuotient :
    ¬ ClosedUnderRightQuotient (α := Bool) is_DCF := by
  intro hclosed
  exact notCF_quotient
    (is_CF_of_is_DCF
      (hclosed quotientNumerator quotientDenominator
        DCFA2nBnPosStar.DCF_quotientNumerator
        DCFBnAnPosStarB.DCF_quotientDenominator))
