import Langlib.Examples.A2nBnPos

/-! # The language `{a^(2n)b^n | n >= 1}*` -/

/-- Numerator language for the CFL/CFL quotient counterexample. -/
def quotientNumerator : Language Bool :=
  KStar.kstar quotientLeftBlock
