import Langlib.Examples.BnAnPos

/-! # The language `{b^n a^n | n >= 1}* {b}` -/

/-- Denominator language for the CFL/CFL quotient counterexample. -/
def quotientDenominator : Language Bool :=
  KStar.kstar quotientRightBlock * {[true]}
