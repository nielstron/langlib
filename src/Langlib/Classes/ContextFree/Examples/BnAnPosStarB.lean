import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Closure.Star
import Langlib.Classes.ContextFree.Examples.BnAnPos

/-! # The `{b^n a^n | n >= 1}* {b}` language -/

open Language

/-- Denominator language for the CFL/CFL quotient counterexample. -/
def quotientDenominator : Language Bool :=
  KStar.kstar quotientRightBlock * {[true]}

lemma CF_quotientDenominator : is_CF quotientDenominator := by
  apply CF_of_CF_c_CF
  exact ⟨CF_of_star_CF quotientRightBlock CF_quotientRightBlock, is_CF_singleton [true]⟩
