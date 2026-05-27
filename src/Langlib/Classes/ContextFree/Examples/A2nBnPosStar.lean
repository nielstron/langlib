import Langlib.Classes.ContextFree.Closure.Star
import Langlib.Classes.ContextFree.Examples.A2nBnPos

/-! # The `{a^(2n)b^n | n >= 1}*` language -/

open Language

/-- Numerator language for the CFL/CFL quotient counterexample. -/
def quotientNumerator : Language Bool :=
  KStar.kstar quotientLeftBlock

lemma CF_quotientNumerator : is_CF quotientNumerator :=
  CF_of_star_CF quotientLeftBlock CF_quotientLeftBlock
