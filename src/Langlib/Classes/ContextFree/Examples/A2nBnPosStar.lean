import Langlib.Classes.ContextFree.Closure.Star
import Langlib.Classes.ContextFree.Examples.A2nBnPos
import Langlib.Examples.A2nBnPosStar

/-! # The `{a^(2n)b^n | n >= 1}*` language -/

open Language

lemma CF_quotientNumerator : is_CF quotientNumerator :=
  CF_of_star_CF quotientLeftBlock CF_quotientLeftBlock
