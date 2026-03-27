import Grammars.Classes.Unrestricted.Basics.Lifting
import Grammars.Classes.Unrestricted.ClosureProperties.Concatenation
import Grammars.Utilities.WrittenByOthers.TrimAssoc

/-! # RE Closure Under Kleene Star

This file proves closure of recursively enumerable languages under Kleene star.

## Main declarations

- `RE_of_star_RE`
-/

variable {T : Type}

/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : Language T) :
  is_RE L  →  is_RE (KStar.kstar L)  := by
  sorry
