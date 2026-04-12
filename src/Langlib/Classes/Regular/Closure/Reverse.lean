import Mathlib
import Langlib.Utilities.ClosurePredicates

/-! # Regular Closure Under Reversal (Iff)

This file restates mathlib's proof that a language is regular if and only if its
reversal is regular.

## Main declarations

- `Language.isRegular_reverse_iff'` — local alias for the Mathlib iff statement.
-/

namespace Language

variable {α : Type*}

/-- A language is regular if and only if its reversal is regular. This is a local alias for
    `Language.isRegular_reverse_iff` from Mathlib. -/
theorem isRegular_reverse_iff' {L : Language α} :
    L.reverse.IsRegular ↔ L.IsRegular :=
  isRegular_reverse_iff

end Language

/-- The class of regular languages is closed under reversal. -/
theorem Regular_closedUnderReverse : ClosedUnderReverse {L : Language α | L.IsRegular} :=
  fun L hL => hL.reverse
