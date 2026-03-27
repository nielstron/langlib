import Mathlib

/-! # Regular Closure Under Reversal

This file restates mathlib's closure of regular languages under reversal.

## Main declarations

- `Language.IsRegular.reverse`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under reversal. -/
theorem IsRegular.reverse' {L : Language α} (h : L.IsRegular) :
    L.reverse.IsRegular := by
  exact h.reverse

end Language
