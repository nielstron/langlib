import Mathlib

/-! # Regular Closure Under Complement (Iff)

This file proves that a language is regular if and only if its complement is regular.

## Main declarations

- `Language.isRegular_compl_iff`
-/

namespace Language

variable {α : Type*}

/-- A language is regular if and only if its complement is regular. -/
theorem isRegular_compl_iff {L : Language α} :
    Lᶜ.IsRegular ↔ L.IsRegular := by
  constructor
  · intro h
    rw [← compl_compl L]
    exact h.compl
  · exact IsRegular.compl

end Language
