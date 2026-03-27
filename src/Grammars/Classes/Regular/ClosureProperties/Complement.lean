import Mathlib

/-! # Regular Closure Under Complement

This file restates mathlib's closure of regular languages under complement.

## Main declarations

- `Language.IsRegular.compl'`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under complement. -/
theorem IsRegular.compl' {L : Language α} (h : L.IsRegular) :
    Lᶜ.IsRegular := by
  exact h.compl

end Language
