import Mathlib

/-! # Regular Closure Under Intersection

This file restates mathlib's closure of regular languages under intersection.

## Main declarations

- `Language.IsRegular.inf'`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under intersection. -/
theorem IsRegular.inf' {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ ⊓ L₂).IsRegular := by
  exact h₁.inf h₂

end Language
