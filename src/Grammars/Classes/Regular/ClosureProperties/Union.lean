import Mathlib

/-! # Regular Closure Under Union

This file restates mathlib's closure of regular languages under union.

## Main declarations

- `Language.IsRegular.add'`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under union. -/
theorem IsRegular.add' {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ + L₂).IsRegular := by
  exact h₁.add h₂

end Language
