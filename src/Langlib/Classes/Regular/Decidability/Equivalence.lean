import Mathlib
import Langlib.Classes.Regular.Closure.Complement
import Langlib.Classes.Regular.Closure.Intersection
import Langlib.Classes.Regular.Closure.Union
import Langlib.Classes.Regular.Decidability.Emptiness

/-! # Decidability of Equivalence for Regular Languages

This file proves that equivalence is decidable for regular languages.

The proof reduces equivalence to emptiness of the symmetric difference:
`L₁ = L₂ ↔ symmDiff L₁ L₂ = ∅`, and the symmetric difference is regular
(by closure under complement, intersection, and union).

## Main results

- `regular_equivalence_decidable` — equivalence of two regular languages is decidable.
-/

section Regular

variable {α : Type*}

private lemma eq_iff_symmDiff_eq_bot (L₁ L₂ : Language α) :
    L₁ = L₂ ↔ symmDiff L₁ L₂ = ⊥ := by
  constructor <;> intro <;> rw [ symmDiff ] at * <;> aesop

private lemma symmDiff_isRegular {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (symmDiff L₁ L₂).IsRegular := by
  convert Language.IsRegular.add' _ _ using 1;
  · convert Language.IsRegular.inf' h₁ ( Language.IsRegular.compl h₂ ) using 1;
  · convert Language.IsRegular.inf' h₂ ( Language.IsRegular.compl h₁ ) using 1

/-- Equivalence of two regular languages is decidable. -/
noncomputable def regular_equivalence_decidable
    [Fintype α] [DecidableEq α] (L₁ L₂ : Language α)
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    Decidable (L₁ = L₂) := by
  rw [eq_iff_symmDiff_eq_bot]
  exact regular_emptiness_decidable _ (symmDiff_isRegular h₁ h₂)

end Regular