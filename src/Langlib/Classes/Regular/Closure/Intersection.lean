import Mathlib
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Examples.TopBot
import Langlib.Utilities.ClosurePredicates

/-! # Regular Closure Under Intersection

This file restates mathlib's closure of regular languages under intersection and
shows that the converse fails.

## Main declarations

- `Language.IsRegular.inf'`
- `Language.not_iff_regular_intersection`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under intersection. -/
theorem IsRegular.inf' {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ ⊓ L₂).IsRegular := by
  exact h₁.inf h₂

/-- The converse of intersection closure fails. -/
theorem not_iff_regular_intersection :
    ¬ (∀ (L₁ L₂ : Language Bool), (L₁ ⊓ L₂).IsRegular ↔ (L₁.IsRegular ∧ L₂.IsRegular)) := by
  intro h
  have hinf : (anbn ⊓ ⊥).IsRegular := by
    rw [show anbn ⊓ (⊥ : Language Bool) = ⊥ by simp]
    exact isRegular_bot
  exact anbn_not_isRegular ((h anbn ⊥).mp hinf).1

end Language

/-- The class of regular languages is closed under intersection. -/
theorem Regular_closedUnderIntersection : ClosedUnderIntersection {L : Language α | L.IsRegular} :=
  fun L₁ L₂ h₁ h₂ => h₁.inf h₂
