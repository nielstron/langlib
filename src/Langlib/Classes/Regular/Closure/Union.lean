import Mathlib
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Examples.TopBot
import Langlib.Utilities.ClosurePredicates

/-! # Regular Closure Under Union

This file restates mathlib's closure of regular languages under union and shows
that the converse fails.

## Main declarations

- `Language.IsRegular.add'`
- `Language.not_iff_regular_union`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under union. -/
theorem IsRegular.add' {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ + L₂).IsRegular := by
  exact h₁.add h₂

/-- The converse of union closure fails. -/
theorem not_iff_regular_union :
    ¬ (∀ (L₁ L₂ : Language Bool), (L₁ + L₂).IsRegular ↔ (L₁.IsRegular ∧ L₂.IsRegular)) := by
  intro h
  have hunion : (anbn + anbnᶜ).IsRegular := by
    have : anbn + anbnᶜ = ⊤ := sup_compl_eq_top
    rw [this]
    exact isRegular_top
  exact anbn_not_isRegular ((h anbn anbnᶜ).mp hunion).1

end Language

/-- The class of regular languages is closed under union. -/
theorem RG_closedUnderUnion [Fintype α] : ClosedUnderUnion (α := α) is_RG := by
  intro L₁ L₂ h₁ h₂
  exact is_RG_of_isRegular (isRegular_of_is_RG h₁ |>.add (isRegular_of_is_RG h₂))
