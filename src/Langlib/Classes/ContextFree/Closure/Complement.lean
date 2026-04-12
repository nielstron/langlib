import Langlib.Classes.ContextFree.Closure.Union
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Definition
import Langlib.Utilities.ClosurePredicates


/-! # Context-Free Non-Closure Under Complement

This file derives failure of closure under complement from the corresponding intersection result.

## Main declarations

- `nnyCF_of_complement_CF`
-/

/-- The class of context-free languages isn't closed under complement. -/
theorem nnyCF_of_complement_CF : ¬ (∀ L : Language (Fin 3),
    is_CF L  →  is_CF (Lᶜ)
) :=
by
  intro h
  have nny := nnyCF_of_CF_i_CF
  push_neg at nny
  rcases nny with ⟨L₁, L₂, ⟨hL₁, hL₂⟩, hyp_neg⟩
  specialize h
  have hu := CF_of_CF_u_CF (L₁ᶜ) (L₂ᶜ) ⟨h L₁ hL₁, h L₂ hL₂⟩
  have contra := h (L₁ᶜ + L₂ᶜ) hu
  apply hyp_neg
  -- golfed by Eric Wieser
  rwa [Language.add_def, Set.compl_union, compl_compl, compl_compl] at contra

/-- Context-free languages over `Fin 3` are not closed under complement. -/
theorem CF_notClosedUnderComplement :
    ¬ ClosedUnderComplement (α := Fin 3) is_CF := by
  rw [ClosedUnderComplement]
  exact nnyCF_of_complement_CF

/-- Context-free languages are not closed under complement for any type with at least
    3 elements. That is, as long as `α` has at least 3 distinct elements, not all
    complements of context-free languages over `α` are context-free. -/
theorem CF_notClosedUnderComplement_of_three {α : Type}
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ClosedUnderComplement (α := α) is_CF := by
  intro hcomp
  apply CF_notClosedUnderIntersection_of_three a b c hab hac hbc
  -- Derive closure under intersection from complement + union (De Morgan)
  intro L₁ L₂ hL₁ hL₂
  have hc₁ := hcomp L₁ hL₁
  have hc₂ := hcomp L₂ hL₂
  have hunion := CF_of_CF_u_CF L₁ᶜ L₂ᶜ ⟨hc₁, hc₂⟩
  have hcc := hcomp (L₁ᶜ + L₂ᶜ) hunion
  rwa [Language.add_def, Set.compl_union, compl_compl, compl_compl] at hcc
