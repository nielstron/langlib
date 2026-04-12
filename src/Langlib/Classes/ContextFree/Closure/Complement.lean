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
theorem nnyCF_of_complement_CF : ¬ (∀ T : Type, ∀ L : Language T,
    is_CF L  →  is_CF (Lᶜ)
) :=
by
  intro h
  have nny := nnyCF_of_CF_i_CF
  push_neg at nny
  rcases nny with ⟨T, L₁, L₂, ⟨hL₁, hL₂⟩, hyp_neg⟩
  specialize h T
  have hu := CF_of_CF_u_CF (L₁ᶜ) (L₂ᶜ) ⟨h L₁ hL₁, h L₂ hL₂⟩
  have contra := h (L₁ᶜ + L₂ᶜ) hu
  apply hyp_neg
  -- golfed by Eric Wieser
  rwa [Language.add_def, Set.compl_union, compl_compl, compl_compl] at contra

/-- Context-free languages over `Fin 3` are not closed under complement. -/
theorem CF_notClosedUnderComplement :
    ¬ ClosedUnderComplement (α := Fin 3) is_CF := by
  intro h
  have h_inter : ClosedUnderIntersection (α := Fin 3) is_CF := by
    intro L₁ L₂ hL₁ hL₂
    have h_union_compl : is_CF (L₁ᶜ + L₂ᶜ) := by
      exact CF_of_CF_u_CF (L₁ᶜ) (L₂ᶜ) ⟨h _ hL₁, h _ hL₂⟩
    have h_compl_back : is_CF ((L₁ᶜ + L₂ᶜ)ᶜ) := h _ h_union_compl
    simpa [Language.add_def, Set.compl_union, compl_compl, compl_compl] using h_compl_back
  exact CF_notClosedUnderIntersection h_inter
