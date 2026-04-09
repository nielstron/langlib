import Mathlib
import Langlib.Classes.Linear.Definition

/-! # Regular Languages Included in Linear Languages

This file proves that every regular language is linear by showing that
right-regular productions are linear productions.

## Main results

- `is_Linear_of_is_RG`    — every regular language is linear
- `RG_subclass_Linear`    — `RG ⊆ Linear`
-/

open Language List Relation Classical

noncomputable section

variable {T : Type}

/-- A right-regular output has linear form. -/
theorem linear_output_of_right_regular {N : Type} {s : List (symbol T N)}
    (h : right_regular_output s) : linear_output s := by
  rcases h with ⟨a, B, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact Or.inr ⟨[a], B, [], by simp⟩
  · exact Or.inl (by intro x hx; simp at hx; exact ⟨a, hx⟩)
  · exact Or.inl (by simp)

/-- A right-regular grammar is linear. -/
theorem grammar_linear_of_right_regular {g : grammar T}
    (hg : grammar_right_regular g) : grammar_linear g := by
  intro r hr
  obtain ⟨h1, h2, h3⟩ := hg r hr
  exact ⟨h1, h2, linear_output_of_right_regular h3⟩

/-- Every regular language is linear. -/
theorem is_Linear_of_is_RG {L : Language T} (h : is_RG L) : is_Linear L := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g, grammar_linear_of_right_regular hg, rfl⟩

/-- The class of regular languages is a subclass of the linear languages. -/
theorem RG_subclass_Linear :
    (RG : Set (Language T)) ⊆ (Linear : Set (Language T)) := by
  intro L hL
  exact is_Linear_of_is_RG hL

end
