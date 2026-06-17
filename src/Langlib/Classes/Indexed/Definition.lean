import Langlib.Grammars.Indexed.Definition

/-! # Indexed Languages

This file defines the class of indexed languages via indexed grammars.

## Main declarations

- `is_Indexed`
- `Indexed`
-/

variable {T : Type}

/-- Predicate that a language is an indexed language. -/
def is_Indexed (L : Language T) : Prop :=
  ∃ g : IndexedGrammar T, g.Language = L

/-- The class of indexed languages. -/
def Indexed : Set (Language T) :=
  setOf is_Indexed

/-- Predicate that a language has an indexed-grammar witness with no ε-productions. -/
def is_Indexed_noEpsilon (L : Language T) : Prop :=
  ∃ g : IndexedGrammar T, g.NoEpsilon' ∧ g.Language = L

/-- The class of indexed languages with an ε-free indexed-grammar witness. -/
def IndexedNoEpsilon : Set (Language T) :=
  setOf is_Indexed_noEpsilon

theorem is_Indexed_of_is_Indexed_noEpsilon {L : Language T}
    (h : is_Indexed_noEpsilon L) : is_Indexed L := by
  rcases h with ⟨g, _, hL⟩
  exact ⟨g, hL⟩

theorem IndexedNoEpsilon_subclass_Indexed :
    (IndexedNoEpsilon : Set (Language T)) ⊆ Indexed := by
  intro L hL
  exact is_Indexed_of_is_Indexed_noEpsilon hL
