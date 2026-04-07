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
