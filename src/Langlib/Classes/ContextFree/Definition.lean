import Langlib.Grammars.ContextFree.Definition

/-! # Context-Free Languages

This file defines the class of context-free languages via context-free grammars.
-/

variable {T : Type}

/-- Predicate that a language is context-free. -/
def is_CF (L : Language T) : Prop :=
  ∃ g : CF_grammar T, CF_language g = L

/-- The class of context-free languages. -/
def CF : Set (Language T) :=
  setOf is_CF
