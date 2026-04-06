import Langlib.Grammars.ContextSensitive.Definition

/-! # Context-Sensitive Languages

This file defines the class of context-sensitive languages via context-sensitive grammars.
-/

variable {T : Type}

/-- Predicate that a language is context-sensitive. -/
def is_CS (L : Language T) : Prop :=
  ∃ g : CS_grammar T, CS_language g = L

/-- The class of context-sensitive languages. -/
def CS : Set (Language T) :=
  setOf is_CS
