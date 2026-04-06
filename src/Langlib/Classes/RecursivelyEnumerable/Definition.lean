import Langlib.Grammars.Unrestricted.Definition

/-! # Recursively Enumerable Languages

This file defines the class of recursively enumerable languages via unrestricted grammars.
-/

variable {T : Type}

/-- Predicate that a language is recursively enumerable. -/
def is_RE (L : Language T) : Prop :=
  ∃ g : grammar T, grammar_language g = L

/-- The class of recursively enumerable languages. -/
def RE : Set (Language T) :=
  setOf is_RE
