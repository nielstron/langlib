import Langlib.Grammars.ContextFree.Definition
import Langlib.Grammars.Unrestricted.Definition

/-! # Context-Free Languages

This file defines the class of context-free languages via unrestricted grammars
satisfying the context-free rule-shape property.
-/

variable {T : Type}

/-- An unrestricted grammar is context-free if every rule has empty left and right context. -/
def grammar_context_free (g : grammar T) : Prop :=
  ∀ r ∈ g.rules, r.input_L = [] ∧ r.input_R = []

/-- Predicate that a language is context-free. -/
def is_CF (L : Language T) : Prop :=
  ∃ g : grammar T, grammar_context_free g ∧ grammar_language g = L

/-- Legacy characterization of context-free languages via `CF_grammar`. -/
def is_CF_via_cfg (L : Language T) : Prop :=
  ∃ g : CF_grammar T, CF_language g = L

/-- The class of context-free languages. -/
def CF : Set (Language T) :=
  setOf is_CF
