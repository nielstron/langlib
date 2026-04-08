import Langlib.Grammars.ContextSensitive.Definition
import Langlib.Grammars.Unrestricted.Definition

/-! # Context-Sensitive Languages

This file defines the class of context-sensitive languages via unrestricted grammars
satisfying the context-sensitive rule-shape property.
-/

variable {T : Type}

/-- An unrestricted grammar is context-sensitive if every rule preserves its
surrounding context and rewrites the distinguished nonterminal to a non-empty string. -/
def grammar_context_sensitive (g : grammar T) : Prop :=
  ∀ r ∈ g.rules, ∃ γ : List (symbol T g.nt), γ ≠ [] ∧
    r.output_string = r.input_L ++ γ ++ r.input_R

/-- Predicate that a language is context-sensitive. -/
def is_CS (L : Language T) : Prop :=
  ∃ g : grammar T, grammar_context_sensitive g ∧ grammar_language g = L

/-- Legacy characterization of context-sensitive languages via `CS_grammar`. -/
def is_CS_via_csg (L : Language T) : Prop :=
  ∃ g : CS_grammar T, CS_language g = L

/-- The class of context-sensitive languages. -/
def CS : Set (Language T) :=
  setOf is_CS
