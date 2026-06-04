module

public import Langlib.Grammars.ContextSensitive.Definition
public import Langlib.Grammars.NonContracting.Definition
@[expose]
public section



/-! # Context-Sensitive Languages

This file defines the class of context-sensitive languages via unrestricted grammars:
all rules are non-contracting, except for an optional distinguished start rule `S → ε`.
-/

variable {T : Type}

/-- The distinguished empty-word rule `S → ε`. -/
@[expose]
public def initial_epsilon_rule (g : grammar T) (r : grule T g.nt) : Prop :=
  r.input_L = [] ∧ r.input_N = g.initial ∧ r.input_R = [] ∧ r.output_string = []

/-- The non-contracting rule condition for a single unrestricted grammar rule. -/
@[expose]
public def grule_noncontracting {N : Type} (r : grule T N) : Prop :=
  r.output_string.length ≥ r.input_L.length + 1 + r.input_R.length

/-- The start symbol does not occur on the right-hand side of any rule. -/
@[expose]
public def initial_not_on_rhs (g : grammar T) : Prop :=
  ∀ r ∈ g.rules, symbol.nonterminal g.initial ∉ r.output_string

/-- An unrestricted grammar is context-sensitive if every rule is either the optional
distinguished rule `S → ε` or is non-contracting, **and** — whenever the `S → ε` rule is
present — the start symbol `S` never occurs on a right-hand side.

The right-hand-side restriction is part of the standard definition of a context-sensitive
grammar: it guarantees that `S` only ever appears as the initial sentential form, so that
the erasing rule `S → ε` contributes exactly the empty word (and nothing else). Without it,
rules such as `S → SS` together with `S → ε` would allow contracting derivations of
non-empty words, taking the grammar outside the context-sensitive (linear-bounded) class. -/
@[expose]
public def grammar_context_sensitive (g : grammar T) : Prop :=
  (∀ r ∈ g.rules, initial_epsilon_rule g r ∨ grule_noncontracting r) ∧
  ((∃ r ∈ g.rules, initial_epsilon_rule g r) → initial_not_on_rhs g)

/-- Every non-contracting grammar is context-sensitive: it has no `S → ε` rule, so the
right-hand-side restriction is vacuous. -/
public theorem grammar_context_sensitive_of_noncontracting (g : grammar T)
    (hg : grammar_noncontracting g) : grammar_context_sensitive g := by
  refine ⟨fun r hr => Or.inr (hg r hr), ?_⟩
  rintro ⟨r, hr, _, _, _, hout⟩
  have := hg r hr
  rw [hout] at this
  simp at this

/-- Predicate that a language is context-sensitive. -/
@[expose]
public def is_CS (L : Language T) : Prop :=
  ∃ g : grammar T, grammar_context_sensitive g ∧ grammar_language g = L

/-- Every non-contracting language is context-sensitive. -/
public theorem is_CS_of_is_noncontracting {L : Language T} (h : is_noncontracting L) :
    is_CS L := by
  obtain ⟨g, hg, hL⟩ := h
  exact ⟨g, grammar_context_sensitive_of_noncontracting g hg, hL⟩

/-- Characterization of context-sensitive languages via ε-free context-preserving grammars. -/
@[expose]
public def is_CS_via_csg (L : Language T) : Prop :=
  ∃ g : CS_grammar T, CS_language g = L

/-- The class of context-sensitive languages. -/
@[expose]
public def CS : Set (Language T) :=
  setOf is_CS
