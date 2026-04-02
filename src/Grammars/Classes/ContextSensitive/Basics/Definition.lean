import Grammars.Classes.Unrestricted.Basics.Definition


/-! # Context-Sensitive Grammar Definitions

This file defines context-sensitive grammars, their derivations, and the induced language predicate.

A context-sensitive grammar has rules of the form `αAβ → αγβ` where:
- `α` (`context_left`) and `β` (`context_right`) are the context (strings of symbols),
- `A` (`input_nonterminal`) is a nonterminal, and
- `γ` (`output_string`) is a non-empty string of symbols.

The non-emptiness requirement on `γ` ensures that derivation steps never decrease the length
of the sentential form, which is the defining property of context-sensitive grammars.

## Main declarations

- `csrule`
- `CS_grammar`
- `CS_transforms`
- `CS_language`
- `is_CS`
-/

/-- Transformation rule for a context-sensitive grammar.

A rule `αAβ → αγβ` where `α` is `context_left`, `A` is `input_nonterminal`,
`β` is `context_right`, and `γ` is `output_string`. -/
structure csrule (T : Type) (N : Type) where
(context_left : List (symbol T N))
(input_nonterminal : N)
(context_right : List (symbol T N))
(output_string : List (symbol T N))

/-- Context-sensitive grammar that generates words over the alphabet `T` (a type of terminals).

The `output_nonempty` field ensures that every rule has a non-empty output string, matching
the standard definition of context-sensitive grammars. This guarantees that derivation steps
never decrease the length of the sentential form. -/
structure CS_grammar (T : Type) where
(nt : Type)                   -- type of nonterminals
(initial : nt)                -- initial symbol
(rules : List (csrule T nt))  -- rewrite rules
(output_nonempty : ∀ r ∈ rules, r.output_string ≠ [])

variable {T : Type}

/-- One step of context-sensitive transformation. -/
def CS_transforms (g : CS_grammar T) (w₁ w₂ : List (symbol T g.nt))  : Prop :=
  ∃r : csrule T g.nt, ∃u v : List (symbol T g.nt), r ∈ g.rules ∧
  (w₁ = u ++ r.context_left ++ [symbol.nonterminal r.input_nonterminal] ++ r.context_right ++ v) ∧
  (w₂ = u ++ r.context_left ++ r.output_string ++ r.context_right ++ v)

/-- Any number of steps of context-sensitive transformation; reflexive+transitive closure of `CS_transforms`. -/
def CS_derives (g : CS_grammar T) : List (symbol T g.nt) → List (symbol T g.nt) → Prop :=
Relation.ReflTransGen (CS_transforms g)

/-- The Set of words that can be derived from the initial nonterminal. -/
def CS_language (g : CS_grammar T) : Language T :=
λ w : List T ↦ CS_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w)

/-- Predicate "is context-sensitive"; defined by existence of a context-sensitive grammar for the given Language. -/
def is_CS (L : Language T) : Prop :=
∃ g : CS_grammar T, CS_language g = L

/-- The class of context-sensitive languages. -/
def CS : Set (Language T) :=
  setOf is_CS
