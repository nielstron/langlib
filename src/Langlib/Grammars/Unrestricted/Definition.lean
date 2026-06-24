module

public import Mathlib.Computability.Language
@[expose]
public section



/-! # Unrestricted Grammar Definitions

This file defines unrestricted grammars and their derivations.

## Main declarations

- `symbol`
- `grammar`
- `grammar_derives`
- `grammar_language`
-/

open Relation

/-- The type of symbols is the disjoint union of terminals and nonterminals. -/
public inductive symbol (T : Type) (N : Type) where
  | terminal : T → symbol T N
  | nonterminal : N → symbol T N
deriving DecidableEq

/-- Transformation rule for a grammar without any restrictions. -/
public structure grule (T : Type) (N : Type) where
  input_L : List (symbol T N)
  input_N : N
  input_R : List (symbol T N)
  output_string : List (symbol T N)

/-- Grammar (unrestricted) that generates words over the alphabet `T` (a type of terminals). -/
public structure grammar (T : Type) where
  nt : Type -- type of nonterminals
  initial : nt -- initial symbol
  rules : List (grule T nt) -- rewrite rules

variable {T : Type}

/-- One step of grammatical transformation. -/
@[expose]
public def grammar_transforms (g : grammar T) (w₁ w₂ : List (symbol T g.nt)) : Prop :=
  ∃ r : grule T g.nt,
    r ∈ g.rules ∧
      ∃ u v : List (symbol T g.nt),
        (w₁ = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v) ∧
        (w₂ = u ++ r.output_string ++ v)

/-- Any number of steps of grammatical transformation; reflexive+transitive closure of `grammar_transforms`. -/
@[expose]
public def grammar_derives (g : grammar T) :
    List (symbol T g.nt) → List (symbol T g.nt) → Prop :=
  Relation.ReflTransGen (grammar_transforms g)

/-- `grammar_derivesIn g n w₁ w₂` means that `w₁` derives `w₂` in exactly `n`
unrestricted-grammar transformation steps. -/
@[expose]
public def grammar_derivesIn (g : grammar T) :
    ℕ → List (symbol T g.nt) → List (symbol T g.nt) → Prop
  | 0, w₁, w₂ => w₁ = w₂
  | n + 1, w₁, w₂ =>
      ∃ w, grammar_derivesIn g n w₁ w ∧ grammar_transforms g w w₂

@[simp] public theorem grammar_derivesIn_zero {g : grammar T}
    {w₁ w₂ : List (symbol T g.nt)} :
    grammar_derivesIn g 0 w₁ w₂ ↔ w₁ = w₂ :=
  Iff.rfl

@[simp] public theorem grammar_derivesIn_succ {g : grammar T} {n : ℕ}
    {w₁ w₂ : List (symbol T g.nt)} :
    grammar_derivesIn g (n + 1) w₁ w₂ ↔
      ∃ w, grammar_derivesIn g n w₁ w ∧ grammar_transforms g w w₂ :=
  Iff.rfl

public theorem grammar_derivesIn_refl {g : grammar T}
    (w : List (symbol T g.nt)) :
    grammar_derivesIn g 0 w w :=
  rfl

public theorem grammar_derivesIn_one_of_transforms {g : grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : grammar_transforms g w₁ w₂) :
    grammar_derivesIn g 1 w₁ w₂ :=
  ⟨w₁, rfl, h⟩

public theorem grammar_derives_of_derivesIn {g : grammar T} {n : ℕ}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : grammar_derivesIn g n w₁ w₂) :
    grammar_derives g w₁ w₂ := by
  induction n generalizing w₂ with
  | zero =>
      subst w₂
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact (ih hprev).tail hstep

public theorem exists_grammar_derivesIn_of_derives {g : grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : grammar_derives g w₁ w₂) :
    ∃ n, grammar_derivesIn g n w₁ w₂ := by
  induction h with
  | refl =>
      exact ⟨0, rfl⟩
  | tail hprev hstep ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, _, hn, hstep⟩

public theorem grammar_derives_iff_exists_derivesIn {g : grammar T}
    {w₁ w₂ : List (symbol T g.nt)} :
    grammar_derives g w₁ w₂ ↔ ∃ n, grammar_derivesIn g n w₁ w₂ := by
  constructor
  · exact exists_grammar_derivesIn_of_derives
  · rintro ⟨n, h⟩
    exact grammar_derives_of_derivesIn h

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
@[expose]
public def grammar_generates (g : grammar T) (w : List T) : Prop :=
  grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
@[expose]
public def grammar_language (g : grammar T) : Language T :=
  setOf (grammar_generates g)
