import Langlib.Utilities.Tactics
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Examples.AnBn
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization

/-! # Tactic smoke tests

Verifies that each custom tactic works on representative proof patterns.
-/

open List

/-! ## Test: no_nonterminal -/

-- A nonterminal cannot appear in a list of terminals
example (w : List Bool) (h : List.map symbol.terminal w =
    [symbol.nonterminal ()] ++ List.map symbol.terminal w) : False := by
  no_nonterminal

-- The toFinset variant
example (n : ℕ) (h : List.map (symbol.terminal (N := Unit)) (List.replicate n false ++ List.replicate n true) =
    List.replicate n (symbol.terminal false) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal true)) :
    False := by
  no_nonterminal

-- With explicit symbol witness (fast path)
example (w : List Bool) (h : List.map symbol.terminal w =
    [symbol.nonterminal ()] ++ List.map symbol.terminal w) : False := by
  no_nonterminal (symbol.nonterminal ()) at h


/-! ## Test: deri_context -/

example {T : Type} {g : CF_grammar T} {w₁ w₂ pᵣ pₒ : List (symbol T g.nt)}
    (h : CF_derives g w₁ w₂) :
    CF_derives g (pᵣ ++ w₁ ++ pₒ) (pᵣ ++ w₂ ++ pₒ) := by
  deri_context
  exact h

example {T : Type} {g : CF_grammar T} {w₁ w₂ pᵣ : List (symbol T g.nt)}
    (h : CF_derives g w₁ w₂) :
    CF_derives g (pᵣ ++ w₁) (pᵣ ++ w₂) := by
  deri_context
  exact h
