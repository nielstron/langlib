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


/-! ## Test: replicate_norm -/

example (n : ℕ) :
    List.length (List.replicate n false ++ List.replicate n true) = n + n := by
  replicate_norm

example (n : ℕ) :
    List.replicate (n + 1) false = false :: List.replicate n false := by
  replicate_norm


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


/-! ## Test: language_ext -/

example : ({w : List Bool | w = []} : Language Bool) = {w | w = []} := by
  language_ext


/-! ## Test: grammar_cases on cfg_anbn -/

-- Test that grammar_cases destructures a CF_transforms and case-splits on rules.
-- After grammar_cases, each branch has the concrete rule substituted.
example (w' : List (symbol Bool Unit))
    (ht : CF_transforms cfg_anbn [symbol.nonterminal ()] w') :
    w' = [symbol.terminal false, symbol.nonterminal (), symbol.terminal true] ∨ w' = [] := by
  grammar_cases ht [cfg_anbn]
