import Grammars.Classes.ContextFree.PumpingCfg.ChomskyNormalForm

/-! # CNF Bridge Lemmas

This file adds small bridge lemmas connecting the project's Chomsky-normal-form API to mathlib conventions.

## Main declarations

- `ChomskyNormalFormRule.Rewrites.word`
- `ChomskyNormalFormGrammar.Produces.input_output`
-/

universe uT uN
variable {T : Type uT}

lemma ChomskyNormalFormRule.Rewrites.word {N : Type uN} {r : ChomskyNormalFormRule T N}
    {u : List T} {v : List (Symbol T N)}
    (hruv : r.Rewrites (u.map Symbol.terminal) v) :
    False := by
  induction u generalizing v with
  | nil => cases hruv
  | cons _ _ ih =>
    cases hruv with
    | cons _ _ hru => exact ih hru

lemma ChomskyNormalFormGrammar.Produces.input_output
    {g : ChomskyNormalFormGrammar.{uN} T} {r : ChomskyNormalFormRule T g.NT}
    (hrg : r ∈ g.rules) :
    g.Produces [.nonterminal r.input] r.output :=
  ⟨r, hrg, ChomskyNormalFormRule.Rewrites.input_output⟩
