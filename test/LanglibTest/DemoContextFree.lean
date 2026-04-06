import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Utilities.ListUtils
import Langlib.Utilities.WrittenByOthers.TrimAssoc


/-! # Context-Free Examples

This file contains example context-free grammars and sample derivation proofs.
-/

private def a_ : Fin 3 := 0
private def a : symbol (Fin 3) (Fin 2) := symbol.terminal a_

private def b_ : Fin 3 := 1
private def b : symbol (Fin 3) (Fin 2) := symbol.terminal b_

private def c_ : Fin 3 := 2
private def c : symbol (Fin 3) (Fin 2) := symbol.terminal c_

private def S_ : Fin 2 := 0
private def S : symbol (Fin 3) (Fin 2) := symbol.nonterminal S_

private def R_ : Fin 2 := 1
private def R : symbol (Fin 3) (Fin 2) := symbol.nonterminal R_

private def gr_add : CF_grammar (Fin 3) :=
  CF_grammar.mk (Fin 2) S_ [
    (S_, [a, S, c]),
    (S_, [R]),
    (R_, [b, R, c]),
    (R_, [])
  ]

/-- A macro for performing one CF grammar derivation step (with a subsequent derivation). -/
macro "cf_step" rule:term "," pref:term "," post:term : tactic =>
  `(tactic| (
    apply CF_deri_of_tran_deri
    · refine ⟨$rule, $pref, $post, ?_, ?_, ?_⟩
      · simp [gr_add]
      · rfl
      · rfl
  ))

example : CF_generates gr_add [a_, a_, b_, c_, c_, c_] := by
  cf_step (S_, [a, S, c]), [], []
  cf_step (S_, [a, S, c]), [a], [c]
  cf_step (S_, [R]), [a, a], [c, c]
  cf_step (R_, [b, R, c]), [a, a], [c, c]
  apply CF_deri_of_tran
  · refine ⟨(R_, []), [a, a, b], [c, c, c], ?_, ?_, ?_⟩
    · simp [gr_add]
    · rfl
    · rfl


private def anbmcnm (n m : ℕ) : List (Fin 3) :=
  List.replicate n a_ ++ List.replicate m b_ ++ List.replicate (n + m) c_

private def language_add : Language (Fin 3) :=
  fun x => ∃ n m : ℕ, x = anbmcnm n m

example : [a_, a_, b_, c_, c_, c_] ∈ language_add := by
  use 2, 1
  rfl

/- The original Lean 3 file contained a proof of `CF_language gr_add = language_add`.
   That proof relied heavily on Lean 3 tactics (`finish`, `nthLe`, `trichotomous`, etc.)
   and is omitted from this Lean 4 translation. -/
