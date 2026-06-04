module

public import Langlib.Examples.Halting
public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Mathlib.Computability.Halting
import Langlib.Automata.Turing.DSL.CodeToTMDirect
import Langlib.Automata.Turing.DSL.SearchProcToTM0
import Langlib.Automata.Turing.Equivalence.TMEqualsRE
@[expose]
public section

/-! # The halting language is recursively enumerable

This file proves `haltingUnaryLanguage_RE`: the language of all halting Turing machines
(`haltingUnaryLanguage`) is recursively enumerable.

Bounded evaluation `Nat.Partrec.Code.evaln` gives a computable test `haltingUnaryTest`
that, searched over the step budget `k`, accepts exactly the words whose length decodes to
a halting code.  A computable search is partial-recursive, hence realizable by a Turing
machine, hence RE.
-/

open Nat.Partrec

/-- Bounded halting test for the unary language. -/
@[expose]
public def haltingUnaryTest (k : ℕ) (w : List Unit) : Bool :=
  (Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0).isSome

public theorem haltingUnaryTest_computable₂ :
    Computable₂ haltingUnaryTest := by
  apply Computable₂.mk
  have hEval : Primrec (fun p : ℕ × List Unit =>
      Nat.Partrec.Code.evaln p.1 (Nat.Partrec.Code.ofNatCode p.2.length) 0) := by
    convert Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.fst.pair
        ((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.list_length.comp Primrec.snd))).pair
        (Primrec.const 0)) using 1
  exact (Primrec.option_isSome.comp hEval).to_comp.of_eq (by
    intro p
    rfl)

public theorem haltingUnaryLanguage_search (w : List Unit) :
    w ∈ haltingUnaryLanguage ↔ ∃ k, haltingUnaryTest k w = true := by
  unfold haltingUnaryLanguage haltingUnaryTest
  constructor
  · intro h
    change ((Nat.Partrec.Code.ofNatCode w.length).eval 0).Dom at h
    rw [Part.dom_iff_mem] at h
    obtain ⟨x, hx⟩ := h
    rw [Nat.Partrec.Code.evaln_complete] at hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    cases hEval : Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0 with
    | none =>
        simp [hEval] at hk
    | some y =>
        rfl
  · rintro ⟨k, hk⟩
    cases hEval : Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0 with
    | none =>
        simp [hEval] at hk
    | some y =>
        change ((Nat.Partrec.Code.ofNatCode w.length).eval 0).Dom
        rw [Part.dom_iff_mem]
        exact ⟨y, Nat.Partrec.Code.evaln_sound (by simpa [hEval])⟩

/-- The unary halting language is recursively enumerable. -/
public theorem haltingUnaryLanguage_RE : is_RE haltingUnaryLanguage := by
  obtain ⟨c, hc⟩ := search_is_partrec haltingUnaryTest haltingUnaryTest_computable₂
  have htm : is_TM haltingUnaryLanguage :=
    code_implies_isTM_direct haltingUnaryLanguage c (fun w => by
      rw [← hc w]
      exact haltingUnaryLanguage_search w)
  exact (is_TM_iff_is_RE haltingUnaryLanguage).1 htm

end
