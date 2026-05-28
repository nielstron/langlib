module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Regular.Definition
public import Langlib.Classes.DeterministicContextFree.Definition
public import Mathlib.Computability.DFA
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-! # Regular Languages Included in Deterministic Context-Free Languages

This file proves that every regular language over a finite alphabet is deterministic
context-free.

## Main results

- `is_DCF_of_is_RG` — every regular language is deterministic context-free
- `RG_subclass_DCF` — `RG ⊆ DCF`
-/

open Relation Classical

noncomputable section

variable {T : Type} [Fintype T]

/-- DPDA that simulates a DFA by ignoring its stack. -/
def DPDA_of_DFA {σ : Type} [Fintype σ] (M : DFA T σ) :
    DPDA σ T Unit where
  initial_state := M.start
  start_symbol := ()
  final_states := M.accept
  transition q a _ := some (M.step q a, [()])
  epsilon_transition _ _ := none
  no_mixed := by intro _ _ h; exact absurd rfl h

lemma DPDA_of_DFA_reaches {σ : Type} [Fintype σ] (M : DFA T σ) (q : σ) (w : List T) :
    @PDA.Reaches σ T Unit _ _ _ (DPDA_of_DFA M).toPDA
      ⟨q, w, [()]⟩ ⟨M.evalFrom q w, [], [()]⟩ := by
        induction' w with a w ih generalizing q <;> simp_all +decide [DFA.evalFrom]
        · exact Relation.ReflTransGen.refl
        · refine' Relation.ReflTransGen.trans _ (ih _)
          apply_rules [Relation.ReflTransGen.single]
          constructor
          unfold DPDA.toPDA
          simp +decide [DPDA_of_DFA]

lemma DPDA_of_DFA_reaches_unique {σ : Type} [Fintype σ] (M : DFA T σ)
    (q : σ) (w : List T) (q' : σ) (γ : List Unit)
    (h : @PDA.Reaches σ T Unit _ _ _ (DPDA_of_DFA M).toPDA
      ⟨q, w, [()]⟩ ⟨q', [], γ⟩) :
    q' = M.evalFrom q w ∧ γ = [()] := by
      induction' w with a w ih generalizing q q'
      · contrapose! h
        intro H
        have := H.cases_head
        simp_all +decide [PDA.Reaches₁]
        simp_all +decide [PDA.step]
        unfold DPDA_of_DFA at this
        aesop
      · obtain ⟨q'', hq'', h'⟩ := Relation.ReflTransGen.cases_head h
        rename_i h
        obtain ⟨c, hc₁, hc₂⟩ := h
        cases hc₁
        · unfold DPDA_of_DFA at *
          simp_all +decide
          unfold DPDA.toPDA at *
          simp_all +decide
          exact ih _ _ hc₂
        · simp_all +decide [DPDA_of_DFA]
          tauto

/-- The DPDA of a DFA accepts the same language as the DFA. -/
theorem DPDA_of_DFA_accepts {σ : Type} [Fintype σ] (M : DFA T σ) :
    (DPDA_of_DFA M).acceptsByFinalState = M.accepts := by
      ext w
      constructor <;> intro h
      · obtain ⟨q, hq, γ, hγ⟩ := h
        have := DPDA_of_DFA_reaches_unique M _ _ _ _ hγ
        aesop
      · rw [DFA.mem_accepts] at h
        exact ⟨M.eval w, h, [()], DPDA_of_DFA_reaches M M.start w⟩

/-- Every right-regular language over a finite alphabet is a DCF. -/
theorem is_DCF_of_is_RG {L : Language T} (h : is_RG L) : is_DCF L := by
  obtain ⟨σ, hfin, M, rfl⟩ := isRegular_of_is_RG h
  exact ⟨σ, Unit, hfin, inferInstance, DPDA_of_DFA M, DPDA_of_DFA_accepts M⟩

theorem RG_subclass_DCF :
  RG ⊆ (DCF : Set (Language T)) := by
  intro L
  exact is_DCF_of_is_RG

end
