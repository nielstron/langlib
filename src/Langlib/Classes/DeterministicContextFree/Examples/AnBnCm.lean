module

public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Examples.AnBnCm
public import Langlib.Classes.DeterministicContextFree.Examples.AbcStack
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
@[expose]
public section



/-! # Deterministic Context-Free Examples over `a b c`

This file gives a deterministic pushdown automaton for `{aⁿbⁿcᵐ | n,m ≥ 0}`.
-/

open PDA List

namespace DCFLIntersection

public inductive EqAnyState where
  | start
  | seenA
  | seenB
  | trailC
  | onlyC
  deriving DecidableEq, Fintype


open EqAnyState ABCStack

private lemma replicate_append_cons_self {α : Type} (n : ℕ) (x : α) (rest : List α) :
    replicate n x ++ x :: rest = x :: (replicate n x ++ rest) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, ih]

private lemma replicate_append_cons_eq {α : Type} (n : ℕ) (x : α) (rest : List α) :
    replicate n x ++ x :: rest = replicate (n + 1) x ++ rest := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, ih]

/-- DPDA recognizing `{aⁿbⁿcᵐ | n,m ≥ 0}`. -/
@[expose]
public def dpda_eq_any : DPDA EqAnyState (Fin 3) ABCStack where
  initial_state := EqAnyState.start
  start_symbol := bottom
  final_states := {EqAnyState.start, trailC, onlyC}
  transition q x Z :=
    match q, x, Z with
    | EqAnyState.start, x, bottom =>
        if x = a_ then some (seenA, [mark, bottom])
        else if x = c_ then some (onlyC, [bottom])
        else none
    | EqAnyState.seenA, x, mark =>
        if x = a_ then some (EqAnyState.seenA, [mark, mark])
        else if x = b_ then some (EqAnyState.seenB, [])
        else none
    | EqAnyState.seenB, x, mark =>
        if x = b_ then some (EqAnyState.seenB, [])
        else none
    | trailC, x, bottom =>
        if x = c_ then some (trailC, [bottom])
        else none
    | onlyC, x, bottom =>
        if x = c_ then some (onlyC, [bottom])
        else none
    | _, _, _ => none
  epsilon_transition q Z :=
    match q, Z with
    | EqAnyState.seenB, bottom => some (trailC, [bottom])
    | _, _ => none
  no_mixed := by decide

private lemma eq_any_step_read_a_init (rest : List (Fin 3)) :
    @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.start, a_ :: rest, [bottom]⟩
      ⟨EqAnyState.seenA, rest, [mark, bottom]⟩ := by
  constructor
  unfold dpda_eq_any
  aesop

private lemma eq_any_step_read_c_init (rest : List (Fin 3)) :
    @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.start, c_ :: rest, [bottom]⟩
      ⟨onlyC, rest, [bottom]⟩ := by
  constructor
  unfold dpda_eq_any
  aesop

private lemma eq_any_step_read_a (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.seenA, a_ :: rest, mark :: stk⟩
      ⟨EqAnyState.seenA, rest, mark :: mark :: stk⟩ := by
  constructor
  unfold dpda_eq_any
  aesop

private lemma eq_any_step_read_b_from_a (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.seenA, b_ :: rest, mark :: stk⟩
      ⟨EqAnyState.seenB, rest, stk⟩ := by
  constructor
  unfold dpda_eq_any
  aesop

private lemma eq_any_step_read_b (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.seenB, b_ :: rest, mark :: stk⟩
      ⟨EqAnyState.seenB, rest, stk⟩ := by
  constructor
  unfold dpda_eq_any
  aesop

private lemma eq_any_step_to_trail (rest : List (Fin 3)) :
    @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.seenB, rest, [bottom]⟩
      ⟨trailC, rest, [bottom]⟩ := by
  cases rest <;> simp +decide [PDA.Reaches₁, PDA.step, dpda_eq_any, DPDA.toPDA]

private lemma eq_any_step_read_c_trail (rest : List (Fin 3)) :
    @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨trailC, c_ :: rest, [bottom]⟩
      ⟨trailC, rest, [bottom]⟩ := by
  constructor
  unfold dpda_eq_any
  aesop

private lemma eq_any_step_read_c_only (rest : List (Fin 3)) :
    @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨onlyC, c_ :: rest, [bottom]⟩
      ⟨onlyC, rest, [bottom]⟩ := by
  constructor
  unfold dpda_eq_any
  aesop

private lemma eq_any_read_as (k : ℕ) (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.seenA, replicate k a_ ++ rest, mark :: stk⟩
      ⟨EqAnyState.seenA, rest, replicate (k + 1) mark ++ stk⟩ := by
  induction' k with k ih generalizing rest stk
  · constructor
  · specialize ih rest (mark :: stk)
    convert ih.head _ using 1
    · simp +decide [replicate_add]
    · apply eq_any_step_read_a

private lemma eq_any_read_bs (k : ℕ) (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.seenB, replicate k b_ ++ rest, replicate k mark ++ stk⟩
      ⟨EqAnyState.seenB, rest, stk⟩ := by
  induction' k with k ih generalizing rest stk <;> simp_all +decide [List.replicate]
  · constructor
  · exact Reaches.trans (.single (eq_any_step_read_b _ _)) (ih _ _)

private lemma eq_any_read_cs_trail (k : ℕ) (rest : List (Fin 3)) :
    @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨trailC, replicate k c_ ++ rest, [bottom]⟩
      ⟨trailC, rest, [bottom]⟩ := by
  induction' k with k ih generalizing rest <;> simp_all +decide [List.replicate]
  · constructor
  · exact Reaches.trans (.single (eq_any_step_read_c_trail _)) (ih _)

private lemma eq_any_read_cs_only (k : ℕ) (rest : List (Fin 3)) :
    @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨onlyC, replicate k c_ ++ rest, [bottom]⟩
      ⟨onlyC, rest, [bottom]⟩ := by
  induction' k with k ih generalizing rest <;> simp_all +decide [List.replicate]
  · constructor
  · exact Reaches.trans (.single (eq_any_step_read_c_only _)) (ih _)

private lemma dpda_eq_any_complete (n m : ℕ) :
    replicate n a_ ++ replicate n b_ ++ replicate m c_ ∈ dpda_eq_any.acceptsByFinalState := by
  rcases n with _ | n
  · rcases m with _ | m
    · use EqAnyState.start
      refine ⟨by simp [DPDA.toPDA, dpda_eq_any], [bottom], ?_⟩
      change @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
        ⟨EqAnyState.start, [], [bottom]⟩ ⟨EqAnyState.start, [], [bottom]⟩
      rfl
    · use onlyC
      constructor
      · simp [DPDA.toPDA, dpda_eq_any]
      · use [bottom]
        convert
          Relation.ReflTransGen.trans
            (Relation.ReflTransGen.single (eq_any_step_read_c_init _))
            (eq_any_read_cs_only m []) using 1
        simp +decide [List.replicate]
  · use trailC
    constructor
    · simp [DPDA.toPDA, dpda_eq_any]
    · use [bottom]
      refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single (eq_any_step_read_a_init _)) ?_
      let restC := replicate m c_
      have h_as :
          @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
            ⟨EqAnyState.seenA, replicate n a_ ++ (replicate (n + 1) b_ ++ restC),
              [mark, bottom]⟩
            ⟨EqAnyState.seenA, replicate (n + 1) b_ ++ restC,
              replicate (n + 1) mark ++ [bottom]⟩ := by
        exact eq_any_read_as n (replicate (n + 1) b_ ++ restC) [bottom]
      have h_b0 :
          @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
            ⟨EqAnyState.seenA, replicate (n + 1) b_ ++ restC,
              replicate (n + 1) mark ++ [bottom]⟩
            ⟨EqAnyState.seenB, replicate n b_ ++ restC, replicate n mark ++ [bottom]⟩ := by
        convert Relation.ReflTransGen.single
          (eq_any_step_read_b_from_a (replicate n b_ ++ restC) (replicate n mark ++ [bottom])) using 1 <;>
          simp +decide [List.replicate]
      have h_bs :
          @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
            ⟨EqAnyState.seenB, replicate n b_ ++ restC, replicate n mark ++ [bottom]⟩
            ⟨EqAnyState.seenB, restC, [bottom]⟩ :=
        eq_any_read_bs n restC [bottom]
      have h_eps :
          @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
            ⟨EqAnyState.seenB, restC, [bottom]⟩
            ⟨trailC, restC, [bottom]⟩ :=
        Relation.ReflTransGen.single (eq_any_step_to_trail restC)
      have h_cs :
          @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
            ⟨trailC, restC, [bottom]⟩
            ⟨trailC, [], [bottom]⟩ := by
        simpa [restC] using eq_any_read_cs_trail m []
      convert
        Relation.ReflTransGen.trans h_as
          (Relation.ReflTransGen.trans h_b0
            (Relation.ReflTransGen.trans h_bs
              (Relation.ReflTransGen.trans h_eps h_cs))) using 1 ;
        simp +decide [List.replicate, List.append_assoc, restC]

private def EqAnyInv (w : List (Fin 3))
    (c : @PDA.conf EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA) : Prop :=
  ∃ na nb nc : ℕ,
    w = replicate na a_ ++ replicate nb b_ ++ replicate nc c_ ++ c.input ∧
    ((c.state = EqAnyState.start ∧ na = 0 ∧ nb = 0 ∧ nc = 0 ∧ c.stack = [bottom]) ∨
     (c.state = EqAnyState.seenA ∧ na ≥ 1 ∧ nb = 0 ∧ nc = 0 ∧
       c.stack = replicate na mark ++ [bottom]) ∨
     (c.state = EqAnyState.seenB ∧ na ≥ 1 ∧ 1 ≤ nb ∧ nb ≤ na ∧ nc = 0 ∧
       c.stack = replicate (na - nb) mark ++ [bottom]) ∨
     (c.state = trailC ∧ nb = na ∧ c.stack = [bottom]) ∨
     (c.state = onlyC ∧ na = 0 ∧ nb = 0 ∧ 1 ≤ nc ∧ c.stack = [bottom]))

private lemma eq_any_inv_step_state_start (w input : List (Fin 3))
    (c' : @PDA.conf EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA)
    (hw : w = input)
    (hstep : @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.start, input, [bottom]⟩ c') :
    EqAnyInv w c' := by
  rcases input with _ | ⟨x, rest⟩ <;> simp_all +decide [PDA.Reaches₁]
  · obtain ⟨p, β, hpβ, rfl⟩ := hstep
    simp_all +decide [dpda_eq_any, DPDA.toPDA]
  · fin_cases x <;> simp_all +decide [PDA.step, dpda_eq_any, DPDA.toPDA]
    · exact ⟨1, 0, 0, by simp [a_], by aesop⟩
    · exact ⟨0, 0, 1, by simp [c_], by aesop⟩

private lemma eq_any_inv_step_state_seenA (w : List (Fin 3)) (na : ℕ) (input : List (Fin 3))
    (c' : @PDA.conf EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA)
    (hna : na ≥ 1)
    (hw : w = replicate na a_ ++ input)
    (hstep : @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.seenA, input, replicate na mark ++ [bottom]⟩ c') :
    EqAnyInv w c' := by
  rcases na with _ | na
  · omega
  rcases input with _ | ⟨x, rest⟩
  · exfalso
    cases hstep
    rename_i p hp
    simp_all +decide [dpda_eq_any, DPDA.toPDA]
  · fin_cases x <;> simp_all +decide [PDA.Reaches₁, PDA.step, dpda_eq_any, DPDA.toPDA, List.replicate]
    · refine ⟨na + 2, 0, 0, ?_, ?_⟩
      · simp +decide [a_]
        simpa [a_, List.replicate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using replicate_append_cons_eq (na + 1) a_ rest
      · right; left
        simp +decide [List.replicate]
    · refine ⟨na + 1, 1, 0, ?_, ?_⟩
      · simp +decide [a_, b_, List.replicate, List.append_assoc]
      · right; right; left
        refine ⟨rfl, by omega, by omega, by omega, rfl, ?_⟩
        rw [Nat.add_sub_cancel]

private lemma eq_any_inv_step_state_seenB (w : List (Fin 3)) (na nb : ℕ)
    (input : List (Fin 3))
    (c' : @PDA.conf EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA)
    (hna : na ≥ 1) (hnb1 : 1 ≤ nb) (hnb2 : nb ≤ na)
    (hw : w = replicate na a_ ++ replicate nb b_ ++ input)
    (hstep : @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨EqAnyState.seenB, input, replicate (na - nb) mark ++ [bottom]⟩ c') :
    EqAnyInv w c' := by
  cases hsub : na - nb with
  | zero =>
      have hnb_eq : nb = na := by omega
      rcases input with _ | ⟨x, rest⟩ <;>
        simp_all +decide [PDA.Reaches₁, PDA.step, dpda_eq_any, DPDA.toPDA]
      · exact ⟨na, na, 0, by simpa [hnb_eq] using hw, by aesop⟩
      · exact ⟨na, na, 0, by simpa [hnb_eq] using hw, by aesop⟩
  | succ k =>
      rcases input with _ | ⟨x, rest⟩
      · exfalso
        unfold PDA.Reaches₁ PDA.step at hstep
        simp_all +decide [dpda_eq_any, DPDA.toPDA, List.replicate]
      · fin_cases x <;>
          simp_all +decide [PDA.Reaches₁, PDA.step, dpda_eq_any, DPDA.toPDA, List.replicate]
        refine ⟨na, nb + 1, 0, ?_, ?_⟩
        · simp +decide [b_, List.append_assoc]
          simpa [b_] using replicate_append_cons_eq nb b_ rest
        · right; right; left
          have hk : k = na - (nb + 1) := by omega
          refine ⟨rfl, hna, by omega, by omega, rfl, ?_⟩
          rw [hk]

private lemma eq_any_inv_step_state_trailC (w : List (Fin 3)) (na nc : ℕ)
    (input : List (Fin 3))
    (c' : @PDA.conf EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA)
    (hw : w = replicate na a_ ++ replicate na b_ ++ replicate nc c_ ++ input)
    (hstep : @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨trailC, input, [bottom]⟩ c') :
    EqAnyInv w c' := by
  rcases input with _ | ⟨x, rest⟩ <;> simp_all +decide [PDA.Reaches₁, PDA.step, dpda_eq_any, DPDA.toPDA]
  fin_cases x <;> simp_all +decide []
  · refine ⟨na, na, nc + 1, ?_, ?_⟩
    · simp +decide [c_, List.append_assoc]
      simpa [c_] using replicate_append_cons_eq nc c_ rest
    · right; right; right; left
      simp

private lemma eq_any_inv_step_state_onlyC (w : List (Fin 3)) (nc : ℕ)
    (input : List (Fin 3))
    (c' : @PDA.conf EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA)
    (_hnc : 1 ≤ nc)
    (hw : w = replicate nc c_ ++ input)
    (hstep : @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA
      ⟨onlyC, input, [bottom]⟩ c') :
    EqAnyInv w c' := by
  rcases input with _ | ⟨x, rest⟩ <;> simp_all +decide [PDA.Reaches₁, PDA.step, dpda_eq_any, DPDA.toPDA]
  fin_cases x <;> simp_all +decide []
  · refine ⟨0, 0, nc + 1, ?_, ?_⟩
    · simp +decide [c_]
      simpa [c_] using replicate_append_cons_eq nc c_ rest
    · right; right; right; right
      simp +arith

private lemma eq_any_inv_step (w : List (Fin 3))
    (c c' : @PDA.conf EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA)
    (hinv : EqAnyInv w c)
    (hstep : @PDA.Reaches₁ EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA c c') :
    EqAnyInv w c' := by
  rcases c with ⟨q, input, stack⟩
  obtain ⟨na, nb, nc, hw, hcases⟩ := hinv
  dsimp at hw hcases hstep
  rcases hcases with hstart | hseenA | hseenB | htrail | honly
  · rcases hstart with ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp at hw
    exact eq_any_inv_step_state_start w input c' hw hstep
  · rcases hseenA with ⟨rfl, hna, rfl, rfl, rfl⟩
    simp at hw
    exact eq_any_inv_step_state_seenA w na input c' hna hw hstep
  · rcases hseenB with ⟨rfl, hna, hnb1, hnb2, rfl, rfl⟩
    have hw' : w = replicate na a_ ++ replicate nb b_ ++ input := by
      simpa using hw
    exact eq_any_inv_step_state_seenB w na nb input c' hna hnb1 hnb2 hw' hstep
  · rcases htrail with ⟨rfl, hnb, rfl⟩
    subst nb
    exact eq_any_inv_step_state_trailC w na nc input c' hw hstep
  · rcases honly with ⟨rfl, rfl, rfl, hnc, rfl⟩
    simp at hw
    exact eq_any_inv_step_state_onlyC w nc input c' hnc hw hstep

private lemma eq_any_inv_reaches (w : List (Fin 3))
    (c c' : @PDA.conf EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA)
    (hinv : EqAnyInv w c)
    (hreach : @PDA.Reaches EqAnyState (Fin 3) ABCStack _ _ _ dpda_eq_any.toPDA c c') :
    EqAnyInv w c' := by
  induction hreach with
  | refl => exact hinv
  | tail _ hstep ih => exact eq_any_inv_step w _ _ ih hstep

private lemma dpda_eq_any_sound (w : List (Fin 3))
    (h : w ∈ dpda_eq_any.acceptsByFinalState) : w ∈ lang_eq_any := by
  obtain ⟨q, hq, γ, hreach⟩ := h
  obtain ⟨na, nb, nc, hw, hcases⟩ :=
    eq_any_inv_reaches w
      ⟨dpda_eq_any.toPDA.initial_state, w, [dpda_eq_any.toPDA.start_symbol]⟩
      ⟨q, [], γ⟩
      ⟨0, 0, 0, by aesop, by aesop⟩ hreach
  rcases hcases with hstart | hseenA | hseenB | htrail | honly
  · rcases hstart with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨0, 0, by simpa using hw⟩
  · rcases hseenA with ⟨rfl, _, _, _, _⟩
    simp [DPDA.toPDA, dpda_eq_any] at hq
  · rcases hseenB with ⟨rfl, _, _, _, _, _⟩
    simp [DPDA.toPDA, dpda_eq_any] at hq
  · rcases htrail with ⟨rfl, hnb, rfl⟩
    subst nb
    exact ⟨na, nc, by simpa [List.append_assoc] using hw⟩
  · rcases honly with ⟨rfl, rfl, rfl, _, rfl⟩
    exact ⟨0, nc, by simpa using hw⟩

/-- The `dpda_eq_any` automaton recognizes `{aⁿbⁿcᵐ | n,m ≥ 0}`. -/
public theorem dpda_eq_any_accepts : dpda_eq_any.acceptsByFinalState = lang_eq_any := by
  ext w
  constructor
  · exact dpda_eq_any_sound w
  · rintro ⟨n, m, rfl⟩
    exact dpda_eq_any_complete n m

/-- The first witness language `{aⁿbⁿcᵐ | n,m ≥ 0}` is deterministic context-free. -/
public theorem DCF_lang_eq_any : is_DCF lang_eq_any := by
  refine ⟨EqAnyState, ABCStack, inferInstance, inferInstance, dpda_eq_any, ?_⟩
  exact dpda_eq_any_accepts

end DCFLIntersection
