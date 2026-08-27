module

public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Examples.AnBn
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Cases
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
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



/-! # `a^n b^n` as a DCF

This file constructs a deterministic pushdown automaton for the language
`{a^n b^n | n >= 0}` and proves that this language is deterministic context-free.
-/

open PDA List

/-- DPDA recognizing `{aⁿbⁿ | n ≥ 0}` where `false = a` and `true = b`. -/
public def dpda_anbn : DPDA (Fin 4) Bool Bool where
  initial_state := 0
  start_symbol := false
  final_states := {(0 : Fin 4), (3 : Fin 4)}
  transition q a Z :=
    if q = (0 : Fin 4) ∧ a = false ∧ Z = false then some ((1 : Fin 4), [true, false])
    else if q = (1 : Fin 4) ∧ a = false ∧ Z = true then some ((1 : Fin 4), [true, true])
    else if q = (1 : Fin 4) ∧ a = true ∧ Z = true then some ((2 : Fin 4), [])
    else if q = (2 : Fin 4) ∧ a = true ∧ Z = true then some ((2 : Fin 4), [])
    else none
  epsilon_transition q Z :=
    if q = (2 : Fin 4) ∧ Z = false then some ((3 : Fin 4), [])
    else none
  no_mixed := by decide

private lemma step_read_a_init (rest : List Bool) :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨0, false :: rest, [false]⟩ ⟨1, rest, [true, false]⟩ := by
  constructor
  unfold PDA.transition_fun
  aesop

private lemma step_read_a (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, false :: rest, true :: stk⟩ ⟨1, rest, true :: true :: stk⟩ := by
  unfold PDA.Reaches₁ PDA.step
  apply Set.mem_union_left
  refine ⟨1, [true, true], ?_, rfl⟩
  unfold DPDA.toPDA dpda_anbn
  exact Set.mem_singleton _

private lemma step_read_b_from1 (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, true :: rest, true :: stk⟩ ⟨2, rest, stk⟩ := by
  constructor
  unfold dpda_anbn
  aesop

private lemma step_read_b (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, true :: rest, true :: stk⟩ ⟨2, rest, stk⟩ := by
  constructor
  unfold dpda_anbn
  aesop

private lemma step_epsilon_empty :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, [], [false]⟩ ⟨3, [], []⟩ := by
  unfold PDA.Reaches₁ PDA.step
  refine ⟨3, [], ?_, rfl⟩
  unfold DPDA.toPDA dpda_anbn
  exact Set.mem_singleton _

private lemma read_as (k : ℕ) (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, replicate k false ++ rest, true :: stk⟩
      ⟨1, rest, replicate (k + 1) true ++ stk⟩ := by
  induction k generalizing rest stk with
  | zero => exact Reaches.refl _
  | succ k ih =>
      have hfirst := Relation.ReflTransGen.single
        (step_read_a (replicate k false ++ rest) stk)
      have hrest := ih rest (true :: stk)
      have hstack : replicate (k + 1) true ++ true :: stk =
          replicate (k.succ + 1) true ++ stk := by
        have hrepl : replicate (k.succ + 1) true =
            replicate (k + 1) true ++ [true] := by
          rw [show k.succ + 1 = (k + 1) + 1 by omega, List.replicate_succ']
        rw [hrepl, List.append_assoc]
        rfl
      have hinput : replicate k.succ false ++ rest =
          false :: (replicate k false ++ rest) := by simp [List.replicate_succ]
      change Relation.ReflTransGen (@PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
        ⟨1, replicate k.succ false ++ rest, true :: stk⟩
        ⟨1, rest, replicate (k.succ + 1) true ++ stk⟩
      rw [hinput, ← hstack]
      exact hfirst.trans hrest

private lemma read_bs (k : ℕ) (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, replicate k true ++ rest, replicate k true ++ stk⟩
      ⟨2, rest, stk⟩ := by
  induction' k with k ih generalizing rest stk <;> simp_all +decide [List.replicate]
  · constructor
  · exact Reaches.trans (.single (step_read_b _ _)) (ih _ _)

private lemma dpda_anbn_complete (n : ℕ) :
    replicate n false ++ replicate n true ∈ dpda_anbn.acceptsByFinalState := by
  rcases n with _ | n <;> simp_all +decide [List.replicate]
  · use 0
    exact ⟨by tauto, [false], by tauto⟩
  · use 3
    simp +decide [dpda_anbn]
    refine ⟨[], ?_⟩
    change Relation.ReflTransGen (@PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
      ⟨0, false :: (replicate n false ++ true :: replicate n true), [false]⟩ ⟨3, [], []⟩
    have h₁ := Relation.ReflTransGen.single
      (step_read_a_init (replicate n false ++ replicate (n + 1) true))
    have h₂ := read_as n (replicate (n + 1) true) [false]
    have h₃ := Relation.ReflTransGen.single
      (step_read_b_from1 (replicate n true) (replicate n true ++ [false]))
    have h₄ : @PDA.Reaches (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
        ⟨2, replicate n true, replicate n true ++ [false]⟩ ⟨2, [], [false]⟩ := by
      simpa using read_bs n [] [false]
    have h₅ := Relation.ReflTransGen.single step_epsilon_empty
    simpa [List.replicate_succ, List.append_assoc, Nat.succ_eq_add_one] using
      h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

private def AnBnInv (w : List Bool)
    (c : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA) : Prop :=
  ∃ na nb : ℕ,
    w = replicate na false ++ replicate nb true ++ c.input ∧
    ((c.state = (0 : Fin 4) ∧ na = 0 ∧ nb = 0 ∧ c.stack = [false]) ∨
     (c.state = (1 : Fin 4) ∧ na ≥ 1 ∧ nb = 0 ∧ c.stack = replicate na true ++ [false]) ∨
     (c.state = (2 : Fin 4) ∧ 1 ≤ nb ∧ nb ≤ na ∧
       c.stack = replicate (na - nb) true ++ [false]) ∨
     (c.state = (3 : Fin 4) ∧ nb = na ∧ c.stack = []))

private lemma no_step_state3 (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨3, input, []⟩ c') : False := by
  cases input <;> cases c' <;> cases hstep

private lemma inv_step_state0 (w : List Bool) (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hw : w = input)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨0, input, [false]⟩ c') :
    AnBnInv w c' := by
  rcases input with _ | ⟨a, rest⟩ <;> simp_all +decide [PDA.Reaches₁]
  · obtain ⟨p, β, hpβ, rfl⟩ := hstep
    unfold dpda_anbn at hpβ
    simp_all +decide
  · cases a
    · rcases hstep with (⟨p, β, hp, rfl⟩ | ⟨p, β, hp, rfl⟩) <;> simp_all +decide [dpda_anbn]
      · simp_all +decide [DPDA.toPDA]
        exact ⟨1, 0, by aesop⟩
    · cases hstep <;> simp_all +decide [dpda_anbn]

private lemma inv_step_state1 (w : List Bool) (na : ℕ) (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hna : na ≥ 1)
    (hw : w = replicate na false ++ input)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, input, replicate na true ++ [false]⟩ c') :
    AnBnInv w c' := by
  classical
  cases na with
  | zero => omega
  | succ k =>
      simp only [List.replicate_succ, List.cons_append] at hstep
      cases input with
      | nil =>
          unfold Reaches₁ step at hstep
          rcases hstep with ⟨p, β, htrans, _⟩
          change (p, β) ∈ (∅ : Set ((Fin 4) × List Bool)) at htrans
          exact ((Set.mem_empty_iff_false _).mp htrans).elim
      | cons a input' =>
          unfold Reaches₁ step at hstep
          rw [Set.mem_union] at hstep
          rcases hstep with hread | heps
          · rcases hread with ⟨p, β, htrans, hc⟩
            cases a
            · change (p, β) ∈ ({((1 : Fin 4), [true, true])} : Set ((Fin 4) × List Bool)) at htrans
              rw [Set.mem_singleton_iff] at htrans
              have hp := congrArg Prod.fst htrans
              have hβ := congrArg Prod.snd htrans
              simp only at hp hβ
              subst p
              subst β
              subst c'
              refine ⟨k + 2, 0, ?_, Or.inr <| Or.inl ⟨rfl, by omega, rfl, ?_⟩⟩
              · simpa [replicate_add, List.append_assoc] using hw
              · rw [show k + 2 = 2 + k by omega, replicate_add]
                simp
            · change (p, β) ∈ ({((2 : Fin 4), [])} : Set ((Fin 4) × List Bool)) at htrans
              rw [Set.mem_singleton_iff] at htrans
              have hp := congrArg Prod.fst htrans
              have hβ := congrArg Prod.snd htrans
              simp only at hp hβ
              subst p
              subst β
              subst c'
              refine ⟨k + 1, 1, ?_, Or.inr <| Or.inr <| Or.inl ⟨rfl, by omega, by omega, ?_⟩⟩
              · simpa [replicate_add, List.append_assoc] using hw
              · simp
          · rcases heps with ⟨p, β, htrans, _⟩
            change (p, β) ∈ (∅ : Set ((Fin 4) × List Bool)) at htrans
            exact ((Set.mem_empty_iff_false _).mp htrans).elim

private lemma inv_step_state2 (w : List Bool) (na nb : ℕ) (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hnb1 : 1 ≤ nb) (hnb2 : nb ≤ na)
    (hw : w = replicate na false ++ replicate nb true ++ input)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, input, replicate (na - nb) true ++ [false]⟩ c') :
    AnBnInv w c' := by
  classical
  unfold Reaches₁ step at hstep
  cases hdiff : na - nb with
  | zero =>
      simp only [hdiff, List.replicate_zero, List.nil_append] at hstep
      have hna : na = nb := by omega
      cases input with
      | nil =>
          rcases hstep with ⟨p, β, htrans, hc⟩
          change (p, β) ∈ ({((3 : Fin 4), [])} : Set ((Fin 4) × List Bool)) at htrans
          rw [Set.mem_singleton_iff] at htrans
          have hp := congrArg Prod.fst htrans
          have hβ := congrArg Prod.snd htrans
          simp only at hp hβ
          subst p
          subst β
          subst c'
          exact ⟨na, nb, hw, Or.inr <| Or.inr <| Or.inr ⟨rfl, hna.symm, rfl⟩⟩
      | cons a input' =>
          rw [Set.mem_union] at hstep
          rcases hstep with hread | heps
          · rcases hread with ⟨p, β, htrans, _⟩
            cases a <;> change (p, β) ∈ (∅ : Set ((Fin 4) × List Bool)) at htrans
            all_goals exact ((Set.mem_empty_iff_false _).mp htrans).elim
          · rcases heps with ⟨p, β, htrans, hc⟩
            change (p, β) ∈ ({((3 : Fin 4), [])} : Set ((Fin 4) × List Bool)) at htrans
            rw [Set.mem_singleton_iff] at htrans
            have hp := congrArg Prod.fst htrans
            have hβ := congrArg Prod.snd htrans
            simp only at hp hβ
            subst p
            subst β
            subst c'
            exact ⟨na, nb, hw, Or.inr <| Or.inr <| Or.inr ⟨rfl, hna.symm, rfl⟩⟩
  | succ k =>
      simp only [hdiff, List.replicate_succ, List.cons_append] at hstep
      cases input with
      | nil =>
          rcases hstep with ⟨p, β, htrans, _⟩
          change (p, β) ∈ (∅ : Set ((Fin 4) × List Bool)) at htrans
          exact ((Set.mem_empty_iff_false _).mp htrans).elim
      | cons a input' =>
          rw [Set.mem_union] at hstep
          rcases hstep with hread | heps
          · rcases hread with ⟨p, β, htrans, hc⟩
            cases a
            · change (p, β) ∈ (∅ : Set ((Fin 4) × List Bool)) at htrans
              exact ((Set.mem_empty_iff_false _).mp htrans).elim
            · change (p, β) ∈ ({((2 : Fin 4), [])} : Set ((Fin 4) × List Bool)) at htrans
              rw [Set.mem_singleton_iff] at htrans
              have hp := congrArg Prod.fst htrans
              have hβ := congrArg Prod.snd htrans
              simp only at hp hβ
              subst p
              subst β
              subst c'
              have hdiff' : na - (nb + 1) = k := by omega
              refine ⟨na, nb + 1, ?_, Or.inr <| Or.inr <| Or.inl ⟨rfl, by omega, by omega, ?_⟩⟩
              · simpa [replicate_add, List.append_assoc] using hw
              · simp [hdiff']
          · rcases heps with ⟨p, β, htrans, _⟩
            change (p, β) ∈ (∅ : Set ((Fin 4) × List Bool)) at htrans
            exact ((Set.mem_empty_iff_false _).mp htrans).elim

private lemma inv_step (w : List Bool)
    (c c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hinv : AnBnInv w c) (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA c c') :
    AnBnInv w c' := by
  rcases c with ⟨q, inp, stk⟩
  obtain ⟨na, nb, hw, hcases⟩ := hinv
  dsimp at hw hcases hstep
  rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hna, rfl, rfl⟩ | ⟨rfl, hnb1, hnb2, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp at hw
    exact inv_step_state0 w inp c' hw hstep
  · simp at hw
    exact inv_step_state1 w na inp c' hna hw hstep
  · exact inv_step_state2 w na nb inp c' hnb1 hnb2 hw hstep
  · exact absurd hstep (fun h => no_step_state3 inp c' h)

private lemma inv_reaches (w : List Bool)
    (c c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hinv : AnBnInv w c)
    (hreach : @PDA.Reaches (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA c c') :
    AnBnInv w c' := by
  induction hreach with
  | refl => exact hinv
  | tail _ hstep ih => exact inv_step w _ _ ih hstep

private lemma dpda_anbn_sound (w : List Bool)
    (h : w ∈ dpda_anbn.acceptsByFinalState) : w ∈ anbn := by
  obtain ⟨q, hq, γ, hreach⟩ := h
  obtain ⟨na, nb, hw, hcases⟩ :=
    inv_reaches w ⟨dpda_anbn.toPDA.initial_state, w, [dpda_anbn.toPDA.start_symbol]⟩ ⟨q, [], γ⟩
      ⟨0, 0, by aesop⟩ hreach
  fin_cases q <;> simp_all +decide [anbn]
  · exists 0
  · cases hq
    · contradiction
    · contradiction
  · cases hq
    · contradiction
    · contradiction
  · exact ⟨na, rfl⟩

/-- The DPDA `dpda_anbn` accepts exactly the language `{aⁿbⁿ}`. -/
public theorem dpda_anbn_accepts : dpda_anbn.acceptsByFinalState = anbn := by
  ext w
  exact ⟨dpda_anbn_sound w, fun ⟨n, hw⟩ => hw ▸ dpda_anbn_complete n⟩

/-- The language `{aⁿbⁿ}` is deterministic context-free. -/
public theorem anbn_is_DCF : is_DCF anbn :=
  ⟨Fin 4, Bool, inferInstance, inferInstance, dpda_anbn, dpda_anbn_accepts⟩
