import Langlib.Classes.DeterministicContextFree.Examples.AnBnCm
import Langlib.Examples.AnBmCm

/-! # The deterministic context-free language `{a^n b^m c^m}`

This file gives a deterministic pushdown automaton for `{aⁿbᵐcᵐ | n,m ≥ 0}`
over the `Fin 3` alphabet shared with `AnBnCm`.
-/

open PDA List

namespace DCFLIntersection

inductive AnyEqState where
  | start
  | seenB
  | seenC
  | matched
  deriving DecidableEq, Fintype

open AnyEqState ABCStack

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

/-- DPDA recognizing `{aⁿbᵐcᵐ | n,m ≥ 0}`. -/
def dpda_any_eq : DPDA AnyEqState (Fin 3) ABCStack where
  initial_state := AnyEqState.start
  start_symbol := bottom
  final_states := {AnyEqState.start, matched}
  transition q x Z :=
    match q, x, Z with
    | AnyEqState.start, x, bottom =>
        if x = a_ then some (AnyEqState.start, [bottom])
        else if x = b_ then some (AnyEqState.seenB, [mark, bottom])
        else none
    | AnyEqState.seenB, x, mark =>
        if x = b_ then some (AnyEqState.seenB, [mark, mark])
        else if x = c_ then some (seenC, [])
        else none
    | seenC, x, mark =>
        if x = c_ then some (seenC, [])
        else none
    | _, _, _ => none
  epsilon_transition q Z :=
    match q, Z with
    | seenC, bottom => some (matched, [bottom])
    | _, _ => none
  no_mixed := by decide

private lemma any_eq_step_read_a_start (rest : List (Fin 3)) :
    @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨AnyEqState.start, a_ :: rest, [bottom]⟩
      ⟨AnyEqState.start, rest, [bottom]⟩ := by
  constructor
  unfold dpda_any_eq
  aesop

private lemma any_eq_step_read_b_start (rest : List (Fin 3)) :
    @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨AnyEqState.start, b_ :: rest, [bottom]⟩
      ⟨AnyEqState.seenB, rest, [mark, bottom]⟩ := by
  constructor
  unfold dpda_any_eq
  aesop

private lemma any_eq_step_read_b (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨AnyEqState.seenB, b_ :: rest, mark :: stk⟩
      ⟨AnyEqState.seenB, rest, mark :: mark :: stk⟩ := by
  constructor
  unfold dpda_any_eq
  aesop

private lemma any_eq_step_read_c_from_b (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨AnyEqState.seenB, c_ :: rest, mark :: stk⟩
      ⟨seenC, rest, stk⟩ := by
  constructor
  unfold dpda_any_eq
  aesop

private lemma any_eq_step_read_c (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨seenC, c_ :: rest, mark :: stk⟩
      ⟨seenC, rest, stk⟩ := by
  constructor
  unfold dpda_any_eq
  aesop

private lemma any_eq_step_to_matched (rest : List (Fin 3)) :
    @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨seenC, rest, [bottom]⟩
      ⟨matched, rest, [bottom]⟩ := by
  cases rest <;> simp +decide [PDA.Reaches₁, PDA.step, dpda_any_eq, DPDA.toPDA]

private lemma any_eq_read_as (k : ℕ) (rest : List (Fin 3)) :
    @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨AnyEqState.start, replicate k a_ ++ rest, [bottom]⟩
      ⟨AnyEqState.start, rest, [bottom]⟩ := by
  induction' k with k ih generalizing rest <;> simp_all +decide [List.replicate]
  · constructor
  · exact Reaches.trans (.single (any_eq_step_read_a_start _)) (ih _)

private lemma any_eq_read_bs (k : ℕ) (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨AnyEqState.seenB, replicate k b_ ++ rest, mark :: stk⟩
      ⟨AnyEqState.seenB, rest, replicate k mark ++ mark :: stk⟩ := by
  induction' k with k ih generalizing rest stk
  · constructor
  · specialize ih rest (mark :: stk)
    convert ih.head _ using 1
    · simp +decide [replicate_add]
    · apply any_eq_step_read_b

private lemma any_eq_read_cs (k : ℕ) (rest : List (Fin 3)) (stk : List ABCStack) :
    @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨seenC, replicate k c_ ++ rest, replicate k mark ++ stk⟩
      ⟨seenC, rest, stk⟩ := by
  induction' k with k ih generalizing rest stk <;> simp_all +decide [List.replicate]
  · constructor
  · exact Reaches.trans (.single (any_eq_step_read_c _ _)) (ih _ _)

private lemma dpda_any_eq_complete (n m : ℕ) :
    replicate n a_ ++ replicate m b_ ++ replicate m c_ ∈ dpda_any_eq.acceptsByFinalState := by
  rcases m with _ | m
  · use AnyEqState.start
    refine ⟨by simp [DPDA.toPDA, dpda_any_eq], [bottom], ?_⟩
    simpa [DPDA.toPDA, dpda_any_eq, List.replicate] using any_eq_read_as n []
  · use matched
    constructor
    · simp [DPDA.toPDA, dpda_any_eq]
    · use [bottom]
      change @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
        ⟨AnyEqState.start,
          replicate n a_ ++ replicate (m + 1) b_ ++ replicate (m + 1) c_,
          [bottom]⟩
        ⟨matched, [], [bottom]⟩
      let restC := replicate (m + 1) c_
      have h_as :
          @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
            ⟨AnyEqState.start, replicate n a_ ++ (replicate (m + 1) b_ ++ restC), [bottom]⟩
            ⟨AnyEqState.start, replicate (m + 1) b_ ++ restC, [bottom]⟩ :=
        any_eq_read_as n (replicate (m + 1) b_ ++ restC)
      have h_b0 :
          @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
            ⟨AnyEqState.start, replicate (m + 1) b_ ++ restC, [bottom]⟩
            ⟨AnyEqState.seenB, replicate m b_ ++ restC, [mark, bottom]⟩ := by
        convert Relation.ReflTransGen.single (any_eq_step_read_b_start (replicate m b_ ++ restC)) using 1 <;>
          simp +decide [List.replicate]
      have h_bs :
          @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
            ⟨AnyEqState.seenB, replicate m b_ ++ restC, [mark, bottom]⟩
            ⟨AnyEqState.seenB, restC, replicate m mark ++ [mark, bottom]⟩ :=
        any_eq_read_bs m restC [bottom]
      have h_c0 :
          @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
            ⟨AnyEqState.seenB, restC, replicate m mark ++ [mark, bottom]⟩
            ⟨seenC, replicate m c_, replicate m mark ++ [bottom]⟩ := by
        convert Relation.ReflTransGen.single
          (any_eq_step_read_c_from_b (replicate m c_) (replicate m mark ++ [bottom])) using 1
        · simp +decide [List.replicate, restC]
          simpa [List.append_assoc] using replicate_append_cons_self m mark [bottom]
      have h_cs :
          @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
            ⟨seenC, replicate m c_, replicate m mark ++ [bottom]⟩
            ⟨seenC, [], [bottom]⟩ :=
        by simpa using any_eq_read_cs m [] [bottom]
      have h_eps :
          @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
            ⟨seenC, [], [bottom]⟩ ⟨matched, [], [bottom]⟩ :=
        Relation.ReflTransGen.single (any_eq_step_to_matched [])
      convert
        Relation.ReflTransGen.trans h_as
          (Relation.ReflTransGen.trans h_b0
            (Relation.ReflTransGen.trans h_bs
              (Relation.ReflTransGen.trans h_c0
                (Relation.ReflTransGen.trans h_cs h_eps)))) using 1 <;>
        simp +decide [List.append_assoc, restC]

private def AnyEqInv (w : List (Fin 3))
    (c : @PDA.conf AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA) : Prop :=
  ∃ na nb nc : ℕ,
    w = replicate na a_ ++ replicate nb b_ ++ replicate nc c_ ++ c.input ∧
    ((c.state = AnyEqState.start ∧ nb = 0 ∧ nc = 0 ∧ c.stack = [bottom]) ∨
     (c.state = AnyEqState.seenB ∧ 1 ≤ nb ∧ nc = 0 ∧
       c.stack = replicate nb mark ++ [bottom]) ∨
     (c.state = seenC ∧ 1 ≤ nc ∧ nc ≤ nb ∧
       c.stack = replicate (nb - nc) mark ++ [bottom]) ∨
     (c.state = matched ∧ nc = nb ∧ c.stack = [bottom]))

private lemma any_eq_inv_step_state_start (w input : List (Fin 3))
    (c' : @PDA.conf AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA)
    (na : ℕ)
    (hw : w = replicate na a_ ++ input)
    (hstep : @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨AnyEqState.start, input, [bottom]⟩ c') :
    AnyEqInv w c' := by
  rcases input with _ | ⟨x, rest⟩
  · exfalso
    unfold PDA.Reaches₁ PDA.step at hstep
    simp_all +decide [dpda_any_eq, DPDA.toPDA]
  · fin_cases x <;> simp_all +decide [PDA.Reaches₁, PDA.step, dpda_any_eq, DPDA.toPDA]
    · refine ⟨na + 1, 0, 0, ?_, ?_⟩
      · simp +decide [a_, List.append_assoc]
        simpa [a_] using replicate_append_cons_eq na a_ rest
      · left
        simp
    · refine ⟨na, 1, 0, ?_, ?_⟩
      · simp +decide [b_, List.append_assoc]
      · right; left
        simp

private lemma any_eq_inv_step_state_seenB (w : List (Fin 3)) (na nb : ℕ)
    (input : List (Fin 3))
    (c' : @PDA.conf AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA)
    (hnb : 1 ≤ nb)
    (hw : w = replicate na a_ ++ replicate nb b_ ++ input)
    (hstep : @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨AnyEqState.seenB, input, replicate nb mark ++ [bottom]⟩ c') :
    AnyEqInv w c' := by
  rcases nb with _ | nb
  · omega
  rcases input with _ | ⟨x, rest⟩
  · exfalso
    unfold PDA.Reaches₁ PDA.step at hstep
    simp_all +decide [dpda_any_eq, DPDA.toPDA, List.replicate]
  · fin_cases x <;> simp_all +decide [PDA.Reaches₁, PDA.step, dpda_any_eq, DPDA.toPDA, List.replicate]
    · refine ⟨na, nb + 2, 0, ?_, ?_⟩
      · simp +decide [b_, List.append_assoc]
        simpa [b_, List.replicate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using replicate_append_cons_eq (nb + 1) b_ rest
      · right; left
        simp +arith [List.replicate]
    · refine ⟨na, nb + 1, 1, ?_, ?_⟩
      · simp +decide [c_, List.append_assoc]
        simp [b_, List.replicate]
      · right; right; left
        simp +arith

private lemma any_eq_inv_step_state_seenC (w : List (Fin 3)) (na nb nc : ℕ)
    (input : List (Fin 3))
    (c' : @PDA.conf AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA)
    (hnc1 : 1 ≤ nc) (hnc2 : nc ≤ nb)
    (hw : w = replicate na a_ ++ replicate nb b_ ++ replicate nc c_ ++ input)
    (hstep : @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨seenC, input, replicate (nb - nc) mark ++ [bottom]⟩ c') :
    AnyEqInv w c' := by
  cases hsub : nb - nc with
  | zero =>
      have hnc_eq : nc = nb := by omega
      rcases input with _ | ⟨x, rest⟩ <;>
        simp_all +decide [PDA.Reaches₁, PDA.step, dpda_any_eq, DPDA.toPDA]
      · exact ⟨na, nb, nb, by simpa [hnc_eq] using hw, by aesop⟩
      · exact ⟨na, nb, nb, by simpa [hnc_eq] using hw, by aesop⟩
  | succ k =>
      rcases input with _ | ⟨x, rest⟩
      · exfalso
        unfold PDA.Reaches₁ PDA.step at hstep
        simp_all +decide [dpda_any_eq, DPDA.toPDA, List.replicate]
      · fin_cases x <;>
          simp_all +decide [PDA.Reaches₁, PDA.step, dpda_any_eq, DPDA.toPDA, List.replicate]
        refine ⟨na, nb, nc + 1, ?_, ?_⟩
        · simp +decide [c_, List.append_assoc]
          simpa [c_] using replicate_append_cons_eq nc c_ rest
        · right; right; left
          have hk : k = nb - (nc + 1) := by omega
          refine ⟨rfl, by omega, by omega, ?_⟩
          rw [hk]

private lemma any_eq_inv_step_state_matched (input : List (Fin 3))
    (c' : @PDA.conf AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA)
    (hstep : @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA
      ⟨matched, input, [bottom]⟩ c') :
    False := by
  rcases input with _ | ⟨x, rest⟩ <;>
    simp_all +decide [PDA.Reaches₁, PDA.step, dpda_any_eq, DPDA.toPDA]

private lemma any_eq_inv_step (w : List (Fin 3))
    (c c' : @PDA.conf AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA)
    (hinv : AnyEqInv w c)
    (hstep : @PDA.Reaches₁ AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA c c') :
    AnyEqInv w c' := by
  rcases c with ⟨q, input, stack⟩
  obtain ⟨na, nb, nc, hw, hcases⟩ := hinv
  dsimp at hw hcases hstep
  rcases hcases with hstart | hseenB | hseenC | hmatched
  · rcases hstart with ⟨rfl, rfl, rfl, rfl⟩
    simp at hw
    exact any_eq_inv_step_state_start w input c' na hw hstep
  · rcases hseenB with ⟨rfl, hnb, rfl, rfl⟩
    have hw' : w = replicate na a_ ++ replicate nb b_ ++ input := by
      simpa using hw
    exact any_eq_inv_step_state_seenB w na nb input c' hnb hw' hstep
  · rcases hseenC with ⟨rfl, hnc1, hnc2, rfl⟩
    exact any_eq_inv_step_state_seenC w na nb nc input c' hnc1 hnc2 hw hstep
  · rcases hmatched with ⟨rfl, _, rfl⟩
    exact False.elim (any_eq_inv_step_state_matched input c' hstep)

private lemma any_eq_inv_reaches (w : List (Fin 3))
    (c c' : @PDA.conf AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA)
    (hinv : AnyEqInv w c)
    (hreach : @PDA.Reaches AnyEqState (Fin 3) ABCStack _ _ _ dpda_any_eq.toPDA c c') :
    AnyEqInv w c' := by
  induction hreach with
  | refl => exact hinv
  | tail _ hstep ih => exact any_eq_inv_step w _ _ ih hstep

private lemma dpda_any_eq_sound (w : List (Fin 3))
    (h : w ∈ dpda_any_eq.acceptsByFinalState) : w ∈ lang_any_eq := by
  obtain ⟨q, hq, γ, hreach⟩ := h
  obtain ⟨na, nb, nc, hw, hcases⟩ :=
    any_eq_inv_reaches w
      ⟨dpda_any_eq.toPDA.initial_state, w, [dpda_any_eq.toPDA.start_symbol]⟩
      ⟨q, [], γ⟩
      ⟨0, 0, 0, by aesop, by aesop⟩ hreach
  rcases hcases with hstart | hseenB | hseenC | hmatched
  · rcases hstart with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨na, 0, by simpa using hw⟩
  · rcases hseenB with ⟨rfl, _, _, _⟩
    simp [DPDA.toPDA, dpda_any_eq] at hq
  · rcases hseenC with ⟨rfl, _, _, _⟩
    simp [DPDA.toPDA, dpda_any_eq] at hq
  · rcases hmatched with ⟨rfl, hnc, rfl⟩
    subst nc
    exact ⟨na, nb, by simpa [List.append_assoc] using hw⟩

/-- The second witness language `{aⁿbᵐcᵐ | n,m ≥ 0}` is deterministic context-free. -/
theorem DCF_lang_any_eq : is_DCF lang_any_eq := by
  refine ⟨AnyEqState, ABCStack, inferInstance, inferInstance, dpda_any_eq, ?_⟩
  ext w
  constructor
  · exact dpda_any_eq_sound w
  · rintro ⟨n, m, rfl⟩
    exact dpda_any_eq_complete n m


end DCFLIntersection
