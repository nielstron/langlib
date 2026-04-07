import Mathlib
import Langlib.Automata.DeterministicPushdown.Definition
import Langlib.Classes.DeterministicContextFree.Definition
import Langlib.Classes.Regular.Basics.NonRegular

/-! # `a^n b^n` as a DCF

This file constructs a deterministic pushdown automaton for the language
`{a^n b^n | n >= 0}` and proves that this language is deterministic context-free.
-/

open PDA List

/-- DPDA recognizing `{aⁿbⁿ | n ≥ 0}` where `false = a` and `true = b`. -/
def dpda_anbn : DPDA (Fin 4) Bool Bool where
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
  exact Set.mem_union_left _ ⟨_, _, by aesop⟩

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
  constructor
  aesop (simp_config := { decide := true })

private lemma read_as (k : ℕ) (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, replicate k false ++ rest, true :: stk⟩
      ⟨1, rest, replicate (k + 1) true ++ stk⟩ := by
  induction' k with k ih generalizing rest stk
  · constructor
  · specialize ih rest (true :: stk)
    convert ih.head _ using 1
    · simp +decide [replicate_add]
    · apply step_read_a

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
    constructor
    · exact Or.inr rfl
    · use []
      convert
        Relation.ReflTransGen.trans (Relation.ReflTransGen.single (step_read_a_init _))
          (Relation.ReflTransGen.trans (read_as _ _ _) _) using 1
      convert
        Relation.ReflTransGen.trans (Relation.ReflTransGen.single (step_read_b_from1 _ _))
          (Relation.ReflTransGen.trans (read_bs _ _ _) (Relation.ReflTransGen.single step_epsilon_empty))
        using 1
      swap
      · exact n
      · simp +decide [List.replicate]

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
    simp_all +decide [DPDA.toPDA]
  · cases a <;> simp_all +decide [step]
    · rcases hstep with (⟨p, β, hp, rfl⟩ | ⟨p, β, hp, rfl⟩) <;> simp_all +decide [dpda_anbn]
      · simp_all +decide [DPDA.toPDA]
        exact ⟨1, 0, by aesop⟩
      · simp_all +decide [DPDA.toPDA]
    · cases hstep <;> simp_all +decide [dpda_anbn]
      · simp_all +decide [DPDA.toPDA]
      · simp_all +decide [DPDA.toPDA]

private lemma inv_step_state1 (w : List Bool) (na : ℕ) (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hna : na ≥ 1)
    (hw : w = replicate na false ++ input)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, input, replicate na true ++ [false]⟩ c') :
    AnBnInv w c' := by
  cases' input with a input'
  · rcases na with _ | _ | na <;> simp_all +decide
    · cases hstep
      rename_i q hq
      rcases hq with ⟨β, hβ₁, rfl⟩
      fin_cases q <;> simp_all +decide
      · cases hβ₁
      · cases hβ₁
      · cases hβ₁
      · cases hβ₁
    · cases hstep
      unfold dpda_anbn at *
      simp_all +decide
      rename_i k hk
      fin_cases k <;> simp_all +decide [DPDA.toPDA]
  · cases' na with na <;> simp_all +decide [List.replicate]
    cases' a with a a <;> simp_all +decide [Reaches₁]
    · unfold step at hstep
      unfold dpda_anbn at hstep
      simp_all +decide [PDA.transition_fun, PDA.transition_fun']
      unfold DPDA.toPDA at hstep
      simp_all +decide [List.replicate]
      use na + 2, 0
      exact Nat.recOn na (by simp +decide) fun n ihn => by simp +decide [List.replicate] at ihn ⊢; aesop
    · cases' hstep with h h <;> simp_all +decide [step]
      · unfold DPDA.toPDA at h
        simp_all +decide [dpda_anbn]
        use na + 1, 1
        simp +arith +decide [List.replicate]
      · obtain ⟨p, β, hp, rfl⟩ := h
        cases hp

private lemma inv_step_state2 (w : List Bool) (na nb : ℕ) (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hnb1 : 1 ≤ nb) (hnb2 : nb ≤ na)
    (hw : w = replicate na false ++ replicate nb true ++ input)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, input, replicate (na - nb) true ++ [false]⟩ c') :
    AnBnInv w c' := by
  unfold Reaches₁ at hstep
  unfold PDA.step at hstep
  cases input <;> cases h : na - nb <;> simp_all +decide [dpda_anbn]
  · unfold DPDA.toPDA at hstep
    simp_all +decide [dpda_anbn]
    use nb, nb
    rw [Nat.sub_eq_iff_eq_add] at h <;> aesop
  · cases hstep <;> simp_all +decide [dpda_anbn]
    unfold DPDA.toPDA at *
    simp_all +decide [PDA.transition_fun']
  · unfold DPDA.toPDA at *
    exact ⟨na, na, by rw [Nat.sub_eq_iff_eq_add] at h <;> aesop⟩
  · unfold DPDA.toPDA at hstep
    simp_all +decide [List.replicate]
    split_ifs at hstep <;> simp_all +decide [Set.mem_singleton_iff]
    refine ⟨na, nb + 1, ?_, ?_⟩ <;> simp_all +decide [Nat.sub_succ]
    · simp +decide [replicate_add, List.append_assoc]
    · omega

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
theorem dpda_anbn_accepts : dpda_anbn.acceptsByFinalState = anbn := by
  ext w
  exact ⟨dpda_anbn_sound w, fun ⟨n, hw⟩ => hw ▸ dpda_anbn_complete n⟩

/-- The language `{aⁿbⁿ}` is deterministic context-free. -/
theorem anbn_is_DCF : is_DCF anbn :=
  ⟨Fin 4, Bool, inferInstance, inferInstance, dpda_anbn, dpda_anbn_accepts⟩
