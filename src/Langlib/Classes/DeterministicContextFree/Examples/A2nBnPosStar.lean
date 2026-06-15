module

public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Examples.A2nBnPosStar
import Mathlib.Tactic

/-!
# The `{a^(2n)b^n | n >= 1}*` Language as a DCF

This file builds the deterministic pushdown automaton for the numerator witness
used in the right-quotient counterexample, with `false = a` and `true = b`.
-/

open PDA

namespace DCFA2nBnPosStar

private inductive NumState where
  | boundary
  | oddA
  | evenA
  | readB
deriving DecidableEq, Fintype

private inductive NumStack where
  | bottom
  | pair
deriving DecidableEq, Fintype

private def transition : NumState → Bool → NumStack →
    Option (NumState × List NumStack)
  | .boundary, false, .bottom => some (.oddA, [.bottom])
  | .oddA, false, .bottom => some (.evenA, [.pair, .bottom])
  | .oddA, false, .pair => some (.evenA, [.pair, .pair])
  | .evenA, false, Z => some (.oddA, [Z])
  | .evenA, true, .pair => some (.readB, [])
  | .readB, true, .pair => some (.readB, [])
  | _, _, _ => none

private def epsilon : NumState → NumStack → Option (NumState × List NumStack)
  | .readB, .bottom => some (.boundary, [.bottom])
  | _, _ => none

private def dpda_quotientNumerator : DPDA NumState Bool NumStack where
  initial_state := .boundary
  start_symbol := .bottom
  final_states := {.boundary}
  transition := transition
  epsilon_transition := epsilon
  no_mixed := by
    intro q Z hε a
    cases q <;> cases Z <;> cases a <;> simp [epsilon, transition] at hε ⊢

private lemma step_boundary_false (rest : List Bool) :
    @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.boundary, false :: rest, [.bottom]⟩
      ⟨.oddA, rest, [.bottom]⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition]

private lemma step_odd_false_bottom (rest : List Bool) :
    @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.oddA, false :: rest, [.bottom]⟩
      ⟨.evenA, rest, [.pair, .bottom]⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition]

private lemma step_odd_false_pair (rest : List Bool) (stk : List NumStack) :
    @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.oddA, false :: rest, .pair :: stk⟩
      ⟨.evenA, rest, .pair :: .pair :: stk⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition]

private lemma step_even_false (rest : List Bool) (Z : NumStack) (stk : List NumStack) :
    @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.evenA, false :: rest, Z :: stk⟩
      ⟨.oddA, rest, Z :: stk⟩ := by
  cases Z <;> simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition]

private lemma step_even_true_pair (rest : List Bool) (stk : List NumStack) :
    @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.evenA, true :: rest, .pair :: stk⟩
      ⟨.readB, rest, stk⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition]

private lemma step_readB_true_pair (rest : List Bool) (stk : List NumStack) :
    @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.readB, true :: rest, .pair :: stk⟩
      ⟨.readB, rest, stk⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition]

private lemma step_readB_bottom (rest : List Bool) :
    @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.readB, rest, [.bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  cases rest <;> simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, epsilon]

private lemma replicate_two_mul_succ_false (n : ℕ) :
    List.replicate (2 * (n + 1)) false =
      false :: false :: List.replicate (2 * n) false := by
  have h : 2 * (n + 1) = 2 + 2 * n := by omega
  rw [h, List.replicate_add]
  simp [List.replicate]

private lemma replicate_pair_append_cons (n : ℕ) (stk : List NumStack) :
    List.replicate n NumStack.pair ++ NumStack.pair :: stk =
      NumStack.pair :: List.replicate n NumStack.pair ++ stk := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons NumStack.pair) ih

private lemma replicate_succ_false_append (n : ℕ) :
    List.replicate (n + 1) false = List.replicate n false ++ [false] := by
  rw [List.replicate_add]
  simp

private lemma replicate_two_mul_succ_false_append (m : ℕ) :
    List.replicate (2 * (m + 1)) false =
      List.replicate (2 * m + 1) false ++ [false] := by
  have h : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
  rw [h, replicate_succ_false_append]

private lemma read_more_a_pairs (n : ℕ) (rest : List Bool) (stk : List NumStack) :
    @PDA.Reaches NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.evenA, List.replicate (2 * n) false ++ rest, .pair :: stk⟩
      ⟨.evenA, rest, List.replicate n .pair ++ .pair :: stk⟩ := by
  induction n generalizing rest stk with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      rw [replicate_two_mul_succ_false]
      simp only [List.cons_append]
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (step_even_false _ .pair stk))
        (Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (step_odd_false_pair _ stk))
          (by
            simpa [List.replicate_succ, List.append_assoc, replicate_pair_append_cons] using
              ih rest (.pair :: stk)))

private lemma read_b_pairs (n : ℕ) (rest : List Bool) (stk : List NumStack) :
    @PDA.Reaches NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.readB, List.replicate n true ++ rest, List.replicate n .pair ++ stk⟩
      ⟨.readB, rest, stk⟩ := by
  induction n generalizing rest stk with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (step_readB_true_pair _ _))
        (by simpa [List.append_assoc] using ih rest stk)

private lemma finish_left_block (n : ℕ) (rest : List Bool) :
    @PDA.Reaches NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.evenA, List.replicate (n + 1) true ++ rest,
        List.replicate n .pair ++ [.pair, .bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  rw [List.replicate_succ, List.cons_append, replicate_pair_append_cons n [.bottom]]
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (step_even_true_pair _ _))
    (Relation.ReflTransGen.trans
      (read_b_pairs n rest [.bottom])
      (Relation.ReflTransGen.single (step_readB_bottom rest)))

private lemma run_left_block (n : ℕ) (rest : List Bool) :
    @PDA.Reaches NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.boundary,
        List.replicate (2 * (n + 1)) false ++ List.replicate (n + 1) true ++ rest,
        [.bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  rw [replicate_two_mul_succ_false]
  simp only [List.cons_append]
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (step_boundary_false _))
    (Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (step_odd_false_bottom _))
      (Relation.ReflTransGen.trans
        (by
          simpa [List.append_assoc] using
            read_more_a_pairs n (List.replicate (n + 1) true ++ rest) [.bottom])
        (finish_left_block n rest)))

private lemma run_left_block_mem {u rest : List Bool} (hu : u ∈ quotientLeftBlock) :
    @PDA.Reaches NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.boundary, u ++ rest, [.bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  rcases hu with ⟨n, rfl⟩
  exact run_left_block n rest

private lemma run_left_blocks (blocks : List (List Bool))
    (hblocks : ∀ y ∈ blocks, y ∈ quotientLeftBlock) (rest : List Bool) :
    @PDA.Reaches NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.boundary, blocks.flatten ++ rest, [.bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  induction blocks with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons b bs ih =>
      have hb : b ∈ quotientLeftBlock := hblocks b (by simp)
      have hbs : ∀ y ∈ bs, y ∈ quotientLeftBlock := by
        intro y hy
        exact hblocks y (by simp [hy])
      simpa [List.append_assoc] using
        Relation.ReflTransGen.trans (run_left_block_mem (u := b) (rest := bs.flatten ++ rest) hb)
          (ih hbs)

private lemma quotientNumerator_complete {w : List Bool} (hw : w ∈ quotientNumerator) :
    w ∈ dpda_quotientNumerator.acceptsByFinalState := by
  rw [quotientNumerator, Language.mem_kstar] at hw
  rcases hw with ⟨blocks, rfl, hblocks⟩
  refine ⟨.boundary, by simp [DPDA.toPDA, dpda_quotientNumerator], [.bottom], ?_⟩
  simpa using run_left_blocks blocks hblocks []

private lemma quotientNumerator_append_left_block {p b : List Bool}
    (hp : p ∈ quotientNumerator) (hb : b ∈ quotientLeftBlock) :
    p ++ b ∈ quotientNumerator := by
  rw [quotientNumerator, Language.mem_kstar] at hp ⊢
  rcases hp with ⟨blocks, rfl, hblocks⟩
  refine ⟨blocks ++ [b], by simp, ?_⟩
  intro y hy
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · exact hblocks y hy
  · rw [List.mem_singleton] at hy
    subst y
    exact hb

private lemma left_block_of_pos (m : ℕ) (hm : 0 < m) :
    List.replicate (2 * m) false ++ List.replicate m true ∈ quotientLeftBlock := by
  rcases m with _ | n
  · omega
  · exact ⟨n, rfl⟩

private def NumInv (w : List Bool)
    (c : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA) : Prop :=
  match c.state with
  | .boundary =>
      c.stack = [.bottom] ∧ ∃ p, p ∈ quotientNumerator ∧ w = p ++ c.input
  | .oddA =>
      ∃ p m, p ∈ quotientNumerator ∧
        w = p ++ List.replicate (2 * m + 1) false ++ c.input ∧
        c.stack = List.replicate m .pair ++ [.bottom]
  | .evenA =>
      ∃ p m, 0 < m ∧ p ∈ quotientNumerator ∧
        w = p ++ List.replicate (2 * m) false ++ c.input ∧
        c.stack = List.replicate m .pair ++ [.bottom]
  | .readB =>
      ∃ p m r, r < m ∧ p ∈ quotientNumerator ∧
        w = p ++ List.replicate (2 * m) false ++ List.replicate (m - r) true ++ c.input ∧
        c.stack = List.replicate r .pair ++ [.bottom]

private lemma NumInv.initial (w : List Bool) :
    NumInv w ⟨dpda_quotientNumerator.toPDA.initial_state, w,
      [dpda_quotientNumerator.toPDA.start_symbol]⟩ := by
  refine ⟨rfl, [], ?_, by simp⟩
  rw [quotientNumerator]
  exact Language.nil_mem_kstar quotientLeftBlock

private lemma boundary_false_inv (rest : List Bool)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.boundary, false :: rest, [.bottom]⟩ c') :
    c' = ⟨.oddA, rest, [.bottom]⟩ := by
  rcases c' with ⟨q', input', stack'⟩
  simpa [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
    List.replicate_succ]
    using hstep

private lemma no_step_boundary_nil
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.boundary, [], [.bottom]⟩ c') : False := by
  rcases c' with ⟨q', input', stack'⟩
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon]
    at hstep

private lemma no_step_odd_nil (m : ℕ)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.oddA, [], List.replicate m .pair ++ [.bottom]⟩ c') : False := by
  rcases c' with ⟨q', input', stack'⟩
  cases m <;>
    simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
      List.replicate_succ]
      at hstep

private lemma odd_false_inv (m : ℕ) (rest : List Bool)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.oddA, false :: rest, List.replicate m .pair ++ [.bottom]⟩ c') :
    c' = ⟨.evenA, rest, List.replicate (m + 1) .pair ++ [.bottom]⟩ := by
  rcases c' with ⟨q', input', stack'⟩
  cases m <;>
    simpa [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
      List.replicate_succ, List.append_assoc] using hstep

private lemma no_step_odd_true (m : ℕ) (rest : List Bool)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.oddA, true :: rest, List.replicate m .pair ++ [.bottom]⟩ c') : False := by
  rcases c' with ⟨q', input', stack'⟩
  cases m <;>
    simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
      List.replicate_succ]
      at hstep

private lemma no_step_even_nil (m : ℕ)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.evenA, [], List.replicate (m + 1) .pair ++ [.bottom]⟩ c') : False := by
  rcases c' with ⟨q', input', stack'⟩
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
    List.replicate_succ]
    at hstep

private lemma even_false_inv (m : ℕ) (rest : List Bool)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.evenA, false :: rest, List.replicate (m + 1) .pair ++ [.bottom]⟩ c') :
    c' = ⟨.oddA, rest, List.replicate (m + 1) .pair ++ [.bottom]⟩ := by
  rcases c' with ⟨q', input', stack'⟩
  simpa [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
    List.replicate_succ]
    using hstep

private lemma even_true_inv (m : ℕ) (rest : List Bool)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.evenA, true :: rest, List.replicate (m + 1) .pair ++ [.bottom]⟩ c') :
    c' = ⟨.readB, rest, List.replicate m .pair ++ [.bottom]⟩ := by
  rcases c' with ⟨q', input', stack'⟩
  simpa [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
    List.replicate_succ]
    using hstep

private lemma readB_bottom_inv (input : List Bool)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.readB, input, [.bottom]⟩ c') :
    c' = ⟨.boundary, input, [.bottom]⟩ := by
  rcases c' with ⟨q', input', stack'⟩
  cases input <;>
    simpa [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon]
      using hstep

private lemma no_step_readB_pair_nil (r : ℕ)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.readB, [], List.replicate (r + 1) .pair ++ [.bottom]⟩ c') : False := by
  rcases c' with ⟨q', input', stack'⟩
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
    List.replicate_succ]
    at hstep

private lemma no_step_readB_pair_false (r : ℕ) (rest : List Bool)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.readB, false :: rest, List.replicate (r + 1) .pair ++ [.bottom]⟩ c') : False := by
  rcases c' with ⟨q', input', stack'⟩
  simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
    List.replicate_succ]
    at hstep

private lemma readB_true_pair_inv (r : ℕ) (rest : List Bool)
    (c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA
      ⟨.readB, true :: rest, List.replicate (r + 1) .pair ++ [.bottom]⟩ c') :
    c' = ⟨.readB, rest, List.replicate r .pair ++ [.bottom]⟩ := by
  rcases c' with ⟨q', input', stack'⟩
  simpa [PDA.Reaches₁, PDA.step, dpda_quotientNumerator, DPDA.toPDA, transition, epsilon,
    List.replicate_succ]
    using hstep

private lemma NumInv.step {w : List Bool}
    {c c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA}
    (hinv : NumInv w c)
    (hstep : @PDA.Reaches₁ NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA c c') :
    NumInv w c' := by
  rcases c with ⟨q, input, stack⟩
  cases q <;>
    simp [NumInv] at hinv ⊢
  · rcases hinv with ⟨rfl, p, hp, hw⟩
    cases input with
    | nil =>
        exact False.elim (no_step_boundary_nil c' hstep)
    | cons a rest =>
        cases a
        · have hc' := boundary_false_inv rest c' hstep
          subst c'
          refine ⟨p, hp, 0, ?_, by simp⟩
          simp [hw]
        · rcases c' with ⟨q', input', stack'⟩
          simp [PDA.Reaches₁, PDA.step, dpda_quotientNumerator,
            DPDA.toPDA, transition, epsilon] at hstep
  · rcases hinv with ⟨p, hp, m, hw, hstack⟩
    subst stack
    cases input with
    | nil =>
        exact False.elim (no_step_odd_nil m c' hstep)
    | cons a rest =>
        cases a
        · have hc' := odd_false_inv m rest c' hstep
          subst c'
          refine ⟨p, m + 1, by omega, hp, ?_, by simp⟩
          simp [hw, replicate_two_mul_succ_false_append, List.append_assoc]
        · exact False.elim (no_step_odd_true m rest c' hstep)
  · rcases hinv with ⟨p, m, hm, hp, hw, hstack⟩
    subst stack
    cases m with
    | zero => omega
    | succ m =>
    cases input with
    | nil =>
        exact False.elim (no_step_even_nil m c' hstep)
    | cons a rest =>
        cases a
        · have hc' := even_false_inv m rest c' hstep
          subst c'
          refine ⟨p, hp, m + 1, ?_, by simp⟩
          simp [hw, replicate_succ_false_append, List.append_assoc]
        · have hc' := even_true_inv m rest c' hstep
          subst c'
          refine ⟨p, m + 1, m, by omega, hp, ?_, by simp⟩
          simp [hw, List.replicate_succ]
  · rcases hinv with ⟨p, m, r, hr, hp, hw, hstack⟩
    subst stack
    cases r with
    | zero =>
        have hc' := readB_bottom_inv input c' hstep
        subst c'
        refine ⟨rfl, p ++ (List.replicate (2 * m) false ++ List.replicate m true), ?_, ?_⟩
        · exact quotientNumerator_append_left_block hp (left_block_of_pos m (by omega))
        · simp [hw, List.append_assoc]
    | succ r =>
        cases input with
        | nil =>
            exact False.elim (no_step_readB_pair_nil r c' hstep)
        | cons a rest =>
            cases a
            · exact False.elim (no_step_readB_pair_false r rest c' hstep)
            · have hc' := readB_true_pair_inv r rest c' hstep
              subst c'
              refine ⟨p, m, r, by omega, hp, ?_, by simp⟩
              have hsub : m - r = (m - Nat.succ r) + 1 := by omega
              rw [hsub]
              simp [hw, List.replicate_add, List.append_assoc]

private lemma NumInv.reaches {w : List Bool}
    {c c' : @PDA.conf NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA}
    (hinv : NumInv w c)
    (hreach : @PDA.Reaches NumState Bool NumStack _ _ _ dpda_quotientNumerator.toPDA c c') :
    NumInv w c' := by
  induction hreach with
  | refl => exact hinv
  | tail _ hstep ih => exact NumInv.step ih hstep

private lemma quotientNumerator_sound {w : List Bool}
    (h : w ∈ dpda_quotientNumerator.acceptsByFinalState) :
    w ∈ quotientNumerator := by
  rcases h with ⟨q, hq, γ, hreach⟩
  have hinv := NumInv.reaches (NumInv.initial w) hreach
  cases q <;> simp [DPDA.toPDA, dpda_quotientNumerator] at hq
  change γ = [.bottom] ∧ ∃ p, p ∈ quotientNumerator ∧ w = p ++ [] at hinv
  rcases hinv with ⟨_, p, hp, hw⟩
  simpa [hw] using hp

/-- The numerator DPDA accepts exactly `{a^(2n)b^n | n >= 1}*`. -/
private theorem dpda_quotientNumerator_accepts :
    dpda_quotientNumerator.acceptsByFinalState = quotientNumerator := by
  ext w
  exact ⟨quotientNumerator_sound, quotientNumerator_complete⟩

/-- The language `{a^(2n)b^n | n >= 1}*` is deterministic context-free. -/
public theorem DCF_quotientNumerator : is_DCF quotientNumerator :=
  ⟨NumState, NumStack, inferInstance, inferInstance,
    dpda_quotientNumerator, dpda_quotientNumerator_accepts⟩

end DCFA2nBnPosStar
