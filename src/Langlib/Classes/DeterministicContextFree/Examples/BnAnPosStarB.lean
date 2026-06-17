module

public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Examples.BnAnPosStarB
import Mathlib.Tactic

/-!
# The `{b^n a^n | n >= 1}* {b}` Language as a DCF

This file builds the deterministic pushdown automaton for the denominator
witness used in the right-quotient counterexample, with `false = a` and
`true = b`.
-/

open PDA
open Language

namespace DCFBnAnPosStarB

private inductive DenState where
  | boundary
  | finalB
  | readB
  | readA
deriving DecidableEq, Fintype

private inductive DenStack where
  | bottom
  | bmark
deriving DecidableEq, Fintype

private def transition : DenState → Bool → DenStack →
    Option (DenState × List DenStack)
  | .boundary, true, .bottom => some (.finalB, [.bmark, .bottom])
  | .finalB, true, .bmark => some (.readB, [.bmark, .bmark])
  | .finalB, false, .bmark => some (.readA, [])
  | .readB, true, .bmark => some (.readB, [.bmark, .bmark])
  | .readB, false, .bmark => some (.readA, [])
  | .readA, false, .bmark => some (.readA, [])
  | _, _, _ => none

private def epsilon : DenState → DenStack → Option (DenState × List DenStack)
  | .readA, .bottom => some (.boundary, [.bottom])
  | _, _ => none

private def dpda_quotientDenominator : DPDA DenState Bool DenStack where
  initial_state := .boundary
  start_symbol := .bottom
  final_states := {.finalB}
  transition := transition
  epsilon_transition := epsilon
  no_mixed := by
    intro q Z hε a
    cases q <;> cases Z <;> cases a <;> simp [epsilon, transition] at hε ⊢

private lemma step_boundary_true (rest : List Bool) :
    @PDA.Reaches₁ DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.boundary, true :: rest, [.bottom]⟩
      ⟨.finalB, rest, [.bmark, .bottom]⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition]

private lemma step_finalB_true (rest : List Bool) (stk : List DenStack) :
    @PDA.Reaches₁ DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.finalB, true :: rest, .bmark :: stk⟩
      ⟨.readB, rest, .bmark :: .bmark :: stk⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition]

private lemma step_finalB_false (rest : List Bool) (stk : List DenStack) :
    @PDA.Reaches₁ DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.finalB, false :: rest, .bmark :: stk⟩
      ⟨.readA, rest, stk⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition]

private lemma step_readB_true (rest : List Bool) (stk : List DenStack) :
    @PDA.Reaches₁ DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.readB, true :: rest, .bmark :: stk⟩
      ⟨.readB, rest, .bmark :: .bmark :: stk⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition]

private lemma step_readB_false (rest : List Bool) (stk : List DenStack) :
    @PDA.Reaches₁ DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.readB, false :: rest, .bmark :: stk⟩
      ⟨.readA, rest, stk⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition]

private lemma step_readA_false (rest : List Bool) (stk : List DenStack) :
    @PDA.Reaches₁ DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.readA, false :: rest, .bmark :: stk⟩
      ⟨.readA, rest, stk⟩ := by
  simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition]

private lemma step_readA_bottom (rest : List Bool) :
    @PDA.Reaches₁ DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.readA, rest, [.bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  cases rest <;> simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, epsilon]

private lemma replicate_bmark_append_cons (n : ℕ) (stk : List DenStack) :
    List.replicate n DenStack.bmark ++ DenStack.bmark :: stk =
      DenStack.bmark :: List.replicate n DenStack.bmark ++ stk := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons DenStack.bmark) ih

private lemma replicate_succ_true_append (n : ℕ) :
    List.replicate (n + 1) true = List.replicate n true ++ [true] := by
  rw [List.replicate_add]
  simp

private lemma read_more_b (n : ℕ) (rest : List Bool) (stk : List DenStack) :
    @PDA.Reaches DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.readB, List.replicate n true ++ rest, .bmark :: stk⟩
      ⟨.readB, rest, List.replicate n .bmark ++ .bmark :: stk⟩ := by
  induction n generalizing rest stk with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (step_readB_true _ _))
        (by
          simpa [List.replicate_succ, List.append_assoc, replicate_bmark_append_cons] using
            ih rest (.bmark :: stk))

private lemma read_more_a (n : ℕ) (rest : List Bool) (stk : List DenStack) :
    @PDA.Reaches DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.readA, List.replicate n false ++ rest, List.replicate n .bmark ++ stk⟩
      ⟨.readA, rest, stk⟩ := by
  induction n generalizing rest stk with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (step_readA_false _ _))
        (by simpa [List.append_assoc] using ih rest stk)

private lemma run_right_block (n : ℕ) (rest : List Bool) :
    @PDA.Reaches DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.boundary, List.replicate (n + 1) true ++ List.replicate (n + 1) false ++ rest,
        [.bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  cases n with
  | zero =>
      simp only [List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append]
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (step_boundary_true _))
        (Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (step_finalB_false _ _))
          (Relation.ReflTransGen.single (step_readA_bottom rest)))
  | succ n =>
      rw [List.replicate_succ, List.cons_append]
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (step_boundary_true _))
        (Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (step_finalB_true _ _))
          (Relation.ReflTransGen.trans
            (by
              simpa [List.append_assoc] using
                read_more_b n (List.replicate (n + 2) false ++ rest) [.bmark, .bottom])
            (Relation.ReflTransGen.trans
              (by
                simpa [List.replicate_succ, List.append_assoc, replicate_bmark_append_cons] using
                  Relation.ReflTransGen.single
                    (step_readB_false (List.replicate (n + 1) false ++ rest)
                      (List.replicate (n + 1) .bmark ++ [.bottom])))
              (Relation.ReflTransGen.trans
                (read_more_a (n + 1) rest [.bottom])
                (Relation.ReflTransGen.single (step_readA_bottom rest))))))

private lemma run_right_block_mem {u rest : List Bool} (hu : u ∈ quotientRightBlock) :
    @PDA.Reaches DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.boundary, u ++ rest, [.bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  rcases hu with ⟨n, rfl⟩
  exact run_right_block n rest

private lemma run_right_blocks (blocks : List (List Bool))
    (hblocks : ∀ y ∈ blocks, y ∈ quotientRightBlock) (rest : List Bool) :
    @PDA.Reaches DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA
      ⟨.boundary, blocks.flatten ++ rest, [.bottom]⟩
      ⟨.boundary, rest, [.bottom]⟩ := by
  induction blocks with
  | nil => exact Relation.ReflTransGen.refl
  | cons b bs ih =>
      have hb : b ∈ quotientRightBlock := hblocks b (by simp)
      have hbs : ∀ y ∈ bs, y ∈ quotientRightBlock := by
        intro y hy
        exact hblocks y (by simp [hy])
      simpa [List.append_assoc] using
        Relation.ReflTransGen.trans (run_right_block_mem (u := b) (rest := bs.flatten ++ rest) hb)
          (ih hbs)

private lemma quotientDenominator_complete {w : List Bool} (hw : w ∈ quotientDenominator) :
    w ∈ dpda_quotientDenominator.acceptsByFinalState := by
  rw [quotientDenominator] at hw
  rcases hw with ⟨u, hu, v, hv, huw⟩
  rw [Language.mem_kstar] at hu
  rw [Set.mem_singleton_iff] at hv
  subst v
  subst w
  rcases hu with ⟨blocks, rfl, hblocks⟩
  refine ⟨.finalB, by simp [DPDA.toPDA, dpda_quotientDenominator], [.bmark, .bottom], ?_⟩
  exact Relation.ReflTransGen.trans (run_right_blocks blocks hblocks [true])
    (Relation.ReflTransGen.single (step_boundary_true []))

private lemma denominatorStar_append_right_block {p b : List Bool}
    (hp : p ∈ KStar.kstar quotientRightBlock) (hb : b ∈ quotientRightBlock) :
    p ++ b ∈ KStar.kstar quotientRightBlock := by
  rw [Language.mem_kstar] at hp ⊢
  rcases hp with ⟨blocks, rfl, hblocks⟩
  refine ⟨blocks ++ [b], by simp, ?_⟩
  intro y hy
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · exact hblocks y hy
  · rw [List.mem_singleton] at hy
    subst y
    exact hb

private lemma right_block_of_pos (m : ℕ) (hm : 0 < m) :
    List.replicate m true ++ List.replicate m false ∈ quotientRightBlock := by
  rcases m with _ | n
  · omega
  · exact ⟨n, rfl⟩

private lemma quotientDenominator_of_star {p : List Bool}
    (hp : p ∈ KStar.kstar quotientRightBlock) :
    p ++ [true] ∈ quotientDenominator := by
  rw [quotientDenominator]
  exact ⟨p, hp, [true], by rw [Set.mem_singleton_iff], rfl⟩

private def DenInv (w : List Bool)
    (c : @PDA.conf DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA) : Prop :=
  match c.state with
  | .boundary =>
      c.stack = [.bottom] ∧ ∃ p, p ∈ KStar.kstar quotientRightBlock ∧ w = p ++ c.input
  | .finalB =>
      c.stack = [.bmark, .bottom] ∧ ∃ p, p ∈ KStar.kstar quotientRightBlock ∧
        w = p ++ [true] ++ c.input
  | .readB =>
      ∃ p m, 2 ≤ m ∧ p ∈ KStar.kstar quotientRightBlock ∧
        w = p ++ List.replicate m true ++ c.input ∧
        c.stack = List.replicate m .bmark ++ [.bottom]
  | .readA =>
      ∃ p m r, r < m ∧ p ∈ KStar.kstar quotientRightBlock ∧
        w = p ++ List.replicate m true ++ List.replicate (m - r) false ++ c.input ∧
        c.stack = List.replicate r .bmark ++ [.bottom]

private lemma DenInv.initial (w : List Bool) :
    DenInv w ⟨dpda_quotientDenominator.toPDA.initial_state, w,
      [dpda_quotientDenominator.toPDA.start_symbol]⟩ := by
  refine ⟨rfl, [], ?_, by simp⟩
  exact Language.nil_mem_kstar quotientRightBlock

private lemma DenInv.step {w : List Bool}
    {c c' : @PDA.conf DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA}
    (hinv : DenInv w c)
    (hstep : @PDA.Reaches₁ DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA c c') :
    DenInv w c' := by
  rcases c with ⟨q, input, stack⟩
  rcases c' with ⟨q', input', stack'⟩
  cases q <;> simp [DenInv] at hinv ⊢
  · rcases hinv with ⟨rfl, p, hp, hw⟩
    cases input with
    | nil =>
        simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition, epsilon] at hstep
    | cons a rest =>
        cases a
        · simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition, epsilon] at hstep
        · simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition, epsilon] at hstep
          rcases hstep with ⟨rfl, ⟨rfl, rfl⟩⟩
          refine ⟨rfl, p, hp, ?_⟩
          simp [hw]
  · rcases hinv with ⟨rfl, p, hp, hw⟩
    cases input with
    | nil =>
        simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition, epsilon] at hstep
    | cons a rest =>
        cases a
        · simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition, epsilon] at hstep
          rcases hstep with ⟨rfl, ⟨rfl, rfl⟩⟩
          refine ⟨p, 1, 0, by omega, hp, ?_, by simp⟩
          simp [hw]
        · simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition, epsilon] at hstep
          rcases hstep with ⟨rfl, ⟨rfl, rfl⟩⟩
          refine ⟨p, 2, by omega, hp, ?_, by simp⟩
          simp [hw]
  · rcases hinv with ⟨p, m, hm, hp, hw, hstack⟩
    subst stack
    cases input with
    | nil =>
        cases m with
        | zero => omega
        | succ m =>
            cases m with
            | zero => omega
            | succ m =>
                simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition,
                  epsilon, List.replicate_succ] at hstep
    | cons a rest =>
        cases m with
        | zero => omega
        | succ m =>
            cases m with
            | zero => omega
            | succ m =>
                cases a
                · simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition,
                    epsilon, List.replicate_succ] at hstep
                  rcases hstep with ⟨rfl, ⟨rfl, rfl⟩⟩
                  refine ⟨p, m + 2, m + 1, by omega, hp, ?_, by simp [List.replicate_succ]⟩
                  simp [hw, List.replicate_succ]
                · simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition,
                    epsilon, List.replicate_succ] at hstep
                  rcases hstep with ⟨rfl, ⟨rfl, rfl⟩⟩
                  refine ⟨p, m + 3, by omega, hp, ?_, ?_⟩
                  · simp [hw, replicate_succ_true_append, List.append_assoc]
                  · simp [List.replicate_succ]
  · rcases hinv with ⟨p, m, r, hr, hp, hw, hstack⟩
    subst stack
    cases r with
    | zero =>
        cases input <;>
          simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition, epsilon] at hstep
        all_goals
          rcases hstep with ⟨rfl, ⟨rfl, rfl⟩⟩
          refine ⟨rfl, p ++ (List.replicate m true ++ List.replicate m false), ?_, ?_⟩
          · exact denominatorStar_append_right_block hp (right_block_of_pos m (by omega))
          · simp [hw, List.append_assoc]
    | succ r =>
        cases input with
        | nil =>
            simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition,
              epsilon, List.replicate_succ] at hstep
        | cons a rest =>
            cases a
            · simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition,
                epsilon, List.replicate_succ] at hstep
              rcases hstep with ⟨rfl, ⟨rfl, rfl⟩⟩
              refine ⟨p, m, r, by omega, hp, ?_, by simp⟩
              have hsub : m - r = (m - Nat.succ r) + 1 := by omega
              rw [hsub]
              simp [hw, List.replicate_add, List.append_assoc]
            · simp [PDA.Reaches₁, PDA.step, dpda_quotientDenominator, DPDA.toPDA, transition,
                epsilon, List.replicate_succ] at hstep

private lemma DenInv.reaches {w : List Bool}
    {c c' : @PDA.conf DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA}
    (hinv : DenInv w c)
    (hreach : @PDA.Reaches DenState Bool DenStack _ _ _ dpda_quotientDenominator.toPDA c c') :
    DenInv w c' := by
  induction hreach with
  | refl => exact hinv
  | tail _ hstep ih => exact DenInv.step ih hstep

private lemma quotientDenominator_sound {w : List Bool}
    (h : w ∈ dpda_quotientDenominator.acceptsByFinalState) :
    w ∈ quotientDenominator := by
  rcases h with ⟨q, hq, γ, hreach⟩
  have hinv := DenInv.reaches (DenInv.initial w) hreach
  cases q <;> simp [DPDA.toPDA, dpda_quotientDenominator] at hq
  change γ = [.bmark, .bottom] ∧ ∃ p, p ∈ KStar.kstar quotientRightBlock ∧
    w = p ++ [true] ++ [] at hinv
  rcases hinv with ⟨_, p, hp, hw⟩
  simpa [hw, List.append_assoc] using quotientDenominator_of_star hp

private theorem dpda_quotientDenominator_accepts :
    dpda_quotientDenominator.acceptsByFinalState = quotientDenominator := by
  ext w
  exact ⟨quotientDenominator_sound, quotientDenominator_complete⟩

/-- The language `{b^n a^n | n >= 1}* {b}` is deterministic context-free. -/
public theorem DCF_quotientDenominator : is_DCF quotientDenominator :=
  ⟨DenState, DenStack, inferInstance, inferInstance,
    dpda_quotientDenominator, dpda_quotientDenominator_accepts⟩

end DCFBnAnPosStarB
