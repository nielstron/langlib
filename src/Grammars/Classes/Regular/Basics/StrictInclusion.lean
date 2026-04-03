/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.DPDA
import Grammars.Classes.DetContextFree.Basics.DCFL
import Grammars.Classes.DetContextFree.ClosureProperties.Bijection
import Grammars.Classes.Regular.Basics.NonRegular
import Grammars.Classes.Regular.Basics.Inclusion
import Grammars.Classes.Regular.ClosureProperties.Bijection

/-! # aⁿbⁿ is a DCFL and RG ⊊ DCFL

This file constructs a deterministic pushdown automaton (DPDA) for the language
`{aⁿbⁿ | n ≥ 0}` and proves it accepts exactly that language. This is used to
show that `{aⁿbⁿ}` is a DCFL, and since it is not regular, that regular languages
form a strict subclass of DCFLs.

## Main results

- `anbn_is_DCFL` — The language `{aⁿbⁿ}` is a deterministic context-free language.
- `RG_strict_subclass_DCFL` — Regular languages are a strict subclass of DCFLs.
-/

open PDA List

/-- DPDA recognizing `{aⁿbⁿ | n ≥ 0}` where `false` = a and `true` = b.

  **States** (`Fin 4`):
  - `0` — initial state (also accepting, for the empty string)
  - `1` — reading a's (pushes A's onto the stack)
  - `2` — reading b's (pops A's from the stack)
  - `3` — accept state (reached when all b's have been matched)

  **Stack** (`Bool`):
  - `false` = Z₀ (bottom-of-stack marker)
  - `true`  = A  (counter symbol, one per 'a' read)

  **Final states**: `{0, 3}`. -/
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

/-
============================================================================
Completeness: every aⁿbⁿ is accepted by dpda_anbn
============================================================================

One step: read 'a' from initial state 0 with Z₀ on stack → state 1.
-/
private lemma step_read_a_init (rest : List Bool) :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨0, false :: rest, [false]⟩ ⟨1, rest, [true, false]⟩ := by
        constructor;
        unfold PDA.transition_fun; aesop;

/-
One step: read 'a' from state 1 with A on top → push another A.
-/
private lemma step_read_a (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, false :: rest, true :: stk⟩ ⟨1, rest, true :: true :: stk⟩ := by
        exact Set.mem_union_left _ ⟨ _, _, by aesop ⟩

/-
One step: read 'b' from state 1 with A on top → state 2, pop A.
-/
private lemma step_read_b_from1 (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, true :: rest, true :: stk⟩ ⟨2, rest, stk⟩ := by
        constructor;
        unfold dpda_anbn; aesop;

/-
One step: read 'b' from state 2 with A on top → pop A.
-/
private lemma step_read_b (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, true :: rest, true :: stk⟩ ⟨2, rest, stk⟩ := by
        constructor;
        unfold dpda_anbn; aesop;

/-
One step: ε-transition from state 2 with Z₀ on top → state 3.
-/
private lemma step_epsilon_empty :
    @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, [], [false]⟩ ⟨3, [], []⟩ := by
        constructor ; aesop ( simp_config := { decide := true } ) ;

/-
Reading k a's from state 1 pushes k additional A's onto the stack.
-/
private lemma read_as (k : ℕ) (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, replicate k false ++ rest, true :: stk⟩
      ⟨1, rest, replicate (k + 1) true ++ stk⟩ := by
        induction' k with k ih generalizing rest stk;
        · constructor;
        · specialize ih rest (true :: stk);
          convert ih.head _ using 1;
          · simp +decide [ replicate_add ];
          · apply step_read_a

/-
Reading k b's from state 2 pops k A's from the stack.
-/
private lemma read_bs (k : ℕ) (rest : List Bool) (stk : List Bool) :
    @PDA.Reaches (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, replicate k true ++ rest, replicate k true ++ stk⟩
      ⟨2, rest, stk⟩ := by
        induction' k with k ih generalizing rest stk <;> simp_all +decide [ List.replicate ];
        · constructor;
        · exact Reaches.trans (.single (step_read_b _ _)) (ih _ _)

/-
Every word aⁿbⁿ is accepted by dpda_anbn.
-/
private lemma dpda_anbn_complete (n : ℕ) :
    replicate n false ++ replicate n true ∈ dpda_anbn.acceptsByFinalState := by
      rcases n with ( _ | n ) <;> simp_all +decide [ List.replicate ];
      · use 0;
        exact ⟨ by tauto, [ false ], by tauto ⟩;
      · use 3; simp +decide [ dpda_anbn ] ;
        constructor;
        · exact Or.inr rfl;
        · use [];
          convert Relation.ReflTransGen.trans ( Relation.ReflTransGen.single ( step_read_a_init _ ) ) ( Relation.ReflTransGen.trans ( read_as _ _ _ ) _ ) using 1;
          convert Relation.ReflTransGen.trans ( Relation.ReflTransGen.single ( step_read_b_from1 _ _ ) ) ( Relation.ReflTransGen.trans ( read_bs _ _ _ ) ( Relation.ReflTransGen.single ( step_epsilon_empty ) ) ) using 1;
          swap;
          exacts [ n, by simp +decide [ List.replicate ] ]

-- ============================================================================
-- Soundness: only words of the form aⁿbⁿ are accepted
-- ============================================================================

/-- Reachability invariant for configurations reachable from `⟨0, w, [Z₀]⟩`.

  Any such configuration must be in one of four forms:
  - **State 0**: initial, no input consumed, stack = `[Z₀]`
  - **State 1**: consumed `na ≥ 1` a's, stack = `A^na · Z₀`
  - **State 2**: consumed `na` a's and `nb` b's (1 ≤ nb ≤ na), stack = `A^(na-nb) · Z₀`
  - **State 3**: consumed `na` a's and `na` b's (fully matched), stack = `[]` -/
private def AnBnInv (w : List Bool)
    (c : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA) : Prop :=
  ∃ na nb : ℕ,
    w = replicate na false ++ replicate nb true ++ c.input ∧
    ((c.state = (0 : Fin 4) ∧ na = 0 ∧ nb = 0 ∧ c.stack = [false]) ∨
     (c.state = (1 : Fin 4) ∧ na ≥ 1 ∧ nb = 0 ∧ c.stack = replicate na true ++ [false]) ∨
     (c.state = (2 : Fin 4) ∧ 1 ≤ nb ∧ nb ≤ na ∧
       c.stack = replicate (na - nb) true ++ [false]) ∨
     (c.state = (3 : Fin 4) ∧ nb = na ∧ c.stack = []))

/-
No PDA step is possible from state 3 (empty stack).
-/
private lemma no_step_state3 (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨3, input, []⟩ c') : False := by
        cases input <;> cases c' <;> cases hstep

/-
Invariant preservation from state 0.
-/
private lemma inv_step_state0 (w : List Bool) (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hw : w = input)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨0, input, [false]⟩ c') :
    AnBnInv w c' := by
      rcases input with ( _ | ⟨ a, rest ⟩ ) <;> simp_all +decide [ PDA.Reaches₁ ];
      · obtain ⟨ p, β, hpβ, rfl ⟩ := hstep; unfold dpda_anbn at hpβ; simp_all +decide [ DPDA.toPDA ] ;
      · cases a <;> simp_all +decide [ step ];
        · rcases hstep with ( ⟨ p, β, hp, rfl ⟩ | ⟨ p, β, hp, rfl ⟩ ) <;> simp_all +decide [ dpda_anbn ];
          · simp_all +decide [ DPDA.toPDA ];
            exact ⟨ 1, 0, by aesop ⟩;
          · simp_all +decide [ DPDA.toPDA ];
        · cases hstep <;> simp_all +decide [ dpda_anbn ];
          · simp_all +decide [ DPDA.toPDA ];
          · simp_all +decide [ DPDA.toPDA ]

/-
Invariant preservation from state 1.
-/
private lemma inv_step_state1 (w : List Bool) (na : ℕ) (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hna : na ≥ 1)
    (hw : w = replicate na false ++ input)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨1, input, replicate na true ++ [false]⟩ c') :
    AnBnInv w c' := by
      cases' input with a input';
      · rcases na with ( _ | _ | na ) <;> simp_all +decide;
        · cases hstep;
          rename_i q hq; rcases hq with ⟨ β, hβ₁, rfl ⟩ ; fin_cases q <;> simp_all +decide ;
          · cases hβ₁;
          · cases hβ₁;
          · cases hβ₁;
          · cases hβ₁;
        · cases hstep;
          unfold dpda_anbn at * ; simp_all +decide;
          rename_i k hk;
          fin_cases k <;> simp_all +decide [ DPDA.toPDA ];
      · cases' na with na <;> simp_all +decide [ List.replicate ];
        cases' a with a a <;> simp_all +decide [ Reaches₁ ];
        · unfold step at hstep;
          unfold dpda_anbn at hstep; simp_all +decide [ PDA.transition_fun, PDA.transition_fun' ] ;
          unfold DPDA.toPDA at hstep; simp_all +decide [ List.replicate ] ;
          use na + 2, 0;
          exact Nat.recOn na ( by simp +decide ) fun n ihn => by simp +decide [ List.replicate ] at ihn ⊢ ; aesop;
        · cases' hstep with h h ; simp_all +decide [ step ];
          · unfold DPDA.toPDA at h; simp_all +decide [ dpda_anbn ] ;
            use na + 1, 1;
            simp +arith +decide [ List.replicate ];
          · obtain ⟨ p, β, hp, rfl ⟩ := h;
            cases hp

/-
Invariant preservation from state 2.
-/
private lemma inv_step_state2 (w : List Bool) (na nb : ℕ) (input : List Bool)
    (c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hnb1 : 1 ≤ nb) (hnb2 : nb ≤ na)
    (hw : w = replicate na false ++ replicate nb true ++ input)
    (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA
      ⟨2, input, replicate (na - nb) true ++ [false]⟩ c') :
    AnBnInv w c' := by
      unfold Reaches₁ at hstep;
      unfold PDA.step at hstep;
      cases input <;> cases h : na - nb <;> simp_all +decide [ dpda_anbn ];
      · unfold DPDA.toPDA at hstep; simp_all +decide [ dpda_anbn ] ;
        use nb, nb;
        rw [ Nat.sub_eq_iff_eq_add ] at h <;> aesop;
      · cases hstep ; simp_all +decide [ dpda_anbn ];
        unfold DPDA.toPDA at *; simp_all +decide [ PDA.transition_fun' ] ;
      · unfold DPDA.toPDA at *;
        exact ⟨ na, na, by rw [ Nat.sub_eq_iff_eq_add ] at h <;> aesop ⟩;
      · unfold DPDA.toPDA at hstep; simp_all +decide [ List.replicate ] ;
        split_ifs at hstep <;> simp_all +decide [ Set.mem_singleton_iff ];
        refine' ⟨ na, nb + 1, _, _ ⟩ <;> simp_all +decide [ Nat.sub_succ ];
        · simp +decide [ replicate_add, List.append_assoc ];
        · omega

/-- The invariant is preserved by one PDA step. -/
private lemma inv_step (w : List Bool)
    (c c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hinv : AnBnInv w c) (hstep : @PDA.Reaches₁ (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA c c') :
    AnBnInv w c' := by
  rcases c with ⟨q, inp, stk⟩
  obtain ⟨na, nb, hw, hcases⟩ := hinv
  dsimp at hw hcases hstep
  rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hna, rfl, rfl⟩ | ⟨rfl, hnb1, hnb2, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp at hw; exact inv_step_state0 w inp c' hw hstep
  · simp at hw; exact inv_step_state1 w na inp c' hna hw hstep
  · exact inv_step_state2 w na nb inp c' hnb1 hnb2 hw hstep
  · exact absurd hstep (fun h => no_step_state3 inp c' h)

/-- The invariant is preserved by `Reaches` (reflexive-transitive closure). -/
private lemma inv_reaches (w : List Bool)
    (c c' : @PDA.conf (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA)
    (hinv : AnBnInv w c)
    (hreach : @PDA.Reaches (Fin 4) Bool Bool _ _ _ dpda_anbn.toPDA c c') :
    AnBnInv w c' := by
  induction hreach with
  | refl => exact hinv
  | tail _ hstep ih => exact inv_step w _ _ ih hstep

/-
Only words of the form aⁿbⁿ are accepted by dpda_anbn.
-/
private lemma dpda_anbn_sound (w : List Bool)
    (h : w ∈ dpda_anbn.acceptsByFinalState) : w ∈ anbn := by
      -- From h, obtain ⟨q, hq, γ, hreach⟩.
      obtain ⟨q, hq, γ, hreach⟩ := h;
      obtain ⟨ na, nb, hw, hcases ⟩ := inv_reaches w ⟨ dpda_anbn.toPDA.initial_state, w, [ dpda_anbn.toPDA.start_symbol ] ⟩ ⟨ q, [], γ ⟩ ⟨ 0, 0, by aesop ⟩ hreach;
      fin_cases q <;> simp_all +decide [ anbn ];
      · exists 0;
      · cases hq;
        · contradiction;
        · contradiction;
      · cases hq;
        · contradiction;
        · contradiction;
      · exact ⟨ na, rfl ⟩

-- ============================================================================
-- Main results
-- ============================================================================

/-- The DPDA `dpda_anbn` accepts exactly the language `{aⁿbⁿ}`. -/
theorem dpda_anbn_accepts : dpda_anbn.acceptsByFinalState = anbn := by
  ext w
  exact ⟨dpda_anbn_sound w, fun ⟨n, hw⟩ => hw ▸ dpda_anbn_complete n⟩

/-- The language `{aⁿbⁿ}` is a deterministic context-free language. -/
theorem anbn_is_DCFL : is_DCFL anbn :=
  ⟨Fin 4, Bool, inferInstance, inferInstance, dpda_anbn, dpda_anbn_accepts⟩

/-- Regular languages are a strict subclass of deterministic context-free languages over any
nontrivial alphabet. -/
theorem RG_strict_subclass_DCFL {T : Type} [Fintype T] [Nontrivial T] :
    (RG : Set (Language T)) ⊂ (DCFL : Set (Language T)) := by
  refine ⟨RG_subclass_DCFL, ?_⟩
  intro hDCFLsubsetRG
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> try rfl
    · simp [f] at hxy
      exact False.elim (hab hxy)
    · simp [f] at hxy
      exact False.elim (hab hxy.symm)
  have hRG : Language.map f anbn ∈ (RG : Set (Language T)) :=
    hDCFLsubsetRG (a := Language.map f anbn)
      (DCFL_of_map_injective_DCFL hf anbn anbn_is_DCFL)
  have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
  exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)
