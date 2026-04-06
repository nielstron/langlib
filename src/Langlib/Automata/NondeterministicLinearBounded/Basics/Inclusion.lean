import Mathlib
import Langlib.Automata.NondeterministicLinearBounded.Definition

/-!
# NLBA Languages ⊆ Turing Machine Languages

We show that every language recognized by a nondeterministic linearly bounded automaton
(NLBA) is also recognized by a Turing machine, adapting the LBA ⊆ TM proof for the
nondeterministic case.

## Strategy

The key challenge is that NLBAs are nondeterministic: there may be multiple possible
successor configurations at each step. We handle this by **BFS determinization**: the
simulating Turing machine tracks the entire *set* of currently reachable NLBA
configurations, expanding it by one nondeterministic step at a time.

### Part 1: BFS Determinization

We define `stepFinset M S`, which expands a `Finset` of configurations by one NLBA step,
and `iterStepFinset M S k`, which applies `k` expansion steps. We prove:
- Monotonicity: the configuration sets grow over time
- Correctness: if `Reaches M cfg cfg'` and `cfg ∈ S`, then `cfg' ∈ iterStepFinset M S k`
  for some `k`

### Part 2: Concrete TM0 Simulation

We construct a `Turing.TM0.Machine` that simulates a given NLBA via BFS:
1. **Reading phase**: Same as the LBA simulation — read input symbols into the state.
2. **Simulation phase**: Track a `Finset (LBA.Cfg Γ Λ n)` of reachable configurations.
   At each step, expand the set via `stepFinset`. If any configuration is accepting, halt.
   If the set reaches a fixpoint (no new configurations), loop forever.

The TM0 halts if and only if the NLBA accepts the input.

## Main Results

* `NLBA.reaches_mem_iterStepFinset` — multi-step reachability is captured by BFS
* `NLBA.reading_phase_complete` — reading phase reaches the initial simulation state
* `NLBA.nlba_language_subset_tm0_language` — every word accepted by the NLBA is accepted
  by the simulating TM0 machine
-/

namespace NLBA

open Turing

/-! ## Initialization -/

/-- Initial configuration for a `Fin`-indexed input word. -/
def initCfg {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) : LBA.Cfg Γ Λ n :=
  ⟨M.initial, ⟨w, ⟨0, Nat.zero_lt_succ n⟩⟩⟩

/-- The language recognized by an NLBA at a fixed input length. -/
def LanguageN {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (n : ℕ) : Set (Fin (n + 1) → Γ) :=
  { w | Accepts M (initCfg M w) }

/-! ## Part 1: BFS Determinization -/

/-- Whether a `Finset` of configurations contains an accepting one. -/
def hasAccepting {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n)) : Prop :=
  ∃ cfg ∈ S, M.accept cfg.state = true

open Classical in
noncomputable instance hasAcceptingDec {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n)) :
    Decidable (hasAccepting M S) :=
  inferInstance

open Classical in
/-- One-step BFS expansion: union of `S` with all configurations reachable in one
NLBA step from any configuration in `S`. -/
noncomputable def stepFinset {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n)) :
    Finset (LBA.Cfg Γ Λ n) :=
  S ∪ Finset.univ.filter (fun cfg' => ∃ cfg ∈ S, Step M cfg cfg')

open Classical in
/-- Iterated BFS expansion. -/
noncomputable def iterStepFinset {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n)) :
    ℕ → Finset (LBA.Cfg Γ Λ n)
  | 0 => S
  | k + 1 => stepFinset M (iterStepFinset M S k)

section BFS

variable {Γ : Type*} {Λ : Type*} {n : ℕ}
  [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

theorem subset_stepFinset (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n)) :
    S ⊆ stepFinset M S :=
  Finset.subset_union_left

theorem step_mem_stepFinset (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n))
    {cfg cfg' : LBA.Cfg Γ Λ n} (hcfg : cfg ∈ S) (hstep : Step M cfg cfg') :
    cfg' ∈ stepFinset M S := by
  -- Since cfg' is reachable from cfg, it must be in the stepFinset of S.
  simp [stepFinset];
  exact Or.inr ⟨ cfg, hcfg, hstep ⟩

theorem iterStepFinset_subset_succ (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n))
    (k : ℕ) :
    iterStepFinset M S k ⊆ iterStepFinset M S (k + 1) := by
  exact subset_stepFinset M _

theorem iterStepFinset_mono (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n))
    {i j : ℕ} (hij : i ≤ j) :
    iterStepFinset M S i ⊆ iterStepFinset M S j := by
  exact Nat.le_induction ( by tauto ) ( fun k hk ih => by exact Finset.Subset.trans ih ( iterStepFinset_subset_succ _ _ _ ) ) _ hij

/-
Multi-step NLBA reachability is captured by iterated BFS expansion.
-/
theorem reaches_mem_iterStepFinset (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n))
    {cfg cfg' : LBA.Cfg Γ Λ n} (hcfg : cfg ∈ S) (hreach : Reaches M cfg cfg') :
    ∃ k, cfg' ∈ iterStepFinset M S k := by
  by_contra h_contra;
  induction' hreach with cfg'' hcfg'' hreach' ih;
  · exact h_contra ⟨ 0, hcfg ⟩;
  · obtain ⟨ k, hk ⟩ := not_not.mp ‹_›;
    exact h_contra ⟨ k + 1, step_mem_stepFinset M ( iterStepFinset M S k ) hk ih ⟩

end BFS

/-! ## Part 2: Concrete TM0 Simulation -/

/-- States of the TM0 machine simulating an NLBA via BFS. -/
inductive NSimState (Γ : Type*) (Λ : Type*) (n : ℕ) where
  | reading : List Γ → NSimState Γ Λ n
  | simulating : Finset (@LBA.Cfg Γ Λ n) → NSimState Γ Λ n
  | loop : NSimState Γ Λ n

instance NSimState.instInhabited {Γ : Type*} {Λ : Type*} {n : ℕ} :
    Inhabited (NSimState Γ Λ n) :=
  ⟨.reading []⟩

open Classical in
/-- The TM0 machine that simulates a given NLBA via breadth-first search. -/
noncomputable def nToTM0 {Γ : Type*} {Λ : Type*}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (n : ℕ) :
    @Turing.TM0.Machine (Option Γ) (NSimState Γ Λ n) ⟨.reading []⟩ :=
  fun state sym =>
    match state with
    | .reading acc =>
      match sym with
      | some a => some (.reading (acc ++ [a]), .move .right)
      | none =>
        if h : acc.length = n + 1 then
          let w : Fin (n + 1) → Γ := fun i => acc.get (Fin.cast h.symm i)
          some (.simulating {initCfg M w}, .write none)
        else
          none
    | .simulating S =>
      if hasAccepting M S then none
      else
        let S' := stepFinset M S
        if S' = S then some (.loop, .write sym)
        else some (.simulating S', .write sym)
    | .loop => some (.loop, .write sym)

/-- Encode an NLBA input as a TM0 input (list over `Option Γ`). -/
def encodeInput {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ) : List (Option Γ) :=
  (List.ofFn w).map some

/-- The TM0 step function for the NLBA simulation machine. -/
noncomputable abbrev ntm0Step {Γ : Type*} {Λ : Type*}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (n : ℕ) :=
  @Turing.TM0.step (Option Γ) (NSimState Γ Λ n) ⟨.reading []⟩ ⟨none⟩ (nToTM0 M n)

/-- Abbreviation for TM0 configurations in the NLBA simulation. -/
abbrev NSimCfg (Γ : Type*) (Λ : Type*) (n : ℕ) :=
  @Turing.TM0.Cfg (Option Γ) (NSimState Γ Λ n) ⟨(none : Option Γ)⟩

/-- The initial TM0 configuration for a given encoded input. -/
noncomputable def ntm0Init {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) : NSimCfg Γ Λ n :=
  @Turing.TM0.init _ _ ⟨NSimState.reading ([] : List Γ)⟩ ⟨none⟩ (encodeInput w)

/-! ### Tape Helper Lemmas -/

theorem tape_iter_move_right_nth {α : Type*} [Inhabited α]
    (T : Turing.Tape α) (k : ℕ) (i : ℤ) :
    ((Turing.Tape.move Turing.Dir.right)^[k] T).nth i = T.nth (i + k) := by
  induction' k with k ih generalizing i <;> simp_all +decide [ Function.iterate_succ_apply' ];
  ring

theorem tape_mk1_move_right_head {α : Type*} [Inhabited α]
    (l : List α) (k : ℕ) :
    ((Turing.Tape.move Turing.Dir.right)^[k] (Turing.Tape.mk₁ l)).head = l.getI k := by
  simp +decide [ Tape.mk₁, Tape.nth ];
  cases k <;> simp +decide [ Tape.mk₂ ];
  · cases l <;> rfl;
  · cases l <;> simp +decide [ List.getI ]

theorem encodeInput_length {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ) :
    (encodeInput w).length = n + 1 := by
  unfold encodeInput; simp +decide [ List.length_ofFn ] ;

theorem encodeInput_getI {Γ : Type*} {n : ℕ}
    (w : Fin (n + 1) → Γ) (k : ℕ) (hk : k < n + 1) :
    (encodeInput w).getI k = some (w ⟨k, hk⟩) := by
  unfold encodeInput; simp +decide [ List.getI ] ;
  cases k <;> simp_all +decide

theorem encodeInput_getI_end {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ) :
    (encodeInput w).getI (n + 1) = none := by
  unfold encodeInput; simp +decide ;
  simp +decide [ List.getI ];
  rfl

/-! ### Reading Phase -/

/-
A single reading step: if the head symbol is `some a`, the machine appends `a`
to the accumulator and moves right.
-/
theorem reading_single_step {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (acc : List Γ) (a : Γ)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hhead : T.head = some a) :
    ntm0Step M n (⟨NSimState.reading acc, T⟩ : NSimCfg Γ Λ n) =
      some ⟨NSimState.reading (acc ++ [a]), Turing.Tape.move .right T⟩ := by
  unfold ntm0Step;
  unfold nToTM0;
  simp +decide [ TM0.step, hhead ]

/-
When the head is `none` and the accumulator has length `n + 1`, the reading phase
transitions to the simulation phase with a singleton configuration set.
-/
theorem reading_to_simulating {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (acc : List Γ) (hacc : acc.length = n + 1)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hhead : T.head = none) :
    ∃ T', ntm0Step M n (⟨NSimState.reading acc, T⟩ : NSimCfg Γ Λ n) =
      some (⟨NSimState.simulating
        {initCfg M (fun i => acc.get (Fin.cast hacc.symm i))}, T'⟩ :
          NSimCfg Γ Λ n) := by
  unfold ntm0Step;
  unfold nToTM0;
  unfold TM0.step; aesop;

/-
The reading phase, after `k` steps (where `k ≤ n + 1`), has accumulated the
first `k` elements of `List.ofFn w` and the tape head is at position `k`.
-/
theorem reading_phase_k_steps {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) (k : ℕ) (hk : k ≤ n + 1) :
    Turing.Reaches (ntm0Step M n) (ntm0Init M w)
      (⟨NSimState.reading (List.take k (List.ofFn w)),
        (Turing.Tape.move Turing.Dir.right)^[k]
          (Turing.Tape.mk₁ (encodeInput w))⟩ : NSimCfg Γ Λ n) := by
  induction' k with k ih;
  · constructor;
  · convert ih ( Nat.le_of_succ_le hk ) |> fun h => h.tail _ using 1;
    convert reading_single_step M ( List.take k ( List.ofFn w ) ) ( w ⟨ k, by linarith ⟩ ) _ _ using 1;
    any_goals exact ( Turing.Tape.move Turing.Dir.right ) ^[ k ] ( Turing.Tape.mk₁ ( encodeInput w ) );
    any_goals exact n;
    · simp +decide [ List.take_add_one, Function.iterate_succ_apply' ];
      grind;
    · convert tape_mk1_move_right_head ( encodeInput w ) k using 1;
      exact Eq.symm ( encodeInput_getI w k ( by linarith ) )

/-
After reading all `n + 1` symbols, the TM0 reaches the simulation phase with
the correct initial singleton configuration set.
-/
theorem reading_phase_complete {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) :
    ∃ T, Turing.Reaches (ntm0Step M n) (ntm0Init M w)
      (⟨NSimState.simulating {initCfg M w}, T⟩ : NSimCfg Γ Λ n) := by
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, Turing.Reaches (ntm0Step M n) (ntm0Init M w) (⟨NSimState.reading (List.ofFn w), T₁⟩ : NSimCfg Γ Λ n) ∧ T₁.head = none := by
    refine' ⟨ _, _, _ ⟩
    generalize_proofs at *;
    exact ( Turing.Tape.move Turing.Dir.right ) ^[ n + 1 ] ( Turing.Tape.mk₁ ( encodeInput w ) );
    · convert reading_phase_k_steps M w ( n + 1 ) le_rfl using 1 ; simp +decide [ List.take_of_length_le ];
    · convert encodeInput_getI_end w using 1;
      exact tape_mk1_move_right_head (encodeInput w) (n + 1);
  obtain ⟨T₂, hT₂⟩ : ∃ T₂, ntm0Step M n (⟨NSimState.reading (List.ofFn w), T₁⟩ : NSimCfg Γ Λ n) = some (⟨NSimState.simulating {initCfg M w}, T₂⟩ : NSimCfg Γ Λ n) := by
    convert reading_to_simulating M ( List.ofFn w ) _ T₁ _;
    all_goals simp_all +decide;
    rename_i i; induction i using Fin.inductionOn <;> simp +decide [ * ] ;
  exact ⟨ T₂, hT₁.1.tail hT₂ ⟩

/-! ### Simulation Phase -/

/-
In the simulation phase, if no configuration is accepting and the BFS has not
reached a fixpoint, the TM0 steps to the expanded configuration set.
-/
theorem simulation_step_bfs {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n))
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hnacc : ¬hasAccepting M S)
    (hne : stepFinset M S ≠ S) :
    ∃ T', ntm0Step M n (⟨NSimState.simulating S, T⟩ : NSimCfg Γ Λ n) =
      some (⟨NSimState.simulating (stepFinset M S), T'⟩ : NSimCfg Γ Λ n) := by
  unfold ntm0Step;
  unfold nToTM0;
  simp +decide [ hnacc, hne, TM0.step ]

/-
In the simulation phase, if some configuration is accepting, the TM0 halts.
-/
theorem simulation_halts_on_accept {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n))
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hacc : hasAccepting M S) :
    ntm0Step M n (⟨NSimState.simulating S, T⟩ : NSimCfg Γ Λ n) = none := by
  unfold ntm0Step;
  unfold nToTM0;
  unfold TM0.step;
  grind

/-
If the BFS reaches a fixpoint at step `i`, all subsequent iterations are the same.
-/
theorem iterStepFinset_fixpoint {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S : Finset (LBA.Cfg Γ Λ n))
    {i : ℕ} (hfix : stepFinset M (iterStepFinset M S i) = iterStepFinset M S i)
    {m : ℕ} (hm : i ≤ m) :
    iterStepFinset M S m = iterStepFinset M S i := by
  induction' hm with m hm ih;
  · rfl;
  · exact ih.symm ▸ hfix

/-
The TM0 correctly simulates `k` BFS expansion steps, provided no accepting config
has been found and the set keeps growing.
-/
theorem simulation_reaches_iterStepFinset {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S₀ : Finset (LBA.Cfg Γ Λ n))
    (T₀ : @Turing.Tape (Option Γ) ⟨none⟩) (k : ℕ)
    (hnacc : ∀ j < k, ¬hasAccepting M (iterStepFinset M S₀ j))
    (hgrow : ∀ j < k, stepFinset M (iterStepFinset M S₀ j) ≠ iterStepFinset M S₀ j) :
    ∃ T, Turing.Reaches (ntm0Step M n)
      (⟨NSimState.simulating S₀, T₀⟩ : NSimCfg Γ Λ n)
      (⟨NSimState.simulating (iterStepFinset M S₀ k), T⟩ : NSimCfg Γ Λ n) := by
  induction' k with k ih;
  · exact ⟨ T₀, Relation.ReflTransGen.refl ⟩;
  · obtain ⟨ T, hT ⟩ := ih ( fun j hj => hnacc j ( Nat.lt_succ_of_lt hj ) ) ( fun j hj => hgrow j ( Nat.lt_succ_of_lt hj ) );
    obtain ⟨ T', hT' ⟩ := simulation_step_bfs M ( iterStepFinset M S₀ k ) T ( hnacc k ( Nat.lt_succ_self k ) ) ( hgrow k ( Nat.lt_succ_self k ) );
    exact ⟨ T', hT.tail hT' ⟩

/-
If the NLBA accepts from some configuration in `S₀`, the TM0 simulation halts.

The proof proceeds by showing that the BFS expansion must eventually include an
accepting configuration. Since `Reaches M cfg cfg'` implies `cfg'` appears in
`iterStepFinset M S₀ k` for some `k`, and the BFS monotonically expands the set,
the accepting config will be found. The TM0 checks for acceptance at each step,
so it halts as soon as the accepting config enters the set.
-/
theorem tm0_halts_of_nlba_accepts {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (S₀ : Finset (LBA.Cfg Γ Λ n))
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hacc : ∃ cfg ∈ S₀, Accepts M cfg) :
    (Turing.eval (ntm0Step M n)
      (⟨NSimState.simulating S₀, T⟩ : NSimCfg Γ Λ n)).Dom := by
  -- By definition of `hasAccepting`, there exists some `j` such that `hasAccepting (iterStepFinset S₀ j)`.
  obtain ⟨j, hj⟩ : ∃ j, hasAccepting M (iterStepFinset M S₀ j) ∧ ∀ i < j, ¬hasAccepting M (iterStepFinset M S₀ i) := by
    have h_exists_j : ∃ j, hasAccepting M (iterStepFinset M S₀ j) := by
      obtain ⟨ cfg, hcfg₁, hcfg₂ ⟩ := hacc;
      obtain ⟨ cfg', hcfg' ⟩ := hcfg₂;
      exact Exists.elim ( reaches_mem_iterStepFinset M S₀ hcfg₁ hcfg'.1 ) fun k hk => ⟨ k, cfg', hk, hcfg'.2 ⟩;
    exact ⟨ Nat.find h_exists_j, Nat.find_spec h_exists_j, fun i hi => Nat.find_min h_exists_j hi ⟩
  generalize_proofs at *; (
  -- By definition of `iterStepFinset`, we know that `iterStepFinset M S₀ j` is reachable from `S₀`.
  have h_reachable : ∃ T', Turing.Reaches (ntm0Step M n) ⟨NSimState.simulating S₀, T⟩ ⟨NSimState.simulating (iterStepFinset M S₀ j), T'⟩ := by
    apply simulation_reaches_iterStepFinset M S₀ T j hj.2 (by
    grind +suggestions)
  generalize_proofs at *; (
  have h_eval : (eval (ntm0Step M n) ⟨NSimState.simulating (iterStepFinset M S₀ j), h_reachable.choose⟩).Dom := by
    have h_eval : ntm0Step M n ⟨NSimState.simulating (iterStepFinset M S₀ j), h_reachable.choose⟩ = none := by
      exact simulation_halts_on_accept M _ _ hj.1
    generalize_proofs at *; (
    convert Part.dom_iff_mem.mpr _ using 1
    generalize_proofs at *; (
    exact ⟨ _, PFun.mem_fix_iff.mpr <| by aesop ⟩))
  generalize_proofs at *; (
  grind +suggestions)))

/-
If `Turing.Reaches f a b` and `(Turing.eval f b).Dom`, then
`(Turing.eval f a).Dom`.
-/
theorem eval_dom_of_reaches {σ : Type*} (f : σ → Option σ) (a b : σ)
    (hr : Turing.Reaches f a b) (hb : (Turing.eval f b).Dom) :
    (Turing.eval f a).Dom := by
  grind +suggestions

/-! ### Main Theorem -/

/-- **Main theorem**: Every word accepted by the NLBA is also accepted by the
simulating TM0 machine. This establishes that NLBA languages are a subset of
TM0-recognizable languages. -/
theorem nlba_language_subset_tm0_language
    {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ)
    (hw : w ∈ LanguageN M n) :
    (Turing.eval (ntm0Step M n) (ntm0Init M w)).Dom := by
  -- Step 1: The reading phase reaches the simulation phase
  obtain ⟨T, hreach⟩ := reading_phase_complete M w
  -- Step 2: The simulation phase halts because the NLBA accepts
  have hsim := tm0_halts_of_nlba_accepts M {initCfg M w} T
    ⟨initCfg M w, Finset.mem_singleton_self _, hw⟩
  -- Step 3: Combine: reachability + halting from reached state → halting from init
  exact eval_dom_of_reaches _ _ _ hreach hsim

end NLBA