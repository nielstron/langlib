import Mathlib
import Langlib.Automata.DeterministicLinearBounded.Definition

/-!
# DLBA Languages ⊆ Turing Machine Languages

We show that every language recognized by a linearly bounded automaton (DLBA) is also
recognized by a Turing machine, connecting the DLBA framework to Mathlib's Turing machine
definitions.

## Strategy

### Part 1: `Turing.eval` characterization

We show that `DLBA.Accepts` is equivalent to Mathlib's `Turing.eval` halting in an
accepting state. Since `Turing.eval` is the common foundation underlying all Mathlib TM
models (`TM0`, `TM1`, `TM2`), this connects the DLBA framework directly to Mathlib's
notion of Turing computation.

### Part 2: Concrete TM0 simulation

We construct a `Turing.TM0.Machine` that simulates a given DLBA. The construction has
two phases:
1. **Reading phase**: The TM0 reads the input from the tape symbol by symbol,
   accumulating the symbols in its state space.
2. **Simulation phase**: Once the input is fully read, the TM0 simulates the DLBA
   step-by-step entirely within its state space (no further tape access needed).

The TM0 halts if and only if the DLBA accepts the input.

## Main Results

* `DLBA.iterateStep_reaches` — `iterateStep` implies `Turing.Reaches`
* `DLBA.reaches_iterateStep` — `Turing.Reaches` implies `iterateStep`
* `DLBA.accepts_iff_eval` — DLBA acceptance ↔ `Turing.eval` halts with accepting state
* `DLBA.lba_language_subset_tm0_language` — Every word accepted by the DLBA is accepted
  by the simulating TM0 machine
-/

namespace DLBA

open Turing

/-! ## Part 1: Connecting DLBA to `Turing.eval` -/

/-- If `iterateStep M cfg k = some cfg'`, then `Turing.Reaches (step M) cfg cfg'`. -/
theorem iterateStep_reaches {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg cfg' : Cfg Γ Λ n) {k : ℕ}
    (hk : iterateStep M cfg k = some cfg') :
    Turing.Reaches (step M) cfg cfg' := by
  induction' k with k ih generalizing cfg cfg'
  · cases hk; tauto
  · cases h : iterateStep M cfg k <;> simp_all +decide [iterateStep_succ]
    exact Relation.ReflTransGen.tail (ih _ _ h) (by aesop)

/-- If `Turing.Reaches (step M) cfg cfg'`, then there exists `k` such that
`iterateStep M cfg k = some cfg'`. -/
theorem reaches_iterateStep {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg cfg' : Cfg Γ Λ n)
    (hr : Turing.Reaches (step M) cfg cfg') :
    ∃ k, iterateStep M cfg k = some cfg' := by
  induction hr
  · exact ⟨0, rfl⟩
  · rcases ‹_› with ⟨k, hk⟩
    use k + 1
    rw [iterateStep_succ, hk]; aesop

/-- DLBA acceptance is equivalent to `Turing.eval` halting in an accepting state.
This connects the DLBA directly to Mathlib's `Turing.eval` framework, which underlies
all TM models (`TM0`, `TM1`, `TM2`). -/
theorem accepts_iff_eval {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Accepts M cfg ↔
      ∃ c, c ∈ Turing.eval (step M) cfg ∧ M.accept c.state = true := by
  constructor
  · rintro ⟨k, hk, cfg', hk', hk''⟩
    refine ⟨cfg', ?_, hk''⟩
    rw [Turing.mem_eval]
    exact ⟨iterateStep_reaches M cfg cfg' hk',
      by rw [show iterateStep M cfg (k + 1) = (iterateStep M cfg k).bind (step M) from rfl] at hk
         aesop⟩
  · rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := reaches_iterateStep M cfg c (by rw [Turing.mem_eval] at hc; aesop)
    use k
    rw [iterateStep_succ]
    rw [Turing.mem_eval] at hc; aesop

/-! ## Part 2: Concrete TM0 Simulation -/

/-- States of the TM0 machine simulating an DLBA. -/
inductive SimState (Γ : Type*) (Λ : Type*) (n : ℕ) where
  | reading : List Γ → SimState Γ Λ n
  | simulating : Cfg Γ Λ n → SimState Γ Λ n
  | loop : SimState Γ Λ n

instance SimState.instInhabited {Γ : Type*} {Λ : Type*} {n : ℕ} :
    Inhabited (SimState Γ Λ n) :=
  ⟨.reading []⟩

/-- The TM0 machine that simulates a given DLBA. -/
noncomputable def toTM0 {Γ : Type*} {Λ : Type*} [DecidableEq Γ]
    (M : Machine Γ Λ) (n : ℕ) :
    @Turing.TM0.Machine (Option Γ) (SimState Γ Λ n) ⟨.reading []⟩ :=
  fun state sym =>
    match state with
    | .reading acc =>
      match sym with
      | some a => some (.reading (acc ++ [a]), .move .right)
      | none =>
        if h : acc.length = n + 1 then
          let w : Fin (n + 1) → Γ := fun i => acc.get (Fin.cast h.symm i)
          some (.simulating (initCfg M w), .write none)
        else
          none
    | .simulating cfg =>
      match step M cfg with
      | some cfg' => some (.simulating cfg', .write sym)
      | none =>
        if M.accept cfg.state then none
        else some (.loop, .write sym)
    | .loop => some (.loop, .write sym)

/-- Encode an DLBA input as a TM0 input (list over `Option Γ`). -/
def encodeInput {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ) : List (Option Γ) :=
  (List.ofFn w).map some

/-- The TM0 step function for the DLBA simulation machine. -/
noncomputable abbrev tm0Step {Γ : Type*} {Λ : Type*} [DecidableEq Γ]
    (M : Machine Γ Λ) (n : ℕ) :=
  @Turing.TM0.step (Option Γ) (SimState Γ Λ n) ⟨.reading []⟩ ⟨none⟩ (toTM0 M n)

/-- Abbreviation for TM0 configurations in the simulation. -/
abbrev SimCfg (Γ : Type*) (Λ : Type*) (n : ℕ) :=
  @Turing.TM0.Cfg (Option Γ) (SimState Γ Λ n) ⟨(none : Option Γ)⟩

/-- The initial TM0 configuration for a given encoded input. -/
noncomputable def tm0Init {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (_M : Machine Γ Λ) (w : Fin (n + 1) → Γ) : SimCfg Γ Λ n :=
  @Turing.TM0.init _ _ ⟨.reading ([] : List Γ)⟩ ⟨none⟩ (encodeInput w)

/-! ### Tape Helper Lemmas -/

/-
The `k`-th element of a tape obtained by moving right `k` times.
-/
theorem tape_iter_move_right_nth {Γ : Type*} [Inhabited Γ]
    (T : Turing.Tape Γ) (k : ℕ) (i : ℤ) :
    ((Turing.Tape.move Turing.Dir.right)^[k] T).nth i = T.nth (i + k) := by
  induction' k with k ih generalizing i <;> simp_all +decide [ Function.iterate_succ_apply' ];
  ring

/-
After moving right `k` times from `Tape.mk₁ l`, the head is `l.getI k`.
-/
theorem tape_mk1_move_right_head {Γ : Type*} [Inhabited Γ]
    (l : List Γ) (k : ℕ) :
    ((Turing.Tape.move Turing.Dir.right)^[k] (Turing.Tape.mk₁ l)).head = l.getI k := by
  convert tape_iter_move_right_nth _ _ _ using 1;
  any_goals exact ( Tape.mk' ( ListBlank.mk [] ) ( ListBlank.mk l ) );
  convert rfl;
  convert Tape.nth_zero _;
  simp +decide [ Tape.mk', ListBlank.mk ];
  simp +decide [ ListBlank.head, ListBlank.tail, Tape.nth ];
  cases l <;> cases k <;> simp +decide [ List.getI ]

/-
The head of `Tape.mk₁ l` is `l.headI`.
-/
theorem tape_mk1_head {Γ : Type*} [Inhabited Γ] (l : List Γ) :
    (Turing.Tape.mk₁ l).head = l.headI := by
  cases l <;> aesop

/-
For `k < l.length`, `l.getI k = l.get ⟨k, ...⟩`.
-/
theorem list_getI_eq_get {α : Type*} [Inhabited α] (l : List α) (k : ℕ) (hk : k < l.length) :
    l.getI k = l.get ⟨k, hk⟩ := by
  simp +decide [ hk, List.getI ]

/-
`encodeInput w` has length `n + 1`.
-/
theorem encodeInput_length {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ) :
    (encodeInput w).length = n + 1 := by
  unfold encodeInput; simp +decide ;

/-
The `k`-th element of `encodeInput w` (for `k < n + 1`) is `some (w ⟨k, ...⟩)`.
-/
theorem encodeInput_getI {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ)
    (k : ℕ) (hk : k < n + 1) :
    (encodeInput w).getI k = some (w ⟨k, hk⟩) := by
  convert list_getI_eq_get _ _ _ using 1;
  unfold encodeInput; simp +decide [ List.get ] ;
  rcases k with ( _ | k ) <;> simp_all +decide [ List.get ];
  exact hk.trans_le ( by simp +decide [ encodeInput_length ] )

/-
The element past the end of `encodeInput w` is `none` (the default).
-/
theorem encodeInput_getI_end {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ) :
    (encodeInput w).getI (n + 1) = none := by
  -- By definition of `encodeInput`, we know that `(encodeInput w).getI (n + 1)` is the default value, which is `none`.
  simp [encodeInput, List.getI];
  rfl

/-! ### Reading Phase -/

/-- A single reading step: if the head symbol is `some a`, the machine appends `a`
to the accumulator and moves right. -/
theorem reading_single_step {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (acc : List Γ) (a : Γ)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hhead : T.head = some a) :
    tm0Step M n (⟨.reading acc, T⟩ : SimCfg Γ Λ n) =
      some ⟨.reading (acc ++ [a]), Turing.Tape.move .right T⟩ := by
  unfold tm0Step
  unfold TM0.step
  unfold toTM0; aesop

/-- When the head is `none` and the accumulator has length `n + 1`, the reading phase
transitions to the simulation phase. -/
theorem reading_to_simulating {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (acc : List Γ) (hacc : acc.length = n + 1)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hhead : T.head = none) :
    ∃ T', tm0Step M n (⟨.reading acc, T⟩ : SimCfg Γ Λ n) =
      some (⟨.simulating (initCfg M (fun i => acc.get (Fin.cast hacc.symm i))), T'⟩ :
        SimCfg Γ Λ n) := by
  unfold tm0Step Turing.TM0.step
  unfold toTM0; aesop

/-
The reading phase, after `k` steps (where `k ≤ n + 1`), has accumulated the
first `k` elements of `List.ofFn w` and the tape head is at position `k`.
-/
theorem reading_phase_k_steps {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) (k : ℕ) (hk : k ≤ n + 1) :
    Turing.Reaches (tm0Step M n) (tm0Init M w)
      (⟨.reading (List.take k (List.ofFn w)),
        (Turing.Tape.move Turing.Dir.right)^[k]
          (Turing.Tape.mk₁ (encodeInput w))⟩ : SimCfg Γ Λ n) := by
  have h_base : Reaches (tm0Step M n) (tm0Init M w) ⟨SimState.reading (List.take 0 (List.ofFn w)), (Turing.Tape.move Turing.Dir.right)^[0] (Turing.Tape.mk₁ (encodeInput w))⟩ := by
    constructor;
  induction' k with k ih;
  · exact h_base;
  · have h_step : tm0Step M n ⟨SimState.reading (List.take k (List.ofFn w)), (Turing.Tape.move Turing.Dir.right)^[k] (Turing.Tape.mk₁ (encodeInput w))⟩ = some ⟨SimState.reading (List.take (k + 1) (List.ofFn w)), (Turing.Tape.move Turing.Dir.right)^[k + 1] (Turing.Tape.mk₁ (encodeInput w))⟩ := by
      convert reading_single_step M _ _ _ _ using 1;
      rotate_left;
      exact w ⟨ k, by linarith ⟩;
      · convert tape_mk1_move_right_head _ _ using 1;
        exact Eq.symm ( encodeInput_getI w k ( by linarith ) );
      · simp +decide [ List.take_add_one, Function.iterate_succ_apply' ];
        grind;
    exact .tail ( ih ( Nat.le_of_succ_le hk ) ) h_step

/-
After reading all n+1 symbols from the encoded input, the TM0 reaches the
simulation phase with the correct initial DLBA configuration.
-/
theorem reading_phase_complete {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) :
    ∃ T, Turing.Reaches (tm0Step M n) (tm0Init M w)
      (⟨.simulating (initCfg M w), T⟩ : SimCfg Γ Λ n) := by
  -- By definition of `tm0Init`, we know that after reading all n+1 symbols, we reach the simulation phase.
  have h_reaches : Turing.Reaches (tm0Step M n) (tm0Init M w) (⟨.reading (List.ofFn w), (Turing.Tape.move Turing.Dir.right)^[n + 1] (Turing.Tape.mk₁ (encodeInput w))⟩ : SimCfg Γ Λ n) := by
    convert reading_phase_k_steps M w ( n + 1 ) ( Nat.le_refl _ ) using 1;
    rw [ List.take_of_length_le ( by simp +decide ) ];
  -- By definition of `tm0Step`, we know that after reading all n+1 symbols, we reach the simulation phase.
  have h_reaches_sim : ∃ T', Turing.TM0.step (toTM0 M n) (⟨.reading (List.ofFn w), (Turing.Tape.move Turing.Dir.right)^[n + 1] (Turing.Tape.mk₁ (encodeInput w))⟩ : SimCfg Γ Λ n) = some (⟨.simulating (initCfg M w), T'⟩ : SimCfg Γ Λ n) := by
    have h_head : ((Turing.Tape.move Turing.Dir.right)^[n + 1] (Turing.Tape.mk₁ (encodeInput w))).head = none := by
      convert tape_mk1_move_right_head _ _ using 1;
      exact?;
    convert reading_to_simulating M ( List.ofFn w ) _ _ _;
    all_goals simp_all +decide [ List.get_ofFn ];
    rename_i i; induction i using Fin.inductionOn <;> simp +decide [ * ] ;
  exact ⟨ _, h_reaches.tail h_reaches_sim.choose_spec ⟩

/-! ### Simulation Phase Correctness -/

/-- In the simulation phase, if the DLBA takes a step, the TM0 also takes a step
maintaining the simulation invariant. -/
theorem simulation_preserves_step {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (cfg cfg' : Cfg Γ Λ n)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hstep : step M cfg = some cfg') :
    ∃ T', tm0Step M n ⟨.simulating cfg, T⟩ =
      some (⟨.simulating cfg', T'⟩ : SimCfg Γ Λ n) := by
  unfold tm0Step
  unfold toTM0
  unfold TM0.step; aesop

/-- In the simulation phase, if the DLBA halts in an accepting state, the TM0 halts. -/
theorem simulation_halts_on_accept {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hhalt : step M cfg = none) (hacc : M.accept cfg.state = true) :
    tm0Step M n (⟨.simulating cfg, T⟩ : SimCfg Γ Λ n) = none := by
  unfold tm0Step
  unfold TM0.step toTM0
  grind

/-
If the DLBA reaches an accepting halt from `cfg`, then the TM0 halts from the
simulating phase starting at `cfg`.
-/
theorem tm0_halts_of_lba_accepts {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hacc : Accepts M cfg) :
    (Turing.eval (tm0Step M n)
      (⟨.simulating cfg, T⟩ : SimCfg Γ Λ n)).Dom := by
  -- Let's obtain the witness `k` from the `Accepts` definition.
  obtain ⟨k, hk⟩ := hacc;
  -- By induction on $k$, we can show that the simulation preserves the steps of the DLBA.
  have h_ind : ∀ k, ∀ cfg cfg', iterateStep M cfg k = some cfg' → ∀ T, ∃ T', Turing.Reaches (tm0Step M n) (⟨.simulating cfg, T⟩ : SimCfg Γ Λ n) (⟨.simulating cfg', T'⟩ : SimCfg Γ Λ n) := by
    intro k cfg cfg' hk T; induction' k with k ih generalizing cfg cfg' T <;> simp_all +decide [ iterateStep ] ;
    · exact ⟨ T, by constructor ⟩;
    · rcases h : iterateStep M cfg k with ( _ | cfg'' ) <;> simp_all +decide [ Reaches ];
      obtain ⟨ T', hT' ⟩ := ih _ _ h T;
      obtain ⟨ T'', hT'' ⟩ := simulation_preserves_step M cfg'' cfg' T' hk; exact ⟨ T'', hT'.trans ( Relation.ReflTransGen.single hT'' ) ⟩ ;
  obtain ⟨cfg', hcfg', hacc⟩ := hk.2
  obtain ⟨T', hT'⟩ := h_ind k cfg cfg' hcfg' T
  have h_dom : (eval (tm0Step M n) { q := SimState.simulating cfg', Tape := T' }).Dom := by
                                      have h_dom : step M cfg' = none := by
                                        rw [ show iterateStep M cfg ( k + 1 ) = ( iterateStep M cfg k ).bind ( step M ) from rfl ] at hk ; aesop;
                                      convert simulation_halts_on_accept M cfg' T' h_dom hacc using 1;
                                      constructor <;> intro h <;> simp_all +decide [ Turing.eval ];
                                      · convert simulation_halts_on_accept M cfg' T' h_dom hacc using 1;
                                      · convert Part.dom_iff_mem.mpr _;
                                        use ⟨.simulating cfg', T'⟩;
                                        rw [ PFun.mem_fix_iff ] ; aesop;
  exact (by
    have h_reaches : Turing.Reaches (tm0Step M n) { q := SimState.simulating cfg, Tape := T } { q := SimState.simulating cfg', Tape := T' } := by
                                                                                                  grind +revert
    grind +suggestions
  )

/-
If `Turing.Reaches f a b` and `(Turing.eval f b).Dom`, then `(Turing.eval f a).Dom`.
-/
theorem eval_dom_of_reaches {σ : Type*} (f : σ → Option σ) (a b : σ)
    (hr : Turing.Reaches f a b) (hb : (Turing.eval f b).Dom) :
    (Turing.eval f a).Dom := by
  grind +suggestions

/-! ### Main Theorem -/

/-- **Main theorem**: Every word accepted by the DLBA is also accepted by the
simulating TM0 machine. This establishes that DLBA languages are a subset of
TM0-recognizable languages. -/
theorem lba_language_subset_tm0_language
    {Γ : Type*} {Λ : Type*} {n : ℕ}
    [DecidableEq Γ] [Fintype Γ] [DecidableEq Λ] [Fintype Λ]
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ)
    (hw : w ∈ Language M n) :
    (Turing.eval (tm0Step M n) (tm0Init M w)).Dom := by
  -- Step 1: The reading phase reaches the simulation phase
  obtain ⟨T, hreach⟩ := reading_phase_complete M w
  -- Step 2: The simulation phase halts because the DLBA accepts
  have hsim := tm0_halts_of_lba_accepts M (initCfg M w) T hw
  -- Step 3: Combine: reachability + halting from reached state → halting from init
  exact eval_dom_of_reaches _ _ _ hreach hsim

end DLBA
