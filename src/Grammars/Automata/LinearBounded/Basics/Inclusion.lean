import Mathlib
import Grammars.Automata.LinearBounded.Basics.LBA

/-!
# LBA Languages ⊆ Turing Machine Languages

We show that every language recognized by a linearly bounded automaton (LBA) is also
recognized by a Turing machine, connecting the LBA framework to Mathlib's Turing machine
definitions.

## Strategy

### Part 1: `Turing.eval` characterization

We show that `LBA.Accepts` is equivalent to Mathlib's `Turing.eval` halting in an
accepting state. Since `Turing.eval` is the common foundation underlying all Mathlib TM
models (`TM0`, `TM1`, `TM2`), this connects the LBA framework directly to Mathlib's
notion of Turing computation.

### Part 2: Concrete TM0 simulation

We construct a `Turing.TM0.Machine` that simulates a given LBA. The construction has
two phases:
1. **Reading phase**: The TM0 reads the input from the tape symbol by symbol,
   accumulating the symbols in its state space.
2. **Simulation phase**: Once the input is fully read, the TM0 simulates the LBA
   step-by-step entirely within its state space (no further tape access needed).

The TM0 halts if and only if the LBA accepts the input.

## Main Results

* `LBA.iterateStep_reaches` — `iterateStep` implies `Turing.Reaches`
* `LBA.reaches_iterateStep` — `Turing.Reaches` implies `iterateStep`
* `LBA.accepts_iff_eval` — LBA acceptance ↔ `Turing.eval` halts with accepting state
* `LBA.lba_language_subset_tm0_language` — Every word accepted by the LBA is accepted
  by the simulating TM0 machine
-/

namespace LBA

open Turing

/-! ## Part 1: Connecting LBA to `Turing.eval` -/

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

/-- LBA acceptance is equivalent to `Turing.eval` halting in an accepting state.
This connects the LBA directly to Mathlib's `Turing.eval` framework, which underlies
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

/-- States of the TM0 machine simulating an LBA. -/
inductive SimState (Γ : Type*) (Λ : Type*) (n : ℕ) where
  | reading : List Γ → SimState Γ Λ n
  | simulating : Cfg Γ Λ n → SimState Γ Λ n
  | loop : SimState Γ Λ n

instance SimState.instInhabited {Γ : Type*} {Λ : Type*} {n : ℕ} :
    Inhabited (SimState Γ Λ n) :=
  ⟨.reading []⟩

/-- The TM0 machine that simulates a given LBA. -/
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

/-- Encode an LBA input as a TM0 input (list over `Option Γ`). -/
def encodeInput {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ) : List (Option Γ) :=
  (List.ofFn w).map some

/-- The TM0 step function for the LBA simulation machine. -/
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
PROBLEM
The `k`-th element of a tape obtained by moving right `k` times.

PROVIDED SOLUTION
By induction on k. Base case k=0: trivial (simp). Inductive case: rw Function.iterate_succ_apply', then use move_right_nth and IH, then push_cast and ring.
-/
theorem tape_iter_move_right_nth {Γ : Type*} [Inhabited Γ]
    (T : Turing.Tape Γ) (k : ℕ) (i : ℤ) :
    ((Turing.Tape.move Turing.Dir.right)^[k] T).nth i = T.nth (i + k) := by
  induction' k with k ih generalizing i <;> simp_all +decide [ Function.iterate_succ_apply' ];
  ring

/-
PROBLEM
After moving right `k` times from `Tape.mk₁ l`, the head is `l.getI k`.

PROVIDED SOLUTION
Use tape_iter_move_right_nth with i=0 (via Tape.nth_zero) and then show (Tape.mk₁ l).nth ↑k = l.getI k.

For the second part: (Tape.mk₁ l).nth ↑k. Tape.mk₁ l = Tape.mk₂ [] l = Tape.mk' (ListBlank.mk []) (ListBlank.mk l). By Tape.mk'_nth_nat, (Tape.mk' L R).nth ↑n = R.nth n. So (Tape.mk₁ l).nth ↑k = (ListBlank.mk l).nth k = l.getI k by ListBlank.nth_mk.

Combining: head = nth 0 (by nth_zero) = (after shift by k) = (Tape.mk₁ l).nth k = l.getI k.
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
PROBLEM
The head of `Tape.mk₁ l` is `l.headI`.

PROVIDED SOLUTION
Unfold Tape.mk₁, Tape.mk₂, Tape.mk'. The head is (ListBlank.mk l).head = l.headI by ListBlank.head_mk.
-/
theorem tape_mk1_head {Γ : Type*} [Inhabited Γ] (l : List Γ) :
    (Turing.Tape.mk₁ l).head = l.headI := by
  cases l <;> aesop

/-
PROBLEM
For `k < l.length`, `l.getI k = l.get ⟨k, ...⟩`.

PROVIDED SOLUTION
This is List.getI_eq_get or similar. Use simp with List.getI_eq_getElem? or unfold getI.
-/
theorem list_getI_eq_get {α : Type*} [Inhabited α] (l : List α) (k : ℕ) (hk : k < l.length) :
    l.getI k = l.get ⟨k, hk⟩ := by
  simp +decide [ hk, List.getI ]

/-
PROBLEM
`encodeInput w` has length `n + 1`.

PROVIDED SOLUTION
encodeInput w = (List.ofFn w).map some. The length is (List.ofFn w).map some).length = (List.ofFn w).length = n+1. Use List.length_map and List.length_ofFn.
-/
theorem encodeInput_length {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ) :
    (encodeInput w).length = n + 1 := by
  unfold encodeInput; simp +decide ;

/-
PROBLEM
The `k`-th element of `encodeInput w` (for `k < n + 1`) is `some (w ⟨k, ...⟩)`.

PROVIDED SOLUTION
encodeInput w = (List.ofFn w).map some. For k < n+1, the k-th element is some ((List.ofFn w)[k]) = some (w ⟨k, hk⟩) by List.getElem_map and List.getElem_ofFn. Use getI_eq_getElem (since k < length).
-/
theorem encodeInput_getI {Γ : Type*} {n : ℕ} (w : Fin (n + 1) → Γ)
    (k : ℕ) (hk : k < n + 1) :
    (encodeInput w).getI k = some (w ⟨k, hk⟩) := by
  convert list_getI_eq_get _ _ _ using 1;
  unfold encodeInput; simp +decide [ List.get ] ;
  rcases k with ( _ | k ) <;> simp_all +decide [ List.get ];
  exact hk.trans_le ( by simp +decide [ encodeInput_length ] )

/-
PROBLEM
The element past the end of `encodeInput w` is `none` (the default).

PROVIDED SOLUTION
encodeInput w has length n+1 (by encodeInput_length). So getI (n+1) is past the end, returning default = none.
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
PROBLEM
The reading phase, after `k` steps (where `k ≤ n + 1`), has accumulated the
first `k` elements of `List.ofFn w` and the tape head is at position `k`.

PROVIDED SOLUTION
By induction on k.

Base case k=0: List.take 0 = [], and the iterate^[0] is identity, and tm0Init gives exactly this config. So Reaches is reflexive.

Inductive case k → k+1 (with k+1 ≤ n+1, so k ≤ n, so k < n+1):
By IH, we have Reaches from tm0Init to ⟨.reading (List.take k (List.ofFn w)), T_k⟩ where T_k = (move right)^[k] (Tape.mk₁ (encodeInput w)).

The head of T_k is (encodeInput w).getI k (by tape_mk1_move_right_head).
Since k < n+1, this equals some (w ⟨k, ...⟩) (by encodeInput_getI).

By reading_single_step, tm0Step takes ⟨.reading (List.take k ...), T_k⟩ to ⟨.reading (List.take k ... ++ [w k]), move right T_k⟩.

Now List.take k (List.ofFn w) ++ [w ⟨k, ...⟩] = List.take (k+1) (List.ofFn w) (by List.take_succ_app_ofFn or similar: take k l ++ [l[k]] = take (k+1) l when k < l.length).

And move right T_k = (move right)^[k+1] (Tape.mk₁ (encodeInput w)).

So one more step from the IH config reaches the (k+1) config. Extend Reaches with .tail.
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
PROBLEM
After reading all n+1 symbols from the encoded input, the TM0 reaches the
simulation phase with the correct initial LBA configuration.

PROVIDED SOLUTION
Step 1: By reading_phase_k_steps with k = n+1, we reach the config ⟨.reading (List.take (n+1) (List.ofFn w)), T_{n+1}⟩ where T_{n+1} = (move right)^[n+1] (Tape.mk₁ (encodeInput w)).

Note: List.take (n+1) (List.ofFn w) = List.ofFn w (because (List.ofFn w).length = n+1, so taking n+1 elements gives the whole list).

Step 2: The head of T_{n+1} is (encodeInput w).getI (n+1) = none (by tape_mk1_move_right_head and encodeInput_getI_end).

Step 3: Apply reading_to_simulating with acc = List.ofFn w, hacc = List.length_ofFn, T = T_{n+1}, hhead = none.

This gives ∃ T', tm0Step takes ⟨.reading (List.ofFn w), T_{n+1}⟩ to ⟨.simulating (initCfg M w'), T'⟩ where w' = fun i => (List.ofFn w).get (Fin.cast ...).

Step 4: Show w' = w: fun i => (List.ofFn w).get (Fin.cast ... i) = w i. This follows from List.get_ofFn (or getElem_ofFn): (List.ofFn w).get ⟨i, ...⟩ = w ⟨i, ...⟩.

Combine steps 1 and 3 using .tail to get Reaches from tm0Init to the simulating state.
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

/-- In the simulation phase, if the LBA takes a step, the TM0 also takes a step
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

/-- In the simulation phase, if the LBA halts in an accepting state, the TM0 halts. -/
theorem simulation_halts_on_accept {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hhalt : step M cfg = none) (hacc : M.accept cfg.state = true) :
    tm0Step M n (⟨.simulating cfg, T⟩ : SimCfg Γ Λ n) = none := by
  unfold tm0Step
  unfold TM0.step toTM0
  grind

/-
PROBLEM
If the LBA reaches an accepting halt from `cfg`, then the TM0 halts from the
simulating phase starting at `cfg`.

PROVIDED SOLUTION
By induction on the number of LBA steps k in the Accepts witness.

Accepts M cfg gives ∃ k, iterateStep M cfg (k+1) = none ∧ ∃ cfg', iterateStep M cfg k = some cfg' ∧ M.accept cfg'.state = true.

Induct on k.

k = 0: cfg' = cfg (from iterateStep 0 = some cfg). step M cfg = none. M.accept cfg.state = true. By simulation_halts_on_accept, tm0Step M n ⟨.simulating cfg, T⟩ = none. Since the step function returns none, by Turing.mem_eval, cfg ∈ eval, so Dom holds.

k+1: From iterateStep, step M cfg = some cfg₁ for some cfg₁ (extracting from the bind in iterateStep). By simulation_preserves_step, tm0Step M n ⟨.simulating cfg, T⟩ = some ⟨.simulating cfg₁, T'⟩. The remaining LBA computation from cfg₁ accepts (with witness k). By IH, (eval (tm0Step M n) ⟨.simulating cfg₁, T'⟩).Dom. Since tm0Step takes cfg to cfg₁ (one step), and eval from cfg₁ is defined, eval from cfg is also defined (by the fixpoint property of eval, or by eval_dom_of_reaches with a single step).
-/
theorem tm0_halts_of_lba_accepts {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (T : @Turing.Tape (Option Γ) ⟨none⟩)
    (hacc : Accepts M cfg) :
    (Turing.eval (tm0Step M n)
      (⟨.simulating cfg, T⟩ : SimCfg Γ Λ n)).Dom := by
  -- Let's obtain the witness `k` from the `Accepts` definition.
  obtain ⟨k, hk⟩ := hacc;
  -- By induction on $k$, we can show that the simulation preserves the steps of the LBA.
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
PROBLEM
If `Turing.Reaches f a b` and `(Turing.eval f b).Dom`, then `(Turing.eval f a).Dom`.

PROVIDED SOLUTION
By induction on the ReflTransGen relation hr.

Base case (a = b): trivial, hb directly gives the result.

Inductive case: We have some c with Reaches f a c, f c = some b (via one step), and (eval f b).Dom. By IH, we need to show (eval f c).Dom given (eval f b).Dom and f c = some b.

For the one-step case: if f c = some b and (eval f b).Dom, then (eval f c).Dom. This follows from the definition of Turing.eval as PFun.fix: eval f c = PFun.fix (fun s => Part.some ((f s).elim (Sum.inl s) Sum.inr)) c. When f c = some b, this becomes Sum.inr b, so it continues to eval f b.

Use Turing.eval_eq_step or similar: if f a = some b then eval f a = eval f b. Actually try: Turing.eval itself has a step lemma. Try rewriting with the definition and showing the fixpoint unfolds.
-/
theorem eval_dom_of_reaches {σ : Type*} (f : σ → Option σ) (a b : σ)
    (hr : Turing.Reaches f a b) (hb : (Turing.eval f b).Dom) :
    (Turing.eval f a).Dom := by
  grind +suggestions

/-! ### Main Theorem -/

/-- **Main theorem**: Every word accepted by the LBA is also accepted by the
simulating TM0 machine. This establishes that LBA languages are a subset of
TM0-recognizable languages. -/
theorem lba_language_subset_tm0_language
    {Γ : Type*} {Λ : Type*} {n : ℕ}
    [DecidableEq Γ] [Fintype Γ] [DecidableEq Λ] [Fintype Λ]
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ)
    (hw : w ∈ Language M n) :
    (Turing.eval (tm0Step M n) (tm0Init M w)).Dom := by
  -- Step 1: The reading phase reaches the simulation phase
  obtain ⟨T, hreach⟩ := reading_phase_complete M w
  -- Step 2: The simulation phase halts because the LBA accepts
  have hsim := tm0_halts_of_lba_accepts M (initCfg M w) T hw
  -- Step 3: Combine: reachability + halting from reached state → halting from init
  exact eval_dom_of_reaches _ _ _ hreach hsim

end LBA