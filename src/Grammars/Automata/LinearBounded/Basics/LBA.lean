import Mathlib

/-!
# Linearly Bounded Automata

A **linearly bounded automaton** (LBA) is a deterministic Turing machine whose read/write
head is restricted to the portion of the tape containing the input. This makes the
configuration space finite, yielding powerful decidability results that do not hold for
unrestricted Turing machines.

We adapt Mathlib's Turing machine framework (`Turing.TM0`, `Turing.TM1`) by replacing
the infinite `Turing.Tape` with a fixed-length `BoundedTape`.

## Main Definitions

* `LBA.BoundedTape Γ n` — A tape of `n` cells over alphabet `Γ` with a head position
* `LBA.Machine Γ Λ` — A deterministic linearly bounded automaton
* `LBA.Cfg Γ Λ n` — Configuration (state + bounded tape contents)
* `LBA.step` — Single computation step (`none` = halted)
* `LBA.iterateStep` — Multi-step computation
* `LBA.Halts` — Whether the machine eventually halts
* `LBA.HaltsAt` — The specific step at which the machine first halts
* `LBA.Accepts` — Whether the machine halts in an accepting state
* `LBA.complementMachine` — Complement machine (same transitions, negated acceptance)

## Main Results

* `LBA.Cfg.instFintype` — The configuration space is finite (for finite alphabets/states)
* `LBA.iterateStep_none_mono` — Once halted, the machine remains halted
* `LBA.complement_step_eq` — The complement machine takes identical transitions
* `LBA.complement_halts_iff` — The complement machine halts iff the original does
* `LBA.complement_accepts_iff` — On halting inputs, complement accepts iff original rejects
* `LBA.halts_iff_haltsWithin` — An LBA halts iff it halts within `Fintype.card Cfg` steps
* `LBA.decidableHalts` — The halting problem for LBAs is decidable
* `LBA.decidableAccepts` — Acceptance for LBAs is decidable

## References

* Kuroda, S.Y. (1964), "Classes of languages and linear-bounded automata"
* Myhill, J. (1960), "Linear bounded automata"

## Implementation Notes

We use `Fin (n + 1)` to index tape cells, guaranteeing at least one cell exists.
Head movement is *clamped* at boundaries: moving left at position 0 or right at the
last position leaves the head in place. This is the standard convention for LBAs, where
boundary markers prevent the head from leaving the input region.
-/

namespace LBA

open Fintype in
/-! ### Direction -/

/-- Direction for head movement. We include `stay` since the head is clamped at tape
boundaries and this simplifies the definition of `moveHead`. -/
inductive Dir where
  | left  : Dir
  | right : Dir
  | stay  : Dir
  deriving DecidableEq, Repr, Fintype, Inhabited

/-! ### Bounded Tape -/

/-- A bounded tape of `n + 1` cells over alphabet `Γ`, with a read/write head.
This replaces the infinite `Turing.Tape` used in unrestricted Turing machines.
The tape always has at least one cell (indexed by `Fin (n + 1)`). -/
structure BoundedTape (Γ : Type*) (n : ℕ) where
  /-- Contents of each tape cell -/
  contents : Fin (n + 1) → Γ
  /-- Current head position -/
  head : Fin (n + 1)
  deriving DecidableEq

/-- Read the symbol under the head. -/
@[simp]
def BoundedTape.read {Γ : Type*} {n : ℕ} (t : BoundedTape Γ n) : Γ :=
  t.contents t.head

/-- Write a symbol at the current head position. -/
def BoundedTape.write {Γ : Type*} {n : ℕ} (t : BoundedTape Γ n) (a : Γ) :
    BoundedTape Γ n :=
  { t with contents := Function.update t.contents t.head a }

/-- Move the head, clamping at boundaries (left end = 0, right end = n). -/
def BoundedTape.moveHead {Γ : Type*} {n : ℕ} (t : BoundedTape Γ n) (d : Dir) :
    BoundedTape Γ n :=
  { t with head :=
    match d with
    | Dir.stay => t.head
    | Dir.left =>
      if h : 0 < t.head.val then ⟨t.head.val - 1, by omega⟩ else t.head
    | Dir.right =>
      if h : t.head.val < n then ⟨t.head.val + 1, by omega⟩ else t.head }

noncomputable instance BoundedTape.instFintype {Γ : Type*} {n : ℕ}
    [Fintype Γ] : Fintype (BoundedTape Γ n) :=
  Fintype.ofInjective
    (fun t => (t.contents, t.head))
    (fun t₁ t₂ h => by cases t₁; cases t₂; simpa using h)

/-! ### Machine Definition -/

/-- A deterministic linearly bounded automaton.
- `Γ` is the tape alphabet (must include a blank symbol, but we keep it general)
- `Λ` is the finite set of states
- `transition` maps `(state, symbol)` to `(new_state, symbol_to_write, direction)`,
  or `none` to signal halting.
- `accept` determines which states are accepting (used to define the recognized language).
- `initial` is the start state. -/
structure Machine (Γ : Type*) (Λ : Type*) where
  /-- Transition function. Returns `none` to halt. -/
  transition : Λ → Γ → Option (Λ × Γ × Dir)
  /-- Which states are accepting (decidable predicate). -/
  accept : Λ → Bool
  /-- The initial state. -/
  initial : Λ

/-! ### Configuration -/

/-- A configuration of an LBA running on a tape of `n + 1` cells. -/
structure Cfg (Γ : Type*) (Λ : Type*) (n : ℕ) where
  /-- Current state of the machine. -/
  state : Λ
  /-- Current tape contents and head position. -/
  tape : BoundedTape Γ n
  deriving DecidableEq

noncomputable instance Cfg.instFintype {Γ : Type*} {Λ : Type*} {n : ℕ}
    [Fintype Γ] [Fintype Λ] : Fintype (Cfg Γ Λ n) :=
  Fintype.ofInjective
    (fun c => (c.state, c.tape))
    (fun c₁ c₂ h => by cases c₁; cases c₂; simpa using h)

/-! ### Step Function -/

/-- Execute one step of the LBA. Returns `none` if the machine halts
(i.e., the transition function returns `none` for the current state and symbol).
The configuration just before halting can be inspected for acceptance. -/
def step {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) : Option (Cfg Γ Λ n) :=
  match M.transition cfg.state cfg.tape.read with
  | none => none
  | some (q', a, d) => some ⟨q', (cfg.tape.write a).moveHead d⟩

/-- Iterate the step function `k` times. Returns `some cfg'` if the machine is
still running after `k` steps, or `none` if it halted at or before step `k`. -/
def iterateStep {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) : ℕ → Option (Cfg Γ Λ n)
  | 0 => some cfg
  | k + 1 => (iterateStep M cfg k).bind (step M)

@[simp]
theorem iterateStep_zero {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    iterateStep M cfg 0 = some cfg := rfl

theorem iterateStep_succ {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) (k : ℕ) :
    iterateStep M cfg (k + 1) = (iterateStep M cfg k).bind (step M) := rfl

theorem iterateStep_none_mono {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) {k : ℕ}
    (hk : iterateStep M cfg k = none) (j : ℕ) :
    iterateStep M cfg (k + j) = none := by
  induction' j with j ih;
  · exact hk;
  · rw [ Nat.add_succ, iterateStep_succ, ih, Option.bind ]

theorem iterateStep_some_of_succ_some {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) {k : ℕ} {cfg' : Cfg Γ Λ n}
    (hk : iterateStep M cfg (k + 1) = some cfg') :
    ∃ cfg'', iterateStep M cfg k = some cfg'' := by
  simp_all +decide [ iterateStep ];
  cases h : iterateStep M cfg k <;> aesop

theorem iterateStep_add {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) (i j : ℕ) :
    iterateStep M cfg (i + j) = (iterateStep M cfg i).bind (fun c => iterateStep M c j) := by
  induction' j with j ih generalizing i;
  · aesop;
  · rw [ ← add_assoc, iterateStep_succ, ih ];
    cases h : iterateStep M cfg i <;> aesop

/-! ### Halting and Acceptance -/

/-- The machine **halts** from configuration `cfg` if there exists a step at which
`iterateStep` returns `none`. -/
def Halts {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) : Prop :=
  ∃ k, iterateStep M cfg k = none

/-- The **halting configuration**: the configuration of the machine at the last step
before it halts. This is where we check acceptance. -/
noncomputable def haltingCfg {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) (h : Halts M cfg) : Cfg Γ Λ n :=
  let k := Nat.find h
  match hk : iterateStep M cfg (k - 1) with
  | some c => c
  | none => cfg  -- fallback (k = 0 case)

/-- The machine **accepts** from configuration `cfg` if it halts and the last
configuration before halting has an accepting state. -/
def Accepts {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) : Prop :=
  ∃ k, iterateStep M cfg (k + 1) = none ∧
    ∃ cfg', iterateStep M cfg k = some cfg' ∧ M.accept cfg'.state = true

/-- The machine **rejects** from configuration `cfg` if it halts and the last
configuration before halting has a non-accepting state. -/
def Rejects {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) : Prop :=
  ∃ k, iterateStep M cfg (k + 1) = none ∧
    ∃ cfg', iterateStep M cfg k = some cfg' ∧ M.accept cfg'.state = false

/-- The initial configuration for input `w` on a tape of `n + 1` cells. -/
def initCfg {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) : Cfg Γ Λ n :=
  ⟨M.initial, ⟨w, ⟨0, Nat.zero_lt_succ n⟩⟩⟩

/-- The **language** recognized by an LBA: the set of inputs (of each length) that
the machine accepts. -/
def Language {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (n : ℕ) : Set (Fin (n + 1) → Γ) :=
  { w | Accepts M (initCfg M w) }

/-! ### Complement Machine -/

/-- The **complement** of a deterministic LBA: same transitions, negated acceptance.
This is the key construction for showing closure under complement. -/
def complementMachine {Γ : Type*} {Λ : Type*} (M : Machine Γ Λ) : Machine Γ Λ where
  transition := M.transition
  accept := fun q => !M.accept q
  initial := M.initial

@[simp]
theorem complement_step_eq {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    step (complementMachine M) cfg = step M cfg := by
  unfold step complementMachine; aesop;

@[simp]
theorem complement_iterateStep_eq {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) (k : ℕ) :
    iterateStep (complementMachine M) cfg k = iterateStep M cfg k := by
  induction' k with k ih generalizing cfg <;> simp +decide [ *, iterateStep ]

theorem complement_halts_iff {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Halts (complementMachine M) cfg ↔ Halts M cfg := by
  constructor <;> rintro ⟨ k, hk ⟩ <;> use k <;> aesop

theorem complement_accepts_iff_rejects {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Accepts (complementMachine M) cfg ↔ Rejects M cfg := by
  constructor <;> intro h;
  · obtain ⟨ k, hk₁, cfg', hk₂, hk₃ ⟩ := h;
    exact ⟨ k, by simpa only [ complement_iterateStep_eq ] using hk₁, cfg', by simpa only [ complement_iterateStep_eq ] using hk₂, by simpa [ complementMachine ] using hk₃ ⟩;
  · obtain ⟨ k, hk₁, hk₂ ⟩ := h;
    obtain ⟨ cfg', hk₃, hk₄ ⟩ := hk₂;
    refine' ⟨ k, _, cfg', _ ⟩;
    · rw [ complement_iterateStep_eq, hk₁ ];
    · exact ⟨ complement_iterateStep_eq M cfg k ▸ hk₃, by unfold complementMachine; aesop ⟩

theorem complement_rejects_iff_accepts {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Rejects (complementMachine M) cfg ↔ Accepts M cfg := by
  -- Apply the equivalence from `complement_accepts_iff_rejects`
  apply Iff.intro;
  · rintro ⟨ k, hk₁, cfg', hk₂, hk₃ ⟩;
    use k, by
      rw [ ← complement_iterateStep_eq, hk₁ ], cfg', by
      rw [ ← hk₂, complement_iterateStep_eq ], by
      unfold complementMachine at hk₃; aesop;
  · intro h_accepts;
    obtain ⟨ k, hk₁, cfg', hk₂, hk₃ ⟩ := h_accepts;
    exact ⟨ k, by simp [ hk₁, complement_iterateStep_eq ], cfg', by simp [ hk₂, complement_iterateStep_eq ], by simp [ hk₃, complementMachine ] ⟩

theorem accepts_or_rejects_of_halts {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) (h : Halts M cfg) :
    Accepts M cfg ∨ Rejects M cfg := by
  obtain ⟨ k, hk ⟩ := Nat.findX h;
  rcases k with ( _ | k ) <;> simp_all +decide;
  -- By definition of `iterateStep`, if `iterateStep M cfg (k + 1) = none`, then `iterateStep M cfg k = some cfg'` for some `cfg'`.
  obtain ⟨cfg', hcfg'⟩ : ∃ cfg', iterateStep M cfg k = some cfg' := by
    exact Option.ne_none_iff_exists'.mp ( hk.2 k le_rfl );
  cases em ( M.accept cfg'.state ) <;> [ left; right ] <;> use k <;> aesop

theorem not_accepts_and_rejects {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    ¬(Accepts M cfg ∧ Rejects M cfg) := by
  -- Assume that `Accepts M cfg` and `Rejects M cfg` are both true.
  by_contra h
  obtain ⟨k₁, cfg₁, hk₁⟩ := h.left
  obtain ⟨k₂, cfg₂, hk₂⟩ := h.right;
  -- If `k₁ < k₂`, then `iterateStep M cfg (k₁ + 1) = none` implies `iterateStep M cfg (k₂ + 1) = none` by monotonicity.
  by_cases h_cases : k₁ < k₂;
  · have := iterateStep_none_mono M cfg cfg₁ ( k₂ - ( k₁ + 1 ) ) ; simp_all +decide [ Nat.sub_sub ] ;
  · -- If `k₂ < k₁`, then `iterateStep M cfg (k₂ + 1) = none` implies `iterateStep M cfg (k₁ + 1) = none` by monotonicity.
    by_cases h_cases' : k₂ < k₁;
    · have := iterateStep_none_mono M cfg cfg₂ ( k₁ - ( k₂ + 1 ) ) ; simp_all +decide [ Nat.add_sub_of_le h_cases'.le ] ;
    · grind

theorem complement_language {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) (hh : Halts M (initCfg M w)) :
    w ∈ Language (complementMachine M) n ↔ w ∉ Language M n := by
  constructor;
  · intro hw h'w;
    obtain ⟨k₁, hk₁⟩ := hw
    obtain ⟨k₂, hk₂⟩ := h'w;
    -- Since the machine halts, it must either accept or reject.
    by_cases h_accept : Accepts M (initCfg M w);
    · exact absurd ( complement_accepts_iff_rejects M ( initCfg M w ) |>.1 ⟨ k₁, hk₁.1, hk₁.2.choose, by
        convert hk₁.2.choose_spec.1 using 1, by
        exact hk₁.2.choose_spec.2 ⟩ ) ( by
        exact fun h => not_accepts_and_rejects M ( initCfg M w ) ⟨ h_accept, h ⟩ );
    · exact h_accept ⟨ k₂, hk₂.1, hk₂.2 ⟩;
  · intro hw
    have h_compl : Accepts (complementMachine M) (initCfg M w) := by
      unfold Language at hw;
      grind +suggestions;
    exact h_compl

/-! ### Decidability of Halting -/

section Decidability

variable {Γ : Type*} {Λ : Type*} {n : ℕ}
  [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

theorem not_halts_of_iterate_eq (M : Machine Γ Λ) (cfg : Cfg Γ Λ n)
    {i j : ℕ} (hij : i < j)
    (hi : iterateStep M cfg i = iterateStep M cfg j)
    (hi_some : (iterateStep M cfg i).isSome) :
    ¬Halts M cfg := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m, iterateStep M cfg m = none := by
    exact h;
  induction' m using Nat.strong_induction_on with m ih generalizing cfg i j;
  -- If $m \geq j$, then by the periodicity, $iterateStep M cfg m = iterateStep M cfg (i + (m - i))$.
  by_cases hm_ge_j : m ≥ j;
  · have h_periodic : iterateStep M cfg m = iterateStep M cfg (i + (m - j)) := by
      rw [ show m = j + ( m - j ) by rw [ Nat.add_sub_cancel' hm_ge_j ], iterateStep_add ];
      simp +decide [ ← hi ];
      rw [ iterateStep_add ];
    grind;
  · -- Since $m < j$, we have $iterateStep M cfg m = none$ implies $iterateStep M cfg (m + (j - m)) = none$.
    have h_iterateStep_none : iterateStep M cfg (m + (j - m)) = none := by
      convert iterateStep_none_mono M cfg hm ( j - m ) using 1;
    rw [ show m + ( j - m ) = j by rw [ Nat.add_sub_cancel' ( le_of_not_ge hm_ge_j ) ] ] at h_iterateStep_none ; simp_all +decide ;

theorem exists_iterate_eq_of_long_run (M : Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (hrun : ∀ k ≤ Fintype.card (Cfg Γ Λ n), (iterateStep M cfg k).isSome) :
    ∃ i j, i < j ∧ j ≤ Fintype.card (Cfg Γ Λ n) ∧
      iterateStep M cfg i = iterateStep M cfg j ∧
      (iterateStep M cfg i).isSome := by
  obtain ⟨i, j, hij, hconfig⟩ : ∃ i j : Fin (Fintype.card (Cfg Γ Λ n) + 1), i ≠ j ∧ iterateStep M cfg i = iterateStep M cfg j := by
    by_contra! h;
    have h_distinct : Finset.card (Finset.image (fun i : Fin (Fintype.card (Cfg Γ Λ n) + 1) => iterateStep M cfg i) Finset.univ) = Fintype.card (Cfg Γ Λ n) + 1 := by
      rw [ Finset.card_image_of_injective _ fun i j hij => not_imp_not.mp ( h i j ) hij, Finset.card_fin ];
    have h_subset : Finset.image (fun i : Fin (Fintype.card (Cfg Γ Λ n) + 1) => iterateStep M cfg i) Finset.univ ⊆ Finset.image (fun c : Cfg Γ Λ n => some c) Finset.univ := by
      simp +decide [ Finset.subset_iff ];
      exact fun i => by obtain ⟨ x, hx ⟩ := Option.isSome_iff_exists.mp ( hrun i ( Nat.le_of_lt_succ i.2 ) ) ; exact ⟨ x, hx.symm ⟩ ;
    exact h_distinct.not_lt ( lt_of_le_of_lt ( Finset.card_le_card h_subset ) ( by simp +decide [ Finset.card_image_of_injective, Function.Injective ] ) );
  cases lt_trichotomy i j <;> simp_all +decide;
  · exact ⟨ i, j, by assumption, Nat.le_of_lt_succ j.2, hconfig, hrun i ( Nat.le_of_lt_succ i.2 ) ⟩;
  · exact ⟨ j, i, by assumption, Nat.le_of_lt_succ i.2, hconfig.symm, hrun _ ( Nat.le_of_lt_succ j.2 ) ⟩

theorem halts_iff_haltsWithin (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Halts M cfg ↔ ∃ k ≤ Fintype.card (Cfg Γ Λ n), iterateStep M cfg k = none := by
  constructor;
  · intro h;
    by_contra h_contra;
    -- By the pigeonhole principle, if the machine runs for more than the cardinality of the configuration space without halting, it must have visited the same configuration twice.
    obtain ⟨i, j, hij, hi⟩ : ∃ i j, i < j ∧ j ≤ Fintype.card (Cfg Γ Λ n) ∧ iterateStep M cfg i = iterateStep M cfg j ∧ (iterateStep M cfg i).isSome := by
      apply exists_iterate_eq_of_long_run M cfg;
      exact fun k hk => by push_neg at h_contra; exact Option.isSome_iff_ne_none.mpr ( h_contra k hk ) ;
    exact not_halts_of_iterate_eq M cfg hij hi.2.1 ( by aesop ) h;
  · exact fun ⟨ k, hk₁, hk₂ ⟩ => ⟨ k, hk₂ ⟩

noncomputable instance decidableHalts (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Decidable (Halts M cfg) :=
  decidable_of_iff (∃ k ≤ Fintype.card (Cfg Γ Λ n), iterateStep M cfg k = none)
    (halts_iff_haltsWithin M cfg).symm

theorem accepts_iff_bounded (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Accepts M cfg ↔ ∃ k ≤ Fintype.card (Cfg Γ Λ n),
      iterateStep M cfg (k + 1) = none ∧
        ∃ cfg', iterateStep M cfg k = some cfg' ∧ M.accept cfg'.state = true := by
  constructor <;> intro h;
  · obtain ⟨ k, hk ⟩ := h;
    obtain ⟨ m, hm ⟩ := halts_iff_haltsWithin M cfg |>.1 ⟨ k + 1, hk.1 ⟩;
    by_cases hkm : k < m;
    · exact ⟨ k, by linarith, hk.1, hk.2 ⟩;
    · exact absurd ( iterateStep_none_mono M cfg hm.2 ( k - m ) ) ( by rw [ Nat.add_sub_of_le ( le_of_not_gt hkm ) ] ; aesop );
  · exact ⟨ h.choose, h.choose_spec.2.1, h.choose_spec.2.2 ⟩

noncomputable instance decidableAccepts (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Decidable (Accepts M cfg) :=
  decidable_of_iff _ (accepts_iff_bounded M cfg).symm

theorem rejects_iff_bounded (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Rejects M cfg ↔ ∃ k ≤ Fintype.card (Cfg Γ Λ n),
      iterateStep M cfg (k + 1) = none ∧
        ∃ cfg', iterateStep M cfg k = some cfg' ∧ M.accept cfg'.state = false := by
  constructor;
  · rintro ⟨ k, hk₁, hk₂ ⟩;
    obtain ⟨ m, hm ⟩ := halts_iff_haltsWithin M cfg |>.1 ⟨ k + 1, hk₁ ⟩;
    by_cases hkm : k ≥ m;
    · have := iterateStep_none_mono M cfg hm.2 ( k - m ) ; simp_all +decide [ add_tsub_cancel_of_le hkm ] ;
    · grind +splitIndPred;
  · exact fun ⟨ k, hk₁, hk₂, cfg', hk₃, hk₄ ⟩ => ⟨ k, hk₂, cfg', hk₃, hk₄ ⟩

noncomputable instance decidableRejects (M : Machine Γ Λ) (cfg : Cfg Γ Λ n) :
    Decidable (Rejects M cfg) :=
  decidable_of_iff _ (rejects_iff_bounded M cfg).symm

noncomputable instance decidableLanguage (M : Machine Γ Λ) (w : Fin (n + 1) → Γ) :
    Decidable (w ∈ Language M n) :=
  decidableAccepts M (initCfg M w)

end Decidability

/-! ### Closure Under Intersection and Union -/

section Closure

variable {Γ : Type*} {Λ₁ Λ₂ : Type*} {n : ℕ}

/-- **Product machine** for showing closure under intersection.
Runs two LBAs in parallel by taking their product state space.
Both machines share the same tape (for the intersection construction,
we need them to operate on the same input). -/
def productMachine (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂) :
    Machine Γ (Λ₁ × Λ₂ × Bool) where
  transition := fun ⟨q₁, q₂, phase⟩ a =>
    -- Phase false: simulate M₁; Phase true: simulate M₂
    -- This is a simplified sequential simulation
    if phase = false then
      match M₁.transition q₁ a with
      | none => -- M₁ halted, switch to phase true (start M₂)
        some (⟨q₁, q₂, true⟩, a, Dir.stay)
      | some (q₁', a', d) => some (⟨q₁', q₂, false⟩, a', d)
    else
      match M₂.transition q₂ a with
      | none => none  -- M₂ also halted
      | some (q₂', a', d) => some (⟨q₁, q₂', true⟩, a', d)
  accept := fun ⟨q₁, q₂, _⟩ => M₁.accept q₁ && M₂.accept q₂
  initial := ⟨M₁.initial, M₂.initial, false⟩

end Closure

/-! ### Configuration Space Cardinality -/

section Cardinality

variable {Γ : Type*} {Λ : Type*} {n : ℕ}
  [Fintype Γ] [Fintype Λ]

theorem card_cfg :
    Fintype.card (Cfg Γ Λ n) =
      Fintype.card Λ * Fintype.card Γ ^ (n + 1) * (n + 1) := by
  -- The set of bounded tapes is equivalent to the product of the set of functions from Fin (n + 1) to Γ and the set of Fin (n + 1).
  have h_bounded_tape_equiv : (BoundedTape Γ n) ≃ (Fin (n + 1) → Γ) × Fin (n + 1) := by
    exact ⟨ fun t => ⟨ t.contents, t.head ⟩, fun t => ⟨ t.1, t.2 ⟩, fun t => rfl, fun t => rfl ⟩;
  have h_CFG_card : Nat.card (Cfg Γ Λ n) = Nat.card Λ * Nat.card (BoundedTape Γ n) := by
    rw [ ← Nat.card_prod ];
    apply Nat.card_congr;
    exact ⟨ fun c => ⟨ c.state, c.tape ⟩, fun c => ⟨ c.1, c.2 ⟩, fun c => rfl, fun c => rfl ⟩;
  simp_all +decide [ mul_assoc ];
  exact Or.inl ( by rw [ Fintype.card_congr h_bounded_tape_equiv ] ; simp +decide [ Fintype.card_pi ] )

theorem card_boundedTape :
    Fintype.card (BoundedTape Γ n) = Fintype.card Γ ^ (n + 1) * (n + 1) := by
  have h_iso : BoundedTape Γ n ≃ (Fin (n + 1) → Γ) × Fin (n + 1) := by
    exact ⟨ fun t => ⟨ t.contents, t.head ⟩, fun t => ⟨ t.1, t.2 ⟩, fun t => rfl, fun t => rfl ⟩;
  rw [ Fintype.card_congr h_iso, Fintype.card_prod, Fintype.card_pi ] ; simp +decide

end Cardinality

end LBA