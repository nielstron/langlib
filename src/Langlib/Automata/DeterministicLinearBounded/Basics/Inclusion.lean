import Mathlib
import Langlib.Automata.DeterministicLinearBounded.Definition
import Langlib.Automata.LinearBounded.Definition

/-!
# Deterministic LBA Languages ⊆ LBA Languages

We show that every language recognized by a deterministic linearly bounded automaton (DLBA)
is also recognized by a nondeterministic linearly bounded automaton (LBA).

## Strategy

The conversion uses `Option Λ` as the LBA state space:
- `some q` simulates LBA state `q` (always non-accepting in the NLBA)
- `none` is a special accepting halt state

When the DLBA halts (`transition` returns `none`) in an accepting state, the LBA
transitions to `none`. This ensures the LBA accepts (reaches an accepting state)
if and only if the DLBA accepts (halts in an accepting state).

## Main Results

* `is_DLBA_subset_is_LBA` — Every DLBA language is an LBA language
-/

namespace DLBA

open LBA

/-! ### Conversion from DLBA to LBA -/

/-- Convert a deterministic DLBA to an LBA using `Option Λ` states.
- `some q` simulates DLBA state `q` (non-accepting)
- `none` is the accepting halt state
When the DLBA halts in an accepting state, we transition to `none`. -/
def toLBA' {Γ : Type*} {Λ : Type*} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) : LBA.Machine Γ (Option Λ) where
  transition := fun q a =>
    match q with
    | none => ∅
    | some q =>
      match M.transition q a with
      | some (q', a', d) => {(some q', a', d)}
      | none => if M.accept q then {(none, a, DLBA.Dir.stay)} else ∅
  accept := fun q =>
    match q with
    | none => true
    | some _ => false
  initial := some M.initial

/-! ### Step Correspondence -/

/-
If the DLBA takes a step from state q, the converted LBA takes the corresponding step.
-/
theorem dlba_step_implies_lba_step {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (cfg : Cfg Γ Λ n) (cfg' : Cfg Γ Λ n)
    (h : DLBA.step M cfg = some cfg') :
    LBA.Step (toLBA' M)
      ⟨some cfg.state, cfg.tape⟩
      ⟨some cfg'.state, cfg'.tape⟩ := by
  unfold step at h;
  rcases h' : M.transition cfg.state cfg.tape.read with ( _ | ⟨ q', a, d ⟩ ) <;> simp_all +decide;
  exact ⟨ q', a, d, by unfold toLBA'; aesop ⟩

/-
If the DLBA halts in an accepting state, the LBA can transition to the accepting
halt state `none`.
-/
theorem dlba_halt_accept_implies_lba_step {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (h_halt : DLBA.step M cfg = none)
    (h_acc : M.accept cfg.state = true) :
    LBA.Step (toLBA' M)
      ⟨some cfg.state, cfg.tape⟩
      ⟨none, cfg.tape⟩ := by
  use none, cfg.tape.read, DLBA.Dir.stay;
  simp_all +decide [ BoundedTape.write, BoundedTape.moveHead ];
  unfold toLBA';
  unfold step at h_halt; aesop;

/-! ### Multi-step Correspondence -/

/-- Lift a single DLBA configuration to the LBA state space. -/
def liftCfg {Γ : Type*} {Λ : Type*} {n : ℕ}
    (cfg : Cfg Γ Λ n) : DLBA.Cfg Γ (Option Λ) n :=
  ⟨some cfg.state, cfg.tape⟩

/-
If `iterateStep M cfg k = some cfg'`, then the converted LBA can reach
`liftCfg cfg'` from `liftCfg cfg`.
-/
theorem iterateStep_implies_lba_reaches {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (cfg cfg' : Cfg Γ Λ n) {k : ℕ}
    (hk : iterateStep M cfg k = some cfg') :
    LBA.Reaches (toLBA' M) (liftCfg cfg) (liftCfg cfg') := by
  induction' k with k ih generalizing cfg cfg';
  · cases cfg' ; cases cfg ; cases hk ; tauto;
  · obtain ⟨cfg'', hk''⟩ : ∃ cfg'', iterateStep M cfg k = some cfg'' ∧ DLBA.step M cfg'' = some cfg' := by
      exact Option.bind_eq_some_iff.mp hk;
    exact Relation.ReflTransGen.trans ( ih cfg cfg'' hk''.1 ) ( Relation.ReflTransGen.single ( dlba_step_implies_lba_step M cfg'' cfg' hk''.2 ) )

/-! ### Acceptance Correspondence -/

/-
If the deterministic DLBA accepts, the converted LBA also accepts (from the
lifted initial configuration).
-/
theorem dlba_accepts_implies_lba_accepts' {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (h : DLBA.Accepts M cfg) :
    LBA.Accepts (toLBA' M) (liftCfg cfg) := by
  obtain ⟨ k, hk₁, cfg', hk₂, hk₃ ⟩ := h;
  -- Use `dlba_halt_accept_implies_lba_step` to get the step from `liftCfg cfg'` to `⟨none, cfg'.tape⟩`.
  have h_step : LBA.Step (toLBA' M) ⟨some cfg'.state, cfg'.tape⟩ ⟨none, cfg'.tape⟩ := by
    apply dlba_halt_accept_implies_lba_step;
    · rw [ iterateStep_succ, hk₂ ] at hk₁ ; aesop;
    · exact hk₃;
  refine' ⟨ _, _, _ ⟩;
  exact ⟨ none, cfg'.tape ⟩;
  · exact Relation.ReflTransGen.tail ( iterateStep_implies_lba_reaches M cfg cfg' hk₂ ) h_step;
  · rfl

/-
Conversely, if the converted LBA accepts from a lifted configuration, then the
original DLBA also accepts.

For a step from `some q` in the converted LBA, the result is either `some q'`
(simulating a DLBA step) or `none` (DLBA halts in accepting state).
-/
theorem toLBA'_step_cases {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (q : Λ) (tape : BoundedTape Γ n)
    (cfg' : Cfg Γ (Option Λ) n)
    (h : LBA.Step (toLBA' M) ⟨some q, tape⟩ cfg') :
    (∃ q' tape', cfg' = ⟨some q', tape'⟩ ∧ DLBA.step M ⟨q, tape⟩ = some ⟨q', tape'⟩) ∨
    (cfg' = ⟨none, tape⟩ ∧ DLBA.step M ⟨q, tape⟩ = none ∧ M.accept q = true) := by
  cases cfg' ; simp_all +decide [ Step ];
  rcases h with ⟨ a, d, h, rfl ⟩;
  unfold toLBA' at h;
  unfold step; simp +decide;
  cases h' : M.transition q ( tape.contents tape.head ) <;> simp +decide [ h' ] at h ⊢;
  · unfold BoundedTape.write BoundedTape.moveHead; aesop;
  · grind +splitImp

/-
If the converted LBA reaches a configuration from `liftCfg cfg`, then either
the state is `some q` with a corresponding DLBA iterateStep, or the DLBA accepts.
-/
theorem toLBA'_reaches_inv {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (cfg' : Cfg Γ (Option Λ) n)
    (h : LBA.Reaches (toLBA' M) (liftCfg cfg) cfg') :
    (∃ cfg_lba : Cfg Γ Λ n, cfg'.state = some cfg_lba.state ∧ cfg'.tape = cfg_lba.tape ∧
      ∃ k, iterateStep M cfg k = some cfg_lba) ∨
    (cfg'.state = none ∧ DLBA.Accepts M cfg) := by
  induction' h with cfg'' cfg''' h;
  · exact Or.inl ⟨ cfg, rfl, rfl, 0, rfl ⟩;
  · rename_i h₁ h₂;
    rcases h₂ with ( ⟨ cfg_lba, h₂, h₃, k, hk ⟩ | ⟨ h₂, h₃ ⟩ ) <;> simp_all +decide [ Step ];
    · rcases h₁ with ⟨ q', a, d, h₁, rfl ⟩;
      unfold toLBA' at h₁; simp_all +decide;
      rcases h : M.transition cfg_lba.state ( cfg_lba.tape.contents cfg_lba.tape.head ) with ( _ | ⟨ q', a', d' ⟩ ) <;> simp_all +decide;
      · use k;
        simp_all +decide [ iterateStep_succ ];
        unfold step; aesop;
      · refine' ⟨ ⟨ q', ( cfg_lba.tape.write a' ).moveHead d' ⟩, _, _, k + 1, _ ⟩ <;> simp_all +decide [ iterateStep_succ ];
        unfold step; aesop;
    · unfold toLBA' at h₁; aesop;

theorem lba_accepts_implies_dlba_accepts' {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (h : LBA.Accepts (toLBA' M) (liftCfg cfg)) :
    DLBA.Accepts M cfg := by
  obtain ⟨ cfg', hcfg', hcfg'' ⟩ := h;
  obtain ⟨ cfg_lba, hcfg_lba₁, hcfg_lba₂, k, hk ⟩ | hcfg_lba₃ := toLBA'_reaches_inv M cfg cfg' hcfg';
  · unfold toLBA' at hcfg''; aesop;
  · exact hcfg_lba₃.2

/-! ### Language Definitions For DLBAs -/

/-- Load a non-empty list onto a bounded tape for a deterministic DLBA. -/
noncomputable def loadListDLBA {Γ : Type*} (w : List Γ) (hw : w ≠ []) :
    BoundedTape Γ (w.length - 1) :=
  ⟨fun i => w.get ⟨i.val, by have := i.isLt; have := List.length_pos_of_ne_nil hw; omega⟩,
   ⟨0, by have := List.length_pos_of_ne_nil hw; omega⟩⟩

/-- Initial configuration for a non-empty list input on a deterministic DLBA. -/
noncomputable def initCfgListDLBA {Γ : Type*} {Λ : Type*}
    (M : DLBA.Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    Cfg Γ Λ (w.length - 1) :=
  ⟨M.initial, loadListDLBA w hw⟩

/-- Recognition via an embedding from the input alphabet into the tape alphabet,
for a deterministic DLBA. -/
noncomputable def LanguageViaEmbedDLBA {T Γ : Type*} {Λ : Type*}
    (M : DLBA.Machine Γ Λ) (embed : T → Γ) : _root_.Language T :=
  fun w => ∃ (hw : w.map embed ≠ []),
    DLBA.Accepts M (initCfgListDLBA M (w.map embed) hw)

/-! ### Initial Configuration Correspondence -/

/-
The lifted DLBA initial configuration equals the LBA initial configuration.
-/
theorem initCfg_lift_eq {Γ : Type*} {Λ : Type*} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    liftCfg (initCfgListDLBA M w hw) =
    LBA.initCfgList (toLBA' M) w hw := by
  rfl

end DLBA

/-! ### Main Theorem -/

/-
The language via embedding for the DLBA equals that of the converted LBA.
-/
theorem dlba_language_eq_lba_language {T Γ : Type*} {Λ : Type*} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) (embed : T → Γ) :
    DLBA.LanguageViaEmbedDLBA M embed = LBA.LanguageViaEmbed (DLBA.toLBA' M) embed := by
  funext w
  simp [DLBA.LanguageViaEmbedDLBA, LBA.LanguageViaEmbed];
  grind +suggestions

/-
**Main theorem**: Every deterministic LBA language is also an LBA language.
-/
theorem is_DLBA_subset_is_LBA {T : Type} {L : _root_.Language T}
    (h : is_DLBA L) : is_LBA L := by
  obtain ⟨ Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, embed, M, hM ⟩ := h;
  use Γ, Option Λ;
  use inferInstance, inferInstance, inferInstance, inferInstance;
  exact ⟨ embed, DLBA.toLBA' M, dlba_language_eq_lba_language M embed ▸ hM ⟩

theorem DLBA_subset_LBA {T : Type} : (DLBA : Set (Language T)) ⊆ LBA := by
  intro L hL
  simp [DLBA] at hL
  exact is_DLBA_subset_is_LBA hL
