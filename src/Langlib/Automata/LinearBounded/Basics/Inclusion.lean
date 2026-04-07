import Mathlib
import Langlib.Automata.LinearBounded.Definition
import Langlib.Automata.NondeterministicLinearBounded.Definition

/-!
# Deterministic LBA Languages ⊆ Nondeterministic LBA Languages

We show that every language recognized by a deterministic linearly bounded automaton (LBA)
is also recognized by a nondeterministic linearly bounded automaton (NLBA).

## Strategy

The conversion uses `Option Λ` as the NLBA state space:
- `some q` simulates LBA state `q` (always non-accepting in the NLBA)
- `none` is a special accepting halt state

When the LBA halts (`transition` returns `none`) in an accepting state, the NLBA
transitions to `none`. This ensures the NLBA accepts (reaches an accepting state)
if and only if the LBA accepts (halts in an accepting state).

## Main Results

* `is_LBA_subset_is_NLBA` — Every LBA language is an NLBA language
-/

namespace LBA

open NLBA

/-! ### Conversion from LBA to NLBA -/

/-- Convert a deterministic LBA to a nondeterministic LBA using `Option Λ` states.
- `some q` simulates LBA state `q` (non-accepting)
- `none` is the accepting halt state
When the LBA halts in an accepting state, we transition to `none`. -/
def toNLBA' {Γ : Type*} {Λ : Type*} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) : NLBA.Machine Γ (Option Λ) where
  transition := fun q a =>
    match q with
    | none => ∅
    | some q =>
      match M.transition q a with
      | some (q', a', d) => {(some q', a', d)}
      | none => if M.accept q then {(none, a, LBA.Dir.stay)} else ∅
  accept := fun q =>
    match q with
    | none => true
    | some _ => false
  initial := some M.initial

/-! ### Step Correspondence -/

/-
If the LBA takes a step from state q, the converted NLBA takes the corresponding step.
-/
theorem lba_step_implies_nlba_step {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (cfg : Cfg Γ Λ n) (cfg' : Cfg Γ Λ n)
    (h : LBA.step M cfg = some cfg') :
    NLBA.Step (toNLBA' M)
      ⟨some cfg.state, cfg.tape⟩
      ⟨some cfg'.state, cfg'.tape⟩ := by
  unfold step at h;
  rcases h' : M.transition cfg.state cfg.tape.read with ( _ | ⟨ q', a, d ⟩ ) <;> simp_all +decide;
  exact ⟨ q', a, d, by unfold toNLBA'; aesop ⟩

/-
If the LBA halts in an accepting state, the NLBA can transition to the accepting
halt state `none`.
-/
theorem lba_halt_accept_implies_nlba_step {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (h_halt : LBA.step M cfg = none)
    (h_acc : M.accept cfg.state = true) :
    NLBA.Step (toNLBA' M)
      ⟨some cfg.state, cfg.tape⟩
      ⟨none, cfg.tape⟩ := by
  use none, cfg.tape.read, LBA.Dir.stay;
  simp_all +decide [ BoundedTape.write, BoundedTape.moveHead ];
  unfold toNLBA';
  unfold step at h_halt; aesop;

/-! ### Multi-step Correspondence -/

/-- Lift a single LBA configuration to the NLBA state space. -/
def liftCfg {Γ : Type*} {Λ : Type*} {n : ℕ}
    (cfg : Cfg Γ Λ n) : LBA.Cfg Γ (Option Λ) n :=
  ⟨some cfg.state, cfg.tape⟩

/-
If `iterateStep M cfg k = some cfg'`, then the converted NLBA can reach
`liftCfg cfg'` from `liftCfg cfg`.
-/
theorem iterateStep_implies_nlba_reaches {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (cfg cfg' : Cfg Γ Λ n) {k : ℕ}
    (hk : iterateStep M cfg k = some cfg') :
    NLBA.Reaches (toNLBA' M) (liftCfg cfg) (liftCfg cfg') := by
  induction' k with k ih generalizing cfg cfg';
  · cases cfg' ; cases cfg ; cases hk ; tauto;
  · obtain ⟨cfg'', hk''⟩ : ∃ cfg'', iterateStep M cfg k = some cfg'' ∧ LBA.step M cfg'' = some cfg' := by
      exact Option.bind_eq_some_iff.mp hk;
    exact Relation.ReflTransGen.trans ( ih cfg cfg'' hk''.1 ) ( Relation.ReflTransGen.single ( lba_step_implies_nlba_step M cfg'' cfg' hk''.2 ) )

/-! ### Acceptance Correspondence -/

/-
If the deterministic LBA accepts, the converted NLBA also accepts (from the
lifted initial configuration).
-/
theorem lba_accepts_implies_nlba_accepts' {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (h : LBA.Accepts M cfg) :
    NLBA.Accepts (toNLBA' M) (liftCfg cfg) := by
  obtain ⟨ k, hk₁, cfg', hk₂, hk₃ ⟩ := h;
  -- Use `lba_halt_accept_implies_nlba_step` to get the step from `liftCfg cfg'` to `⟨none, cfg'.tape⟩`.
  have h_step : NLBA.Step (toNLBA' M) ⟨some cfg'.state, cfg'.tape⟩ ⟨none, cfg'.tape⟩ := by
    apply lba_halt_accept_implies_nlba_step;
    · rw [ iterateStep_succ, hk₂ ] at hk₁ ; aesop;
    · exact hk₃;
  refine' ⟨ _, _, _ ⟩;
  exact ⟨ none, cfg'.tape ⟩;
  · exact Relation.ReflTransGen.tail ( iterateStep_implies_nlba_reaches M cfg cfg' hk₂ ) h_step;
  · rfl

/-
Conversely, if the converted NLBA accepts from a lifted configuration, then the
original LBA also accepts.

For a step from `some q` in the converted NLBA, the result is either `some q'`
(simulating an LBA step) or `none` (LBA halts in accepting state).
-/
theorem toNLBA'_step_cases {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (q : Λ) (tape : BoundedTape Γ n)
    (cfg' : Cfg Γ (Option Λ) n)
    (h : NLBA.Step (toNLBA' M) ⟨some q, tape⟩ cfg') :
    (∃ q' tape', cfg' = ⟨some q', tape'⟩ ∧ LBA.step M ⟨q, tape⟩ = some ⟨q', tape'⟩) ∨
    (cfg' = ⟨none, tape⟩ ∧ LBA.step M ⟨q, tape⟩ = none ∧ M.accept q = true) := by
  cases cfg' ; simp_all +decide [ Step ];
  rcases h with ⟨ a, d, h, rfl ⟩;
  unfold toNLBA' at h;
  unfold step; simp +decide;
  cases h' : M.transition q ( tape.contents tape.head ) <;> simp +decide [ h' ] at h ⊢;
  · unfold BoundedTape.write BoundedTape.moveHead; aesop;
  · grind +splitImp

/-
If the converted NLBA reaches a configuration from `liftCfg cfg`, then either
the state is `some q` with a corresponding LBA iterateStep, or the LBA accepts.
-/
theorem toNLBA'_reaches_inv {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (cfg' : Cfg Γ (Option Λ) n)
    (h : NLBA.Reaches (toNLBA' M) (liftCfg cfg) cfg') :
    (∃ cfg_lba : Cfg Γ Λ n, cfg'.state = some cfg_lba.state ∧ cfg'.tape = cfg_lba.tape ∧
      ∃ k, iterateStep M cfg k = some cfg_lba) ∨
    (cfg'.state = none ∧ LBA.Accepts M cfg) := by
  induction' h with cfg'' cfg''' h;
  · exact Or.inl ⟨ cfg, rfl, rfl, 0, rfl ⟩;
  · rename_i h₁ h₂;
    rcases h₂ with ( ⟨ cfg_lba, h₂, h₃, k, hk ⟩ | ⟨ h₂, h₃ ⟩ ) <;> simp_all +decide [ Step ];
    · rcases h₁ with ⟨ q', a, d, h₁, rfl ⟩;
      unfold toNLBA' at h₁; simp_all +decide;
      rcases h : M.transition cfg_lba.state ( cfg_lba.tape.contents cfg_lba.tape.head ) with ( _ | ⟨ q', a', d' ⟩ ) <;> simp_all +decide;
      · use k;
        simp_all +decide [ iterateStep_succ ];
        unfold step; aesop;
      · refine' ⟨ ⟨ q', ( cfg_lba.tape.write a' ).moveHead d' ⟩, _, _, k + 1, _ ⟩ <;> simp_all +decide [ iterateStep_succ ];
        unfold step; aesop;
    · unfold toNLBA' at h₁; aesop;

theorem nlba_accepts_implies_lba_accepts' {Γ : Type*} {Λ : Type*} {n : ℕ} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (cfg : Cfg Γ Λ n)
    (h : NLBA.Accepts (toNLBA' M) (liftCfg cfg)) :
    LBA.Accepts M cfg := by
  obtain ⟨ cfg', hcfg', hcfg'' ⟩ := h;
  obtain ⟨ cfg_lba, hcfg_lba₁, hcfg_lba₂, k, hk ⟩ | hcfg_lba₃ := toNLBA'_reaches_inv M cfg cfg' hcfg';
  · unfold toNLBA' at hcfg''; aesop;
  · exact hcfg_lba₃.2

/-! ### Language Definitions for LBA -/

/-- Load a non-empty list onto a bounded tape for a deterministic LBA. -/
noncomputable def loadListLBA {Γ : Type*} (w : List Γ) (hw : w ≠ []) :
    BoundedTape Γ (w.length - 1) :=
  ⟨fun i => w.get ⟨i.val, by have := i.isLt; have := List.length_pos_of_ne_nil hw; omega⟩,
   ⟨0, by have := List.length_pos_of_ne_nil hw; omega⟩⟩

/-- Initial configuration for a non-empty list input on a deterministic LBA. -/
noncomputable def initCfgListLBA {Γ : Type*} {Λ : Type*}
    (M : LBA.Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    Cfg Γ Λ (w.length - 1) :=
  ⟨M.initial, loadListLBA w hw⟩

/-- Recognition via an embedding from the input alphabet into the tape alphabet,
for a deterministic LBA. -/
noncomputable def LanguageViaEmbedLBA {T Γ : Type*} {Λ : Type*}
    (M : LBA.Machine Γ Λ) (embed : T → Γ) : _root_.Language T :=
  fun w => ∃ (hw : w.map embed ≠ []),
    LBA.Accepts M (initCfgListLBA M (w.map embed) hw)

/-! ### Initial Configuration Correspondence -/

/-
The lifted LBA initial configuration equals the NLBA initial configuration.
-/
theorem initCfg_lift_eq {Γ : Type*} {Λ : Type*} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    liftCfg (initCfgListLBA M w hw) =
    NLBA.initCfgList (toNLBA' M) w hw := by
  rfl

end LBA

/-! ### Main Theorem -/

/-
The language via embedding for the LBA equals that of the converted NLBA.
-/
theorem lba_language_eq_nlba_language {T Γ : Type*} {Λ : Type*} [DecidableEq Γ]
    (M : LBA.Machine Γ Λ) (embed : T → Γ) :
    LBA.LanguageViaEmbedLBA M embed = NLBA.LanguageViaEmbed (LBA.toNLBA' M) embed := by
  -- By definition of `LanguageViaEmbedLBA` and `LanguageViaEmbed`, we can show that they are equal by showing that the acceptance conditions are equivalent.
  funext w
  simp [LBA.LanguageViaEmbedLBA, NLBA.LanguageViaEmbed];
  grind +suggestions

/-
**Main theorem**: Every deterministic LBA language is also an NLBA language.
-/
theorem is_LBA_subset_is_NLBA {T : Type} {L : _root_.Language T}
    (h : is_LBA L) : is_NLBA L := by
  obtain ⟨ Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, embed, M, hM ⟩ := h;
  use Γ, Option Λ;
  use inferInstance, inferInstance, inferInstance, inferInstance;
  exact ⟨ embed, LBA.toNLBA' M, lba_language_eq_nlba_language M embed ▸ hM ⟩

theorem LBA_subset_NLBA {T : Type} : (LBA : Set (Language T)) ⊆ NLBA := by
  intro L hL
  simp [LBA] at hL
  exact is_LBA_subset_is_NLBA hL
