module

public import Langlib.Automata.LinearBounded.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# A same-width three-matching normal form for LBAs

Given an LBA `M`, this compiler replaces every control state by an `input` and an `output`
copy.  An input configuration has one symbol-preserving stay edge to the corresponding output
configuration.  An output configuration performs one genuine `M` step and returns to the input
copy of its target state.  Accepting states occur only in the input phase.

If the old configuration relation is partitioned into two bi-unique layers, old edges retain
their old color and the new input-to-output edges receive a fresh third color.  Every resulting
color is a directed matching: it is bi-unique and contains no composable pair of edges.  The
compiler preserves the tape alphabet and tape width exactly.

All operational statements below concern the complete fixed-width configuration graph, not
only configurations reachable from a canonical input.  In particular the step inversion and
acyclicity theorems include every raw configuration.
-/

namespace LBA

open Classical Relation Set

variable {Γ Λ : Type*}

/-- Input and output copies of a source-machine control state. -/
public inductive ThreeMatchingState (Λ : Type*) where
  | input (state : Λ)
  | output (state : Λ)
  deriving DecidableEq, Fintype

/-- Split every source step into a fresh internal edge followed by the genuine source step. -/
public def Machine.threeMatchings (M : Machine Γ Λ) :
    Machine Γ (ThreeMatchingState Λ) where
  transition state symbol :=
    match state with
    | .input source => {(.output source, symbol, DLBA.Dir.stay)}
    | .output source =>
        (fun move : Λ × Γ × DLBA.Dir =>
          (ThreeMatchingState.input move.1, move.2.1, move.2.2)) ''
            M.transition source symbol
  accept
    | .input state => M.accept state
    | .output _ => false
  initial := .input M.initial

/-- Embed a source configuration into the accepting/input phase. -/
@[expose]
public def threeMatchingInputCfg {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg Γ (ThreeMatchingState Λ) n :=
  ⟨.input cfg.state, cfg.tape⟩

/-- Embed a source configuration into the nonaccepting/output phase. -/
@[expose]
public def threeMatchingOutputCfg {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg Γ (ThreeMatchingState Λ) n :=
  ⟨.output cfg.state, cfg.tape⟩

/-- Forget the phase of a split configuration. -/
@[expose]
public def threeMatchingProjectCfg {n : ℕ}
    (cfg : DLBA.Cfg Γ (ThreeMatchingState Λ) n) : DLBA.Cfg Γ Λ n :=
  match cfg.state with
  | .input state => ⟨state, cfg.tape⟩
  | .output state => ⟨state, cfg.tape⟩

@[simp]
public theorem threeMatchingProjectCfg_input {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    threeMatchingProjectCfg (threeMatchingInputCfg cfg) = cfg := rfl

@[simp]
public theorem threeMatchingProjectCfg_output {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    threeMatchingProjectCfg (threeMatchingOutputCfg cfg) = cfg := rfl

private theorem write_read_stay {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    (tape.write tape.read).moveHead .stay = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
    Function.update_eq_self]

/-! ## Exact raw-configuration step semantics -/

/-- An input configuration has exactly its symbol-preserving output copy as successor. -/
public theorem Machine.step_threeMatchings_input_iff
    (M : Machine Γ Λ) {n : ℕ} (state : Λ) (tape : DLBA.BoundedTape Γ n)
    (target : DLBA.Cfg Γ (ThreeMatchingState Λ) n) :
    Step M.threeMatchings ⟨.input state, tape⟩ target ↔
      target = ⟨.output state, tape⟩ := by
  constructor
  · rintro ⟨next, written, direction, hmem, rfl⟩
    simp only [Machine.threeMatchings, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    exact congrArg
      (fun nextTape =>
        (⟨ThreeMatchingState.output state, nextTape⟩ :
          DLBA.Cfg Γ (ThreeMatchingState Λ) n))
      (write_read_stay tape)
  · rintro rfl
    refine ⟨.output state, tape.read, .stay, ?_, ?_⟩
    · simp [Machine.threeMatchings]
    · exact congrArg
        (fun nextTape =>
          (⟨ThreeMatchingState.output state, nextTape⟩ :
            DLBA.Cfg Γ (ThreeMatchingState Λ) n))
        (write_read_stay tape).symm

/-- An output configuration performs exactly one enabled transition of the source machine. -/
public theorem Machine.step_threeMatchings_output_iff
    (M : Machine Γ Λ) {n : ℕ} (state : Λ) (tape : DLBA.BoundedTape Γ n)
    (target : DLBA.Cfg Γ (ThreeMatchingState Λ) n) :
    Step M.threeMatchings ⟨.output state, tape⟩ target ↔
      ∃ next written direction,
        (next, written, direction) ∈ M.transition state tape.read ∧
        target = ⟨.input next, (tape.write written).moveHead direction⟩ := by
  constructor
  · rintro ⟨next, written, direction, hmem, rfl⟩
    simp only [Machine.threeMatchings] at hmem
    obtain ⟨move, henabled, hmove⟩ := hmem
    simp only [Prod.mk.injEq] at hmove
    rcases hmove with ⟨rfl, rfl, rfl⟩
    exact ⟨move.1, move.2.1, move.2.2, henabled, rfl⟩
  · rintro ⟨next, written, direction, henabled, rfl⟩
    refine ⟨.input next, written, direction, ?_, rfl⟩
    exact ⟨(next, written, direction), henabled, rfl⟩

/-- Complete phase-explicit characterization of the compiled step relation. -/
public theorem Machine.step_threeMatchings_iff
    (M : Machine Γ Λ) {n : ℕ}
    (source target : DLBA.Cfg Γ (ThreeMatchingState Λ) n) :
    Step M.threeMatchings source target ↔
      (∃ cfg : DLBA.Cfg Γ Λ n,
        source = threeMatchingInputCfg cfg ∧
          target = threeMatchingOutputCfg cfg) ∨
      (∃ old new : DLBA.Cfg Γ Λ n,
        Step M old new ∧ source = threeMatchingOutputCfg old ∧
          target = threeMatchingInputCfg new) := by
  rcases source with ⟨sourceState, sourceTape⟩
  cases sourceState with
  | input state =>
      rw [M.step_threeMatchings_input_iff]
      constructor
      · intro h
        left
        exact ⟨⟨state, sourceTape⟩, rfl, h⟩
      · rintro (⟨cfg, hsource, htarget⟩ | ⟨old, new, _, hsource, _⟩)
        · have hcfg : cfg = ⟨state, sourceTape⟩ := by
            simpa [threeMatchingInputCfg] using
              (congrArg threeMatchingProjectCfg hsource).symm
          subst cfg
          exact htarget
        · cases old
          simp [threeMatchingOutputCfg] at hsource
  | output state =>
      rw [M.step_threeMatchings_output_iff]
      constructor
      · rintro ⟨next, written, direction, henabled, rfl⟩
        right
        refine ⟨⟨state, sourceTape⟩,
          ⟨next, (sourceTape.write written).moveHead direction⟩, ?_, rfl, rfl⟩
        exact ⟨next, written, direction, henabled, rfl⟩
      · rintro (⟨cfg, hsource, _⟩ | ⟨old, new, hstep, hsource, htarget⟩)
        · cases cfg
          simp [threeMatchingInputCfg] at hsource
        · have hold : old = ⟨state, sourceTape⟩ := by
            simpa [threeMatchingOutputCfg] using
              (congrArg threeMatchingProjectCfg hsource).symm
          subst old
          rcases hstep with ⟨next, written, direction, henabled, rfl⟩
          exact ⟨next, written, direction, henabled, htarget⟩

/-- Between an output copy and an input copy, compiled stepping is exactly source stepping. -/
public theorem Machine.step_threeMatchingOutput_input_iff
    (M : Machine Γ Λ) {n : ℕ} (source target : DLBA.Cfg Γ Λ n) :
    Step M.threeMatchings (threeMatchingOutputCfg source)
        (threeMatchingInputCfg target) ↔
      Step M source target := by
  rcases source with ⟨state, tape⟩
  constructor
  · intro hstep
    obtain ⟨next, written, direction, henabled, heq⟩ :=
      (M.step_threeMatchings_output_iff state tape _).1 hstep
    exact ⟨next, written, direction, henabled,
      congrArg threeMatchingProjectCfg heq⟩
  · rintro ⟨next, written, direction, henabled, rfl⟩
    exact (M.step_threeMatchings_output_iff state tape _).2
      ⟨next, written, direction, henabled, rfl⟩

/-- Every compiled edge either stutters under projection or projects to one source edge. -/
public theorem Machine.threeMatchingProjectCfg_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg Γ (ThreeMatchingState Λ) n}
    (hstep : Step M.threeMatchings source target) :
    threeMatchingProjectCfg source = threeMatchingProjectCfg target ∨
      Step M (threeMatchingProjectCfg source) (threeMatchingProjectCfg target) := by
  rw [M.step_threeMatchings_iff] at hstep
  rcases hstep with ⟨cfg, rfl, rfl⟩ | ⟨old, new, hedge, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr hedge

/-! ## Exact reachability and language preservation -/

/-- One source edge expands to an internal edge followed by an external edge. -/
public theorem Machine.reaches_threeMatchingInput_of_step
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hstep : Step M source target) :
    Reaches M.threeMatchings (threeMatchingInputCfg source)
      (threeMatchingInputCfg target) := by
  apply ReflTransGen.head
      ((M.step_threeMatchings_input_iff source.state source.tape
        (threeMatchingOutputCfg source)).2 rfl)
  apply ReflTransGen.single
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  exact (M.step_threeMatchings_output_iff source.state source.tape _).2
    ⟨next, written, direction, henabled, rfl⟩

/-- Every source run lifts between input-phase configurations. -/
public theorem Machine.reaches_threeMatchingInput_of_reaches
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hreach : Reaches M source target) :
    Reaches M.threeMatchings (threeMatchingInputCfg source)
      (threeMatchingInputCfg target) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.trans (M.reaches_threeMatchingInput_of_step hstep)

/-- Projecting an arbitrary compiled run deletes internal edges and retains source edges. -/
public theorem Machine.reaches_project_of_threeMatchings_reaches
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg Γ (ThreeMatchingState Λ) n}
    (hreach : Reaches M.threeMatchings source target) :
    Reaches M (threeMatchingProjectCfg source)
      (threeMatchingProjectCfg target) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases M.threeMatchingProjectCfg_step hstep with heq | hedge
      · simpa only [heq] using ih
      · exact ih.tail hedge

/-- Source reachability is exactly compiled reachability between input-phase copies. -/
public theorem Machine.reaches_threeMatchingInput_iff
    (M : Machine Γ Λ) {n : ℕ} (source target : DLBA.Cfg Γ Λ n) :
    Reaches M.threeMatchings (threeMatchingInputCfg source)
        (threeMatchingInputCfg target) ↔
      Reaches M source target := by
  constructor
  · intro hreach
    simpa using M.reaches_project_of_threeMatchings_reaches hreach
  · exact M.reaches_threeMatchingInput_of_reaches

/-- Compiled acceptance from an input phase is exactly source-machine acceptance. -/
public theorem Machine.accepts_threeMatchings_iff
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Accepts M.threeMatchings (threeMatchingInputCfg cfg) ↔ Accepts M cfg := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    have hproject := M.reaches_project_of_threeMatchings_reaches hreach
    rcases target with ⟨targetState, targetTape⟩
    cases targetState with
    | input state =>
        exact ⟨⟨state, targetTape⟩, hproject, haccept⟩
    | output state =>
        simp [Machine.threeMatchings] at haccept
  · rintro ⟨target, hreach, haccept⟩
    exact ⟨threeMatchingInputCfg target,
      M.reaches_threeMatchingInput_of_reaches hreach, haccept⟩

@[simp]
public theorem Machine.initCfgEnd_threeMatchings
    {T : Type*} (M : Machine (EndAlpha T Γ) Λ) (word : List T) :
    initCfgEnd M.threeMatchings word = threeMatchingInputCfg (initCfgEnd M word) := rfl

/-- The split compiler preserves the canonical endmarker language exactly, including `ε`. -/
public theorem Machine.languageEnd_threeMatchings_eq
    {T : Type*} (M : Machine (EndAlpha T Γ) Λ) :
    LanguageEnd M.threeMatchings = LanguageEnd M := by
  funext word
  apply propext
  change Accepts M.threeMatchings (threeMatchingInputCfg (initCfgEnd M word)) ↔
    Accepts M (initCfgEnd M word)
  exact M.accepts_threeMatchings_iff _

end LBA

end
