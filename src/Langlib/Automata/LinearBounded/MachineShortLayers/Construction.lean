module

public import Langlib.Automata.LinearBounded.MachineShortLayers.StepLabelInjective

@[expose]
public section

/-!
# A local four-phase subdivision of LBA steps

This compiler replaces one source-machine step by four target-machine steps:

`core → chosen → landed → pad → core`.

`chosen` retains the finite local transition triple and the source state/read symbol.  The
`chosen → landed` edge performs the only genuine tape action.  `landed` deliberately forgets
the source label and is canonical for the resulting target configuration; this quotient is what
makes the construction realizable with finite control rather than an auxiliary vertex indexed by
a pair of whole configurations.  The other three edges write back the symbol currently under the
head and stay put.

All projection theorems quantify over raw configurations, including malformed intermediate
states.  In particular no reachability or tape-format promise is used for soundness.
-/

namespace LBA

open Classical

variable {Γ Λ : Type*}

/-- Finite control states of the local four-phase step compiler. -/
public inductive ShortLayerState (Γ Λ : Type*) where
  | core (state : Λ)
  | chosen (source : Λ) (expected : Γ) (move : LBA.Move Γ Λ)
  | landed (target : Λ)
  | pad (target : Λ)
  deriving DecidableEq, Fintype

/-- Replace every source transition by the four-phase local protocol. -/
public noncomputable def Machine.shortLayers
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) : Machine Γ (ShortLayerState Γ Λ) where
  transition state symbol :=
    match state with
    | .core source =>
        (fun move =>
          (ShortLayerState.chosen source symbol move, symbol, DLBA.Dir.stay)) ''
            M.transition source symbol
    | .chosen source expected move =>
        if symbol = expected ∧ move ∈ M.transition source expected then
          {(ShortLayerState.landed move.1, move.2.1, move.2.2)}
        else ∅
    | .landed target =>
        {(ShortLayerState.pad target, symbol, DLBA.Dir.stay)}
    | .pad target =>
        {(ShortLayerState.core target, symbol, DLBA.Dir.stay)}
  accept
    | .core state => M.accept state
    | .chosen _ _ _ => false
    | .landed _ => false
    | .pad _ => false
  initial := .core M.initial

/-- Embed a source configuration into the core phase. -/
public def shortLayerLiftCfg [Fintype Γ] [Fintype Λ]
    {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg Γ (ShortLayerState Γ Λ) n :=
  ⟨.core cfg.state, cfg.tape⟩

/-- Project every protocol phase to the represented source-machine configuration.  A chosen
configuration still represents its source; landed and padding configurations represent the
target reached by the saved move. -/
public def shortLayerProjectCfg [Fintype Γ] [Fintype Λ]
    {n : ℕ} (cfg : DLBA.Cfg Γ (ShortLayerState Γ Λ) n) :
    DLBA.Cfg Γ Λ n :=
  match cfg.state with
  | .core state => ⟨state, cfg.tape⟩
  | .chosen source _ _ => ⟨source, cfg.tape⟩
  | .landed target => ⟨target, cfg.tape⟩
  | .pad target => ⟨target, cfg.tape⟩

@[simp]
public theorem shortLayerProjectCfg_lift
    [Fintype Γ] [Fintype Λ] {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    shortLayerProjectCfg (shortLayerLiftCfg cfg) = cfg := rfl

private theorem write_read_stay {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    (tape.write tape.read).moveHead .stay = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
    Function.update_eq_self]

/-- The first dummy edge saves one enabled local transition without changing the tape. -/
public theorem Machine.step_shortLayer_core_chosen
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (move : LBA.Move Γ Λ)
    (henabled : move ∈ M.transition cfg.state cfg.tape.read) :
    Step M.shortLayers (shortLayerLiftCfg cfg)
      ⟨.chosen cfg.state cfg.tape.read move, cfg.tape⟩ := by
  refine ⟨.chosen cfg.state cfg.tape.read move, cfg.tape.read, .stay, ?_, ?_⟩
  · exact ⟨move, henabled, rfl⟩
  · exact congrArg
      (fun nextTape =>
        (⟨ShortLayerState.chosen cfg.state cfg.tape.read move, nextTape⟩ :
          DLBA.Cfg Γ (ShortLayerState Γ Λ) n))
      (write_read_stay cfg.tape).symm

/-- The second edge performs the saved genuine source-machine move. -/
public theorem Machine.step_shortLayer_chosen_landed
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (move : LBA.Move Γ Λ)
    (henabled : move ∈ M.transition cfg.state cfg.tape.read) :
    Step M.shortLayers
      ⟨.chosen cfg.state cfg.tape.read move, cfg.tape⟩
      ⟨.landed move.1, (cfg.tape.write move.2.1).moveHead move.2.2⟩ := by
  refine ⟨.landed move.1, move.2.1, move.2.2, ?_, rfl⟩
  simp only [Machine.shortLayers]
  have henabled' : move ∈
      M.transition cfg.state (cfg.tape.contents cfg.tape.head) := by
    simpa only [DLBA.BoundedTape.read] using henabled
  simp [henabled']

/-- The canonical landed configuration enters its fixed padding phase. -/
public theorem Machine.step_shortLayer_landed_pad
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (target : Λ)
    (tape : DLBA.BoundedTape Γ n) :
    Step M.shortLayers ⟨.landed target, tape⟩ ⟨.pad target, tape⟩ := by
  refine ⟨.pad target, tape.read, .stay, ?_, ?_⟩
  · simp [Machine.shortLayers]
  · exact congrArg
      (fun nextTape =>
        (⟨ShortLayerState.pad target, nextTape⟩ :
          DLBA.Cfg Γ (ShortLayerState Γ Λ) n))
      (write_read_stay tape).symm

/-- The second padding edge returns to the target core configuration. -/
public theorem Machine.step_shortLayer_pad_core
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (target : Λ)
    (tape : DLBA.BoundedTape Γ n) :
    Step M.shortLayers ⟨.pad target, tape⟩ ⟨.core target, tape⟩ := by
  refine ⟨.core target, tape.read, .stay, ?_, ?_⟩
  · simp [Machine.shortLayers]
  · exact congrArg
      (fun nextTape =>
        (⟨ShortLayerState.core target, nextTape⟩ :
          DLBA.Cfg Γ (ShortLayerState Γ Λ) n))
      (write_read_stay tape).symm

/-! ## Exact one-step inversion -/

/-- Exact successors of a core configuration. -/
public theorem Machine.step_shortLayers_core_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape Γ n)
    (target : DLBA.Cfg Γ (ShortLayerState Γ Λ) n) :
    Step M.shortLayers ⟨.core source, tape⟩ target ↔
      ∃ move ∈ M.transition source tape.read,
        target = ⟨.chosen source tape.read move, tape⟩ := by
  constructor
  · rintro ⟨next, written, direction, hmem, rfl⟩
    simp only [Machine.shortLayers] at hmem
    obtain ⟨move, henabled, htriple⟩ := hmem
    simp only [Prod.mk.injEq] at htriple
    rcases htriple with ⟨rfl, rfl, rfl⟩
    refine ⟨move, henabled, ?_⟩
    exact congrArg
      (fun nextTape =>
        (⟨ShortLayerState.chosen source tape.read move, nextTape⟩ :
          DLBA.Cfg Γ (ShortLayerState Γ Λ) n))
      (write_read_stay tape)
  · rintro ⟨move, henabled, rfl⟩
    exact M.step_shortLayer_core_chosen ⟨source, tape⟩ move henabled

/-- Exact successor of a chosen configuration, including the checks needed on malformed raw
states. -/
public theorem Machine.step_shortLayers_chosen_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (source : Λ) (expected : Γ)
    (move : LBA.Move Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (target : DLBA.Cfg Γ (ShortLayerState Γ Λ) n) :
    Step M.shortLayers ⟨.chosen source expected move, tape⟩ target ↔
      tape.read = expected ∧ move ∈ M.transition source expected ∧
        target = ⟨.landed move.1,
          (tape.write move.2.1).moveHead move.2.2⟩ := by
  constructor
  · rintro ⟨next, written, direction, hmem, rfl⟩
    simp only [Machine.shortLayers] at hmem
    by_cases henabled : tape.read = expected ∧
        move ∈ M.transition source expected
    · simp only [if_pos henabled, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      exact ⟨henabled.1, henabled.2, rfl⟩
    · simp at hmem
      exact (henabled ⟨by
        simpa only [DLBA.BoundedTape.read] using hmem.1.1,
        hmem.1.2⟩).elim
  · rintro ⟨hread, henabled, rfl⟩
    refine ⟨.landed move.1, move.2.1, move.2.2, ?_, rfl⟩
    simp only [Machine.shortLayers]
    have hread' : tape.contents tape.head = expected := by
      simpa only [DLBA.BoundedTape.read] using hread
    simp [hread', henabled]

/-- A landed configuration has exactly its canonical padding successor. -/
public theorem Machine.step_shortLayers_landed_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (state : Λ)
    (tape : DLBA.BoundedTape Γ n)
    (target : DLBA.Cfg Γ (ShortLayerState Γ Λ) n) :
    Step M.shortLayers ⟨.landed state, tape⟩ target ↔
      target = ⟨.pad state, tape⟩ := by
  constructor
  · rintro ⟨next, written, direction, hmem, rfl⟩
    simp only [Machine.shortLayers, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    exact congrArg
      (fun nextTape =>
        (⟨ShortLayerState.pad state, nextTape⟩ :
          DLBA.Cfg Γ (ShortLayerState Γ Λ) n))
      (write_read_stay tape)
  · rintro rfl
    exact M.step_shortLayer_landed_pad state tape

/-- A padding configuration has exactly its target core successor. -/
public theorem Machine.step_shortLayers_pad_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (state : Λ)
    (tape : DLBA.BoundedTape Γ n)
    (target : DLBA.Cfg Γ (ShortLayerState Γ Λ) n) :
    Step M.shortLayers ⟨.pad state, tape⟩ target ↔
      target = ⟨.core state, tape⟩ := by
  constructor
  · rintro ⟨next, written, direction, hmem, rfl⟩
    simp only [Machine.shortLayers, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    exact congrArg
      (fun nextTape =>
        (⟨ShortLayerState.core state, nextTape⟩ :
          DLBA.Cfg Γ (ShortLayerState Γ Λ) n))
      (write_read_stay tape)
  · rintro rfl
    exact M.step_shortLayer_pad_core state tape

/-- One genuine source step expands to exactly the four protocol phases. -/
public theorem Machine.reaches_shortLayerLift_of_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} {cfg cfg' : DLBA.Cfg Γ Λ n}
    (hstep : Step M cfg cfg') :
    Reaches M.shortLayers (shortLayerLiftCfg cfg) (shortLayerLiftCfg cfg') := by
  rcases hstep with ⟨target, written, direction, henabled, rfl⟩
  let move : LBA.Move Γ Λ := (target, written, direction)
  let landedTape := (cfg.tape.write written).moveHead direction
  exact .head
    (M.step_shortLayer_core_chosen cfg move henabled)
    (.head
      (M.step_shortLayer_chosen_landed cfg move henabled)
      (.head
        (M.step_shortLayer_landed_pad target landedTape)
        (.single (M.step_shortLayer_pad_core target landedTape))))

/-- Every source run lifts to a run between core configurations. -/
public theorem Machine.reaches_shortLayerLift_of_reaches
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} {cfg cfg' : DLBA.Cfg Γ Λ n}
    (hreach : Reaches M cfg cfg') :
    Reaches M.shortLayers (shortLayerLiftCfg cfg) (shortLayerLiftCfg cfg') := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.trans (M.reaches_shortLayerLift_of_step hstep)

/-- Projecting one raw protocol step either stutters or performs one genuine source step. -/
public theorem Machine.shortLayerProjectCfg_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ (ShortLayerState Γ Λ) n}
    (hstep : Step M.shortLayers cfg cfg') :
    shortLayerProjectCfg cfg = shortLayerProjectCfg cfg' ∨
      Step M (shortLayerProjectCfg cfg) (shortLayerProjectCfg cfg') := by
  rcases cfg with ⟨state, tape⟩
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  cases state with
  | core source =>
      simp only [Machine.shortLayers] at hmem
      obtain ⟨move, henabled, htriple⟩ := hmem
      simp only [Prod.mk.injEq] at htriple
      rcases htriple with ⟨rfl, rfl, rfl⟩
      left
      change
        (⟨source, tape⟩ : DLBA.Cfg Γ Λ n) =
          ⟨source, (tape.write tape.read).moveHead .stay⟩
      exact congrArg (fun nextTape => (⟨source, nextTape⟩ : DLBA.Cfg Γ Λ n))
        (write_read_stay tape).symm
  | chosen source expected move =>
      simp only [Machine.shortLayers] at hmem
      by_cases henabled : tape.read = expected ∧
          move ∈ M.transition source expected
      · simp only [if_pos henabled, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        right
        refine ⟨move.1, move.2.1, move.2.2, ?_, rfl⟩
        change move ∈ M.transition source tape.read
        rw [henabled.1]
        exact henabled.2
      · simp at hmem
        exact (henabled ⟨by
          simpa only [DLBA.BoundedTape.read] using hmem.1.1,
          hmem.1.2⟩).elim
  | landed target =>
      simp only [Machine.shortLayers, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      left
      exact congrArg (fun nextTape => (⟨target, nextTape⟩ : DLBA.Cfg Γ Λ n))
        (write_read_stay tape).symm
  | pad target =>
      simp only [Machine.shortLayers, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      left
      exact congrArg (fun nextTape => (⟨target, nextTape⟩ : DLBA.Cfg Γ Λ n))
        (write_read_stay tape).symm

/-- Projecting an arbitrary raw protocol run gives a source-machine run. -/
public theorem Machine.reaches_shortLayerProjectCfg
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ (ShortLayerState Γ Λ) n}
    (hreach : Reaches M.shortLayers cfg cfg') :
    Reaches M (shortLayerProjectCfg cfg) (shortLayerProjectCfg cfg') := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases M.shortLayerProjectCfg_step hstep with hsame | horiginal
      · simpa only [hsame] using ih
      · exact ih.tail horiginal

/-- Four-phase subdivision preserves acceptance from every embedded source configuration. -/
public theorem Machine.accepts_shortLayers_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Accepts M.shortLayers (shortLayerLiftCfg cfg) ↔ Accepts M cfg := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    have hprojected : Reaches M cfg (shortLayerProjectCfg target) := by
      simpa using M.reaches_shortLayerProjectCfg hreach
    cases hstate : target.state with
    | core state =>
        refine ⟨shortLayerProjectCfg target, hprojected, ?_⟩
        simpa [Machine.shortLayers, hstate, shortLayerProjectCfg] using haccept
    | chosen source expected move =>
        simp [Machine.shortLayers, hstate] at haccept
    | landed state =>
        simp [Machine.shortLayers, hstate] at haccept
    | pad state =>
        simp [Machine.shortLayers, hstate] at haccept
  · rintro ⟨target, hreach, haccept⟩
    refine ⟨shortLayerLiftCfg target,
      M.reaches_shortLayerLift_of_reaches hreach, ?_⟩
    simpa [Machine.shortLayers, shortLayerLiftCfg] using haccept

/-- The compiler preserves canonical endmarker languages without changing the tape alphabet or
width, including the genuine two-cell empty input. -/
public theorem Machine.languageEnd_shortLayers_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} [Fintype T] [DecidableEq T]
    (M : Machine (EndAlpha T Γ) Λ) :
    LanguageEnd M.shortLayers = LanguageEnd M := by
  funext word
  apply propext
  change
    Accepts M.shortLayers (shortLayerLiftCfg (initCfgEnd M word)) ↔
      Accepts M (initCfgEnd M word)
  exact M.accepts_shortLayers_iff _

/-- The concrete bounded-degree/four-phase pipeline preserves the source endmarker language. -/
public theorem Machine.languageEnd_boundedDegree_shortLayers_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} [Fintype T] [DecidableEq T]
    (M : Machine (EndAlpha T Γ) Λ) :
    LanguageEnd M.boundedDegree.shortLayers = LanguageEnd M :=
  M.boundedDegree.languageEnd_shortLayers_eq.trans
    M.languageEnd_boundedDegree_eq

end LBA

end
