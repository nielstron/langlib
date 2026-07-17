module

public import Langlib.Automata.LinearBounded.MachineShortLayers.Construction
public import Langlib.Automata.LinearBounded.TwoLayerReachability

@[expose]
public section

/-!
# Two short biunique layers for the four-phase compiler

Assume the source configuration relation is exactly partitioned into two biunique layers and
that configuration edges have unique operational labels.  A source edge of color `c` is expanded
with the color word

`c, opposite(c), 0, 1`.

The first two colors retain the source layer information; the final `0,1` delimiter permits all
incoming labels to merge into one canonical landed configuration without creating a
monochromatic path of three edges.
-/

namespace LBA.MachineShortLayers

open Classical Relation

variable {Γ Λ : Type*}

/-- The other one of two colors. -/
@[expose]
public def opposite (color : Fin 2) : Fin 2 :=
  ⟨1 - color.val, by omega⟩

@[simp]
public theorem opposite_opposite (color : Fin 2) :
    opposite (opposite color) = color := by
  apply Fin.ext
  simp only [opposite]
  omega

public theorem opposite_injective : Function.Injective opposite := by
  intro left right h
  have := congrArg opposite h
  simpa only [opposite_opposite] using this

public theorem opposite_ne (color : Fin 2) : opposite color ≠ color := by
  intro h
  have hval := congrArg Fin.val h
  simp only [opposite] at hval
  omega

/-- Apply a local transition triple to a source configuration, without requiring a membership
proof. -/
@[expose]
public def moveTarget {n : ℕ} (source : DLBA.Cfg Γ Λ n)
    (move : LBA.Move Γ Λ) : DLBA.Cfg Γ Λ n :=
  ⟨move.1, (source.tape.write move.2.1).moveHead move.2.2⟩

/-- Phase-dependent color condition.  Genuine target-machine steps are added separately by
`StepLayer`; keeping this predicate separate makes subrelation proofs immediate. -/
@[expose]
public def PhaseColor [Fintype Γ] [Fintype Λ]
    {n : ℕ} (oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)
    (color : Fin 2)
    (old new : DLBA.Cfg Γ (ShortLayerState Γ Λ) n) : Prop :=
  match old.state, new.state with
  | .core source, .chosen _ _ move =>
      oldLayer color ⟨source, old.tape⟩ (moveTarget ⟨source, old.tape⟩ move)
  | .chosen source _ _, .landed target =>
      oldLayer (opposite color) ⟨source, old.tape⟩ ⟨target, new.tape⟩
  | .landed _, .pad _ => color = 0
  | .pad _, .core _ => color = 1
  | _, _ => False

/-- One of the two layers of the compiled step relation. -/
public def StepLayer
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)
    (color : Fin 2) :
    DLBA.Cfg Γ (ShortLayerState Γ Λ) n →
      DLBA.Cfg Γ (ShortLayerState Γ Λ) n → Prop :=
  fun old new => Step M.shortLayers old new ∧ PhaseColor oldLayer color old new

/-- Every colored compiled edge is a genuine compiled-machine step. -/
public theorem stepLayer_sub_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)
    {color : Fin 2} {old new : DLBA.Cfg Γ (ShortLayerState Γ Λ) n}
    (h : StepLayer M oldLayer color old new) :
    Step M.shortLayers old new := h.1

/-- The four-phase coloring covers every compiled edge exactly once. -/
public theorem step_iff_existsUnique_stepLayer
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition (Step M) oldLayer)
    (old new : DLBA.Cfg Γ (ShortLayerState Γ Λ) n) :
    Step M.shortLayers old new ↔
      ∃! color, StepLayer M oldLayer color old new := by
  constructor
  · intro hstep
    rcases old with ⟨state, tape⟩
    cases state with
    | core source =>
        obtain ⟨move, henabled, rfl⟩ :=
          (M.step_shortLayers_core_iff source tape new).mp hstep
        let sourceCfg : DLBA.Cfg Γ Λ n := ⟨source, tape⟩
        let targetCfg : DLBA.Cfg Γ Λ n := moveTarget sourceCfg move
        have holdStep : Step M sourceCfg targetCfg :=
          ⟨move.1, move.2.1, move.2.2, henabled, rfl⟩
        obtain ⟨color, hcolor, hunique⟩ :=
          (partition.edge_iff_existsUnique_layer sourceCfg targetCfg).mp holdStep
        refine ⟨color, ⟨hstep, ?_⟩, ?_⟩
        · simpa only [PhaseColor, sourceCfg, targetCfg]
        · intro other hother
          apply hunique other
          simpa only [StepLayer, PhaseColor, sourceCfg, targetCfg] using hother.2
    | chosen source expected move =>
        obtain ⟨hread, henabled, rfl⟩ :=
          (M.step_shortLayers_chosen_iff source expected move tape new).mp hstep
        let sourceCfg : DLBA.Cfg Γ Λ n := ⟨source, tape⟩
        let targetCfg : DLBA.Cfg Γ Λ n := moveTarget sourceCfg move
        have holdStep : Step M sourceCfg targetCfg := by
          refine ⟨move.1, move.2.1, move.2.2, ?_, rfl⟩
          rw [hread]
          exact henabled
        obtain ⟨oldColor, hcolor, hunique⟩ :=
          (partition.edge_iff_existsUnique_layer sourceCfg targetCfg).mp holdStep
        refine ⟨opposite oldColor, ⟨hstep, ?_⟩, ?_⟩
        · simpa only [PhaseColor, opposite_opposite, sourceCfg, targetCfg]
        · intro other hother
          have hopposite : opposite other = oldColor := by
            apply hunique (opposite other)
            simpa only [StepLayer, PhaseColor, sourceCfg, targetCfg] using hother.2
          have := congrArg opposite hopposite
          simpa only [opposite_opposite] using this
    | landed target =>
        have hnew := (M.step_shortLayers_landed_iff target tape new).mp hstep
        subst new
        refine ⟨0, ⟨hstep, rfl⟩, ?_⟩
        intro other hother
        simpa only [StepLayer, PhaseColor] using hother.2
    | pad target =>
        have hnew := (M.step_shortLayers_pad_iff target tape new).mp hstep
        subst new
        refine ⟨1, ⟨hstep, rfl⟩, ?_⟩
        intro other hother
        simpa only [StepLayer, PhaseColor] using hother.2
  · rintro ⟨color, hcolor, _⟩
    exact hcolor.1

/-! ## Biuniqueness -/

/-- Each compiled color is functional.  The only nondeterministic phase is `core`; old-layer
functionality identifies its represented target, and label injectivity then identifies the saved
transition triple itself. -/
public theorem stepLayer_rightUnique
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hlabel : M.StepLabelInjective) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 2) : Relator.RightUnique (StepLayer M oldLayer color) := by
  intro old left right hleft hright
  rcases old with ⟨state, tape⟩
  cases state with
  | core source =>
      obtain ⟨leftMove, hleftEnabled, hleftTarget⟩ :=
        (M.step_shortLayers_core_iff source tape left).mp hleft.1
      obtain ⟨rightMove, hrightEnabled, hrightTarget⟩ :=
        (M.step_shortLayers_core_iff source tape right).mp hright.1
      subst left
      subst right
      have hleftLayer : oldLayer color
          (⟨source, tape⟩ : DLBA.Cfg Γ Λ n)
          (moveTarget ⟨source, tape⟩ leftMove) := by
        simpa only [PhaseColor] using hleft.2
      have hrightLayer : oldLayer color
          (⟨source, tape⟩ : DLBA.Cfg Γ Λ n)
          (moveTarget ⟨source, tape⟩ rightMove) := by
        simpa only [PhaseColor] using hright.2
      have htargets :
          moveTarget (⟨source, tape⟩ : DLBA.Cfg Γ Λ n) leftMove =
            moveTarget ⟨source, tape⟩ rightMove :=
        (hbiUnique color).2 hleftLayer hrightLayer
      have hmoves : leftMove = rightMove :=
        M.transitionLabel_eq_of_stepLabelInjective hlabel
          hleftEnabled hrightEnabled htargets
      subst rightMove
      rfl
  | chosen source expected move =>
      obtain ⟨_, _, hleftTarget⟩ :=
        (M.step_shortLayers_chosen_iff source expected move tape left).mp hleft.1
      obtain ⟨_, _, hrightTarget⟩ :=
        (M.step_shortLayers_chosen_iff source expected move tape right).mp hright.1
      exact hleftTarget.trans hrightTarget.symm
  | landed target =>
      have hleftTarget := (M.step_shortLayers_landed_iff target tape left).mp hleft.1
      have hrightTarget := (M.step_shortLayers_landed_iff target tape right).mp hright.1
      exact hleftTarget.trans hrightTarget.symm
  | pad target =>
      have hleftTarget := (M.step_shortLayers_pad_iff target tape left).mp hleft.1
      have hrightTarget := (M.step_shortLayers_pad_iff target tape right).mp hright.1
      exact hleftTarget.trans hrightTarget.symm

/-- Each compiled color is cofunctional.  Chosen targets retain their complete source label;
landed targets use old-layer cofunctionality and label injectivity; the two padding maps are
literal injections. -/
public theorem stepLayer_leftUnique
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hlabel : M.StepLabelInjective) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 2) : Relator.LeftUnique (StepLayer M oldLayer color) := by
  intro left right target hleft hright
  rcases left with ⟨leftState, leftTape⟩
  cases leftState with
  | core leftSource =>
      obtain ⟨leftMove, leftEnabled, htarget⟩ :=
        (M.step_shortLayers_core_iff leftSource leftTape target).mp hleft.1
      subst target
      rcases right with ⟨rightState, rightTape⟩
      have hrightPhase := hright.2
      cases rightState with
      | core rightSource =>
          obtain ⟨rightMove, rightEnabled, hrightTarget⟩ :=
            (M.step_shortLayers_core_iff rightSource rightTape
              ⟨.chosen leftSource leftTape.read leftMove, leftTape⟩).mp hright.1
          have hcanonical :
              (⟨ShortLayerState.chosen leftSource leftTape.read leftMove, leftTape⟩ :
                DLBA.Cfg Γ (ShortLayerState Γ Λ) n) =
              ⟨ShortLayerState.chosen rightSource rightTape.read rightMove,
                rightTape⟩ := hrightTarget
          have hsources := congrArg shortLayerProjectCfg hcanonical
          exact congrArg shortLayerLiftCfg hsources
      | chosen rightSource rightExpected rightMove =>
          simp only [PhaseColor] at hrightPhase
      | landed rightTarget =>
          simp only [PhaseColor] at hrightPhase
      | pad rightTarget =>
          simp only [PhaseColor] at hrightPhase
  | chosen leftSource leftExpected leftMove =>
      obtain ⟨leftRead, leftEnabled, htarget⟩ :=
        (M.step_shortLayers_chosen_iff leftSource leftExpected leftMove
          leftTape target).mp hleft.1
      subst target
      rcases right with ⟨rightState, rightTape⟩
      have hrightPhase := hright.2
      cases rightState with
      | core rightSource =>
          simp only [PhaseColor] at hrightPhase
      | chosen rightSource rightExpected rightMove =>
          obtain ⟨rightRead, rightEnabled, hrightTarget⟩ :=
            (M.step_shortLayers_chosen_iff rightSource rightExpected rightMove
              rightTape
              ⟨.landed leftMove.1,
                (leftTape.write leftMove.2.1).moveHead leftMove.2.2⟩).mp hright.1
          have hleftLayer : oldLayer (opposite color)
              (⟨leftSource, leftTape⟩ : DLBA.Cfg Γ Λ n)
              (moveTarget ⟨leftSource, leftTape⟩ leftMove) := by
            simpa only [PhaseColor, moveTarget] using hleft.2
          have hrightLayer : oldLayer (opposite color)
              (⟨rightSource, rightTape⟩ : DLBA.Cfg Γ Λ n)
              (moveTarget ⟨leftSource, leftTape⟩ leftMove) := by
            simpa only [PhaseColor, moveTarget] using hright.2
          have hsources :
              (⟨leftSource, leftTape⟩ : DLBA.Cfg Γ Λ n) =
                ⟨rightSource, rightTape⟩ :=
            (hbiUnique (opposite color)).1 hleftLayer hrightLayer
          cases hsources
          subst leftExpected
          subst rightExpected
          have hleftEnabled' : leftMove ∈
              M.transition leftSource leftTape.read := by
            exact leftEnabled
          have hrightEnabled' : rightMove ∈
              M.transition leftSource leftTape.read := by
            exact rightEnabled
          have htargets :
              moveTarget (⟨leftSource, leftTape⟩ : DLBA.Cfg Γ Λ n) leftMove =
                moveTarget ⟨leftSource, leftTape⟩ rightMove := by
            have hcompiled := congrArg shortLayerProjectCfg hrightTarget
            simpa only [shortLayerProjectCfg, moveTarget] using hcompiled
          have hmoves : leftMove = rightMove :=
            M.transitionLabel_eq_of_stepLabelInjective hlabel
              hleftEnabled' hrightEnabled' htargets
          subst rightMove
          rfl
      | landed rightTarget =>
          simp only [PhaseColor] at hrightPhase
      | pad rightTarget =>
          simp only [PhaseColor] at hrightPhase
  | landed leftTarget =>
      have htarget :=
        (M.step_shortLayers_landed_iff leftTarget leftTape target).mp hleft.1
      subst target
      rcases right with ⟨rightState, rightTape⟩
      have hrightPhase := hright.2
      cases rightState with
      | core rightSource =>
          simp only [PhaseColor] at hrightPhase
      | chosen rightSource rightExpected rightMove =>
          simp only [PhaseColor] at hrightPhase
      | landed rightTarget =>
          have hrightTarget :=
            (M.step_shortLayers_landed_iff rightTarget rightTape
              ⟨.pad leftTarget, leftTape⟩).mp hright.1
          have hbase := congrArg shortLayerProjectCfg hrightTarget
          cases hbase
          rfl
      | pad rightTarget =>
          simp only [PhaseColor] at hrightPhase
  | pad leftTarget =>
      have htarget :=
        (M.step_shortLayers_pad_iff leftTarget leftTape target).mp hleft.1
      subst target
      rcases right with ⟨rightState, rightTape⟩
      have hrightPhase := hright.2
      cases rightState with
      | core rightSource =>
          simp only [PhaseColor] at hrightPhase
      | chosen rightSource rightExpected rightMove =>
          simp only [PhaseColor] at hrightPhase
      | landed rightTarget =>
          simp only [PhaseColor] at hrightPhase
      | pad rightTarget =>
          have hrightTarget :=
            (M.step_shortLayers_pad_iff rightTarget rightTape
              ⟨.core leftTarget, leftTape⟩).mp hright.1
          have hbase := congrArg shortLayerProjectCfg hrightTarget
          cases hbase
          rfl

/-- Each compiled layer is both functional and cofunctional. -/
public theorem stepLayer_biUnique
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hlabel : M.StepLabelInjective) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 2) : Relator.BiUnique (StepLayer M oldLayer color) :=
  ⟨stepLayer_leftUnique M hlabel hbiUnique color,
    stepLayer_rightUnique M hlabel hbiUnique color⟩

/-! ## Short monochromatic paths -/

/-- A relation has no directed path consisting of three composable edges. -/
public def PathLengthAtMostTwo {V : Type*} (relation : V → V → Prop) : Prop :=
  ∀ ⦃a b c d⦄, relation a b → relation b c → relation c d → False

/-- No compiled layer contains three composable edges. -/
public theorem stepLayer_pathLengthAtMostTwo
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition (Step M) oldLayer)
    (color : Fin 2) : PathLengthAtMostTwo (StepLayer M oldLayer color) := by
  intro a b c d hab hbc hcd
  rcases a with ⟨state, tape⟩
  cases state with
  | core source =>
      obtain ⟨move, henabled, hb⟩ :=
        (M.step_shortLayers_core_iff source tape b).mp hab.1
      subst b
      obtain ⟨hread, hmoveEnabled, hc⟩ :=
        (M.step_shortLayers_chosen_iff source tape.read move tape c).mp hbc.1
      subst c
      have hfirst : oldLayer color
          (⟨source, tape⟩ : DLBA.Cfg Γ Λ n)
          (moveTarget ⟨source, tape⟩ move) := by
        simpa only [PhaseColor] using hab.2
      have hmiddle : oldLayer (opposite color)
          (⟨source, tape⟩ : DLBA.Cfg Γ Λ n)
          (moveTarget ⟨source, tape⟩ move) := by
        simpa only [PhaseColor, moveTarget] using hbc.2
      have heq : color = opposite color :=
        partition.layer_disjoint hfirst hmiddle
      exact opposite_ne color heq.symm

  | chosen source expected move =>
      obtain ⟨hread, henabled, hb⟩ :=
        (M.step_shortLayers_chosen_iff source expected move tape b).mp hab.1
      subst b
      have hc :=
        (M.step_shortLayers_landed_iff move.1
          ((tape.write move.2.1).moveHead move.2.2) c).mp hbc.1
      subst c
      have hd :=
        (M.step_shortLayers_pad_iff move.1
          ((tape.write move.2.1).moveHead move.2.2) d).mp hcd.1
      subst d
      have hzero : color = 0 := by
        simpa only [PhaseColor] using hbc.2
      have hone : color = 1 := by
        simpa only [PhaseColor] using hcd.2
      have : (0 : Fin 2) = 1 := hzero.symm.trans hone
      omega
  | landed target =>
      have hb := (M.step_shortLayers_landed_iff target tape b).mp hab.1
      subst b
      have hc := (M.step_shortLayers_pad_iff target tape c).mp hbc.1
      subst c
      have hzero : color = 0 := by
        simpa only [PhaseColor] using hab.2
      have hone : color = 1 := by
        simpa only [PhaseColor] using hbc.2
      have : (0 : Fin 2) = 1 := hzero.symm.trans hone
      omega
  | pad target =>
      have hb := (M.step_shortLayers_pad_iff target tape b).mp hab.1
      subst b
      obtain ⟨move, henabled, hc⟩ :=
        (M.step_shortLayers_core_iff target tape c).mp hbc.1
      subst c
      obtain ⟨hread, hmoveEnabled, hd⟩ :=
        (M.step_shortLayers_chosen_iff target tape.read move tape d).mp hcd.1
      subst d
      have hfirst : oldLayer color
          (⟨target, tape⟩ : DLBA.Cfg Γ Λ n)
          (moveTarget ⟨target, tape⟩ move) := by
        simpa only [PhaseColor] using hbc.2
      have hmiddle : oldLayer (opposite color)
          (⟨target, tape⟩ : DLBA.Cfg Γ Λ n)
          (moveTarget ⟨target, tape⟩ move) := by
        simpa only [PhaseColor, moveTarget] using hcd.2
      have heq : color = opposite color :=
        partition.layer_disjoint hfirst hmiddle
      exact opposite_ne color heq.symm

/-! ## Width-uniform machine property -/

/-- A single family of two exact biunique layers covers every fixed-width configuration relation,
and neither layer contains a path of three edges. -/
public def _root_.LBA.Machine.HasTwoShortBiUniqueStepPartition
    (M : Machine Γ Λ) : Prop :=
  ∃ layer : (n : ℕ) → Fin 2 →
      DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop,
    (∀ n source target,
      Step M source target ↔ ∃! color, layer n color source target) ∧
    (∀ n color source target,
      layer n color source target → Step M source target) ∧
    (∀ n color, Relator.BiUnique (layer n color)) ∧
    ∀ n color, PathLengthAtMostTwo (layer n color)

/-- The four-phase compiler turns a width-uniform two-biunique partition into a width-uniform
short two-biunique partition. -/
public theorem _root_.LBA.Machine.shortLayers_hasTwoShortBiUniqueStepPartition
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hlabel : M.StepLabelInjective)
    (hold : M.HasTwoBiUniqueStepPartition) :
    M.shortLayers.HasTwoShortBiUniqueStepPartition := by
  rcases hold with ⟨oldLayer, hcover, hsub, hbiUnique⟩
  let newLayer : (n : ℕ) → Fin 2 →
      DLBA.Cfg Γ (ShortLayerState Γ Λ) n →
        DLBA.Cfg Γ (ShortLayerState Γ Λ) n → Prop :=
    fun n => StepLayer M (oldLayer n)
  refine ⟨newLayer, ?_, ?_, ?_, ?_⟩
  · intro n source target
    let partition : TwoLayerReachability.TwoPartialFunctionPartition
        (Step M) (oldLayer n) :=
      TwoLayerReachability.TwoPartialFunctionPartition.of_existsUnique_biUnique
        (hcover n) (hsub n) (hbiUnique n)
    exact step_iff_existsUnique_stepLayer M partition source target
  · intro n color source target hlayer
    exact hlayer.1
  · intro n color
    exact stepLayer_biUnique M hlabel (hbiUnique n) color
  · intro n color
    let partition : TwoLayerReachability.TwoPartialFunctionPartition
        (Step M) (oldLayer n) :=
      TwoLayerReachability.TwoPartialFunctionPartition.of_existsUnique_biUnique
        (hcover n) (hsub n) (hbiUnique n)
    exact stepLayer_pathLengthAtMostTwo M partition color

/-- Two exact biunique layers entail both configuration degree bounds, independently of the
additional short-path property. -/
public theorem _root_.LBA.Machine.configurationDegreeAtMostTwo_of_hasTwoShortBiUniqueStepPartition
    (M : Machine Γ Λ) (hshort : M.HasTwoShortBiUniqueStepPartition) :
    M.ConfigurationDegreeAtMostTwo := by
  rcases hshort with ⟨layer, hcover, hsub, hbiUnique, hpath⟩
  constructor
  · intro n source
    let partition : TwoLayerReachability.TwoPartialFunctionPartition
        (Step M) (layer n) :=
      TwoLayerReachability.TwoPartialFunctionPartition.of_existsUnique_biUnique
        (hcover n) (hsub n) (hbiUnique n)
    exact (partition.directedDegreeAtMostTwo_of_biUnique (hbiUnique n)).1 source
  · intro n target
    let partition : TwoLayerReachability.TwoPartialFunctionPartition
        (Step M) (layer n) :=
      TwoLayerReachability.TwoPartialFunctionPartition.of_existsUnique_biUnique
        (hcover n) (hsub n) (hbiUnique n)
    exact (partition.directedDegreeAtMostTwo_of_biUnique (hbiUnique n)).2 target

/-- Applying the four-phase compiler after the existing simultaneous degree serializer supplies
the complete short two-layer witness for every source machine. -/
public theorem _root_.LBA.Machine.boundedDegree_shortLayers_hasTwoShortBiUniqueStepPartition
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.boundedDegree.shortLayers.HasTwoShortBiUniqueStepPartition :=
  M.boundedDegree.shortLayers_hasTwoShortBiUniqueStepPartition
    M.boundedDegree_stepLabelInjective
    M.boundedDegree_hasTwoBiUniqueStepPartition

/-- The concrete bounded-degree/four-phase pipeline has both directed configuration degrees at
most two at every width. -/
public theorem _root_.LBA.Machine.boundedDegree_shortLayers_configurationDegreeAtMostTwo
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.boundedDegree.shortLayers.ConfigurationDegreeAtMostTwo :=
  M.boundedDegree.shortLayers
    |>.configurationDegreeAtMostTwo_of_hasTwoShortBiUniqueStepPartition
      M.boundedDegree_shortLayers_hasTwoShortBiUniqueStepPartition

/-- Packaged exact two-partial-function partition of the compiled relation. -/
public theorem twoPartialFunctionPartition
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition (Step M) oldLayer)
    (rightUnique : ∀ color, Relator.RightUnique (StepLayer M oldLayer color)) :
    TwoLayerReachability.TwoPartialFunctionPartition
      (Step M.shortLayers) (StepLayer M oldLayer) :=
  TwoLayerReachability.TwoPartialFunctionPartition.of_existsUnique
    (step_iff_existsUnique_stepLayer M partition)
    (fun _ _ _ h => h.1)
    rightUnique

end LBA.MachineShortLayers

end
