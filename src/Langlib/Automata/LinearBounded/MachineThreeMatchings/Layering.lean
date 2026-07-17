module

public import Langlib.Automata.LinearBounded.MachineThreeMatchings.Construction
public import Langlib.Automata.LinearBounded.BoundedDegree
public import Langlib.Automata.LinearBounded.LinearTwoDiforestReachability

@[expose]
public section

/-!
# Three directed-matching layers on split LBA configurations

This file lifts a width-uniform exact two-biunique-layer partition of a machine step relation
through `Machine.threeMatchings`.  The first two colors label genuine source-machine steps; the
fresh color `2` labels input-to-output edges.  Besides exact cover and absence of spurious layer
edges, every color is both bi-unique and has no composable pair of edges.
-/

namespace LBA

open Relation Set

variable {Γ Λ : Type*}

/-- Embed either old color into the first two of the three new colors. -/
@[expose]
public def threeMatchingOldColor (color : Fin 2) : Fin 3 :=
  ⟨color.val, by omega⟩

public theorem threeMatchingOldColor_injective :
    Function.Injective threeMatchingOldColor := by
  intro left right heq
  apply Fin.ext
  exact Fin.mk.inj heq

/-- An embedded old color is never the fresh internal-edge color. -/
public theorem threeMatchingOldColor_ne_two (color : Fin 2) :
    threeMatchingOldColor color ≠ (2 : Fin 3) := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [threeMatchingOldColor] at hval
  omega

/-- Lift two old configuration layers to the three layers of the split machine. -/
@[expose]
public def Machine.threeMatchingStepLayer
    (_M : Machine Γ Λ) {n : ℕ}
    (oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)
    (color : Fin 3) :
    DLBA.Cfg Γ (ThreeMatchingState Λ) n →
      DLBA.Cfg Γ (ThreeMatchingState Λ) n → Prop :=
  fun source target =>
    match source.state, target.state with
    | .input _, .output _ =>
        threeMatchingProjectCfg source = threeMatchingProjectCfg target ∧ color = 2
    | .output _, .input _ =>
        ∃ oldColor,
          oldLayer oldColor (threeMatchingProjectCfg source)
              (threeMatchingProjectCfg target) ∧
            threeMatchingOldColor oldColor = color
    | _, _ => False

/-- Every internal edge belongs to the fresh third layer. -/
public theorem Machine.threeMatchingStepLayer_internal
    (M : Machine Γ Λ) {n : ℕ} (oldLayer : Fin 2 →
      DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)
    (cfg : DLBA.Cfg Γ Λ n) :
    M.threeMatchingStepLayer oldLayer 2
      (threeMatchingInputCfg cfg) (threeMatchingOutputCfg cfg) := by
  rcases cfg with ⟨state, tape⟩
  simp [Machine.threeMatchingStepLayer, threeMatchingInputCfg,
    threeMatchingOutputCfg, threeMatchingProjectCfg]

/-- An old colored edge gives the corresponding external split edge. -/
public theorem Machine.threeMatchingStepLayer_external
    (M : Machine Γ Λ) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    {color : Fin 2} {source target : DLBA.Cfg Γ Λ n}
    (h : oldLayer color source target) :
    M.threeMatchingStepLayer oldLayer (threeMatchingOldColor color)
      (threeMatchingOutputCfg source) (threeMatchingInputCfg target) := by
  exact ⟨color, h, rfl⟩

/-- Every compiled step has exactly one new color, assuming exact old cover and no spurious old
layer edges. -/
public theorem Machine.threeMatchingStepLayer_partition
    (M : Machine Γ Λ) {n : ℕ}
    (oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)
    (oldCover : ∀ source target, Step M source target ↔
      ∃! color, oldLayer color source target)
    (oldLayerSubStep : ∀ color source target,
      oldLayer color source target → Step M source target) :
    (∀ source target, Step M.threeMatchings source target ↔
      ∃! color, M.threeMatchingStepLayer oldLayer color source target) ∧
      ∀ color source target,
        M.threeMatchingStepLayer oldLayer color source target →
          Step M.threeMatchings source target := by
  constructor
  · intro source target
    constructor
    · intro hstep
      rw [M.step_threeMatchings_iff] at hstep
      rcases hstep with ⟨cfg, rfl, rfl⟩ | ⟨old, new, hedge, rfl, rfl⟩
      · refine ⟨2, ⟨rfl, rfl⟩, ?_⟩
        intro color hcolor
        exact hcolor.2
      · obtain ⟨oldColor, hold, hunique⟩ := (oldCover old new).mp hedge
        refine ⟨threeMatchingOldColor oldColor, ⟨oldColor, hold, rfl⟩, ?_⟩
        intro color hcolor
        obtain ⟨other, hother, hotherColor⟩ := hcolor
        have hcolors : other = oldColor := hunique other hother
        subst other
        exact hotherColor.symm
    · rintro ⟨color, hcolor, _⟩
      rcases source with ⟨sourceState, sourceTape⟩
      rcases target with ⟨targetState, targetTape⟩
      cases sourceState <;> cases targetState <;>
        simp only [Machine.threeMatchingStepLayer,
          threeMatchingProjectCfg] at hcolor
      · exact (M.step_threeMatchings_input_iff _ _ _).2
          (congrArg threeMatchingOutputCfg hcolor.1).symm
      · obtain ⟨oldColor, hold, _⟩ := hcolor
        rw [M.step_threeMatchings_iff]
        exact Or.inr ⟨_, _, oldLayerSubStep oldColor _ _ hold, rfl, rfl⟩
  · intro color source target hlayer
    rcases source with ⟨sourceState, sourceTape⟩
    rcases target with ⟨targetState, targetTape⟩
    cases sourceState <;> cases targetState <;>
      simp only [Machine.threeMatchingStepLayer,
        threeMatchingProjectCfg] at hlayer
    · exact (M.step_threeMatchings_input_iff _ _ _).2
        (congrArg threeMatchingOutputCfg hlayer.1).symm
    · obtain ⟨oldColor, hold, _⟩ := hlayer
      rw [M.step_threeMatchings_iff]
      exact Or.inr ⟨_, _, oldLayerSubStep oldColor _ _ hold, rfl, rfl⟩

/-! ## Each layer is a directed matching -/

private theorem Machine.threeMatchingStepLayer_rightUnique
    (M : Machine Γ Λ) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (oldBiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 3) :
    Relator.RightUnique (M.threeMatchingStepLayer oldLayer color) := by
  intro source left right hleft hright
  rcases source with ⟨sourceState, sourceTape⟩
  rcases left with ⟨leftState, leftTape⟩
  rcases right with ⟨rightState, rightTape⟩
  cases sourceState <;> cases leftState <;> cases rightState <;>
    simp only [Machine.threeMatchingStepLayer,
      threeMatchingProjectCfg] at hleft hright
  · exact congrArg threeMatchingOutputCfg (hleft.1.symm.trans hright.1)
  · obtain ⟨leftColor, hleftLayer, hleftColor⟩ := hleft
    obtain ⟨rightColor, hrightLayer, hrightColor⟩ := hright
    have hcolors : leftColor = rightColor :=
      threeMatchingOldColor_injective (hleftColor.trans hrightColor.symm)
    subst rightColor
    exact congrArg threeMatchingInputCfg
      ((oldBiUnique leftColor).2 hleftLayer hrightLayer)

private theorem Machine.threeMatchingStepLayer_leftUnique
    (M : Machine Γ Λ) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (oldBiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 3) :
    Relator.LeftUnique (M.threeMatchingStepLayer oldLayer color) := by
  intro left right target hleft hright
  rcases left with ⟨leftState, leftTape⟩
  rcases right with ⟨rightState, rightTape⟩
  rcases target with ⟨targetState, targetTape⟩
  cases targetState <;> cases leftState <;> cases rightState <;>
    simp only [Machine.threeMatchingStepLayer,
      threeMatchingProjectCfg] at hleft hright
  · obtain ⟨leftColor, hleftLayer, hleftColor⟩ := hleft
    obtain ⟨rightColor, hrightLayer, hrightColor⟩ := hright
    have hcolors : leftColor = rightColor :=
      threeMatchingOldColor_injective (hleftColor.trans hrightColor.symm)
    subst rightColor
    exact congrArg threeMatchingOutputCfg
      ((oldBiUnique leftColor).1 hleftLayer hrightLayer)
  · exact congrArg threeMatchingInputCfg (hleft.1.trans hright.1.symm)

/-- Each of the three supplied configuration layers is both functional and cofunctional. -/
public theorem Machine.threeMatchingStepLayer_biUnique
    (M : Machine Γ Λ) {n : ℕ}
    {oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (oldBiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 3) :
    Relator.BiUnique (M.threeMatchingStepLayer oldLayer color) :=
  ⟨M.threeMatchingStepLayer_leftUnique oldBiUnique color,
    M.threeMatchingStepLayer_rightUnique oldBiUnique color⟩

/-- No two edges of one new layer are composable. -/
public theorem Machine.threeMatchingStepLayer_pathLengthAtMostOne
    (M : Machine Γ Λ) {n : ℕ}
    (oldLayer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)
    (color : Fin 3) :
    LinearTwoDiforestReachability.PathLengthAtMostOne
      (M.threeMatchingStepLayer oldLayer color) := by
  intro first middle last hfirst hlast
  rcases first with ⟨firstState, firstTape⟩
  rcases middle with ⟨middleState, middleTape⟩
  rcases last with ⟨lastState, lastTape⟩
  cases firstState <;> cases middleState <;> cases lastState <;>
    simp only [Machine.threeMatchingStepLayer,
      threeMatchingProjectCfg] at hfirst hlast
  · obtain ⟨oldColor, _, holdColor⟩ := hlast
    exact threeMatchingOldColor_ne_two oldColor
      (holdColor.trans hfirst.2)
  · obtain ⟨oldColor, _, holdColor⟩ := hfirst
    exact threeMatchingOldColor_ne_two oldColor
      (holdColor.trans hlast.2)

/-- A width-uniform family of exact three-color configuration partitions whose colors are
directed matchings. -/
public def Machine.HasThreeMatchingStepPartition (M : Machine Γ Λ) : Prop :=
  ∃ layer : (n : ℕ) → Fin 3 →
      DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop,
    (∀ n source target,
      Step M source target ↔ ∃! color, layer n color source target) ∧
      (∀ n color source target,
        layer n color source target → Step M source target) ∧
      (∀ n color, Relator.BiUnique (layer n color)) ∧
      ∀ n color,
        LinearTwoDiforestReachability.PathLengthAtMostOne (layer n color)

/-- Splitting a machine equipped with two uniform bi-unique layers gives three uniform directed
matching layers. -/
public theorem Machine.threeMatchings_hasThreeMatchingStepPartition
    (M : Machine Γ Λ) (hold : M.HasTwoBiUniqueStepPartition) :
    M.threeMatchings.HasThreeMatchingStepPartition := by
  rcases hold with ⟨oldLayer, oldCover, oldSub, oldBiUnique⟩
  refine ⟨fun n => M.threeMatchingStepLayer (oldLayer n), ?_, ?_, ?_, ?_⟩
  · intro n
    exact (M.threeMatchingStepLayer_partition (oldLayer n)
      (oldCover n) (oldSub n)).1
  · intro n
    exact (M.threeMatchingStepLayer_partition (oldLayer n)
      (oldCover n) (oldSub n)).2
  · intro n
    exact M.threeMatchingStepLayer_biUnique (oldBiUnique n)
  · intro n
    exact M.threeMatchingStepLayer_pathLengthAtMostOne (oldLayer n)

end LBA

end
