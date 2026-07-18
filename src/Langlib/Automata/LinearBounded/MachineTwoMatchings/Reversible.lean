module

public import Langlib.Automata.LinearBounded.Cofunctional
public import Langlib.Automata.LinearBounded.MachineThreeMatchings.Construction
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.Definition

@[expose]
public section

/-!
# Reversible LBA presentations give two matching layers

A machine is configuration-reversible when its complete fixed-width step relation is both
functional and cofunctional at every tape width.  The existing `Machine.threeMatchings` compiler
splits every source step into two phases:

* an input copy takes a symbol-preserving stay step to its output copy;
* an output copy performs the source step and returns to an input copy.

For a configuration-reversible source these two kinds of edges are themselves directed
matchings.  Coloring the internal edges zero and the source edges one therefore gives an exact
two-matching presentation, at the same tape width and over the same tape alphabet.

This module proves only that structural bridge.  Under the repository's clamped movement and
all-raw-configuration quantification, however, this source promise is much stronger than the
standard marked-tape notion of a reversible Turing machine: any enabled directional move creates
a raw boundary collision.  `MachineTwoMatchings/ReversibleTriviality.lean` proves that the
language class defined below consequently contains only the empty and universal languages.  A
standard reversible-space simulation must therefore be adapted directly to the weaker exact-two-
matching target rather than presented as a compiler into `ConfigurationBiUnique`.
-/

namespace LBA

open Relation

variable {Γ Λ : Type*}

/-- The complete source step relation is a partial bijection at every tape width. -/
public def Machine.ConfigurationBiUnique (M : Machine Γ Λ) : Prop :=
  ∀ n : ℕ, Relator.BiUnique (@Step Γ Λ n M)

/-- Local transition functionality makes the complete configuration step relation functional,
including when a head move clamps at a tape boundary. -/
public theorem Machine.configurationStep_rightUnique_of_functional
    (M : Machine Γ Λ) (hfunctional : M.Functional) {n : ℕ} :
    Relator.RightUnique (@Step Γ Λ n M) := by
  intro source left right hleft hright
  rcases hleft with ⟨leftState, leftWrite, leftDir, hleftEnabled, rfl⟩
  rcases hright with ⟨rightState, rightWrite, rightDir, hrightEnabled, rfl⟩
  have hmove : (leftState, leftWrite, leftDir) =
      (rightState, rightWrite, rightDir) :=
    hfunctional source.state source.tape.read hleftEnabled hrightEnabled
  cases hmove
  rfl

/-- A locally functional and configuration-cofunctional machine is configuration-reversible. -/
public theorem Machine.configurationBiUnique_of_functional_cofunctional
    (M : Machine Γ Λ) (hfunctional : M.Functional) (hcofunctional : M.Cofunctional) :
    M.ConfigurationBiUnique := by
  intro n
  exact ⟨fun _ _ _ hleft hright => hcofunctional hleft hright,
    M.configurationStep_rightUnique_of_functional hfunctional⟩

/-- The two phase-dependent layers on the split machine.  Color zero contains exactly the
input-to-output copy edges; color one contains exactly the lifted reversible source steps. -/
public def Machine.reversibleTwoMatchingStepLayer
    (M : Machine Γ Λ) {n : ℕ} (color : Fin 2) :
    DLBA.Cfg Γ (ThreeMatchingState Λ) n →
      DLBA.Cfg Γ (ThreeMatchingState Λ) n → Prop :=
  fun source target =>
    match source.state, target.state with
    | .input _, .output _ =>
        threeMatchingProjectCfg source = threeMatchingProjectCfg target ∧ color = 0
    | .output _, .input _ =>
        Step M (threeMatchingProjectCfg source) (threeMatchingProjectCfg target) ∧ color = 1
    | _, _ => False

/-- Every split-machine edge has exactly one of the two phase colors, and every colored edge is
a genuine split-machine step. -/
public theorem Machine.reversibleTwoMatchingStepLayer_partition
    (M : Machine Γ Λ) {n : ℕ} :
    (∀ source target : DLBA.Cfg Γ (ThreeMatchingState Λ) n,
      Step M.threeMatchings source target ↔
        ∃! color, M.reversibleTwoMatchingStepLayer (n := n) color source target) ∧
      ∀ color (source target : DLBA.Cfg Γ (ThreeMatchingState Λ) n),
        M.reversibleTwoMatchingStepLayer color source target →
          Step M.threeMatchings source target := by
  constructor
  · intro source target
    constructor
    · intro hstep
      rw [M.step_threeMatchings_iff] at hstep
      rcases hstep with ⟨cfg, rfl, rfl⟩ | ⟨old, new, hedge, rfl, rfl⟩
      · refine ⟨0, ⟨rfl, rfl⟩, ?_⟩
        intro color hcolor
        exact hcolor.2
      · refine ⟨1, ⟨hedge, rfl⟩, ?_⟩
        intro color hcolor
        exact hcolor.2
    · rintro ⟨color, hcolor, _⟩
      rcases source with ⟨sourceState, sourceTape⟩
      rcases target with ⟨targetState, targetTape⟩
      cases sourceState <;> cases targetState <;>
        simp only [Machine.reversibleTwoMatchingStepLayer,
          threeMatchingProjectCfg] at hcolor
      · exact (M.step_threeMatchings_input_iff _ _ _).2
          (congrArg threeMatchingOutputCfg hcolor.1).symm
      · exact (M.step_threeMatchingOutput_input_iff _ _).2 hcolor.1
  · intro color source target hlayer
    rcases source with ⟨sourceState, sourceTape⟩
    rcases target with ⟨targetState, targetTape⟩
    cases sourceState <;> cases targetState <;>
      simp only [Machine.reversibleTwoMatchingStepLayer,
        threeMatchingProjectCfg] at hlayer
    · exact (M.step_threeMatchings_input_iff _ _ _).2
        (congrArg threeMatchingOutputCfg hlayer.1).symm
    · exact (M.step_threeMatchingOutput_input_iff _ _).2 hlayer.1

/-- Each phase color is functional when the source configuration relation is functional. -/
private theorem Machine.reversibleTwoMatchingStepLayer_rightUnique
    (M : Machine Γ Λ) {n : ℕ}
    (hsource : Relator.RightUnique (@Step Γ Λ n M)) (color : Fin 2) :
    Relator.RightUnique (M.reversibleTwoMatchingStepLayer (n := n) color) := by
  intro source left right hleft hright
  rcases source with ⟨sourceState, sourceTape⟩
  rcases left with ⟨leftState, leftTape⟩
  rcases right with ⟨rightState, rightTape⟩
  cases sourceState <;> cases leftState <;> cases rightState <;>
    simp only [Machine.reversibleTwoMatchingStepLayer,
      threeMatchingProjectCfg] at hleft hright
  · exact congrArg threeMatchingOutputCfg (hleft.1.symm.trans hright.1)
  · exact congrArg threeMatchingInputCfg (hsource hleft.1 hright.1)

/-- Each phase color is cofunctional when the source configuration relation is cofunctional. -/
private theorem Machine.reversibleTwoMatchingStepLayer_leftUnique
    (M : Machine Γ Λ) {n : ℕ}
    (hsource : Relator.LeftUnique (@Step Γ Λ n M)) (color : Fin 2) :
    Relator.LeftUnique (M.reversibleTwoMatchingStepLayer (n := n) color) := by
  intro left right target hleft hright
  rcases left with ⟨leftState, leftTape⟩
  rcases right with ⟨rightState, rightTape⟩
  rcases target with ⟨targetState, targetTape⟩
  cases targetState <;> cases leftState <;> cases rightState <;>
    simp only [Machine.reversibleTwoMatchingStepLayer,
      threeMatchingProjectCfg] at hleft hright
  · exact congrArg threeMatchingOutputCfg (hsource hleft.1 hright.1)
  · exact congrArg threeMatchingInputCfg (hleft.1.trans hright.1.symm)

/-- Both phases are partial bijections when the source configuration relation is. -/
public theorem Machine.reversibleTwoMatchingStepLayer_biUnique
    (M : Machine Γ Λ) {n : ℕ}
    (hsource : Relator.BiUnique (@Step Γ Λ n M)) (color : Fin 2) :
    Relator.BiUnique (M.reversibleTwoMatchingStepLayer (n := n) color) :=
  ⟨M.reversibleTwoMatchingStepLayer_leftUnique hsource.1 color,
    M.reversibleTwoMatchingStepLayer_rightUnique hsource.2 color⟩

/-- No two edges of one phase color are composable. -/
public theorem Machine.reversibleTwoMatchingStepLayer_pathLengthAtMostOne
    (M : Machine Γ Λ) {n : ℕ} (color : Fin 2) :
    LinearTwoDiforestReachability.PathLengthAtMostOne
      (M.reversibleTwoMatchingStepLayer (n := n) color) := by
  intro first middle last hfirst hlast
  rcases first with ⟨firstState, firstTape⟩
  rcases middle with ⟨middleState, middleTape⟩
  rcases last with ⟨lastState, lastTape⟩
  cases firstState <;> cases middleState <;> cases lastState <;>
    simp only [Machine.reversibleTwoMatchingStepLayer,
      threeMatchingProjectCfg] at hfirst hlast
  · exact Fin.zero_ne_one (hfirst.2.symm.trans hlast.2)
  · exact Fin.zero_ne_one (hfirst.2.symm.trans hlast.2).symm

/-- Splitting a configuration-reversible machine into input and output phases gives an exact
two-directed-matching presentation. -/
public theorem Machine.threeMatchings_hasTwoMatchingStepPartition_of_configurationBiUnique
    (M : Machine Γ Λ) (hreversible : M.ConfigurationBiUnique) :
    M.threeMatchings.HasTwoMatchingStepPartition := by
  refine ⟨fun n => M.reversibleTwoMatchingStepLayer (n := n), ?_, ?_, ?_, ?_⟩
  · intro n
    exact M.reversibleTwoMatchingStepLayer_partition.1
  · intro n
    exact M.reversibleTwoMatchingStepLayer_partition.2
  · intro n color
    exact M.reversibleTwoMatchingStepLayer_biUnique (hreversible n) color
  · intro n color
    exact M.reversibleTwoMatchingStepLayer_pathLengthAtMostOne color

/-- Convenience form using the existing local-functionality and configuration-cofunctionality
interfaces. -/
public theorem Machine.threeMatchings_hasTwoMatchingStepPartition_of_functional_cofunctional
    (M : Machine Γ Λ) (hfunctional : M.Functional) (hcofunctional : M.Cofunctional) :
    M.threeMatchings.HasTwoMatchingStepPartition :=
  M.threeMatchings_hasTwoMatchingStepPartition_of_configurationBiUnique
    (M.configurationBiUnique_of_functional_cofunctional hfunctional hcofunctional)

end LBA

/-! ## Language classes -/

/-- A language with a canonical endmarker LBA presentation whose complete **raw clamped**
configuration step relation is a partial bijection at every tape width.  This is deliberately the
literal structural property used above, not the usual promise-restricted marked-tape notion. -/
public def is_ReversibleLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.ConfigurationBiUnique ∧ LBA.LanguageEnd M = L

/-- Languages with a finite all-raw-configuration-biunique LBA presentation.  The later theorem
`reversibleLBA_eq_trivial_languages` characterizes this class exactly. -/
public def ReversibleLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_ReversibleLBA

/-- A configuration-reversible presentation becomes an exact-two-matching presentation after
the same-width two-phase split. -/
public theorem is_TwoMatchingLBA_of_is_ReversibleLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_ReversibleLBA L) : is_TwoMatchingLBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hreversible, hM⟩
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  refine ⟨Γ, LBA.ThreeMatchingState Λ,
    hΓ, inferInstance, hdecΓ, inferInstance, M.threeMatchings,
    M.threeMatchings_hasTwoMatchingStepPartition_of_configurationBiUnique hreversible, ?_⟩
  exact M.languageEnd_threeMatchings_eq.trans hM

/-- Every language with a configuration-reversible LBA presentation has an exact-two-matching
LBA presentation. -/
public theorem reversibleLBA_subset_twoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (ReversibleLBA : Set (Language T)) ⊆ TwoMatchingLBA :=
  fun _ hL => is_TwoMatchingLBA_of_is_ReversibleLBA hL

end
