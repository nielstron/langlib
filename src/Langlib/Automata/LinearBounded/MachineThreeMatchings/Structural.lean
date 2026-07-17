module

public import Langlib.Automata.LinearBounded.AcyclicBoundedDegree
public import Langlib.Automata.LinearBounded.FiniteAcyclicRank
public import Langlib.Automata.LinearBounded.MachineThreeMatchings.Layering

@[expose]
public section

/-!
# Degree and acyclicity of the machine-level three-matching split

Input copies have one internal successor and inherit the source indegree.  Output copies inherit
the source outdegree and have one internal predecessor.  Thus simultaneous indegree/outdegree
two is preserved.  A strict rank for an acyclic finite source configuration graph lifts by
putting input and output copies at consecutive ranks, proving global acyclicity on every raw
fixed-width configuration graph.
-/

namespace LBA

open Classical Relation Set

variable {Γ Λ : Type*}

private theorem Machine.target_eq_input_project_of_step_output
    (M : Machine Γ Λ) {n : ℕ} (state : Λ) (tape : DLBA.BoundedTape Γ n)
    {target : DLBA.Cfg Γ (ThreeMatchingState Λ) n}
    (hstep : Step M.threeMatchings ⟨.output state, tape⟩ target) :
    target = threeMatchingInputCfg (threeMatchingProjectCfg target) := by
  obtain ⟨next, written, direction, henabled, rfl⟩ :=
    (M.step_threeMatchings_output_iff state tape target).1 hstep
  rfl

private theorem Machine.source_eq_output_project_of_step_input
    (M : Machine Γ Λ) {n : ℕ}
    {source : DLBA.Cfg Γ (ThreeMatchingState Λ) n}
    (state : Λ) (tape : DLBA.BoundedTape Γ n)
    (hstep : Step M.threeMatchings source ⟨.input state, tape⟩) :
    source = threeMatchingOutputCfg (threeMatchingProjectCfg source) := by
  rcases source with ⟨sourceState, sourceTape⟩
  cases sourceState with
  | input source =>
      have heq :=
        (M.step_threeMatchings_input_iff source sourceTape
          (⟨ThreeMatchingState.input state, tape⟩ :
            DLBA.Cfg Γ (ThreeMatchingState Λ) n)).1 hstep
      simp at heq
  | output source => rfl

/-- The split compiler preserves simultaneous configuration indegree/outdegree at most two. -/
public theorem Machine.configurationDegreeAtMostTwo_threeMatchings
    (M : Machine Γ Λ) (hdegree : M.ConfigurationDegreeAtMostTwo) :
    M.threeMatchings.ConfigurationDegreeAtMostTwo := by
  constructor
  · intro n source
    rcases source with ⟨sourceState, sourceTape⟩
    cases sourceState with
    | input state =>
        calc
          Set.encard {target | Step M.threeMatchings
              (⟨ThreeMatchingState.input state, sourceTape⟩ :
                DLBA.Cfg Γ (ThreeMatchingState Λ) n) target} ≤ 1 := by
            apply Set.encard_le_one_iff.mpr
            intro left right hleft hright
            exact
              ((M.step_threeMatchings_input_iff state sourceTape left).1 hleft).trans
                ((M.step_threeMatchings_input_iff state sourceTape right).1 hright).symm
          _ ≤ 2 := by norm_num
    | output state =>
        calc
          Set.encard {target | Step M.threeMatchings
              (⟨ThreeMatchingState.output state, sourceTape⟩ :
                DLBA.Cfg Γ (ThreeMatchingState Λ) n) target} ≤
              Set.encard {target | Step M
                (⟨state, sourceTape⟩ : DLBA.Cfg Γ Λ n) target} := by
            apply Set.encard_le_encard_of_injOn
              (f := threeMatchingProjectCfg)
            · intro target htarget
              obtain ⟨next, written, direction, henabled, rfl⟩ :=
                (M.step_threeMatchings_output_iff state sourceTape target).1 htarget
              exact ⟨next, written, direction, henabled, rfl⟩
            · intro left hleft right hright heq
              calc
                left = threeMatchingInputCfg (threeMatchingProjectCfg left) :=
                  M.target_eq_input_project_of_step_output state sourceTape hleft
                _ = threeMatchingInputCfg (threeMatchingProjectCfg right) :=
                  congrArg threeMatchingInputCfg heq
                _ = right :=
                  (M.target_eq_input_project_of_step_output state sourceTape hright).symm
          _ ≤ 2 := hdegree.1 n ⟨state, sourceTape⟩
  · intro n target
    rcases target with ⟨targetState, targetTape⟩
    cases targetState with
    | input state =>
        calc
          Set.encard {source | Step M.threeMatchings source
              (⟨ThreeMatchingState.input state, targetTape⟩ :
                DLBA.Cfg Γ (ThreeMatchingState Λ) n)} ≤
              Set.encard {source | Step M source
                (⟨state, targetTape⟩ : DLBA.Cfg Γ Λ n)} := by
            apply Set.encard_le_encard_of_injOn
              (f := threeMatchingProjectCfg)
            · intro source hsource
              have hphase :=
                M.source_eq_output_project_of_step_input state targetTape hsource
              rw [hphase] at hsource
              exact (M.step_threeMatchingOutput_input_iff
                (threeMatchingProjectCfg source) ⟨state, targetTape⟩).1 hsource
            · intro left hleft right hright heq
              calc
                left = threeMatchingOutputCfg (threeMatchingProjectCfg left) :=
                  M.source_eq_output_project_of_step_input state targetTape hleft
                _ = threeMatchingOutputCfg (threeMatchingProjectCfg right) :=
                  congrArg threeMatchingOutputCfg heq
                _ = right :=
                  (M.source_eq_output_project_of_step_input state targetTape hright).symm
          _ ≤ 2 := hdegree.2 n ⟨state, targetTape⟩
    | output state =>
        calc
          Set.encard {source | Step M.threeMatchings source
              (⟨ThreeMatchingState.output state, targetTape⟩ :
                DLBA.Cfg Γ (ThreeMatchingState Λ) n)} ≤ 1 := by
            apply Set.encard_le_one_iff.mpr
            intro left right hleft hright
            change Step M.threeMatchings left
              (⟨ThreeMatchingState.output state, targetTape⟩ :
                DLBA.Cfg Γ (ThreeMatchingState Λ) n) at hleft
            change Step M.threeMatchings right
              (⟨ThreeMatchingState.output state, targetTape⟩ :
                DLBA.Cfg Γ (ThreeMatchingState Λ) n) at hright
            rw [M.step_threeMatchings_iff] at hleft hright
            rcases hleft with
              ⟨oldLeft, hleftSource, hleftTarget⟩ |
                ⟨oldLeft, newLeft, _, hleftSource, hleftTarget⟩
            · rcases hright with
                ⟨oldRight, hrightSource, hrightTarget⟩ |
                  ⟨oldRight, newRight, _, hrightSource, hrightTarget⟩
              · have hold : oldLeft = oldRight := by
                  exact congrArg threeMatchingProjectCfg
                    (hleftTarget.symm.trans hrightTarget)
                subst oldRight
                exact hleftSource.trans hrightSource.symm
              · rcases newRight with ⟨rightState, rightTape⟩
                simp [threeMatchingInputCfg] at hrightTarget
            · rcases newLeft with ⟨leftState, leftTape⟩
              simp [threeMatchingInputCfg] at hleftTarget
          _ ≤ 2 := by norm_num

/-! ## Global raw-configuration acyclicity -/

/-- Lift an old strict rank by placing the input and output copies at consecutive values. -/
@[expose]
public def threeMatchingRank {n : ℕ} (rank : DLBA.Cfg Γ Λ n → ℕ)
    (cfg : DLBA.Cfg Γ (ThreeMatchingState Λ) n) : ℕ :=
  match cfg.state with
  | .input _ => rank (threeMatchingProjectCfg cfg) * 2
  | .output _ => rank (threeMatchingProjectCfg cfg) * 2 + 1

/-- A strict source-configuration rank remains strict after the phase split. -/
public theorem Machine.threeMatchingRank_lt_of_step
    (M : Machine Γ Λ) {n : ℕ} (rank : DLBA.Cfg Γ Λ n → ℕ)
    (hstrict : ∀ ⦃source target⦄, Step M source target →
      rank source < rank target)
    {source target : DLBA.Cfg Γ (ThreeMatchingState Λ) n}
    (hstep : Step M.threeMatchings source target) :
    threeMatchingRank rank source < threeMatchingRank rank target := by
  rw [M.step_threeMatchings_iff] at hstep
  rcases hstep with ⟨cfg, rfl, rfl⟩ | ⟨old, new, hedge, rfl, rfl⟩
  · rcases cfg with ⟨state, tape⟩
    simp [threeMatchingRank, threeMatchingInputCfg,
      threeMatchingOutputCfg, threeMatchingProjectCfg]
  · have hrank := hstrict hedge
    rcases old with ⟨oldState, oldTape⟩
    rcases new with ⟨newState, newTape⟩
    simp only [threeMatchingRank, threeMatchingInputCfg,
      threeMatchingOutputCfg, threeMatchingProjectCfg]
    omega

/-- Splitting preserves global acyclicity of every complete fixed-width configuration graph. -/
public theorem Machine.configurationAcyclic_threeMatchings
    [Fintype Γ] [Fintype Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic) :
    M.threeMatchings.ConfigurationAcyclic := by
  intro n cfg
  let oldRank : DLBA.Cfg Γ Λ n → ℕ :=
    FiniteAcyclicRank.rank (Step M)
  apply FiniteAcyclicRank.acyclic_of_strictRank
    (rank := threeMatchingRank oldRank)
  intro source target hstep
  apply M.threeMatchingRank_lt_of_step oldRank
  · intro old new hedge
    exact FiniteAcyclicRank.rank_lt_of_edge (hacyclic n) hedge
  · exact hstep

end LBA

end
