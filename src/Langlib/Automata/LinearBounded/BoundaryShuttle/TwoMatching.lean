module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.Sink
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.AlternatingMatchingCriterion
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact two-matching presentation of the boundary shuttle

The shuttle's raw configuration graph is a partial function of indegree at most two.  Every
genuine double merge is terminal, and the four syntactic protocol phases alternate parity.
The general alternating-matching criterion therefore partitions every fixed-width raw step
relation into exactly two short directed matchings; raw cycles cause no problem.

This theorem concerns `boundaryShuttle`, which compiles only enabled **directional** source
instructions.  It does not eliminate source stay moves and does not by itself assert equality of
whole recognized languages.  `reaches_boundaryShuttle_of_move` is the corresponding positive
four-step simulation theorem for non-clamped directional moves.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- Finite two-valued phase associated with the shuttle's Boolean syntactic parity. -/
@[expose]
public def shuttlePhase {n : ℕ}
    (cfg : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n) : Fin 2 :=
  if shuttleParity cfg.state then 1 else 0

/-- Every raw shuttle edge flips the finite phase. -/
public theorem Machine.shuttlePhase_ne_of_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    (hstep : Step M.boundaryShuttle source target) :
    shuttlePhase source ≠ shuttlePhase target := by
  have hparity := M.shuttleParity_ne_of_step hstep
  unfold shuttlePhase
  cases hsource : shuttleParity source.state <;>
    cases htarget : shuttleParity target.state <;> simp_all

/-- The boundary shuttle has an exact width-uniform partition into two directed matchings under
the precise row-functionality and target-tag erasure hypotheses. -/
public theorem Machine.boundaryShuttle_hasTwoMatchingStepPartition
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : M.DirectionalFunctional)
    (htargetInjective : M.DirectionalTargetInjective) :
    M.boundaryShuttle.HasTwoMatchingStepPartition := by
  apply M.boundaryShuttle.hasTwoMatchingStepPartition_of_localFunctional_alternating
    (M.boundaryShuttle_functional hfunctional)
    (M.boundaryShuttle_configurationIndegreeAtMostTwo htargetInjective)
    (fun n left right target hleft hright hne next ↦
      M.sink_of_two_distinct_predecessors_boundaryShuttle
        htargetInjective hne hleft hright next)
    (fun _ cfg ↦ shuttlePhase cfg)
  intro n source target hstep
  exact M.shuttlePhase_ne_of_step hstep

/-- Convenience form: ordinary local functionality of the source discharges the shuttle's
directional row-functionality premise.  Target-state uniqueness of full incoming instructions
remains a separate, genuinely stronger normal-form requirement. -/
public theorem Machine.boundaryShuttle_hasTwoMatchingStepPartition_of_functional
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : M.Functional)
    (htargetInjective : M.DirectionalTargetInjective) :
    M.boundaryShuttle.HasTwoMatchingStepPartition :=
  M.boundaryShuttle_hasTwoMatchingStepPartition
    (M.directionalFunctional_of_functional hfunctional) htargetInjective

end LBA

