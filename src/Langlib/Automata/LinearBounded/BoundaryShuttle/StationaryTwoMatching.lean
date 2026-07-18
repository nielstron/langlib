module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.StationaryRawDegree
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.AlternatingMatchingCriterion
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact two-matching presentation of the stationary shuttle

The raw stationary-shuttle graph is functional, has indegree at most one, and flips phase on
every edge.  The general `AlternatingMatchingCriterion` therefore supplies, uniformly at every
tape width, an exact partition into two directed matchings whose monochromatic paths have length
at most one.

This remains a theorem about the standalone stay-instruction compiler.  A combined compiler must
use a sum of the two protocol alphabets/states and establish cross-kind predecessor inversion.
In particular it needs `Machine.ShuttleTargetKindDisjoint` (or an equivalent retained kind tag):
the final directional edge restores an arbitrary plain neighbour, so merely separating the
written symbols of directional and stationary source instructions does not rule out a continuing
merge at a shared normal target state.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- Finite two-valued phase associated with the stationary protocol state. -/
@[expose]
public def stationaryShuttlePhase {n : ℕ}
    (cfg :
      DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n) :
    Fin 2 :=
  if stationaryShuttleParity cfg.state then 1 else 0

/-- Every raw stationary-shuttle edge flips the finite phase. -/
public theorem Machine.stationaryShuttlePhase_ne_of_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target :
      DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n}
    (hstep : Step M.stationaryShuttle source target) :
    stationaryShuttlePhase source ≠ stationaryShuttlePhase target := by
  have hparity := M.stationaryShuttleParity_ne_of_step hstep
  unfold stationaryShuttlePhase
  cases hsource : stationaryShuttleParity source.state <;>
    cases htarget : stationaryShuttleParity target.state <;> simp_all

/-- Exact width-uniform two-matching presentation of the stationary shuttle under precisely
row functionality and `(target, written)` backward injectivity. -/
public theorem Machine.stationaryShuttle_hasTwoMatchingStepPartition
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : M.StationaryFunctional)
    (htarget : M.StationaryTargetWrittenInjective) :
    M.stationaryShuttle.HasTwoMatchingStepPartition := by
  apply M.stationaryShuttle.hasTwoMatchingStepPartition_of_localFunctional_alternating
    (M.stationaryShuttle_functional hfunctional)
    (M.stationaryShuttle_configurationIndegreeAtMostTwo htarget)
    (fun n left right target hleft hright hne next ↦
      M.sink_of_two_distinct_predecessors_stationaryShuttle
        htarget hne hleft hright next)
    (fun _ cfg ↦ stationaryShuttlePhase cfg)
  intro n source target hstep
  exact M.stationaryShuttlePhase_ne_of_step hstep

/-- Ordinary local functionality discharges the stationary row-functionality premise. -/
public theorem Machine.stationaryShuttle_hasTwoMatchingStepPartition_of_functional
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : M.Functional)
    (htarget : M.StationaryTargetWrittenInjective) :
    M.stationaryShuttle.HasTwoMatchingStepPartition :=
  M.stationaryShuttle_hasTwoMatchingStepPartition
    (M.stationaryFunctional_of_functional hfunctional) htarget

end LBA
