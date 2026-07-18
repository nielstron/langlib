module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedSink
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.AlternatingMatchingCriterion
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact two-matching presentation of the combined shuttle

The unified compiler includes every enabled source instruction.  Its complete raw configuration
graph is functional, has indegree at most two, flips a two-valued syntactic phase on every edge,
and makes every genuine double merge terminal.  The general alternating-matching criterion
therefore partitions each fixed-width raw step relation into exactly two directed matchings.

This is not a whole-language equivalence theorem.  Outward clamped source moves, endmarker
transport, and reflection of arbitrary compiled runs remain separate obligations.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- Finite phase corresponding to `combinedShuttleParity`. -/
@[expose]
public def combinedShuttlePhase {n : ℕ}
    (cfg : DLBA.Cfg
      (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n) : Fin 2 :=
  if combinedShuttleParity cfg.state then 1 else 0

public theorem Machine.combinedShuttlePhase_ne_of_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg
      (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    (hstep : Step M.combinedBoundaryShuttle source target) :
    combinedShuttlePhase source ≠ combinedShuttlePhase target := by
  have hparity := M.combinedShuttleParity_ne_of_step hstep
  unfold combinedShuttlePhase
  cases hsource : combinedShuttleParity source.state <;>
    cases htarget : combinedShuttleParity target.state <;> simp_all

/-- Exact width-uniform two-matching partition of the combined raw machine under the three
backward normal-form hypotheses and ordinary source functionality. -/
public theorem Machine.combinedBoundaryShuttle_hasTwoMatchingStepPartition
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : M.Functional)
    (hdirectional : M.DirectionalTargetInjective)
    (hstationary : M.StationaryTargetWrittenInjective)
    (hkind : M.ShuttleTargetKindDisjoint) :
    M.combinedBoundaryShuttle.HasTwoMatchingStepPartition := by
  apply M.combinedBoundaryShuttle.hasTwoMatchingStepPartition_of_localFunctional_alternating
    (M.combinedBoundaryShuttle_functional hfunctional)
    (M.combinedBoundaryShuttle_configurationIndegreeAtMostTwo
      hdirectional hstationary hkind)
    (fun n left right target hleft hright hne next ↦
      M.sink_of_two_distinct_predecessors_combinedBoundaryShuttle
        hdirectional hstationary hkind hne hleft hright next)
    (fun _ cfg ↦ combinedShuttlePhase cfg)
  intro n source target hstep
  exact M.combinedShuttlePhase_ne_of_step hstep

end LBA
