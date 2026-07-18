module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.RawDegree
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.AlternatingMatchingCriterion
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact two-matching presentation of the marked Euler probe

The marked Euler probe is locally deterministic, has raw configuration
indegree at most two, and makes every genuine double merge terminal.  Its
explicit Boolean microphase flips on every raw step.  The general alternating
matching criterion therefore partitions its complete fixed-width raw graph
into two short directed matchings, uniformly over every tape width.  No
well-formedness promise or cardinality hypothesis on any source type is used.
-/

namespace GraphWalking

namespace MarkedEulerProbe

universe uTerminal uWork uState

variable {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}

/-- The finite two-valued coloring induced by the probe's explicit Boolean
microphase. -/
@[expose]
public def rawPhase {n : ℕ}
    (cfg : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n) : Fin 2 :=
  if cfg.state.phase then 1 else 0

/-- Every raw probe edge crosses the two-valued phase coloring. -/
public theorem rawPhase_ne_of_step
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {source target : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) source target) :
    rawPhase source ≠ rawPhase target := by
  have hphase := phase_ne_of_step machine hstep
  unfold rawPhase
  cases hsource : source.state.phase <;>
    cases htarget : target.state.phase <;> simp_all

/-- The complete raw marked-probe graph admits a width-uniform partition into
two directed matchings. -/
public theorem rawMachine_hasTwoMatchingStepPartition
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    (rawMachine machine).HasTwoMatchingStepPartition := by
  apply (rawMachine machine).hasTwoMatchingStepPartition_of_localFunctional_alternating
    (rawMachine_functional machine)
    (rawMachine_configurationIndegreeAtMostTwo machine)
    (fun n left right target hleft hright hne next ↦
      sink_of_two_distinct_predecessors_rawMachine machine hne hleft hright next)
    (fun _ cfg ↦ rawPhase cfg)
  intro n source target hstep
  exact rawPhase_ne_of_step machine hstep

end MarkedEulerProbe

end GraphWalking

end
