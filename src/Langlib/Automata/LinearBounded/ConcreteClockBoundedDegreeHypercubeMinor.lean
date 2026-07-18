module

public import Langlib.Automata.LinearBounded.ConcreteClockBoundedDegreeBranchSetMinor
public import Langlib.Automata.LinearBounded.ConcreteClockLocalityHypercubeMinor
public import Langlib.Automata.LinearBounded.AcyclicBoundedDegree

@[expose]
public section

/-!
# Hypercube minors survive the complete concrete clock-and-degree pipeline

This file closes the last structural contraction in the fixed locality witness.  It composes the
hypercube model through the actual one-tape acyclic-clock protocol and then through both actual
degree serializers.  The final relation is the complete raw configuration relation, including
malformed protocol states.  Independently, the same final machine is globally acyclic, has both
directed degrees at most two, and has the serializer's uniform two-partial-bijection partition.

These are graph-structure statements.  They do not decide directed reachability and do not
determinize the machine.
-/

namespace LBA.LocalityHypercube.ConcreteClock

open Relation

/-- The single fixed clocked and degree-serialized locality machine used by the final minor
certificate. -/
public noncomputable def boundedDegreeMachine :=
  (LBA.AcyclicClock.machine endmarkedReflexiveMachine).boundedDegree

/-- **Concrete clock-and-serializer cube theorem.**  For every `n`, the `(n+1)`-dimensional
Boolean cube is a branch-set minor of the complete raw width-`n` configuration graph of the
actual clocked, degree-two machine. -/
public noncomputable def boundedDegreeHypercubeBranchSetMinor (n : ℕ) :
    BranchSetMinorModel
      (LBA.LocalityHypercube.CubeEdge (d := n + 1))
      (LBA.Step (n := n) boundedDegreeMachine) := by
  change BranchSetMinorModel
    (LBA.LocalityHypercube.CubeEdge (d := n + 1))
    (LBA.Step (n := n)
      (LBA.AcyclicClock.machine endmarkedReflexiveMachine).boundedDegree)
  exact (endmarkedHypercubeBranchSetMinor n).trans
    (LBA.AcyclicClock.concreteClockBoundedDegreeBranchSetMinorModel
      endmarkedReflexiveMachine step_endmarkedReflexiveMachine_self)

/-- The final machine is globally acyclic on its complete raw configuration graphs, not merely
on the configurations used by the minor certificate. -/
public theorem boundedDegreeMachine_configurationAcyclic :
    boundedDegreeMachine.ConfigurationAcyclic := by
  apply LBA.AcyclicBoundedDegree.configurationAcyclic_boundedDegree
  intro n
  exact concreteClock_endmarkedReflexiveMachine_acyclic n

/-- Both directed degrees of every complete fixed-width configuration graph of the final machine
are at most two. -/
public theorem boundedDegreeMachine_configurationDegreeAtMostTwo :
    boundedDegreeMachine.ConfigurationDegreeAtMostTwo :=
  LBA.Machine.boundedDegree_configurationDegreeAtMostTwo
    (LBA.AcyclicClock.machine endmarkedReflexiveMachine)

/-- The final raw step relation has one syntactic, width-uniform partition into two partial
bijections.  The layers are not claimed to be directed matchings. -/
public theorem boundedDegreeMachine_hasTwoBiUniqueStepPartition :
    boundedDegreeMachine.HasTwoBiUniqueStepPartition :=
  LBA.Machine.boundedDegree_hasTwoBiUniqueStepPartition
    (LBA.AcyclicClock.machine endmarkedReflexiveMachine)

/-- Package the three global promises satisfied simultaneously by the machine whose every
fixed-width graph contains the cube minor above. -/
public theorem boundedDegreeMachine_globalProperties :
    boundedDegreeMachine.ConfigurationAcyclic ∧
      boundedDegreeMachine.ConfigurationDegreeAtMostTwo ∧
      boundedDegreeMachine.HasTwoBiUniqueStepPartition :=
  ⟨boundedDegreeMachine_configurationAcyclic,
    boundedDegreeMachine_configurationDegreeAtMostTwo,
    boundedDegreeMachine_hasTwoBiUniqueStepPartition⟩

end LBA.LocalityHypercube.ConcreteClock

end
