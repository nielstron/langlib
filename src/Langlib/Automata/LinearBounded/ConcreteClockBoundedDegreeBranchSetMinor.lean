module

public import Langlib.Automata.LinearBounded.BoundedDegreeBranchSetMinor
public import Langlib.Automata.LinearBounded.ConcreteClockBranchSetMinor

@[expose]
public section

/-!
# Branch-set minors through the complete clock-and-degree pipeline

This is the generic composition theorem for the two concrete compiler stages.  Every reflexive
fixed-width source configuration graph survives first the actual one-tape acyclic-clock protocol
and then both actual degree serializers as an underlying-undirected branch-set minor of the
complete final raw graph.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]
variable [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]

/-- **Complete concrete-pipeline contraction.**  At every tape width, a reflexive source
configuration relation is a branch-set minor of the raw configuration relation produced by the
actual acyclic-clock compiler followed by the actual simultaneous degree serializer.

No positive-width or alphabet-cardinality hypothesis is used, and the large relation is not
restricted to well-formed protocol configurations. -/
public noncomputable def concreteClockBoundedDegreeBranchSetMinorModel
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (selfLoop : ∀ cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n,
      LBA.Step M cfg cfg) :
    BranchSetMinorModel
      (SymmetricClosure (LBA.Step (n := n) M))
      (LBA.Step (n := n) (machine M).boundedDegree) :=
  (concreteClockBranchSetMinorModel M selfLoop).trans
    (LBA.Machine.boundedDegreeStepBranchSetMinorModel (machine M) n)

end LBA.AcyclicClock

end
