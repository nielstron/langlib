module

public import Langlib.Automata.LinearBounded.BinaryBranchingBranchSetMinor
public import Langlib.Automata.LinearBounded.IncomingSerializerBranchSetMinor

@[expose]
public section

/-!
# The complete degree serializer preserves configuration-graph minors

`Machine.boundedDegree` first replaces arbitrary outgoing branching by a binary scan and then
serializes the resulting incoming edges.  The two concrete branch-set models compose without
restricting the raw target graph: malformed serializer configurations remain present, but need
not belong to a branch set.
-/

namespace LBA

open Relation

variable {Γ Λ : Type*}

/-- **Complete degree-serializer contraction.**  At every tape width, the symmetrized raw
configuration graph of a machine is a branch-set minor of the raw configuration graph obtained
by applying both concrete degree serializers.

The statement is uniform in `n`, has no positive-width premise, and does not restrict the large
relation to well-formed protocol configurations. -/
public noncomputable def Machine.boundedDegreeStepBranchSetMinorModel
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (n : ℕ) :
    BranchSetMinorModel
      (SymmetricClosure (Step (n := n) M))
      (Step (n := n) M.boundedDegree) :=
  (M.binaryBranchStepBranchSetMinorModel n).trans
    (IncomingSerializer.branchSetMinorModel M.binaryBranch)

end LBA

end
