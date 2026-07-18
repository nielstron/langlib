module

public import Langlib.Automata.LinearBounded.BranchSetMinor
public import Langlib.Automata.LinearBounded.LocalityHypercube
import Mathlib.Tactic

@[expose]
public section

/-!
# A formal hypercube minor certificate for a fixed LBA

`LocalityHypercube` proves the transition facts from which a Boolean-cube minor follows.  This
file packages those facts as an actual branch-set certificate.  The branch set of a Boolean
vector consists of all phase/head configurations carrying exactly that tape contents.

This is a structural obstruction only: the fixed machine accepts no language, and a graph-minor
certificate is not a reachability or determinization lower bound.
-/

namespace LBA.LocalityHypercube

/-- Adjacency in the Boolean cube: the target is obtained by flipping one coordinate. -/
@[expose]
public def CubeEdge {d : ℕ} (source target : Fin d → Bool) : Prop :=
  ∃ coordinate : Fin d,
    target = Function.update source coordinate (!source coordinate)

/-- All configurations whose phase/head representative carries a fixed tape contents. -/
@[expose]
public def fiber {n : ℕ} (contents : Fin (n + 1) → Bool) :
    Set (DLBA.Cfg Bool Phase n) :=
  Set.range fun representative : Phase × Fin (n + 1) =>
    phaseCfg representative.1 contents representative.2

private theorem right_succ_in_fiber {n k : ℕ}
    (contents : Fin (n + 1) → Bool) (hk : k < n) :
    Relation.Restricted (fiber contents)
      (Relation.SymmetricClosure (LBA.Step machine))
      (rightCfg contents ⟨k, by omega⟩)
      (rightCfg contents ⟨k + 1, by omega⟩) := by
  refine ⟨?_, Or.inl (step_right_succ contents hk), ?_⟩
  · exact ⟨(.right, ⟨k, by omega⟩), rfl⟩
  · exact ⟨(.right, ⟨k + 1, by omega⟩), rfl⟩

private theorem left_pred_in_fiber {n k : ℕ}
    (contents : Fin (n + 1) → Bool) (hk : k + 1 < n + 1) :
    Relation.Restricted (fiber contents)
      (Relation.SymmetricClosure (LBA.Step machine))
      (leftCfg contents ⟨k + 1, hk⟩)
      (leftCfg contents ⟨k, by omega⟩) := by
  refine ⟨?_, Or.inl (step_left_pred contents hk), ?_⟩
  · exact ⟨(.left, ⟨k + 1, hk⟩), rfl⟩
  · exact ⟨(.left, ⟨k, by omega⟩), rfl⟩

private theorem turn_left_in_fiber {n : ℕ}
    (contents : Fin (n + 1) → Bool) (head : Fin (n + 1)) :
    Relation.Restricted (fiber contents)
      (Relation.SymmetricClosure (LBA.Step machine))
      (rightCfg contents head) (leftCfg contents head) := by
  exact ⟨⟨(.right, head), rfl⟩, Or.inl (step_turn_left contents head),
    ⟨(.left, head), rfl⟩⟩

private theorem turn_right_in_fiber {n : ℕ}
    (contents : Fin (n + 1) → Bool) (head : Fin (n + 1)) :
    Relation.Restricted (fiber contents)
      (Relation.SymmetricClosure (LBA.Step machine))
      (leftCfg contents head) (rightCfg contents head) := by
  exact ⟨⟨(.left, head), rfl⟩, Or.inl (step_turn_right contents head),
    ⟨(.right, head), rfl⟩⟩

private theorem fiber_reaches_right_from_zero {n k : ℕ}
    (contents : Fin (n + 1) → Bool) (hk : k < n + 1) :
    Relation.ReflTransGen
      (Relation.Restricted (fiber contents)
        (Relation.SymmetricClosure (LBA.Step machine)))
      (rightCfg contents ⟨0, Nat.zero_lt_succ n⟩)
      (rightCfg contents ⟨k, hk⟩) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
      have hk' : k < n + 1 := by omega
      exact (ih hk').tail (right_succ_in_fiber contents (by omega))

private theorem fiber_reaches_left_to_zero {n k : ℕ}
    (contents : Fin (n + 1) → Bool) (hk : k < n + 1) :
    Relation.ReflTransGen
      (Relation.Restricted (fiber contents)
        (Relation.SymmetricClosure (LBA.Step machine)))
      (leftCfg contents ⟨k, hk⟩)
      (leftCfg contents ⟨0, Nat.zero_lt_succ n⟩) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
      have hk' : k < n + 1 := by omega
      exact Relation.ReflTransGen.head (left_pred_in_fiber contents hk) (ih hk')

/-- The fixed-contents representatives are connected by paths staying inside their branch set. -/
public theorem fixedContents_connectedWithinFiber {n : ℕ}
    (contents : Fin (n + 1) → Bool)
    (sourcePhase targetPhase : Phase) (sourceHead targetHead : Fin (n + 1)) :
    Relation.ReflTransGen
      (Relation.Restricted (fiber contents)
        (Relation.SymmetricClosure (LBA.Step machine)))
      (phaseCfg sourcePhase contents sourceHead)
      (phaseCfg targetPhase contents targetHead) := by
  have source_to_zero :
      Relation.ReflTransGen
        (Relation.Restricted (fiber contents)
          (Relation.SymmetricClosure (LBA.Step machine)))
        (phaseCfg sourcePhase contents sourceHead)
        (rightCfg contents ⟨0, Nat.zero_lt_succ n⟩) := by
    cases sourcePhase with
    | right =>
        exact Relation.ReflTransGen.head (turn_left_in_fiber contents sourceHead)
          ((fiber_reaches_left_to_zero contents sourceHead.isLt).tail
            (turn_right_in_fiber contents ⟨0, Nat.zero_lt_succ n⟩))
    | left =>
        exact (fiber_reaches_left_to_zero contents sourceHead.isLt).tail
          (turn_right_in_fiber contents ⟨0, Nat.zero_lt_succ n⟩)
  have zero_to_target :
      Relation.ReflTransGen
        (Relation.Restricted (fiber contents)
          (Relation.SymmetricClosure (LBA.Step machine)))
        (rightCfg contents ⟨0, Nat.zero_lt_succ n⟩)
        (phaseCfg targetPhase contents targetHead) := by
    cases targetPhase with
    | right => exact fiber_reaches_right_from_zero contents targetHead.isLt
    | left =>
        exact (fiber_reaches_right_from_zero contents targetHead.isLt).tail
          (turn_left_in_fiber contents targetHead)
  exact source_to_zero.trans zero_to_target

/-- Distinct Boolean contents have disjoint configuration branch sets. -/
public theorem fiber_disjoint {n : ℕ} {left right : Fin (n + 1) → Bool}
    (hne : left ≠ right) : Disjoint (fiber left) (fiber right) := by
  rw [Set.disjoint_left]
  rintro _ ⟨⟨leftPhase, leftHead⟩, rfl⟩ ⟨⟨rightPhase, rightHead⟩, heq⟩
  exact hne (phaseCfg_eq_imp_contents_eq heq.symm)

/-- Every positive-dimensional Boolean cube has a branch-set minor model in the underlying
undirected configuration graph of one fixed two-state, binary-tape LBA. -/
public def hypercubeBranchSetMinor (n : ℕ) :
    Relation.BranchSetMinorModel
      (CubeEdge (d := n + 1))
      (LBA.Step (n := n) machine) where
  branchSet := fiber
  nonempty contents :=
    ⟨rightCfg contents ⟨0, Nat.zero_lt_succ n⟩,
      ⟨(.right, ⟨0, Nat.zero_lt_succ n⟩), rfl⟩⟩
  disjoint hne := fiber_disjoint hne
  connected contents {source target} hsource htarget := by
    rcases hsource with ⟨⟨sourcePhase, sourceHead⟩, rfl⟩
    rcases htarget with ⟨⟨targetPhase, targetHead⟩, rfl⟩
    exact fixedContents_connectedWithinFiber contents
      sourcePhase targetPhase sourceHead targetHead
  map_edge {source target} := by
    rintro ⟨coordinate, rfl⟩
    let flipped := Function.update source coordinate (!source coordinate)
    refine ⟨rightCfg source coordinate, ⟨(.right, coordinate), rfl⟩,
      leftCfg flipped coordinate, ⟨(.left, coordinate), rfl⟩, ?_⟩
    exact Or.inl (step_flip source coordinate)

end LBA.LocalityHypercube

end
