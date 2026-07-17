module

public import Langlib.Automata.LinearBounded.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# A fixed binary LBA with hypercube tape edges

This file gives a small, concrete obstruction to extracting useful graph structure merely from
the locality of LBA transitions.  The machine has two phases.  In its right-moving phase it may
continue right, turn around without changing the tape, or flip the bit under its head and turn
around.  In its left-moving phase it may continue left or turn around.

Consequently every machine step either preserves the whole tape or changes only the bit at the
old head position.  Conversely, at every tape and every coordinate there is a one-step edge
which flips exactly that coordinate.  Thus, after forgetting the finite control and head
position, this single fixed LBA exposes every edge of every finite Boolean hypercube.
-/

namespace LBA.LocalityHypercube

/-- The two head-sweep phases of the hypercube machine. -/
public inductive Phase where
  | right
  | left
  deriving DecidableEq, Fintype, Repr

/-- A fixed binary LBA which can move across a tape without changing it and can
nondeterministically flip the bit under its head when switching from right to left. -/
public def machine : LBA.Machine Bool Phase where
  transition
    | .right, b =>
        {(.right, b, .right), (.left, b, .stay), (.left, !b, .stay)}
    | .left, b =>
        {(.left, b, .left), (.right, b, .stay)}
  accept := fun _ => false
  initial := .right

/-- The configuration in the right-moving phase with prescribed contents and head position. -/
@[expose]
public def rightCfg {n : ℕ} (contents : Fin (n + 1) → Bool) (head : Fin (n + 1)) :
    DLBA.Cfg Bool Phase n :=
  ⟨.right, ⟨contents, head⟩⟩

/-- The configuration in the left-moving phase with prescribed contents and head position. -/
@[expose]
public def leftCfg {n : ℕ} (contents : Fin (n + 1) → Bool) (head : Fin (n + 1)) :
    DLBA.Cfg Bool Phase n :=
  ⟨.left, ⟨contents, head⟩⟩

/-- A step of the hypercube machine either preserves all tape contents or changes the tape
to the result of flipping exactly the bit at the source head position. -/
public theorem step_contents_eq_or_flip {n : ℕ} {cfg cfg' : DLBA.Cfg Bool Phase n}
    (hstep : LBA.Step machine cfg cfg') :
    cfg'.tape.contents = cfg.tape.contents ∨
      cfg'.tape.contents =
        Function.update cfg.tape.contents cfg.tape.head (!cfg.tape.read) := by
  rcases hstep with ⟨q', a, d, htransition, rfl⟩
  rcases cfg with ⟨q, tape⟩
  cases q <;>
    simp only [machine, Set.mem_insert_iff, Set.mem_singleton_iff] at htransition
  · rcases htransition with htransition | htransition | htransition <;>
      cases htransition <;>
      simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  · rcases htransition with htransition | htransition <;>
      cases htransition <;>
      simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

/-- At every tape and every coordinate, the machine has a one-step edge which flips exactly
that coordinate and changes from the right-moving phase to the left-moving phase. -/
public theorem step_flip {n : ℕ} (contents : Fin (n + 1) → Bool)
    (head : Fin (n + 1)) :
    LBA.Step machine (rightCfg contents head)
      (leftCfg (Function.update contents head (!contents head)) head) := by
  refine ⟨.left, !contents head, .stay, ?_, ?_⟩
  · simp [machine, rightCfg]
  · simp [rightCfg, leftCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

/-- A non-boundary right-moving step preserves the tape and advances the head by one cell. -/
public theorem step_right_succ {n k : ℕ} (contents : Fin (n + 1) → Bool)
    (hk : k < n) :
    LBA.Step machine
      (rightCfg contents ⟨k, by omega⟩)
      (rightCfg contents ⟨k + 1, by omega⟩) := by
  refine ⟨.right, contents ⟨k, by omega⟩, .right, ?_, ?_⟩
  · simp [machine, rightCfg]
  · simp [rightCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hk]

/-- A left-moving step from a positive coordinate preserves the tape and decreases the head
coordinate by one. -/
public theorem step_left_pred {n k : ℕ} (contents : Fin (n + 1) → Bool)
    (hk : k + 1 < n + 1) :
    LBA.Step machine
      (leftCfg contents ⟨k + 1, hk⟩)
      (leftCfg contents ⟨k, by omega⟩) := by
  refine ⟨.left, contents ⟨k + 1, hk⟩, .left, ?_, ?_⟩
  · simp [machine, leftCfg]
  · simp [leftCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

/-- Turning from right-moving to left-moving may preserve both the tape and head position. -/
public theorem step_turn_left {n : ℕ} (contents : Fin (n + 1) → Bool)
    (head : Fin (n + 1)) :
    LBA.Step machine (rightCfg contents head) (leftCfg contents head) := by
  refine ⟨.left, contents head, .stay, ?_, ?_⟩
  · simp [machine, rightCfg]
  · simp [rightCfg, leftCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

/-- Turning from left-moving to right-moving may preserve both the tape and head position. -/
public theorem step_turn_right {n : ℕ} (contents : Fin (n + 1) → Bool)
    (head : Fin (n + 1)) :
    LBA.Step machine (leftCfg contents head) (rightCfg contents head) := by
  refine ⟨.right, contents head, .stay, ?_, ?_⟩
  · simp [machine, leftCfg]
  · simp [rightCfg, leftCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

/-- Starting at coordinate zero in the right-moving phase, the machine can reach every head
coordinate without changing the tape. -/
public theorem reaches_right_from_zero {n k : ℕ} (contents : Fin (n + 1) → Bool)
    (hk : k < n + 1) :
    LBA.Reaches machine
      (rightCfg contents ⟨0, Nat.zero_lt_succ n⟩)
      (rightCfg contents ⟨k, hk⟩) := by
  induction k with
  | zero =>
      exact .refl
  | succ k ih =>
      have hk' : k < n + 1 := by omega
      exact (ih hk').tail (step_right_succ contents (by omega))

/-- In the left-moving phase, the machine can reach coordinate zero from every head coordinate
without changing the tape. -/
public theorem reaches_left_to_zero {n k : ℕ} (contents : Fin (n + 1) → Bool)
    (hk : k < n + 1) :
    LBA.Reaches machine
      (leftCfg contents ⟨k, hk⟩)
      (leftCfg contents ⟨0, Nat.zero_lt_succ n⟩) := by
  induction k with
  | zero =>
      exact .refl
  | succ k ih =>
      have hk' : k < n + 1 := by omega
      exact Relation.ReflTransGen.head (step_left_pred contents hk) (ih hk')

/-- A configuration with an arbitrary phase, prescribed tape contents, and prescribed head. -/
@[expose]
public def phaseCfg {n : ℕ} (phase : Phase) (contents : Fin (n + 1) → Bool)
    (head : Fin (n + 1)) : DLBA.Cfg Bool Phase n :=
  match phase with
  | .right => rightCfg contents head
  | .left => leftCfg contents head

/-- Projecting the tape contents from a fiber representative recovers its fiber label. -/
@[simp]
public theorem phaseCfg_contents {n : ℕ} (phase : Phase)
    (contents : Fin (n + 1) → Bool) (head : Fin (n + 1)) :
    (phaseCfg phase contents head).tape.contents = contents := by
  cases phase <;> rfl

/-- Representatives of two fixed-contents fibers can be equal only when the contents agree.
In particular, fibers carrying distinct Boolean vectors are disjoint. -/
public theorem phaseCfg_eq_imp_contents_eq {n : ℕ}
    {sourceContents targetContents : Fin (n + 1) → Bool}
    {sourcePhase targetPhase : Phase} {sourceHead targetHead : Fin (n + 1)}
    (h :
      phaseCfg sourcePhase sourceContents sourceHead =
        phaseCfg targetPhase targetContents targetHead) :
    sourceContents = targetContents := by
  have hcontents := congrArg (fun cfg => cfg.tape.contents) h
  simpa using hcontents

/-- The two fibers joined by a hypercube edge are disjoint, independently of the chosen
phase and head representatives. -/
public theorem phaseCfg_ne_flipAt {n : ℕ} (contents : Fin (n + 1) → Bool)
    (coordinate : Fin (n + 1)) (sourcePhase targetPhase : Phase)
    (sourceHead targetHead : Fin (n + 1)) :
    phaseCfg sourcePhase contents sourceHead ≠
      phaseCfg targetPhase
        (Function.update contents coordinate (!contents coordinate)) targetHead := by
  intro h
  have hcontents := phaseCfg_eq_imp_contents_eq h
  have hatCoordinate := congrFun hcontents coordinate
  simp at hatCoordinate

/-- For fixed tape contents, all choices of finite-control phase and head position lie in one
strongly connected component of the directed configuration graph. -/
public theorem fixedContents_reaches {n : ℕ} (contents : Fin (n + 1) → Bool)
    (sourcePhase targetPhase : Phase) (sourceHead targetHead : Fin (n + 1)) :
    LBA.Reaches machine
      (phaseCfg sourcePhase contents sourceHead)
      (phaseCfg targetPhase contents targetHead) := by
  have source_to_zero :
      LBA.Reaches machine
        (phaseCfg sourcePhase contents sourceHead)
        (rightCfg contents ⟨0, Nat.zero_lt_succ n⟩) := by
    cases sourcePhase with
    | right =>
        exact Relation.ReflTransGen.head (step_turn_left contents sourceHead)
          ((reaches_left_to_zero contents sourceHead.isLt).tail
            (step_turn_right contents ⟨0, Nat.zero_lt_succ n⟩))
    | left =>
        exact (reaches_left_to_zero contents sourceHead.isLt).tail
          (step_turn_right contents ⟨0, Nat.zero_lt_succ n⟩)
  have zero_to_target :
      LBA.Reaches machine
        (rightCfg contents ⟨0, Nat.zero_lt_succ n⟩)
        (phaseCfg targetPhase contents targetHead) := by
    cases targetPhase with
    | right =>
        exact reaches_right_from_zero contents targetHead.isLt
    | left =>
        exact (reaches_right_from_zero contents targetHead.isLt).tail
          (step_turn_left contents targetHead)
  exact source_to_zero.trans zero_to_target

/-- Every directed edge of the Boolean hypercube is represented between the corresponding
strongly connected fixed-contents fibers.  The source and target phase/head representatives
may be chosen arbitrarily. -/
public theorem hypercubeEdge_reaches {n : ℕ} (contents : Fin (n + 1) → Bool)
    (coordinate : Fin (n + 1)) (sourcePhase targetPhase : Phase)
    (sourceHead targetHead : Fin (n + 1)) :
    LBA.Reaches machine
      (phaseCfg sourcePhase contents sourceHead)
      (phaseCfg targetPhase
        (Function.update contents coordinate (!contents coordinate)) targetHead) := by
  let flipped := Function.update contents coordinate (!contents coordinate)
  have to_coordinate :
      LBA.Reaches machine
        (phaseCfg sourcePhase contents sourceHead)
        (rightCfg contents coordinate) := by
    simpa [phaseCfg] using
      fixedContents_reaches contents sourcePhase .right sourceHead coordinate
  have flip :
      LBA.Step machine (rightCfg contents coordinate) (leftCfg flipped coordinate) := by
    simpa [flipped] using step_flip contents coordinate
  have from_coordinate :
      LBA.Reaches machine
        (leftCfg flipped coordinate)
        (phaseCfg targetPhase flipped targetHead) := by
    simpa [phaseCfg] using
      fixedContents_reaches flipped .left targetPhase coordinate targetHead
  exact (to_coordinate.tail flip).trans from_coordinate

/-- Flipping the same Boolean coordinate twice restores the original tape contents. -/
@[simp]
public theorem flipAt_involutive {n : ℕ} (contents : Fin (n + 1) → Bool)
    (coordinate : Fin (n + 1)) :
    Function.update
        (Function.update contents coordinate (!contents coordinate))
        coordinate
        (!(Function.update contents coordinate (!contents coordinate)) coordinate) =
      contents := by
  funext index
  by_cases hindex : index = coordinate
  · subst index
    simp
  · simp [hindex]

/-- The represented hypercube edge is available in the reverse direction as well. -/
public theorem hypercubeEdge_reverse_reaches {n : ℕ}
    (contents : Fin (n + 1) → Bool) (coordinate : Fin (n + 1))
    (sourcePhase targetPhase : Phase) (sourceHead targetHead : Fin (n + 1)) :
    LBA.Reaches machine
      (phaseCfg sourcePhase
        (Function.update contents coordinate (!contents coordinate)) sourceHead)
      (phaseCfg targetPhase contents targetHead) := by
  let flipped := Function.update contents coordinate (!contents coordinate)
  have h :=
    hypercubeEdge_reaches flipped coordinate sourcePhase targetPhase sourceHead targetHead
  simpa only [flipped, flipAt_involutive] using h

/-- Adjacent Boolean vectors label distinct strongly connected fibers with reachability in both
directions between any chosen pair of representatives. -/
public theorem adjacentFibers_mutuallyReach {n : ℕ}
    (contents : Fin (n + 1) → Bool) (coordinate : Fin (n + 1))
    (sourcePhase targetPhase : Phase) (sourceHead targetHead : Fin (n + 1)) :
    LBA.Reaches machine
        (phaseCfg sourcePhase contents sourceHead)
        (phaseCfg targetPhase
          (Function.update contents coordinate (!contents coordinate)) targetHead) ∧
      LBA.Reaches machine
        (phaseCfg targetPhase
          (Function.update contents coordinate (!contents coordinate)) targetHead)
        (phaseCfg sourcePhase contents sourceHead) :=
  ⟨hypercubeEdge_reaches contents coordinate sourcePhase targetPhase sourceHead targetHead,
    hypercubeEdge_reverse_reaches contents coordinate targetPhase sourcePhase
      targetHead sourceHead⟩

end LBA.LocalityHypercube

end
