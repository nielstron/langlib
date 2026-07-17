module

public import Langlib.Automata.LinearBounded.BoundedDegree
public import Langlib.Automata.LinearBounded.Unambiguous

@[expose]
public section

/-!
# Uniqueness of operational labels for configuration edges

`Step` forgets which transition triple produced a successor configuration.  The short-layer
machine compiler retains that triple in an intermediate control state, so it needs the mild
normal-form condition that one source/target configuration pair has at most one such label.

The incoming-edge serializer already enforces this condition.  At a base state its target state
contains the complete source-side transition tag, while every other phase has a singleton local
transition set.  Consequently the simultaneous `boundedDegree` serializer enforces it as well.
-/

namespace LBA

open Classical

variable {Γ Λ : Type*}

/-- Every configuration edge of `M` has at most one enabled transition-triple witness.  This is
strictly weaker than functionality: different targets may still be reached nondeterministically.
-/
public def Machine.StepLabelInjective (M : Machine Γ Λ) : Prop :=
  ∀ {n : ℕ} (source target : DLBA.Cfg Γ Λ n),
    Subsingleton (M.MoveTo source target)

/-- Under label injectivity, two enabled moves from one configuration with the same successor
are the same labeled move. -/
public theorem Machine.Move.eq_of_stepLabelInjective
    {M : Machine Γ Λ} (hinjective : M.StepLabelInjective)
    {n : ℕ} {source : DLBA.Cfg Γ Λ n}
    (left right : M.Move source) (htarget : left.target = right.target) :
    left = right := by
  let leftTo : M.MoveTo source left.target := ⟨left, rfl⟩
  let rightTo : M.MoveTo source left.target := ⟨right, htarget.symm⟩
  have hto : leftTo = rightTo :=
    (hinjective source left.target).allEq leftTo rightTo
  exact congrArg Subtype.val hto

/-- Tuple-level form of `Move.eq_of_stepLabelInjective`, convenient for transition-table
compilers that store the raw finite move triple in a control state. -/
public theorem Machine.transitionLabel_eq_of_stepLabelInjective
    {M : Machine Γ Λ} (hinjective : M.StepLabelInjective)
    {n : ℕ} {source : DLBA.Cfg Γ Λ n}
    {left right : LBA.Move Γ Λ}
    (hleft : left ∈ M.transition source.state source.tape.read)
    (hright : right ∈ M.transition source.state source.tape.read)
    (htarget :
      (⟨left.1, (source.tape.write left.2.1).moveHead left.2.2⟩ :
        DLBA.Cfg Γ Λ n) =
      ⟨right.1, (source.tape.write right.2.1).moveHead right.2.2⟩) :
    left = right := by
  let leftMove : M.Move source :=
    ⟨left.1, left.2.1, left.2.2, hleft⟩
  let rightMove : M.Move source :=
    ⟨right.1, right.2.1, right.2.2, hright⟩
  have hmoves : leftMove = rightMove :=
    leftMove.eq_of_stepLabelInjective hinjective rightMove htarget
  exact congrArg
    (fun move : M.Move source =>
      (move.nextState, move.write, move.dir)) hmoves

/-- The incoming-edge serializer gives every configuration edge a unique operational label. -/
public theorem Machine.serializeIncoming_stepLabelInjective
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.serializeIncoming.StepLabelInjective := by
  intro n source target
  constructor
  intro left right
  rcases left with ⟨⟨leftState, leftWrite, leftDir, leftEnabled⟩, leftTarget⟩
  rcases right with ⟨⟨rightState, rightWrite, rightDir, rightEnabled⟩, rightTarget⟩
  apply Subtype.ext
  cases source with
  | mk sourceState tape =>
      cases sourceState with
      | base q =>
          simp only [Machine.serializeIncoming] at leftEnabled rightEnabled
          obtain ⟨leftMove, leftMoveEnabled, leftTriple⟩ := leftEnabled
          obtain ⟨rightMove, rightMoveEnabled, rightTriple⟩ := rightEnabled
          simp only [Prod.mk.injEq] at leftTriple rightTriple
          rcases leftTriple with ⟨rfl, rfl, rfl⟩
          rcases rightTriple with ⟨rfl, rfl, rfl⟩
          have htarget :
              (⟨IncomingState.written leftMove.1
                    { source := q
                      old := tape.read
                      written := leftMove.2.1
                      direction := leftMove.2.2 },
                  (tape.write leftMove.2.1).moveHead .stay⟩ :
                DLBA.Cfg Γ (IncomingState Γ Λ) n) =
              ⟨IncomingState.written rightMove.1
                    { source := q
                      old := tape.read
                      written := rightMove.2.1
                      direction := rightMove.2.2 },
                  (tape.write rightMove.2.1).moveHead .stay⟩ :=
            leftTarget.trans rightTarget.symm
          have hstate := congrArg DLBA.Cfg.state htarget
          simp only [IncomingState.written.injEq] at hstate
          rcases hstate with ⟨htargetState, htag⟩
          have hwritten : leftMove.2.1 = rightMove.2.1 :=
            congrArg IncomingTag.written htag
          have hdir : leftMove.2.2 = rightMove.2.2 :=
            congrArg IncomingTag.direction htag
          cases leftMove with
          | mk leftTargetState leftRest =>
              cases leftRest with
              | mk leftWritten leftDirection =>
                  cases rightMove with
                  | mk rightTargetState rightRest =>
                      cases rightRest with
                      | mk rightWritten rightDirection =>
                          simp only at htargetState hwritten hdir
                          subst rightTargetState
                          subst rightWritten
                          subst rightDirection
                          rfl
      | written writtenTarget tag =>
          simp only [Machine.serializeIncoming] at leftEnabled rightEnabled
          by_cases henabled : tape.read = tag.written ∧
              (writtenTarget, tag.written, tag.direction) ∈
                M.transition tag.source tag.old
          · simp only [if_pos henabled, Set.mem_singleton_iff] at leftEnabled rightEnabled
            cases leftEnabled
            cases rightEnabled
            rfl
          · simp at leftEnabled
            exact (henabled (by
              simpa only [DLBA.BoundedTape.read] using leftEnabled.1)).elim
      | arrived arrivedTarget tag =>
          simp only [Machine.serializeIncoming, Set.mem_singleton_iff] at leftEnabled rightEnabled
          cases leftEnabled
          cases rightEnabled
          rfl
      | merge mergeTarget index =>
          simp only [Machine.serializeIncoming] at leftEnabled rightEnabled
          by_cases hnext : index.val + 1 < Fintype.card (IncomingTag Γ Λ)
          · simp only [dif_pos hnext, Set.mem_singleton_iff] at leftEnabled rightEnabled
            cases leftEnabled
            cases rightEnabled
            rfl
          · simp only [dif_neg hnext, Set.mem_singleton_iff] at leftEnabled rightEnabled
            cases leftEnabled
            cases rightEnabled
            rfl

/-- In particular, the simultaneous outgoing/incoming degree serializer has unique labels on
configuration edges. -/
public theorem Machine.boundedDegree_stepLabelInjective
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.boundedDegree.StepLabelInjective :=
  M.binaryBranch.serializeIncoming_stepLabelInjective

end LBA

end
