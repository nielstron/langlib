module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.EnumerationActions
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

@[expose]
public section

/-!
# Synchronous scanners for enumeration actions

The state below combines the constant-memory scanners needed by one canonical enumeration
action.  It carries at most one source-radix successor, one count-radix successor, one
comparison result, and a Boolean conjunction of cell-local checks.
-/

open Classical

namespace CertifiedRowSystem.Complement

/-- Whether the scanner is waiting for its first cell, processing a row, or irrecoverably bad. -/
public inductive EnumerationMode where
  | start
  | scan
  | bad
  deriving DecidableEq, Fintype, Repr

/-- Constant-size accumulator shared by all enumeration actions. -/
public structure EnumerationAccumulator where
  action : ProtocolAction
  overflow : Bool
  found : Bool
  vertexSucc : RowNumeral.CarryState
  countSucc : RowNumeral.CarryState
  comparison : Ordering
  ok : Bool
  deriving DecidableEq, Repr

public noncomputable instance EnumerationAccumulator.instFintype :
    Fintype EnumerationAccumulator := by
  classical
  exact Fintype.ofInjective
    (fun x : EnumerationAccumulator =>
      (x.action, x.overflow, x.found, x.vertexSucc, x.countSucc, x.comparison, x.ok))
    (by
      intro x y h
      cases x
      cases y
      simp_all)

/-- Complete finite-state verifier state for enumeration actions. -/
public structure EnumerationVerifier where
  mode : EnumerationMode
  acc : EnumerationAccumulator
  deriving DecidableEq, Repr

public noncomputable instance EnumerationVerifier.instFintype :
    Fintype EnumerationVerifier := by
  classical
  exact Fintype.ofInjective
    (fun x : EnumerationVerifier => (x.mode, x.acc))
    (by
      intro x y h
      cases x
      cases y
      simp_all)

/-- Dummy accumulator used before the first cell and after rejection. -/
public def initialEnumerationAccumulator : EnumerationAccumulator where
  action := .beginRound
  overflow := false
  found := false
  vertexSucc := .carry
  countSucc := .carry
  comparison := .eq
  ok := true

/-- Initial scanner state. -/
public def enumerationStart : EnumerationVerifier :=
  ⟨.start, initialEnumerationAccumulator⟩

/-- Absorbing bad scanner state. -/
public def enumerationBad : EnumerationVerifier :=
  ⟨.bad, initialEnumerationAccumulator⟩

/-- Initialize an accumulator for an action, using the first cell only to remember which
of the two canonical successor outcomes the target phase claims. -/
public def startEnumerationAccumulator {A : Type*} [Fintype A]
    (action : ProtocolAction) (old new : ProtocolCell A) : EnumerationAccumulator where
  action := action
  overflow := match action with
    | .skipInner => new.phase == .finishOuter
    | .finishOuter => new.phase == .finishRound
    | .finishRound => new.phase == .finalChoose
    | .finalSkip => new.phase == .finalFinish
    | _ => false
  found := action == .finishOuter && old.found
  vertexSucc := .carry
  countSucc := .carry
  comparison := .eq
  ok := true

/-- Cell-local checks for entering an inner scan. -/
public noncomputable def beginRoundLocalOK {A : Type*} [Fintype A]
    [DecidableEq A] (old new : ProtocolCell A) : Bool :=
  decide (old.phase = .roundStart ∧ new.phase = .chooseInner ∧
    old.vertex = new.vertex ∧ old.counter = new.counter ∧ old.found = new.found)

/-- Cell-local checks for skipping an inner vertex.  The successor itself is checked by
the `vertexSucc` component. -/
public noncomputable def skipInnerLocalOK {A : Type*} [Fintype A]
    [DecidableEq A] (overflow : Bool) (old new : ProtocolCell A) : Bool :=
  decide (old.phase = .chooseInner ∧
    new.phase = (if overflow then .finishOuter else .chooseInner) ∧
    old.vertex.source = new.vertex.source ∧ old.vertex.depth = new.vertex.depth ∧
    old.vertex.outer = new.vertex.outer ∧ old.vertex.path = new.vertex.path ∧
    old.vertex.fuel = new.vertex.fuel ∧ old.counter = new.counter ∧
    old.found = new.found)

/-- Cell-local checks for finishing one outer vertex. -/
public noncomputable def finishOuterLocalOK {A : Type*} [Fintype A]
    [Nonempty A] [DecidableEq A] (overflow found : Bool)
    (old new : ProtocolCell A) : Bool :=
  decide (old.phase = .finishOuter ∧
    new.phase = (if overflow then .finishRound else .chooseInner) ∧
    old.vertex.source = new.vertex.source ∧ old.vertex.depth = new.vertex.depth ∧
    old.counter.oldCount = new.counter.oldCount ∧
    old.counter.seenCount = old.counter.oldCount ∧
    new.vertex.inner = (vertexCodec A).zero ∧
    new.counter.seenCount = (countCodec A).zero ∧
    new.vertex.path = (vertexCodec A).zero ∧
    new.vertex.fuel = (vertexCodec A).zero ∧
    new.found = false ∧ old.found = found ∧
    (¬ found → new.counter.newCount = old.counter.newCount))

/-- Cell-local checks at a complete count-round boundary. -/
public noncomputable def finishRoundLocalOK {A : Type*} [Fintype A]
    [Nonempty A] [DecidableEq A] (plateau : Bool)
    (old new : ProtocolCell A) : Bool :=
  decide (old.phase = .finishRound ∧
    new.phase = (if plateau then .finalChoose else .roundStart) ∧
    old.vertex.source = new.vertex.source ∧
    new.counter.newCount = (countCodec A).zero ∧
    new.counter.seenCount = (countCodec A).zero ∧
    new.vertex.outer = (vertexCodec A).zero ∧
    new.vertex.inner = (vertexCodec A).zero ∧
    new.vertex.path = (vertexCodec A).zero ∧
    new.vertex.fuel = (vertexCodec A).zero ∧ new.found = false ∧
    (if plateau then
      new.vertex.depth = old.vertex.depth ∧
        new.counter.oldCount = old.counter.oldCount
    else new.counter.oldCount = old.counter.newCount))

/-- Cell-local checks for skipping a vertex in the final scan. -/
public noncomputable def finalSkipLocalOK {A : Type*} [Fintype A]
    [DecidableEq A] (overflow : Bool) (old new : ProtocolCell A) : Bool :=
  decide (old.phase = .finalChoose ∧
    new.phase = (if overflow then .finalFinish else .finalChoose) ∧
    old.vertex.source = new.vertex.source ∧ old.vertex.depth = new.vertex.depth ∧
    old.vertex.outer = new.vertex.outer ∧ old.vertex.path = new.vertex.path ∧
    old.vertex.fuel = new.vertex.fuel ∧ old.counter = new.counter ∧
    old.found = new.found)

/-- Cell-local checks for the accepting transition after the final scan. -/
public noncomputable def finalFinishLocalOK {A : Type*} [Fintype A]
    [DecidableEq A] (old new : ProtocolCell A) : Bool :=
  decide (old.phase = .finalFinish ∧ new.phase = .accept ∧
    old.counter.seenCount = old.counter.oldCount ∧
    old.vertex.source = new.vertex.source)

/-- Process one cell after an enumeration action has been selected. -/
public noncomputable def scanEnumerationCell {A : Type*} [Fintype A]
    [Nonempty A] [DecidableEq A]
    (acc : EnumerationAccumulator) (old new : ProtocolCell A) : EnumerationAccumulator :=
  match acc.action with
  | .beginRound => { acc with ok := acc.ok && beginRoundLocalOK old new }
  | .skipInner =>
      { acc with
        vertexSucc := (vertexCodec A).succStep acc.vertexSucc old.vertex.inner new.vertex.inner
        ok := acc.ok && skipInnerLocalOK acc.overflow old new }
  | .finishOuter =>
      { acc with
        vertexSucc := (vertexCodec A).succStep acc.vertexSucc old.vertex.outer new.vertex.outer
        countSucc := if acc.found then
            (countCodec A).succStep acc.countSucc old.counter.newCount new.counter.newCount
          else acc.countSucc
        ok := acc.ok && finishOuterLocalOK acc.overflow acc.found old new }
  | .finishRound =>
      { acc with
        vertexSucc := if acc.overflow then acc.vertexSucc else
          (vertexCodec A).succStep acc.vertexSucc old.vertex.depth new.vertex.depth
        comparison := (countCodec A).compareStep acc.comparison
          old.counter.oldCount old.counter.newCount
        ok := acc.ok && finishRoundLocalOK acc.overflow old new }
  | .finalSkip =>
      { acc with
        vertexSucc := (vertexCodec A).succStep acc.vertexSucc old.vertex.inner new.vertex.inner
        ok := acc.ok && finalSkipLocalOK acc.overflow old new }
  | .finalFinish => { acc with ok := acc.ok && finalFinishLocalOK old new }
  | _ => { acc with ok := false }

/-- One cell of the enumeration-action verifier. -/
public noncomputable def enumerationStepCell {A : Type*} [Fintype A]
    [Nonempty A] [DecidableEq A] :
    EnumerationVerifier → ProtocolCell A → ProtocolCell A →
      ProtocolAction → EnumerationVerifier
  | ⟨.bad, _⟩, _, _, _ => enumerationBad
  | ⟨.start, _⟩, old, new, action =>
      let acc := startEnumerationAccumulator action old new
      ⟨.scan, scanEnumerationCell acc old new⟩
  | ⟨.scan, acc⟩, old, new, action =>
      if action = acc.action then ⟨.scan, scanEnumerationCell acc old new⟩
      else enumerationBad

/-- Terminal check for one enumeration action. -/
public def enumerationDone : EnumerationVerifier → Bool
  | ⟨.scan, acc⟩ =>
      acc.ok && match acc.action with
      | .beginRound => true
      | .skipInner => decide
          (acc.vertexSucc = if acc.overflow then .carry else .done)
      | .finishOuter => decide
          (acc.vertexSucc = if acc.overflow then .carry else .done) &&
          (!acc.found || decide (acc.countSucc = .done))
      | .finishRound =>
          decide (acc.comparison = if acc.overflow then .eq else .lt) &&
          (acc.overflow || decide (acc.vertexSucc = .done))
      | .finalSkip => decide
          (acc.vertexSucc = if acc.overflow then .carry else .done)
      | .finalFinish => true
      | _ => false
  | _ => false

/-- Run an enumeration-action scanner over three aligned rows. -/
public noncomputable def evalEnumeration {A : Type*} [Fintype A]
    [Nonempty A] [DecidableEq A] :
    EnumerationVerifier → ProtocolRow A → ProtocolRow A →
      List ProtocolAction → Option EnumerationVerifier
  | q, [], [], [] => some q
  | q, old :: olds, new :: news, action :: actions =>
      evalEnumeration (enumerationStepCell q old new action) olds news actions
  | _, _, _, _ => none

end CertifiedRowSystem.Complement
