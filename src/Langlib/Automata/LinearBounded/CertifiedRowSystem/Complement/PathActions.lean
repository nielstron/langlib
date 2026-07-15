module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Definition
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Determinize
public import Langlib.Automata.LinearBounded.RowEnumeration
import Mathlib.Tactic

@[expose]
public section

/-!
# Path actions for the certified-row complement protocol

These scanners implement the path-witnessing part of inductive counting.  The source
system supplied here has `Unit` certificates; in the complete construction it is the
subset-construction system `CertifiedRowSystem.determinize`.
-/

open Classical

namespace CertifiedRowSystem
namespace Complement

variable {I A Q F : Type*}

/-! ## Small scanner utilities -/

/-- Extend a possibly-unset replicated bit, rejecting a disagreement. -/
public def noteBit : Option Bool → Bool → Option Bool
  | none, bit => some bit
  | some expected, bit => if bit = expected then some expected else none

@[simp] public theorem noteBit_none (bit : Bool) : noteBit none bit = some bit := rfl

/-- Extend a possibly-unset replicated phase, rejecting a disagreement. -/
public def notePhase : Option ProtocolPhase → ProtocolPhase → Option ProtocolPhase
  | none, phase => some phase
  | some expected, phase => if phase = expected then some expected else none

@[simp] public theorem notePhase_none (phase : ProtocolPhase) :
    notePhase none phase = some phase := rfl

/-- Scan a replicated Boolean track. -/
public def scanBits : Option Bool → List Bool → Option Bool
  | q, [] => q
  | q, bit :: bits => scanBits (noteBit q bit) bits

/-- Scan a replicated phase track. -/
public def scanPhases : Option ProtocolPhase → List ProtocolPhase → Option ProtocolPhase
  | q, [] => q
  | q, phase :: phases => scanPhases (notePhase q phase) phases

/-- Equality accumulator for an aligned pair of tracks. -/
public def noteEq [DecidableEq A] (ok : Bool) (old new : A) : Bool :=
  ok && decide (old = new)

/-- Boolean scan of a cell-local relation on two aligned lists. -/
public def checkPairs (p : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | x :: xs, y :: ys => p x y && checkPairs p xs ys
  | _, _ => false

private theorem decide_and_bool (p q : Prop) [Decidable p] [Decidable q] :
    decide (p ∧ q) = (decide p && decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

@[simp]
public theorem checkPairs_eq_true_iff (p : α → β → Bool) (xs : List α) (ys : List β) :
    checkPairs p xs ys = true ↔ List.Forall₂ (fun x y ↦ p x y = true) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [checkPairs]
  | cons x xs ih =>
      cases ys with
      | nil => simp [checkPairs]
      | cons y ys => simp [checkPairs, ih]

/-- Every list of unit certificates is the canonical replicated unit list. -/
public theorem unitList_eq_replicate (cert : List Unit) :
    cert = List.replicate cert.length () := by
  induction cert with
  | nil => rfl
  | cons cert certs ih =>
      have : cert = () := Subsingleton.elim _ _
      subst cert
      rw [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons ()) ih

/-- For a unit-certified system there is only one certificate row of a given length. -/
public theorem rowStep_iff_evalUnit
    (D : CertifiedRowSystem I A Unit Q F) (old new : List A) :
    D.RowStep old new ↔
      ∃ q, D.evalStep D.stepStart old new (List.replicate old.length ()) = some q ∧
        D.stepDone q = true := by
  constructor
  · rintro ⟨cert, q, heval, hdone⟩
    have hlens := D.evalStep_nil_iff heval
    have hcert : cert = List.replicate old.length () := by
      rw [unitList_eq_replicate cert, hlens.2]
    exact ⟨q, by simpa [hcert] using heval, hdone⟩
  · rintro ⟨q, heval, hdone⟩
    exact ⟨List.replicate old.length (), q, heval, hdone⟩

/-- A deterministic unit-certified verifier has a unique run on every aligned pair. -/
public theorem exists_evalStep_unit_of_length
    (D : CertifiedRowSystem I A Unit Q F) (q : Q) (old new : List A)
    (hlen : old.length = new.length) :
    ∃ out, D.evalStep q old new (List.replicate old.length ()) = some out := by
  induction old generalizing q new with
  | nil =>
      have hnew : new = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst new
      exact ⟨q, rfl⟩
  | cons old olds ih =>
      cases new with
      | nil => simp at hlen
      | cons new news =>
          obtain ⟨out, hout⟩ := ih (D.stepCell q old new ()) news (by simpa using hlen)
          exact ⟨out, by simpa [CertifiedRowSystem.evalStep, List.replicate_succ] using hout⟩

/-! ## Starting a path -/

/-- Cell-local part of path initialization.  All persistent tracks are copied, the
path is reset to the immutable source row, and fuel is reset to zero. -/
public noncomputable def startPathLocalOK
    [Fintype A] [Nonempty A] [DecidableEq A]
    (oldPhase newPhase : ProtocolPhase) (old new : ProtocolCell A) : Bool :=
  decide (
    old.phase = oldPhase ∧ new.phase = newPhase ∧
    new.vertex.source = old.vertex.source ∧
    new.vertex.depth = old.vertex.depth ∧
    new.vertex.outer = old.vertex.outer ∧
    new.vertex.inner = old.vertex.inner ∧
    new.vertex.path = old.vertex.source ∧
    new.vertex.fuel = (vertexCodec A).zero ∧
    new.counter.oldCount = old.counter.oldCount ∧
    new.counter.newCount = old.counter.newCount ∧
    new.counter.seenCount = old.counter.seenCount ∧
    new.found = old.found)

/-- State of a path-initialization scan. -/
public abbrev StartPathVerifier := Bool

/-- One cell of a path-initialization scan. -/
public noncomputable def startPathStepCell
    [Fintype A] [Nonempty A] [DecidableEq A]
    (oldPhase newPhase : ProtocolPhase) (ok : StartPathVerifier)
    (old new : ProtocolCell A) : StartPathVerifier :=
  ok && startPathLocalOK oldPhase newPhase old new

/-- Successful terminal state for path initialization. -/
public def startPathDone (q : StartPathVerifier) : Bool := q

/-- Run a path-initialization scanner on aligned protocol rows. -/
public noncomputable def evalStartPath
    [Fintype A] [Nonempty A] [DecidableEq A]
    (oldPhase newPhase : ProtocolPhase) :
    StartPathVerifier → ProtocolRow A → ProtocolRow A → Option StartPathVerifier
  | q, [], [] => some q
  | q, old :: olds, new :: news =>
      evalStartPath oldPhase newPhase
        (startPathStepCell oldPhase newPhase q old new) olds news
  | _, _, _ => none

/-- Exact list-level specification of path initialization. -/
public def StartsPath
    [Fintype A] [Nonempty A] [DecidableEq A]
    (oldPhase newPhase : ProtocolPhase) (old new : ProtocolRow A) : Prop :=
  List.Forall₂
    (fun oldCell newCell ↦
      startPathLocalOK oldPhase newPhase oldCell newCell = true)
    old new

private theorem evalStartPath_done_iff_aux
    [Fintype A] [Nonempty A] [DecidableEq A]
    (oldPhase newPhase : ProtocolPhase) (q : StartPathVerifier)
    (old new : ProtocolRow A) :
    evalStartPath oldPhase newPhase q old new = some true ↔
      q = true ∧ StartsPath oldPhase newPhase old new := by
  induction old generalizing q new with
  | nil => cases new <;> simp [evalStartPath, StartsPath]
  | cons old olds ih =>
      cases new with
      | nil => simp [evalStartPath, StartsPath]
      | cons new news =>
          rw [evalStartPath]
          rw [ih]
          simp only [startPathStepCell, Bool.and_eq_true, StartsPath,
            List.forall₂_cons]
          tauto

/-- The finite scanner accepts exactly the list-level path-initialization relation. -/
public theorem evalStartPath_done_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (oldPhase newPhase : ProtocolPhase) (old new : ProtocolRow A) :
    evalStartPath oldPhase newPhase true old new = some true ↔
      StartsPath oldPhase newPhase old new := by
  simpa using evalStartPath_done_iff_aux oldPhase newPhase true old new

@[simp]
public theorem startPathLocalOK_eq_true_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (oldPhase newPhase : ProtocolPhase) (old new : ProtocolCell A) :
    startPathLocalOK oldPhase newPhase old new = true ↔
      old.phase = oldPhase ∧ new.phase = newPhase ∧
      new.vertex.source = old.vertex.source ∧
      new.vertex.depth = old.vertex.depth ∧
      new.vertex.outer = old.vertex.outer ∧
      new.vertex.inner = old.vertex.inner ∧
      new.vertex.path = old.vertex.source ∧
      new.vertex.fuel = (vertexCodec A).zero ∧
      new.counter.oldCount = old.counter.oldCount ∧
      new.counter.newCount = old.counter.newCount ∧
      new.counter.seenCount = old.counter.seenCount ∧
      new.found = old.found := by
  simp [startPathLocalOK]

/-- Track/phase projection of the list-level path initialization relation. -/
public theorem StartsPath.spec
    [Fintype A] [Nonempty A] [DecidableEq A]
    {oldPhase newPhase : ProtocolPhase} {old new : ProtocolRow A}
    (h : StartsPath oldPhase newPhase old new) :
    old.length = new.length ∧
    HasPhase oldPhase old ∧ HasPhase newPhase new ∧
    sourceTrack new = sourceTrack old ∧
    depthTrack new = depthTrack old ∧
    outerTrack new = outerTrack old ∧
    innerTrack new = innerTrack old ∧
    pathTrack new = sourceTrack old ∧
    fuelTrack new = (vertexCodec A).zeroRow new.length ∧
    oldCountTrack new = oldCountTrack old ∧
    newCountTrack new = newCountTrack old ∧
    seenCountTrack new = seenCountTrack old ∧
    foundTrack new = foundTrack old := by
  change List.Forall₂
    (fun oldCell newCell ↦
      startPathLocalOK oldPhase newPhase oldCell newCell = true) old new at h
  induction h with
  | nil =>
      simp [HasPhase, sourceTrack, depthTrack, outerTrack, innerTrack,
        pathTrack, fuelTrack, oldCountTrack, newCountTrack, seenCountTrack,
        foundTrack, RowNumeral.DigitCodec.zeroRow]
  | cons hcell htail ih =>
      rw [startPathLocalOK_eq_true_iff] at hcell
      rcases hcell with ⟨holdPhase, hnewPhase, hsource, hdepth, houter,
        hinner, hpath, hfuel, holdCount, hnewCount, hseenCount, hfound⟩
      simp only [List.length_cons, HasPhase, List.mem_cons, forall_eq_or_imp,
        sourceTrack, depthTrack, outerTrack, innerTrack, pathTrack, fuelTrack,
        oldCountTrack, newCountTrack, seenCountTrack, foundTrack, List.map_cons,
        RowNumeral.DigitCodec.zeroRow, List.replicate_succ, List.cons.injEq]
      aesop

/-- Ordinary counting-round path initialization. -/
public noncomputable abbrev startPathCell
    [Fintype A] [Nonempty A] [DecidableEq A] :=
  startPathStepCell (A := A) .chooseInner .path

/-- Final-rejection path initialization. -/
public noncomputable abbrev finalStartPathCell
    [Fintype A] [Nonempty A] [DecidableEq A] :=
  startPathStepCell (A := A) .finalChoose .finalPath

/-! ## Extending a bounded path -/

/-- Finite state of the synchronous bounded-path scanner. -/
public structure PathStepVerifier (Q : Type*) where
  sourceState : Q
  samePath : Bool
  fuelSucc : RowNumeral.CarryState
  fuelDepth : Ordering
  localOK : Bool
  deriving DecidableEq

public noncomputable instance PathStepVerifier.instFintype
    [Fintype Q] : Fintype (PathStepVerifier Q) := by
  classical
  exact Fintype.ofInjective
    (fun q : PathStepVerifier Q =>
      (q.sourceState, q.samePath, q.fuelSucc, q.fuelDepth, q.localOK))
    (by intro x y h; cases x; cases y; simp_all)

/-- Initial state for a bounded path-extension scan. -/
public def pathStepStart (D : CertifiedRowSystem I A Unit Q F) : PathStepVerifier Q where
  sourceState := D.stepStart
  samePath := true
  fuelSucc := .carry
  fuelDepth := .eq
  localOK := true

/-- Persistent cell-local conditions of a path extension. -/
public def pathStepLocalOK
    [Fintype A] [DecidableEq A]
    (phase : ProtocolPhase) (old new : ProtocolCell A) : Bool :=
  decide (
    old.phase = phase ∧ new.phase = phase ∧
    new.vertex.source = old.vertex.source ∧
    new.vertex.depth = old.vertex.depth ∧
    new.vertex.outer = old.vertex.outer ∧
    new.vertex.inner = old.vertex.inner ∧
    new.counter.oldCount = old.counter.oldCount ∧
    new.counter.newCount = old.counter.newCount ∧
    new.counter.seenCount = old.counter.seenCount ∧
    new.found = old.found)

@[simp]
public theorem pathStepLocalOK_eq_true_iff
    [Fintype A] [DecidableEq A]
    (phase : ProtocolPhase) (old new : ProtocolCell A) :
    pathStepLocalOK phase old new = true ↔
      old.phase = phase ∧ new.phase = phase ∧
      new.vertex.source = old.vertex.source ∧
      new.vertex.depth = old.vertex.depth ∧
      new.vertex.outer = old.vertex.outer ∧
      new.vertex.inner = old.vertex.inner ∧
      new.counter.oldCount = old.counter.oldCount ∧
      new.counter.newCount = old.counter.newCount ∧
      new.counter.seenCount = old.counter.seenCount ∧
      new.found = old.found := by
  simp [pathStepLocalOK]

/-- One cell of a path extension.  It simultaneously runs the deterministic source
edge verifier, the stuttering check, the fuel successor, and `fuel < depth`. -/
public noncomputable def pathStepCell
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (phase : ProtocolPhase)
    (q : PathStepVerifier Q) (old new : ProtocolCell A) : PathStepVerifier Q where
  sourceState := D.stepCell q.sourceState old.vertex.path new.vertex.path ()
  samePath := noteEq q.samePath old.vertex.path new.vertex.path
  fuelSucc := (vertexCodec A).succStep q.fuelSucc old.vertex.fuel new.vertex.fuel
  fuelDepth := (vertexCodec A).compareStep q.fuelDepth old.vertex.fuel old.vertex.depth
  localOK := q.localOK && pathStepLocalOK phase old new

/-- A path extension succeeds exactly for a proper bounded fuel increment and either
a stutter or a source edge. -/
public def pathStepDone (D : CertifiedRowSystem I A Unit Q F)
    (q : PathStepVerifier Q) : Bool :=
  q.localOK && decide (q.fuelSucc = .done) && decide (q.fuelDepth = .lt) &&
    (q.samePath || D.stepDone q.sourceState)

/-- Run the path-extension scanner on aligned rows. -/
public noncomputable def evalPathStep
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (phase : ProtocolPhase) :
    PathStepVerifier Q → ProtocolRow A → ProtocolRow A →
      Option (PathStepVerifier Q)
  | q, [], [] => some q
  | q, old :: olds, new :: news =>
      evalPathStep D phase (pathStepCell D phase q old new) olds news
  | _, _, _ => none

/-- Exact componentwise behavior of the path-extension scan.  This theorem is the
bridge from the finite product state to the list-level source, counter, comparison,
and preservation checks. -/
public theorem evalPathStep_eq_some_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (phase : ProtocolPhase)
    (q out : PathStepVerifier Q) (old new : ProtocolRow A) :
    evalPathStep D phase q old new = some out ↔
      D.evalStep q.sourceState (pathTrack old) (pathTrack new)
          (List.replicate old.length ()) = some out.sourceState ∧
      out.samePath = (q.samePath && decide (pathTrack old = pathTrack new)) ∧
      (vertexCodec A).evalSucc q.fuelSucc (fuelTrack old) (fuelTrack new) =
        some out.fuelSucc ∧
      (vertexCodec A).evalCompare q.fuelDepth (fuelTrack old) (depthTrack old) =
        some out.fuelDepth ∧
      out.localOK =
        (q.localOK && checkPairs (pathStepLocalOK phase) old new) := by
  induction old generalizing q out new with
  | nil =>
      cases new with
      | nil =>
          cases q
          cases out
          simp [evalPathStep, pathTrack, fuelTrack, depthTrack,
            CertifiedRowSystem.evalStep, RowNumeral.DigitCodec.evalSucc,
            RowNumeral.DigitCodec.evalCompare, checkPairs]
          aesop
      | cons new news => simp [evalPathStep, pathTrack, fuelTrack, depthTrack,
          CertifiedRowSystem.evalStep, RowNumeral.DigitCodec.evalSucc,
          RowNumeral.DigitCodec.evalCompare]
  | cons old olds ih =>
      cases new with
      | nil => simp [evalPathStep, pathTrack, fuelTrack, depthTrack,
          CertifiedRowSystem.evalStep, RowNumeral.DigitCodec.evalSucc,
          RowNumeral.DigitCodec.evalCompare]
      | cons new news =>
          rw [evalPathStep, ih]
          simp only [pathTrack, fuelTrack, depthTrack, List.map_cons,
            List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, RowNumeral.DigitCodec.evalSucc,
            RowNumeral.DigitCodec.evalCompare, pathStepCell, noteEq, checkPairs]
          constructor
          · rintro ⟨hsource, hsame, hsucc, hcompare, hlocal⟩
            refine ⟨hsource, ?_, hsucc, hcompare, ?_⟩
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hsame
            · simpa only [Bool.and_assoc] using hlocal
          · rintro ⟨hsource, hsame, hsucc, hcompare, hlocal⟩
            refine ⟨hsource, ?_, hsucc, hcompare, ?_⟩
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hsame
            · simpa only [Bool.and_assoc] using hlocal

/-- List-level semantics of one bounded path extension. -/
public def IsPathStep
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (phase : ProtocolPhase)
    (old new : ProtocolRow A) : Prop :=
  List.Forall₂
      (fun oldCell newCell ↦ pathStepLocalOK phase oldCell newCell = true)
      old new ∧
    (vertexCodec A).evalSucc .carry (fuelTrack old) (fuelTrack new) = some .done ∧
    (vertexCodec A).compareRows (fuelTrack old) (depthTrack old) = some .lt ∧
    (pathTrack new = pathTrack old ∨ D.RowStep (pathTrack old) (pathTrack new))

/-- Phase and persistent-track projection of a bounded path step. -/
public theorem IsPathStep.persistent_spec
    [Fintype A] [Nonempty A] [DecidableEq A]
    {D : CertifiedRowSystem I A Unit Q F} {phase : ProtocolPhase}
    {old new : ProtocolRow A} (h : IsPathStep D phase old new) :
    old.length = new.length ∧
    HasPhase phase old ∧ HasPhase phase new ∧
    sourceTrack new = sourceTrack old ∧
    depthTrack new = depthTrack old ∧
    outerTrack new = outerTrack old ∧
    innerTrack new = innerTrack old ∧
    oldCountTrack new = oldCountTrack old ∧
    newCountTrack new = newCountTrack old ∧
    seenCountTrack new = seenCountTrack old ∧
    foundTrack new = foundTrack old := by
  rcases h with ⟨hlocal, hsucc, hcompare, hpath⟩
  clear hsucc hcompare hpath
  induction hlocal with
  | nil =>
      simp [HasPhase, sourceTrack, depthTrack, outerTrack, innerTrack,
        oldCountTrack, newCountTrack, seenCountTrack, foundTrack]
  | cons hcell htail ih =>
      rw [pathStepLocalOK_eq_true_iff] at hcell
      rcases hcell with ⟨holdPhase, hnewPhase, hsource, hdepth, houter,
        hinner, holdCount, hnewCount, hseenCount, hfound⟩
      simp only [List.length_cons, HasPhase, List.mem_cons, forall_eq_or_imp,
        sourceTrack, depthTrack, outerTrack, innerTrack, oldCountTrack,
        newCountTrack, seenCountTrack, foundTrack, List.map_cons, List.cons.injEq]
      aesop

/-- The path scanner accepts exactly a persistent, proper fuel increment whose path
component either stutters or follows one determinized source edge. -/
public theorem evalPathStep_done_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (phase : ProtocolPhase)
    (old new : ProtocolRow A) :
    (∃ out, evalPathStep D phase (pathStepStart D) old new = some out ∧
      pathStepDone D out = true) ↔ IsPathStep D phase old new := by
  constructor
  · rintro ⟨out, heval, hdone⟩
    rw [evalPathStep_eq_some_iff] at heval
    rcases heval with ⟨hsource, hsame, hsucc, hcompare, hlocal⟩
    simp only [pathStepDone, Bool.and_eq_true, decide_eq_true_eq] at hdone
    rcases hdone with ⟨⟨⟨hloc, hfuel⟩, hlt⟩, hedge⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show out.localOK = checkPairs (pathStepLocalOK phase) old new by
        simpa [pathStepStart] using hlocal] at hloc
      exact (checkPairs_eq_true_iff _ _ _).1 hloc
    · simpa [pathStepStart] using hsucc.trans (congrArg some hfuel)
    · simpa [RowNumeral.DigitCodec.compareRows, pathStepStart] using
        hcompare.trans (congrArg some hlt)
    · rw [show out.samePath = decide (pathTrack old = pathTrack new) by
        simpa [pathStepStart] using hsame] at hedge
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hedge
      rcases hedge with heq | hedge
      · exact Or.inl heq.symm
      · exact Or.inr ((rowStep_iff_evalUnit D _ _).2
          ⟨out.sourceState, by simpa [pathStepStart, pathTrack] using hsource, hedge⟩)
  · rintro ⟨hlocal, hsucc, hcompare, hpath⟩
    have hlocalBool : checkPairs (pathStepLocalOK phase) old new = true :=
      (checkPairs_eq_true_iff _ _ _).2 hlocal
    obtain ⟨sourceState, hsourceEval, hsourceDone⟩ :
        ∃ sourceState,
          D.evalStep D.stepStart (pathTrack old) (pathTrack new)
              (List.replicate (pathTrack old).length ()) = some sourceState ∧
            (pathTrack new = pathTrack old ∨ D.stepDone sourceState = true) := by
      rcases hpath with hsame | hedge
      · have hlen : (pathTrack old).length = (pathTrack new).length := by
          simpa [pathTrack] using hlocal.length_eq
        obtain ⟨sourceState, hsourceEval⟩ :=
          exists_evalStep_unit_of_length D D.stepStart _ _ hlen
        exact ⟨sourceState, hsourceEval, Or.inl hsame⟩
      · obtain ⟨sourceState, hsourceEval, hsourceDone⟩ :=
          (rowStep_iff_evalUnit D _ _).1 hedge
        exact ⟨sourceState, by simpa using hsourceEval, Or.inr hsourceDone⟩
    let out : PathStepVerifier Q :=
      { sourceState := sourceState
        samePath := decide (pathTrack old = pathTrack new)
        fuelSucc := .done
        fuelDepth := .lt
        localOK := true }
    refine ⟨out, ?_, ?_⟩
    · rw [evalPathStep_eq_some_iff]
      refine ⟨?_, rfl, hsucc, ?_, by simp [out, pathStepStart, hlocalBool]⟩
      · simpa [pathStepStart, pathTrack] using hsourceEval
      · simpa [RowNumeral.DigitCodec.compareRows] using hcompare
    · change pathStepDone D out = true
      rcases hsourceDone with hsame | hdone
      · simp [pathStepDone, out, hsame.symm]
      · simp [pathStepDone, out, hdone]

/-- Counting-round path extension. -/
public noncomputable abbrev countingPathStepCell
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) := pathStepCell D .path

/-- Final-rejection path extension. -/
public noncomputable abbrev finalPathStepCell
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) := pathStepCell D .finalPath

/-! ## Completing a counting-round witness -/

/-- Finite state for completing a reachability witness in a counting round. -/
public structure FinishWitnessVerifier (Q : Type*) where
  edgeState : Q
  pathInner : Bool
  fuelDepth : Bool
  innerOuter : Bool
  seenSucc : RowNumeral.CarryState
  innerSucc : RowNumeral.CarryState
  oldFound : Option Bool
  newFound : Option Bool
  newPhase : Option ProtocolPhase
  localOK : Bool
  deriving DecidableEq

public noncomputable instance FinishWitnessVerifier.instFintype
    [Fintype Q] : Fintype (FinishWitnessVerifier Q) := by
  classical
  exact Fintype.ofInjective
    (fun q : FinishWitnessVerifier Q =>
      (q.edgeState, q.pathInner, q.fuelDepth, q.innerOuter, q.seenSucc,
        q.innerSucc, q.oldFound, q.newFound, q.newPhase, q.localOK))
    (by intro x y h; cases x; cases y; simp_all)

/-- Initial state of the witness-completion scan. -/
public def finishWitnessStart (D : CertifiedRowSystem I A Unit Q F) :
    FinishWitnessVerifier Q where
  edgeState := D.stepStart
  pathInner := true
  fuelDepth := true
  innerOuter := true
  seenSucc := .carry
  innerSucc := .carry
  oldFound := none
  newFound := none
  newPhase := none
  localOK := true

/-- Persistent and reset conditions of counting-round witness completion. -/
public noncomputable def finishWitnessLocalOK
    [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolCell A) : Bool :=
  decide (
    old.phase = .path ∧
    new.vertex.source = old.vertex.source ∧
    new.vertex.depth = old.vertex.depth ∧
    new.vertex.outer = old.vertex.outer ∧
    new.vertex.path = (vertexCodec A).zero ∧
    new.vertex.fuel = (vertexCodec A).zero ∧
    new.counter.oldCount = old.counter.oldCount ∧
    new.counter.newCount = old.counter.newCount)

@[simp]
public theorem finishWitnessLocalOK_eq_true_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolCell A) :
    finishWitnessLocalOK old new = true ↔
      old.phase = .path ∧
      new.vertex.source = old.vertex.source ∧
      new.vertex.depth = old.vertex.depth ∧
      new.vertex.outer = old.vertex.outer ∧
      new.vertex.path = (vertexCodec A).zero ∧
      new.vertex.fuel = (vertexCodec A).zero ∧
      new.counter.oldCount = old.counter.oldCount ∧
      new.counter.newCount = old.counter.newCount := by
  simp [finishWitnessLocalOK]

/-- One cell of witness completion. -/
public noncomputable def finishWitnessCell
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (q : FinishWitnessVerifier Q)
    (old new : ProtocolCell A) : FinishWitnessVerifier Q where
  edgeState := D.stepCell q.edgeState old.vertex.inner old.vertex.outer ()
  pathInner := noteEq q.pathInner old.vertex.path old.vertex.inner
  fuelDepth := noteEq q.fuelDepth old.vertex.fuel old.vertex.depth
  innerOuter := noteEq q.innerOuter old.vertex.inner old.vertex.outer
  seenSucc := (countCodec A).succStep q.seenSucc
    old.counter.seenCount new.counter.seenCount
  innerSucc := (vertexCodec A).succStep q.innerSucc old.vertex.inner new.vertex.inner
  oldFound := noteBit q.oldFound old.found
  newFound := noteBit q.newFound new.found
  newPhase := notePhase q.newPhase new.phase
  localOK := q.localOK && finishWitnessLocalOK old new

/-- Successful witness completion.  The phase is determined by whether advancing the
canonical inner enumeration overflows. -/
public def finishWitnessDone (D : CertifiedRowSystem I A Unit Q F)
    (q : FinishWitnessVerifier Q) : Bool :=
  q.localOK && q.pathInner && q.fuelDepth && decide (q.seenSucc = .done) &&
    decide (
      (q.innerSucc = .done ∧ q.newPhase = some .chooseInner) ∨
      (q.innerSucc = .carry ∧ q.newPhase = some .finishOuter)) &&
    decide (
      ∃ oldFound newFound,
        q.oldFound = some oldFound ∧ q.newFound = some newFound ∧
        newFound = (oldFound || q.innerOuter || D.stepDone q.edgeState))

/-- Run counting-round witness completion on aligned rows. -/
public noncomputable def evalFinishWitness
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) :
    FinishWitnessVerifier Q → ProtocolRow A → ProtocolRow A →
      Option (FinishWitnessVerifier Q)
  | q, [], [] => some q
  | q, old :: olds, new :: news =>
      evalFinishWitness D (finishWitnessCell D q old new) olds news
  | _, _, _ => none

/-- Exact componentwise behavior of counting-round witness completion. -/
public theorem evalFinishWitness_eq_some_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (q out : FinishWitnessVerifier Q)
    (old new : ProtocolRow A) :
    evalFinishWitness D q old new = some out ↔
      D.evalStep q.edgeState (innerTrack old) (outerTrack old)
          (List.replicate old.length ()) = some out.edgeState ∧
      out.pathInner = (q.pathInner && decide (pathTrack old = innerTrack old)) ∧
      out.fuelDepth = (q.fuelDepth && decide (fuelTrack old = depthTrack old)) ∧
      out.innerOuter = (q.innerOuter && decide (innerTrack old = outerTrack old)) ∧
      (countCodec A).evalSucc q.seenSucc (seenCountTrack old) (seenCountTrack new) =
        some out.seenSucc ∧
      (vertexCodec A).evalSucc q.innerSucc (innerTrack old) (innerTrack new) =
        some out.innerSucc ∧
      out.oldFound = scanBits q.oldFound (old.map (·.found)) ∧
      out.newFound = scanBits q.newFound (new.map (·.found)) ∧
      out.newPhase = scanPhases q.newPhase (new.map (·.phase)) ∧
      out.localOK =
        (q.localOK && checkPairs finishWitnessLocalOK old new) := by
  induction old generalizing q out new with
  | nil =>
      cases new with
      | nil =>
          cases q
          cases out
          simp [evalFinishWitness, innerTrack, outerTrack, pathTrack, fuelTrack,
            depthTrack, seenCountTrack, CertifiedRowSystem.evalStep,
            RowNumeral.DigitCodec.evalSucc, scanBits, scanPhases, checkPairs]
          aesop
      | cons new news => simp [evalFinishWitness, innerTrack, outerTrack, pathTrack,
          fuelTrack, depthTrack, seenCountTrack,
          RowNumeral.DigitCodec.evalSucc]
  | cons old olds ih =>
      cases new with
      | nil => simp [evalFinishWitness, innerTrack, outerTrack, pathTrack,
          fuelTrack, depthTrack, seenCountTrack,
          RowNumeral.DigitCodec.evalSucc]
      | cons new news =>
          rw [evalFinishWitness, ih]
          simp only [innerTrack, outerTrack, pathTrack, fuelTrack, depthTrack,
            seenCountTrack, List.map_cons, List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, RowNumeral.DigitCodec.evalSucc,
            finishWitnessCell, noteEq, scanBits, scanPhases, checkPairs]
          constructor
          · rintro ⟨hsource, hpath, hfuel, houter, hseen, hinner,
              holdFound, hnewFound, hphase, hlocal⟩
            refine ⟨hsource, ?_, ?_, ?_, hseen, hinner, holdFound, hnewFound,
              hphase, ?_⟩
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hpath
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hfuel
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using houter
            · simpa only [Bool.and_assoc] using hlocal
          · rintro ⟨hsource, hpath, hfuel, houter, hseen, hinner,
              holdFound, hnewFound, hphase, hlocal⟩
            refine ⟨hsource, ?_, ?_, ?_, hseen, hinner, holdFound, hnewFound,
              hphase, ?_⟩
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hpath
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hfuel
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using houter
            · simpa only [Bool.and_assoc] using hlocal

/-- List-level specification of completing a counting-round reachability witness. -/
public def IsFinishWitness
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) : Prop :=
  ∃ edgeState innerState oldFound newFound newPhase,
    List.Forall₂
        (fun oldCell newCell ↦ finishWitnessLocalOK oldCell newCell = true)
        old new ∧
    D.evalStep D.stepStart (innerTrack old) (outerTrack old)
        (List.replicate old.length ()) = some edgeState ∧
    pathTrack old = innerTrack old ∧
    fuelTrack old = depthTrack old ∧
    (countCodec A).evalSucc .carry (seenCountTrack old) (seenCountTrack new) =
      some .done ∧
    (vertexCodec A).evalSucc .carry (innerTrack old) (innerTrack new) =
      some innerState ∧
    ((innerState = .done ∧ newPhase = .chooseInner) ∨
      (innerState = .carry ∧ newPhase = .finishOuter)) ∧
    scanBits none (old.map (·.found)) = some oldFound ∧
    scanBits none (new.map (·.found)) = some newFound ∧
    scanPhases none (new.map (·.phase)) = some newPhase ∧
    newFound =
      (oldFound || decide (innerTrack old = outerTrack old) || D.stepDone edgeState)

/-- Persistent/reset-track projection of counting-round witness completion. -/
public theorem IsFinishWitness.persistent_spec
    [Fintype A] [Nonempty A] [DecidableEq A]
    {D : CertifiedRowSystem I A Unit Q F} {old new : ProtocolRow A}
    (h : IsFinishWitness D old new) :
    old.length = new.length ∧ HasPhase .path old ∧
    sourceTrack new = sourceTrack old ∧
    depthTrack new = depthTrack old ∧
    outerTrack new = outerTrack old ∧
    pathTrack new = (vertexCodec A).zeroRow new.length ∧
    fuelTrack new = (vertexCodec A).zeroRow new.length ∧
    oldCountTrack new = oldCountTrack old ∧
    newCountTrack new = newCountTrack old := by
  rcases h with ⟨edgeState, innerState, oldFound, newFound, newPhase,
    hlocal, hedge, hpath, hfuel, hseen, hinner, hphase,
    holdFound, hnewFound, hnewPhase, hfound⟩
  clear hedge hpath hfuel hseen hinner hphase holdFound hnewFound hnewPhase hfound
    edgeState innerState oldFound newFound newPhase
  induction hlocal with
  | nil =>
      simp [HasPhase, sourceTrack, depthTrack, outerTrack, pathTrack, fuelTrack,
        oldCountTrack, newCountTrack, RowNumeral.DigitCodec.zeroRow]
  | cons hcell htail ih =>
      rw [finishWitnessLocalOK_eq_true_iff] at hcell
      rcases hcell with ⟨hphase, hsource, hdepth, houter, hpath, hfuel,
        holdCount, hnewCount⟩
      simp only [List.length_cons, HasPhase, List.mem_cons, forall_eq_or_imp,
        sourceTrack, depthTrack, outerTrack, pathTrack, fuelTrack, oldCountTrack,
        newCountTrack, List.map_cons, RowNumeral.DigitCodec.zeroRow,
        List.replicate_succ, List.cons.injEq]
      aesop

/-- The finite scanner accepts exactly the list-level witness-completion action. -/
public theorem evalFinishWitness_done_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    (∃ out, evalFinishWitness D (finishWitnessStart D) old new = some out ∧
      finishWitnessDone D out = true) ↔ IsFinishWitness D old new := by
  constructor
  · rintro ⟨out, heval, hdone⟩
    rw [evalFinishWitness_eq_some_iff] at heval
    rcases heval with ⟨hedge, hpath, hfuel, houter, hseen, hinner,
      holdFound, hnewFound, hphase, hlocalEval⟩
    simp only [finishWitnessDone, Bool.and_eq_true, decide_eq_true_eq] at hdone
    rcases hdone with ⟨⟨⟨⟨⟨hlocalDone, hpathDone⟩, hfuelDone⟩, hseenDone⟩,
      hphaseDone⟩, hfoundDone⟩
    obtain ⟨oldFound, newFound, holdSome, hnewSome, hfound⟩ := hfoundDone
    obtain ⟨newPhase, hphaseSome⟩ : ∃ phase, out.newPhase = some phase := by
      rcases hphaseDone with h | h
      · exact ⟨.chooseInner, h.2⟩
      · exact ⟨.finishOuter, h.2⟩
    refine ⟨out.edgeState, out.innerSucc, oldFound, newFound, newPhase,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show out.localOK = checkPairs finishWitnessLocalOK old new by
        simpa [finishWitnessStart] using hlocalEval] at hlocalDone
      exact (checkPairs_eq_true_iff _ _ _).1 hlocalDone
    · simpa [finishWitnessStart] using hedge
    · rw [show out.pathInner = decide (pathTrack old = innerTrack old) by
        simpa [finishWitnessStart] using hpath] at hpathDone
      exact of_decide_eq_true hpathDone
    · rw [show out.fuelDepth = decide (fuelTrack old = depthTrack old) by
        simpa [finishWitnessStart] using hfuel] at hfuelDone
      exact of_decide_eq_true hfuelDone
    · simpa [finishWitnessStart, hseenDone] using hseen
    · simpa [finishWitnessStart] using hinner
    · rcases hphaseDone with h | h
      · exact Or.inl ⟨h.1, Option.some.inj (hphaseSome.symm.trans h.2)⟩
      · exact Or.inr ⟨h.1, Option.some.inj (hphaseSome.symm.trans h.2)⟩
    · exact holdFound.symm.trans holdSome
    · exact hnewFound.symm.trans hnewSome
    · exact hphase.symm.trans hphaseSome
    · rw [show out.innerOuter = decide (innerTrack old = outerTrack old) by
        simpa [finishWitnessStart] using houter] at hfound
      exact hfound
  · rintro ⟨edgeState, innerState, oldFound, newFound, newPhase,
      hlocal, hedge, hpath, hfuel, hseen, hinner, hphase,
      holdFound, hnewFound, hnewPhase, hfound⟩
    let out : FinishWitnessVerifier Q :=
      { edgeState := edgeState
        pathInner := true
        fuelDepth := true
        innerOuter := decide (innerTrack old = outerTrack old)
        seenSucc := .done
        innerSucc := innerState
        oldFound := some oldFound
        newFound := some newFound
        newPhase := some newPhase
        localOK := true }
    refine ⟨out, ?_, ?_⟩
    · rw [evalFinishWitness_eq_some_iff]
      refine ⟨by simpa [finishWitnessStart] using hedge, ?_, ?_, rfl,
        by simpa [finishWitnessStart] using hseen,
        by simpa [finishWitnessStart] using hinner, ?_, ?_, ?_, ?_⟩
      · simp [out, finishWitnessStart, hpath]
      · simp [out, finishWitnessStart, hfuel]
      · simpa [out, finishWitnessStart] using holdFound.symm
      · simpa [out, finishWitnessStart] using hnewFound.symm
      · simpa [out, finishWitnessStart] using hnewPhase.symm
      · have hlocalBool := (checkPairs_eq_true_iff _ _ _).2 hlocal
        simp [out, finishWitnessStart, hlocalBool]
    · rcases hphase with hphase | hphase
      · simp [finishWitnessDone, out, hphase.1, hphase.2, hfound]
      · simp [finishWitnessDone, out, hphase.1, hphase.2, hfound]

/-! ## Completing a final-rejection witness -/

/-- Finite state for completing one witness in the final all-nonfinal scan. -/
public structure FinalWitnessVerifier (F : Type*) where
  finalState : F
  pathInner : Bool
  fuelDepth : Bool
  seenSucc : RowNumeral.CarryState
  innerSucc : RowNumeral.CarryState
  newPhase : Option ProtocolPhase
  localOK : Bool
  deriving DecidableEq

public noncomputable instance FinalWitnessVerifier.instFintype
    [Fintype F] : Fintype (FinalWitnessVerifier F) := by
  classical
  exact Fintype.ofInjective
    (fun q : FinalWitnessVerifier F =>
      (q.finalState, q.pathInner, q.fuelDepth, q.seenSucc, q.innerSucc,
        q.newPhase, q.localOK))
    (by intro x y h; cases x; cases y; simp_all)

/-- Initial state for final witness completion. -/
public def finalWitnessStart (D : CertifiedRowSystem I A Unit Q F) :
    FinalWitnessVerifier F where
  finalState := D.finalStart
  pathInner := true
  fuelDepth := true
  seenSucc := .carry
  innerSucc := .carry
  newPhase := none
  localOK := true

/-- Persistent/reset conditions for final witness completion. -/
public noncomputable def finalWitnessLocalOK
    [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolCell A) : Bool :=
  decide (
    old.phase = .finalPath ∧
    new.vertex.source = old.vertex.source ∧
    new.vertex.depth = old.vertex.depth ∧
    new.vertex.outer = old.vertex.outer ∧
    new.vertex.path = (vertexCodec A).zero ∧
    new.vertex.fuel = (vertexCodec A).zero ∧
    new.counter.oldCount = old.counter.oldCount ∧
    new.counter.newCount = old.counter.newCount ∧
    new.found = old.found)

@[simp]
public theorem finalWitnessLocalOK_eq_true_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolCell A) :
    finalWitnessLocalOK old new = true ↔
      old.phase = .finalPath ∧
      new.vertex.source = old.vertex.source ∧
      new.vertex.depth = old.vertex.depth ∧
      new.vertex.outer = old.vertex.outer ∧
      new.vertex.path = (vertexCodec A).zero ∧
      new.vertex.fuel = (vertexCodec A).zero ∧
      new.counter.oldCount = old.counter.oldCount ∧
      new.counter.newCount = old.counter.newCount ∧
      new.found = old.found := by
  simp [finalWitnessLocalOK]

/-- One cell of final witness completion. -/
public noncomputable def finalWitnessCell
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (q : FinalWitnessVerifier F)
    (old new : ProtocolCell A) : FinalWitnessVerifier F where
  finalState := D.finalCell q.finalState old.vertex.inner
  pathInner := noteEq q.pathInner old.vertex.path old.vertex.inner
  fuelDepth := noteEq q.fuelDepth old.vertex.fuel old.vertex.depth
  seenSucc := (countCodec A).succStep q.seenSucc
    old.counter.seenCount new.counter.seenCount
  innerSucc := (vertexCodec A).succStep q.innerSucc old.vertex.inner new.vertex.inner
  newPhase := notePhase q.newPhase new.phase
  localOK := q.localOK && finalWitnessLocalOK old new

/-- Successful final witness completion also requires the witnessed source row to be
nonfinal. -/
public def finalWitnessDone (D : CertifiedRowSystem I A Unit Q F)
    (q : FinalWitnessVerifier F) : Bool :=
  q.localOK && q.pathInner && q.fuelDepth && decide (q.seenSucc = .done) &&
    decide (
      (q.innerSucc = .done ∧ q.newPhase = some .finalChoose) ∨
      (q.innerSucc = .carry ∧ q.newPhase = some .finalFinish)) &&
    decide (D.finalDone q.finalState = false)

/-- Run final witness completion on aligned rows. -/
public noncomputable def evalFinalWitness
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) :
    FinalWitnessVerifier F → ProtocolRow A → ProtocolRow A →
      Option (FinalWitnessVerifier F)
  | q, [], [] => some q
  | q, old :: olds, new :: news =>
      evalFinalWitness D (finalWitnessCell D q old new) olds news
  | _, _, _ => none

/-- Exact componentwise behavior of final witness completion. -/
public theorem evalFinalWitness_eq_some_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (q out : FinalWitnessVerifier F)
    (old new : ProtocolRow A) :
    evalFinalWitness D q old new = some out ↔
      D.evalFinal q.finalState (innerTrack old) = out.finalState ∧
      out.pathInner = (q.pathInner && decide (pathTrack old = innerTrack old)) ∧
      out.fuelDepth = (q.fuelDepth && decide (fuelTrack old = depthTrack old)) ∧
      (countCodec A).evalSucc q.seenSucc (seenCountTrack old) (seenCountTrack new) =
        some out.seenSucc ∧
      (vertexCodec A).evalSucc q.innerSucc (innerTrack old) (innerTrack new) =
        some out.innerSucc ∧
      out.newPhase = scanPhases q.newPhase (new.map (·.phase)) ∧
      out.localOK =
        (q.localOK && checkPairs finalWitnessLocalOK old new) := by
  induction old generalizing q out new with
  | nil =>
      cases new with
      | nil =>
          cases q
          cases out
          simp [evalFinalWitness, innerTrack, pathTrack, fuelTrack, depthTrack,
            seenCountTrack, CertifiedRowSystem.evalFinal,
            RowNumeral.DigitCodec.evalSucc, scanPhases, checkPairs]
          aesop
      | cons new news => simp [evalFinalWitness, innerTrack, pathTrack, fuelTrack,
          depthTrack, seenCountTrack, RowNumeral.DigitCodec.evalSucc]
  | cons old olds ih =>
      cases new with
      | nil => simp [evalFinalWitness, innerTrack, pathTrack, fuelTrack,
          depthTrack, seenCountTrack, RowNumeral.DigitCodec.evalSucc]
      | cons new news =>
          rw [evalFinalWitness, ih]
          simp only [innerTrack, pathTrack, fuelTrack, depthTrack, seenCountTrack,
            List.map_cons, CertifiedRowSystem.evalFinal, List.foldl_cons,
            RowNumeral.DigitCodec.evalSucc, finalWitnessCell, noteEq,
            scanPhases, checkPairs]
          constructor
          · rintro ⟨hfinal, hpath, hfuel, hseen, hinner, hphase, hlocal⟩
            refine ⟨hfinal, ?_, ?_, hseen, hinner, hphase, ?_⟩
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hpath
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hfuel
            · simpa only [Bool.and_assoc] using hlocal
          · rintro ⟨hfinal, hpath, hfuel, hseen, hinner, hphase, hlocal⟩
            refine ⟨hfinal, ?_, ?_, hseen, hinner, hphase, ?_⟩
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hpath
            · simpa only [List.cons.injEq, decide_and_bool, Bool.and_assoc] using hfuel
            · simpa only [Bool.and_assoc] using hlocal

/-- List-level specification of completing one final all-nonfinal witness. -/
public def IsFinalWitness
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) : Prop :=
  ∃ finalState innerState newPhase,
    List.Forall₂
        (fun oldCell newCell ↦ finalWitnessLocalOK oldCell newCell = true)
        old new ∧
    D.evalFinal D.finalStart (innerTrack old) = finalState ∧
    pathTrack old = innerTrack old ∧
    fuelTrack old = depthTrack old ∧
    (countCodec A).evalSucc .carry (seenCountTrack old) (seenCountTrack new) =
      some .done ∧
    (vertexCodec A).evalSucc .carry (innerTrack old) (innerTrack new) =
      some innerState ∧
    ((innerState = .done ∧ newPhase = .finalChoose) ∨
      (innerState = .carry ∧ newPhase = .finalFinish)) ∧
    scanPhases none (new.map (·.phase)) = some newPhase ∧
    D.finalDone finalState = false

/-- Persistent/reset-track projection of final witness completion. -/
public theorem IsFinalWitness.persistent_spec
    [Fintype A] [Nonempty A] [DecidableEq A]
    {D : CertifiedRowSystem I A Unit Q F} {old new : ProtocolRow A}
    (h : IsFinalWitness D old new) :
    old.length = new.length ∧ HasPhase .finalPath old ∧
    sourceTrack new = sourceTrack old ∧
    depthTrack new = depthTrack old ∧
    outerTrack new = outerTrack old ∧
    pathTrack new = (vertexCodec A).zeroRow new.length ∧
    fuelTrack new = (vertexCodec A).zeroRow new.length ∧
    oldCountTrack new = oldCountTrack old ∧
    newCountTrack new = newCountTrack old ∧
    foundTrack new = foundTrack old := by
  rcases h with ⟨finalState, innerState, newPhase, hlocal, hfinal,
    hpath, hfuel, hseen, hinner, hphase, hnewPhase, hfinalDone⟩
  clear hfinal hpath hfuel hseen hinner hphase hnewPhase hfinalDone
    finalState innerState newPhase
  induction hlocal with
  | nil =>
      simp [HasPhase, sourceTrack, depthTrack, outerTrack, pathTrack, fuelTrack,
        oldCountTrack, newCountTrack, foundTrack, RowNumeral.DigitCodec.zeroRow]
  | cons hcell htail ih =>
      rw [finalWitnessLocalOK_eq_true_iff] at hcell
      rcases hcell with ⟨hphase, hsource, hdepth, houter, hpath, hfuel,
        holdCount, hnewCount, hfound⟩
      simp only [List.length_cons, HasPhase, List.mem_cons, forall_eq_or_imp,
        sourceTrack, depthTrack, outerTrack, pathTrack, fuelTrack, oldCountTrack,
        newCountTrack, foundTrack, List.map_cons, RowNumeral.DigitCodec.zeroRow,
        List.replicate_succ, List.cons.injEq]
      aesop

/-- The final witness scanner accepts exactly a reachable-row witness whose source
final predicate is false. -/
public theorem evalFinalWitness_done_iff
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    (∃ out, evalFinalWitness D (finalWitnessStart D) old new = some out ∧
      finalWitnessDone D out = true) ↔ IsFinalWitness D old new := by
  constructor
  · rintro ⟨out, heval, hdone⟩
    rw [evalFinalWitness_eq_some_iff] at heval
    rcases heval with ⟨hfinal, hpath, hfuel, hseen, hinner, hphase, hlocalEval⟩
    simp only [finalWitnessDone, Bool.and_eq_true, decide_eq_true_eq] at hdone
    rcases hdone with ⟨⟨⟨⟨⟨hlocalDone, hpathDone⟩, hfuelDone⟩,
      hseenDone⟩, hphaseDone⟩, hfinalDone⟩
    obtain ⟨newPhase, hphaseSome⟩ : ∃ phase, out.newPhase = some phase := by
      rcases hphaseDone with h | h
      · exact ⟨.finalChoose, h.2⟩
      · exact ⟨.finalFinish, h.2⟩
    refine ⟨out.finalState, out.innerSucc, newPhase, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [show out.localOK = checkPairs finalWitnessLocalOK old new by
        simpa [finalWitnessStart] using hlocalEval] at hlocalDone
      exact (checkPairs_eq_true_iff _ _ _).1 hlocalDone
    · simpa [finalWitnessStart] using hfinal
    · rw [show out.pathInner = decide (pathTrack old = innerTrack old) by
        simpa [finalWitnessStart] using hpath] at hpathDone
      exact of_decide_eq_true hpathDone
    · rw [show out.fuelDepth = decide (fuelTrack old = depthTrack old) by
        simpa [finalWitnessStart] using hfuel] at hfuelDone
      exact of_decide_eq_true hfuelDone
    · simpa [finalWitnessStart, hseenDone] using hseen
    · simpa [finalWitnessStart] using hinner
    · rcases hphaseDone with h | h
      · exact Or.inl ⟨h.1, Option.some.inj (hphaseSome.symm.trans h.2)⟩
      · exact Or.inr ⟨h.1, Option.some.inj (hphaseSome.symm.trans h.2)⟩
    · exact hphase.symm.trans hphaseSome
    · exact hfinalDone
  · rintro ⟨finalState, innerState, newPhase, hlocal, hfinal,
      hpath, hfuel, hseen, hinner, hphase, hnewPhase, hfinalDone⟩
    let out : FinalWitnessVerifier F :=
      { finalState := finalState
        pathInner := true
        fuelDepth := true
        seenSucc := .done
        innerSucc := innerState
        newPhase := some newPhase
        localOK := true }
    refine ⟨out, ?_, ?_⟩
    · rw [evalFinalWitness_eq_some_iff]
      refine ⟨by simpa [finalWitnessStart] using hfinal, ?_, ?_,
        by simpa [finalWitnessStart] using hseen,
        by simpa [finalWitnessStart] using hinner, ?_, ?_⟩
      · simp [out, finalWitnessStart, hpath]
      · simp [out, finalWitnessStart, hfuel]
      · simpa [out, finalWitnessStart] using hnewPhase.symm
      · have hlocalBool := (checkPairs_eq_true_iff _ _ _).2 hlocal
        simp [out, finalWitnessStart, hlocalBool]
    · rcases hphase with hphase | hphase
      · simp [finalWitnessDone, out, hphase.1, hphase.2, hfinalDone]
      · simp [finalWitnessDone, out, hphase.1, hphase.2, hfinalDone]

end Complement
end CertifiedRowSystem
