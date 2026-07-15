module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.EnumerationScanners
import Mathlib.Tactic

@[expose]
public section

/-!
# Correctness of the enumeration-action scanners

This file connects the finite-state scanners in `EnumerationScanners.lean` to the
declarative list-level specifications in `EnumerationActions.lean`.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

/-- Acceptance of one action repeated across the complete certificate row. -/
public def EnumerationAccepts (action : ProtocolAction)
    (old new : ProtocolRow A) : Prop :=
  ∃ out, evalEnumeration enumerationStart old new
      (List.replicate old.length action) = some out ∧ enumerationDone out = true

/-- Run an already selected action over aligned row suffixes. -/
private noncomputable def evalEnumerationAccumulator :
    EnumerationAccumulator → ProtocolRow A → ProtocolRow A →
      Option EnumerationAccumulator
  | acc, [], [] => some acc
  | acc, old :: olds, new :: news =>
      evalEnumerationAccumulator (scanEnumerationCell acc old new) olds news
  | _, _, _ => none

@[simp] private theorem scanEnumerationCell_action
    (acc : EnumerationAccumulator) (old new : ProtocolCell A) :
    (scanEnumerationCell acc old new).action = acc.action := by
  cases acc with
  | mk action overflow found vertexSucc countSucc comparison ok =>
      cases action <;> rfl

@[simp] private theorem scanEnumerationCell_overflow
    (acc : EnumerationAccumulator) (old new : ProtocolCell A) :
    (scanEnumerationCell acc old new).overflow = acc.overflow := by
  cases acc with
  | mk action overflow found vertexSucc countSucc comparison ok =>
      cases action <;> rfl

@[simp] private theorem scanEnumerationCell_found
    (acc : EnumerationAccumulator) (old new : ProtocolCell A) :
    (scanEnumerationCell acc old new).found = acc.found := by
  cases acc with
  | mk action overflow found vertexSucc countSucc comparison ok =>
      cases action <;> rfl

private theorem evalEnumeration_scan_replicate
    (acc : EnumerationAccumulator) (old new : ProtocolRow A) :
    evalEnumeration (.mk .scan acc) old new
        (List.replicate old.length acc.action) =
      (evalEnumerationAccumulator acc old new).map fun out => .mk .scan out := by
  induction old generalizing acc new with
  | nil => cases new <;> rfl
  | cons old olds ih =>
      cases new with
      | nil => rfl
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ, evalEnumeration,
            enumerationStepCell, evalEnumerationAccumulator,
            Option.map]
          rw [show acc.action = (scanEnumerationCell acc old new).action by simp]
          exact ih (scanEnumerationCell acc old new) news

private theorem evalEnumeration_start_cons
    (action : ProtocolAction) (old : ProtocolCell A) (olds : ProtocolRow A)
    (new : ProtocolCell A) (news : ProtocolRow A) :
    evalEnumeration enumerationStart (old :: olds) (new :: news)
        (List.replicate (old :: olds).length action) =
      (evalEnumerationAccumulator (startEnumerationAccumulator action old new)
        (old :: olds) (new :: news)).map fun out => .mk .scan out := by
  simp only [List.length_cons, List.replicate_succ, evalEnumeration, enumerationStart,
    enumerationStepCell, evalEnumerationAccumulator, Option.map]
  simpa using evalEnumeration_scan_replicate
    (scanEnumerationCell (startEnumerationAccumulator action old new) old new) olds news

private theorem enumerationAccepts_iff
    (action : ProtocolAction) (old new : ProtocolRow A) :
    EnumerationAccepts action old new ↔
      ∃ oldHead oldTail newHead newTail out,
        old = oldHead :: oldTail ∧ new = newHead :: newTail ∧
        evalEnumerationAccumulator (startEnumerationAccumulator action oldHead newHead)
          old new = some out ∧ enumerationDone (.mk .scan out) = true := by
  cases old with
  | nil =>
      cases new <;>
        simp [EnumerationAccepts, evalEnumeration, enumerationDone, enumerationStart]
  | cons old oldTail =>
      cases new with
      | nil => simp [EnumerationAccepts, evalEnumeration]
      | cons new newTail =>
          rw [EnumerationAccepts, evalEnumeration_start_cons]
          simp

/-- Conjunction of one cell-local Boolean check over two aligned rows. -/
private noncomputable def checkRows
    (check : ProtocolCell A → ProtocolCell A → Bool) :
    ProtocolRow A → ProtocolRow A → Bool
  | [], [] => true
  | old :: olds, new :: news => check old new && checkRows check olds news
  | _, _ => false

private noncomputable def enumerationLocalOK
    (acc : EnumerationAccumulator) (old new : ProtocolCell A) : Bool :=
  match acc.action with
  | .beginRound => beginRoundLocalOK old new
  | .skipInner => skipInnerLocalOK acc.overflow old new
  | .finishOuter => finishOuterLocalOK acc.overflow acc.found old new
  | .finishRound => finishRoundLocalOK acc.overflow old new
  | .finalSkip => finalSkipLocalOK acc.overflow old new
  | .finalFinish => finalFinishLocalOK old new
  | _ => false

@[simp] private theorem scanEnumerationCell_ok
    (acc : EnumerationAccumulator) (old new : ProtocolCell A) :
    (scanEnumerationCell acc old new).ok =
      (acc.ok && enumerationLocalOK acc old new) := by
  cases acc with
  | mk action overflow found vertexSucc countSucc comparison ok =>
      cases action <;> cases ok <;>
        simp [scanEnumerationCell, enumerationLocalOK]

private theorem enumerationLocalOK_scanEnumerationCell
    (acc : EnumerationAccumulator) (old new x y : ProtocolCell A) :
    enumerationLocalOK (scanEnumerationCell acc old new) x y =
      enumerationLocalOK acc x y := by
  cases acc with
  | mk action overflow found vertexSucc countSucc comparison ok =>
      cases action <;> rfl

private theorem evalEnumerationAccumulator_ok
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (h : evalEnumerationAccumulator acc old new = some out) :
    out.ok = (acc.ok && checkRows (enumerationLocalOK acc) old new) := by
  induction old generalizing acc out new with
  | nil =>
      cases new with
      | nil =>
          simp only [evalEnumerationAccumulator, Option.some.injEq] at h
          subst out
          simp [checkRows]
      | cons new news => simp [evalEnumerationAccumulator] at h
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          have hrec := ih (acc := scanEnumerationCell acc old new) h
          calc
            out.ok = ((scanEnumerationCell acc old new).ok &&
                checkRows (enumerationLocalOK (scanEnumerationCell acc old new)) olds news) := hrec
            _ = (acc.ok && checkRows (enumerationLocalOK acc)
                (old :: olds) (new :: news)) := by
              rw [scanEnumerationCell_ok]
              have hlocal :
                  checkRows (enumerationLocalOK (scanEnumerationCell acc old new)) olds news =
                    checkRows (enumerationLocalOK acc) olds news := by
                apply congrArg (fun check => checkRows check olds news)
                funext x y
                exact enumerationLocalOK_scanEnumerationCell acc old new x y
              rw [hlocal]
              simp [checkRows, Bool.and_assoc]

private theorem exists_evalEnumerationAccumulator_iff
    (acc : EnumerationAccumulator) (old new : ProtocolRow A) :
    (∃ out, evalEnumerationAccumulator acc old new = some out) ↔
      old.length = new.length := by
  induction old generalizing acc new with
  | nil => cases new <;> simp [evalEnumerationAccumulator]
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator]
      | cons new news =>
          simpa [evalEnumerationAccumulator] using
            ih (scanEnumerationCell acc old new) news

private theorem evalEnumerationAccumulator_action
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (h : evalEnumerationAccumulator acc old new = some out) :
    out.action = acc.action := by
  induction old generalizing acc out new with
  | nil =>
      cases new <;> simp [evalEnumerationAccumulator] at h
      subst out
      rfl
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          exact (ih h).trans (scanEnumerationCell_action acc old new)

private theorem evalEnumerationAccumulator_overflow
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (h : evalEnumerationAccumulator acc old new = some out) :
    out.overflow = acc.overflow := by
  induction old generalizing acc out new with
  | nil =>
      cases new <;> simp [evalEnumerationAccumulator] at h
      subst out
      rfl
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          exact (ih h).trans (scanEnumerationCell_overflow acc old new)

private theorem evalEnumerationAccumulator_found
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (h : evalEnumerationAccumulator acc old new = some out) :
    out.found = acc.found := by
  induction old generalizing acc out new with
  | nil =>
      cases new <;> simp [evalEnumerationAccumulator] at h
      subst out
      rfl
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          exact (ih h).trans (scanEnumerationCell_found acc old new)

private theorem checkRows_beginRound_iff (old new : ProtocolRow A) :
    checkRows (fun x y => beginRoundLocalOK x y) old new = true ↔
      BeginRoundSpec old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp [checkRows, BeginRoundSpec, CopiesPayload, HasPhase, sourceTrack,
          depthTrack, oldCountTrack, newCountTrack, seenCountTrack, outerTrack,
          innerTrack, pathTrack, fuelTrack, foundTrack]
  | cons old olds ih =>
      cases new with
      | nil =>
          simp [checkRows, BeginRoundSpec, CopiesPayload, HasPhase, sourceTrack,
            depthTrack, oldCountTrack, newCountTrack, seenCountTrack, outerTrack,
            innerTrack, pathTrack, fuelTrack, foundTrack]
      | cons new news =>
          simp only [checkRows, Bool.and_eq_true]
          rw [ih news]
          rcases old with ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          simp [beginRoundLocalOK, BeginRoundSpec, CopiesPayload,
            HasPhase, sourceTrack, depthTrack, oldCountTrack, newCountTrack,
            seenCountTrack, outerTrack, innerTrack, pathTrack, fuelTrack,
            foundTrack] <;> aesop

private def SkipInnerLocalSpec (overflow : Bool) (old new : ProtocolRow A) : Prop :=
  HasPhase .chooseInner old ∧
  HasPhase (if overflow then .finishOuter else .chooseInner) new ∧
  sourceTrack new = sourceTrack old ∧
  depthTrack new = depthTrack old ∧
  oldCountTrack new = oldCountTrack old ∧
  newCountTrack new = newCountTrack old ∧
  seenCountTrack new = seenCountTrack old ∧
  outerTrack new = outerTrack old ∧
  pathTrack new = pathTrack old ∧
  fuelTrack new = fuelTrack old ∧
  foundTrack new = foundTrack old

private theorem hasPhase_if_iff (flag : Bool) (yes no : ProtocolPhase)
    (row : ProtocolRow A) :
    HasPhase (if flag then yes else no) row ↔
      (if flag then HasPhase yes row else HasPhase no row) := by
  cases flag <;> rfl

private theorem checkRows_skipInner_iff (overflow : Bool) (old new : ProtocolRow A) :
    checkRows (fun x y => skipInnerLocalOK overflow x y) old new = true ↔
      SkipInnerLocalSpec overflow old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp [checkRows, SkipInnerLocalSpec, HasPhase, sourceTrack, depthTrack,
          oldCountTrack, newCountTrack, seenCountTrack, outerTrack, pathTrack,
          fuelTrack, foundTrack]
  | cons old olds ih =>
      cases new with
      | nil =>
          simp [checkRows, SkipInnerLocalSpec, HasPhase, sourceTrack, depthTrack,
            oldCountTrack, newCountTrack, seenCountTrack, outerTrack, pathTrack,
            fuelTrack, foundTrack]
      | cons new news =>
          simp only [checkRows, Bool.and_eq_true]
          rw [ih news]
          rcases old with ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          cases overflow <;>
            simp [skipInnerLocalOK, SkipInnerLocalSpec, HasPhase, sourceTrack,
              depthTrack, oldCountTrack, newCountTrack, seenCountTrack, outerTrack,
              pathTrack, fuelTrack, foundTrack] <;> aesop

private def FinishOuterLocalSpec (overflow found : Bool)
    (old new : ProtocolRow A) : Prop :=
  HasPhase .finishOuter old ∧
  HasPhase (if overflow then .finishRound else .chooseInner) new ∧
  seenCountTrack old = oldCountTrack old ∧
  sourceTrack new = sourceTrack old ∧
  depthTrack new = depthTrack old ∧
  oldCountTrack new = oldCountTrack old ∧
  OuterResetSpec old new ∧
  HasFound found old ∧
  (¬ found → newCountTrack new = newCountTrack old)

private theorem checkRows_finishOuter_iff (overflow found : Bool)
    (old new : ProtocolRow A) :
    checkRows (fun x y => finishOuterLocalOK overflow found x y) old new = true ↔
      FinishOuterLocalSpec overflow found old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp [checkRows, FinishOuterLocalSpec, OuterResetSpec, HasPhase, HasFound,
          sourceTrack, depthTrack, oldCountTrack, newCountTrack, seenCountTrack,
          innerTrack, pathTrack, fuelTrack, RowNumeral.DigitCodec.zeroRow]
  | cons old olds ih =>
      cases new with
      | nil =>
          simp [checkRows, FinishOuterLocalSpec, OuterResetSpec, HasPhase, HasFound,
            sourceTrack, depthTrack, oldCountTrack, newCountTrack, seenCountTrack,
            innerTrack, pathTrack, fuelTrack, RowNumeral.DigitCodec.zeroRow]
      | cons new news =>
          simp only [checkRows, Bool.and_eq_true]
          rw [ih news]
          rcases old with ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          cases overflow <;> cases found <;>
            simp [finishOuterLocalOK, FinishOuterLocalSpec, OuterResetSpec,
              HasPhase, HasFound, sourceTrack, depthTrack, oldCountTrack,
              newCountTrack, seenCountTrack, innerTrack, pathTrack, fuelTrack,
              RowNumeral.DigitCodec.zeroRow, List.replicate_succ] <;>
            aesop

private def FinishRoundLocalSpec (plateau : Bool) (old new : ProtocolRow A) : Prop :=
  HasPhase .finishRound old ∧
  HasPhase (if plateau then .finalChoose else .roundStart) new ∧
  sourceTrack new = sourceTrack old ∧
  RoundResetSpec new ∧
  (if plateau then
      depthTrack new = depthTrack old ∧ oldCountTrack new = oldCountTrack old
    else oldCountTrack new = newCountTrack old)

private theorem checkRows_finishRound_iff (plateau : Bool)
    (old new : ProtocolRow A) :
    checkRows (fun x y => finishRoundLocalOK plateau x y) old new = true ↔
      FinishRoundLocalSpec plateau old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp [checkRows, FinishRoundLocalSpec, RoundResetSpec, HasPhase, HasFound,
          sourceTrack, depthTrack, oldCountTrack, newCountTrack, seenCountTrack,
          outerTrack, innerTrack, pathTrack, fuelTrack,
          RowNumeral.DigitCodec.zeroRow]
  | cons old olds ih =>
      cases new with
      | nil =>
          simp [checkRows, FinishRoundLocalSpec, RoundResetSpec, HasPhase, HasFound,
            sourceTrack, depthTrack, oldCountTrack, newCountTrack, seenCountTrack,
            outerTrack, innerTrack, pathTrack, fuelTrack,
            RowNumeral.DigitCodec.zeroRow]
      | cons new news =>
          simp only [checkRows, Bool.and_eq_true]
          rw [ih news]
          rcases old with ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          cases plateau <;>
            simp [finishRoundLocalOK, FinishRoundLocalSpec, RoundResetSpec,
              HasPhase, HasFound, sourceTrack, depthTrack, oldCountTrack,
              newCountTrack, seenCountTrack, outerTrack, innerTrack, pathTrack,
              fuelTrack, RowNumeral.DigitCodec.zeroRow, List.replicate_succ] <;> aesop

private def FinalSkipLocalSpec (overflow : Bool) (old new : ProtocolRow A) : Prop :=
  HasPhase .finalChoose old ∧
  HasPhase (if overflow then .finalFinish else .finalChoose) new ∧
  sourceTrack new = sourceTrack old ∧
  depthTrack new = depthTrack old ∧
  oldCountTrack new = oldCountTrack old ∧
  newCountTrack new = newCountTrack old ∧
  seenCountTrack new = seenCountTrack old ∧
  outerTrack new = outerTrack old ∧
  pathTrack new = pathTrack old ∧
  fuelTrack new = fuelTrack old ∧
  foundTrack new = foundTrack old

private theorem checkRows_finalSkip_iff (overflow : Bool) (old new : ProtocolRow A) :
    checkRows (fun x y => finalSkipLocalOK overflow x y) old new = true ↔
      FinalSkipLocalSpec overflow old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp [checkRows, FinalSkipLocalSpec, HasPhase, sourceTrack, depthTrack,
          oldCountTrack, newCountTrack, seenCountTrack, outerTrack, pathTrack,
          fuelTrack, foundTrack]
  | cons old olds ih =>
      cases new with
      | nil =>
          simp [checkRows, FinalSkipLocalSpec, HasPhase, sourceTrack, depthTrack,
            oldCountTrack, newCountTrack, seenCountTrack, outerTrack, pathTrack,
            fuelTrack, foundTrack]
      | cons new news =>
          simp only [checkRows, Bool.and_eq_true]
          rw [ih news]
          rcases old with ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          cases overflow <;>
            simp [finalSkipLocalOK, FinalSkipLocalSpec, HasPhase, sourceTrack,
              depthTrack, oldCountTrack, newCountTrack, seenCountTrack, outerTrack,
              pathTrack, fuelTrack, foundTrack] <;> aesop

private theorem checkRows_finalFinish_iff (old new : ProtocolRow A) :
    checkRows (fun x y => finalFinishLocalOK x y) old new = true ↔
      FinalFinishSpec old new := by
  induction old generalizing new with
  | nil =>
      cases new <;>
        simp [checkRows, FinalFinishSpec, HasPhase, sourceTrack, oldCountTrack,
          seenCountTrack]
  | cons old olds ih =>
      cases new with
      | nil =>
          simp [checkRows, FinalFinishSpec, HasPhase, sourceTrack, oldCountTrack,
            seenCountTrack]
      | cons new news =>
          simp only [checkRows, Bool.and_eq_true]
          rw [ih news]
          rcases old with ⟨⟨os, od, oo, oi, op, ofu⟩, ⟨oc, onc, osc⟩, ob, oph⟩
          rcases new with ⟨⟨ns, nd, no, ni, np, nfu⟩, ⟨nc, nnc, nsc⟩, nb, nph⟩
          simp [finalFinishLocalOK, FinalFinishSpec, HasPhase, sourceTrack,
            oldCountTrack, seenCountTrack] <;> aesop

private theorem evalEnumerationAccumulator_innerSucc
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (haction : acc.action = .skipInner ∨ acc.action = .finalSkip)
    (h : evalEnumerationAccumulator acc old new = some out) :
    (vertexCodec A).evalSucc acc.vertexSucc (innerTrack old) (innerTrack new) =
      some out.vertexSucc := by
  induction old generalizing acc out new with
  | nil =>
      cases new with
      | nil =>
          simp only [evalEnumerationAccumulator, Option.some.injEq] at h
          subst out
          rfl
      | cons new news => simp [evalEnumerationAccumulator] at h
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          have haction' :
              (scanEnumerationCell acc old new).action = .skipInner ∨
                (scanEnumerationCell acc old new).action = .finalSkip := by
            simpa using haction
          have hrec := ih haction' h
          rcases haction with hskip | hfinal
          · simpa [innerTrack, RowNumeral.DigitCodec.evalSucc,
              scanEnumerationCell, hskip] using hrec
          · simpa [innerTrack, RowNumeral.DigitCodec.evalSucc,
              scanEnumerationCell, hfinal] using hrec

private theorem evalEnumerationAccumulator_outerSucc
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (haction : acc.action = .finishOuter)
    (h : evalEnumerationAccumulator acc old new = some out) :
    (vertexCodec A).evalSucc acc.vertexSucc (outerTrack old) (outerTrack new) =
      some out.vertexSucc := by
  induction old generalizing acc out new with
  | nil =>
      cases new with
      | nil =>
          simp only [evalEnumerationAccumulator, Option.some.injEq] at h
          subst out
          rfl
      | cons new news => simp [evalEnumerationAccumulator] at h
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          have hrec := ih (by simpa using haction) h
          simpa [outerTrack, RowNumeral.DigitCodec.evalSucc,
            scanEnumerationCell, haction] using hrec

private theorem evalEnumerationAccumulator_countSucc
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (haction : acc.action = .finishOuter) (hfound : acc.found = true)
    (h : evalEnumerationAccumulator acc old new = some out) :
    (countCodec A).evalSucc acc.countSucc (newCountTrack old) (newCountTrack new) =
      some out.countSucc := by
  induction old generalizing acc out new with
  | nil =>
      cases new with
      | nil =>
          simp only [evalEnumerationAccumulator, Option.some.injEq] at h
          subst out
          rfl
      | cons new news => simp [evalEnumerationAccumulator] at h
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          have hrec := ih (by simpa using haction) (by simpa using hfound) h
          simpa [newCountTrack, RowNumeral.DigitCodec.evalSucc,
            scanEnumerationCell, haction, hfound] using hrec

private theorem evalEnumerationAccumulator_depthSucc
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (haction : acc.action = .finishRound) (hplateau : acc.overflow = false)
    (h : evalEnumerationAccumulator acc old new = some out) :
    (vertexCodec A).evalSucc acc.vertexSucc (depthTrack old) (depthTrack new) =
      some out.vertexSucc := by
  induction old generalizing acc out new with
  | nil =>
      cases new with
      | nil =>
          simp only [evalEnumerationAccumulator, Option.some.injEq] at h
          subst out
          rfl
      | cons new news => simp [evalEnumerationAccumulator] at h
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          have hrec := ih (by simpa using haction) (by simpa using hplateau) h
          simpa [depthTrack, RowNumeral.DigitCodec.evalSucc,
            scanEnumerationCell, haction, hplateau] using hrec

private theorem evalEnumerationAccumulator_comparison
    {acc out : EnumerationAccumulator} {old new : ProtocolRow A}
    (haction : acc.action = .finishRound)
    (h : evalEnumerationAccumulator acc old new = some out) :
    (countCodec A).evalCompare acc.comparison
        (oldCountTrack old) (newCountTrack old) = some out.comparison := by
  induction old generalizing acc out new with
  | nil =>
      cases new with
      | nil =>
          simp only [evalEnumerationAccumulator, Option.some.injEq] at h
          subst out
          rfl
      | cons new news => simp [evalEnumerationAccumulator] at h
  | cons old olds ih =>
      cases new with
      | nil => simp [evalEnumerationAccumulator] at h
      | cons new news =>
          have hrec := ih (by simpa using haction) h
          simpa [oldCountTrack, newCountTrack, RowNumeral.DigitCodec.evalCompare,
            scanEnumerationCell, haction] using hrec

private theorem length_eq_of_sourceTrack_eq {old new : ProtocolRow A}
    (h : sourceTrack new = sourceTrack old) : old.length = new.length := by
  have := congrArg List.length h
  simpa [sourceTrack] using this.symm

private theorem evalSucc_terminal_iff {D : Type*} [Fintype D] [Nonempty D]
    [DecidableEq D] (E : RowNumeral.DigitCodec D) (overflow : Bool)
    (old new : List D) :
    E.evalSucc .carry old new = some (if overflow then .carry else .done) ↔
      new = E.nextRow old ∧ (E.increment old).2 = overflow := by
  cases overflow <;>
    simp [RowNumeral.DigitCodec.evalSucc_eq_done_iff,
      RowNumeral.DigitCodec.evalSucc_eq_carry_iff,
      RowNumeral.DigitCodec.nextRow]

private theorem compareStep_eq_eq_iff {D : Type*} [Fintype D] [Nonempty D]
    (E : RowNumeral.DigitCodec D) (q : Ordering) (x y : D) :
    E.compareStep q x y = .eq ↔ x = y ∧ q = .eq := by
  rcases lt_trichotomy (E.digitValue x) (E.digitValue y) with hlt | heq | hgt
  · have hxy : x ≠ y := by
      intro h
      subst y
      exact (lt_irrefl _ hlt)
    simp [RowNumeral.DigitCodec.compareStep, Nat.compare_eq_lt.mpr hlt, hxy]
  · have hxy : x = y := E.digitValue_injective heq
    subst y
    simp [RowNumeral.DigitCodec.compareStep]
  · have hxy : x ≠ y := by
      intro h
      subst y
      exact (lt_irrefl _ hgt)
    simp [RowNumeral.DigitCodec.compareStep, Nat.compare_eq_gt.mpr hgt, hxy]

private theorem evalCompare_eq_some_eq_iff {D : Type*} [Fintype D] [Nonempty D]
    (E : RowNumeral.DigitCodec D) (q : Ordering) (xs ys : List D) :
    E.evalCompare q xs ys = some .eq ↔ xs = ys ∧ q = .eq := by
  induction xs generalizing q ys with
  | nil =>
      cases ys <;> simp [RowNumeral.DigitCodec.evalCompare]
  | cons x xs ih =>
      cases ys with
      | nil => simp [RowNumeral.DigitCodec.evalCompare]
      | cons y ys =>
          simp only [RowNumeral.DigitCodec.evalCompare, ih,
            compareStep_eq_eq_iff]
          aesop

private theorem compareRows_eq_some_eq_iff {D : Type*} [Fintype D] [Nonempty D]
    (E : RowNumeral.DigitCodec D) (xs ys : List D) :
    E.compareRows xs ys = some .eq ↔ xs = ys := by
  simpa [RowNumeral.DigitCodec.compareRows] using
    (evalCompare_eq_some_eq_iff E .eq xs ys)

/-- Correctness of the transition entering an inner enumeration round. -/
@[simp] public theorem enumerationAccepts_beginRound_iff
    (old new : ProtocolRow A) :
    EnumerationAccepts .beginRound old new ↔ old ≠ [] ∧ BeginRoundSpec old new := by
  rw [enumerationAccepts_iff]
  constructor
  · rintro ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, hdone⟩
    have haction : out.action = .beginRound := by
      simpa [startEnumerationAccumulator] using evalEnumerationAccumulator_action heval
    have houtok : out.ok = true := by
      simpa [enumerationDone, haction] using hdone
    have hok := evalEnumerationAccumulator_ok heval
    have hcheck : checkRows (fun x y => beginRoundLocalOK x y)
        (oldHead :: oldTail) (newHead :: newTail) = true := by
      rw [houtok] at hok
      simpa [startEnumerationAccumulator, enumerationLocalOK] using hok.symm
    exact ⟨by simp, (checkRows_beginRound_iff _ _).1 hcheck⟩
  · rintro ⟨hold, hspec⟩
    cases old with
    | nil => contradiction
    | cons oldHead oldTail =>
        have hlen : (oldHead :: oldTail).length = new.length :=
          length_eq_of_sourceTrack_eq hspec.2.2.1
        cases new with
        | nil => simp at hlen
        | cons newHead newTail =>
            let acc := startEnumerationAccumulator .beginRound oldHead newHead
            obtain ⟨out, heval⟩ :=
              (exists_evalEnumerationAccumulator_iff acc _ _).2 hlen
            have hcheck := (checkRows_beginRound_iff
              (oldHead :: oldTail) (newHead :: newTail)).2 hspec
            have hok := evalEnumerationAccumulator_ok heval
            have houtok : out.ok = true := by
              rw [hok]
              simpa [acc, startEnumerationAccumulator, enumerationLocalOK] using hcheck
            have haction : out.action = .beginRound := by
              simpa [acc, startEnumerationAccumulator] using
                evalEnumerationAccumulator_action heval
            refine ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, ?_⟩
            simp [enumerationDone, haction, houtok]

/-- Correctness of one canonical inner-enumeration successor. -/
@[simp] public theorem enumerationAccepts_skipInner_iff
    (old new : ProtocolRow A) :
    EnumerationAccepts .skipInner old new ↔ old ≠ [] ∧ SkipInnerSpec old new := by
  rw [enumerationAccepts_iff]
  constructor
  · rintro ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, hdone⟩
    let overflow : Bool := newHead.phase == .finishOuter
    let acc := startEnumerationAccumulator .skipInner oldHead newHead
    have haction : out.action = .skipInner := by
      simpa [acc, startEnumerationAccumulator] using evalEnumerationAccumulator_action heval
    have hoverflow : out.overflow = overflow := by
      simpa [acc, overflow, startEnumerationAccumulator] using
        evalEnumerationAccumulator_overflow heval
    have hdone' : out.ok = true ∧
        out.vertexSucc = if overflow then .carry else .done := by
      simpa [enumerationDone, haction, hoverflow] using hdone
    have hok := evalEnumerationAccumulator_ok heval
    have hcheck : checkRows (fun x y => skipInnerLocalOK overflow x y)
        (oldHead :: oldTail) (newHead :: newTail) = true := by
      rw [hdone'.1] at hok
      simpa [acc, overflow, startEnumerationAccumulator, enumerationLocalOK] using hok.symm
    have hlocal := (checkRows_skipInner_iff overflow _ _).1 hcheck
    have hscan := evalEnumerationAccumulator_innerSucc
      (acc := acc) (out := out) (old := oldHead :: oldTail)
      (new := newHead :: newTail) (Or.inl (by simp [acc, startEnumerationAccumulator])) heval
    have hscan' : (vertexCodec A).evalSucc .carry
        (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail)) =
          some out.vertexSucc := by
      simpa [acc, startEnumerationAccumulator] using hscan
    have hinner : innerTrack (newHead :: newTail) =
        (vertexCodec A).nextRow (innerTrack (oldHead :: oldTail)) := by
      cases hover : overflow with
      | false =>
          have hs := ((vertexCodec A).evalSucc_eq_done_iff
            (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail))).1
              (by simpa [hover, hdone'.2] using hscan')
          simpa [RowNumeral.DigitCodec.nextRow] using hs.1
      | true =>
          have hs := ((vertexCodec A).evalSucc_eq_carry_iff
            (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail))).1
              (by simpa [hover, hdone'.2] using hscan')
          simpa [RowNumeral.DigitCodec.nextRow] using hs.1
    have hflag : ((vertexCodec A).increment (innerTrack (oldHead :: oldTail))).2 =
        overflow := by
      cases hover : overflow with
      | false =>
          exact ((vertexCodec A).evalSucc_eq_done_iff _ _).1
            (by simpa [hover, hdone'.2] using hscan') |>.2
      | true =>
          exact ((vertexCodec A).evalSucc_eq_carry_iff _ _).1
            (by simpa [hover, hdone'.2] using hscan') |>.2
    rcases hlocal with
      ⟨hphaseOld, hphaseNew, hsource, hdepth, holdCount, hnewCount, hseen,
        houter, hpath, hfuel, hfound⟩
    refine ⟨by simp, hphaseOld, hsource, hdepth, holdCount, hnewCount, hseen,
      houter, hpath, hfuel, hfound, hinner, ?_⟩
    rw [hflag]
    exact (hasPhase_if_iff overflow .finishOuter .chooseInner _).1 hphaseNew
  · rintro ⟨hold, hspec⟩
    cases old with
    | nil => contradiction
    | cons oldHead oldTail =>
        have hlen : (oldHead :: oldTail).length = new.length :=
          length_eq_of_sourceTrack_eq hspec.2.1
        cases new with
        | nil => simp at hlen
        | cons newHead newTail =>
            let overflow := ((vertexCodec A).increment
              (innerTrack (oldHead :: oldTail))).2
            have hlocal : SkipInnerLocalSpec overflow
                (oldHead :: oldTail) (newHead :: newTail) := by
              rcases hspec with
                ⟨hphaseOld, hsource, hdepth, holdCount, hnewCount, hseen,
                  houter, hpath, hfuel, hfound, hinner, hphaseNew⟩
              refine ⟨hphaseOld, ?_, hsource, hdepth, holdCount, hnewCount,
                hseen, houter, hpath, hfuel, hfound⟩
              apply (hasPhase_if_iff overflow .finishOuter .chooseInner _).2
              simpa [overflow] using hphaseNew
            have hoverflowHead : (newHead.phase == .finishOuter) = overflow := by
              have hphase := hlocal.2.1 newHead (by simp)
              cases hover : overflow <;> simp [hover] at hphase ⊢ <;> simp [hphase]
            let acc := startEnumerationAccumulator .skipInner oldHead newHead
            obtain ⟨out, heval⟩ :=
              (exists_evalEnumerationAccumulator_iff acc _ _).2 hlen
            have hcheck := (checkRows_skipInner_iff overflow _ _).2 hlocal
            have hok := evalEnumerationAccumulator_ok heval
            have houtok : out.ok = true := by
              rw [hok]
              simpa [acc, startEnumerationAccumulator, enumerationLocalOK,
                hoverflowHead] using hcheck
            have haction : out.action = .skipInner := by
              simpa [acc, startEnumerationAccumulator] using
                evalEnumerationAccumulator_action heval
            have hoverflow : out.overflow = overflow := by
              simpa [acc, startEnumerationAccumulator, hoverflowHead] using
                evalEnumerationAccumulator_overflow heval
            have hscan := evalEnumerationAccumulator_innerSucc
              (acc := acc) (out := out) (old := oldHead :: oldTail)
              (new := newHead :: newTail)
              (Or.inl (by simp [acc, startEnumerationAccumulator])) heval
            have hinner := hspec.2.2.2.2.2.2.2.2.2.2.1
            have hfinalSucc : out.vertexSucc = if overflow then .carry else .done := by
              cases hover : overflow with
              | false =>
                  have hs : (vertexCodec A).evalSucc .carry
                      (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail)) =
                        some .done := ((vertexCodec A).evalSucc_eq_done_iff _ _).2
                    ⟨by simpa [RowNumeral.DigitCodec.nextRow] using hinner,
                      by simpa [overflow] using hover⟩
                  simpa [acc, startEnumerationAccumulator, hover] using
                    Option.some.inj (hscan.symm.trans hs)
              | true =>
                  have hs : (vertexCodec A).evalSucc .carry
                      (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail)) =
                        some .carry := ((vertexCodec A).evalSucc_eq_carry_iff _ _).2
                    ⟨by simpa [RowNumeral.DigitCodec.nextRow] using hinner,
                      by simpa [overflow] using hover⟩
                  simpa [acc, startEnumerationAccumulator, hover] using
                    Option.some.inj (hscan.symm.trans hs)
            refine ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, ?_⟩
            simp [enumerationDone, haction, hoverflow, houtok, hfinalSucc]

/-- Correctness of the accepting transition after the final enumeration. -/
@[simp] public theorem enumerationAccepts_finalFinish_iff
    (old new : ProtocolRow A) :
    EnumerationAccepts .finalFinish old new ↔ old ≠ [] ∧ FinalFinishSpec old new := by
  rw [enumerationAccepts_iff]
  constructor
  · rintro ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, hdone⟩
    have haction : out.action = .finalFinish := by
      simpa [startEnumerationAccumulator] using evalEnumerationAccumulator_action heval
    have houtok : out.ok = true := by
      simpa [enumerationDone, haction] using hdone
    have hok := evalEnumerationAccumulator_ok heval
    have hcheck : checkRows (fun x y => finalFinishLocalOK x y)
        (oldHead :: oldTail) (newHead :: newTail) = true := by
      rw [houtok] at hok
      simpa [startEnumerationAccumulator, enumerationLocalOK] using hok.symm
    exact ⟨by simp, (checkRows_finalFinish_iff _ _).1 hcheck⟩
  · rintro ⟨hold, hspec⟩
    cases old with
    | nil => contradiction
    | cons oldHead oldTail =>
        have hlen : (oldHead :: oldTail).length = new.length :=
          length_eq_of_sourceTrack_eq hspec.2.2.2
        cases new with
        | nil => simp at hlen
        | cons newHead newTail =>
            let acc := startEnumerationAccumulator .finalFinish oldHead newHead
            obtain ⟨out, heval⟩ :=
              (exists_evalEnumerationAccumulator_iff acc _ _).2 hlen
            have hcheck := (checkRows_finalFinish_iff _ _).2 hspec
            have hok := evalEnumerationAccumulator_ok heval
            have houtok : out.ok = true := by
              rw [hok]
              simpa [acc, startEnumerationAccumulator, enumerationLocalOK] using hcheck
            have haction : out.action = .finalFinish := by
              simpa [acc, startEnumerationAccumulator] using
                evalEnumerationAccumulator_action heval
            refine ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, ?_⟩
            simp [enumerationDone, haction, houtok]

/-- Correctness of one canonical successor in the final scan. -/
@[simp] public theorem enumerationAccepts_finalSkip_iff
    (old new : ProtocolRow A) :
    EnumerationAccepts .finalSkip old new ↔ old ≠ [] ∧ FinalSkipSpec old new := by
  rw [enumerationAccepts_iff]
  constructor
  · rintro ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, hdone⟩
    let overflow : Bool := newHead.phase == .finalFinish
    let acc := startEnumerationAccumulator .finalSkip oldHead newHead
    have haction : out.action = .finalSkip := by
      simpa [acc, startEnumerationAccumulator] using evalEnumerationAccumulator_action heval
    have hoverflow : out.overflow = overflow := by
      simpa [acc, overflow, startEnumerationAccumulator] using
        evalEnumerationAccumulator_overflow heval
    have hdone' : out.ok = true ∧
        out.vertexSucc = if overflow then .carry else .done := by
      simpa [enumerationDone, haction, hoverflow] using hdone
    have hok := evalEnumerationAccumulator_ok heval
    have hcheck : checkRows (fun x y => finalSkipLocalOK overflow x y)
        (oldHead :: oldTail) (newHead :: newTail) = true := by
      rw [hdone'.1] at hok
      simpa [acc, overflow, startEnumerationAccumulator, enumerationLocalOK] using hok.symm
    have hlocal := (checkRows_finalSkip_iff overflow _ _).1 hcheck
    have hscan := evalEnumerationAccumulator_innerSucc
      (acc := acc) (out := out) (old := oldHead :: oldTail)
      (new := newHead :: newTail) (Or.inr (by simp [acc, startEnumerationAccumulator])) heval
    have hscan' : (vertexCodec A).evalSucc .carry
        (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail)) =
          some out.vertexSucc := by
      simpa [acc, startEnumerationAccumulator] using hscan
    have hinner : innerTrack (newHead :: newTail) =
        (vertexCodec A).nextRow (innerTrack (oldHead :: oldTail)) := by
      cases hover : overflow with
      | false =>
          have hs := ((vertexCodec A).evalSucc_eq_done_iff
            (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail))).1
              (by simpa [hover, hdone'.2] using hscan')
          simpa [RowNumeral.DigitCodec.nextRow] using hs.1
      | true =>
          have hs := ((vertexCodec A).evalSucc_eq_carry_iff
            (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail))).1
              (by simpa [hover, hdone'.2] using hscan')
          simpa [RowNumeral.DigitCodec.nextRow] using hs.1
    have hflag : ((vertexCodec A).increment (innerTrack (oldHead :: oldTail))).2 =
        overflow := by
      cases hover : overflow with
      | false =>
          exact ((vertexCodec A).evalSucc_eq_done_iff _ _).1
            (by simpa [hover, hdone'.2] using hscan') |>.2
      | true =>
          exact ((vertexCodec A).evalSucc_eq_carry_iff _ _).1
            (by simpa [hover, hdone'.2] using hscan') |>.2
    rcases hlocal with
      ⟨hphaseOld, hphaseNew, hsource, hdepth, holdCount, hnewCount, hseen,
        houter, hpath, hfuel, hfound⟩
    refine ⟨by simp, hphaseOld, hsource, hdepth, holdCount, hnewCount, hseen,
      houter, hpath, hfuel, hfound, hinner, ?_⟩
    rw [hflag]
    exact (hasPhase_if_iff overflow .finalFinish .finalChoose _).1 hphaseNew
  · rintro ⟨hold, hspec⟩
    cases old with
    | nil => contradiction
    | cons oldHead oldTail =>
        have hlen : (oldHead :: oldTail).length = new.length :=
          length_eq_of_sourceTrack_eq hspec.2.1
        cases new with
        | nil => simp at hlen
        | cons newHead newTail =>
            let overflow := ((vertexCodec A).increment
              (innerTrack (oldHead :: oldTail))).2
            have hlocal : FinalSkipLocalSpec overflow
                (oldHead :: oldTail) (newHead :: newTail) := by
              rcases hspec with
                ⟨hphaseOld, hsource, hdepth, holdCount, hnewCount, hseen,
                  houter, hpath, hfuel, hfound, hinner, hphaseNew⟩
              refine ⟨hphaseOld, ?_, hsource, hdepth, holdCount, hnewCount,
                hseen, houter, hpath, hfuel, hfound⟩
              apply (hasPhase_if_iff overflow .finalFinish .finalChoose _).2
              simpa [overflow] using hphaseNew
            have hoverflowHead : (newHead.phase == .finalFinish) = overflow := by
              have hphase := hlocal.2.1 newHead (by simp)
              cases hover : overflow <;> simp [hover] at hphase ⊢ <;> simp [hphase]
            let acc := startEnumerationAccumulator .finalSkip oldHead newHead
            obtain ⟨out, heval⟩ :=
              (exists_evalEnumerationAccumulator_iff acc _ _).2 hlen
            have hcheck := (checkRows_finalSkip_iff overflow _ _).2 hlocal
            have hok := evalEnumerationAccumulator_ok heval
            have houtok : out.ok = true := by
              rw [hok]
              simpa [acc, startEnumerationAccumulator, enumerationLocalOK,
                hoverflowHead] using hcheck
            have haction : out.action = .finalSkip := by
              simpa [acc, startEnumerationAccumulator] using
                evalEnumerationAccumulator_action heval
            have hoverflow : out.overflow = overflow := by
              simpa [acc, startEnumerationAccumulator, hoverflowHead] using
                evalEnumerationAccumulator_overflow heval
            have hscan := evalEnumerationAccumulator_innerSucc
              (acc := acc) (out := out) (old := oldHead :: oldTail)
              (new := newHead :: newTail)
              (Or.inr (by simp [acc, startEnumerationAccumulator])) heval
            have hinner := hspec.2.2.2.2.2.2.2.2.2.2.1
            have hfinalSucc : out.vertexSucc = if overflow then .carry else .done := by
              cases hover : overflow with
              | false =>
                  have hs : (vertexCodec A).evalSucc .carry
                      (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail)) =
                        some .done := ((vertexCodec A).evalSucc_eq_done_iff _ _).2
                    ⟨by simpa [RowNumeral.DigitCodec.nextRow] using hinner,
                      by simpa [overflow] using hover⟩
                  simpa [acc, startEnumerationAccumulator, hover] using
                    Option.some.inj (hscan.symm.trans hs)
              | true =>
                  have hs : (vertexCodec A).evalSucc .carry
                      (innerTrack (oldHead :: oldTail)) (innerTrack (newHead :: newTail)) =
                        some .carry := ((vertexCodec A).evalSucc_eq_carry_iff _ _).2
                    ⟨by simpa [RowNumeral.DigitCodec.nextRow] using hinner,
                      by simpa [overflow] using hover⟩
                  simpa [acc, startEnumerationAccumulator, hover] using
                    Option.some.inj (hscan.symm.trans hs)
            refine ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, ?_⟩
            simp [enumerationDone, haction, hoverflow, houtok, hfinalSucc]

/-- Correctness of classifying one outer vertex and advancing its enumeration. -/
@[simp] public theorem enumerationAccepts_finishOuter_iff
    (old new : ProtocolRow A) :
    EnumerationAccepts .finishOuter old new ↔ old ≠ [] ∧ FinishOuterSpec old new := by
  rw [enumerationAccepts_iff]
  constructor
  · rintro ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, hdone⟩
    let overflow : Bool := newHead.phase == .finishRound
    let found : Bool := oldHead.found
    let acc := startEnumerationAccumulator .finishOuter oldHead newHead
    have haction : out.action = .finishOuter := by
      simpa [acc, startEnumerationAccumulator] using evalEnumerationAccumulator_action heval
    have hoverflow : out.overflow = overflow := by
      simpa [acc, overflow, startEnumerationAccumulator] using
        evalEnumerationAccumulator_overflow heval
    have hfound : out.found = found := by
      simpa [acc, found, startEnumerationAccumulator] using
        evalEnumerationAccumulator_found heval
    have hbase : out.ok = true ∧
        out.vertexSucc = if overflow then .carry else .done := by
      cases hf : found <;>
        simp [enumerationDone, haction, hoverflow, hfound, hf] at hdone <;>
        aesop
    have hok := evalEnumerationAccumulator_ok heval
    have hcheck : checkRows (fun x y => finishOuterLocalOK overflow found x y)
        (oldHead :: oldTail) (newHead :: newTail) = true := by
      rw [hbase.1] at hok
      simpa [acc, overflow, found, startEnumerationAccumulator,
        enumerationLocalOK] using hok.symm
    have hlocal := (checkRows_finishOuter_iff overflow found _ _).1 hcheck
    have houterScan := evalEnumerationAccumulator_outerSucc
      (acc := acc) (out := out) (old := oldHead :: oldTail)
      (new := newHead :: newTail) (by simp [acc, startEnumerationAccumulator]) heval
    have houterTerminal : (vertexCodec A).evalSucc .carry
        (outerTrack (oldHead :: oldTail)) (outerTrack (newHead :: newTail)) =
          some (if overflow then .carry else .done) := by
      rw [← hbase.2]
      simpa [acc, startEnumerationAccumulator] using houterScan
    have houterResult := (evalSucc_terminal_iff (vertexCodec A) overflow _ _).1
      houterTerminal
    rcases hlocal with
      ⟨hphaseOld, hphaseNew, hseen, hsource, hdepth, holdCount, hreset,
        hfoundOld, hcopy⟩
    refine ⟨by simp, hphaseOld, hseen, hsource, hdepth, holdCount,
      houterResult.1, hreset, ?_, ?_⟩
    · cases hf : found
      · exact Or.inr ⟨by simpa [hf] using hfoundOld, hcopy (by simp [hf])⟩
      · have hcountDone : out.countSucc = .done := by
          simp [enumerationDone, haction, hoverflow, hfound, hf] at hdone
          exact hdone.2.2
        have hcountScan := evalEnumerationAccumulator_countSucc
          (acc := acc) (out := out) (old := oldHead :: oldTail)
          (new := newHead :: newTail) (by simp [acc, startEnumerationAccumulator])
          (by simp [acc, found, startEnumerationAccumulator, hf]) heval
        have hcountTerminal : (countCodec A).evalSucc .carry
            (newCountTrack (oldHead :: oldTail)) (newCountTrack (newHead :: newTail)) =
              some .done := by
          rw [← hcountDone]
          simpa [acc, startEnumerationAccumulator] using hcountScan
        have hcount := ((countCodec A).evalSucc_eq_done_iff _ _).1 hcountTerminal
        exact Or.inl ⟨by simpa [hf] using hfoundOld,
          by simpa [RowNumeral.DigitCodec.nextRow] using hcount.1, hcount.2⟩
    · rw [houterResult.2]
      exact (hasPhase_if_iff overflow .finishRound .chooseInner _).1 hphaseNew
  · rintro ⟨hold, hspec⟩
    cases old with
    | nil => contradiction
    | cons oldHead oldTail =>
        have hlen : (oldHead :: oldTail).length = new.length :=
          length_eq_of_sourceTrack_eq hspec.2.2.1
        cases new with
        | nil => simp at hlen
        | cons newHead newTail =>
            let overflow := ((vertexCodec A).increment
              (outerTrack (oldHead :: oldTail))).2
            rcases hspec.2.2.2.2.2.2.2 with hpositive | hnegative
            · let found : Bool := true
              have hlocal : FinishOuterLocalSpec overflow found
                  (oldHead :: oldTail) (newHead :: newTail) := by
                refine ⟨hspec.1, ?_,
                  hspec.2.1, hspec.2.2.1, hspec.2.2.2.1,
                  hspec.2.2.2.2.1, hspec.2.2.2.2.2.2.1, ?_, ?_⟩
                · apply (hasPhase_if_iff overflow .finishRound .chooseInner _).2
                  simpa [overflow] using hspec.2.2.2.2.2.2.2.2
                · simpa [found] using hpositive.1
                · simp [found]
              have hoverflowHead : (newHead.phase == .finishRound) = overflow := by
                have hphase := hlocal.2.1 newHead (by simp)
                cases hover : overflow <;> simp [hover] at hphase ⊢ <;> simp [hphase]
              have hfoundHead : oldHead.found = found :=
                hpositive.1 oldHead (by simp)
              let acc := startEnumerationAccumulator .finishOuter oldHead newHead
              obtain ⟨out, heval⟩ :=
                (exists_evalEnumerationAccumulator_iff acc _ _).2 hlen
              have hcheck := (checkRows_finishOuter_iff overflow found _ _).2 hlocal
              have hok := evalEnumerationAccumulator_ok heval
              have houtok : out.ok = true := by
                rw [hok]
                simpa [acc, found, startEnumerationAccumulator, enumerationLocalOK,
                  hoverflowHead, hfoundHead] using hcheck
              have haction : out.action = .finishOuter := by
                simpa [acc, startEnumerationAccumulator] using
                  evalEnumerationAccumulator_action heval
              have hoverflow : out.overflow = overflow := by
                simpa [acc, startEnumerationAccumulator, hoverflowHead] using
                  evalEnumerationAccumulator_overflow heval
              have hfoundOut : out.found = true := by
                simpa [acc, startEnumerationAccumulator, hfoundHead] using
                  evalEnumerationAccumulator_found heval
              have houterScan := evalEnumerationAccumulator_outerSucc
                (acc := acc) (out := out) (old := oldHead :: oldTail)
                (new := newHead :: newTail) (by simp [acc, startEnumerationAccumulator]) heval
              have houterFinal : out.vertexSucc = if overflow then .carry else .done := by
                have ht := (evalSucc_terminal_iff (vertexCodec A) overflow _ _).2
                  ⟨hspec.2.2.2.2.2.1, rfl⟩
                simpa [acc, startEnumerationAccumulator] using
                  Option.some.inj (houterScan.symm.trans ht)
              have hcountScan := evalEnumerationAccumulator_countSucc
                (acc := acc) (out := out) (old := oldHead :: oldTail)
                (new := newHead :: newTail) (by simp [acc, startEnumerationAccumulator])
                (by simp [acc, found, startEnumerationAccumulator, hfoundHead]) heval
              have hcountDone : out.countSucc = .done := by
                have ht := ((countCodec A).evalSucc_eq_done_iff _ _).2
                  ⟨by simpa [RowNumeral.DigitCodec.nextRow] using hpositive.2.1,
                    hpositive.2.2⟩
                exact Option.some.inj (hcountScan.symm.trans ht)
              refine ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, ?_⟩
              simp [enumerationDone, haction, hoverflow, hfoundOut, houtok,
                houterFinal, hcountDone]
            · let found : Bool := false
              have hlocal : FinishOuterLocalSpec overflow found
                  (oldHead :: oldTail) (newHead :: newTail) := by
                refine ⟨hspec.1, ?_,
                  hspec.2.1, hspec.2.2.1, hspec.2.2.2.1,
                  hspec.2.2.2.2.1, hspec.2.2.2.2.2.2.1, ?_, ?_⟩
                · apply (hasPhase_if_iff overflow .finishRound .chooseInner _).2
                  simpa [overflow] using hspec.2.2.2.2.2.2.2.2
                · simpa [found] using hnegative.1
                · intro
                  exact hnegative.2
              have hoverflowHead : (newHead.phase == .finishRound) = overflow := by
                have hphase := hlocal.2.1 newHead (by simp)
                cases hover : overflow <;> simp [hover] at hphase ⊢ <;> simp [hphase]
              have hfoundHead : oldHead.found = found :=
                hnegative.1 oldHead (by simp)
              let acc := startEnumerationAccumulator .finishOuter oldHead newHead
              obtain ⟨out, heval⟩ :=
                (exists_evalEnumerationAccumulator_iff acc _ _).2 hlen
              have hcheck := (checkRows_finishOuter_iff overflow found _ _).2 hlocal
              have hok := evalEnumerationAccumulator_ok heval
              have houtok : out.ok = true := by
                rw [hok]
                simpa [acc, found, startEnumerationAccumulator, enumerationLocalOK,
                  hoverflowHead, hfoundHead] using hcheck
              have haction : out.action = .finishOuter := by
                simpa [acc, startEnumerationAccumulator] using
                  evalEnumerationAccumulator_action heval
              have hoverflow : out.overflow = overflow := by
                simpa [acc, startEnumerationAccumulator, hoverflowHead] using
                  evalEnumerationAccumulator_overflow heval
              have hfoundOut : out.found = false := by
                simpa [acc, startEnumerationAccumulator, hfoundHead] using
                  evalEnumerationAccumulator_found heval
              have houterScan := evalEnumerationAccumulator_outerSucc
                (acc := acc) (out := out) (old := oldHead :: oldTail)
                (new := newHead :: newTail) (by simp [acc, startEnumerationAccumulator]) heval
              have houterFinal : out.vertexSucc = if overflow then .carry else .done := by
                have ht := (evalSucc_terminal_iff (vertexCodec A) overflow _ _).2
                  ⟨hspec.2.2.2.2.2.1, rfl⟩
                simpa [acc, startEnumerationAccumulator] using
                  Option.some.inj (houterScan.symm.trans ht)
              refine ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, ?_⟩
              simp [enumerationDone, haction, hoverflow, hfoundOut, houtok, houterFinal]

/-- Correctness of the boundary between two counting rounds, including plateau
detection and the non-plateau depth successor. -/
@[simp] public theorem enumerationAccepts_finishRound_iff
    (old new : ProtocolRow A) :
    EnumerationAccepts .finishRound old new ↔ old ≠ [] ∧ FinishRoundSpec old new := by
  rw [enumerationAccepts_iff]
  constructor
  · rintro ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, hdone⟩
    let plateau : Bool := newHead.phase == .finalChoose
    let acc := startEnumerationAccumulator .finishRound oldHead newHead
    have haction : out.action = .finishRound := by
      simpa [acc, startEnumerationAccumulator] using
        evalEnumerationAccumulator_action heval
    have haccPlateau : acc.overflow = plateau := by
      simp [acc, plateau, startEnumerationAccumulator]
    have houtPlateau : out.overflow = plateau :=
      (evalEnumerationAccumulator_overflow heval).trans haccPlateau
    have houtok : out.ok = true := by
      cases hp : plateau <;>
        simp [enumerationDone, haction, houtPlateau, hp] at hdone
      · exact hdone.1
      · exact hdone.1
    have hok := evalEnumerationAccumulator_ok heval
    have hcheck : checkRows (fun x y => finishRoundLocalOK plateau x y)
        (oldHead :: oldTail) (newHead :: newTail) = true := by
      rw [houtok] at hok
      simpa [acc, startEnumerationAccumulator, enumerationLocalOK,
        haccPlateau] using hok.symm
    have hlocal := (checkRows_finishRound_iff plateau _ _).1 hcheck
    have hcomparisonScan : (countCodec A).evalCompare .eq
        (oldCountTrack (oldHead :: oldTail))
        (newCountTrack (oldHead :: oldTail)) = some out.comparison := by
      simpa [acc, startEnumerationAccumulator] using
        (evalEnumerationAccumulator_comparison
          (acc := acc) (out := out) (old := oldHead :: oldTail)
          (new := newHead :: newTail)
          (by simp [acc, startEnumerationAccumulator]) heval)
    rcases hlocal with
      ⟨hphaseOld, hphaseNew, hsource, hreset, hlocalResult⟩
    cases hp : plateau with
    | false =>
        have hcomparisonOut : out.comparison = .lt := by
          simp [enumerationDone, haction, houtPlateau, hp] at hdone
          exact hdone.2.1
        have hvertexDone : out.vertexSucc = .done := by
          simp [enumerationDone, haction, houtPlateau, hp] at hdone
          exact hdone.2.2
        have hless : (countCodec A).rowsLess
            (oldCountTrack (oldHead :: oldTail))
            (newCountTrack (oldHead :: oldTail)) := by
          simp [RowNumeral.DigitCodec.rowsLess,
            RowNumeral.DigitCodec.compareRows, hcomparisonScan, hcomparisonOut]
        have hdepthScan := evalEnumerationAccumulator_depthSucc
          (acc := acc) (out := out) (old := oldHead :: oldTail)
          (new := newHead :: newTail)
          (by simp [acc, startEnumerationAccumulator])
          (haccPlateau.trans hp) heval
        have hdepthTerminal : (vertexCodec A).evalSucc .carry
            (depthTrack (oldHead :: oldTail))
            (depthTrack (newHead :: newTail)) = some .done := by
          rw [← hvertexDone]
          simpa [acc, startEnumerationAccumulator] using hdepthScan
        have hdepth := ((vertexCodec A).evalSucc_eq_done_iff _ _).1 hdepthTerminal
        refine ⟨by simp, hphaseOld, hsource, hreset, Or.inr ⟨hless, ?_, ?_,
          hdepth.2, ?_⟩⟩
        · simpa [hp] using hphaseNew
        · simpa [RowNumeral.DigitCodec.nextRow] using hdepth.1
        · simpa [hp] using hlocalResult
    | true =>
        have hcomparisonOut : out.comparison = .eq := by
          simp [enumerationDone, haction, houtPlateau, hp] at hdone
          exact hdone.2
        have hlocalResult' :
            depthTrack (newHead :: newTail) = depthTrack (oldHead :: oldTail) ∧
              oldCountTrack (newHead :: newTail) =
                oldCountTrack (oldHead :: oldTail) := by
          simpa [hp] using hlocalResult
        have hequal : oldCountTrack (oldHead :: oldTail) =
            newCountTrack (oldHead :: oldTail) := by
          apply (compareRows_eq_some_eq_iff (countCodec A) _ _).1
          simp [RowNumeral.DigitCodec.compareRows, hcomparisonScan, hcomparisonOut]
        refine ⟨by simp, hphaseOld, hsource, hreset, Or.inl ⟨hequal, ?_, ?_, ?_⟩⟩
        · simpa [hp] using hphaseNew
        · exact hlocalResult'.1
        · exact hlocalResult'.2
  · rintro ⟨hold, hspec⟩
    cases old with
    | nil => contradiction
    | cons oldHead oldTail =>
        have hlen : (oldHead :: oldTail).length = new.length :=
          length_eq_of_sourceTrack_eq hspec.2.1
        cases new with
        | nil => simp at hlen
        | cons newHead newTail =>
            rcases hspec with
              ⟨hphaseOld, hsource, hreset,
                ⟨hequal, hphaseNew, hdepthCopy, holdCountCopy⟩ |
                ⟨hless, hphaseNew, hdepthNext, hdepthNoOverflow, holdCountNext⟩⟩
            · let plateau : Bool := true
              have hlocal : FinishRoundLocalSpec plateau
                  (oldHead :: oldTail) (newHead :: newTail) := by
                exact ⟨hphaseOld, by simpa [plateau] using hphaseNew, hsource,
                  hreset, by simpa [plateau] using ⟨hdepthCopy, holdCountCopy⟩⟩
              have hplateauHead : (newHead.phase == .finalChoose) = plateau := by
                have hhead := hphaseNew newHead (by simp)
                simp [plateau, hhead]
              let acc := startEnumerationAccumulator .finishRound oldHead newHead
              obtain ⟨out, heval⟩ :=
                (exists_evalEnumerationAccumulator_iff acc _ _).2 hlen
              have hcheck := (checkRows_finishRound_iff plateau _ _).2 hlocal
              have hok := evalEnumerationAccumulator_ok heval
              have houtok : out.ok = true := by
                rw [hok]
                simpa [acc, startEnumerationAccumulator, enumerationLocalOK,
                  hplateauHead] using hcheck
              have haction : out.action = .finishRound := by
                simpa [acc, startEnumerationAccumulator] using
                  evalEnumerationAccumulator_action heval
              have houtPlateau : out.overflow = plateau := by
                simpa [acc, startEnumerationAccumulator, hplateauHead] using
                  evalEnumerationAccumulator_overflow heval
              have hcomparisonScan : (countCodec A).evalCompare .eq
                  (oldCountTrack (oldHead :: oldTail))
                  (newCountTrack (oldHead :: oldTail)) = some out.comparison := by
                simpa [acc, startEnumerationAccumulator] using
                  (evalEnumerationAccumulator_comparison
                    (acc := acc) (out := out) (old := oldHead :: oldTail)
                    (new := newHead :: newTail)
                    (by simp [acc, startEnumerationAccumulator]) heval)
              have hcomparisonTarget : (countCodec A).evalCompare .eq
                  (oldCountTrack (oldHead :: oldTail))
                  (newCountTrack (oldHead :: oldTail)) = some .eq :=
                (evalCompare_eq_some_eq_iff (countCodec A) .eq _ _).2
                  ⟨hequal, rfl⟩
              have hcomparisonOut : out.comparison = .eq :=
                Option.some.inj (hcomparisonScan.symm.trans hcomparisonTarget)
              refine ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, ?_⟩
              simp [enumerationDone, haction, houtPlateau, plateau, houtok,
                hcomparisonOut]
            · let plateau : Bool := false
              have hlocal : FinishRoundLocalSpec plateau
                  (oldHead :: oldTail) (newHead :: newTail) := by
                exact ⟨hphaseOld, by simpa [plateau] using hphaseNew, hsource,
                  hreset, by simpa [plateau] using holdCountNext⟩
              have hplateauHead : (newHead.phase == .finalChoose) = plateau := by
                have hhead := hphaseNew newHead (by simp)
                simp [plateau, hhead]
              let acc := startEnumerationAccumulator .finishRound oldHead newHead
              obtain ⟨out, heval⟩ :=
                (exists_evalEnumerationAccumulator_iff acc _ _).2 hlen
              have hcheck := (checkRows_finishRound_iff plateau _ _).2 hlocal
              have hok := evalEnumerationAccumulator_ok heval
              have houtok : out.ok = true := by
                rw [hok]
                simpa [acc, startEnumerationAccumulator, enumerationLocalOK,
                  hplateauHead] using hcheck
              have haction : out.action = .finishRound := by
                simpa [acc, startEnumerationAccumulator] using
                  evalEnumerationAccumulator_action heval
              have houtPlateau : out.overflow = plateau := by
                simpa [acc, startEnumerationAccumulator, hplateauHead] using
                  evalEnumerationAccumulator_overflow heval
              have hcomparisonScan : (countCodec A).evalCompare .eq
                  (oldCountTrack (oldHead :: oldTail))
                  (newCountTrack (oldHead :: oldTail)) = some out.comparison := by
                simpa [acc, startEnumerationAccumulator] using
                  (evalEnumerationAccumulator_comparison
                    (acc := acc) (out := out) (old := oldHead :: oldTail)
                    (new := newHead :: newTail)
                    (by simp [acc, startEnumerationAccumulator]) heval)
              have hcomparisonTarget : (countCodec A).evalCompare .eq
                  (oldCountTrack (oldHead :: oldTail))
                  (newCountTrack (oldHead :: oldTail)) = some .lt := by
                simpa [RowNumeral.DigitCodec.rowsLess,
                  RowNumeral.DigitCodec.compareRows] using hless
              have hcomparisonOut : out.comparison = .lt :=
                Option.some.inj (hcomparisonScan.symm.trans hcomparisonTarget)
              have hdepthScan := evalEnumerationAccumulator_depthSucc
                (acc := acc) (out := out) (old := oldHead :: oldTail)
                (new := newHead :: newTail)
                (by simp [acc, startEnumerationAccumulator])
                (by simp [acc, plateau, startEnumerationAccumulator,
                  hplateauHead]) heval
              have hdepthTarget : (vertexCodec A).evalSucc .carry
                  (depthTrack (oldHead :: oldTail))
                  (depthTrack (newHead :: newTail)) = some .done := by
                simpa using (evalSucc_terminal_iff (vertexCodec A) false _ _).2
                  ⟨hdepthNext, hdepthNoOverflow⟩
              have hvertexDone : out.vertexSucc = .done := by
                apply Option.some.inj
                rw [← hdepthTarget]
                simpa [acc, startEnumerationAccumulator] using hdepthScan.symm
              refine ⟨oldHead, oldTail, newHead, newTail, out, rfl, rfl, heval, ?_⟩
              simp [enumerationDone, haction, houtPlateau, plateau, houtok,
                hcomparisonOut, hvertexDone]

end CertifiedRowSystem.Complement
