module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Enumeration actions of the inductive-counting protocol

These list-level specifications describe the canonical inner-vertex scan, outer-vertex
scan, count-round boundary, and final rejecting scan.  The synchronous scanners in
`Construction.lean` implement exactly these predicates.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {A : Type*} [Fintype A] [Nonempty A]

/-- Every track except the replicated phase is copied. -/
public def CopiesPayload (old new : ProtocolRow A) : Prop :=
  sourceTrack new = sourceTrack old ∧
  depthTrack new = depthTrack old ∧
  oldCountTrack new = oldCountTrack old ∧
  newCountTrack new = newCountTrack old ∧
  seenCountTrack new = seenCountTrack old ∧
  outerTrack new = outerTrack old ∧
  innerTrack new = innerTrack old ∧
  pathTrack new = pathTrack old ∧
  fuelTrack new = fuelTrack old ∧
  foundTrack new = foundTrack old

/-- Enter the inner scan for the current outer vertex. -/
public def BeginRoundSpec (old new : ProtocolRow A) : Prop :=
  HasPhase .roundStart old ∧ HasPhase .chooseInner new ∧ CopiesPayload old new

/-- Skip the current inner vertex and advance the canonical enumeration.  Overflow
means every inner vertex has been considered and enters `finishOuter`. -/
public def SkipInnerSpec (old new : ProtocolRow A) : Prop :=
  HasPhase .chooseInner old ∧
  sourceTrack new = sourceTrack old ∧
  depthTrack new = depthTrack old ∧
  oldCountTrack new = oldCountTrack old ∧
  newCountTrack new = newCountTrack old ∧
  seenCountTrack new = seenCountTrack old ∧
  outerTrack new = outerTrack old ∧
  pathTrack new = pathTrack old ∧
  fuelTrack new = fuelTrack old ∧
  foundTrack new = foundTrack old ∧
  innerTrack new = (vertexCodec A).nextRow (innerTrack old) ∧
  (if ((vertexCodec A).increment (innerTrack old)).2 then
      HasPhase .finishOuter new
    else HasPhase .chooseInner new)

/-- Reset all work tracks used for the next canonical outer scan. -/
public def OuterResetSpec (_old new : ProtocolRow A) : Prop :=
  innerTrack new = (vertexCodec A).zeroRow new.length ∧
  seenCountTrack new = (countCodec A).zeroRow new.length ∧
  pathTrack new = (vertexCodec A).zeroRow new.length ∧
  fuelTrack new = (vertexCodec A).zeroRow new.length ∧
  HasFound false new

/-- Finish classifying one outer vertex.  Exactness of `oldCount` is checked by
`seenCount = oldCount`; `newCount` is incremented exactly when `found` is true. -/
public def FinishOuterSpec (old new : ProtocolRow A) : Prop :=
  HasPhase .finishOuter old ∧
  seenCountTrack old = oldCountTrack old ∧
  sourceTrack new = sourceTrack old ∧
  depthTrack new = depthTrack old ∧
  oldCountTrack new = oldCountTrack old ∧
  outerTrack new = (vertexCodec A).nextRow (outerTrack old) ∧
  OuterResetSpec old new ∧
  ((HasFound true old ∧
      newCountTrack new = (countCodec A).nextRow (newCountTrack old) ∧
      ((countCodec A).increment (newCountTrack old)).2 = false) ∨
    (HasFound false old ∧ newCountTrack new = newCountTrack old)) ∧
  (if ((vertexCodec A).increment (outerTrack old)).2 then
      HasPhase .finishRound new
    else HasPhase .chooseInner new)

/-- Common zeroed work tracks at a count-round boundary. -/
public def RoundResetSpec (new : ProtocolRow A) : Prop :=
  newCountTrack new = (countCodec A).zeroRow new.length ∧
  seenCountTrack new = (countCodec A).zeroRow new.length ∧
  outerTrack new = (vertexCodec A).zeroRow new.length ∧
  innerTrack new = (vertexCodec A).zeroRow new.length ∧
  pathTrack new = (vertexCodec A).zeroRow new.length ∧
  fuelTrack new = (vertexCodec A).zeroRow new.length ∧
  HasFound false new

/-- Finish a complete count round.  Equal old and new counts prove a plateau and enter
the final all-nonfinal scan.  Otherwise the count must strictly increase; it becomes the
next exact count while depth is incremented. -/
public def FinishRoundSpec (old new : ProtocolRow A) : Prop :=
  HasPhase .finishRound old ∧
  sourceTrack new = sourceTrack old ∧
  RoundResetSpec new ∧
  ((oldCountTrack old = newCountTrack old ∧
      HasPhase .finalChoose new ∧
      depthTrack new = depthTrack old ∧
      oldCountTrack new = oldCountTrack old) ∨
    ((countCodec A).rowsLess (oldCountTrack old) (newCountTrack old) ∧
      HasPhase .roundStart new ∧
      depthTrack new = (vertexCodec A).nextRow (depthTrack old) ∧
      ((vertexCodec A).increment (depthTrack old)).2 = false ∧
      oldCountTrack new = newCountTrack old))

/-- Skip one vertex in the final canonical scan. -/
public def FinalSkipSpec (old new : ProtocolRow A) : Prop :=
  HasPhase .finalChoose old ∧
  sourceTrack new = sourceTrack old ∧
  depthTrack new = depthTrack old ∧
  oldCountTrack new = oldCountTrack old ∧
  newCountTrack new = newCountTrack old ∧
  seenCountTrack new = seenCountTrack old ∧
  outerTrack new = outerTrack old ∧
  pathTrack new = pathTrack old ∧
  fuelTrack new = fuelTrack old ∧
  foundTrack new = foundTrack old ∧
  innerTrack new = (vertexCodec A).nextRow (innerTrack old) ∧
  (if ((vertexCodec A).increment (innerTrack old)).2 then
      HasPhase .finalFinish new
    else HasPhase .finalChoose new)

/-- The final scan accepts only after it has selected exactly the certified number of
reachable, nonfinal vertices. -/
public def FinalFinishSpec (old new : ProtocolRow A) : Prop :=
  HasPhase .finalFinish old ∧ HasPhase .accept new ∧
  seenCountTrack old = oldCountTrack old ∧
  sourceTrack new = sourceTrack old

end CertifiedRowSystem.Complement
