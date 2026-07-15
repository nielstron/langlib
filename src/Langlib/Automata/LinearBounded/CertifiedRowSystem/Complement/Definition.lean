module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Determinize
public import Langlib.Automata.LinearBounded.FiniteReachabilityCounting
public import Langlib.Automata.LinearBounded.RowEnumeration
import Mathlib.Tactic

@[expose]
public section

/-!
# Complementing certified row systems

This module implements the inductive-counting construction used to complement the
reachability language of a finite `CertifiedRowSystem`.

The source system is first determinized by `CertifiedRowSystem.determinize`.  Its
certificate alphabet is then `Unit`, and its verifier state after an aligned row scan is
the exact set of every source-verifier state reachable by a certificate prefix.  Thus an
edge and the absence of an edge are both synchronous finite-state checks.

The complement protocol stores a constant number of tracks in each row cell.  Vertex and
fuel tracks use the source row alphabet; count tracks use radix `Fintype.card A + 1`, so a
nonempty width-`n` row can represent every count up to `(Fintype.card A) ^ n`.  All tracks
are least-significant-cell first and are scanned using `RowNumeral`.
-/

open Classical

namespace CertifiedRowSystem

/-! ## The semantic finite graph -/

namespace Complement

variable {I A C Q F : Type*}

/-- A fixed-width source row, represented without a length proof in every operation. -/
public abbrev FixedRow (A : Type*) (n : Nat) := Fin n → A

/-- Convert a fixed-width row to the list representation used by a certified row system. -/
public def FixedRow.toList {n : Nat} (row : FixedRow A n) : List A :=
  List.ofFn row

@[simp]
public theorem FixedRow.length_toList {n : Nat} (row : FixedRow A n) :
    row.toList.length = n := by
  simp [FixedRow.toList]

/-- The finite directed graph on width-`n` rows induced by the source row relation. -/
public def rowEdge (S : CertifiedRowSystem I A C Q F) {n : Nat}
    (old new : FixedRow A n) : Prop :=
  S.RowStep old.toList new.toList

/-- The source final predicate on a fixed-width row. -/
public def rowFinal (S : CertifiedRowSystem I A C Q F) {n : Nat}
    (row : FixedRow A n) : Prop :=
  S.Final row.toList

/-- The fixed-width source row obtained from an input row. -/
public def inputRow (S : CertifiedRowSystem I A C Q F) {n : Nat}
    (input : FixedRow I n) : FixedRow A n :=
  S.inputCell ∘ input

/-- The abstract counting certificate characterizes absence of a reachable final row in
the finite graph of width-`n` source rows.  This theorem is the semantic target of the
streaming certified-row protocol below. -/
public theorem no_final_iff_abstract_counting_certificate
    [Fintype A] [DecidableEq A]
    (S : CertifiedRowSystem I A C Q F) {n : Nat} (input : FixedRow I n) :
    (¬ ∃ row, Relation.ReflTransGen (rowEdge S) (inputRow S input) row ∧ rowFinal S row) ↔
      ∃ count,
        FiniteReachabilityCounting.CertifiedCount
            (rowEdge S) (inputRow S input) (Fintype.card (FixedRow A n)) count ∧
          Nonempty
            (FiniteReachabilityCounting.FinalRejection
              (rowEdge S) (inputRow S input) (Fintype.card (FixedRow A n)) count
              (rowFinal S)) := by
  letI : DecidableRel (rowEdge S : FixedRow A n → FixedRow A n → Prop) :=
    Classical.decRel _
  exact FiniteReachabilityCounting.no_reachable_final_iff_counting_certificate
    (rowEdge S) (inputRow S input)

/-! ## Streaming protocol storage -/

/-- Canonical numbering of an arbitrary nonempty finite source alphabet. -/
public noncomputable def vertexCodec (A : Type*) [Fintype A] [Nonempty A] :
    RowNumeral.DigitCodec A where
  toFin := Fintype.equivFin A

/-- Counter digits have one more value than the source alphabet.  Consequently a
width-`n > 0` counter can store the number of all width-`n` source rows. -/
public abbrev CountDigit (A : Type*) [Fintype A] := Fin (Fintype.card A + 1)

/-- Canonical codec for count digits. -/
public def countCodec (A : Type*) [Fintype A] :
    RowNumeral.DigitCodec (CountDigit A) :=
  RowNumeral.orderedCodec _

/-- The count radix is genuinely larger than one whenever the source alphabet is nonempty. -/
public theorem countRadix_gt_one (A : Type*) [Fintype A] [Nonempty A] :
    1 < (countCodec A).radix := by
  simp only [RowNumeral.DigitCodec.radix, CountDigit, Fintype.card_fin]
  exact Nat.lt_add_one_iff.mpr Fintype.card_pos

/-- Control phases of the streaming inductive-counting protocol.

`chooseInner` performs the canonical scan over possible old-reachable vertices.  A
positive choice enters `path`, which guesses a source path bounded by `depth`.  Once every
inner vertex has been considered, `finishOuter` classifies the current outer vertex and
updates the next count.  `finishRound` advances the depth enumeration.  The last two phases
perform the all-nonfinal scan justified by the final exact count. -/
public inductive ProtocolPhase where
  | input
  | roundStart
  | chooseInner
  | path
  | finishWitness
  | finishOuter
  | finishRound
  | finalChoose
  | finalPath
  | finalWitness
  | finalFinish
  | accept
  deriving DecidableEq, Fintype, Repr

/-- Source-alphabet tracks grouped to keep finite-instance synthesis shallow. -/
public structure VertexTracks (A : Type*) [Fintype A] where
  source : A
  depth : A
  outer : A
  inner : A
  path : A
  fuel : A
  deriving DecidableEq

public noncomputable instance VertexTracks.instFintype
    {A : Type*} [Fintype A] : Fintype (VertexTracks A) := by
  classical
  exact Fintype.ofInjective
    (fun x : VertexTracks A => (x.source, x.depth, x.outer, x.inner, x.path, x.fuel))
    (by
      intro x y h
      cases x
      cases y
      simp_all)

/-- Larger-radix counter tracks. -/
public structure CounterTracks (A : Type*) [Fintype A] where
  oldCount : CountDigit A
  newCount : CountDigit A
  seenCount : CountDigit A
  deriving DecidableEq

public noncomputable instance CounterTracks.instFintype
    {A : Type*} [Fintype A] : Fintype (CounterTracks A) := by
  classical
  exact Fintype.ofInjective
    (fun x : CounterTracks A => (x.oldCount, x.newCount, x.seenCount))
    (by
      intro x y h
      cases x
      cases y
      simp_all)

/-- One physical cell of the complement protocol.

`source` is immutable.  `depth`, `outer`, `inner`, `path`, and `fuel` are source-radix
row numerals.  `oldCount`, `newCount`, and `seenCount` use the strictly larger count radix.
The phase and Boolean flag are replicated; the verifier enforces uniformity on every scan. -/
public structure ProtocolCell (A : Type*) [Fintype A] where
  vertex : VertexTracks A
  counter : CounterTracks A
  found : Bool
  phase : ProtocolPhase
  deriving DecidableEq

public noncomputable instance ProtocolCell.instFintype
    {A : Type*} [Fintype A] : Fintype (ProtocolCell A) := by
  classical
  exact Fintype.ofInjective
    (fun x : ProtocolCell A => (x.vertex, x.counter, x.found, x.phase))
    (by
      intro x y h
      cases x
      cases y
      simp_all)

/-- A protocol row has one cell per source/input cell. -/
public abbrev ProtocolRow (A : Type*) [Fintype A] := List (ProtocolCell A)

/-- The phase is replicated across the complete row. -/
public def HasPhase {A : Type*} [Fintype A]
    (phase : ProtocolPhase) (row : ProtocolRow A) : Prop :=
  ∀ cell ∈ row, cell.phase = phase

/-- Extract the immutable source track. -/
public def sourceTrack {A : Type*} [Fintype A] (row : ProtocolRow A) : List A :=
  row.map fun cell ↦ cell.vertex.source

/-- Extract the current counting depth. -/
public def depthTrack {A : Type*} [Fintype A] (row : ProtocolRow A) : List A :=
  row.map fun cell ↦ cell.vertex.depth

/-- Extract the exact count from the preceding round. -/
public def oldCountTrack {A : Type*} [Fintype A]
    (row : ProtocolRow A) : List (CountDigit A) :=
  row.map fun cell ↦ cell.counter.oldCount

/-- Extract the accumulating next-round count. -/
public def newCountTrack {A : Type*} [Fintype A]
    (row : ProtocolRow A) : List (CountDigit A) :=
  row.map fun cell ↦ cell.counter.newCount

/-- Extract the number of old-reachable vertices selected in the current canonical scan. -/
public def seenCountTrack {A : Type*} [Fintype A]
    (row : ProtocolRow A) : List (CountDigit A) :=
  row.map fun cell ↦ cell.counter.seenCount

/-- Extract the outer vertex being classified. -/
public def outerTrack {A : Type*} [Fintype A] (row : ProtocolRow A) : List A :=
  row.map fun cell ↦ cell.vertex.outer

/-- Extract the old vertex currently considered by the inner scan. -/
public def innerTrack {A : Type*} [Fintype A] (row : ProtocolRow A) : List A :=
  row.map fun cell ↦ cell.vertex.inner

/-- Extract the current row of a guessed source path. -/
public def pathTrack {A : Type*} [Fintype A] (row : ProtocolRow A) : List A :=
  row.map fun cell ↦ cell.vertex.path

/-- Extract the length of the guessed path. -/
public def fuelTrack {A : Type*} [Fintype A] (row : ProtocolRow A) : List A :=
  row.map fun cell ↦ cell.vertex.fuel

/-- Extract the replicated inclusion flag. -/
public def foundTrack {A : Type*} [Fintype A] (row : ProtocolRow A) : List Bool :=
  row.map ProtocolCell.found

/-- All replicated `found` flags have the specified value. -/
public def HasFound {A : Type*} [Fintype A] (found : Bool) (row : ProtocolRow A) : Prop :=
  ∀ cell ∈ row, cell.found = found

/-- Shape invariant shared by every protocol phase. -/
public structure WellFormedRow {A : Type*} [Fintype A]
    (width : Nat) (row : ProtocolRow A) : Prop where
  length_eq : row.length = width
  uniform_phase : ∃ phase, HasPhase phase row
  uniform_found : ∃ found, HasFound found row

/-- The input image stores the source row and initializes every work track to zero.  The
first protocol transition changes `oldCount` from the all-zero input image to the
LSD-first numeral one; doing this in a transition lets the finite verifier identify the
first cell. -/
public noncomputable def inputProtocolCell
    {I A : Type*} [Fintype A] [Nonempty A]
    (sourceCell : I → A) (input : I) : ProtocolCell A where
  vertex :=
    { source := sourceCell input
      depth := (vertexCodec A).zero
      outer := (vertexCodec A).zero
      inner := (vertexCodec A).zero
      path := (vertexCodec A).zero
      fuel := (vertexCodec A).zero }
  counter :=
    { oldCount := (countCodec A).zero
      newCount := (countCodec A).zero
      seenCount := (countCodec A).zero }
  found := false
  phase := .input

/-- Predicate describing the canonical initialized row after the boot transition. -/
public def IsInitialized {A : Type*} [Fintype A] [Nonempty A]
    (source : List A) (row : ProtocolRow A) : Prop :=
  sourceTrack row = source ∧
  HasPhase .roundStart row ∧
  depthTrack row = (vertexCodec A).zeroRow row.length ∧
  oldCountTrack row = (countCodec A).oneRow (countRadix_gt_one A) row.length ∧
  newCountTrack row = (countCodec A).zeroRow row.length ∧
  seenCountTrack row = (countCodec A).zeroRow row.length ∧
  outerTrack row = (vertexCodec A).zeroRow row.length ∧
  innerTrack row = (vertexCodec A).zeroRow row.length ∧
  pathTrack row = (vertexCodec A).zeroRow row.length ∧
  fuelTrack row = (vertexCodec A).zeroRow row.length ∧
  HasFound false row

/-- One initialized protocol cell.  The first cell stores the least-significant digit one
of the initial reachable count; every later count digit is zero. -/
public noncomputable def initializedProtocolCell
    {A : Type*} [Fintype A] [Nonempty A] (first : Bool) (source : A) :
    ProtocolCell A where
  vertex :=
    { source := source
      depth := (vertexCodec A).zero
      outer := (vertexCodec A).zero
      inner := (vertexCodec A).zero
      path := (vertexCodec A).zero
      fuel := (vertexCodec A).zero }
  counter :=
    { oldCount := if first then (countCodec A).one (countRadix_gt_one A)
        else (countCodec A).zero
      newCount := (countCodec A).zero
      seenCount := (countCodec A).zero }
  found := false
  phase := .roundStart

/-- Canonical initialized protocol row for a nonempty source row. -/
public noncomputable def initializedProtocolRow
    {A : Type*} [Fintype A] [Nonempty A] : List A → ProtocolRow A
  | [] => []
  | source :: sources =>
      initializedProtocolCell true source ::
        sources.map (initializedProtocolCell false)

@[simp]
public theorem length_initializedProtocolRow
    {A : Type*} [Fintype A] [Nonempty A] (source : List A) :
    (initializedProtocolRow source).length = source.length := by
  cases source <;> simp [initializedProtocolRow]

/-- The canonical initialized row satisfies every initialization invariant. -/
public theorem isInitialized_initializedProtocolRow
    {A : Type*} [Fintype A] [Nonempty A]
    {source : List A} (hne : source ≠ []) :
    IsInitialized source (initializedProtocolRow source) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [IsInitialized, initializedProtocolRow, initializedProtocolCell,
    sourceTrack, depthTrack, oldCountTrack, newCountTrack, seenCountTrack,
    outerTrack, innerTrack, pathTrack, fuelTrack, HasPhase, HasFound,
    RowNumeral.DigitCodec.oneRow, RowNumeral.DigitCodec.zeroRow]
  simp [Function.comp_def, initializedProtocolCell, List.replicate_succ]

/-- A transition label is repeated in the certificate row.  The finite verifier rejects
if different cells request different actions. -/
public inductive ProtocolAction where
  | boot
  | beginRound
  | beginFinal
  | skipInner
  | startPath
  | pathStep
  | finishWitness
  | finishOuter
  | finishRound
  | finalSkip
  | finalStartPath
  | finalPathStep
  | finalFinishWitness
  | finalFinish
  deriving DecidableEq, Fintype, Repr


end Complement

end CertifiedRowSystem
