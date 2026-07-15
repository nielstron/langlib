module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Definition
import Mathlib.Data.List.OfFn

@[expose]
public section

/-!
# Canonical fixed-width protocol rows

This file packages the routine construction of a protocol row from its synchronous
tracks.  The function-indexed constructor is the primitive operation; the list-based
wrapper is convenient when an action copies most tracks from an existing row.
-/

namespace CertifiedRowSystem.Complement

/-- Regard a list as a function on its canonical finite index type. -/
public def listToFixed {X : Type*} (xs : List X) : Fin xs.length → X :=
  xs.get

@[simp]
public theorem ofFn_listToFixed {X : Type*} (xs : List X) :
    List.ofFn (listToFixed xs) = xs := by
  simp [listToFixed]

/-- Reindex a list by any propositionally equal width. -/
public def listToFixedCast {X : Type*} (xs : List X) {width : Nat}
    (h : xs.length = width) : Fin width → X :=
  fun i ↦ xs.get (Fin.cast h.symm i)

@[simp]
public theorem ofFn_listToFixedCast {X : Type*} (xs : List X) {width : Nat}
    (h : xs.length = width) :
    List.ofFn (listToFixedCast xs h) = xs := by
  apply List.ext_get
  · simpa using h.symm
  · intro i hi hj
    simp [listToFixedCast]

/-- Build a protocol row of fixed width from all nine track functions and replicated
`found`/`phase` values. -/
public def canonicalProtocolRow {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) : ProtocolRow A :=
  List.ofFn fun i ↦
    { vertex :=
        { source := source i
          depth := depth i
          outer := outer i
          inner := inner i
          path := path i
          fuel := fuel i }
      counter :=
        { oldCount := oldCount i
          newCount := newCount i
          seenCount := seenCount i }
      found := found
      phase := phase }

@[simp]
public theorem length_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase).length = width := by
  simp [canonicalProtocolRow]

@[simp]
public theorem sourceTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    sourceTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn source := by
  simp [canonicalProtocolRow, sourceTrack, Function.comp_def]

@[simp]
public theorem depthTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    depthTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn depth := by
  simp [canonicalProtocolRow, depthTrack, Function.comp_def]

@[simp]
public theorem outerTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    outerTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn outer := by
  simp [canonicalProtocolRow, outerTrack, Function.comp_def]

@[simp]
public theorem innerTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    innerTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn inner := by
  simp [canonicalProtocolRow, innerTrack, Function.comp_def]

@[simp]
public theorem pathTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    pathTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn path := by
  simp [canonicalProtocolRow, pathTrack, Function.comp_def]

@[simp]
public theorem fuelTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    fuelTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn fuel := by
  simp [canonicalProtocolRow, fuelTrack, Function.comp_def]

@[simp]
public theorem oldCountTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    oldCountTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn oldCount := by
  simp [canonicalProtocolRow, oldCountTrack, Function.comp_def]

@[simp]
public theorem newCountTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    newCountTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn newCount := by
  simp [canonicalProtocolRow, newCountTrack, Function.comp_def]

@[simp]
public theorem seenCountTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    seenCountTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.ofFn seenCount := by
  simp [canonicalProtocolRow, seenCountTrack, Function.comp_def]

@[simp]
public theorem foundTrack_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    foundTrack (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) = List.replicate width found := by
  simp [canonicalProtocolRow, foundTrack, Function.comp_def]

@[simp]
public theorem hasFound_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    HasFound found (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) := by
  simp [HasFound, canonicalProtocolRow]

@[simp]
public theorem hasPhase_canonicalProtocolRow
    {A : Type*} [Fintype A] {width : Nat}
    (source depth outer inner path fuel : Fin width → A)
    (oldCount newCount seenCount : Fin width → CountDigit A)
    (found : Bool) (phase : ProtocolPhase) :
    HasPhase phase (canonicalProtocolRow source depth outer inner path fuel
      oldCount newCount seenCount found phase) := by
  simp [HasPhase, canonicalProtocolRow]

/-- Nine concrete track lists sharing the source-list width. -/
public structure ProtocolTrackLists (A : Type*) [Fintype A] where
  source : List A
  depth : List A
  outer : List A
  inner : List A
  path : List A
  fuel : List A
  oldCount : List (CountDigit A)
  newCount : List (CountDigit A)
  seenCount : List (CountDigit A)
  depth_length : depth.length = source.length
  outer_length : outer.length = source.length
  inner_length : inner.length = source.length
  path_length : path.length = source.length
  fuel_length : fuel.length = source.length
  oldCount_length : oldCount.length = source.length
  newCount_length : newCount.length = source.length
  seenCount_length : seenCount.length = source.length

/-- Build a canonical row directly from equal-width concrete track lists. -/
public def protocolRowOfTracks {A : Type*} [Fintype A]
    (tracks : ProtocolTrackLists A) (found : Bool) (phase : ProtocolPhase) :
    ProtocolRow A :=
  canonicalProtocolRow
    (listToFixed tracks.source)
    (listToFixedCast tracks.depth tracks.depth_length)
    (listToFixedCast tracks.outer tracks.outer_length)
    (listToFixedCast tracks.inner tracks.inner_length)
    (listToFixedCast tracks.path tracks.path_length)
    (listToFixedCast tracks.fuel tracks.fuel_length)
    (listToFixedCast tracks.oldCount tracks.oldCount_length)
    (listToFixedCast tracks.newCount tracks.newCount_length)
    (listToFixedCast tracks.seenCount tracks.seenCount_length)
    found phase

@[simp]
public theorem length_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    (protocolRowOfTracks tracks found phase).length = tracks.source.length := by
  simp [protocolRowOfTracks]

@[simp]
public theorem sourceTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    sourceTrack (protocolRowOfTracks tracks found phase) = tracks.source := by
  simp [protocolRowOfTracks]

@[simp]
public theorem depthTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    depthTrack (protocolRowOfTracks tracks found phase) = tracks.depth := by
  simp [protocolRowOfTracks]

@[simp]
public theorem outerTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    outerTrack (protocolRowOfTracks tracks found phase) = tracks.outer := by
  simp [protocolRowOfTracks]

@[simp]
public theorem innerTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    innerTrack (protocolRowOfTracks tracks found phase) = tracks.inner := by
  simp [protocolRowOfTracks]

@[simp]
public theorem pathTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    pathTrack (protocolRowOfTracks tracks found phase) = tracks.path := by
  simp [protocolRowOfTracks]

@[simp]
public theorem fuelTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    fuelTrack (protocolRowOfTracks tracks found phase) = tracks.fuel := by
  simp [protocolRowOfTracks]

@[simp]
public theorem oldCountTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    oldCountTrack (protocolRowOfTracks tracks found phase) = tracks.oldCount := by
  simp [protocolRowOfTracks]

@[simp]
public theorem newCountTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    newCountTrack (protocolRowOfTracks tracks found phase) = tracks.newCount := by
  simp [protocolRowOfTracks]

@[simp]
public theorem seenCountTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    seenCountTrack (protocolRowOfTracks tracks found phase) = tracks.seenCount := by
  simp [protocolRowOfTracks]

@[simp]
public theorem foundTrack_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    foundTrack (protocolRowOfTracks tracks found phase) =
      List.replicate tracks.source.length found := by
  simp [protocolRowOfTracks]

@[simp]
public theorem hasFound_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    HasFound found (protocolRowOfTracks tracks found phase) := by
  simp [protocolRowOfTracks]

@[simp]
public theorem hasPhase_protocolRowOfTracks
    {A : Type*} [Fintype A] (tracks : ProtocolTrackLists A)
    (found : Bool) (phase : ProtocolPhase) :
    HasPhase phase (protocolRowOfTracks tracks found phase) := by
  simp [protocolRowOfTracks]

end CertifiedRowSystem.Complement
