module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.CanonicalRows
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.PathActionConstructors
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.PathSemanticPreservation
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical executable reachability witnesses

Every member of a bounded reachable layer has an exactly fuel-indexed padded path.
This module turns that path into an executable sequence of protocol actions, both in
an inductive-counting inner scan and in the final all-nonfinal scan.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

private theorem protocolStep_of_startsPath
    {D : CertifiedRowSystem I A Unit Q F} {old new : ProtocolRow A}
    (holdNe : old ≠ [])
    (hstep : StartsPath .chooseInner .path old new) :
    ProtocolStep D old new := by
  refine ⟨holdNe, ?_⟩
  aesop

private theorem protocolStep_of_finalStartsPath
    {D : CertifiedRowSystem I A Unit Q F} {old new : ProtocolRow A}
    (holdNe : old ≠ [])
    (hstep : StartsPath .finalChoose .finalPath old new) :
    ProtocolStep D old new := by
  refine ⟨holdNe, ?_⟩
  aesop

private theorem protocolStep_of_pathStep
    {D : CertifiedRowSystem I A Unit Q F} {old new : ProtocolRow A}
    (holdNe : old ≠ []) (hstep : IsPathStep D .path old new) :
    ProtocolStep D old new := by
  refine ⟨holdNe, ?_⟩
  aesop

private theorem protocolStep_of_finalPathStep
    {D : CertifiedRowSystem I A Unit Q F} {old new : ProtocolRow A}
    (holdNe : old ≠ []) (hstep : IsPathStep D .finalPath old new) :
    ProtocolStep D old new := by
  refine ⟨holdNe, ?_⟩
  aesop

private theorem protocolStep_of_finishWitness
    {D : CertifiedRowSystem I A Unit Q F} {old new : ProtocolRow A}
    (holdNe : old ≠ []) (hstep : IsFinishWitness D old new) :
    ProtocolStep D old new := by
  refine ⟨holdNe, ?_⟩
  aesop

private theorem protocolStep_of_finalWitness
    {D : CertifiedRowSystem I A Unit Q F} {old new : ProtocolRow A}
    (holdNe : old ≠ []) (hstep : IsFinalWitness D old new) :
    ProtocolStep D old new := by
  refine ⟨holdNe, ?_⟩
  aesop

private theorem exists_countingPath_start
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : ChooseInnerInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected) :
    ∃ new, ProtocolStep D old new ∧
      CountingPathInvariant D input new depth oldCount newCount outerIndex
        innerIndex selected (protocolSourceRank D input).val 0 := by
  let found := foundFrom D input ⟨outerIndex, hinv.outer_lt⟩ selected
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := outerTrack old
      inner := innerTrack old
      path := sourceTrack old
      fuel := (vertexCodec A).zeroRow old.length
      oldCount := oldCountTrack old
      newCount := newCountTrack old
      seenCount := seenCountTrack old
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [sourceTrack, outerTrack]
      inner_length := by simp [sourceTrack, innerTrack]
      path_length := rfl
      fuel_length := by simp [sourceTrack]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by simp [sourceTrack, newCountTrack]
      seenCount_length := by simp [sourceTrack, seenCountTrack] }
  let new := protocolRowOfTracks tracks found .path
  have holdFound : foundTrack old = List.replicate old.length found :=
    (foundTrack_eq_replicate_iff old found).2 hinv.found_eq
  have hspec : StartsPath .chooseInner .path old new := by
    rw [startsPath_iff_tracks]
    refine ⟨?_, hinv.phase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks, sourceTrack]
    · simp [new]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks, sourceTrack]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simpa [new, tracks, sourceTrack] using holdFound.symm
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  exact ⟨new, protocolStep_of_startsPath holdNe hspec,
    startsPath_preserves hinv hspec⟩

private theorem exists_finalPath_start
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A} {depth count innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinalChooseInvariant D input old depth count innerIndex selected) :
    ∃ new, ProtocolStep D old new ∧
      FinalPathInvariant D input new depth count innerIndex selected
        (protocolSourceRank D input).val 0 := by
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := outerTrack old
      inner := innerTrack old
      path := sourceTrack old
      fuel := (vertexCodec A).zeroRow old.length
      oldCount := oldCountTrack old
      newCount := newCountTrack old
      seenCount := seenCountTrack old
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [sourceTrack, outerTrack]
      inner_length := by simp [sourceTrack, innerTrack]
      path_length := rfl
      fuel_length := by simp [sourceTrack]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by simp [sourceTrack, newCountTrack]
      seenCount_length := by simp [sourceTrack, seenCountTrack] }
  let new := protocolRowOfTracks tracks false .finalPath
  have holdFound : foundTrack old = List.replicate old.length false :=
    (foundTrack_eq_replicate_iff old false).2 hinv.found_false
  have hspec : StartsPath .finalChoose .finalPath old new := by
    rw [startsPath_iff_tracks]
    refine ⟨?_, hinv.phase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks, sourceTrack]
    · simp [new]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks, sourceTrack]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simpa [new, tracks, sourceTrack] using holdFound.symm
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  exact ⟨new, protocolStep_of_finalStartsPath holdNe hspec,
    finalStartsPath_preserves hinv hspec⟩

private theorem exists_countingPath_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex pathIndex fuel : Nat}
    {selected : Finset (RankVertex A input.length)}
    {next : RankVertex A input.length}
    (hinput : input ≠ [])
    (hinv : CountingPathInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected pathIndex fuel)
    (hfuel : fuel < depth)
    (hmove : (⟨pathIndex, hinv.path_lt⟩ : RankVertex A input.length) = next ∨
      rankEdge D input.length ⟨pathIndex, hinv.path_lt⟩ next) :
    ∃ new, ProtocolStep D old new ∧
      CountingPathInvariant D input new depth oldCount newCount outerIndex
        innerIndex selected next.val (fuel + 1) := by
  let current : RankVertex A input.length := ⟨pathIndex, hinv.path_lt⟩
  let found := foundFrom D input ⟨outerIndex, hinv.outer_lt⟩ selected
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := outerTrack old
      inner := innerTrack old
      path := rankRow input.length next
      fuel := vertexNumeral input.length (fuel + 1)
      oldCount := oldCountTrack old
      newCount := newCountTrack old
      seenCount := seenCountTrack old
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [sourceTrack, outerTrack]
      inner_length := by simp [sourceTrack, innerTrack]
      path_length := by simp [sourceTrack, hinv.length_eq]
      fuel_length := by simp [sourceTrack, hinv.length_eq]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by simp [sourceTrack, newCountTrack]
      seenCount_length := by simp [sourceTrack, seenCountTrack] }
  let new := protocolRowOfTracks tracks found .path
  have holdFound : foundTrack old = List.replicate old.length found :=
    (foundTrack_eq_replicate_iff old found).2 hinv.found_eq
  have htracks : old.length = new.length ∧
      HasPhase .path old ∧ HasPhase .path new ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      innerTrack new = innerTrack old ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old ∧
      seenCountTrack new = seenCountTrack old ∧
      foundTrack new = foundTrack old := by
    refine ⟨?_, hinv.phase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks, sourceTrack]
    · simp [new]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simpa [new, tracks, sourceTrack] using holdFound.symm
  have hfuelCapacity : fuel < Fintype.card A ^ input.length :=
    lt_trans hfuel hinv.depth_lt
  have hfuelStep :
      (vertexCodec A).evalSucc .carry (fuelTrack old) (fuelTrack new) =
        some .done := by
    apply ((vertexCodec A).evalSucc_eq_done_iff _ _).2
    constructor
    · calc
        fuelTrack new = vertexNumeral input.length (fuel + 1) := by
          simp [new, tracks]
        _ = (vertexCodec A).nextRow (vertexNumeral input.length fuel) :=
          (nextRow_vertexNumeral input.length fuel).symm
        _ = (vertexCodec A).nextRow (fuelTrack old) := by rw [hinv.fuel_eq]
    · rw [hinv.fuel_eq]
      apply Bool.eq_false_iff.mpr
      intro hover
      have hcapacity :=
        (increment_vertexNumeral_overflow_iff (A := A) hfuelCapacity).1 hover
      have hnextLt : fuel + 1 < Fintype.card A ^ input.length :=
        lt_of_le_of_lt (Nat.succ_le_iff.mpr hfuel) hinv.depth_lt
      exact (Nat.ne_of_lt hnextLt) hcapacity
  have hfuelBound :
      (vertexCodec A).compareRows (fuelTrack old) (depthTrack old) = some .lt := by
    have hlength : (fuelTrack old).length = (depthTrack old).length := by
      simp [fuelTrack, depthTrack]
    apply ((vertexCodec A).compareRows_eq_lt_iff hlength).2
    rw [hinv.fuel_eq, hinv.depth_eq]
    simpa [value_vertexNumeral (A := A) hfuelCapacity,
      value_vertexNumeral (A := A) hinv.depth_lt] using hfuel
  have hpathStep : pathTrack new = pathTrack old ∨
      D.RowStep (pathTrack old) (pathTrack new) := by
    rcases hmove with hsame | hedge
    · left
      have hsame' : current = next := by simpa [current] using hsame
      calc
        pathTrack new = rankRow input.length next := by simp [new, tracks]
        _ = rankRow input.length current := congrArg (rankRow input.length) hsame'.symm
        _ = vertexNumeral input.length pathIndex := rfl
        _ = pathTrack old := hinv.path_eq.symm
    · right
      have hedge' : D.RowStep (rankRow input.length current)
          (rankRow input.length next) :=
        (rankEdge_iff D input.length current next).1 (by simpa [current] using hedge)
      rw [show pathTrack old = rankRow input.length current by
        simpa [current] using hinv.path_eq]
      rw [show pathTrack new = rankRow input.length next by simp [new, tracks]]
      exact hedge'
  have hspec : IsPathStep D .path old new :=
    isPathStep_of_tracks D .path old new htracks hfuelStep hfuelBound hpathStep
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  obtain ⟨pathIndex', hnextInv⟩ := pathStep_preserves hinv hspec
  have hpathIndex' : pathIndex' = next.val := by
    apply (vertexNumeral_injective (A := A) hnextInv.path_lt next.isLt).1
    calc
      vertexNumeral input.length pathIndex' = pathTrack new := hnextInv.path_eq.symm
      _ = rankRow input.length next := by simp [new, tracks]
      _ = vertexNumeral input.length next.val := rfl
  subst pathIndex'
  exact ⟨new, protocolStep_of_pathStep holdNe hspec, hnextInv⟩

private theorem exists_finalPath_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A}
    {depth count innerIndex pathIndex fuel : Nat}
    {selected : Finset (RankVertex A input.length)}
    {next : RankVertex A input.length}
    (hinput : input ≠ [])
    (hinv : FinalPathInvariant D input old depth count innerIndex selected
      pathIndex fuel)
    (hfuel : fuel < depth)
    (hmove : (⟨pathIndex, hinv.path_lt⟩ : RankVertex A input.length) = next ∨
      rankEdge D input.length ⟨pathIndex, hinv.path_lt⟩ next) :
    ∃ new, ProtocolStep D old new ∧
      FinalPathInvariant D input new depth count innerIndex selected
        next.val (fuel + 1) := by
  let current : RankVertex A input.length := ⟨pathIndex, hinv.path_lt⟩
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := outerTrack old
      inner := innerTrack old
      path := rankRow input.length next
      fuel := vertexNumeral input.length (fuel + 1)
      oldCount := oldCountTrack old
      newCount := newCountTrack old
      seenCount := seenCountTrack old
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [sourceTrack, outerTrack]
      inner_length := by simp [sourceTrack, innerTrack]
      path_length := by simp [sourceTrack, hinv.length_eq]
      fuel_length := by simp [sourceTrack, hinv.length_eq]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by simp [sourceTrack, newCountTrack]
      seenCount_length := by simp [sourceTrack, seenCountTrack] }
  let new := protocolRowOfTracks tracks false .finalPath
  have holdFound : foundTrack old = List.replicate old.length false :=
    (foundTrack_eq_replicate_iff old false).2 hinv.found_false
  have htracks : old.length = new.length ∧
      HasPhase .finalPath old ∧ HasPhase .finalPath new ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      innerTrack new = innerTrack old ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old ∧
      seenCountTrack new = seenCountTrack old ∧
      foundTrack new = foundTrack old := by
    refine ⟨?_, hinv.phase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks, sourceTrack]
    · simp [new]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simpa [new, tracks, sourceTrack] using holdFound.symm
  have hfuelCapacity : fuel < Fintype.card A ^ input.length :=
    lt_trans hfuel hinv.depth_lt
  have hfuelStep :
      (vertexCodec A).evalSucc .carry (fuelTrack old) (fuelTrack new) =
        some .done := by
    apply ((vertexCodec A).evalSucc_eq_done_iff _ _).2
    constructor
    · calc
        fuelTrack new = vertexNumeral input.length (fuel + 1) := by
          simp [new, tracks]
        _ = (vertexCodec A).nextRow (vertexNumeral input.length fuel) :=
          (nextRow_vertexNumeral input.length fuel).symm
        _ = (vertexCodec A).nextRow (fuelTrack old) := by rw [hinv.fuel_eq]
    · rw [hinv.fuel_eq]
      apply Bool.eq_false_iff.mpr
      intro hover
      have hcapacity :=
        (increment_vertexNumeral_overflow_iff (A := A) hfuelCapacity).1 hover
      have hnextLt : fuel + 1 < Fintype.card A ^ input.length :=
        lt_of_le_of_lt (Nat.succ_le_iff.mpr hfuel) hinv.depth_lt
      exact (Nat.ne_of_lt hnextLt) hcapacity
  have hfuelBound :
      (vertexCodec A).compareRows (fuelTrack old) (depthTrack old) = some .lt := by
    have hlength : (fuelTrack old).length = (depthTrack old).length := by
      simp [fuelTrack, depthTrack]
    apply ((vertexCodec A).compareRows_eq_lt_iff hlength).2
    rw [hinv.fuel_eq, hinv.depth_eq]
    simpa [value_vertexNumeral (A := A) hfuelCapacity,
      value_vertexNumeral (A := A) hinv.depth_lt] using hfuel
  have hpathStep : pathTrack new = pathTrack old ∨
      D.RowStep (pathTrack old) (pathTrack new) := by
    rcases hmove with hsame | hedge
    · left
      have hsame' : current = next := by simpa [current] using hsame
      calc
        pathTrack new = rankRow input.length next := by simp [new, tracks]
        _ = rankRow input.length current := congrArg (rankRow input.length) hsame'.symm
        _ = vertexNumeral input.length pathIndex := rfl
        _ = pathTrack old := hinv.path_eq.symm
    · right
      have hedge' : D.RowStep (rankRow input.length current)
          (rankRow input.length next) :=
        (rankEdge_iff D input.length current next).1 (by simpa [current] using hedge)
      rw [show pathTrack old = rankRow input.length current by
        simpa [current] using hinv.path_eq]
      rw [show pathTrack new = rankRow input.length next by simp [new, tracks]]
      exact hedge'
  have hspec : IsPathStep D .finalPath old new :=
    isPathStep_of_tracks D .finalPath old new htracks hfuelStep hfuelBound hpathStep
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  obtain ⟨pathIndex', hnextInv⟩ := finalPathStep_preserves hinv hspec
  have hpathIndex' : pathIndex' = next.val := by
    apply (vertexNumeral_injective (A := A) hnextInv.path_lt next.isLt).1
    calc
      vertexNumeral input.length pathIndex' = pathTrack new := hnextInv.path_eq.symm
      _ = rankRow input.length next := by simp [new, tracks]
      _ = vertexNumeral input.length next.val := rfl
  subst pathIndex'
  exact ⟨new, protocolStep_of_finalPathStep holdNe hspec, hnextInv⟩

private theorem countingPaddedPath_run
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {start : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hstart : CountingPathInvariant D input start depth oldCount newCount
      outerIndex innerIndex selected (protocolSourceRank D input).val 0)
    {fuel : Nat} {target : RankVertex A input.length}
    (hpath : FiniteReachabilityCounting.PaddedPath
      (rankEdge D input.length) (protocolSourceRank D input) fuel target)
    (hfuelLe : fuel ≤ depth) :
    ∃ new, Relation.ReflTransGen (ProtocolStep D) start new ∧
      CountingPathInvariant D input new depth oldCount newCount outerIndex
        innerIndex selected target.val fuel := by
  induction hpath with
  | zero =>
      exact ⟨start, .refl, hstart⟩
  | @succ k previous next hprefix hmove ih =>
      have hkLe : k ≤ depth := le_trans (Nat.le_succ k) hfuelLe
      have hkLt : k < depth := Nat.lt_of_succ_le hfuelLe
      obtain ⟨mid, hrun, hmid⟩ := ih hkLe
      obtain ⟨new, hstep, hnew⟩ :=
        exists_countingPath_step hinput hmid hkLt hmove
      exact ⟨new, hrun.tail hstep, hnew⟩

private theorem finalPaddedPath_run
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {start : ProtocolRow A} {depth count innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hstart : FinalPathInvariant D input start depth count innerIndex selected
      (protocolSourceRank D input).val 0)
    {fuel : Nat} {target : RankVertex A input.length}
    (hpath : FiniteReachabilityCounting.PaddedPath
      (rankEdge D input.length) (protocolSourceRank D input) fuel target)
    (hfuelLe : fuel ≤ depth) :
    ∃ new, Relation.ReflTransGen (ProtocolStep D) start new ∧
      FinalPathInvariant D input new depth count innerIndex selected target.val fuel := by
  induction hpath with
  | zero =>
      exact ⟨start, .refl, hstart⟩
  | @succ k previous next hprefix hmove ih =>
      have hkLe : k ≤ depth := le_trans (Nat.le_succ k) hfuelLe
      have hkLt : k < depth := Nat.lt_of_succ_le hfuelLe
      obtain ⟨mid, hrun, hmid⟩ := ih hkLe
      obtain ⟨new, hstep, hnew⟩ :=
        exists_finalPath_step hinput hmid hkLt hmove
      exact ⟨new, hrun.tail hstep, hnew⟩

private theorem exists_countingPath_finish
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : CountingPathInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected innerIndex depth) :
    ∃ new, ProtocolStep D old new ∧
      ((innerIndex + 1 < Fintype.card A ^ input.length ∧
          ChooseInnerInvariant D input new depth oldCount newCount outerIndex
            (innerIndex + 1) (insert ⟨innerIndex, hinv.inner_lt⟩ selected)) ∨
        (innerIndex + 1 = Fintype.card A ^ input.length ∧
          FinishOuterInvariant D input new depth oldCount newCount outerIndex
            (insert ⟨innerIndex, hinv.inner_lt⟩ selected))) := by
  let oldFound := foundFrom D input ⟨outerIndex, hinv.outer_lt⟩ selected
  obtain ⟨edgeState, hedge⟩ := exists_evalStep_unit_of_length D D.stepStart
    (innerTrack old) (outerTrack old) (by simp [innerTrack, outerTrack])
  have hedge' : D.evalStep D.stepStart (innerTrack old) (outerTrack old)
      (List.replicate old.length ()) = some edgeState := by
    simpa [innerTrack] using hedge
  let newFound := oldFound || decide (innerTrack old = outerTrack old) ||
    D.stepDone edgeState
  let overflow := ((vertexCodec A).increment (innerTrack old)).2
  let innerState : RowNumeral.CarryState := if overflow then .carry else .done
  let newPhase : ProtocolPhase := if overflow then .finishOuter else .chooseInner
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := outerTrack old
      inner := (vertexCodec A).nextRow (innerTrack old)
      path := (vertexCodec A).zeroRow old.length
      fuel := (vertexCodec A).zeroRow old.length
      oldCount := oldCountTrack old
      newCount := newCountTrack old
      seenCount := (countCodec A).nextRow (seenCountTrack old)
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [sourceTrack, outerTrack]
      inner_length := by simp [sourceTrack, innerTrack]
      path_length := by simp [sourceTrack]
      fuel_length := by simp [sourceTrack]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by simp [sourceTrack, newCountTrack]
      seenCount_length := by simp [sourceTrack, seenCountTrack] }
  let new := protocolRowOfTracks tracks newFound newPhase
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  have htracks : old.length = new.length ∧ HasPhase .path old ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      pathTrack new = (vertexCodec A).zeroRow new.length ∧
      fuelTrack new = (vertexCodec A).zeroRow new.length ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old := by
    refine ⟨?_, hinv.phase, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks, sourceTrack]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks, sourceTrack]
    · simp [new, tracks, sourceTrack]
    · simp [new, tracks]
    · simp [new, tracks]
  have hpath : pathTrack old = innerTrack old :=
    hinv.path_eq.trans hinv.inner_eq.symm
  have hfuel : fuelTrack old = depthTrack old :=
    hinv.fuel_eq.trans hinv.depth_eq.symm
  have hselectedCardLt : selected.card < Fintype.card A ^ input.length := by
    calc
      selected.card ≤ (rankPrefix input.length innerIndex).card :=
        Finset.card_le_card hinv.selected_prefix
      _ = innerIndex := card_rankPrefix (Nat.le_of_lt hinv.inner_lt)
      _ < Fintype.card A ^ input.length := hinv.inner_lt
  have hn : 0 < input.length := List.length_pos_of_ne_nil hinput
  have hseenBound : selected.card < (Fintype.card A + 1) ^ input.length :=
    lt_trans hselectedCardLt (rowCapacity_lt_countCapacity (A := A) hn)
  have hseen : (countCodec A).evalSucc .carry
      (seenCountTrack old) (seenCountTrack new) = some .done := by
    apply ((countCodec A).evalSucc_eq_done_iff _ _).2
    constructor
    · calc
        seenCountTrack new = (countCodec A).nextRow (seenCountTrack old) := by
          simp [new, tracks]
        _ = ((countCodec A).increment (seenCountTrack old)).1 := rfl
    · rw [hinv.seen_eq]
      apply Bool.eq_false_iff.mpr
      intro hover
      have hcapacity :=
        (increment_countNumeral_overflow_iff (A := A) hseenBound).1 hover
      have hnextLt : selected.card + 1 < (Fintype.card A + 1) ^ input.length :=
        lt_of_le_of_lt (Nat.succ_le_iff.mpr hselectedCardLt)
          (rowCapacity_lt_countCapacity (A := A) hn)
      exact (Nat.ne_of_lt hnextLt) hcapacity
  have hinner : (vertexCodec A).evalSucc .carry
      (innerTrack old) (innerTrack new) = some innerState := by
    by_cases hover : overflow = true
    · have hcarry := ((vertexCodec A).evalSucc_eq_carry_iff
        (innerTrack old) (innerTrack new)).2
      simpa [innerState, overflow, hover, new, tracks,
        RowNumeral.DigitCodec.nextRow] using
        hcarry ⟨by simp [new, tracks, RowNumeral.DigitCodec.nextRow], by simpa [overflow]⟩
    · have hoverFalse : overflow = false := Bool.eq_false_iff.mpr hover
      have hdone := ((vertexCodec A).evalSucc_eq_done_iff
        (innerTrack old) (innerTrack new)).2
      simpa [innerState, overflow, hoverFalse, new, tracks,
        RowNumeral.DigitCodec.nextRow] using
        hdone ⟨by simp [new, tracks, RowNumeral.DigitCodec.nextRow], by simpa [overflow]⟩
  have hphase : (innerState = .done ∧ newPhase = .chooseInner) ∨
      (innerState = .carry ∧ newPhase = .finishOuter) := by
    by_cases hover : overflow = true
    · right
      simp [innerState, newPhase, hover]
    · left
      have hoverFalse : overflow = false := Bool.eq_false_iff.mpr hover
      simp [innerState, newPhase, hoverFalse]
  have holdFoundUniform : HasFound oldFound old := hinv.found_eq
  have hnewFoundUniform : HasFound newFound new := by simp [new]
  have hnewPhaseUniform : HasPhase newPhase new := by simp [new]
  have hspec : IsFinishWitness D old new :=
    isFinishWitness_of_tracks D old new edgeState innerState oldFound newFound
      newPhase holdNe htracks hedge' hpath hfuel hseen hinner hphase
      holdFoundUniform hnewFoundUniform hnewPhaseUniform rfl
  exact ⟨new, protocolStep_of_finishWitness holdNe hspec,
    finishWitness_preserves hinput hinv hspec⟩

private theorem exists_finalPath_finish
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A} {depth count innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinalPathInvariant D input old depth count innerIndex selected
      innerIndex depth)
    (hnonfinal : ¬ rankFinal D input.length ⟨innerIndex, hinv.inner_lt⟩) :
    ∃ new, ProtocolStep D old new ∧
      ((innerIndex + 1 < Fintype.card A ^ input.length ∧
          FinalChooseInvariant D input new depth count (innerIndex + 1)
            (insert ⟨innerIndex, hinv.inner_lt⟩ selected)) ∨
        (innerIndex + 1 = Fintype.card A ^ input.length ∧
          FinalFinishInvariant D input new depth count
            (insert ⟨innerIndex, hinv.inner_lt⟩ selected))) := by
  let finalState := D.evalFinal D.finalStart (innerTrack old)
  let overflow := ((vertexCodec A).increment (innerTrack old)).2
  let innerState : RowNumeral.CarryState := if overflow then .carry else .done
  let newPhase : ProtocolPhase := if overflow then .finalFinish else .finalChoose
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := outerTrack old
      inner := (vertexCodec A).nextRow (innerTrack old)
      path := (vertexCodec A).zeroRow old.length
      fuel := (vertexCodec A).zeroRow old.length
      oldCount := oldCountTrack old
      newCount := newCountTrack old
      seenCount := (countCodec A).nextRow (seenCountTrack old)
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [sourceTrack, outerTrack]
      inner_length := by simp [sourceTrack, innerTrack]
      path_length := by simp [sourceTrack]
      fuel_length := by simp [sourceTrack]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by simp [sourceTrack, newCountTrack]
      seenCount_length := by simp [sourceTrack, seenCountTrack] }
  let new := protocolRowOfTracks tracks false newPhase
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  have htracks : old.length = new.length ∧ HasPhase .finalPath old ∧
      sourceTrack new = sourceTrack old ∧
      depthTrack new = depthTrack old ∧
      outerTrack new = outerTrack old ∧
      pathTrack new = (vertexCodec A).zeroRow new.length ∧
      fuelTrack new = (vertexCodec A).zeroRow new.length ∧
      oldCountTrack new = oldCountTrack old ∧
      newCountTrack new = newCountTrack old ∧
      foundTrack new = foundTrack old := by
    refine ⟨?_, hinv.phase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks, sourceTrack]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks, sourceTrack]
    · simp [new, tracks, sourceTrack]
    · simp [new, tracks]
    · simp [new, tracks]
    · have holdFound : foundTrack old = List.replicate old.length false :=
        (foundTrack_eq_replicate_iff old false).2 hinv.found_false
      simpa [new, tracks, sourceTrack] using holdFound.symm
  have hpath : pathTrack old = innerTrack old :=
    hinv.path_eq.trans hinv.inner_eq.symm
  have hfuel : fuelTrack old = depthTrack old :=
    hinv.fuel_eq.trans hinv.depth_eq.symm
  have hselectedCardLt : selected.card < Fintype.card A ^ input.length := by
    calc
      selected.card ≤ (rankPrefix input.length innerIndex).card :=
        Finset.card_le_card hinv.selected_prefix
      _ = innerIndex := card_rankPrefix (Nat.le_of_lt hinv.inner_lt)
      _ < Fintype.card A ^ input.length := hinv.inner_lt
  have hn : 0 < input.length := List.length_pos_of_ne_nil hinput
  have hseenBound : selected.card < (Fintype.card A + 1) ^ input.length :=
    lt_trans hselectedCardLt (rowCapacity_lt_countCapacity (A := A) hn)
  have hseen : (countCodec A).evalSucc .carry
      (seenCountTrack old) (seenCountTrack new) = some .done := by
    apply ((countCodec A).evalSucc_eq_done_iff _ _).2
    constructor
    · calc
        seenCountTrack new = (countCodec A).nextRow (seenCountTrack old) := by
          simp [new, tracks]
        _ = ((countCodec A).increment (seenCountTrack old)).1 := rfl
    · rw [hinv.seen_eq]
      apply Bool.eq_false_iff.mpr
      intro hover
      have hcapacity :=
        (increment_countNumeral_overflow_iff (A := A) hseenBound).1 hover
      have hnextLt : selected.card + 1 < (Fintype.card A + 1) ^ input.length :=
        lt_of_le_of_lt (Nat.succ_le_iff.mpr hselectedCardLt)
          (rowCapacity_lt_countCapacity (A := A) hn)
      exact (Nat.ne_of_lt hnextLt) hcapacity
  have hinner : (vertexCodec A).evalSucc .carry
      (innerTrack old) (innerTrack new) = some innerState := by
    by_cases hover : overflow = true
    · have hcarry := ((vertexCodec A).evalSucc_eq_carry_iff
        (innerTrack old) (innerTrack new)).2
      simpa [innerState, overflow, hover, new, tracks,
        RowNumeral.DigitCodec.nextRow] using
        hcarry ⟨by simp [new, tracks, RowNumeral.DigitCodec.nextRow], by simpa [overflow]⟩
    · have hoverFalse : overflow = false := Bool.eq_false_iff.mpr hover
      have hdone := ((vertexCodec A).evalSucc_eq_done_iff
        (innerTrack old) (innerTrack new)).2
      simpa [innerState, overflow, hoverFalse, new, tracks,
        RowNumeral.DigitCodec.nextRow] using
        hdone ⟨by simp [new, tracks, RowNumeral.DigitCodec.nextRow], by simpa [overflow]⟩
  have hphase : (innerState = .done ∧ newPhase = .finalChoose) ∨
      (innerState = .carry ∧ newPhase = .finalFinish) := by
    by_cases hover : overflow = true
    · right
      simp [innerState, newPhase, hover]
    · left
      have hoverFalse : overflow = false := Bool.eq_false_iff.mpr hover
      simp [innerState, newPhase, hoverFalse]
  have hfinalDone : D.finalDone finalState = false := by
    apply Bool.eq_false_iff.mpr
    intro hdone
    apply hnonfinal
    change D.finalDone
      (D.evalFinal D.finalStart
        (rankRow input.length (⟨innerIndex, hinv.inner_lt⟩ :
          RankVertex A input.length))) = true
    have hinnerRow : innerTrack old =
        rankRow input.length (⟨innerIndex, hinv.inner_lt⟩ :
          RankVertex A input.length) := by
      calc
        innerTrack old = vertexNumeral input.length innerIndex := hinv.inner_eq
        _ = rankRow input.length ⟨innerIndex, hinv.inner_lt⟩ := rfl
    rw [← hinnerRow]
    simpa [finalState] using hdone
  have hspec : IsFinalWitness D old new :=
    isFinalWitness_of_tracks D old new finalState innerState newPhase holdNe
      htracks rfl hpath hfuel hseen hinner hphase (by simp [new]) hfinalDone
  exact ⟨new, protocolStep_of_finalWitness holdNe hspec,
    finalWitness_preserves hinput hinv hspec⟩

/-- A reachable current inner rank has a complete executable witness run.  The run
starts the bounded witness, realizes an exactly `depth`-step padded path, and commits
the current rank to the inner-scan transcript. -/
public theorem reachableWitness_run
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : ChooseInnerInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected)
    (hreachable : (⟨innerIndex, hinv.inner_lt⟩ : RankVertex A input.length) ∈
      protocolReached D input depth) :
    ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
      ((innerIndex + 1 < Fintype.card A ^ input.length ∧
          ChooseInnerInvariant D input new depth oldCount newCount outerIndex
            (innerIndex + 1) (insert ⟨innerIndex, hinv.inner_lt⟩ selected)) ∨
        (innerIndex + 1 = Fintype.card A ^ input.length ∧
          FinishOuterInvariant D input new depth oldCount newCount outerIndex
            (insert ⟨innerIndex, hinv.inner_lt⟩ selected))) := by
  let current : RankVertex A input.length := ⟨innerIndex, hinv.inner_lt⟩
  letI : DecidableRel (rankEdge D input.length) := Classical.decRel _
  have hpath : FiniteReachabilityCounting.PaddedPath
      (rankEdge D input.length) (protocolSourceRank D input) depth current := by
    apply (FiniteReachabilityCounting.mem_reached_iff_paddedPath
      (rankEdge D input.length) (protocolSourceRank D input)).1
    simpa only [protocolReached] using hreachable
  obtain ⟨pathStart, hstartStep, hstartInv⟩ :=
    exists_countingPath_start hinput hinv
  obtain ⟨pathEnd, hpathRun, hendInv⟩ :=
    countingPaddedPath_run hinput hstartInv hpath (Nat.le_refl depth)
  obtain ⟨new, hfinishStep, hresult⟩ :=
    exists_countingPath_finish hinput hendInv
  refine ⟨new, ?_, ?_⟩
  · exact (Relation.ReflTransGen.single hstartStep).trans hpathRun |>.tail hfinishStep
  · simpa [current] using hresult

/-- The final scan has the analogous complete executable witness run.  Its final
completion action additionally checks the current reachable row is nonfinal. -/
public theorem finalReachableWitness_run
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A} {depth count innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinalChooseInvariant D input old depth count innerIndex selected)
    (hreachable : (⟨innerIndex, hinv.inner_lt⟩ : RankVertex A input.length) ∈
      protocolReached D input depth)
    (hnonfinal : ¬ rankFinal D input.length
      (⟨innerIndex, hinv.inner_lt⟩ : RankVertex A input.length)) :
    ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
      ((innerIndex + 1 < Fintype.card A ^ input.length ∧
          FinalChooseInvariant D input new depth count (innerIndex + 1)
            (insert ⟨innerIndex, hinv.inner_lt⟩ selected)) ∨
        (innerIndex + 1 = Fintype.card A ^ input.length ∧
          FinalFinishInvariant D input new depth count
            (insert ⟨innerIndex, hinv.inner_lt⟩ selected))) := by
  let current : RankVertex A input.length := ⟨innerIndex, hinv.inner_lt⟩
  letI : DecidableRel (rankEdge D input.length) := Classical.decRel _
  have hpath : FiniteReachabilityCounting.PaddedPath
      (rankEdge D input.length) (protocolSourceRank D input) depth current := by
    apply (FiniteReachabilityCounting.mem_reached_iff_paddedPath
      (rankEdge D input.length) (protocolSourceRank D input)).1
    simpa only [protocolReached] using hreachable
  obtain ⟨pathStart, hstartStep, hstartInv⟩ :=
    exists_finalPath_start hinput hinv
  obtain ⟨pathEnd, hpathRun, hendInv⟩ :=
    finalPaddedPath_run hinput hstartInv hpath (Nat.le_refl depth)
  have hnonfinal' : ¬ rankFinal D input.length
      (⟨innerIndex, hendInv.inner_lt⟩ : RankVertex A input.length) := by
    simpa using hnonfinal
  obtain ⟨new, hfinishStep, hresult⟩ :=
    exists_finalPath_finish hinput hendInv hnonfinal'
  refine ⟨new, ?_, ?_⟩
  · exact (Relation.ReflTransGen.single hstartStep).trans hpathRun |>.tail hfinishStep
  · simpa [current] using hresult

end CertifiedRowSystem.Complement
