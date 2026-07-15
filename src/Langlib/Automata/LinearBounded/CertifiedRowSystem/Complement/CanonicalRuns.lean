module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.CanonicalRows
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.ProtocolSemantics
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical executable steps of the complement protocol

The soundness proof interprets every accepted scanner action.  This file supplies
the converse local facts used by completeness: from each semantic boundary state,
construct the canonical next protocol row and prove that the executable semantic
relation accepts it.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

/-- Entering an inductive-counting round is always executable on a nonempty input. -/
public theorem exists_beginRound_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A} {depth count : Nat}
    (hinput : input ≠ [])
    (hinv : RoundStartInvariant D input old depth count) :
    ∃ new,
      ProtocolStep D old new ∧
      ChooseInnerInvariant D input new depth count 0 0 0 ∅ := by
  let new : ProtocolRow A := old.map fun cell ↦ { cell with phase := .chooseInner }
  have hphase : HasPhase .chooseInner new := by
    intro cell hcell
    simp only [new, List.mem_map] at hcell
    obtain ⟨oldCell, _, rfl⟩ := hcell
    rfl
  have hcopies : CopiesPayload old new := by
    simp [new, CopiesPayload, sourceTrack, depthTrack, oldCountTrack,
      newCountTrack, seenCountTrack, outerTrack, innerTrack, pathTrack,
      fuelTrack, foundTrack, Function.comp_def]
  have hspec : BeginRoundSpec old new := ⟨hinv.phase, hphase, hcopies⟩
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  refine ⟨new, ?_, beginRound_preserves hinv hspec⟩
  exact ⟨holdNe, Or.inr (Or.inl hspec)⟩

/-- The canonical skip action advances the inner enumeration by one rank. -/
public theorem exists_skipInner_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : ChooseInnerInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected) :
    ∃ new,
      ProtocolStep D old new ∧
      ((innerIndex + 1 < Fintype.card A ^ input.length ∧
          ChooseInnerInvariant D input new depth oldCount newCount outerIndex
            (innerIndex + 1) selected) ∨
        (innerIndex + 1 = Fintype.card A ^ input.length ∧
          FinishOuterInvariant D input new depth oldCount newCount outerIndex selected)) := by
  let found := foundFrom D input ⟨outerIndex, hinv.outer_lt⟩ selected
  let nextInner := (vertexCodec A).nextRow (innerTrack old)
  let nextPhase :=
    if ((vertexCodec A).increment (innerTrack old)).2 then
      ProtocolPhase.finishOuter
    else ProtocolPhase.chooseInner
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := outerTrack old
      inner := nextInner
      path := pathTrack old
      fuel := fuelTrack old
      oldCount := oldCountTrack old
      newCount := newCountTrack old
      seenCount := seenCountTrack old
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [sourceTrack, outerTrack]
      inner_length := by simp [nextInner, sourceTrack, innerTrack]
      path_length := by simp [sourceTrack, pathTrack]
      fuel_length := by simp [sourceTrack, fuelTrack]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by simp [sourceTrack, newCountTrack]
      seenCount_length := by simp [sourceTrack, seenCountTrack] }
  let new := protocolRowOfTracks tracks found nextPhase
  have holdFound : foundTrack old = List.replicate old.length found :=
    (foundTrack_eq_replicate_iff old found).2 hinv.found_eq
  have hspec : SkipInnerSpec old new := by
    refine ⟨hinv.phase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simpa [new, tracks, sourceTrack] using holdFound.symm
    · simp [new, tracks, nextInner]
    · by_cases hover : ((vertexCodec A).increment (innerTrack old)).2 = true
      · simp [new, tracks, nextPhase, hover]
      · simp [new, tracks, nextPhase, hover]
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  refine ⟨new, ?_, skipInner_preserves hinv hspec⟩
  exact ⟨holdNe, Or.inr (Or.inr (Or.inl hspec))⟩

/-- The canonical final-scan skip preserves the replicated auxiliary bit while
advancing the ranked inner row. -/
public theorem exists_finalSkip_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A} {depth count innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinalChooseInvariant D input old depth count innerIndex selected) :
    ∃ new,
      ProtocolStep D old new ∧ HasFound false new ∧
      ((innerIndex + 1 < Fintype.card A ^ input.length ∧
          FinalChooseInvariant D input new depth count (innerIndex + 1) selected) ∨
        (innerIndex + 1 = Fintype.card A ^ input.length ∧
          FinalFinishInvariant D input new depth count selected)) := by
  let nextInner := (vertexCodec A).nextRow (innerTrack old)
  let nextPhase :=
    if ((vertexCodec A).increment (innerTrack old)).2 then
      ProtocolPhase.finalFinish
    else ProtocolPhase.finalChoose
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := outerTrack old
      inner := nextInner
      path := pathTrack old
      fuel := fuelTrack old
      oldCount := oldCountTrack old
      newCount := newCountTrack old
      seenCount := seenCountTrack old
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [sourceTrack, outerTrack]
      inner_length := by simp [nextInner, sourceTrack, innerTrack]
      path_length := by simp [sourceTrack, pathTrack]
      fuel_length := by simp [sourceTrack, fuelTrack]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by simp [sourceTrack, newCountTrack]
      seenCount_length := by simp [sourceTrack, seenCountTrack] }
  let new := protocolRowOfTracks tracks false nextPhase
  have holdFound : foundTrack old = List.replicate old.length false :=
    (foundTrack_eq_replicate_iff old false).2 hinv.found_false
  have hspec : FinalSkipSpec old new := by
    refine ⟨hinv.phase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simpa [new, tracks, sourceTrack] using holdFound.symm
    · simp [new, tracks, nextInner]
    · by_cases hover : ((vertexCodec A).increment (innerTrack old)).2 = true
      · simp [new, tracks, nextPhase, hover]
      · simp [new, tracks, nextPhase, hover]
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  refine ⟨new, ?_, by simp [new], finalSkip_preserves hinv hspec⟩
  exact ⟨holdNe, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl hspec))))))))⟩

/-- Once the final scan has selected the complete reachable layer, its exact-count
check has a canonical accepting successor. -/
public theorem exists_finalFinish_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A} {depth count : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinalFinishInvariant D input old depth count selected)
    (hselected : selected = protocolReached D input depth) :
    ∃ new, ProtocolStep D old new ∧ HasPhase .accept new := by
  let new : ProtocolRow A := old.map fun cell ↦ { cell with phase := .accept }
  have hselectedCard : selected.card = count := by
    rw [hselected, ← hinv.count_exact]
  have hseen : seenCountTrack old = oldCountTrack old := by
    rw [hinv.seen_eq, hinv.count_eq, hselectedCard]
  have hphase : HasPhase .accept new := by
    intro cell hcell
    simp only [new, List.mem_map] at hcell
    obtain ⟨oldCell, _, rfl⟩ := hcell
    rfl
  have hsource : sourceTrack new = sourceTrack old := by
    simp [new, sourceTrack, Function.comp_def]
  have hspec : FinalFinishSpec old new :=
    ⟨hinv.phase, hphase, hseen, hsource⟩
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  refine ⟨new, ?_, hphase⟩
  refine ⟨holdNe, ?_⟩
  aesop

/-- The exact round boundary has an executable successor.  Equality selects the
plateau branch; strict growth selects the next counting round. -/
public theorem exists_finishRound_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A} {depth oldCount newCount : Nat}
    (hinput : input ≠ [])
    (hinv : FinishRoundInvariant D input old depth oldCount newCount) :
    ∃ new,
      ProtocolStep D old new ∧
      (FinalChooseInvariant D input new depth oldCount 0 ∅ ∨
        RoundStartInvariant D input new (depth + 1) newCount) := by
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  let zeroVertex := (vertexCodec A).zeroRow old.length
  let zeroCount := (countCodec A).zeroRow old.length
  by_cases hcounts : oldCount = newCount
  · let tracks : ProtocolTrackLists A :=
      { source := sourceTrack old
        depth := depthTrack old
        outer := zeroVertex
        inner := zeroVertex
        path := zeroVertex
        fuel := zeroVertex
        oldCount := oldCountTrack old
        newCount := zeroCount
        seenCount := zeroCount
        depth_length := by simp [sourceTrack, depthTrack]
        outer_length := by simp [zeroVertex, sourceTrack]
        inner_length := by simp [zeroVertex, sourceTrack]
        path_length := by simp [zeroVertex, sourceTrack]
        fuel_length := by simp [zeroVertex, sourceTrack]
        oldCount_length := by simp [sourceTrack, oldCountTrack]
        newCount_length := by simp [zeroCount, sourceTrack]
        seenCount_length := by simp [zeroCount, sourceTrack] }
    let new := protocolRowOfTracks tracks false .finalChoose
    have hcountRows : oldCountTrack old = newCountTrack old := by
      rw [hinv.oldCount_eq, hinv.newCount_eq, hcounts]
    have hspec : FinishRoundSpec old new := by
      refine ⟨hinv.phase, ?_, ?_, Or.inl ?_⟩
      · simp [new, tracks]
      · simp [RoundResetSpec, new, tracks, zeroVertex, zeroCount, sourceTrack]
      · refine ⟨hcountRows, ?_, ?_, ?_⟩ <;> simp [new, tracks]
    refine ⟨new, ?_, finishRound_preserves hinput hinv hspec⟩
    refine ⟨holdNe, ?_⟩
    aesop
  · have hcountLt : oldCount < newCount := by
      have hcard := Finset.card_le_card (protocolReached_mono D input depth)
      rw [← hinv.oldCount_exact, ← hinv.nextCount_exact] at hcard
      omega
    have hn : 0 < input.length := List.length_pos_of_ne_nil hinput
    have holdBound : oldCount < (Fintype.card A + 1) ^ input.length :=
      lt_of_le_of_lt hinv.oldCount_le (rowCapacity_lt_countCapacity (A := A) hn)
    have hnewBound : newCount < (Fintype.card A + 1) ^ input.length :=
      lt_of_le_of_lt hinv.newCount_le (rowCapacity_lt_countCapacity (A := A) hn)
    have hless :
        (countCodec A).rowsLess (oldCountTrack old) (newCountTrack old) := by
      rw [hinv.oldCount_eq, hinv.newCount_eq]
      apply ((countCodec A).compareRows_eq_lt_iff (by simp)).2
      simpa [value_countNumeral (A := A) holdBound,
        value_countNumeral (A := A) hnewBound] using hcountLt
    have hdepthSuccLt : depth + 1 < Fintype.card A ^ input.length :=
      depth_succ_lt_capacity_of_card_lt D input depth (by
        rwa [← hinv.oldCount_exact, ← hinv.nextCount_exact])
    have hdepthNoOverflow :
        ((vertexCodec A).increment (depthTrack old)).2 = false := by
      rw [hinv.depth_eq]
      apply Bool.eq_false_iff.mpr
      intro hover
      have heq := (increment_vertexNumeral_overflow_iff (A := A)
        hinv.depth_lt).1 hover
      omega
    let nextDepth := (vertexCodec A).nextRow (depthTrack old)
    let tracks : ProtocolTrackLists A :=
      { source := sourceTrack old
        depth := nextDepth
        outer := zeroVertex
        inner := zeroVertex
        path := zeroVertex
        fuel := zeroVertex
        oldCount := newCountTrack old
        newCount := zeroCount
        seenCount := zeroCount
        depth_length := by simp [nextDepth, sourceTrack, depthTrack]
        outer_length := by simp [zeroVertex, sourceTrack]
        inner_length := by simp [zeroVertex, sourceTrack]
        path_length := by simp [zeroVertex, sourceTrack]
        fuel_length := by simp [zeroVertex, sourceTrack]
        oldCount_length := by simp [sourceTrack, newCountTrack]
        newCount_length := by simp [zeroCount, sourceTrack]
        seenCount_length := by simp [zeroCount, sourceTrack] }
    let new := protocolRowOfTracks tracks false .roundStart
    have hspec : FinishRoundSpec old new := by
      refine ⟨hinv.phase, ?_, ?_, Or.inr ?_⟩
      · simp [new, tracks]
      · simp [RoundResetSpec, new, tracks, zeroVertex, zeroCount, sourceTrack]
      · refine ⟨hless, ?_, ?_, ?_, ?_⟩
        · simp [new, tracks]
        · simp [new, tracks, nextDepth]
        · exact hdepthNoOverflow
        · simp [new, tracks]
    refine ⟨new, ?_, finishRound_preserves hinput hinv hspec⟩
    refine ⟨holdNe, ?_⟩
    aesop

/-- After the canonical inner scan has selected exactly the old reachable layer,
the current outer vertex can be committed executably. -/
public theorem exists_finishOuter_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old : ProtocolRow A}
    {depth oldCount newCount outerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinishOuterInvariant D input old depth oldCount newCount outerIndex selected)
    (hselected : selected = protocolReached D input depth) :
    ∃ new,
      ProtocolStep D old new ∧
      ((outerIndex + 1 < Fintype.card A ^ input.length ∧
          ChooseInnerInvariant D input new depth oldCount
            (classifiedPrefix D input depth (outerIndex + 1)).card
            (outerIndex + 1) 0 ∅) ∨
        (outerIndex + 1 = Fintype.card A ^ input.length ∧
          FinishRoundInvariant D input new depth oldCount
            (classifiedPrefix D input depth (outerIndex + 1)).card)) := by
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  have hn : 0 < input.length := List.length_pos_of_ne_nil hinput
  have hselectedCard : selected.card = oldCount := by
    rw [hselected, ← hinv.oldCount_exact]
  have hseenExact : seenCountTrack old = oldCountTrack old := by
    rw [hinv.seen_eq, hinv.oldCount_eq, hselectedCard]
  let current : RankVertex A input.length := ⟨outerIndex, hinv.outer_lt⟩
  let nextOuter := (vertexCodec A).nextRow (outerTrack old)
  let zeroVertex := (vertexCodec A).zeroRow old.length
  let zeroCount := (countCodec A).zeroRow old.length
  let nextPhase :=
    if ((vertexCodec A).increment (outerTrack old)).2 then
      ProtocolPhase.finishRound
    else ProtocolPhase.chooseInner
  let nextCountTrack :=
    if current ∈ protocolReached D input (depth + 1) then
      (countCodec A).nextRow (newCountTrack old)
    else newCountTrack old
  let tracks : ProtocolTrackLists A :=
    { source := sourceTrack old
      depth := depthTrack old
      outer := nextOuter
      inner := zeroVertex
      path := zeroVertex
      fuel := zeroVertex
      oldCount := oldCountTrack old
      newCount := nextCountTrack
      seenCount := zeroCount
      depth_length := by simp [sourceTrack, depthTrack]
      outer_length := by simp [nextOuter, sourceTrack, outerTrack]
      inner_length := by simp [zeroVertex, sourceTrack]
      path_length := by simp [zeroVertex, sourceTrack]
      fuel_length := by simp [zeroVertex, sourceTrack]
      oldCount_length := by simp [sourceTrack, oldCountTrack]
      newCount_length := by
        by_cases hcurrent : current ∈ protocolReached D input (depth + 1) <;>
          simp [nextCountTrack, hcurrent, sourceTrack, newCountTrack]
      seenCount_length := by simp [zeroCount, sourceTrack] }
  let new := protocolRowOfTracks tracks false nextPhase
  have hnewCountLt : newCount < Fintype.card A ^ input.length := by
    calc
      newCount = (classifiedPrefix D input depth outerIndex).card :=
        hinv.classified_exact
      _ ≤ (rankPrefix (A := A) input.length outerIndex).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = outerIndex := card_rankPrefix (Nat.le_of_lt hinv.outer_lt)
      _ < Fintype.card A ^ input.length := hinv.outer_lt
  have hcountNoOverflow :
      ((countCodec A).increment (newCountTrack old)).2 = false := by
    rw [hinv.newCount_eq]
    apply Bool.eq_false_iff.mpr
    intro hover
    have hbound : newCount < (Fintype.card A + 1) ^ input.length :=
      lt_of_le_of_lt hinv.newCount_le (rowCapacity_lt_countCapacity (A := A) hn)
    have heq := (increment_countNumeral_overflow_iff (A := A) hbound).1 hover
    have hcapacity := rowCapacity_lt_countCapacity (A := A) hn
    omega
  have hspec : FinishOuterSpec old new := by
    refine ⟨hinv.phase, hseenExact, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks]
    · simp [new, tracks, nextOuter]
    · simp [OuterResetSpec, new, tracks, zeroVertex, zeroCount, sourceTrack]
    · by_cases hcurrent : current ∈ protocolReached D input (depth + 1)
      · left
        have hflag : foundFrom D input current selected = true := by
          rw [hselected]
          exact (foundFrom_full_iff D input depth current).2 hcurrent
        have hfound : HasFound true old := by
          simpa [current, hflag] using hinv.found_eq
        refine ⟨hfound, ?_, hcountNoOverflow⟩
        simp [new, tracks, nextCountTrack, hcurrent]
      · right
        have hflag : foundFrom D input current selected = false := by
          apply Bool.eq_false_iff.mpr
          intro htrue
          have : current ∈ protocolReached D input (depth + 1) :=
            (foundFrom_full_iff D input depth current).1 (by
              simpa [hselected] using htrue)
          exact hcurrent this
        have hfound : HasFound false old := by
          simpa [current, hflag] using hinv.found_eq
        refine ⟨hfound, ?_⟩
        simp [new, tracks, nextCountTrack, hcurrent]
    · by_cases hover : ((vertexCodec A).increment (outerTrack old)).2 = true
      · simp [new, tracks, nextPhase, hover]
      · simp [new, tracks, nextPhase, hover]
  refine ⟨new, ?_, ?_⟩
  · refine ⟨holdNe, ?_⟩
    aesop
  · simpa only using finishOuter_preserves hinput hinv hspec

end CertifiedRowSystem.Complement
