module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.ProtocolSemantics
import Mathlib.Tactic

@[expose]
public section

/-!
# Semantic preservation for bounded path witnesses

This module connects the path-action specifications to the ranked finite-graph
invariants used by the inductive-counting proof.  It is kept separate from
`ProtocolSemantics.lean` so the declarative invariant layer does not depend on the
action-by-action preservation proof.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

private theorem scanBits_some_eq_some_iff (expected result : Bool) (bits : List Bool) :
    scanBits (.value expected) bits = .value result ↔
      result = expected ∧ ∀ bit ∈ bits, bit = expected := by
  induction bits with
  | nil => simp [scanBits, eq_comm]
  | cons bit bits ih =>
      by_cases hbit : bit = expected
      · subst bit
        simp [scanBits, UniformScan.step, ih]
      · simp [scanBits, UniformScan.step, hbit]

private theorem scanBits_none_eq_some_iff {bits : List Bool} (hne : bits ≠ [])
    (result : Bool) :
    scanBits .start bits = .value result ↔ ∀ bit ∈ bits, bit = result := by
  obtain ⟨bit, bits, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [scanBits]
  change scanBits (.value bit) bits = .value result ↔ _
  rw [scanBits_some_eq_some_iff]
  simp only [List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨hresult, htail⟩
    exact ⟨hresult.symm, fun x hx ↦ (htail x hx).trans hresult.symm⟩
  · rintro ⟨hhead, htail⟩
    exact ⟨hhead.symm, fun x hx ↦ (htail x hx).trans hhead.symm⟩

private theorem scanPhases_some_eq_some_iff
    (expected result : ProtocolPhase) (phases : List ProtocolPhase) :
    scanPhases (.value expected) phases = .value result ↔
      result = expected ∧ ∀ phase ∈ phases, phase = expected := by
  induction phases with
  | nil => simp [scanPhases, eq_comm]
  | cons phase phases ih =>
      by_cases hphase : phase = expected
      · subst phase
        simp [scanPhases, UniformScan.step, ih]
      · simp [scanPhases, UniformScan.step, hphase]

private theorem scanPhases_none_eq_some_iff
    {phases : List ProtocolPhase} (hne : phases ≠ []) (result : ProtocolPhase) :
    scanPhases .start phases = .value result ↔
      ∀ phase ∈ phases, phase = result := by
  obtain ⟨phase, phases, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [scanPhases]
  change scanPhases (.value phase) phases = .value result ↔ _
  rw [scanPhases_some_eq_some_iff]
  simp only [List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨hresult, htail⟩
    exact ⟨hresult.symm, fun x hx ↦ (htail x hx).trans hresult.symm⟩
  · rintro ⟨hhead, htail⟩
    exact ⟨hhead.symm, fun x hx ↦ (htail x hx).trans hhead.symm⟩

private theorem scanBits_none_eq_some_iff_hasFound
    {row : ProtocolRow A} (hne : row ≠ []) (found : Bool) :
    scanBits .start (row.map (·.found)) = .value found ↔ HasFound found row := by
  rw [scanBits_none_eq_some_iff (by simpa using hne)]
  simp [HasFound]

private theorem scanPhases_none_eq_some_iff_hasPhase
    {row : ProtocolRow A} (hne : row ≠ []) (phase : ProtocolPhase) :
    scanPhases .start (row.map (·.phase)) = .value phase ↔ HasPhase phase row := by
  rw [scanPhases_none_eq_some_iff (by simpa using hne)]
  simp [HasPhase]

private theorem vertexNumeral_eq_rankRow (n : Nat) (v : RankVertex A n) :
    vertexNumeral n v.val = rankRow n v := rfl

private theorem foundFrom_insert
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (outer inner : RankVertex A input.length)
    (selected : Finset (RankVertex A input.length)) :
    foundFrom D input outer (insert inner selected) =
      (foundFrom D input outer selected ||
        decide (inner = outer ∨ rankEdge D input.length inner outer)) := by
  apply Bool.eq_iff_iff.mpr
  simp [foundFrom]
  exact or_comm

private theorem stepDone_iff_of_evalUnit
    (D : CertifiedRowSystem I A Unit Q F) (old new : List A) (q : Q)
    (heval : D.evalStep D.stepStart old new (List.replicate old.length ()) = some q) :
    D.stepDone q = true ↔ D.RowStep old new := by
  constructor
  · intro hdone
    exact (rowStep_iff_evalUnit D old new).2 ⟨q, heval, hdone⟩
  · intro hstep
    obtain ⟨q', heval', hdone⟩ := (rowStep_iff_evalUnit D old new).1 hstep
    have hq : q' = q := Option.some.inj (heval'.symm.trans heval)
    simpa [hq] using hdone

/-! ## Starting a witness -/

/-- Starting an ordinary witness copies the round transcript, resets fuel to zero, and
places the path at the ranked source vertex. -/
public theorem startsPath_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinv : ChooseInnerInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected)
    (hstep : StartsPath .chooseInner .path old new) :
    CountingPathInvariant D input new depth oldCount newCount outerIndex innerIndex
      selected (protocolSourceRank D input).val 0 := by
  rcases hstep.spec with
    ⟨hlength, _holdPhase, hphase, hsource, hdepth, houter, hinner, hpath,
      hfuel, holdCount, hnewCount, hseen, hfound⟩
  have hlen : new.length = input.length := hlength.symm.trans hinv.length_eq
  refine
    { toInnerScanTranscript :=
        { toRoundTracks :=
            { length_eq := hlen
              source_eq := hsource.trans hinv.source_eq
              depth_eq := hdepth.trans hinv.depth_eq
              oldCount_eq := holdCount.trans hinv.oldCount_eq
              newCount_eq := hnewCount.trans hinv.newCount_eq
              depth_lt := hinv.depth_lt
              oldCount_le := hinv.oldCount_le
              newCount_le := hinv.newCount_le
              oldCount_exact := hinv.oldCount_exact }
          outer_lt := hinv.outer_lt
          inner_le := hinv.inner_le
          outer_eq := houter.trans hinv.outer_eq
          inner_eq := hinner.trans hinv.inner_eq
          seen_eq := hseen.trans hinv.seen_eq
          selected_reachable := hinv.selected_reachable
          selected_prefix := hinv.selected_prefix
          classified_exact := hinv.classified_exact
          found_eq := hasFound_of_foundTrack_eq hinv.found_eq hfound }
      inner_lt := hinv.inner_lt
      phase := hphase
      path_lt := (protocolSourceRank D input).isLt
      fuel_le := Nat.zero_le depth
      path_eq := by
        rw [hpath, hinv.source_eq, vertexNumeral_eq_rankRow,
          rankRow_protocolSourceRank]
      fuel_eq := by simpa [hlen] using hfuel
      path_reachable := by simp }

/-- The final all-nonfinal scan starts the same bounded witness at the source vertex. -/
public theorem finalStartsPath_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A} {depth count innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinv : FinalChooseInvariant D input old depth count innerIndex selected)
    (hstep : StartsPath .finalChoose .finalPath old new) :
    FinalPathInvariant D input new depth count innerIndex selected
      (protocolSourceRank D input).val 0 := by
  rcases hstep.spec with
    ⟨hlength, _holdPhase, hphase, hsource, hdepth, _houter, hinner, hpath,
      hfuel, holdCount, _hnewCount, hseen, _hfound⟩
  have hlen : new.length = input.length := hlength.symm.trans hinv.length_eq
  refine
    { toFinalScanTranscript :=
        { toFinalTracks :=
            { length_eq := hlen
              source_eq := hsource.trans hinv.source_eq
              depth_eq := hdepth.trans hinv.depth_eq
              count_eq := holdCount.trans hinv.count_eq
              depth_lt := hinv.depth_lt
              count_le := hinv.count_le
              count_exact := hinv.count_exact
              plateau := hinv.plateau
              found_false := hasFound_of_foundTrack_eq hinv.found_false _hfound }
          inner_le := hinv.inner_le
          inner_eq := hinner.trans hinv.inner_eq
          seen_eq := hseen.trans hinv.seen_eq
          selected_reachable := hinv.selected_reachable
          selected_prefix := hinv.selected_prefix
          selected_nonfinal := hinv.selected_nonfinal }
      inner_lt := hinv.inner_lt
      phase := hphase
      path_lt := (protocolSourceRank D input).isLt
      fuel_le := Nat.zero_le depth
      path_eq := by
        rw [hpath, hinv.source_eq, vertexNumeral_eq_rankRow,
          rankRow_protocolSourceRank]
      fuel_eq := by simpa [hlen] using hfuel
      path_reachable := by simp }

/-! ## Extending a witness -/

/-- One accepted ordinary path action advances fuel by one and preserves bounded
reachability of the path rank. -/
public theorem pathStep_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex pathIndex fuel : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinv : CountingPathInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected pathIndex fuel)
    (hstep : IsPathStep D .path old new) :
    ∃ pathIndex', CountingPathInvariant D input new depth oldCount newCount
      outerIndex innerIndex selected pathIndex' (fuel + 1) := by
  have hpersistent := hstep.persistent_spec
  rcases hpersistent with
    ⟨hlength, _holdPhase, hphase, hsource, hdepth, houter, hinner,
      holdCount, hnewCount, hseen, hfound⟩
  rcases hstep with ⟨_hlocal, hfuelSucc, hfuelDepth, hpathStep⟩
  have hlen : new.length = input.length := hlength.symm.trans hinv.length_eq
  have hfuelCapacity : fuel < Fintype.card A ^ input.length :=
    lt_of_le_of_lt hinv.fuel_le hinv.depth_lt
  have hcompareLength : (fuelTrack old).length = (depthTrack old).length := by
    simp [fuelTrack, depthTrack]
  have hvalueLt :=
    ((vertexCodec A).compareRows_eq_lt_iff hcompareLength).1 hfuelDepth
  have hfuelLt : fuel < depth := by
    rw [hinv.fuel_eq, hinv.depth_eq] at hvalueLt
    simpa [value_vertexNumeral (A := A) hfuelCapacity,
      value_vertexNumeral (A := A) hinv.depth_lt] using hvalueLt
  have hfuelNext := ((vertexCodec A).evalSucc_eq_done_iff
    (fuelTrack old) (fuelTrack new)).1 hfuelSucc |>.1
  have hfuelEq : fuelTrack new = vertexNumeral input.length (fuel + 1) := by
    calc
      fuelTrack new = (vertexCodec A).nextRow (fuelTrack old) := by
        simpa [RowNumeral.DigitCodec.nextRow] using hfuelNext
      _ = vertexNumeral input.length (fuel + 1) := by
        rw [hinv.fuel_eq, nextRow_vertexNumeral]
  have hpathLength : (pathTrack new).length = input.length := by
    simp [pathTrack, hlen]
  let nextRank := rankOfRow input.length (pathTrack new) hpathLength
  have hnextRankRow : rankRow input.length nextRank = pathTrack new := by
    exact rankRow_rankOfRow input.length (pathTrack new) hpathLength
  let oldRank : RankVertex A input.length := ⟨pathIndex, hinv.path_lt⟩
  have holdRankRow : rankRow input.length oldRank = pathTrack old := by
    rw [← vertexNumeral_eq_rankRow]
    exact hinv.path_eq.symm
  have hpathReachable : nextRank ∈ protocolReached D input (fuel + 1) := by
    rw [protocolReached_succ]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hpathStep with hsame | hedge
    · left
      have hrank : nextRank = oldRank := by
        apply (rankRowEquiv (A := A) input.length).injective
        apply Subtype.ext
        exact hnextRankRow.trans (hsame.trans holdRankRow.symm)
      simpa [hrank, oldRank] using hinv.path_reachable
    · right
      refine ⟨oldRank, by simpa [oldRank] using hinv.path_reachable, ?_⟩
      change D.RowStep (rankRow input.length oldRank) (rankRow input.length nextRank)
      simpa [holdRankRow, hnextRankRow] using hedge
  refine ⟨nextRank.val, ?_⟩
  refine
    { toInnerScanTranscript :=
        { toRoundTracks :=
            { length_eq := hlen
              source_eq := hsource.trans hinv.source_eq
              depth_eq := hdepth.trans hinv.depth_eq
              oldCount_eq := holdCount.trans hinv.oldCount_eq
              newCount_eq := hnewCount.trans hinv.newCount_eq
              depth_lt := hinv.depth_lt
              oldCount_le := hinv.oldCount_le
              newCount_le := hinv.newCount_le
              oldCount_exact := hinv.oldCount_exact }
          outer_lt := hinv.outer_lt
          inner_le := hinv.inner_le
          outer_eq := houter.trans hinv.outer_eq
          inner_eq := hinner.trans hinv.inner_eq
          seen_eq := hseen.trans hinv.seen_eq
          selected_reachable := hinv.selected_reachable
          selected_prefix := hinv.selected_prefix
          classified_exact := hinv.classified_exact
          found_eq := hasFound_of_foundTrack_eq hinv.found_eq hfound }
      inner_lt := hinv.inner_lt
      phase := hphase
      path_lt := nextRank.isLt
      fuel_le := Nat.succ_le_iff.mpr hfuelLt
      path_eq := by
        rw [vertexNumeral_eq_rankRow]
        exact hnextRankRow.symm
      fuel_eq := hfuelEq
      path_reachable := hpathReachable }

/-- One accepted final-scan path action has the same ranked reachability effect. -/
public theorem finalPathStep_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A}
    {depth count innerIndex pathIndex fuel : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinv : FinalPathInvariant D input old depth count innerIndex selected
      pathIndex fuel)
    (hstep : IsPathStep D .finalPath old new) :
    ∃ pathIndex', FinalPathInvariant D input new depth count innerIndex selected
      pathIndex' (fuel + 1) := by
  have hpersistent := hstep.persistent_spec
  rcases hpersistent with
    ⟨hlength, _holdPhase, hphase, hsource, hdepth, _houter, hinner,
      holdCount, _hnewCount, hseen, hfound⟩
  rcases hstep with ⟨_hlocal, hfuelSucc, hfuelDepth, hpathStep⟩
  have hlen : new.length = input.length := hlength.symm.trans hinv.length_eq
  have hfuelCapacity : fuel < Fintype.card A ^ input.length :=
    lt_of_le_of_lt hinv.fuel_le hinv.depth_lt
  have hcompareLength : (fuelTrack old).length = (depthTrack old).length := by
    simp [fuelTrack, depthTrack]
  have hvalueLt :=
    ((vertexCodec A).compareRows_eq_lt_iff hcompareLength).1 hfuelDepth
  have hfuelLt : fuel < depth := by
    rw [hinv.fuel_eq, hinv.depth_eq] at hvalueLt
    simpa [value_vertexNumeral (A := A) hfuelCapacity,
      value_vertexNumeral (A := A) hinv.depth_lt] using hvalueLt
  have hfuelNext := ((vertexCodec A).evalSucc_eq_done_iff
    (fuelTrack old) (fuelTrack new)).1 hfuelSucc |>.1
  have hfuelEq : fuelTrack new = vertexNumeral input.length (fuel + 1) := by
    calc
      fuelTrack new = (vertexCodec A).nextRow (fuelTrack old) := by
        simpa [RowNumeral.DigitCodec.nextRow] using hfuelNext
      _ = vertexNumeral input.length (fuel + 1) := by
        rw [hinv.fuel_eq, nextRow_vertexNumeral]
  have hpathLength : (pathTrack new).length = input.length := by
    simp [pathTrack, hlen]
  let nextRank := rankOfRow input.length (pathTrack new) hpathLength
  have hnextRankRow : rankRow input.length nextRank = pathTrack new := by
    exact rankRow_rankOfRow input.length (pathTrack new) hpathLength
  let oldRank : RankVertex A input.length := ⟨pathIndex, hinv.path_lt⟩
  have holdRankRow : rankRow input.length oldRank = pathTrack old := by
    rw [← vertexNumeral_eq_rankRow]
    exact hinv.path_eq.symm
  have hpathReachable : nextRank ∈ protocolReached D input (fuel + 1) := by
    rw [protocolReached_succ]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hpathStep with hsame | hedge
    · left
      have hrank : nextRank = oldRank := by
        apply (rankRowEquiv (A := A) input.length).injective
        apply Subtype.ext
        exact hnextRankRow.trans (hsame.trans holdRankRow.symm)
      simpa [hrank, oldRank] using hinv.path_reachable
    · right
      refine ⟨oldRank, by simpa [oldRank] using hinv.path_reachable, ?_⟩
      change D.RowStep (rankRow input.length oldRank) (rankRow input.length nextRank)
      simpa [holdRankRow, hnextRankRow] using hedge
  refine ⟨nextRank.val, ?_⟩
  refine
    { toFinalScanTranscript :=
        { toFinalTracks :=
            { length_eq := hlen
              source_eq := hsource.trans hinv.source_eq
              depth_eq := hdepth.trans hinv.depth_eq
              count_eq := holdCount.trans hinv.count_eq
              depth_lt := hinv.depth_lt
              count_le := hinv.count_le
              count_exact := hinv.count_exact
              plateau := hinv.plateau
              found_false := hasFound_of_foundTrack_eq hinv.found_false hfound }
          inner_le := hinv.inner_le
          inner_eq := hinner.trans hinv.inner_eq
          seen_eq := hseen.trans hinv.seen_eq
          selected_reachable := hinv.selected_reachable
          selected_prefix := hinv.selected_prefix
          selected_nonfinal := hinv.selected_nonfinal }
      inner_lt := hinv.inner_lt
      phase := hphase
      path_lt := nextRank.isLt
      fuel_le := Nat.succ_le_iff.mpr hfuelLt
      path_eq := by
        rw [vertexNumeral_eq_rankRow]
        exact hnextRankRow.symm
      fuel_eq := hfuelEq
      path_reachable := hpathReachable }

/-! ## Completing a witness -/

/-- Completing an ordinary witness inserts the current inner rank into the selected
transcript and advances the canonical inner enumeration. -/
public theorem finishWitness_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex pathIndex fuel : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : CountingPathInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected pathIndex fuel)
    (hstep : IsFinishWitness D old new) :
    (innerIndex + 1 < Fintype.card A ^ input.length ∧
      ChooseInnerInvariant D input new depth oldCount newCount outerIndex
        (innerIndex + 1) (insert ⟨innerIndex, hinv.inner_lt⟩ selected)) ∨
    (innerIndex + 1 = Fintype.card A ^ input.length ∧
      FinishOuterInvariant D input new depth oldCount newCount outerIndex
        (insert ⟨innerIndex, hinv.inner_lt⟩ selected)) := by
  have hpersistent := hstep.persistent_spec
  rcases hpersistent with
    ⟨hlength, _holdPhase, hsource, hdepth, houter, hpathZero, hfuelZero,
      holdCount, hnewCount⟩
  rcases hstep with
    ⟨edgeState, innerState, oldFound, newFound, newPhase, _hlocal, hedge,
      hpathInner, hfuelDepth, hseenSucc, hinnerSucc, hinnerPhase,
      holdFoundScan, hnewFoundScan, hnewPhaseScan, hfound⟩
  have hlen : new.length = input.length := hlength.symm.trans hinv.length_eq
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  have hnewNe : new ≠ [] := row_ne_nil_of_length_eq hlen hinput
  have hfuelCapacity : fuel < Fintype.card A ^ input.length :=
    lt_of_le_of_lt hinv.fuel_le hinv.depth_lt
  have hpathIndex : pathIndex = innerIndex :=
    (vertexNumeral_injective (A := A) hinv.path_lt hinv.inner_lt).1
      (hinv.path_eq.symm.trans (hpathInner.trans hinv.inner_eq))
  have hfuelIndex : fuel = depth :=
    (vertexNumeral_injective (A := A) hfuelCapacity hinv.depth_lt).1
      (hinv.fuel_eq.symm.trans (hfuelDepth.trans hinv.depth_eq))
  let current : RankVertex A input.length := ⟨innerIndex, hinv.inner_lt⟩
  let outer : RankVertex A input.length := ⟨outerIndex, hinv.outer_lt⟩
  have hcurrentReachable : current ∈ protocolReached D input depth := by
    simpa [current, hpathIndex, hfuelIndex] using hinv.path_reachable
  have hcurrentNotMem : current ∉ selected := by
    intro hmem
    have hpref := hinv.selected_prefix hmem
    rw [mem_rankPrefix] at hpref
    exact (Nat.lt_irrefl innerIndex) (by simpa [current] using hpref)
  have hinsertCard : (insert current selected).card = selected.card + 1 :=
    Finset.card_insert_of_notMem hcurrentNotMem
  have hselectedReachable :
      insert current selected ⊆ protocolReached D input depth := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hcurrentReachable
    · exact hinv.selected_reachable hv
  have hselectedPrefix :
      insert current selected ⊆ rankPrefix input.length (innerIndex + 1) := by
    intro v hv
    rw [mem_rankPrefix]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp [current]
    · have hpref := hinv.selected_prefix hv
      rw [mem_rankPrefix] at hpref
      omega
  have hseenNext := ((countCodec A).evalSucc_eq_done_iff
    (seenCountTrack old) (seenCountTrack new)).1 hseenSucc |>.1
  have hseenEq :
      seenCountTrack new = countNumeral input.length (insert current selected).card := by
    calc
      seenCountTrack new = (countCodec A).nextRow (seenCountTrack old) := by
        simpa [RowNumeral.DigitCodec.nextRow] using hseenNext
      _ = countNumeral input.length (selected.card + 1) := by
        rw [hinv.seen_eq, nextRow_countNumeral]
      _ = countNumeral input.length (insert current selected).card := by
        rw [hinsertCard]
  have hinnerNext : innerTrack new = vertexNumeral input.length (innerIndex + 1) := by
    rcases hinnerPhase with hdone | hcarry
    · have hnext := ((vertexCodec A).evalSucc_eq_done_iff
        (innerTrack old) (innerTrack new)).1 (by simpa [hdone.1] using hinnerSucc) |>.1
      calc
        innerTrack new = (vertexCodec A).nextRow (innerTrack old) := by
          simpa [RowNumeral.DigitCodec.nextRow] using hnext
        _ = vertexNumeral input.length (innerIndex + 1) := by
          rw [hinv.inner_eq, nextRow_vertexNumeral]
    · have hnext := ((vertexCodec A).evalSucc_eq_carry_iff
        (innerTrack old) (innerTrack new)).1 (by simpa [hcarry.1] using hinnerSucc) |>.1
      calc
        innerTrack new = (vertexCodec A).nextRow (innerTrack old) := by
          simpa [RowNumeral.DigitCodec.nextRow] using hnext
        _ = vertexNumeral input.length (innerIndex + 1) := by
          rw [hinv.inner_eq, nextRow_vertexNumeral]
  have hphaseNew : HasPhase newPhase new :=
    (scanPhases_none_eq_some_iff_hasPhase hnewNe newPhase).1 hnewPhaseScan
  have holdFoundExpected :
      scanBits .start (old.map (·.found)) =
        .value (foundFrom D input outer selected) :=
    (scanBits_none_eq_some_iff_hasFound holdNe _).2 hinv.found_eq
  have holdFoundEq : oldFound = foundFrom D input outer selected :=
    UniformScan.value.inj (holdFoundScan.symm.trans holdFoundExpected)
  have hinnerRow : innerTrack old = rankRow input.length current := by
    calc
      innerTrack old = vertexNumeral input.length innerIndex := hinv.inner_eq
      _ = rankRow input.length current := rfl
  have houterRow : outerTrack old = rankRow input.length outer := by
    calc
      outerTrack old = vertexNumeral input.length outerIndex := hinv.outer_eq
      _ = rankRow input.length outer := rfl
  have hinnerOuterIff : innerTrack old = outerTrack old ↔ current = outer := by
    rw [hinnerRow, houterRow]
    constructor
    · intro hrows
      apply (rankRowEquiv (A := A) input.length).injective
      exact Subtype.ext hrows
    · intro h
      exact congrArg (rankRow input.length) h
  have hedgeUnit :
      D.evalStep D.stepStart (innerTrack old) (outerTrack old)
          (List.replicate (innerTrack old).length ()) = some edgeState := by
    simpa [innerTrack] using hedge
  have hedgeIff : D.stepDone edgeState = true ↔
      rankEdge D input.length current outer := by
    rw [stepDone_iff_of_evalUnit D _ _ _ hedgeUnit]
    change D.RowStep (innerTrack old) (outerTrack old) ↔
      D.RowStep (rankRow input.length current) (rankRow input.length outer)
    rw [hinnerRow, houterRow]
  have hnewFoundValue :
      newFound = foundFrom D input outer (insert current selected) := by
    rw [hfound, holdFoundEq, foundFrom_insert]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [hinnerOuterIff, hedgeIff]
    tauto
  have hfoundNew :
      HasFound (foundFrom D input outer (insert current selected)) new := by
    have := (scanBits_none_eq_some_iff_hasFound hnewNe newFound).1 hnewFoundScan
    simpa [hnewFoundValue] using this
  have hbase : RoundTracks D input new depth oldCount newCount :=
    { length_eq := hlen
      source_eq := hsource.trans hinv.source_eq
      depth_eq := hdepth.trans hinv.depth_eq
      oldCount_eq := holdCount.trans hinv.oldCount_eq
      newCount_eq := hnewCount.trans hinv.newCount_eq
      depth_lt := hinv.depth_lt
      oldCount_le := hinv.oldCount_le
      newCount_le := hinv.newCount_le
      oldCount_exact := hinv.oldCount_exact }
  have htranscript (hle : innerIndex + 1 ≤ Fintype.card A ^ input.length) :
      InnerScanTranscript D input new depth oldCount newCount outerIndex
        (innerIndex + 1) (insert current selected) :=
    { toRoundTracks := hbase
      outer_lt := hinv.outer_lt
      inner_le := hle
      outer_eq := houter.trans hinv.outer_eq
      inner_eq := hinnerNext
      seen_eq := hseenEq
      selected_reachable := hselectedReachable
      selected_prefix := hselectedPrefix
      classified_exact := hinv.classified_exact
      found_eq := hfoundNew }
  rcases hinnerPhase with hdone | hcarry
  · left
    rcases hdone with ⟨rfl, rfl⟩
    have hoverFalse := ((vertexCodec A).evalSucc_eq_done_iff
      (innerTrack old) (innerTrack new)).1 hinnerSucc |>.2
    have hoverFalse' :
        ((vertexCodec A).increment (vertexNumeral input.length innerIndex)).2 = false := by
      simpa [hinv.inner_eq] using hoverFalse
    have hnotLast : innerIndex + 1 ≠ Fintype.card A ^ input.length := by
      intro hlast
      have hoverTrue :=
        (increment_vertexNumeral_overflow_iff (A := A) hinv.inner_lt).2 hlast
      exact Bool.false_ne_true (hoverFalse'.symm.trans hoverTrue)
    have hlt : innerIndex + 1 < Fintype.card A ^ input.length := by
      apply Nat.lt_of_le_of_ne
      · exact Nat.succ_le_iff.mpr hinv.inner_lt
      · exact hnotLast
    refine ⟨hlt, ?_⟩
    exact
      { toInnerScanTranscript := by
          simpa [current] using htranscript (Nat.le_of_lt hlt)
        inner_lt := hlt
        phase := hphaseNew
        path_zero := by simpa [hlen] using hpathZero
        fuel_zero := by simpa [hlen] using hfuelZero }
  · right
    rcases hcarry with ⟨rfl, rfl⟩
    have hoverTrue := ((vertexCodec A).evalSucc_eq_carry_iff
      (innerTrack old) (innerTrack new)).1 hinnerSucc |>.2
    have hoverTrue' :
        ((vertexCodec A).increment (vertexNumeral input.length innerIndex)).2 = true := by
      simpa [hinv.inner_eq] using hoverTrue
    have hlast : innerIndex + 1 = Fintype.card A ^ input.length :=
      (increment_vertexNumeral_overflow_iff (A := A) hinv.inner_lt).1 hoverTrue'
    refine ⟨hlast, ?_⟩
    exact
      { toInnerScanTranscript := by
          simpa [current, hlast] using htranscript (Nat.le_of_eq hlast)
        phase := hphaseNew
        path_zero := by simpa [hlen] using hpathZero
        fuel_zero := by simpa [hlen] using hfuelZero }

/-- Completing a final-scan witness additionally records that the inserted reachable
rank is nonfinal. -/
public theorem finalWitness_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A}
    {depth count innerIndex pathIndex fuel : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinalPathInvariant D input old depth count innerIndex selected
      pathIndex fuel)
    (hstep : IsFinalWitness D old new) :
    (innerIndex + 1 < Fintype.card A ^ input.length ∧
      FinalChooseInvariant D input new depth count (innerIndex + 1)
        (insert ⟨innerIndex, hinv.inner_lt⟩ selected)) ∨
    (innerIndex + 1 = Fintype.card A ^ input.length ∧
      FinalFinishInvariant D input new depth count
        (insert ⟨innerIndex, hinv.inner_lt⟩ selected)) := by
  have hpersistent := hstep.persistent_spec
  rcases hpersistent with
    ⟨hlength, _holdPhase, hsource, hdepth, _houter, hpathZero, hfuelZero,
      holdCount, _hnewCount, hfound⟩
  rcases hstep with
    ⟨finalState, innerState, newPhase, _hlocal, hfinal, hpathInner,
      hfuelDepth, hseenSucc, hinnerSucc, hinnerPhase, hnewPhaseScan, hfinalDone⟩
  have hlen : new.length = input.length := hlength.symm.trans hinv.length_eq
  have hnewNe : new ≠ [] := row_ne_nil_of_length_eq hlen hinput
  have hfuelCapacity : fuel < Fintype.card A ^ input.length :=
    lt_of_le_of_lt hinv.fuel_le hinv.depth_lt
  have hpathIndex : pathIndex = innerIndex :=
    (vertexNumeral_injective (A := A) hinv.path_lt hinv.inner_lt).1
      (hinv.path_eq.symm.trans (hpathInner.trans hinv.inner_eq))
  have hfuelIndex : fuel = depth :=
    (vertexNumeral_injective (A := A) hfuelCapacity hinv.depth_lt).1
      (hinv.fuel_eq.symm.trans (hfuelDepth.trans hinv.depth_eq))
  let current : RankVertex A input.length := ⟨innerIndex, hinv.inner_lt⟩
  have hcurrentReachable : current ∈ protocolReached D input depth := by
    simpa [current, hpathIndex, hfuelIndex] using hinv.path_reachable
  have hcurrentNotMem : current ∉ selected := by
    intro hmem
    have hpref := hinv.selected_prefix hmem
    rw [mem_rankPrefix] at hpref
    exact (Nat.lt_irrefl innerIndex) (by simpa [current] using hpref)
  have hinsertCard : (insert current selected).card = selected.card + 1 :=
    Finset.card_insert_of_notMem hcurrentNotMem
  have hselectedReachable :
      insert current selected ⊆ protocolReached D input depth := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hcurrentReachable
    · exact hinv.selected_reachable hv
  have hselectedPrefix :
      insert current selected ⊆ rankPrefix input.length (innerIndex + 1) := by
    intro v hv
    rw [mem_rankPrefix]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp [current]
    · have hpref := hinv.selected_prefix hv
      rw [mem_rankPrefix] at hpref
      omega
  have hcurrentNonfinal : ¬ rankFinal D input.length current := by
    intro hfinalCurrent
    change D.finalDone (D.evalFinal D.finalStart (rankRow input.length current)) = true
      at hfinalCurrent
    have hinnerRow : innerTrack old = rankRow input.length current := by
      calc
        innerTrack old = vertexNumeral input.length innerIndex := hinv.inner_eq
        _ = rankRow input.length current := rfl
    rw [← hinnerRow, hfinal, hfinalDone] at hfinalCurrent
    contradiction
  have hselectedNonfinal :
      ∀ v ∈ insert current selected, ¬ rankFinal D input.length v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hcurrentNonfinal
    · exact hinv.selected_nonfinal v hv
  have hseenNext := ((countCodec A).evalSucc_eq_done_iff
    (seenCountTrack old) (seenCountTrack new)).1 hseenSucc |>.1
  have hseenEq :
      seenCountTrack new = countNumeral input.length (insert current selected).card := by
    calc
      seenCountTrack new = (countCodec A).nextRow (seenCountTrack old) := by
        simpa [RowNumeral.DigitCodec.nextRow] using hseenNext
      _ = countNumeral input.length (selected.card + 1) := by
        rw [hinv.seen_eq, nextRow_countNumeral]
      _ = countNumeral input.length (insert current selected).card := by
        rw [hinsertCard]
  have hinnerNext : innerTrack new = vertexNumeral input.length (innerIndex + 1) := by
    rcases hinnerPhase with hdone | hcarry
    · have hnext := ((vertexCodec A).evalSucc_eq_done_iff
        (innerTrack old) (innerTrack new)).1 (by simpa [hdone.1] using hinnerSucc) |>.1
      calc
        innerTrack new = (vertexCodec A).nextRow (innerTrack old) := by
          simpa [RowNumeral.DigitCodec.nextRow] using hnext
        _ = vertexNumeral input.length (innerIndex + 1) := by
          rw [hinv.inner_eq, nextRow_vertexNumeral]
    · have hnext := ((vertexCodec A).evalSucc_eq_carry_iff
        (innerTrack old) (innerTrack new)).1 (by simpa [hcarry.1] using hinnerSucc) |>.1
      calc
        innerTrack new = (vertexCodec A).nextRow (innerTrack old) := by
          simpa [RowNumeral.DigitCodec.nextRow] using hnext
        _ = vertexNumeral input.length (innerIndex + 1) := by
          rw [hinv.inner_eq, nextRow_vertexNumeral]
  have hphaseNew : HasPhase newPhase new :=
    (scanPhases_none_eq_some_iff_hasPhase hnewNe newPhase).1 hnewPhaseScan
  have hbase : FinalTracks D input new depth count :=
    { length_eq := hlen
      source_eq := hsource.trans hinv.source_eq
      depth_eq := hdepth.trans hinv.depth_eq
      count_eq := holdCount.trans hinv.count_eq
      depth_lt := hinv.depth_lt
      count_le := hinv.count_le
      count_exact := hinv.count_exact
      plateau := hinv.plateau
      found_false := hasFound_of_foundTrack_eq hinv.found_false hfound }
  have htranscript (hle : innerIndex + 1 ≤ Fintype.card A ^ input.length) :
      FinalScanTranscript D input new depth count (innerIndex + 1)
        (insert current selected) :=
    { toFinalTracks := hbase
      inner_le := hle
      inner_eq := hinnerNext
      seen_eq := hseenEq
      selected_reachable := hselectedReachable
      selected_prefix := hselectedPrefix
      selected_nonfinal := hselectedNonfinal }
  rcases hinnerPhase with hdone | hcarry
  · left
    rcases hdone with ⟨rfl, rfl⟩
    have hoverFalse := ((vertexCodec A).evalSucc_eq_done_iff
      (innerTrack old) (innerTrack new)).1 hinnerSucc |>.2
    have hoverFalse' :
        ((vertexCodec A).increment (vertexNumeral input.length innerIndex)).2 = false := by
      simpa [hinv.inner_eq] using hoverFalse
    have hnotLast : innerIndex + 1 ≠ Fintype.card A ^ input.length := by
      intro hlast
      have hoverTrue :=
        (increment_vertexNumeral_overflow_iff (A := A) hinv.inner_lt).2 hlast
      exact Bool.false_ne_true (hoverFalse'.symm.trans hoverTrue)
    have hlt : innerIndex + 1 < Fintype.card A ^ input.length := by
      apply Nat.lt_of_le_of_ne
      · exact Nat.succ_le_iff.mpr hinv.inner_lt
      · exact hnotLast
    refine ⟨hlt, ?_⟩
    exact
      { toFinalScanTranscript := by
          simpa [current] using htranscript (Nat.le_of_lt hlt)
        inner_lt := hlt
        phase := hphaseNew
        path_zero := by simpa [hlen] using hpathZero
        fuel_zero := by simpa [hlen] using hfuelZero }
  · right
    rcases hcarry with ⟨rfl, rfl⟩
    have hoverTrue := ((vertexCodec A).evalSucc_eq_carry_iff
      (innerTrack old) (innerTrack new)).1 hinnerSucc |>.2
    have hoverTrue' :
        ((vertexCodec A).increment (vertexNumeral input.length innerIndex)).2 = true := by
      simpa [hinv.inner_eq] using hoverTrue
    have hlast : innerIndex + 1 = Fintype.card A ^ input.length :=
      (increment_vertexNumeral_overflow_iff (A := A) hinv.inner_lt).1 hoverTrue'
    refine ⟨hlast, ?_⟩
    exact
      { toFinalScanTranscript := by
          simpa [current, hlast] using htranscript (Nat.le_of_eq hlast)
        phase := hphaseNew
        path_zero := by simpa [hlen] using hpathZero
        fuel_zero := by simpa [hlen] using hfuelZero }

end CertifiedRowSystem.Complement
