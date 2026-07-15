module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Correctness
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.RankGraph
import Mathlib.Tactic

@[expose]
public section

/-!
# Semantic invariants of the streaming complement protocol

This module interprets the protocol's canonical row scans in the finite ranked graph of
width-preserving source configurations.  It is deliberately independent of the later LBA
compiler: all arguments concern `ProtocolStep` and finite graph reachability.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

/-- The source row carried by a protocol run. -/
public def protocolSource (D : CertifiedRowSystem I A Unit Q F) (input : List I) : List A :=
  input.map D.inputCell

omit [Fintype A] [Nonempty A] [DecidableEq A] in
@[simp]
public theorem length_protocolSource (D : CertifiedRowSystem I A Unit Q F)
    (input : List I) :
    (protocolSource D input).length = input.length := by
  simp [protocolSource]

/-- The source vertex in the ranked width-`|input|` graph. -/
public noncomputable def protocolSourceRank
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    RankVertex A input.length :=
  sourceRank input.length (protocolSource D input) (length_protocolSource D input)

omit [DecidableEq A] in
@[simp]
public theorem rankRow_protocolSourceRank
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    rankRow input.length (protocolSourceRank D input) = protocolSource D input := by
  simp [protocolSourceRank]

/-- Bounded reachability in the ranked source graph. -/
public noncomputable def protocolReached
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (k : Nat) :
    Finset (RankVertex A input.length) := by
  letI : DecidableRel (rankEdge D input.length) := Classical.decRel _
  exact FiniteReachabilityCounting.reached
    (rankEdge D input.length) (protocolSourceRank D input) k

omit [DecidableEq A] in
@[simp]
public theorem protocolReached_zero
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    protocolReached D input 0 = {protocolSourceRank D input} := by
  simp [protocolReached, FiniteReachabilityCounting.reached]

omit [DecidableEq A] in
public theorem protocolReached_succ
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (k : Nat) :
    protocolReached D input (k + 1) =
      protocolReached D input k ∪
        Finset.univ.filter (fun v ↦
          ∃ u ∈ protocolReached D input k, rankEdge D input.length u v) := by
  letI : DecidableRel (rankEdge D input.length) := Classical.decRel _
  apply Finset.ext
  intro v
  simp [protocolReached, FiniteReachabilityCounting.reached_succ,
    FiniteReachabilityCounting.grow]

omit [DecidableEq A] in
public theorem protocolReached_mono
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (k : Nat) :
    protocolReached D input k ⊆ protocolReached D input (k + 1) := by
  letI : DecidableRel (rankEdge D input.length) := Classical.decRel _
  exact FiniteReachabilityCounting.reached_mono
    (rankEdge D input.length) (protocolSourceRank D input) k

/-- A plateau layer is the complete reflexive-transitive reachable set. -/
public theorem mem_protocolReached_iff_of_plateau
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (depth : Nat)
    (hplateau : protocolReached D input depth =
      protocolReached D input (depth + 1))
    (v : RankVertex A input.length) :
    v ∈ protocolReached D input depth ↔
      Relation.ReflTransGen (rankEdge D input.length)
        (protocolSourceRank D input) v := by
  letI : DecidableRel (rankEdge D input.length) := Classical.decRel _
  constructor
  · intro hv
    exact FiniteReachabilityCounting.reached_sound
      (rankEdge D input.length) (protocolSourceRank D input) hv
  · intro hreach
    have hsource : protocolSourceRank D input ∈ protocolReached D input depth := by
      apply FiniteReachabilityCounting.reached_mono_nat
        (rankEdge D input.length) (protocolSourceRank D input) (Nat.zero_le depth)
      simp
    have hclosed : ∀ {old new : RankVertex A input.length},
        old ∈ protocolReached D input depth → rankEdge D input.length old new →
          new ∈ protocolReached D input depth := by
      intro old new hold hedge
      have hnew : new ∈ protocolReached D input (depth + 1) := by
        rw [protocolReached_succ]
        exact Finset.mem_union_right _ (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨old, hold, hedge⟩)
      rwa [← hplateau] at hnew
    induction hreach with
    | refl => exact hsource
    | tail _ hedge ih => exact hclosed ih hedge

omit [DecidableEq A] in
public theorem card_protocolReached_le_capacity
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (k : Nat) :
    (protocolReached D input k).card ≤ Fintype.card A ^ input.length := by
  calc
    (protocolReached D input k).card ≤
        Fintype.card (RankVertex A input.length) := Finset.card_le_univ _
    _ = Fintype.card A ^ input.length := by simp

/-- A strict cardinal increase leaves room for the following depth numeral. -/
public theorem depth_succ_lt_capacity_of_card_lt
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (depth : Nat)
    (hgrowth : (protocolReached D input depth).card <
      (protocolReached D input (depth + 1)).card) :
    depth + 1 < Fintype.card A ^ input.length := by
  letI : DecidableRel (rankEdge D input.length) := Classical.decRel _
  have hne : protocolReached D input depth ≠ protocolReached D input (depth + 1) := by
    intro heq
    rw [heq] at hgrowth
    omega
  have hlower : depth + 1 ≤ (protocolReached D input depth).card := by
    simpa only [protocolReached] using
      (FiniteReachabilityCounting.card_reached_lower_of_nonplateau
        (rankEdge D input.length) (protocolSourceRank D input) hne)
  have hupper := card_protocolReached_le_capacity D input (depth + 1)
  omega

/-- Source rejection can be stated entirely in the finite ranked graph. -/
public theorem sourceRejects_iff_ranked
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    SourceRejects D input ↔
      ¬ ∃ row : RankVertex A input.length,
        Relation.ReflTransGen (rankEdge D input.length)
            (protocolSourceRank D input) row ∧
          rankFinal D input.length row := by
  constructor
  · intro hrejected
    rintro ⟨row, hreach, hfinal⟩
    apply hrejected
    refine ⟨rankRow input.length row, ?_, hfinal⟩
    simpa [rankRow_protocolSourceRank] using
      (rankReach_sound D input.length hreach)
  · intro hranked
    rintro ⟨row, hreach, hfinal⟩
    have hstart : protocolSource D input =
        rankRow input.length (protocolSourceRank D input) := by simp
    change Relation.ReflTransGen D.RowStep (protocolSource D input) row at hreach
    rw [hstart] at hreach
    obtain ⟨rank, hrankRow, hrankReach⟩ :=
      rankReach_complete D input.length hreach
    apply hranked
    refine ⟨rank, hrankReach, ?_⟩
    simpa [rankFinal, hrankRow] using hfinal

/-- Vertices already classified before the current outer enumeration position. -/
public noncomputable def classifiedPrefix
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (k outerIndex : Nat) : Finset (RankVertex A input.length) :=
  protocolReached D input (k + 1) ∩ rankPrefix input.length outerIndex

omit [DecidableEq A] in
@[simp]
public theorem mem_classifiedPrefix
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (k outerIndex : Nat) (v : RankVertex A input.length) :
    v ∈ classifiedPrefix D input k outerIndex ↔
      v ∈ protocolReached D input (k + 1) ∧ v.val < outerIndex := by
  simp [classifiedPrefix]

/-- The Boolean accumulated while scanning old-reachable predecessors of one outer
vertex. -/
public noncomputable def foundFrom
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (outer : RankVertex A input.length)
    (selected : Finset (RankVertex A input.length)) : Bool :=
  decide (∃ inner ∈ selected, inner = outer ∨ rankEdge D input.length inner outer)

omit [DecidableEq A] in
@[simp]
public theorem foundFrom_eq_true_iff
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (outer : RankVertex A input.length)
    (selected : Finset (RankVertex A input.length)) :
    foundFrom D input outer selected = true ↔
      ∃ inner ∈ selected, inner = outer ∨ rankEdge D input.length inner outer := by
  simp [foundFrom]

/-- If the selected inner scan is exactly the old reachable layer, its accumulated flag
is precisely membership in the next reachable layer. -/
public theorem foundFrom_full_iff
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (k : Nat)
    (outer : RankVertex A input.length) :
    foundFrom D input outer (protocolReached D input k) = true ↔
      outer ∈ protocolReached D input (k + 1) := by
  rw [foundFrom_eq_true_iff, protocolReached_succ]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨inner, hinner, heq | hedge⟩
    · exact Or.inl (heq ▸ hinner)
    · exact Or.inr ⟨inner, hinner, hedge⟩
  · rintro (hold | ⟨inner, hinner, hedge⟩)
    · exact ⟨outer, hold, Or.inl rfl⟩
    · exact ⟨inner, hinner, Or.inr hedge⟩

/-- Extending the outer prefix classifies exactly its new rank. -/
public theorem classifiedPrefix_succ
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (depth outerIndex : Nat)
    (houter : outerIndex < Fintype.card A ^ input.length) :
    classifiedPrefix D input depth (outerIndex + 1) =
      if (⟨outerIndex, houter⟩ : RankVertex A input.length) ∈
          protocolReached D input (depth + 1) then
        insert ⟨outerIndex, houter⟩ (classifiedPrefix D input depth outerIndex)
      else classifiedPrefix D input depth outerIndex := by
  rw [classifiedPrefix, rankPrefix_succ houter]
  ext v
  by_cases hcurrent : (⟨outerIndex, houter⟩ : RankVertex A input.length) ∈
      protocolReached D input (depth + 1)
  · simp [hcurrent]
  · simp [hcurrent]

/-- Cardinal form of `classifiedPrefix_succ`. -/
public theorem card_classifiedPrefix_succ
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (depth outerIndex : Nat)
    (houter : outerIndex < Fintype.card A ^ input.length) :
    (classifiedPrefix D input depth (outerIndex + 1)).card =
      if (⟨outerIndex, houter⟩ : RankVertex A input.length) ∈
          protocolReached D input (depth + 1) then
        (classifiedPrefix D input depth outerIndex).card + 1
      else (classifiedPrefix D input depth outerIndex).card := by
  rw [classifiedPrefix_succ D input depth outerIndex houter]
  split
  · rw [Finset.card_insert_of_notMem]
    simp [classifiedPrefix]
  · rfl

/-! ## Semantic states of a protocol run -/

omit [Nonempty A] [DecidableEq A] in
/-- A nonempty row cannot carry two different replicated phases. -/
public theorem hasPhase_unique {row : ProtocolRow A} {p q : ProtocolPhase}
    (hne : row ≠ []) (hp : HasPhase p row) (hq : HasPhase q row) : p = q := by
  obtain ⟨cell, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact (hp cell (by simp)).symm.trans (hq cell (by simp))

omit [Nonempty A] [DecidableEq A] in
/-- A nonempty row cannot carry two different replicated Boolean flags. -/
public theorem hasFound_unique {row : ProtocolRow A} {p q : Bool}
    (hne : row ≠ []) (hp : HasFound p row) (hq : HasFound q row) : p = q := by
  obtain ⟨cell, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact (hp cell (by simp)).symm.trans (hq cell (by simp))

omit [Nonempty A] [DecidableEq A] in
@[simp]
public theorem foundTrack_eq_replicate_iff (row : ProtocolRow A) (found : Bool) :
    foundTrack row = List.replicate row.length found ↔ HasFound found row := by
  have hlen : (foundTrack row).length = row.length := by simp [foundTrack]
  rw [← hlen, List.eq_replicate_length]
  simp [foundTrack, HasFound]

omit [Nonempty A] [DecidableEq A] in
@[simp]
public theorem phaseTrack_eq_replicate_iff (row : ProtocolRow A)
    (phase : ProtocolPhase) :
    row.map (fun cell ↦ cell.phase) = List.replicate row.length phase ↔
      HasPhase phase row := by
  have hlen : (row.map (fun cell ↦ cell.phase)).length = row.length := by simp
  rw [← hlen, List.eq_replicate_length]
  simp [HasPhase]

omit [Nonempty A] [DecidableEq A] in
public theorem length_eq_of_sourceTrack_eq {old new : ProtocolRow A}
    (h : sourceTrack new = sourceTrack old) : new.length = old.length := by
  have := congrArg List.length h
  simpa [sourceTrack] using this

omit [Nonempty A] [DecidableEq A] in
public theorem row_ne_nil_of_length_eq {row : ProtocolRow A} {input : List I}
    (hlen : row.length = input.length) (hinput : input ≠ []) : row ≠ [] := by
  intro hrow
  subst row
  simp only [List.length_nil] at hlen
  exact hinput (List.length_eq_zero_iff.mp hlen.symm)

omit [Nonempty A] [DecidableEq A] in
public theorem hasFound_of_foundTrack_eq {old new : ProtocolRow A} {found : Bool}
    (hfound : HasFound found old) (htrack : foundTrack new = foundTrack old) :
    HasFound found new := by
  have hlen : new.length = old.length := by
    have := congrArg List.length htrack
    simpa [foundTrack] using this
  rw [← foundTrack_eq_replicate_iff] at hfound ⊢
  rw [htrack, hfound, hlen]

/-- Tracks shared by every state inside one inductive-counting round. -/
public structure RoundTracks
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth oldCount newCount : Nat) : Prop where
  length_eq : row.length = input.length
  source_eq : sourceTrack row = protocolSource D input
  depth_eq : depthTrack row = vertexNumeral input.length depth
  oldCount_eq : oldCountTrack row = countNumeral input.length oldCount
  newCount_eq : newCountTrack row = countNumeral input.length newCount
  depth_lt : depth < Fintype.card A ^ input.length
  oldCount_le : oldCount ≤ Fintype.card A ^ input.length
  newCount_le : newCount ≤ Fintype.card A ^ input.length
  oldCount_exact : oldCount = (protocolReached D input depth).card

/-- Transcript of the partial canonical inner scan for one outer vertex.  `selected`
contains precisely the old-reachable rows for which a path witness was supplied so far;
soundness only needs the subset and cardinal facts recorded here. -/
public structure InnerScanTranscript
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth oldCount newCount outerIndex innerIndex : Nat)
    (selected : Finset (RankVertex A input.length)) : Prop
    extends RoundTracks D input row depth oldCount newCount where
  outer_lt : outerIndex < Fintype.card A ^ input.length
  inner_le : innerIndex ≤ Fintype.card A ^ input.length
  outer_eq : outerTrack row = vertexNumeral input.length outerIndex
  inner_eq : innerTrack row = vertexNumeral input.length innerIndex
  seen_eq : seenCountTrack row = countNumeral input.length selected.card
  selected_reachable : selected ⊆ protocolReached D input depth
  selected_prefix : selected ⊆ rankPrefix input.length innerIndex
  classified_exact :
    newCount = (classifiedPrefix D input depth outerIndex).card
  found_eq :
    HasFound
      (foundFrom D input ⟨outerIndex, outer_lt⟩ selected) row

/-- A boundary state at the start of a counting round. -/
public structure RoundStartInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth oldCount : Nat) : Prop
    extends RoundTracks D input row depth oldCount 0 where
  phase : HasPhase .roundStart row
  seen_zero : seenCountTrack row = countNumeral input.length 0
  outer_zero : outerTrack row = vertexNumeral input.length 0
  inner_zero : innerTrack row = vertexNumeral input.length 0
  path_zero : pathTrack row = vertexNumeral input.length 0
  fuel_zero : fuelTrack row = vertexNumeral input.length 0
  found_false : HasFound false row

/-- A state ready either to skip the current inner row or start its path witness. -/
public structure ChooseInnerInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth oldCount newCount outerIndex innerIndex : Nat)
    (selected : Finset (RankVertex A input.length)) : Prop
    extends InnerScanTranscript D input row depth oldCount newCount outerIndex innerIndex
      selected where
  inner_lt : innerIndex < Fintype.card A ^ input.length
  phase : HasPhase .chooseInner row
  path_zero : pathTrack row = vertexNumeral input.length 0
  fuel_zero : fuelTrack row = vertexNumeral input.length 0

/-- State inside a bounded path witness for the current inner row. -/
public structure CountingPathInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth oldCount newCount outerIndex innerIndex : Nat)
    (selected : Finset (RankVertex A input.length))
    (pathIndex fuel : Nat) : Prop
    extends InnerScanTranscript D input row depth oldCount newCount outerIndex innerIndex
      selected where
  inner_lt : innerIndex < Fintype.card A ^ input.length
  phase : HasPhase .path row
  path_lt : pathIndex < Fintype.card A ^ input.length
  fuel_le : fuel ≤ depth
  path_eq : pathTrack row = vertexNumeral input.length pathIndex
  fuel_eq : fuelTrack row = vertexNumeral input.length fuel
  path_reachable :
    ⟨pathIndex, path_lt⟩ ∈ protocolReached D input fuel

/-- The inner enumeration has overflowed and the current outer classification is ready
to be committed.  A malformed run may arrive here with too few witnesses; the next
action's exact-count check then blocks it. -/
public structure FinishOuterInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth oldCount newCount outerIndex : Nat)
    (selected : Finset (RankVertex A input.length)) : Prop
    extends InnerScanTranscript D input row depth oldCount newCount outerIndex
      (Fintype.card A ^ input.length) selected where
  phase : HasPhase .finishOuter row
  path_zero : pathTrack row = vertexNumeral input.length 0
  fuel_zero : fuelTrack row = vertexNumeral input.length 0

/-- Boundary state after every outer vertex has been classified. -/
public structure FinishRoundInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth oldCount newCount : Nat) : Prop
    extends RoundTracks D input row depth oldCount newCount where
  phase : HasPhase .finishRound row
  nextCount_exact : newCount = (protocolReached D input (depth + 1)).card
  seen_zero : seenCountTrack row = countNumeral input.length 0
  outer_zero : outerTrack row = vertexNumeral input.length 0
  inner_zero : innerTrack row = vertexNumeral input.length 0
  path_zero : pathTrack row = vertexNumeral input.length 0
  fuel_zero : fuelTrack row = vertexNumeral input.length 0
  found_false : HasFound false row

/-- Tracks shared by the final all-nonfinal scan after an exact count plateau. -/
public structure FinalTracks
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth count : Nat) : Prop where
  length_eq : row.length = input.length
  source_eq : sourceTrack row = protocolSource D input
  depth_eq : depthTrack row = vertexNumeral input.length depth
  count_eq : oldCountTrack row = countNumeral input.length count
  depth_lt : depth < Fintype.card A ^ input.length
  count_le : count ≤ Fintype.card A ^ input.length
  count_exact : count = (protocolReached D input depth).card
  plateau : protocolReached D input depth = protocolReached D input (depth + 1)
  found_false : HasFound false row

/-- Partial transcript of the final canonical scan. -/
public structure FinalScanTranscript
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth count innerIndex : Nat)
    (selected : Finset (RankVertex A input.length)) : Prop
    extends FinalTracks D input row depth count where
  inner_le : innerIndex ≤ Fintype.card A ^ input.length
  inner_eq : innerTrack row = vertexNumeral input.length innerIndex
  seen_eq : seenCountTrack row = countNumeral input.length selected.card
  selected_reachable : selected ⊆ protocolReached D input depth
  selected_prefix : selected ⊆ rankPrefix input.length innerIndex
  selected_nonfinal : ∀ v ∈ selected, ¬ rankFinal D input.length v

/-- State ready to skip or witness the current row in the final scan. -/
public structure FinalChooseInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth count innerIndex : Nat)
    (selected : Finset (RankVertex A input.length)) : Prop
    extends FinalScanTranscript D input row depth count innerIndex selected where
  inner_lt : innerIndex < Fintype.card A ^ input.length
  phase : HasPhase .finalChoose row
  path_zero : pathTrack row = vertexNumeral input.length 0
  fuel_zero : fuelTrack row = vertexNumeral input.length 0

/-- State inside a final-scan reachability witness. -/
public structure FinalPathInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth count innerIndex : Nat)
    (selected : Finset (RankVertex A input.length))
    (pathIndex fuel : Nat) : Prop
    extends FinalScanTranscript D input row depth count innerIndex selected where
  inner_lt : innerIndex < Fintype.card A ^ input.length
  phase : HasPhase .finalPath row
  path_lt : pathIndex < Fintype.card A ^ input.length
  fuel_le : fuel ≤ depth
  path_eq : pathTrack row = vertexNumeral input.length pathIndex
  fuel_eq : fuelTrack row = vertexNumeral input.length fuel
  path_reachable :
    ⟨pathIndex, path_lt⟩ ∈ protocolReached D input fuel

/-- The final enumeration has overflowed and awaits its exact-count check. -/
public structure FinalFinishInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (row : ProtocolRow A) (depth count : Nat)
    (selected : Finset (RankVertex A input.length)) : Prop
    extends FinalScanTranscript D input row depth count
      (Fintype.card A ^ input.length) selected where
  phase : HasPhase .finalFinish row
  path_zero : pathTrack row = vertexNumeral input.length 0
  fuel_zero : fuelTrack row = vertexNumeral input.length 0

/-! ### Local preservation lemmas -/

/-- The canonical boot target is the initial exact count state (`depth = 0`, count
`= 1`). -/
public theorem initialized_roundStartInvariant
    (D : CertifiedRowSystem I A Unit Q F) {input : List I} (hinput : input ≠ []) :
    RoundStartInvariant D input
      (initializedProtocolRow (protocolSource D input)) 0 1 := by
  have hsourceNe : protocolSource D input ≠ [] := by
    intro hsource
    have := congrArg List.length hsource
    simp [protocolSource] at this
    exact hinput this
  have hinit := isInitialized_initializedProtocolRow hsourceNe
  rcases hinit with
    ⟨hsource, hphase, hdepth, holdCount, hnewCount, hseen, houter, hinner,
      hpath, hfuel, hfound⟩
  have hlen :
      (initializedProtocolRow (protocolSource D input)).length = input.length := by
    simp [protocolSource]
  have hn : 0 < input.length := List.length_pos_of_ne_nil hinput
  have hcapacity : 0 < Fintype.card A ^ input.length :=
    Nat.pow_pos Fintype.card_pos
  refine
    { toRoundTracks :=
        { length_eq := hlen
          source_eq := hsource
          depth_eq := by simpa [hlen] using hdepth
          oldCount_eq := by
            rw [holdCount]
            simpa [hlen] using (countNumeral_one (A := A) hn).symm
          newCount_eq := by simpa [hlen] using hnewCount
          depth_lt := hcapacity
          oldCount_le := by
            exact Nat.one_le_pow _ _ Fintype.card_pos
          newCount_le := by simp
          oldCount_exact := by simp }
      phase := hphase
      seen_zero := by simpa [hlen] using hseen
      outer_zero := by simpa [hlen] using houter
      inner_zero := by simpa [hlen] using hinner
      path_zero := by simpa [hlen] using hpath
      fuel_zero := by simpa [hlen] using hfuel
      found_false := hfound }

/-- Entering a round creates the empty inner-scan transcript at outer and inner rank
zero. -/
public theorem beginRound_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A} {depth count : Nat}
    (hinv : RoundStartInvariant D input old depth count)
    (hstep : BeginRoundSpec old new) :
    ChooseInnerInvariant D input new depth count 0 0 0 ∅ := by
  rcases hstep with ⟨_, hphase, hcopy⟩
  rcases hcopy with
    ⟨hsource, hdepth, holdCount, hnewCount, hseen, houter, hinner,
      hpath, hfuel, hfound⟩
  have hlen : new.length = input.length :=
    (length_eq_of_sourceTrack_eq hsource).trans hinv.length_eq
  have hfoundFalse : HasFound false new :=
    hasFound_of_foundTrack_eq hinv.found_false hfound
  have hcapacity : 0 < Fintype.card A ^ input.length :=
    Nat.pow_pos Fintype.card_pos
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
              newCount_le := by simp
              oldCount_exact := hinv.oldCount_exact }
          outer_lt := hcapacity
          inner_le := by simp
          outer_eq := houter.trans hinv.outer_zero
          inner_eq := hinner.trans hinv.inner_zero
          seen_eq := by simpa using hseen.trans hinv.seen_zero
          selected_reachable := by simp
          selected_prefix := by simp
          classified_exact := by simp [classifiedPrefix]
          found_eq := by simpa [foundFrom] using hfoundFalse }
      inner_lt := hcapacity
      phase := hphase
      path_zero := hpath.trans hinv.path_zero
      fuel_zero := hfuel.trans hinv.fuel_zero }

/-- Skipping the current inner row advances its canonical rank.  The last rank moves
to `finishOuter`; every earlier rank stays in `chooseInner`. -/
public theorem skipInner_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A} {depth oldCount newCount outerIndex innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinv : ChooseInnerInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected)
    (hstep : SkipInnerSpec old new) :
    (innerIndex + 1 < Fintype.card A ^ input.length ∧
      ChooseInnerInvariant D input new depth oldCount newCount outerIndex
        (innerIndex + 1) selected) ∨
    (innerIndex + 1 = Fintype.card A ^ input.length ∧
      FinishOuterInvariant D input new depth oldCount newCount outerIndex selected) := by
  rcases hstep with
    ⟨_, hsource, hdepth, holdCount, hnewCount, hseen, houter, hpath, hfuel,
      hfound, hinner, hphase⟩
  have hlen : new.length = input.length :=
    (length_eq_of_sourceTrack_eq hsource).trans hinv.length_eq
  have hinnerEq : innerTrack new = vertexNumeral input.length (innerIndex + 1) := by
    rw [hinner, hinv.inner_eq, nextRow_vertexNumeral]
  have hselectedPrefix :
      selected ⊆ rankPrefix input.length (innerIndex + 1) :=
    hinv.selected_prefix.trans (rankPrefix_mono (Nat.le_succ innerIndex))
  have hfoundNew :
      HasFound
        (foundFrom D input ⟨outerIndex, hinv.outer_lt⟩ selected) new :=
    hasFound_of_foundTrack_eq hinv.found_eq hfound
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
        (innerIndex + 1) selected :=
    { toRoundTracks := hbase
      outer_lt := hinv.outer_lt
      inner_le := hle
      outer_eq := houter.trans hinv.outer_eq
      inner_eq := hinnerEq
      seen_eq := hseen.trans hinv.seen_eq
      selected_reachable := hinv.selected_reachable
      selected_prefix := hselectedPrefix
      classified_exact := hinv.classified_exact
      found_eq := hfoundNew }
  have hoverIff := increment_vertexNumeral_overflow_iff (A := A) hinv.inner_lt
  by_cases hlast : innerIndex + 1 = Fintype.card A ^ input.length
  · right
    refine ⟨hlast, ?_⟩
    have hover : ((vertexCodec A).increment (innerTrack old)).2 = true := by
      rw [hinv.inner_eq]
      exact hoverIff.2 hlast
    refine
      { toInnerScanTranscript := by
          simpa only [hlast] using htranscript (Nat.le_of_eq hlast)
        phase := by simpa [hover] using hphase
        path_zero := hpath.trans hinv.path_zero
        fuel_zero := hfuel.trans hinv.fuel_zero }
  · left
    have hlt : innerIndex + 1 < Fintype.card A ^ input.length := by
      apply Nat.lt_of_le_of_ne
      · simpa only [Nat.succ_eq_add_one] using
          (Nat.succ_le_iff.mpr hinv.inner_lt)
      · exact hlast
    refine ⟨hlt, ?_⟩
    have hover : ((vertexCodec A).increment (innerTrack old)).2 = false := by
      rw [hinv.inner_eq]
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hlast (hoverIff.1 htrue)
    refine
      { toInnerScanTranscript := htranscript (Nat.le_of_lt hlt)
        inner_lt := hlt
        phase := by simpa [hover] using hphase
        path_zero := hpath.trans hinv.path_zero
        fuel_zero := hfuel.trans hinv.fuel_zero }

/-- Committing an exhaustively checked outer row advances the outer enumeration and
the exact next-layer count. -/
public theorem finishOuter_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A} {depth oldCount newCount outerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinishOuterInvariant D input old depth oldCount newCount outerIndex selected)
    (hstep : FinishOuterSpec old new) :
    let nextCount := (classifiedPrefix D input depth (outerIndex + 1)).card
    (outerIndex + 1 < Fintype.card A ^ input.length ∧
      ChooseInnerInvariant D input new depth oldCount nextCount (outerIndex + 1) 0 ∅) ∨
    (outerIndex + 1 = Fintype.card A ^ input.length ∧
      FinishRoundInvariant D input new depth oldCount nextCount) := by
  dsimp only
  rcases hstep with
    ⟨_, hseenExact, hsource, hdepth, holdCount, houter, hreset,
      hcountStep, hphase⟩
  rcases hreset with ⟨hinnerZero, hseenZero, hpathZero, hfuelZero, hfoundFalse⟩
  have hn : 0 < input.length := List.length_pos_of_ne_nil hinput
  have hlen : new.length = input.length :=
    (length_eq_of_sourceTrack_eq hsource).trans hinv.length_eq
  have holdNe : old ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  have hselectedCardLe : selected.card ≤ Fintype.card A ^ input.length := by
    calc
      selected.card ≤ Fintype.card (RankVertex A input.length) :=
        Finset.card_le_univ selected
      _ = Fintype.card A ^ input.length := by simp
  have hselectedCard : selected.card = oldCount := by
    apply (countNumeral_injective_of_le_rowCapacity (A := A) hn
      hselectedCardLe hinv.oldCount_le).1
    calc
      countNumeral input.length selected.card = seenCountTrack old := hinv.seen_eq.symm
      _ = oldCountTrack old := hseenExact
      _ = countNumeral input.length oldCount := hinv.oldCount_eq
  have hselected : selected = protocolReached D input depth := by
    apply Finset.eq_of_subset_of_card_le hinv.selected_reachable
    rw [hselectedCard, hinv.oldCount_exact]
  let nextCount := (classifiedPrefix D input depth (outerIndex + 1)).card
  have hnextCountLe : nextCount ≤ Fintype.card A ^ input.length := by
    calc
      nextCount ≤ Fintype.card (RankVertex A input.length) :=
        Finset.card_le_univ _
      _ = Fintype.card A ^ input.length := by simp
  have hnewCountTrack :
      newCountTrack new = countNumeral input.length nextCount := by
    rcases hcountStep with hfound | hnotFound
    · rcases hfound with ⟨hfoundOld, hnextRow, _⟩
      have hflag :
          foundFrom D input ⟨outerIndex, hinv.outer_lt⟩ selected = true :=
        hasFound_unique holdNe hinv.found_eq hfoundOld
      have hcurrent :
          (⟨outerIndex, hinv.outer_lt⟩ : RankVertex A input.length) ∈
            protocolReached D input (depth + 1) := by
        apply (foundFrom_full_iff D input depth ⟨outerIndex, hinv.outer_lt⟩).1
        simpa [hselected] using hflag
      have hnextCount : nextCount = newCount + 1 := by
        dsimp only [nextCount]
        rw [card_classifiedPrefix_succ D input depth outerIndex hinv.outer_lt,
          if_pos hcurrent, ← hinv.classified_exact]
      rw [hnextRow, hinv.newCount_eq, nextRow_countNumeral, hnextCount]
    · rcases hnotFound with ⟨hfoundOld, hcopy⟩
      have hflag :
          foundFrom D input ⟨outerIndex, hinv.outer_lt⟩ selected = false :=
        hasFound_unique holdNe hinv.found_eq hfoundOld
      have hcurrent :
          (⟨outerIndex, hinv.outer_lt⟩ : RankVertex A input.length) ∉
            protocolReached D input (depth + 1) := by
        intro hmem
        have : foundFrom D input ⟨outerIndex, hinv.outer_lt⟩
            (protocolReached D input depth) = true :=
          (foundFrom_full_iff D input depth ⟨outerIndex, hinv.outer_lt⟩).2 hmem
        rw [← hselected, hflag] at this
        contradiction
      have hnextCount : nextCount = newCount := by
        dsimp only [nextCount]
        rw [card_classifiedPrefix_succ D input depth outerIndex hinv.outer_lt,
          if_neg hcurrent, ← hinv.classified_exact]
      rw [hcopy, hinv.newCount_eq, hnextCount]
  have hbase : RoundTracks D input new depth oldCount nextCount :=
    { length_eq := hlen
      source_eq := hsource.trans hinv.source_eq
      depth_eq := hdepth.trans hinv.depth_eq
      oldCount_eq := holdCount.trans hinv.oldCount_eq
      newCount_eq := hnewCountTrack
      depth_lt := hinv.depth_lt
      oldCount_le := hinv.oldCount_le
      newCount_le := hnextCountLe
      oldCount_exact := hinv.oldCount_exact }
  have houterEq : outerTrack new = vertexNumeral input.length (outerIndex + 1) := by
    rw [houter, hinv.outer_eq, nextRow_vertexNumeral]
  have hoverIff := increment_vertexNumeral_overflow_iff (A := A) hinv.outer_lt
  by_cases hlast : outerIndex + 1 = Fintype.card A ^ input.length
  · right
    refine ⟨hlast, ?_⟩
    have hover : ((vertexCodec A).increment (outerTrack old)).2 = true := by
      rw [hinv.outer_eq]
      exact hoverIff.2 hlast
    refine
      { toRoundTracks := hbase
        phase := by simpa [hover] using hphase
        nextCount_exact := by
          rw [hlast]
          simp [classifiedPrefix]
        seen_zero := by simpa [hlen] using hseenZero
        outer_zero := by simpa [hlast] using houterEq
        inner_zero := by simpa [hlen] using hinnerZero
        path_zero := by simpa [hlen] using hpathZero
        fuel_zero := by simpa [hlen] using hfuelZero
        found_false := hfoundFalse }
  · left
    have hlt : outerIndex + 1 < Fintype.card A ^ input.length := by
      apply Nat.lt_of_le_of_ne
      · simpa only [Nat.succ_eq_add_one] using
          (Nat.succ_le_iff.mpr hinv.outer_lt)
      · exact hlast
    have hover : ((vertexCodec A).increment (outerTrack old)).2 = false := by
      rw [hinv.outer_eq]
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hlast (hoverIff.1 htrue)
    refine ⟨hlt, ?_⟩
    refine
      { toInnerScanTranscript :=
          { toRoundTracks := hbase
            outer_lt := hlt
            inner_le := by simp
            outer_eq := houterEq
            inner_eq := by simpa [hlen] using hinnerZero
            seen_eq := by simpa [hlen] using hseenZero
            selected_reachable := by simp
            selected_prefix := by simp
            classified_exact := rfl
            found_eq := by simpa [foundFrom] using hfoundFalse }
        inner_lt := Nat.pow_pos Fintype.card_pos
        phase := by simpa [hover] using hphase
        path_zero := by simpa [hlen] using hpathZero
        fuel_zero := by simpa [hlen] using hfuelZero }

/-- Finishing an exact count round either records a genuine plateau and starts the final
scan, or advances to the next exact depth/count pair. -/
public theorem finishRound_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A} {depth oldCount newCount : Nat}
    (hinput : input ≠ [])
    (hinv : FinishRoundInvariant D input old depth oldCount newCount)
    (hstep : FinishRoundSpec old new) :
    FinalChooseInvariant D input new depth oldCount 0 ∅ ∨
      RoundStartInvariant D input new (depth + 1) newCount := by
  rcases hstep with ⟨_, hsource, hreset, hbranch⟩
  rcases hreset with
    ⟨hnewZero, hseenZero, houterZero, hinnerZero, hpathZero, hfuelZero,
      hfoundFalse⟩
  have hn : 0 < input.length := List.length_pos_of_ne_nil hinput
  have hlen : new.length = input.length :=
    (length_eq_of_sourceTrack_eq hsource).trans hinv.length_eq
  have holdBound : oldCount < (Fintype.card A + 1) ^ input.length :=
    lt_of_le_of_lt hinv.oldCount_le (rowCapacity_lt_countCapacity (A := A) hn)
  have hnewBound : newCount < (Fintype.card A + 1) ^ input.length :=
    lt_of_le_of_lt hinv.newCount_le (rowCapacity_lt_countCapacity (A := A) hn)
  rcases hbranch with hplateau | hgrowth
  · left
    rcases hplateau with
      ⟨hcountRows, hphase, hdepth, holdCount⟩
    have hcounts : oldCount = newCount := by
      apply (countNumeral_injective_of_le_rowCapacity (A := A) hn
        hinv.oldCount_le hinv.newCount_le).1
      calc
        countNumeral input.length oldCount = oldCountTrack old := hinv.oldCount_eq.symm
        _ = newCountTrack old := hcountRows
        _ = countNumeral input.length newCount := hinv.newCount_eq
    have hreachedPlateau :
        protocolReached D input depth = protocolReached D input (depth + 1) := by
      apply Finset.eq_of_subset_of_card_le (protocolReached_mono D input depth)
      rw [← hinv.nextCount_exact, ← hcounts, hinv.oldCount_exact]
    refine
      { toFinalScanTranscript :=
          { toFinalTracks :=
              { length_eq := hlen
                source_eq := hsource.trans hinv.source_eq
                depth_eq := hdepth.trans hinv.depth_eq
                count_eq := holdCount.trans hinv.oldCount_eq
                depth_lt := hinv.depth_lt
                count_le := hinv.oldCount_le
                count_exact := hinv.oldCount_exact
                plateau := hreachedPlateau
                found_false := hfoundFalse }
            inner_le := by simp
            inner_eq := by simpa [hlen] using hinnerZero
            seen_eq := by simpa [hlen] using hseenZero
            selected_reachable := by simp
            selected_prefix := by simp
            selected_nonfinal := by simp }
        inner_lt := Nat.pow_pos Fintype.card_pos
        phase := hphase
        path_zero := by simpa [hlen] using hpathZero
        fuel_zero := by simpa [hlen] using hfuelZero }
  · right
    rcases hgrowth with
      ⟨hless, hphase, hdepth, hdepthNoOverflow, holdCount⟩
    have hcountLt : oldCount < newCount := by
      have hlenCounts :
          (countNumeral (A := A) input.length oldCount).length =
            (countNumeral (A := A) input.length newCount).length := by simp
      have hless' :
          (countCodec A).compareRows
              (countNumeral (A := A) input.length oldCount)
              (countNumeral (A := A) input.length newCount) = some .lt := by
        simpa [RowNumeral.DigitCodec.rowsLess, hinv.oldCount_eq,
          hinv.newCount_eq] using hless
      have hvalues :=
        ((countCodec A).compareRows_eq_lt_iff hlenCounts).1 hless'
      simpa [value_countNumeral (A := A) holdBound,
        value_countNumeral (A := A) hnewBound] using hvalues
    have hdepthLt : depth + 1 < Fintype.card A ^ input.length :=
      depth_succ_lt_capacity_of_card_lt D input depth (by
        rwa [← hinv.oldCount_exact, ← hinv.nextCount_exact])
    refine
      { toRoundTracks :=
          { length_eq := hlen
            source_eq := hsource.trans hinv.source_eq
            depth_eq := by
              rw [hdepth, hinv.depth_eq, nextRow_vertexNumeral]
            oldCount_eq := holdCount.trans hinv.newCount_eq
            newCount_eq := by simpa [hlen] using hnewZero
            depth_lt := hdepthLt
            oldCount_le := hinv.newCount_le
            newCount_le := by simp
            oldCount_exact := hinv.nextCount_exact }
        phase := hphase
        seen_zero := by simpa [hlen] using hseenZero
        outer_zero := by simpa [hlen] using houterZero
        inner_zero := by simpa [hlen] using hinnerZero
        path_zero := by simpa [hlen] using hpathZero
        fuel_zero := by simpa [hlen] using hfuelZero
        found_false := hfoundFalse }

omit [DecidableEq A] in
/-- Skipping a row in the final scan advances the same canonical enumeration. -/
public theorem finalSkip_preserves
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A} {depth count innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinv : FinalChooseInvariant D input old depth count innerIndex selected)
    (hstep : FinalSkipSpec old new) :
    (innerIndex + 1 < Fintype.card A ^ input.length ∧
      FinalChooseInvariant D input new depth count (innerIndex + 1) selected) ∨
    (innerIndex + 1 = Fintype.card A ^ input.length ∧
      FinalFinishInvariant D input new depth count selected) := by
  rcases hstep with
    ⟨_, hsource, hdepth, holdCount, _hnewCount, hseen, _houter, hpath,
      hfuel, hfound, hinner, hphase⟩
  have hlen : new.length = input.length :=
    (length_eq_of_sourceTrack_eq hsource).trans hinv.length_eq
  have hinnerEq : innerTrack new = vertexNumeral input.length (innerIndex + 1) := by
    rw [hinner, hinv.inner_eq, nextRow_vertexNumeral]
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
  have hprefix : selected ⊆ rankPrefix input.length (innerIndex + 1) :=
    hinv.selected_prefix.trans (rankPrefix_mono (Nat.le_succ innerIndex))
  have htranscript (hle : innerIndex + 1 ≤ Fintype.card A ^ input.length) :
      FinalScanTranscript D input new depth count (innerIndex + 1) selected :=
    { toFinalTracks := hbase
      inner_le := hle
      inner_eq := hinnerEq
      seen_eq := hseen.trans hinv.seen_eq
      selected_reachable := hinv.selected_reachable
      selected_prefix := hprefix
      selected_nonfinal := hinv.selected_nonfinal }
  have hoverIff := increment_vertexNumeral_overflow_iff (A := A) hinv.inner_lt
  by_cases hlast : innerIndex + 1 = Fintype.card A ^ input.length
  · right
    refine ⟨hlast, ?_⟩
    have hover : ((vertexCodec A).increment (innerTrack old)).2 = true := by
      rw [hinv.inner_eq]
      exact hoverIff.2 hlast
    refine
      { toFinalScanTranscript := by
          simpa only [hlast] using htranscript (Nat.le_of_eq hlast)
        phase := by simpa [hover] using hphase
        path_zero := hpath.trans hinv.path_zero
        fuel_zero := hfuel.trans hinv.fuel_zero }
  · left
    have hlt : innerIndex + 1 < Fintype.card A ^ input.length := by
      apply Nat.lt_of_le_of_ne
      · simpa only [Nat.succ_eq_add_one] using
          (Nat.succ_le_iff.mpr hinv.inner_lt)
      · exact hlast
    refine ⟨hlt, ?_⟩
    have hover : ((vertexCodec A).increment (innerTrack old)).2 = false := by
      rw [hinv.inner_eq]
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hlast (hoverIff.1 htrue)
    refine
      { toFinalScanTranscript := htranscript (Nat.le_of_lt hlt)
        inner_lt := hlt
        phase := by simpa [hover] using hphase
        path_zero := hpath.trans hinv.path_zero
        fuel_zero := hfuel.trans hinv.fuel_zero }

/-- The exact final scan proves that every globally reachable ranked row is nonfinal. -/
public theorem finalFinish_rejects
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A} {depth count : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinput : input ≠ [])
    (hinv : FinalFinishInvariant D input old depth count selected)
    (hstep : FinalFinishSpec old new) :
    SourceRejects D input ∧ HasPhase .accept new ∧ new.length = input.length := by
  rcases hstep with ⟨_, haccept, hseenExact, hsource⟩
  have hn : 0 < input.length := List.length_pos_of_ne_nil hinput
  have hselectedCardLe : selected.card ≤ Fintype.card A ^ input.length := by
    calc
      selected.card ≤ Fintype.card (RankVertex A input.length) :=
        Finset.card_le_univ selected
      _ = Fintype.card A ^ input.length := by simp
  have hselectedCard : selected.card = count := by
    apply (countNumeral_injective_of_le_rowCapacity (A := A) hn
      hselectedCardLe hinv.count_le).1
    calc
      countNumeral input.length selected.card = seenCountTrack old := hinv.seen_eq.symm
      _ = oldCountTrack old := hseenExact
      _ = countNumeral input.length count := hinv.count_eq
  have hselected : selected = protocolReached D input depth := by
    apply Finset.eq_of_subset_of_card_le hinv.selected_reachable
    rw [hselectedCard, hinv.count_exact]
  refine ⟨(sourceRejects_iff_ranked D input).2 ?_, haccept,
    (length_eq_of_sourceTrack_eq hsource).trans hinv.length_eq⟩
  rintro ⟨row, hreach, hfinal⟩
  have hbounded : row ∈ protocolReached D input depth :=
    (mem_protocolReached_iff_of_plateau D input depth hinv.plateau row).2 hreach
  exact hinv.selected_nonfinal row (by simpa [hselected] using hbounded) hfinal

/-- Full semantic invariant covering every control phase of a protocol run. -/
public inductive ProtocolInvariant
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) : ProtocolRow A → Prop
  | input : ProtocolInvariant D input (input.map (inputProtocolCell D.inputCell))
  | roundStart {row depth count} :
      RoundStartInvariant D input row depth count → ProtocolInvariant D input row
  | chooseInner {row depth oldCount newCount outerIndex innerIndex selected} :
      ChooseInnerInvariant D input row depth oldCount newCount outerIndex innerIndex
        selected → ProtocolInvariant D input row
  | countingPath {row depth oldCount newCount outerIndex innerIndex selected pathIndex fuel} :
      CountingPathInvariant D input row depth oldCount newCount outerIndex innerIndex
        selected pathIndex fuel → ProtocolInvariant D input row
  | finishOuter {row depth oldCount newCount outerIndex selected} :
      FinishOuterInvariant D input row depth oldCount newCount outerIndex selected →
        ProtocolInvariant D input row
  | finishRound {row depth oldCount newCount} :
      FinishRoundInvariant D input row depth oldCount newCount → ProtocolInvariant D input row
  | finalChoose {row depth count innerIndex selected} :
      FinalChooseInvariant D input row depth count innerIndex selected →
        ProtocolInvariant D input row
  | finalPath {row depth count innerIndex selected pathIndex fuel} :
      FinalPathInvariant D input row depth count innerIndex selected pathIndex fuel →
        ProtocolInvariant D input row
  | finalFinish {row depth count selected} :
      FinalFinishInvariant D input row depth count selected → ProtocolInvariant D input row
  | accept {row} : SourceRejects D input → HasPhase .accept row →
      row.length = input.length →
      ProtocolInvariant D input row

omit [DecidableEq A] in
public theorem ProtocolInvariant.length_eq
    {D : CertifiedRowSystem I A Unit Q F} {input : List I} {row : ProtocolRow A}
    (hinv : ProtocolInvariant D input row) : row.length = input.length := by
  cases hinv with
  | input => simp
  | roundStart h => exact h.length_eq
  | chooseInner h => exact h.length_eq
  | countingPath h => exact h.length_eq
  | finishOuter h => exact h.length_eq
  | finishRound h => exact h.length_eq
  | finalChoose h => exact h.length_eq
  | finalPath h => exact h.length_eq
  | finalFinish h => exact h.length_eq
  | accept _ _ hlen => exact hlen

omit [DecidableEq A] in
public theorem ProtocolInvariant.rejects_of_accept
    {D : CertifiedRowSystem I A Unit Q F} {input : List I} {row : ProtocolRow A}
    (hinv : ProtocolInvariant D input row) (haccept : HasPhase .accept row)
    (hne : row ≠ []) : SourceRejects D input := by
  cases hinv with
  | input =>
      have hphase : HasPhase .input
          (input.map (inputProtocolCell D.inputCell)) := by
        intro cell hcell
        rw [List.mem_map] at hcell
        obtain ⟨symbol, _, rfl⟩ := hcell
        rfl
      have := hasPhase_unique hne hphase haccept
      contradiction
  | roundStart h =>
      have := hasPhase_unique hne h.phase haccept
      contradiction
  | chooseInner h =>
      have := hasPhase_unique hne h.phase haccept
      contradiction
  | countingPath h =>
      have := hasPhase_unique hne h.phase haccept
      contradiction
  | finishOuter h =>
      have := hasPhase_unique hne h.phase haccept
      contradiction
  | finishRound h =>
      have := hasPhase_unique hne h.phase haccept
      contradiction
  | finalChoose h =>
      have := hasPhase_unique hne h.phase haccept
      contradiction
  | finalPath h =>
      have := hasPhase_unique hne h.phase haccept
      contradiction
  | finalFinish h =>
      have := hasPhase_unique hne h.phase haccept
      contradiction
  | accept hrejected _ _ => exact hrejected

/-! ## Compiled versus semantic protocol reachability -/

/-- Replacing the integrated finite scanner by its declarative action union preserves
all finite protocol runs. -/
public theorem compiledProtocolAccepts_iff_protocolAccepts
    [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    CompiledProtocolAccepts D input ↔ ProtocolAccepts D input := by
  constructor
  · rintro ⟨row, hreach, hfinal⟩
    refine ⟨row, hreach.mono (fun old new hstep ↦ ?_), hfinal⟩
    exact (deterministicComplementSystem_rowStep_iff D old new).1 hstep
  · rintro ⟨row, hreach, hfinal⟩
    refine ⟨row, hreach.mono (fun old new hstep ↦ ?_), hfinal⟩
    exact (deterministicComplementSystem_rowStep_iff D old new).2 hstep

/-- Membership in the compiled deterministic-source complement is semantic protocol
acceptance, together with the certified-row model's nonempty-input convention. -/
public theorem mem_deterministicComplementSystem_iff_protocolAccepts
    [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    input ∈ (deterministicComplementSystem D).rowReachLanguage ↔
      input ≠ [] ∧ ProtocolAccepts D input := by
  rw [mem_deterministicComplementSystem_iff,
    compiledProtocolAccepts_iff_protocolAccepts]

end CertifiedRowSystem.Complement
