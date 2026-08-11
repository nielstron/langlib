module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedBalancingChain
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotSwitchReachability

@[expose]
public section

/-!
# Proposition-49 pivot opportunity selection

After every normalized balancing result, the retained pivot is the right-hand
component.  Proposition 49 therefore first searches a bounded window for a
left-oriented segment, which retains that pivot directly.  If no such close
left opportunity exists, it advances to the close-window boundary and chooses
the next unoriented opportunity from the cofinal supply.

This file packages that policy independently of Proposition-45 assembly.  The
chosen `PathBalancingSegment` is retained verbatim, so it can be passed to
`DerivedPairAt.exists_balancingStep_of_selected` without losing its offset or
orientation.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

/-- A paper-faithful opportunity selection after a normalized balancing
result.

The close branch chooses the least left opportunity no later than
`closeBound`.  The fallback branch records that no left opportunity exists in
that whole window and chooses the least unoriented opportunity at or after
`closeBound`. -/
public structure PivotSelectionPolicy
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (segmentBound closeBound : ℕ) where
  offset : ℕ
  selected : PathBalancingSegment path segmentBound offset
  closeLeft_or_afterClose :
    (offset ≤ closeBound ∧
      SelectedBalancingSegment.side selected = BalancingSide.left ∧
      ∀ earlier, earlier < offset →
        ¬path.HasLeftBalancingOpportunity segmentBound earlier) ∨
    (closeBound ≤ offset ∧
      (∀ earlier, earlier ≤ closeBound →
        ¬path.HasLeftBalancingOpportunity segmentBound earlier) ∧
      ∀ earlier, closeBound ≤ earlier → earlier < offset →
        ¬path.HasBalancingOpportunity segmentBound earlier)

namespace PivotSelectionPolicy

/-- Forget the policy metadata and retain the ordinary balancing
opportunity. -/
public theorem hasBalancingOpportunity
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound closeBound : ℕ}
    (selection : PivotSelectionPolicy path segmentBound closeBound) :
    path.HasBalancingOpportunity segmentBound selection.offset :=
  ⟨selection.selected⟩

/-- The selected concrete segment can be fed directly to Proposition-45
assembly. -/
public theorem selected_is_usable
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound closeBound : ℕ}
    (selection : PivotSelectionPolicy path segmentBound closeBound) :
    Nonempty
      (PathBalancingSegment path segmentBound selection.offset) :=
  ⟨selection.selected⟩

end PivotSelectionPolicy

/-- Cofinal balancing opportunities yield the close-left/fallback selection
used in Proposition 49. -/
public theorem exists_pivotSelectionPolicy
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (segmentBound closeBound : ℕ)
    (hcofinal : path.HasCofinalBalancingOpportunities segmentBound) :
    Nonempty (PivotSelectionPolicy path segmentBound closeBound) := by
  classical
  by_cases hclose : ∃ offset,
      offset ≤ closeBound ∧
        path.HasLeftBalancingOpportunity segmentBound offset
  · let offset := Nat.find hclose
    obtain ⟨hoffset, hopportunity⟩ := Nat.find_spec hclose
    obtain ⟨segment⟩ := hopportunity
    exact ⟨
      { offset := offset
        selected := .left segment
        closeLeft_or_afterClose := .inl
          ⟨hoffset, rfl, by
            intro earlier hearlier hopportunity
            exact Nat.find_min hclose hearlier
              ⟨by omega, hopportunity⟩⟩ }⟩
  · have hafter : ∃ offset,
        closeBound ≤ offset ∧
          path.HasBalancingOpportunity segmentBound offset :=
      hcofinal closeBound
    let offset := Nat.find hafter
    obtain ⟨hoffset, hopportunity⟩ := Nat.find_spec hafter
    obtain ⟨selected⟩ := hopportunity
    exact ⟨
      { offset := offset
        selected := selected
        closeLeft_or_afterClose := .inr
          ⟨hoffset, by
            intro earlier hearlier hopportunity
            exact hclose ⟨earlier, hearlier, hopportunity⟩,
            by
              intro earlier hbound hearlier hopportunity
              exact Nat.find_min hafter hearlier
                ⟨hbound, hopportunity⟩⟩ }⟩

/-- Absence of a derived repeat gives a cofinal opportunity supply on every
certificate-derived continuation path. -/
public theorem DerivedPairAt.continuationPath_hasCofinalBalancingOpportunities
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {start segmentBound : ℕ}
    (source : path.DerivedPairAt start) :
    (source.continuationPath hg hground hinitial)
      |>.HasCofinalBalancingOpportunities segmentBound := by
  let continuation :=
    source.continuationPath hg hground hinitial
  have hsourceGround :=
    groundPairCode_of_pair_derivable source.derivation
  have laws := guardedContextLaws_of_wellFormed hg
  have hsourceEquivalent :=
    source.derivation.pair_traceEquivalent_of_initial laws hinitial
  have hnoRawRepeat : ¬continuation.HasRepeat :=
    source.continuationPath_hasNoRepeat
      hg hground hinitial hnoRepeat
  apply continuation.hasCofinalBalancingOpportunities_of_noRepeat
    hnoRawRepeat
  intro threshold hnoOpportunity
  exact continuation.hasRepeat_of_eventually_noBalancingOpportunity
    hg hsourceGround hsourceEquivalent segmentBound threshold
      hnoOpportunity

/-- Specialized policy selection on any certificate-derived recursive state
of a path with no derived repeat. -/
public theorem DerivedPairAt.exists_pivotSelectionPolicy_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {start segmentBound : ℕ}
    (source : path.DerivedPairAt start)
    (closeBound : ℕ) :
    Nonempty
      (PivotSelectionPolicy
        (source.continuationPath hg hground hinitial)
        segmentBound closeBound) := by
  apply exists_pivotSelectionPolicy
  exact source.continuationPath_hasCofinalBalancingOpportunities
    hg hground hinitial hnoRepeat

/-- Selection followed by Proposition-45 assembly, retaining exact proof that
the constructed step uses the policy's chosen offset and segment. -/
public theorem DerivedPairAt.exists_policyBalancingStep_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {start segmentBound : ℕ}
    (source : path.DerivedPairAt start)
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    (closeBound : ℕ) :
    ∃ selection :
        PivotSelectionPolicy
          (source.continuationPath hg hground hinitial)
          segmentBound closeBound,
      ∃ step : DerivedBalancingStep
          hg hground hinitial source segmentBound,
        step.offset = selection.offset ∧
          SelectedBalancingSegment.side step.selected =
            SelectedBalancingSegment.side selection.selected ∧
          HEq step.selected selection.selected := by
  obtain ⟨selection⟩ :=
    source.exists_pivotSelectionPolicy_of_noDerivedRepeat
      hg hground hinitial hnoRepeat closeBound
  obtain ⟨step, hoffset, hside, hselected⟩ :=
    source.exists_balancingStep_of_selected
      hg hnormal hground hinitial hexposureBound selection.selected
  exact ⟨selection, step, hoffset, hside, hselected⟩

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
