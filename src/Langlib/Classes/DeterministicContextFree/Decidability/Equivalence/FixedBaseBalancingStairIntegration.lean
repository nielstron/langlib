module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedBaseProtectedDepth
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailBalancingStairAssembly

@[expose]
public section

/-!
# Fixed-base non-sinking supplies balancing-stair depth

The fixed-tail stair constructors require every retained pivot schema to
protect the balancing-segment depth.  The fixed-base non-sinking theorem
supplies protection at the presentation's chosen depth, so a depth at least
as deep as the segment bound discharges that premise directly.

This isolates the remaining Proposition-49 construction obligation: build a
retained fixed-tail presentation whose common depth is at least the chosen
segment bound and whose concrete prefixes never sink from the fixed base.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace FixedTailPivotPresentation

/-- Fixed-base non-sinking protects every requested depth no larger than the
common fixed-tail depth. -/
public theorem protectsDepth_of_fixedBaseNonSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    {depth : ℕ}
    (hdepth : depth ≤ presentation.depth)
    (hnever : ∀ j,
      g.NeverSinksFromBase base (presentation.actions j)) :
    presentation.ProtectsDepth depth := by
  intro j
  exact
    (presentation.schemas_applicationDepth_of_fixedBaseNonSinking
      hg hnever j).mono hdepth

end FixedTailPivotPresentation

namespace LeftBalancingSubsequence

/-- A retained right-pivot presentation whose fixed base never sinks and
whose chosen depth covers the segment bound yields the canonical witnessed active
stair. -/
public def
    toWitnessedRegularActiveStairSequence_of_fixedBaseNonSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : LeftBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (hdepth : segmentBound ≤ presentation.depth)
    (hnever : ∀ j,
      g.NeverSinksFromBase
        (subsequence.pivot 0) (presentation.actions j)) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      presentation.width
      (fun j => g.fixedBalancingPresentationBound segmentBound
        presentation.arity (presentation.schemaGrowth j))
      path :=
  subsequence
    |>.toWitnessedRegularActiveStairSequence_of_fixedTail_canonicalGrowth
      hg hnormal hexposureBound hground hinitial hfiller presentation
      (presentation.protectsDepth_of_fixedBaseNonSinking
        hg hdepth hnever)

/-- The path-local no-repeat conclusion at the balancing-segment depth.
The width and growth witnesses remain presentation-dependent; their later
grammar-uniformization is a separate global step. -/
public theorem
    exists_witnessedRegularActiveStairSequence_of_noExposure_nonSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : LeftBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (hnotExposes : ∀ j,
      ¬g.ExposesBy (subsequence.pivot 0)
        (subsequence.bridgeLabels j) segmentBound)
    (hnever : ∀ j actions,
      subsequence.bridgeLabels j = actions.map Sum.inl →
      g.NeverSinksFromBase (subsequence.pivot 0) actions) :
    ∃ width growth,
      Nonempty (WitnessedRegularActiveStairSequence g
        initialLeft initialRight width growth path) := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hpivotGround :
      (subsequence.pivot 0).Ground g.ranks := by
    have hpair := path.residual_ground hgroundSteps hground
      (subsequence.levels 0)
    unfold groundPairCode at hpair
    rw [Bool.and_eq_true] at hpair
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpair.2
  obtain ⟨presentation, hpresentationDepth⟩ :=
    DCFEquivalence.EncodedFirstOrderGrammar.exists_fixedTailPivotPresentation_atDepth
      (g := g) hg hpivotGround hfiller segmentBound
      (fun j =>
        subsequence.pivot_run
          (i := 0) (j := j) (Nat.zero_le j))
      (fun j =>
          path.exists_actions_segmentWord hgroundSteps hground
            (subsequence.levels 0)
            (subsequence.levels j - subsequence.levels 0))
      hnotExposes
  refine ⟨presentation.width,
    (fun j => g.fixedBalancingPresentationBound segmentBound
      presentation.arity (presentation.schemaGrowth j)),
    ⟨?_⟩⟩
  apply
    subsequence
      |>.toWitnessedRegularActiveStairSequence_of_fixedBaseNonSinking
        hg hnormal hexposureBound hground hinitial hfiller presentation
  · rw [hpresentationDepth]
  · intro j
    exact hnever j (presentation.actions j)
      (presentation.labels_eq j)

end LeftBalancingSubsequence

namespace RightBalancingSubsequence

/-- Symmetric fixed-base non-sinking integration for retained left pivots. -/
public def
    toWitnessedRegularActiveStairSequence_of_fixedBaseNonSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : RightBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (hdepth : segmentBound ≤ presentation.depth)
    (hnever : ∀ j,
      g.NeverSinksFromBase
        (subsequence.pivot 0) (presentation.actions j)) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      presentation.width
      (fun j => g.fixedBalancingPresentationBound segmentBound
        presentation.arity (presentation.schemaGrowth j))
      path :=
  subsequence
    |>.toWitnessedRegularActiveStairSequence_of_fixedTail_canonicalGrowth
      hg hnormal hexposureBound hground hinitial hfiller presentation
      (presentation.protectsDepth_of_fixedBaseNonSinking
        hg hdepth hnever)

/-- Symmetric path-local stair existence at the balancing-segment depth. -/
public theorem
    exists_witnessedRegularActiveStairSequence_of_noExposure_nonSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : RightBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (hnotExposes : ∀ j,
      ¬g.ExposesBy (subsequence.pivot 0)
        (subsequence.bridgeLabels j) segmentBound)
    (hnever : ∀ j actions,
      subsequence.bridgeLabels j = actions.map Sum.inl →
      g.NeverSinksFromBase (subsequence.pivot 0) actions) :
    ∃ width growth,
      Nonempty (WitnessedRegularActiveStairSequence g
        initialLeft initialRight width growth path) := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hpivotGround :
      (subsequence.pivot 0).Ground g.ranks := by
    have hpair := path.residual_ground hgroundSteps hground
      (subsequence.levels 0)
    unfold groundPairCode at hpair
    rw [Bool.and_eq_true] at hpair
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpair.1
  obtain ⟨presentation, hpresentationDepth⟩ :=
    DCFEquivalence.EncodedFirstOrderGrammar.exists_fixedTailPivotPresentation_atDepth
      (g := g) hg hpivotGround hfiller segmentBound
      (fun j =>
        subsequence.pivot_run
          (i := 0) (j := j) (Nat.zero_le j))
      (fun j =>
          path.exists_actions_segmentWord hgroundSteps hground
            (subsequence.levels 0)
            (subsequence.levels j - subsequence.levels 0))
      hnotExposes
  refine ⟨presentation.width,
    (fun j => g.fixedBalancingPresentationBound segmentBound
      presentation.arity (presentation.schemaGrowth j)),
    ⟨?_⟩⟩
  apply
    subsequence
      |>.toWitnessedRegularActiveStairSequence_of_fixedBaseNonSinking
        hg hnormal hexposureBound hground hinitial hfiller presentation
  · rw [hpresentationDepth]
  · intro j
    exact hnever j (presentation.actions j)
      (presentation.labels_eq j)

end RightBalancingSubsequence

end EncodedFirstOrderGrammar

end DCFEquivalence
