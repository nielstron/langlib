module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerBalancingResultCoverage

@[expose]
public section

/-!
# Marker-stable fixed-tail balancing stairs

This is the marker-stable analogue of `FixedTailBalancingStairAssembly`.
Besides the ordinary fixed-tail and non-sinking hypotheses, each selected
level supplies:

* original-rank well-formedness of its fixed pivot schema;
* original-rank well-formedness of the depth-one active prefix; and
* original words whose critical lifts are the accumulated stem and balancing
  segment.

The resulting local stair is immediately widened to selected grammar-uniform
active-width and arity bounds.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace MarkerStableBoundedWitnessedActiveSchemaCoverage

/-- Transport a marker-stable row across equality of its accumulated word. -/
public def castWord
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word word' : List (Label (Action ⊕ ℕ))}
    (coverage : MarkerStableBoundedWitnessedActiveSchemaCoverage
      g count initialLeft initialRight bound width arguments word)
    (hword : word = word') :
    MarkerStableBoundedWitnessedActiveSchemaCoverage
      g count initialLeft initialRight bound width arguments word' := by
  subst word'
  exact coverage

end MarkerStableBoundedWitnessedActiveSchemaCoverage

namespace LeftBalancingSubsequence

/-- A marker-stable fixed-tail presentation of retained right pivots,
widened to exact common active-width and arity bounds. -/
public def
    toMarkerStableWitnessedRegularActiveStairSequence_of_fixedTail_widened
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {segmentBound targetWidth targetArity : ℕ}
    (hexposureBound :
      (g.withCriticalMarkers count).exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : LeftBalancingSubsequence sequence)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (hdepth : segmentBound ≤ presentation.depth)
    (hnever : ∀ j,
      (g.withCriticalMarkers count).NeverSinksFromBase
        (subsequence.pivot 0) (presentation.actions j))
    (hpivotSchemaOriginal : ∀ j,
      (presentation.schema j).WellFormed
        g.ranks presentation.arity)
    (hactivePrefixOriginal : ∀ j,
      ((path.left (subsequence.levels j)).depthPrefix 1)
        |>.head.toRegularTerm.WellFormed g.ranks
          (((path.left (subsequence.levels j)).depthPrefix 1)
            |>.schemaArity (g.withCriticalMarkers count).ranks))
    (originalStem originalSegment : ℕ → List (Label Action))
    (hstem : ∀ j,
      path.word (subsequence.levels j) =
        (originalStem j).map liftCriticalLabel)
    (hsegment : ∀ j,
      path.segmentWord (subsequence.levels j) segmentBound =
        (originalSegment j).map liftCriticalLabel)
    (hwidth : presentation.width ≤ targetWidth)
    (harity : presentation.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight targetWidth
      (fun j => max targetArity
        ((g.withCriticalMarkers count)
          |>.fixedBalancingPresentationBound segmentBound
            presentation.arity (presentation.schemaGrowth j)))
      path := by
  let extended := g.withCriticalMarkers count
  let hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  let hgroundSteps : extended.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hgExtended
  have hprotected :
      presentation.ProtectsDepth segmentBound :=
    presentation.protectsDepth_of_fixedBaseNonSinking
      hgExtended hdepth hnever
  let localStair : MarkerStableWitnessedRegularActiveStairSequence
      g count initialLeft initialRight presentation.width
      (fun j => extended.fixedBalancingPresentationBound segmentBound
        presentation.arity (presentation.schemaGrowth j))
      path := by
    let levels : ℕ → ℕ :=
      fun j => subsequence.levels j + segmentBound
    refine
      { arguments := presentation.arguments
        levels := levels
        levels_strictMono := ?_
        covered := ?_ }
    · intro i j hij
      exact Nat.add_lt_add_right
        (subsequence.levels_strictMono hij) segmentBound
    · intro j
      let start := subsequence.levels j
      let segment := subsequence.segment j
      have hpairGround :=
        path.residual_ground hgroundSteps hground start
      unfold groundPairCode at hpairGround
      rw [Bool.and_eq_true] at hpairGround
      have hactive : (path.left start).Ground extended.ranks :=
        (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
          hpairGround.1
      have hpivot : (path.right start).Ground extended.ranks :=
        (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
          hpairGround.2
      have houter :=
        path.pair_derivable hgroundSteps hground hinitial start
      have hequivalent :=
        path.residual_traceEquivalent hinitial start
      obtain ⟨X, children, hroot⟩ :=
        hactive.exists_rootApplication
      obtain ⟨coverage⟩ :=
        segment
          |>.exists_markerStableSchemaBoundedWitnessedBalancingResult
            hg hnormal hexposureBound hactive hpivot hfiller
            houter hequivalent
            (presentation.schema_supported j)
            (presentation.schema_hasPrefixWitness j)
            presentation.rankMax_le_arity
            (hprotected j)
            presentation.arguments_length
            presentation.arguments_ground
            (presentation.schema_instance_matches j)
            (presentation.schema_nodes_length_le_schemaGrowth j)
            (hpivotSchemaOriginal j)
            (by simpa [start] using hactivePrefixOriginal j)
            (originalStem j) (originalSegment j)
            (by simpa [start] using hstem j)
            (by simpa [start] using hsegment j)
            hroot
      have hword :
          path.word start ++ path.segmentWord start segmentBound =
            path.word (start + segmentBound) := by
        exact (path.word_add start segmentBound).symm
      exact ⟨coverage.castWord (by
        simpa [segment, start, levels] using hword)⟩
  apply localStair.widen filler hfiller hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

end LeftBalancingSubsequence

namespace RightBalancingSubsequence

/-- Symmetric marker-stable fixed-tail widening for retained left pivots. -/
public def
    toMarkerStableWitnessedRegularActiveStairSequence_of_fixedTail_widened
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {segmentBound targetWidth targetArity : ℕ}
    (hexposureBound :
      (g.withCriticalMarkers count).exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : RightBalancingSubsequence sequence)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (hdepth : segmentBound ≤ presentation.depth)
    (hnever : ∀ j,
      (g.withCriticalMarkers count).NeverSinksFromBase
        (subsequence.pivot 0) (presentation.actions j))
    (hpivotSchemaOriginal : ∀ j,
      (presentation.schema j).WellFormed
        g.ranks presentation.arity)
    (hactivePrefixOriginal : ∀ j,
      ((path.right (subsequence.levels j)).depthPrefix 1)
        |>.head.toRegularTerm.WellFormed g.ranks
          (((path.right (subsequence.levels j)).depthPrefix 1)
            |>.schemaArity (g.withCriticalMarkers count).ranks))
    (originalStem originalSegment : ℕ → List (Label Action))
    (hstem : ∀ j,
      path.word (subsequence.levels j) =
        (originalStem j).map liftCriticalLabel)
    (hsegment : ∀ j,
      path.segmentWord (subsequence.levels j) segmentBound =
        (originalSegment j).map liftCriticalLabel)
    (hwidth : presentation.width ≤ targetWidth)
    (harity : presentation.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight targetWidth
      (fun j => max targetArity
        ((g.withCriticalMarkers count)
          |>.fixedBalancingPresentationBound segmentBound
            presentation.arity (presentation.schemaGrowth j)))
      path := by
  let extended := g.withCriticalMarkers count
  let hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  let hgroundSteps : extended.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hgExtended
  have hprotected :
      presentation.ProtectsDepth segmentBound :=
    presentation.protectsDepth_of_fixedBaseNonSinking
      hgExtended hdepth hnever
  let localStair : MarkerStableWitnessedRegularActiveStairSequence
      g count initialLeft initialRight presentation.width
      (fun j => extended.fixedBalancingPresentationBound segmentBound
        presentation.arity (presentation.schemaGrowth j))
      path := by
    let levels : ℕ → ℕ :=
      fun j => subsequence.levels j + segmentBound
    refine
      { arguments := presentation.arguments
        levels := levels
        levels_strictMono := ?_
        covered := ?_ }
    · intro i j hij
      exact Nat.add_lt_add_right
        (subsequence.levels_strictMono hij) segmentBound
    · intro j
      let start := subsequence.levels j
      let segment := subsequence.segment j
      have hpairGround :=
        path.residual_ground hgroundSteps hground start
      unfold groundPairCode at hpairGround
      rw [Bool.and_eq_true] at hpairGround
      have hactive : (path.right start).Ground extended.ranks :=
        (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
          hpairGround.2
      have hpivot : (path.left start).Ground extended.ranks :=
        (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
          hpairGround.1
      have houter :=
        CertificateDerivable.symmetry
          (path.pair_derivable hgroundSteps hground hinitial start)
      have hequivalent :=
        (path.residual_traceEquivalent hinitial start).symm
      obtain ⟨X, children, hroot⟩ :=
        hactive.exists_rootApplication
      obtain ⟨coverage⟩ :=
        segment
          |>.exists_markerStableSchemaBoundedWitnessedBalancingResult
            hg hnormal hexposureBound hactive hpivot hfiller
            houter hequivalent
            (presentation.schema_supported j)
            (presentation.schema_hasPrefixWitness j)
            presentation.rankMax_le_arity
            (hprotected j)
            presentation.arguments_length
            presentation.arguments_ground
            (presentation.schema_instance_matches j)
            (presentation.schema_nodes_length_le_schemaGrowth j)
            (hpivotSchemaOriginal j)
            (by simpa [start] using hactivePrefixOriginal j)
            (originalStem j) (originalSegment j)
            (by simpa [start] using hstem j)
            (by simpa [start] using hsegment j)
            hroot
      have hword :
          path.word start ++ path.segmentWord start segmentBound =
            path.word (start + segmentBound) := by
        exact (path.word_add start segmentBound).symm
      exact ⟨coverage.castWord (by
        simpa [segment, start, levels] using hword)⟩
  apply localStair.widen filler hfiller hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

end RightBalancingSubsequence

end EncodedFirstOrderGrammar

end DCFEquivalence
