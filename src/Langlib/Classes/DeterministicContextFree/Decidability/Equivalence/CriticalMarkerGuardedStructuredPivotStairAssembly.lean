module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedBalancingResultCoverage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerFixedTailBalancingStairAssembly

@[expose]
public section

/-!
# Guarded marker-stable stairs on operational pivot rebases

The marker-aware critical prefix cuts fresh nullary marker roots into the
common argument tuple.  Its guarded-depth invariant is sufficient to reflect
each concrete balancing word and each canonical exposing continuation.
Consequently the operational `MaximalProgressRebase` assembles into a
marker-stable witnessed stair without requiring the rebased base itself to be
marker-free at every protected depth.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain

/-- Assemble marker-stable structured balancing rows over a guarded
critical-prefix presentation.  Marker-free absolute endpoints supply the
original outer stem, balancing segment, and active depth-one prefix; the
presentation supplies the original pivot schema and guarded reflection. -/
public noncomputable def
    toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressFixedTail
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound :
      (g.withCriticalMarkers count).exposureBound hnormal ≤ bound)
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalProgressRebase)
    {base filler : RegularTerm}
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler rebase.labels
      (fun j =>
        trajectory.representatives (rebase.start + j)))
    (hdepth : bound ≤ presentation.depth)
    (schemaBound : ℕ → ℕ)
    (hschema : ∀ j,
      (presentation.schema j).nodes.length ≤ schemaBound j)
    (hendpoint : ∀ j, NoCriticalMarkerActions
      (path.word (chain.levels (rebase.start + j)))) :
    MarkerStableWitnessedRegularActiveStairSequence
      g count initialLeft initialRight presentation.width
      (fun j =>
        (g.withCriticalMarkers count)
          |>.fixedBalancingPresentationBound
            bound presentation.arity (schemaBound j))
      path := by
  let extended := g.withCriticalMarkers count
  let hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have hbound : 0 < bound :=
    (extended.exposureBound_pos hnormal).trans_le hexposureBound
  let levels : ℕ → ℕ :=
    fun j => chain.levels (rebase.start + j)
  refine
    { arguments := presentation.arguments
      levels := levels
      levels_strictMono := ?_
      covered := ?_ }
  · exact (chain.levels_strictMono hbound).comp
      (by
        intro i j hij
        exact Nat.add_lt_add_left hij rebase.start)
  · intro j
    let index := rebase.start + j
    let state := chain.states index
    let step := state.incoming
    let segment := SelectedBalancingSegment.asSegment step.selected
    have hpivotInstance :
        ((presentation.schema j).instantiate
            presentation.arguments).UnfoldingEquivalent
          (SelectedBalancingSegment.pivot step.selected) := by
      have hpresentation :=
        presentation.schema_instance_matches j
      have hrepresentative :=
        trajectory.representative_matches index
      exact hpresentation.trans (by
        simpa [index, state, step, pivot] using hrepresentative)
    obtain ⟨originalStem, originalSegment,
        hstem, hsegment⟩ :=
      chain.exists_originalStemAndSegment_of_endpoint_noMarkerActions
        (hg := hg) index (hendpoint j)
    have hactivePrefixOriginal :=
      chain.activePrefixOriginal_of_endpoint_noMarkerActions
        (hg := hg) hbound index (hendpoint j)
    obtain ⟨X, children, hroot⟩ :=
      step.active_ground.exists_rootApplication
    obtain ⟨coverage⟩ :=
      segment
        |>.exists_markerStableSchemaBoundedWitnessedBalancingResult_of_criticalGuardedFixedTail
          hg hnormal hexposureBound
          step.active_ground step.pivot_ground
          presentation hdepth hpivotInstance
          step.outer_derivation
          step.active_traceEquivalent_pivot
          (hschema j)
          (by
            simpa [index, state, step] using
              hactivePrefixOriginal)
          originalStem originalSegment
          (by simpa [index, state, step] using hstem)
          (by simpa [index, state, step, segment] using hsegment)
          hroot
    have hword :
        step.outerStem ++
            (state.source.continuationPath
              hgExtended hground hinitial).segmentWord
                step.offset bound =
          path.word (chain.levels index) := by
      simpa [index, state, step, levels] using
        step.outerStem_append_labels
    exact ⟨coverage.castWord hword⟩

/-- Widen the guarded marker-stable structured stair to exact common
grammar-uniform width and arity targets. -/
public noncomputable def
    toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressFixedTail_widened
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    {bound targetWidth targetArity : ℕ}
    (hexposureBound :
      (g.withCriticalMarkers count).exposureBound hnormal ≤ bound)
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalProgressRebase)
    {base filler : RegularTerm}
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler rebase.labels
      (fun j =>
        trajectory.representatives (rebase.start + j)))
    (hdepth : bound ≤ presentation.depth)
    (schemaBound : ℕ → ℕ)
    (hschema : ∀ j,
      (presentation.schema j).nodes.length ≤ schemaBound j)
    (hendpoint : ∀ j, NoCriticalMarkerActions
      (path.word (chain.levels (rebase.start + j))))
    (hwidth : presentation.width ≤ targetWidth)
    (harity : presentation.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    MarkerStableWitnessedRegularActiveStairSequence
      g count initialLeft initialRight targetWidth
      (fun j => max targetArity
        ((g.withCriticalMarkers count)
          |>.fixedBalancingPresentationBound
            bound presentation.arity (schemaBound j)))
      path := by
  let source :=
    chain
      |>.toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressFixedTail
        hg hnormal hground hinitial hexposureBound
        trajectory rebase presentation hdepth
        schemaBound hschema hendpoint
  apply source.widen filler presentation.filler_ground hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
