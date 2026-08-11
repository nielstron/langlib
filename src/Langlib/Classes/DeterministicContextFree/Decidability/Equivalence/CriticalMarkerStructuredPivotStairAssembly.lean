module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotStairAssembly
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerFixedTailBalancingStairAssembly

@[expose]
public section

/-!
# Marker-stable stairs on structured pivot chains

This is the critical-marker analogue of `StructuredPivotStairAssembly`.
The structured chain supplies the exact certificate-derived balancing rows,
while a fixed-tail presentation supplies one common argument tuple.  The
additional hypotheses record that the selected schemas, active prefixes, and
path words still come from the original grammar; the resulting rows therefore
survive marker elimination.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain

/-- A fixed-tail suffix of a structured pivot chain in the critical-marker
extension assembles directly into a marker-stable witnessed regular stair. -/
public noncomputable def
    toMarkerStableWitnessedRegularActiveStairSequence_of_fixedTail
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
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
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalExposureRebase)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j)))
    (hdepth : bound ≤ presentation.depth)
    (hnever : ∀ j,
      (g.withCriticalMarkers count).NeverSinksFromBase rebase.base
        (presentation.actions j))
    (actionBound : ℕ → ℕ)
    (hactions : ∀ j,
      (presentation.actions j).length ≤ actionBound j)
    (hpivotSchemaOriginal : ∀ j,
      (presentation.schema j).WellFormed
        g.ranks presentation.arity)
    (hactivePrefixOriginal : ∀ j,
      let index := rebase.start + j
      let step := (chain.states index).incoming
      ((SelectedBalancingSegment.active step.selected).depthPrefix 1)
        |>.head.toRegularTerm.WellFormed g.ranks
          (((SelectedBalancingSegment.active step.selected).depthPrefix 1)
            |>.schemaArity (g.withCriticalMarkers count).ranks))
    (originalStem originalSegment : ℕ → List (Label Action))
    (hstem : ∀ j,
      let index := rebase.start + j
      let step := (chain.states index).incoming
      step.outerStem = (originalStem j).map liftCriticalLabel)
    (hsegment : ∀ j,
      let index := rebase.start + j
      let state := chain.states index
      let step := state.incoming
      (state.source.continuationPath
          (g.withCriticalMarkers_wellFormed hg count)
          hground hinitial).segmentWord step.offset bound =
        (originalSegment j).map liftCriticalLabel) :
    MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight presentation.width
      (fun j =>
        (g.withCriticalMarkers count)
          |>.fixedBalancingPresentationBound bound presentation.arity
            ((g.withCriticalMarkers count).fixedTailSchemaBound
              presentation.depth (actionBound j)))
      path := by
  let extended := g.withCriticalMarkers count
  let hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have hbound : 0 < bound :=
    (extended.exposureBound_pos hnormal).trans_le hexposureBound
  have hprotected : presentation.ProtectsDepth bound :=
    presentation.protectsDepth_of_fixedBaseNonSinking
      hgExtended hdepth hnever
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
      have hpresentation := presentation.schema_instance_matches j
      have hrepresentative := trajectory.representative_matches index
      exact hpresentation.trans (by
        simpa [index, state, step, pivot] using hrepresentative)
    obtain ⟨X, children, hroot⟩ :=
      step.active_ground.exists_rootApplication
    obtain ⟨coverage⟩ :=
      segment.exists_markerStableSchemaBoundedWitnessedBalancingResult
        hg hnormal hexposureBound
        step.active_ground step.pivot_ground hfiller
        step.outer_derivation step.active_traceEquivalent_pivot
        (presentation.schema_supported j)
        (presentation.schema_hasPrefixWitness j)
        presentation.rankMax_le_arity
        (hprotected j)
        presentation.arguments_length
        presentation.arguments_ground
        hpivotInstance
        (presentation.schema_nodes_length_le_fixedTailSchemaBound
          j (actionBound j) (hactions j))
        (hpivotSchemaOriginal j)
        (by simpa [index, state, step] using hactivePrefixOriginal j)
        (originalStem j) (originalSegment j)
        (by simpa [index, state, step] using hstem j)
        (by simpa [index, state, step] using hsegment j)
        hroot
    have hword :
        step.outerStem ++
            ((state.source.continuationPath hgExtended hground hinitial).segmentWord
              step.offset bound) =
          path.word (chain.levels index) := by
      simpa [index, state, step, levels] using
        step.outerStem_append_labels
    exact ⟨coverage.castWord hword⟩

/-- Grammar-uniform widening of the marker-stable structured fixed-tail
stair. -/
public noncomputable def
    toMarkerStableWitnessedRegularActiveStairSequence_of_fixedTail_widened
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
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
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalExposureRebase)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j)))
    (hdepth : bound ≤ presentation.depth)
    (hnever : ∀ j,
      (g.withCriticalMarkers count).NeverSinksFromBase rebase.base
        (presentation.actions j))
    (actionBound : ℕ → ℕ)
    (hactions : ∀ j,
      (presentation.actions j).length ≤ actionBound j)
    (hpivotSchemaOriginal : ∀ j,
      (presentation.schema j).WellFormed
        g.ranks presentation.arity)
    (hactivePrefixOriginal : ∀ j,
      let index := rebase.start + j
      let step := (chain.states index).incoming
      ((SelectedBalancingSegment.active step.selected).depthPrefix 1)
        |>.head.toRegularTerm.WellFormed g.ranks
          (((SelectedBalancingSegment.active step.selected).depthPrefix 1)
            |>.schemaArity (g.withCriticalMarkers count).ranks))
    (originalStem originalSegment : ℕ → List (Label Action))
    (hstem : ∀ j,
      let index := rebase.start + j
      let step := (chain.states index).incoming
      step.outerStem = (originalStem j).map liftCriticalLabel)
    (hsegment : ∀ j,
      let index := rebase.start + j
      let state := chain.states index
      let step := state.incoming
      (state.source.continuationPath
          (g.withCriticalMarkers_wellFormed hg count)
          hground hinitial).segmentWord step.offset bound =
        (originalSegment j).map liftCriticalLabel)
    (hwidth : presentation.width ≤ targetWidth)
    (harity : presentation.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight targetWidth
      (fun j => max targetArity
        ((g.withCriticalMarkers count)
          |>.fixedBalancingPresentationBound bound presentation.arity
            ((g.withCriticalMarkers count).fixedTailSchemaBound
              presentation.depth (actionBound j))))
      path := by
  let source :=
    chain
      |>.toMarkerStableWitnessedRegularActiveStairSequence_of_fixedTail
        hg hnormal hground hinitial hexposureBound trajectory rebase
          hfiller presentation hdepth hnever actionBound hactions
          hpivotSchemaOriginal hactivePrefixOriginal
          originalStem originalSegment hstem hsegment
  apply source.widen filler hfiller hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
