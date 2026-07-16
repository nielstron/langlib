module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotExposureRebasing
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailUniformBounds
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailPresentationWidening
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaBalancingBoundedCoverage

@[expose]
public section

/-!
# Fixed-tail stairs on a structured pivot chain

The older fixed-tail assembly modules work with balancing opportunities on
the raw residual path.  Proposition 49 recursively balances certificate-
derived pairs, so its retained segments live instead on the canonical
continuation path of each derived state.

This file performs the same local Proposition-45 assembly directly on a
`StructuredPivotChain`.  A fixed-tail presentation of the concrete pivot
representatives supplies one common argument tuple; unfolding equivalence
transports each represented pivot back to the exact selected segment.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredDerivedBalancingStep

/-- Absolute word immediately before the retained balancing segment. -/
@[expose] public def outerStem
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) : List (Label Action) :=
  path.word (start + step.offset)

/-- The selected active/pivot pair is already derivable at the pre-segment
absolute word, with the selected orientation respected. -/
public theorem outer_derivation
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) :
    CertificateDerivable g initialLeft initialRight []
      (.pair step.outerStem
        (SelectedBalancingSegment.active step.selected)
        (SelectedBalancingSegment.pivot step.selected)) := by
  let current :=
    (source.continuationAt hg hground hinitial step.offset).target
  cases step.selected with
  | left segment =>
      simpa [outerStem, SelectedBalancingSegment.active,
        SelectedBalancingSegment.pivot,
        DerivedPairAt.continuationPath, current] using
          current.derivation
  | right segment =>
      simpa [outerStem, SelectedBalancingSegment.active,
        SelectedBalancingSegment.pivot,
        DerivedPairAt.continuationPath, current] using
          CertificateDerivable.symmetry current.derivation

/-- The selected active and pivot terms remain trace equivalent. -/
public theorem active_traceEquivalent_pivot
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) :
    g.TraceEquivalent
      (SelectedBalancingSegment.active step.selected)
      (SelectedBalancingSegment.pivot step.selected) :=
  step.outer_derivation
    |>.pair_traceEquivalent_of_initial
      (guardedContextLaws_of_wellFormed hg) hinitial

/-- The selected segment word closes the pre-segment stem at the exact chain
endpoint. -/
public theorem outerStem_append_labels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) :
    step.outerStem ++
        (source.continuationPath hg hground hinitial).segmentWord
          step.offset bound =
      path.word step.endLevel := by
  rw [outerStem]
  change path.word (start + step.offset) ++
      (source.continuationPath hg hground hinitial).segmentWord
        step.offset bound =
    path.word (start + step.offset + bound)
  rw [source.continuationPath_segmentWord
    hg hground hinitial step.offset bound]
  exact (path.word_add (start + step.offset) bound).symm

end TracePath.StructuredDerivedBalancingStep

namespace TracePath.StructuredPivotChain

/-- A fixed-tail presentation of a suffix of the concrete pivot trajectory
assembles into a witnessed regular active stair on the original path. -/
public noncomputable def toWitnessedRegularActiveStairSequence_of_fixedTail
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalExposureRebase)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      rebase.base filler rebase.labels
      (fun count =>
        trajectory.representatives (rebase.start + count)))
    (hdepth : bound ≤ presentation.depth)
    (hnever : ∀ count,
      g.NeverSinksFromBase rebase.base
        (presentation.actions count))
    (actionBound : ℕ → ℕ)
    (hactions : ∀ count,
      (presentation.actions count).length ≤ actionBound count) :
    WitnessedRegularActiveStairSequence g
      initialLeft initialRight presentation.width
      (fun count =>
        g.fixedBalancingPresentationBound bound presentation.arity
          (g.fixedTailSchemaBound presentation.depth
            (actionBound count)))
      path := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
  have hprotected : presentation.ProtectsDepth bound :=
    presentation.protectsDepth_of_fixedBaseNonSinking
      hg hdepth hnever
  let levels : ℕ → ℕ :=
    fun count => chain.levels (rebase.start + count)
  refine
    { arguments := presentation.arguments
      levels := levels
      levels_strictMono := ?_
      covered := ?_ }
  · exact (chain.levels_strictMono hbound).comp
      (by
        intro i j hij
        exact Nat.add_lt_add_left hij rebase.start)
  · intro count
    let index := rebase.start + count
    let state := chain.states index
    let step := state.incoming
    let segment := SelectedBalancingSegment.asSegment step.selected
    have hpivotInstance :
        ((presentation.schema count).instantiate
            presentation.arguments).UnfoldingEquivalent
          (SelectedBalancingSegment.pivot step.selected) := by
      have hpresentation := presentation.schema_instance_matches count
      have hrepresentative := trajectory.representative_matches index
      exact hpresentation.trans (by
        simpa [index, state, step, pivot] using hrepresentative)
    obtain ⟨X, children, hroot⟩ :=
      step.active_ground.exists_rootApplication
    obtain ⟨coverage⟩ :=
      segment.exists_schemaBoundedWitnessedBalancingResult
        hg hnormal hexposureBound
        step.active_ground step.pivot_ground hfiller
        step.outer_derivation step.active_traceEquivalent_pivot
        (presentation.schema_supported count)
        (presentation.schema_hasPrefixWitness count)
        presentation.rankMax_le_arity
        (hprotected count)
        presentation.arguments_length
        presentation.arguments_ground
        hpivotInstance
        (presentation.schema_nodes_length_le_fixedTailSchemaBound
          count (actionBound count) (hactions count))
        hroot
    have hword :
        step.outerStem ++
            (state.source.continuationPath hg hground hinitial).segmentWord
              step.offset bound =
          path.word (chain.levels index) := by
      simpa [index, state, step, levels] using
        step.outerStem_append_labels
    exact ⟨coverage.castWord hword⟩

/-- Grammar-uniform widening of the structured fixed-tail stair. -/
public noncomputable def toWitnessedRegularActiveStairSequence_of_fixedTail_widened
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound targetWidth targetArity : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalExposureRebase)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      rebase.base filler rebase.labels
      (fun count =>
        trajectory.representatives (rebase.start + count)))
    (hdepth : bound ≤ presentation.depth)
    (hnever : ∀ count,
      g.NeverSinksFromBase rebase.base
        (presentation.actions count))
    (actionBound : ℕ → ℕ)
    (hactions : ∀ count,
      (presentation.actions count).length ≤ actionBound count)
    (hwidth : presentation.width ≤ targetWidth)
    (harity : presentation.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    WitnessedRegularActiveStairSequence g
      initialLeft initialRight targetWidth
      (fun count => max targetArity
        (g.fixedBalancingPresentationBound bound presentation.arity
          (g.fixedTailSchemaBound presentation.depth
            (actionBound count))))
      path := by
  let source := chain.toWitnessedRegularActiveStairSequence_of_fixedTail
    hg hnormal hground hinitial hexposureBound trajectory rebase
      hfiller presentation hdepth hnever actionBound hactions
  apply source.widen filler hfiller hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
