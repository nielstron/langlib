module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedStructuredPivotStairAssembly
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerCancellation
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteSchemaCompaction

@[expose]
public section

/-!
# Marker-stable stairs from compact guarded pivot schemas

The critical fixed-tail presentation retains the exact guarded-depth
invariant needed to reflect original-action continuations.  The quantitative
`M₂` recurrence, however, bounds a finite schema semantically equivalent to
the raw residual rather than the raw residual graph itself.

This module records the minimal compact representative needed by the guarded
marker-stable balancing theorem and feeds a pointwise family of such
representatives directly into the structured stair assembly.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A finite schema compaction which retains the guarded depth used by
critical-marker reflection. -/
public structure GuardedFiniteSchemaCompaction
    (ranks : List ℕ) (arity width guardDepth depth : ℕ)
    (guard : ℕ → Prop) (schema : RegularTerm)
    extends RegularTerm.FiniteSchemaCompaction
      ranks arity width depth schema where
  guardedApplicationDepth :
    compact.GuardedApplicationDepth guard guardDepth

/-- Semantic compaction preserves guarded application depth. -/
public theorem exists_guardedFiniteSchemaCompaction
    {ranks : List ℕ} {arity width guardDepth depth : ℕ}
    {guard : ℕ → Prop} {schema : RegularTerm}
    (hwellFormed : schema.WellFormed ranks arity)
    (hwitness : schema.HasPrefixWitness width)
    (hwidth : width ≤ arity)
    (hrankMax : ranks.foldr max 0 ≤ arity)
    (hguarded : schema.GuardedApplicationDepth guard guardDepth)
    (hdepth : schema.UnfoldingDepthAtMost depth) :
    Nonempty (GuardedFiniteSchemaCompaction
      ranks arity width guardDepth depth guard schema) := by
  obtain ⟨compaction⟩ :=
    RegularTerm.exists_finiteSchemaCompaction
      hwellFormed hwitness hwidth hrankMax hdepth
  exact ⟨
    { toFiniteSchemaCompaction := compaction
      guardedApplicationDepth :=
        compaction.equivalent.symm.guardedApplicationDepth hguarded }⟩

/-- Critical-instance cancellation combines the actual residual's guarded
depth with an auxiliary residual's quantitative unfolding-depth bound. -/
public theorem
    exists_guardedFiniteSchemaCompaction_of_criticalInstances
    {g : EncodedFirstOrderGrammar Action}
    {arity width guardDepth depth : ℕ}
    {guard : ℕ → Prop} {actual auxiliary : RegularTerm}
    (hactual : actual.WellFormed g.ranks arity)
    (hauxiliary : auxiliary.WellFormed g.ranks arity)
    (hwitness : actual.HasPrefixWitness width)
    (hwidth : width ≤ arity)
    (hrankMax : g.ranks.foldr max 0 ≤ arity)
    (hguarded : actual.GuardedApplicationDepth guard guardDepth)
    (hauxiliaryDepth :
      auxiliary.UnfoldingDepthAtMost depth)
    (hcritical :
      (actual.instantiate (g.criticalArguments arity))
        |>.UnfoldingEquivalent
          (auxiliary.instantiate (g.criticalArguments arity))) :
    Nonempty (GuardedFiniteSchemaCompaction g.ranks
      arity width guardDepth depth guard actual) := by
  have hopen : actual.UnfoldingEquivalent auxiliary :=
    g.unfoldingEquivalent_of_criticalInstantiation
      hactual hauxiliary hcritical
  have hactualDepth : actual.UnfoldingDepthAtMost depth :=
    hopen.symm.unfoldingDepthAtMost hauxiliaryDepth
  exact exists_guardedFiniteSchemaCompaction
    hactual hwitness hwidth hrankMax hguarded hactualDepth

/-- Convenience form with a finite auxiliary schema and a raw node bound. -/
public theorem
    exists_guardedFiniteSchemaCompaction_of_criticalInstances_of_nodes
    {g : EncodedFirstOrderGrammar Action}
    {arity width guardDepth depth : ℕ}
    {guard : ℕ → Prop} {actual auxiliary : RegularTerm}
    (hactual : actual.WellFormed g.ranks arity)
    (hauxiliary : auxiliary.WellFormed g.ranks arity)
    (hwitness : actual.HasPrefixWitness width)
    (hwidth : width ≤ arity)
    (hrankMax : g.ranks.foldr max 0 ≤ arity)
    (hguarded : actual.GuardedApplicationDepth guard guardDepth)
    (hauxiliaryFinite : auxiliary.UnfoldsFinite)
    (hauxiliarySize : auxiliary.nodes.length ≤ depth)
    (hcritical :
      (actual.instantiate (g.criticalArguments arity))
        |>.UnfoldingEquivalent
          (auxiliary.instantiate (g.criticalArguments arity))) :
    Nonempty (GuardedFiniteSchemaCompaction g.ranks
      arity width guardDepth depth guard actual) := by
  apply g.exists_guardedFiniteSchemaCompaction_of_criticalInstances
    hactual hauxiliary hwitness hwidth hrankMax hguarded
  · exact RegularTerm.UnfoldingDepthAtMost.mono
      hauxiliaryFinite.unfoldingDepthAtMost_nodes hauxiliarySize
  · exact hcritical

namespace TracePath.StructuredPivotChain

/-- Assemble a marker-stable structured stair from pointwise compact
representatives of the guarded fixed-tail schemas. -/
public noncomputable def
    toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressCompactedSchemas
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
    (schemaDepth : ℕ → ℕ)
    (compactions : ∀ j,
      GuardedFiniteSchemaCompaction g.ranks
        presentation.arity presentation.width presentation.depth
        (schemaDepth j)
        (g.CriticalBoundaryGuard count
          (g.criticalDepthPrefix presentation.depth base))
        (presentation.schema j))
    (hendpoint : ∀ j, NoCriticalMarkerActions
      (path.word (chain.levels (rebase.start + j)))) :
    MarkerStableWitnessedRegularActiveStairSequence
      g count initialLeft initialRight presentation.width
      (fun j =>
        (g.withCriticalMarkers count)
          |>.fixedBalancingPresentationBound
            bound presentation.arity
            (RegularTerm.finiteSchemaNodeBound
              g.ranks (schemaDepth j)))
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
    let segmentLabels :=
      (state.source.continuationPath
        hgExtended hground hinitial).segmentWord step.offset bound
    let segment := SelectedBalancingSegment.asSegment step.selected
    let compaction := compactions j
    have hargumentsClosed :
        ∀ argument ∈ presentation.arguments,
          argument.ReferenceClosed := by
      intro argument hargument
      exact RegularTerm.referenceClosed_of_ground
        (presentation.arguments_ground argument hargument)
    have hcompactWellFormedExtended :
        compaction.compact.WellFormed
          extended.ranks presentation.arity := by
      simpa [extended] using
        g.wellFormed_extendedRanks count compaction.wellFormed
    have hcompactSupported :
        RegularTerm.SupportedByPrefix
          extended.ranks presentation.arity presentation.width
          compaction.compact :=
      compaction.hasPrefixWitness.supportedByPrefix
        hcompactWellFormedExtended presentation.width_le_arity
    have hcompactInstance :
        (compaction.compact.instantiate presentation.arguments)
          |>.UnfoldingEquivalent
            ((presentation.schema j).instantiate
              presentation.arguments) := by
      exact RegularTerm.UnfoldingEquivalent.instantiate_sameArguments
        (ranks := g.ranks) compaction.equivalent
        (by
          rw [presentation.arguments_length]
          exact compaction.wellFormed)
        (by
          rw [presentation.arguments_length]
          exact presentation.schema_wellFormed_original j)
        hargumentsClosed
    have hpivotInstance :
        (compaction.compact.instantiate presentation.arguments)
          |>.UnfoldingEquivalent
            (SelectedBalancingSegment.pivot step.selected) := by
      have hpresentation :=
        presentation.schema_instance_matches j
      have hrepresentative :=
        trajectory.representative_matches index
      exact hcompactInstance.trans
        (hpresentation.trans (by
          simpa [index, state, step, pivot] using hrepresentative))
    obtain ⟨originalStem, originalSegment,
        hstem, hsegment⟩ :=
      chain.exists_originalStemAndSegment_of_endpoint_noMarkerActions
        (hg := hg) index (hendpoint j)
    have hactivePrefixOriginal :=
      chain.activePrefixOriginal_of_endpoint_noMarkerActions
        (hg := hg) hbound index (hendpoint j)
    obtain ⟨X, children, hroot⟩ :=
      step.active_ground.exists_rootApplication
    have hpivotNoVariable :
        ∀ actions : List (Action ⊕ ℕ),
          segmentLabels = actions.map Sum.inl →
            extended.NoVariableBefore
              compaction.compact actions := by
      intro actions hlabelsActions
      have hwordOriginal :
          actions.map Sum.inl =
            originalSegment.map liftCriticalLabel := by
        calc
          actions.map Sum.inl = segmentLabels := hlabelsActions.symm
          _ = originalSegment.map liftCriticalLabel := by
            simpa [index, state, step, segmentLabels] using hsegment
      obtain ⟨originalActions, hactions, _horiginalLabels⟩ :=
        exists_originalActions_of_map_inl_eq_map_liftCriticalLabel
          hwordOriginal
      have hsegmentLength : segmentLabels.length = bound := by
        simp [segmentLabels, index, state, step]
      have hlengthMap := congrArg List.length hlabelsActions
      simp only [List.length_map] at hlengthMap
      have hlengthEq : actions.length = bound := by
        omega
      have hlength : actions.length ≤ presentation.depth := by
        rw [hlengthEq]
        exact hdepth
      have hpivotRun :
          extended.runActions? actions
              (SelectedBalancingSegment.pivot step.selected) =
            some segment.pivotTarget := by
        change extended.run? (actions.map Sum.inl)
            (SelectedBalancingSegment.pivot step.selected) =
          some segment.pivotTarget
        rw [← hlabelsActions]
        simpa [extended, segmentLabels, segment, index, state, step] using
          segment.pivot_run
      exact g.criticalNoVariableBefore_of_guardedApplicationDepth
        (target := segment.pivotTarget)
        hg presentation.base_ground presentation.filler_ground
        hcompactWellFormedExtended
        compaction.guardedApplicationDepth hlength
        originalActions hactions hpivotInstance
        (RegularTerm.referenceClosed_of_ground step.pivot_ground)
        hpivotRun
    have hexposingNoVariable :
        ∀ position, position.1.val = X →
          extended.NoVariableBefore compaction.compact
            (extended.exposingWord hnormal position) := by
      intro position hposition
      let word := extended.exposingWord hnormal position
      have hshort : word.length < bound :=
        lt_of_lt_of_le
          (extended.exposingWord_length_lt_exposureBound
            hnormal position)
          hexposureBound
      have hlength : word.length ≤ presentation.depth :=
        (Nat.le_of_lt hshort).trans hdepth
      obtain ⟨originalActions, hwordOriginal⟩ :=
        g.withCriticalMarkers_exposingWord_exists_originalActions
          hg hnormal position
      have hrootPosition :
          (SelectedBalancingSegment.active step.selected).rootApplication? =
            some (position.1.val, children) := by
        simpa [hposition] using hroot
      have hrank :=
        step.active_ground.root_rank_arity hrootPosition
      have hrankGet :
          extended.ranks.get position.1 = children.length := by
        apply Option.some.inj
        calc
          some (extended.ranks.get position.1) =
              extended.ranks[position.1.val]? := by simp
          _ = some children.length := hrank
      have hchildLt :
          position.2.val < children.length := by
        exact lt_of_lt_of_eq position.2.isLt hrankGet
      let child := children[position.2.val]
      have hchild :
          children[position.2.val]? = some child :=
        List.getElem?_eq_getElem hchildLt
      obtain ⟨_activeTarget, pivotTarget, _hactiveRun,
          _hactiveMatches, hpivotRun⟩ :=
        segment.exists_pivotTarget_for_exposedSuccessor
          hgExtended step.active_ground position
          (extended.exposingWord_exposes hnormal position)
          hshort hrootPosition hchild
      exact g.criticalNoVariableBefore_of_guardedApplicationDepth
        (target := pivotTarget)
        hg presentation.base_ground presentation.filler_ground
        hcompactWellFormedExtended
        compaction.guardedApplicationDepth hlength
        originalActions (by simpa [word] using hwordOriginal)
        hpivotInstance
        (RegularTerm.referenceClosed_of_ground step.pivot_ground)
        (by simpa [word] using hpivotRun)
    obtain ⟨coverage⟩ :=
      segment
        |>.exists_markerStableSchemaBoundedWitnessedBalancingResult_of_noVariableBefore
          hg hnormal hexposureBound
          step.active_ground step.pivot_ground
          presentation.filler_ground
          step.outer_derivation
          step.active_traceEquivalent_pivot
          hcompactSupported
          compaction.hasPrefixWitness
          presentation.rankMax_le_arity
          hpivotNoVariable hexposingNoVariable
          presentation.arguments_length
          presentation.arguments_ground
          hpivotInstance
          compaction.nodes_length_le
          compaction.wellFormed
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

/-- Widen the compacted guarded marker-stable stair to common target width
and arity bounds. -/
public noncomputable def
    toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressCompactedSchemas_widened
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
    (schemaDepth : ℕ → ℕ)
    (compactions : ∀ j,
      GuardedFiniteSchemaCompaction g.ranks
        presentation.arity presentation.width presentation.depth
        (schemaDepth j)
        (g.CriticalBoundaryGuard count
          (g.criticalDepthPrefix presentation.depth base))
        (presentation.schema j))
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
            bound presentation.arity
            (RegularTerm.finiteSchemaNodeBound
              g.ranks (schemaDepth j))))
      path := by
  let source :=
    chain
      |>.toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressCompactedSchemas
        hg hnormal hground hinitial hexposureBound
        trajectory rebase presentation hdepth schemaDepth
        compactions hendpoint
  apply source.widen filler presentation.filler_ground hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

/-- Choice-friendly wrapper for pointwise existential guarded compactions. -/
public noncomputable def
    toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressCompactedSchemas_nonempty
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
    (schemaDepth : ℕ → ℕ)
    (compactions : ∀ j,
      Nonempty (GuardedFiniteSchemaCompaction g.ranks
        presentation.arity presentation.width presentation.depth
        (schemaDepth j)
        (g.CriticalBoundaryGuard count
          (g.criticalDepthPrefix presentation.depth base))
        (presentation.schema j)))
    (hendpoint : ∀ j, NoCriticalMarkerActions
      (path.word (chain.levels (rebase.start + j)))) :
    MarkerStableWitnessedRegularActiveStairSequence
      g count initialLeft initialRight presentation.width
      (fun j =>
        (g.withCriticalMarkers count)
          |>.fixedBalancingPresentationBound
            bound presentation.arity
            (RegularTerm.finiteSchemaNodeBound
              g.ranks (schemaDepth j)))
      path :=
  chain
    |>.toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressCompactedSchemas
      hg hnormal hground hinitial hexposureBound
      trajectory rebase presentation hdepth schemaDepth
      (fun j => Classical.choice (compactions j)) hendpoint

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
