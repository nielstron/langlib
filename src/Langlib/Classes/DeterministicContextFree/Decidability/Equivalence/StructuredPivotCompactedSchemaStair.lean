module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotSchemaStairBase
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalSinkSchemaCompaction

@[expose]
public section

/-!
# Structured stairs from compact pivot-schema representatives

The direct schema-bound stair constructor uses the raw fixed-tail residual.
The `M₂` recurrence instead obtains a compact schema semantically equivalent
to that residual, retaining the same fixed argument arity, active-prefix
witness, protected application depth, and a uniform graph-size bound.

This module feeds those compact representatives directly to Proposition 45.
No accumulated action-word bound is used.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain

/-- Assemble structured balancing rows using a pointwise compact
representative of every fixed-tail pivot schema. -/
public noncomputable def
    toWitnessedRegularActiveStairSequence_of_progressCompactedSchemas
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
    (rebase : trajectory.MaximalProgressRebase)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      rebase.base filler rebase.labels
      (fun count =>
        trajectory.representatives (rebase.start + count)))
    (schemaDepth : ℕ → ℕ)
    (compactions : ∀ count,
      ProtectedFiniteSchemaCompaction g.ranks
        presentation.arity presentation.width bound
        (schemaDepth count) (presentation.schema count)) :
    WitnessedRegularActiveStairSequence g
      initialLeft initialRight presentation.width
      (fun count =>
        g.fixedBalancingPresentationBound bound
          presentation.arity
          (RegularTerm.finiteSchemaNodeBound
            g.ranks (schemaDepth count)))
      path := by
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
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
    let compaction := compactions count
    have hargumentsClosed :
        ∀ argument ∈ presentation.arguments,
          argument.ReferenceClosed := by
      intro argument hargument
      exact RegularTerm.referenceClosed_of_ground
        (presentation.arguments_ground argument hargument)
    have hcompactInstance :
        (compaction.compact.instantiate presentation.arguments)
          |>.UnfoldingEquivalent
            ((presentation.schema count).instantiate
              presentation.arguments) := by
      exact RegularTerm.UnfoldingEquivalent.instantiate_sameArguments
        (ranks := g.ranks) compaction.equivalent
        (by
          rw [presentation.arguments_length]
          exact compaction.wellFormed)
        (by
          rw [presentation.arguments_length]
          exact (presentation.schema_supported count).1)
        hargumentsClosed
    have hpivotInstance :
        (compaction.compact.instantiate presentation.arguments)
          |>.UnfoldingEquivalent
            (SelectedBalancingSegment.pivot step.selected) := by
      have hpresentation :=
        presentation.schema_instance_matches count
      have hrepresentative :=
        trajectory.representative_matches index
      exact hcompactInstance.trans
        (hpresentation.trans (by
          simpa [index, state, step, pivot] using hrepresentative))
    obtain ⟨X, children, hroot⟩ :=
      step.active_ground.exists_rootApplication
    obtain ⟨coverage⟩ :=
      segment.exists_schemaBoundedWitnessedBalancingResult
        hg hnormal hexposureBound
        step.active_ground step.pivot_ground hfiller
        step.outer_derivation step.active_traceEquivalent_pivot
        compaction.supported
        compaction.hasPrefixWitness
        presentation.rankMax_le_arity
        compaction.applicationDepth
        presentation.arguments_length
        presentation.arguments_ground
        hpivotInstance
        compaction.nodes_length_le
        hroot
    have hword :
        step.outerStem ++
            (state.source.continuationPath hg hground hinitial).segmentWord
              step.offset bound =
          path.word (chain.levels index) := by
      simpa [index, state, step, levels] using
        step.outerStem_append_labels
    exact ⟨coverage.castWord hword⟩

/-- Choice-friendly wrapper for pointwise existential compactions produced by
the `M₂` recurrence. -/
public noncomputable def
    toWitnessedRegularActiveStairSequence_of_progressCompactedSchemas_nonempty
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
    (rebase : trajectory.MaximalProgressRebase)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      rebase.base filler rebase.labels
      (fun count =>
        trajectory.representatives (rebase.start + count)))
    (schemaDepth : ℕ → ℕ)
    (compactions : ∀ count,
      Nonempty (ProtectedFiniteSchemaCompaction g.ranks
        presentation.arity presentation.width bound
        (schemaDepth count) (presentation.schema count))) :
    WitnessedRegularActiveStairSequence g
      initialLeft initialRight presentation.width
      (fun count =>
        g.fixedBalancingPresentationBound bound
          presentation.arity
          (RegularTerm.finiteSchemaNodeBound
            g.ranks (schemaDepth count)))
      path :=
  chain.toWitnessedRegularActiveStairSequence_of_progressCompactedSchemas
    hg hnormal hground hinitial hexposureBound trajectory rebase
    hfiller presentation schemaDepth
    (fun count => Classical.choice (compactions count))

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
