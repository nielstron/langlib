module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotStairAssembly
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OperationalFixedTailPresentation

@[expose]
public section

/-!
# Structured stairs from an operational maximal rebase

This is the semantic endgame of `StructuredPivotStairBase`, with
`MaximalProgressRebase` replacing semantic maximal exposure.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain

/-- Assemble the structured balancing rows over an operationally rebased
fixed-tail presentation. -/
public noncomputable def
    toWitnessedRegularActiveStairSequence_of_progressFixedTail
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

/-- Grammar-uniform widening of the progress-rebased structured stair. -/
public noncomputable def
    toWitnessedRegularActiveStairSequence_of_progressFixedTail_widened
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
    (rebase : trajectory.MaximalProgressRebase)
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
  let source :=
    chain.toWitnessedRegularActiveStairSequence_of_progressFixedTail
      hg hnormal hground hinitial hexposureBound trajectory rebase
      hfiller presentation hdepth hnever actionBound hactions
  apply source.widen filler hfiller hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

end TracePath.StructuredPivotChain

/-- Uniform `M₂` output phrased with the operational maximal rebase. -/
@[expose] public def HasUniformStructuredPivotProgressRebaseBound
    (g : EncodedFirstOrderGrammar Action)
    (bound : ℕ) (actionBound : ℕ → ℕ) : Prop :=
  ∀ (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    (_hexposureBound : g.exposureBound hnormal ≤ bound)
    (initialLeft initialRight : RegularTerm)
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (_hnoRepeat : ¬path.HasDerivedRepeat)
    (initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound)
    (chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial),
    ∃ trajectory : chain.PivotTrajectory,
      ∃ rebase : trajectory.MaximalProgressRebase,
        ∀ j, (rebase.labels j).length ≤ actionBound j

/-- An operationally bounded structured pivot suffix supplies the witnessed
regular active stair base. -/
public theorem
    hasWitnessedRegularActiveStairBase_of_structuredPivotProgressRebaseBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hbound : 0 < bound)
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (actionBound : ℕ → ℕ)
    (hm2 :
      g.HasUniformStructuredPivotProgressRebaseBound
        bound actionBound) :
    g.HasWitnessedRegularActiveStairBase
      (g.fixedTailWidthBound bound) := by
  let targetWidth := g.fixedTailWidthBound bound
  let targetArity := g.fixedTailArityBound bound
  let growth : ℕ → ℕ := fun j =>
    max 1 (max targetArity
      (g.fixedBalancingPresentationBound bound targetArity
        (g.fixedTailSchemaBound bound (actionBound j))))
  refine ⟨growth, ?_⟩
  intro initialLeft initialRight hground hinitial path
  by_cases hrepeat : path.HasDerivedRepeat
  · exact Or.inl
      ((path.eventuallyBoundedOpenSound_of_hasDerivedRepeat hrepeat).mono
        (by
          dsimp [growth]
          exact Nat.le_max_left _ _))
  · let source : path.DerivedPairAt 0 :=
      { left := initialLeft
        right := initialRight
        derivation := by
          simpa [path.starts_word] using
            (CertificateDerivable.axiom
              (basis := ([] : List BasisPair)) hground) }
    obtain ⟨initial⟩ :=
      source.exists_initialStructuredBalancingState
        hg hnormal hground hinitial hrepeat hexposureBound
    obtain ⟨chain⟩ :=
      path.exists_structuredPivotChain_of_noDerivedRepeat
        hnormal hrepeat hexposureBound initial
    obtain ⟨trajectory, rebase, hrebaseBound⟩ :=
      hm2 hg hnormal hexposureBound initialLeft initialRight path
        hground hinitial hrepeat initial chain
    have hfiller : initialLeft.Ground g.ranks := by
      unfold groundPairCode at hground
      rw [Bool.and_eq_true] at hground
      exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hground.1
    obtain ⟨presentation, hpresentationDepth, hnever⟩ :=
      rebase.exists_fixedTailPivotPresentation_atDepth
        hfiller bound hbound
    have hpresentationDepthLe : bound ≤ presentation.depth := by
      omega
    have hactions : ∀ j,
        (presentation.actions j).length ≤ actionBound j := by
      intro j
      have hlength := congrArg List.length (presentation.labels_eq j)
      have hlength' :
          (rebase.labels j).length =
            (presentation.actions j).length := by
        simpa using hlength
      rw [← hlength']
      exact hrebaseBound j
    have hwidth : presentation.width ≤ targetWidth := by
      dsimp [targetWidth]
      simpa [hpresentationDepth] using
        presentation.width_le_fixedTailWidthBound
    have harity : presentation.arity ≤ targetArity := by
      dsimp [targetArity]
      simpa [hpresentationDepth] using
        presentation.arity_le_fixedTailArityBound
    have htargetWidth : targetWidth ≤ targetArity := by
      dsimp [targetWidth, targetArity, fixedTailArityBound]
      exact Nat.le_max_left _ _
    let stair :=
      chain
        |>.toWitnessedRegularActiveStairSequence_of_progressFixedTail_widened
          hg hnormal hground hinitial hexposureBound trajectory rebase
          hfiller presentation hpresentationDepthLe hnever
          actionBound hactions hwidth harity htargetWidth
    refine Or.inr ⟨
      { arguments := stair.arguments
        levels := stair.levels
        levels_strictMono := stair.levels_strictMono
        covered := ?_ }⟩
    intro j
    obtain ⟨coverage⟩ := stair.covered j
    refine ⟨coverage.mono ?_⟩
    have harityBound :
        g.fixedBalancingPresentationBound bound presentation.arity
            (g.fixedTailSchemaBound presentation.depth (actionBound j)) ≤
          g.fixedBalancingPresentationBound bound targetArity
            (g.fixedTailSchemaBound bound (actionBound j)) := by
      rw [hpresentationDepth]
      unfold fixedBalancingPresentationBound
      exact max_le_max harity (le_refl _)
    have hlocal :
        max targetArity
            (g.fixedBalancingPresentationBound bound presentation.arity
              (g.fixedTailSchemaBound presentation.depth
                (actionBound j))) ≤
          max targetArity
            (g.fixedBalancingPresentationBound bound targetArity
              (g.fixedTailSchemaBound bound (actionBound j))) :=
      max_le_max (le_refl _) harityBound
    exact hlocal.trans (Nat.le_max_right _ _)

end EncodedFirstOrderGrammar

end DCFEquivalence
