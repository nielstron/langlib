module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotProgressStairBase
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailArgumentProtection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailSchemaTransitions

@[expose]
public section

/-!
# Structured stairs from direct pivot-schema bounds

Proposition 49 bounds the presentation of the `j`th pivot context directly.
It does not bound the entire accumulated action word reaching that pivot.
This file exposes the exact interface consumed by the stair construction:
one operational maximal rebase, one fixed-tail presentation, and a pointwise
grammar-uniform bound on the residual schemas themselves.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain

/-- Assemble structured balancing rows from direct bounds on the fixed-tail
pivot schemas. -/
public noncomputable def
    toWitnessedRegularActiveStairSequence_of_progressSchemaBound
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
    (schemaBound : ℕ → ℕ)
    (hschema : ∀ count,
      (presentation.schema count).nodes.length ≤
        schemaBound count) :
    WitnessedRegularActiveStairSequence g
      initialLeft initialRight presentation.width
      (fun count =>
        g.fixedBalancingPresentationBound bound
          presentation.arity (schemaBound count))
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
      have hpresentation :=
        presentation.schema_instance_matches count
      have hrepresentative :=
        trajectory.representative_matches index
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
        (hschema count)
        hroot
    have hword :
        step.outerStem ++
            (state.source.continuationPath hg hground hinitial).segmentWord
              step.offset bound =
          path.word (chain.levels index) := by
      simpa [index, state, step, levels] using
        step.outerStem_append_labels
    exact ⟨coverage.castWord hword⟩

end TracePath.StructuredPivotChain

/-- The direct quantitative output required from the operational `M₂`
argument.  The filler is quantified because the stair constructor may choose
either initial component as its harmless padding term. -/
@[expose] public def HasUniformStructuredPivotProgressSchemaBound
    (g : EncodedFirstOrderGrammar Action)
    (bound : ℕ) (schemaBound : ℕ → ℕ) : Prop :=
  ∀ (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    (_hexposureBound : g.exposureBound hnormal ≤ bound)
    (initialLeft initialRight filler : RegularTerm)
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (_hnoRepeat : ¬path.HasDerivedRepeat)
    (_hfiller : filler.Ground g.ranks)
    (initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound)
    (chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial),
    ∃ trajectory : chain.PivotTrajectory,
      ∃ rebase : trajectory.MaximalProgressRebase,
        ∃ presentation : FixedTailPivotPresentation g
            rebase.base filler rebase.labels
            (fun count =>
              trajectory.representatives (rebase.start + count)),
          presentation.depth = bound ∧
            (∀ count,
              g.NeverSinksFromBase rebase.base
                (presentation.actions count)) ∧
            ∀ count,
              (presentation.schema count).nodes.length ≤
                schemaBound count

/-- A grammar-uniform direct schema bound supplies the witnessed regular
active stair base without any accumulated-word length hypothesis. -/
public theorem
    hasWitnessedRegularActiveStairBase_of_structuredPivotProgressSchemaBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (_hbound : 0 < bound)
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (schemaBound : ℕ → ℕ)
    (hm2 :
      g.HasUniformStructuredPivotProgressSchemaBound
        bound schemaBound) :
    g.HasWitnessedRegularActiveStairBase
      (g.fixedTailWidthBound bound) := by
  let targetWidth := g.fixedTailWidthBound bound
  let targetArity := g.fixedTailArityBound bound
  let growth : ℕ → ℕ := fun count =>
    max 1 (max targetArity
      (g.fixedBalancingPresentationBound
        bound targetArity (schemaBound count)))
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
    have hfiller : initialLeft.Ground g.ranks := by
      unfold groundPairCode at hground
      rw [Bool.and_eq_true] at hground
      exact
        (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hground.1
    obtain ⟨trajectory, rebase, presentation, hpresentationDepth,
        hnever, hschema⟩ :=
      hm2 hg hnormal hexposureBound initialLeft initialRight
        initialLeft path hground hinitial hrepeat hfiller initial chain
    have hpresentationDepthLe :
        bound ≤ presentation.depth := by
      omega
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
      chain.toWitnessedRegularActiveStairSequence_of_progressSchemaBound
        hg hnormal hground hinitial hexposureBound trajectory rebase
        hfiller presentation hpresentationDepthLe hnever
        schemaBound hschema
    let widened :=
      stair.widen initialLeft hfiller hwidth
        (by
          change presentation.arguments.length ≤ targetArity
          rw [presentation.arguments_length]
          exact harity)
        htargetWidth
    refine Or.inr ⟨
      { arguments := widened.arguments
        levels := widened.levels
        levels_strictMono := widened.levels_strictMono
        covered := ?_ }⟩
    intro count
    obtain ⟨coverage⟩ := widened.covered count
    refine ⟨coverage.mono ?_⟩
    have hlocal :
        max targetArity
            (g.fixedBalancingPresentationBound
              bound presentation.arity (schemaBound count)) ≤
          max targetArity
            (g.fixedBalancingPresentationBound
              bound targetArity (schemaBound count)) := by
      apply max_le_max (le_refl _)
      unfold fixedBalancingPresentationBound
      exact max_le_max harity (le_refl _)
    exact hlocal.trans (Nat.le_max_right _ _)

end EncodedFirstOrderGrammar

end DCFEquivalence
