module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedFixedTailPresentation
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerBalancingResultCoverage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerNormalForm

@[expose]
public section

/-!
# Marker-stable balancing from guarded reflection

This is the marker-aware counterpart of
`exists_markerStableSchemaBoundedWitnessedBalancingResult`.  Instead of a
blanket application-depth premise, it accepts the exact no-variable facts for
the balancing word and every selected normal-form exposing word.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

public theorem
    BalancingSegment.exists_markerStableSchemaBoundedWitnessedBalancingResult_of_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {bound : ℕ}
    (hexposureBound :
      (g.withCriticalMarkers count).exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm}
    {labels : List (Label (Action ⊕ ℕ))}
    (segment : BalancingSegment (g.withCriticalMarkers count)
      bound active pivot labels)
    (hactive : active.Ground (g.withCriticalMarkers count).ranks)
    (hpivot : pivot.Ground (g.withCriticalMarkers count).ranks)
    {filler : RegularTerm}
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label (Action ⊕ ℕ))}
    (houter : CertificateDerivable (g.withCriticalMarkers count)
      initialLeft initialRight [] (.pair stem active pivot))
    (hequivalent :
      (g.withCriticalMarkers count).TraceEquivalent active pivot)
    {pivotSchema : RegularTerm} {arguments : List RegularTerm}
    {arity width schemaBound : ℕ}
    (hpivotSupported : RegularTerm.SupportedByPrefix
      (g.withCriticalMarkers count).ranks
      arity width pivotSchema)
    (hpivotWitness : pivotSchema.HasPrefixWitness width)
    (hpadding :
      (g.withCriticalMarkers count).ranks.foldr max 0 ≤ arity)
    (hpivotNoVariable :
      ∀ actions : List (Action ⊕ ℕ),
        labels = actions.map Sum.inl →
          (g.withCriticalMarkers count).NoVariableBefore
            pivotSchema actions)
    {X : ℕ} {children : List ℕ}
    (hexposingNoVariable :
      ∀ position, position.1.val = X →
        (g.withCriticalMarkers count).NoVariableBefore
          pivotSchema
          ((g.withCriticalMarkers count).exposingWord
            hnormal position))
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground (g.withCriticalMarkers count).ranks)
    (hpivotInstance :
      (pivotSchema.instantiate arguments).UnfoldingEquivalent pivot)
    (hpivotSchemaSize : pivotSchema.nodes.length ≤ schemaBound)
    (hpivotSchemaOriginal :
      pivotSchema.WellFormed g.ranks arity)
    (hactivePrefixOriginal :
      (active.depthPrefix 1).head.toRegularTerm.WellFormed
        g.ranks
        ((active.depthPrefix 1).schemaArity
          (g.withCriticalMarkers count).ranks))
    (originalStem originalLabels : List (Label Action))
    (hstem : stem = originalStem.map liftCriticalLabel)
    (hlabels : labels = originalLabels.map liftCriticalLabel)
    (hroot : active.rootApplication? = some (X, children)) :
    Nonempty (MarkerStableBoundedWitnessedActiveSchemaCoverage
      g count initialLeft initialRight
      ((g.withCriticalMarkers count).fixedBalancingPresentationBound
        bound arity schemaBound)
      width arguments (stem ++ labels)) := by
  let extended := g.withCriticalMarkers count
  have hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  obtain ⟨activeResult⟩ :=
    segment.exists_activePrefixResidual hgExtended hactive hfiller
  have hpivotNoVariableActions :
      extended.NoVariableBefore pivotSchema activeResult.actions := by
    exact hpivotNoVariable activeResult.actions
      activeResult.labels_eq
  obtain ⟨pivotResult⟩ :=
    segment.exists_schemaPivotResidual_of_noVariableBefore
      hgExtended activeResult hpivotSupported hpivotWitness
      hpadding hpivotNoVariableActions
      hargumentsLength hargumentsClosed hpivotInstance
      (RegularTerm.referenceClosed_of_ground hpivot)
  obtain ⟨family⟩ :=
    segment.exists_schemaExposedSuccessorFamily_of_noVariableBefore
      hgExtended hnormal hexposureBound hactive hpivot houter
      hequivalent hpivotSupported hpivotWitness hpadding
      hexposingNoVariable hargumentsLength hargumentsClosed
      hpivotInstance hroot
  have hbound : 0 < bound :=
    (extended.exposureBound_pos hnormal).trans_le hexposureBound
  obtain ⟨result⟩ :=
    family.exists_structuredBoundedWitnessedBalancingResult
      hgExtended hbound hactive hpivot hfiller hroot houter
      hequivalent hpadding hargumentsGround activeResult pivotResult
      hpivotSchemaSize
  have hpaddingOriginal : g.ranks.foldr max 0 ≤ arity := by
    rw [← withCriticalMarkers_rankMax g count]
    exact hpadding
  have hactiveArityPadding :
      g.ranks.foldr max 0 ≤
        (active.depthPrefix 1).schemaArity extended.ranks := by
    unfold DepthPrefix.schemaArity
    rw [show extended.ranks.foldr max 0 =
        g.ranks.foldr max 0 by
      exact withCriticalMarkers_rankMax g count]
    exact Nat.le_max_right _ _
  have hactiveResidualOriginal :
      activeResult.residual.WellFormed g.ranks
        ((active.depthPrefix 1).schemaArity extended.ranks) :=
    runActions?_preserves_wellFormed_original hg
      hactivePrefixOriginal hactiveArityPadding
      activeResult.symbolic_run
  have hpivotResidualOriginal :
      pivotResult.residual.WellFormed g.ranks arity :=
    runActions?_preserves_wellFormed_original hg
      hpivotSchemaOriginal hpaddingOriginal
      pivotResult.symbolic_run
  let contexts := family.activeCompositionContexts
  have hcontextsOriginal :
      ∀ context ∈ contexts,
        context.WellFormed g.ranks arity := by
    intro context hcontext
    change context ∈ family.pivotResiduals ++
      List.replicate
        ((active.depthPrefix 1).schemaArity extended.ranks -
          children.length)
        (RegularTerm.variableTerm 0) at hcontext
    rw [List.mem_append] at hcontext
    rcases hcontext with hresidual | hpaddingContext
    · obtain ⟨i, hi, hget⟩ :=
        List.mem_iff_getElem.mp hresidual
      let index : Fin children.length := ⟨i, by
        simpa [family.pivotResiduals_length] using hi⟩
      have hresidualEq :
          context = (family.row index).pivotResidual := by
        exact hget.symm.trans
          (family.pivotResiduals_getElem index)
      rw [hresidualEq]
      exact runActions?_preserves_wellFormed_original hg
        hpivotSchemaOriginal hpaddingOriginal
        (family.row index).pivot_symbolic_run
    · have hcontextEq :
          context = RegularTerm.variableTerm 0 := by
        simpa using (List.eq_of_mem_replicate hpaddingContext)
      subst context
      have hpaddingCount :
          0 <
            (active.depthPrefix 1).schemaArity extended.ranks -
              children.length := by
        have hnonempty := List.ne_nil_of_mem hpaddingContext
        apply Nat.pos_of_ne_zero
        simpa using hnonempty
      have harityActive :=
        family.active_schemaArity_eq_rankMax hactive hroot
      have hpositive : 1 ≤ arity := by
        rw [harityActive, withCriticalMarkers_rankMax] at hpaddingCount
        omega
      exact RegularTerm.variableTerm_wellFormed hpositive
  have hcontextsLength :
      contexts.length =
        (active.depthPrefix 1).schemaArity extended.ranks :=
    family.activeCompositionContexts_length hactive hroot
  have houterOriginal :
      activeResult.residual.WellFormed g.ranks contexts.length := by
    rw [hcontextsLength]
    exact hactiveResidualOriginal
  have hcontextsLeArity : contexts.length ≤ arity := by
    rw [hcontextsLength,
      family.active_schemaArity_eq_rankMax hactive hroot,
      withCriticalMarkers_rankMax]
    exact hpaddingOriginal
  have hleftOriginal :
      (family.composedActiveSchema activeResult)
        |>.WellFormed g.ranks arity := by
    have hcomposed :=
      RegularTerm.instantiate_wellFormed_max
        houterOriginal hcontextsOriginal
    change (activeResult.residual.instantiate contexts)
      |>.WellFormed g.ranks arity
    simpa [Nat.max_eq_right hcontextsLeArity] using hcomposed
  have horiginalSchema :
      g.basisPairWellFormedCode
        result.coverage.witnessed.coverage.schema = true := by
    rw [result.schema_eq]
    unfold basisPairWellFormedCode
    rw [Bool.and_eq_true]
    exact ⟨hleftOriginal, hpivotResidualOriginal⟩
  have horiginalLabels : originalLabels ≠ [] := by
    intro hnil
    subst originalLabels
    apply segment.word_ne_nil hbound
    simpa using hlabels
  have horiginalWord : originalStem ++ originalLabels ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    have hlabelsLength : 0 < originalLabels.length :=
      List.length_pos_iff.mpr horiginalLabels
    simp only [List.length_append, List.length_nil] at hlength
    omega
  have hcoverageWord :
      stem ++ activeResult.actions.map Sum.inl =
        stem ++ labels :=
    congrArg (stem ++ ·) activeResult.labels_eq.symm
  have hword :
      stem ++ activeResult.actions.map Sum.inl =
        (originalStem ++ originalLabels).map liftCriticalLabel := by
    calc
      stem ++ activeResult.actions.map Sum.inl =
          stem ++ labels := hcoverageWord
      _ = originalStem.map liftCriticalLabel ++
          originalLabels.map liftCriticalLabel := by
            rw [hstem, hlabels]
      _ = (originalStem ++ originalLabels).map
          liftCriticalLabel := by simp
  let stable :=
    result.coverage.toMarkerStable horiginalSchema
      (originalStem ++ originalLabels) horiginalWord hword
  have htype :
      MarkerStableBoundedWitnessedActiveSchemaCoverage
          g count initialLeft initialRight
          (extended.fixedBalancingPresentationBound
            bound arity schemaBound)
          width arguments
          (stem ++ activeResult.actions.map Sum.inl) =
        MarkerStableBoundedWitnessedActiveSchemaCoverage
          g count initialLeft initialRight
          (extended.fixedBalancingPresentationBound
            bound arity schemaBound)
          width arguments (stem ++ labels) :=
    congrArg (fun word =>
      MarkerStableBoundedWitnessedActiveSchemaCoverage
        g count initialLeft initialRight
        (extended.fixedBalancingPresentationBound
          bound arity schemaBound)
        width arguments word) hcoverageWord
  exact ⟨htype.mp stable⟩

/-- A guarded critical-prefix presentation discharges both word-specific
no-variable premises required by the marker-stable balancing constructor.
The balancing word is short because its length is exactly `bound`; canonical
successor-exposing words are shorter than `bound`.  In both cases the
continuation consists only of injected original actions. -/
public theorem
    BalancingSegment.exists_markerStableSchemaBoundedWitnessedBalancingResult_of_criticalGuardedFixedTail
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {bound : ℕ}
    (hexposureBound :
      (g.withCriticalMarkers count).exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm}
    {segmentLabels : List (Label (Action ⊕ ℕ))}
    {labels : ℕ → List (Label (Action ⊕ ℕ))}
    {pivots : ℕ → RegularTerm} {j : ℕ}
    (segment : BalancingSegment (g.withCriticalMarkers count)
      bound active pivot segmentLabels)
    (hactive : active.Ground (g.withCriticalMarkers count).ranks)
    (hpivot : pivot.Ground
      (g.withCriticalMarkers count).ranks)
    {base filler : RegularTerm}
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (hdepth : bound ≤ presentation.depth)
    (hpivotInstance :
      ((presentation.schema j).instantiate
          presentation.arguments).UnfoldingEquivalent pivot)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label (Action ⊕ ℕ))}
    (houter : CertificateDerivable (g.withCriticalMarkers count)
      initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent :
      (g.withCriticalMarkers count).TraceEquivalent
        active pivot)
    {schemaBound : ℕ}
    (hpivotSchemaSize :
      (presentation.schema j).nodes.length ≤ schemaBound)
    (hactivePrefixOriginal :
      (active.depthPrefix 1).head.toRegularTerm.WellFormed
        g.ranks
        ((active.depthPrefix 1).schemaArity
          (g.withCriticalMarkers count).ranks))
    (originalStem originalSegment : List (Label Action))
    (hstem : stem = originalStem.map liftCriticalLabel)
    (hsegment :
      segmentLabels = originalSegment.map liftCriticalLabel)
    {X : ℕ} {children : List ℕ}
    (hroot : active.rootApplication? = some (X, children)) :
    Nonempty (MarkerStableBoundedWitnessedActiveSchemaCoverage
      g count initialLeft initialRight
      ((g.withCriticalMarkers count).fixedBalancingPresentationBound
        bound presentation.arity schemaBound)
      presentation.width presentation.arguments
      (stem ++ segmentLabels)) := by
  let extended := g.withCriticalMarkers count
  have hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have hpivotNoVariable :
      ∀ actions : List (Action ⊕ ℕ),
        segmentLabels = actions.map Sum.inl →
          extended.NoVariableBefore
            (presentation.schema j) actions := by
    intro actions hlabelsActions
    have hwordOriginal :
        actions.map Sum.inl =
          originalSegment.map liftCriticalLabel := by
      calc
        actions.map Sum.inl = segmentLabels := hlabelsActions.symm
        _ = originalSegment.map liftCriticalLabel := hsegment
    obtain ⟨originalActions, hactions, _horiginalLabels⟩ :=
      exists_originalActions_of_map_inl_eq_map_liftCriticalLabel
        hwordOriginal
    have hlengthEq : actions.length = bound := by
      simpa [hlabelsActions] using segment.word_length
    have hlength : actions.length ≤ presentation.depth := by
      rw [hlengthEq]
      exact hdepth
    have hpivotRun :
        extended.runActions? actions pivot =
          some segment.pivotTarget := by
      simpa [runActions?, hlabelsActions] using
        segment.pivot_run
    exact g.criticalNoVariableBefore_of_guardedApplicationDepth
      hg presentation.base_ground presentation.filler_ground
      (presentation.schema_supported j).1
      (presentation.schema_guarded j) hlength
      originalActions hactions
      hpivotInstance
      (RegularTerm.referenceClosed_of_ground hpivot)
      hpivotRun
  have hexposingNoVariable :
      ∀ position, position.1.val = X →
        extended.NoVariableBefore
          (presentation.schema j)
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
        active.rootApplication? =
          some (position.1.val, children) := by
      simpa [hposition] using hroot
    have hrank :=
      hactive.root_rank_arity hrootPosition
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
        hgExtended hactive position
        (extended.exposingWord_exposes hnormal position)
        hshort hrootPosition hchild
    exact g.criticalNoVariableBefore_of_guardedApplicationDepth
      hg presentation.base_ground presentation.filler_ground
      (presentation.schema_supported j).1
      (presentation.schema_guarded j) hlength
      originalActions (by simpa [word] using hwordOriginal)
      hpivotInstance
      (RegularTerm.referenceClosed_of_ground hpivot)
      (by simpa [word] using hpivotRun)
  apply
    segment
      |>.exists_markerStableSchemaBoundedWitnessedBalancingResult_of_noVariableBefore
        hg hnormal hexposureBound hactive hpivot
        presentation.filler_ground houter hequivalent
        (presentation.schema_supported j)
        (presentation.schema_hasPrefixWitness j)
        presentation.rankMax_le_arity
        hpivotNoVariable hexposingNoVariable
        presentation.arguments_length
        presentation.arguments_ground
        hpivotInstance
        hpivotSchemaSize
        (presentation.schema_wellFormed_original j)
        hactivePrefixOriginal
        originalStem originalSegment hstem hsegment
        hroot

end EncodedFirstOrderGrammar

end DCFEquivalence
