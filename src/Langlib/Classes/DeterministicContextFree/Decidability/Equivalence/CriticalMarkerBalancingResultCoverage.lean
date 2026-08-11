module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerFixedTailWidening
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaBalancingBoundedCoverage

@[expose]
public section

/-!
# Marker-stable bounded balancing results

The ordinary bounded balancing constructor executes in one grammar and hence
forgets that, before a critical marker is exposed, its symbolic schemas still
belong to the original grammar.  The structured result retained by
`SchemaBalancingBoundedCoverage` exposes its exact schema pair.  This file
uses critical-marker conservativity to prove both component schemas
well-formed over the original rank table and packages the row in the
marker-stable interface.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private theorem exists_originalActions_of_map_inl_eq_map_liftCriticalLabel
    {extendedActions : List (Action ⊕ ℕ)}
    {originalWord : List (Label Action)}
    (hword :
      extendedActions.map Sum.inl =
        originalWord.map liftCriticalLabel) :
    ∃ originalActions : List Action,
      extendedActions = originalActions.map Sum.inl ∧
        originalWord = originalActions.map Sum.inl := by
  induction extendedActions generalizing originalWord with
  | nil =>
      simp only [List.map_nil] at hword
      have horiginal : originalWord = [] :=
        List.map_eq_nil_iff.mp hword.symm
      subst originalWord
      exact ⟨[], rfl, rfl⟩
  | cons extendedAction extendedActions ih =>
      cases originalWord with
      | nil => simp at hword
      | cons originalLabel originalWord =>
          simp only [List.map_cons, List.cons.injEq] at hword
          rcases hword with ⟨hhead, htail⟩
          cases extendedAction with
          | inl action =>
              cases originalLabel with
              | inl originalAction =>
                  simp only [liftCriticalLabel,
                    Sum.inl.injEq] at hhead
                  subst originalAction
                  obtain ⟨actions, hextended, horiginal⟩ :=
                    ih htail
                  exact ⟨action :: actions, by
                    simp [hextended], by simp [horiginal]⟩
              | inr x =>
                  simp [liftCriticalLabel] at hhead
          | inr marker =>
              cases originalLabel <;>
                simp [liftCriticalLabel] at hhead

/-- A successful ordinary-action run of an original schema in a critical
extension is the lift of an original ordinary-action run. -/
private theorem exists_original_runActions_of_extended_runActions
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity : ℕ} {source target : RegularTerm}
    {extendedActions : List (Action ⊕ ℕ)}
    (hsource : source.WellFormed g.ranks arity)
    (hrun :
      (g.withCriticalMarkers count).runActions?
        extendedActions source = some target) :
    ∃ originalActions : List Action,
      extendedActions = originalActions.map Sum.inl ∧
        g.runActions? originalActions source = some target := by
  have hrun' :
      (g.withCriticalMarkers count).run?
        (extendedActions.map Sum.inl) source = some target := by
    simpa [runActions?] using hrun
  obtain ⟨originalWord, hword, horiginalRun⟩ :=
    (withCriticalMarkers_run?_some_iff_original
      g hg count
      (RegularTerm.usesOriginalSymbols_of_wellFormed hsource)).mp
      hrun'
  obtain ⟨originalActions, hextended, horiginalWord⟩ :=
    exists_originalActions_of_map_inl_eq_map_liftCriticalLabel
      hword
  refine ⟨originalActions, hextended, ?_⟩
  rw [horiginalWord] at horiginalRun
  simpa [runActions?] using horiginalRun

/-- Original ranked well-formedness is preserved by any successful symbolic
ordinary-action run in a critical-marker extension. -/
private theorem residual_wellFormed_original
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity : ℕ} {source residual : RegularTerm}
    {extendedActions : List (Action ⊕ ℕ)}
    (hsource : source.WellFormed g.ranks arity)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hrun :
      (g.withCriticalMarkers count).runActions?
        extendedActions source = some residual) :
    residual.WellFormed g.ranks arity := by
  obtain ⟨originalActions, _hextended, horiginalRun⟩ :=
    exists_original_runActions_of_extended_runActions
      hg hsource hrun
  exact g.runActions?_preserves_wellFormed_padded
    hg hpadding originalActions hsource horiginalRun

/-- Marker-stable form of the bounded fixed-argument balancing constructor.
The two additional schema premises are precisely the original-rank facts
discarded by the ordinary critical-extension interface. -/
public theorem
    BalancingSegment.exists_markerStableSchemaBoundedWitnessedBalancingResult
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
    (hpivotDepth : pivotSchema.ApplicationDepth bound)
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
    {X : ℕ} {children : List ℕ}
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
  have hpivotDepthActions :
      pivotSchema.ApplicationDepth activeResult.actions.length := by
    simpa [activeResult.actions_length] using hpivotDepth
  obtain ⟨pivotResult⟩ :=
    segment.exists_schemaPivotResidual hgExtended activeResult
      hpivotSupported hpivotWitness hpadding hpivotDepthActions
      hargumentsLength hargumentsClosed hpivotInstance
      (RegularTerm.referenceClosed_of_ground hpivot)
  obtain ⟨family⟩ :=
    segment.exists_schemaExposedSuccessorFamily hgExtended hnormal
      hexposureBound hactive hpivot houter hequivalent
      hpivotSupported hpivotWitness hpadding hpivotDepth
      hargumentsLength hargumentsClosed hpivotInstance hroot
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
    residual_wellFormed_original hg hactivePrefixOriginal
      hactiveArityPadding activeResult.symbolic_run
  have hpivotResidualOriginal :
      pivotResult.residual.WellFormed g.ranks arity :=
    residual_wellFormed_original hg hpivotSchemaOriginal
      hpaddingOriginal pivotResult.symbolic_run
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
      exact residual_wellFormed_original hg hpivotSchemaOriginal
        hpaddingOriginal (family.row index).pivot_symbolic_run
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

end EncodedFirstOrderGrammar

end DCFEquivalence
