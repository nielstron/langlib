module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaBalancingSchemaComposition

@[expose]
public section

/-!
# Fixed-argument certificate coverage from one balancing segment

This is the pivot-path form of Proposition 45.  The pivot is presented by a
schema over one pre-existing ground argument tuple, and both output schemas
retain exactly that tuple and its active prefix width.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace BalancingSegment.SchemaExposedSuccessorFamily

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {initialLeft initialRight : RegularTerm}
  {stem : List (Label Action)} {filler : RegularTerm}
  {children : List ℕ} {pivotSchema : RegularTerm}
  {arguments : List RegularTerm} {arity width : ℕ}

/-- Assemble a complete witnessed balancing row while retaining the supplied
argument tuple verbatim. -/
public theorem exists_witnessedBalancingResult
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (hg : g.WellFormed)
    (hbound : 0 < bound)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (activeResult : segment.ActivePrefixResidual filler)
    (pivotResult : segment.SchemaPivotResidual activeResult
      pivotSchema arguments arity width) :
    Nonempty (WitnessedActiveSchemaCoverage g initialLeft initialRight
      width (stem ++ activeResult.actions.map Sum.inl)) := by
  classical
  let activeArguments :=
    (active.depthPrefix 1).paddedArguments g.ranks filler
  let contexts := family.activeCompositionContexts
  let leftSchema := family.composedActiveSchema activeResult
  let rightSchema := pivotResult.residual
  have hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hactiveRun :
      g.runActions? activeResult.actions active =
        some segment.active_target := by
    simpa [runActions?, activeResult.labels_eq] using segment.active_run
  have hpivotRun :
      g.runActions? activeResult.actions pivot =
        some segment.pivotTarget := by
    simpa [runActions?, activeResult.labels_eq] using segment.pivot_run
  have hsegmentDerivation :
      CertificateDerivable g initialLeft initialRight []
        (.pair (stem ++ activeResult.actions.map Sum.inl)
          segment.active_target segment.pivotTarget) :=
    houter.follow_runActions hgroundSteps hequivalent
      hactiveRun hpivotRun
  have hactiveArgumentsGround :
      ∀ argument ∈ activeArguments, argument.Ground g.ranks := by
    exact RegularTerm.depthPrefix_paddedArguments_ground
      hactive hfiller 1
  have hreplacementsGround :
      ∀ replacement ∈ family.pivotTargets,
        replacement.Ground g.ranks :=
    family.pivotTargets_ground hg hpivot
  have hreplacementLength :
      family.pivotTargets.length ≤ activeArguments.length := by
    rw [family.pivotTargets_length]
    have htails :=
      RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
    have hchildrenArity :
        children.length ≤
          (active.depthPrefix 1).schemaArity g.ranks := by
      simp [DepthPrefix.schemaArity, htails]
    simpa [activeArguments] using hchildrenArity
  let childIndex : Fin family.pivotTargets.length → Fin children.length :=
    fun i => ⟨i.val, by simpa using i.isLt⟩
  let shorterWord : Fin family.pivotTargets.length →
      List (Label Action) :=
    fun i => stem ++ (family.row (childIndex i)).word.map Sum.inl
  let shorterLeft : Fin family.pivotTargets.length → RegularTerm :=
    fun i => (family.row (childIndex i)).activeTarget
  let shorterRight : Fin family.pivotTargets.length → RegularTerm :=
    fun i => (family.row (childIndex i)).pivotTarget
  have hactiveSchemaWellFormed :
      activeResult.residual.WellFormed g.ranks activeArguments.length := by
    simpa [activeArguments] using activeResult.supported.1
  obtain ⟨result, hresultDerivation, hresultMatch⟩ :=
    hsegmentDerivation.replaceArgumentPrefixFin
      hactiveSchemaWellFormed hactiveArgumentsGround
      hreplacementsGround hreplacementLength
      activeResult.instance_matches.symm
      shorterWord shorterLeft shorterRight
      (fun i => (family.row (childIndex i)).shorter_derivation)
      (fun i => by
        simp only [shorterWord, List.length_append, List.length_map]
        have hshort := (family.row (childIndex i)).word_length_lt
        have houterLength := activeResult.actions_length
        omega)
      (fun i => by
        let index := childIndex i
        have hiChildren : i.val < children.length := index.isLt
        have htails :=
          RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
        have hiArguments : i.val < activeArguments.length :=
          i.isLt.trans_le hreplacementLength
        have hargumentGet :
            activeArguments[i.val]? =
              some (active.withRoot children[i.val]) := by
          unfold activeArguments DepthPrefix.paddedArguments
          rw [List.getElem?_append_left (by
            simpa [htails] using hiChildren)]
          simp [htails, List.getElem?_eq_getElem hiChildren]
        have hargumentEq :
            activeArguments[i.val] =
              active.withRoot children[i.val] := by
          exact Option.some.inj
            ((List.getElem?_eq_getElem hiArguments).symm.trans
              hargumentGet)
        rw [hargumentEq]
        simpa [index, childIndex] using
          (family.row index).active_matches)
      (fun i => by
        let index := childIndex i
        have htarget :
            family.pivotTargets[i.val] =
              (family.row index).pivotTarget :=
          family.pivotTargets_getElem index
        rw [htarget])
  have hresultConcrete :
      result.UnfoldingEquivalent
        (activeResult.residual.instantiate
          (family.pivotTargets ++
            List.replicate
              ((active.depthPrefix 1).schemaArity g.ranks -
                children.length) filler)) := by
    simpa [activeArguments,
      family.replaceArgumentPrefix_activeArguments hroot] using
        hresultMatch
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hcontextsWellFormed :
      ∀ context ∈ contexts,
        context.WellFormed g.ranks arity := by
    exact family.activeCompositionContexts_wellFormed
      hactive hroot hpadding
  have hcontextsClosed :
      ∀ context ∈ contexts, context.ReferenceClosed := by
    intro context hcontext
    exact RegularTerm.referenceClosed_of_wellFormed
      (hcontextsWellFormed context hcontext)
  have hcontextsLength :
      contexts.length =
        (active.depthPrefix 1).schemaArity g.ranks :=
    family.activeCompositionContexts_length hactive hroot
  have houterWellFormed :
      activeResult.residual.WellFormed g.ranks contexts.length := by
    rw [hcontextsLength]
    exact activeResult.supported.1
  have hcomposition :=
    RegularTerm.instantiate_comp_unfoldingEquivalent
      (outer := activeResult.residual)
      (contexts := contexts) (arguments := arguments)
      houterWellFormed hcontextsClosed hargumentsClosed
  have hconcreteArgumentsClosed :
      ∀ argument ∈
          family.pivotTargets ++
            List.replicate
              ((active.depthPrefix 1).schemaArity g.ranks -
                children.length) filler,
        argument.ReferenceClosed := by
    intro argument hargument
    simp only [List.mem_append, List.mem_replicate] at hargument
    rcases hargument with htarget | ⟨_hcount, rfl⟩
    · exact RegularTerm.referenceClosed_of_ground
        (hreplacementsGround argument htarget)
    · exact RegularTerm.referenceClosed_of_ground hfiller
  have hcomposedClosed :
      ∀ argument ∈ RegularTerm.composedContexts contexts arguments,
        argument.ReferenceClosed := by
    intro argument hargument
    obtain ⟨context, hcontext, rfl⟩ :=
      List.mem_map.mp hargument
    exact RegularTerm.instantiate_referenceClosed
      (hcontextsClosed context hcontext) hargumentsClosed
  have hcomposedLength :
      (RegularTerm.composedContexts contexts arguments).length =
        (active.depthPrefix 1).schemaArity g.ranks := by
    simp [RegularTerm.composedContexts, hcontextsLength]
  have hconcreteLength :
      (family.pivotTargets ++
          List.replicate
            ((active.depthPrefix 1).schemaArity g.ranks -
              children.length) filler).length =
        (active.depthPrefix 1).schemaArity g.ranks := by
    have hchildrenArity :
        children.length ≤
          (active.depthPrefix 1).schemaArity g.ranks := by
      have htails :=
        RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
      simp [DepthPrefix.schemaArity, htails]
    simp [family.pivotTargets_length]
    omega
  have hprefixSemantic :
      (activeResult.residual.instantiate
          (RegularTerm.composedContexts contexts arguments))
        |>.UnfoldingEquivalent
          (activeResult.residual.instantiate
            (family.pivotTargets ++
              List.replicate
                ((active.depthPrefix 1).schemaArity g.ranks -
                  children.length) filler)) := by
    have htails :=
      RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
    apply activeResult.supported.2.2
    · exact hcomposedLength
    · exact hconcreteLength
    · exact hcomposedClosed
    · exact hconcreteArgumentsClosed
    · simpa [contexts, htails] using
        (family.composedActiveContexts_equivalentThrough
          (filler := filler))
  have hleftInstanceConcrete :
      (leftSchema.instantiate arguments).UnfoldingEquivalent
        (activeResult.residual.instantiate
          (family.pivotTargets ++
            List.replicate
              ((active.depthPrefix 1).schemaArity g.ranks -
                children.length) filler)) := by
    simpa [leftSchema,
      BalancingSegment.SchemaExposedSuccessorFamily.composedActiveSchema,
      contexts] using hcomposition.trans hprefixSemantic
  have hleftMatch :
      result.UnfoldingEquivalent
        (leftSchema.instantiate arguments) :=
    hresultConcrete.trans hleftInstanceConcrete.symm
  have hrightMatch :
      segment.pivotTarget.UnfoldingEquivalent
        (rightSchema.instantiate arguments) := by
    simpa [rightSchema] using pivotResult.instance_matches.symm
  have hwidthArity : width ≤ arity := pivotResult.supported.2.1
  have hleftSupported :=
    family.composedActiveSchema_supported
      hg hactive hroot hpadding hwidthArity activeResult
  have hleftWitness :=
    family.composedActiveSchema_hasPrefixWitness
      hg hactive hroot hpadding activeResult
  have hargumentsGroundCode :
      g.groundArgumentsCode arguments = true := by
    unfold groundArgumentsCode
    apply List.all_eq_true.mpr
    intro argument hargument
    exact (RegularTerm.groundCode_eq_true_iff g.ranks argument).mpr
      (hargumentsGround argument hargument)
  have hwordNonempty :
      stem ++ activeResult.actions.map Sum.inl ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp only [List.length_append, List.length_map,
      List.length_nil] at hlength
    have hactionsPositive : 0 < activeResult.actions.length := by
      rw [activeResult.actions_length]
      exact hbound
    omega
  let schema : BasisPair := (arity, leftSchema, rightSchema)
  let coverage : ActiveSchemaCoverage g initialLeft initialRight
      width (stem ++ activeResult.actions.map Sum.inl) :=
    { left := result
      right := segment.pivotTarget
      derivation := hresultDerivation
      schema := schema
      arguments := arguments
      word_nonempty := hwordNonempty
      schema_wellFormed := by
        unfold schema basisPairWellFormedCode
        rw [Bool.and_eq_true]
        exact ⟨hleftSupported.1, pivotResult.supported.1⟩
      rank_padding := by
        simpa [schema, BasisPair.arity] using hpadding
      left_supported := by
        simpa [schema, BasisPair.arity, BasisPair.left,
          leftSchema] using hleftSupported
      right_supported := by
        simpa [schema, BasisPair.arity, BasisPair.right,
          rightSchema] using pivotResult.supported
      argument_count := by
        simpa [schema, BasisPair.arity] using pivotResult.argument_count
      arguments_ground := hargumentsGroundCode
      left_matches :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by simpa [schema, BasisPair.left] using hleftMatch)
      right_matches :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by simpa [schema, BasisPair.right] using hrightMatch) }
  exact ⟨
    { coverage := coverage
      left_witness := by
        simpa [coverage, schema, BasisPair.left, leftSchema] using
          hleftWitness
      right_witness := by
        simpa [coverage, schema, BasisPair.right, rightSchema] using
          pivotResult.hasPrefixWitness }⟩

end BalancingSegment.SchemaExposedSuccessorFamily

/-- Full fixed-argument Proposition-45 assembly for one normal-form balancing
segment. -/
public theorem BalancingSegment.exists_schemaWitnessedBalancingResult
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hexposureBound : g.exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    {filler : RegularTerm} (hfiller : filler.Ground g.ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    {pivotSchema : RegularTerm} {arguments : List RegularTerm}
    {arity width : ℕ}
    (hpivotSupported : RegularTerm.SupportedByPrefix g.ranks
      arity width pivotSchema)
    (hpivotWitness : pivotSchema.HasPrefixWitness width)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hpivotDepth : pivotSchema.ApplicationDepth bound)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (hpivotInstance :
      (pivotSchema.instantiate arguments).UnfoldingEquivalent pivot)
    {X : ℕ} {children : List ℕ}
    (hroot : active.rootApplication? = some (X, children)) :
    Nonempty (WitnessedActiveSchemaCoverage g initialLeft initialRight
      width (stem ++ labels)) := by
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  obtain ⟨activeResult⟩ :=
    segment.exists_activePrefixResidual hg hactive hfiller
  have hpivotDepthActions :
      pivotSchema.ApplicationDepth activeResult.actions.length := by
    simpa [activeResult.actions_length] using hpivotDepth
  obtain ⟨pivotResult⟩ :=
    segment.exists_schemaPivotResidual hg activeResult
      hpivotSupported hpivotWitness hpadding hpivotDepthActions
      hargumentsLength hargumentsClosed hpivotInstance
      (RegularTerm.referenceClosed_of_ground hpivot)
  obtain ⟨family⟩ :=
    segment.exists_schemaExposedSuccessorFamily hg hnormal
      hexposureBound hactive hpivot houter hequivalent
      hpivotSupported hpivotWitness hpadding hpivotDepth
      hargumentsLength hargumentsClosed hpivotInstance hroot
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
  obtain ⟨coverage⟩ :=
    family.exists_witnessedBalancingResult hg hbound
      hactive hpivot hfiller hroot houter hequivalent
      hpadding hargumentsGround activeResult pivotResult
  exact ⟨by
    simpa only [← activeResult.labels_eq] using coverage⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
