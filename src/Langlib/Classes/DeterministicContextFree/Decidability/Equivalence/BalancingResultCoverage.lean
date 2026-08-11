module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingSchemaComposition

@[expose]
public section

/-!
# Certificate coverage produced by one balancing segment

This is the certificate-calculus form of Jančar's Proposition 45.  Starting
from a derived balancing pair, the segment is executed, every active immediate
successor is replaced using its strictly shorter exposing row, and the result
is presented by two regular schemas over the pivot depth-prefix tails.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A witnessed balancing coverage which records that Proposition 45 leaves
the pivot-side concrete residual unchanged. -/
public structure BalancingSegment.WitnessedBalancingResult
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (initialLeft initialRight : RegularTerm)
    (word : List (Label Action)) where
  witnessed :
    WitnessedActiveSchemaCoverage g initialLeft initialRight
      (pivot.depthPrefix bound).tails.length word
  pivot_eq : witnessed.coverage.right = segment.pivotTarget

namespace BalancingSegment.ExposedSuccessorFamily

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {initialLeft initialRight : RegularTerm}
  {stem : List (Label Action)} {filler : RegularTerm}
  {children : List ℕ}

/-- Assemble one complete, structurally witnessed balancing-result row from
the already selected active residual, pivot residual, and successor family. -/
public theorem exists_witnessedBalancingResult
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed)
    (hbound : 0 < bound)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    (activeResult : segment.ActivePrefixResidual filler)
    (pivotResult : segment.PivotPrefixResidual filler activeResult) :
    Nonempty (segment.WitnessedBalancingResult
      initialLeft initialRight
      (stem ++ activeResult.actions.map Sum.inl)) := by
  classical
  let activeArguments :=
    (active.depthPrefix 1).paddedArguments g.ranks filler
  let pivotArguments :=
    (pivot.depthPrefix bound).paddedArguments g.ranks filler
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
      (fun i => by
        exact (family.row (childIndex i)).shorter_derivation)
      (fun i => by
        simp only [shorterWord, List.length_append, List.length_map]
        have hshort :=
          (family.row (childIndex i)).word_length_lt
        have houterLength := activeResult.actions_length
        omega)
      (fun i => by
        let index := childIndex i
        have hiChildren : i.val < children.length := index.isLt
        have htails :=
          RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
        have hiArguments : i.val < activeArguments.length := by
          exact i.isLt.trans_le hreplacementLength
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
              (family.row index).pivotTarget := by
          exact family.pivotTargets_getElem index
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
  have hpivotArgumentsGround :
      ∀ argument ∈ pivotArguments, argument.Ground g.ranks := by
    exact RegularTerm.depthPrefix_paddedArguments_ground
      hpivot hfiller bound
  have hpivotArgumentsClosed :
      ∀ argument ∈ pivotArguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hpivotArgumentsGround argument hargument)
  have hcontextsWellFormed :
      ∀ context ∈ contexts,
        context.WellFormed g.ranks
          ((pivot.depthPrefix bound).schemaArity g.ranks) := by
    exact family.activeCompositionContexts_wellFormed
      hactive hroot
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
      (contexts := contexts) (arguments := pivotArguments)
      houterWellFormed hcontextsClosed hpivotArgumentsClosed
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
      ∀ argument ∈ RegularTerm.composedContexts contexts pivotArguments,
        argument.ReferenceClosed := by
    intro argument hargument
    obtain ⟨context, hcontext, rfl⟩ :=
      List.mem_map.mp hargument
    exact RegularTerm.instantiate_referenceClosed
      (hcontextsClosed context hcontext) hpivotArgumentsClosed
  have hcomposedLength :
      (RegularTerm.composedContexts contexts pivotArguments).length =
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
          (RegularTerm.composedContexts contexts pivotArguments))
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
    · simpa [contexts, pivotArguments, htails] using
        family.composedActiveContexts_equivalentThrough
  have hleftInstanceConcrete :
      (leftSchema.instantiate pivotArguments).UnfoldingEquivalent
        (activeResult.residual.instantiate
          (family.pivotTargets ++
            List.replicate
              ((active.depthPrefix 1).schemaArity g.ranks -
                children.length) filler)) := by
    simpa [leftSchema, BalancingSegment.ExposedSuccessorFamily.composedActiveSchema,
      contexts] using hcomposition.trans hprefixSemantic
  have hleftMatch :
      result.UnfoldingEquivalent
        (leftSchema.instantiate pivotArguments) :=
    hresultConcrete.trans hleftInstanceConcrete.symm
  have hrightMatch :
      segment.pivotTarget.UnfoldingEquivalent
        (rightSchema.instantiate pivotArguments) := by
    simpa [rightSchema, pivotArguments] using pivotResult.instance_matches.symm
  have hleftSupported :=
    family.composedActiveSchema_supported
      hg hactive hpivot hroot activeResult
  have hleftWitness :=
    family.composedActiveSchema_hasPrefixWitness
      hg hactive hpivot hroot activeResult
  have hrightWitness :=
    family.pivotResidual_hasPrefixWitness
      hg hpivot activeResult pivotResult
  have hargumentsGroundCode :
      g.groundArgumentsCode pivotArguments = true := by
    unfold groundArgumentsCode
    apply List.all_eq_true.mpr
    intro argument hargument
    exact (RegularTerm.groundCode_eq_true_iff g.ranks argument).mpr
      (hpivotArgumentsGround argument hargument)
  have hwordNonempty :
      stem ++ activeResult.actions.map Sum.inl ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp only [List.length_append, List.length_map, List.length_nil] at hlength
    have hactionsPositive : 0 < activeResult.actions.length := by
      rw [activeResult.actions_length]
      exact hbound
    omega
  let schema : BasisPair :=
    ((pivot.depthPrefix bound).schemaArity g.ranks,
      leftSchema, rightSchema)
  let coverage : ActiveSchemaCoverage g initialLeft initialRight
      (pivot.depthPrefix bound).tails.length
      (stem ++ activeResult.actions.map Sum.inl) :=
    { left := result
      right := segment.pivotTarget
      derivation := hresultDerivation
      schema := schema
      arguments := pivotArguments
      word_nonempty := hwordNonempty
      schema_wellFormed := by
        unfold schema basisPairWellFormedCode
        rw [Bool.and_eq_true]
        exact ⟨hleftSupported.1, pivotResult.supported.1⟩
      rank_padding := by
        unfold schema BasisPair.arity
        exact Nat.le_max_right _ _
      left_supported := by
        simpa [schema, BasisPair.arity, BasisPair.left,
          leftSchema] using hleftSupported
      right_supported := by
        simpa [schema, BasisPair.arity, BasisPair.right,
          rightSchema] using pivotResult.supported
      argument_count := by
        simpa [schema, BasisPair.arity, pivotArguments]
      arguments_ground := hargumentsGroundCode
      left_matches :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by
            simpa [schema, BasisPair.left] using hleftMatch)
      right_matches :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by
            simpa [schema, BasisPair.right] using hrightMatch) }
  let witnessed :
      WitnessedActiveSchemaCoverage g initialLeft initialRight
        (pivot.depthPrefix bound).tails.length
        (stem ++ activeResult.actions.map Sum.inl) :=
    { coverage := coverage
      left_witness := by
        simpa [coverage, schema, BasisPair.left, leftSchema] using
          hleftWitness
      right_witness := by
        simpa [coverage, schema, BasisPair.right, rightSchema] using
          hrightWitness }
  exact ⟨
    { witnessed := witnessed
      pivot_eq := by rfl }⟩

end BalancingSegment.ExposedSuccessorFamily

/-- Refined full Proposition-45 assembly retaining the exact pivot-side
concrete residual. -/
public theorem BalancingSegment.exists_concreteWitnessedBalancingResult
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
    {X : ℕ} {children : List ℕ}
    (hroot : active.rootApplication? = some (X, children)) :
    Nonempty (segment.WitnessedBalancingResult
      initialLeft initialRight (stem ++ labels)) := by
  obtain ⟨activeResult⟩ :=
    segment.exists_activePrefixResidual hg hactive hfiller
  obtain ⟨pivotResult⟩ :=
    segment.exists_pivotPrefixResidual hg hpivot hfiller activeResult
  obtain ⟨family⟩ :=
    segment.exists_exposedSuccessorFamily hg hnormal hexposureBound
      hactive hpivot hfiller houter hequivalent hroot
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
  obtain ⟨result⟩ :=
    family.exists_witnessedBalancingResult hg hbound
      hactive hpivot hfiller hroot houter hequivalent
      activeResult pivotResult
  exact ⟨by
    simpa only [← activeResult.labels_eq] using result⟩

/-- Full Proposition-45 assembly for one normal-form balancing segment. -/
public theorem BalancingSegment.exists_witnessedBalancingResult
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
    {X : ℕ} {children : List ℕ}
    (hroot : active.rootApplication? = some (X, children)) :
    Nonempty (WitnessedActiveSchemaCoverage g initialLeft initialRight
      (pivot.depthPrefix bound).tails.length (stem ++ labels)) := by
  obtain ⟨result⟩ :=
    segment.exists_concreteWitnessedBalancingResult
      hg hnormal hexposureBound hactive hpivot hfiller
      houter hequivalent hroot
  exact ⟨result.witnessed⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
