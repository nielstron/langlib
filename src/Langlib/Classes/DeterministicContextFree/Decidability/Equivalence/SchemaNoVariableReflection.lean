module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedDepth
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaBalancingSuccessorFamily

@[expose]
public section

/-!
# Fixed-argument balancing from word-specific reflection

The ordinary fixed-tail interface assumes a blanket `ApplicationDepth`
bound.  Marker-aware prefixes deliberately allow shallow variables denoting
fresh marker arguments, so that blanket statement is false.  Reflection only
needs the exact operational premise that the particular word being executed
does not reach a variable before its end.

This module restates the pivot and exposed-successor constructors with that
minimal premise.  The resulting structures are unchanged, so all later
balancing composition and size bounds remain reusable.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A concrete run from a fixed schema instance reflects to a supported
symbolic residual whenever the specific word reaches no variable early. -/
public theorem exists_supportedSchemaResidual_of_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema concrete target : RegularTerm}
    {arguments : List RegularTerm} {arity width : ℕ}
    {word : List Action}
    (hsupported : RegularTerm.SupportedByPrefix g.ranks
      arity width schema)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hnoVariable : g.NoVariableBefore schema word)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hinstance : (schema.instantiate arguments).UnfoldingEquivalent
      concrete)
    (hconcreteClosed : concrete.ReferenceClosed)
    (hrun : g.runActions? word concrete = some target) :
    ∃ residual,
      g.runActions? word schema = some residual ∧
      (residual.instantiate arguments).UnfoldingEquivalent target ∧
      arguments.length = arity ∧
      RegularTerm.SupportedByPrefix g.ranks arity width residual ∧
      residual.nodes.length ≤
        g.residualNodeBound word.length schema.nodes.length := by
  have hschemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hsupported.1
  have hinstanceClosed := RegularTerm.instantiate_referenceClosed
    hschemaClosed hargumentsClosed
  obtain ⟨instanceTarget, hinstanceRun, htargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hg hinstance
      hinstanceClosed hconcreteClosed hrun
  obtain ⟨residual, hsymbolic, hresidualInstance⟩ :=
    g.runActions?_reflects_instantiation_of_noVariableBefore
      hg word ⟨arity, hsupported.1⟩ hargumentsClosed
      hinstanceRun hnoVariable
  have hresidualSupported :=
    hsupported.residual hg hpadding hsymbolic
  have hsize : residual.nodes.length ≤
      g.residualNodeBound word.length schema.nodes.length :=
    g.runActions?_nodes_length_le hg
      ⟨arity, hsupported.1⟩ (le_refl _) hsymbolic
  exact ⟨residual, hsymbolic,
    hresidualInstance.trans htargetEquivalent,
    hargumentsLength, hresidualSupported, hsize⟩

/-- Word-specific reflection form of the fixed-argument pivot residual. -/
public theorem BalancingSegment.exists_schemaPivotResidual_of_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {active pivot : RegularTerm}
    {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {filler : RegularTerm}
    (activeResult : segment.ActivePrefixResidual filler)
    {pivotSchema : RegularTerm} {arguments : List RegularTerm}
    {arity width : ℕ}
    (hsupported : RegularTerm.SupportedByPrefix g.ranks
      arity width pivotSchema)
    (hpivotWitness : pivotSchema.HasPrefixWitness width)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hnoVariable :
      g.NoVariableBefore pivotSchema activeResult.actions)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hinstance : (pivotSchema.instantiate arguments).UnfoldingEquivalent
      pivot)
    (hpivotClosed : pivot.ReferenceClosed) :
    Nonempty (segment.SchemaPivotResidual activeResult
      pivotSchema arguments arity width) := by
  have hpivotRun :
      g.runActions? activeResult.actions pivot =
        some segment.pivotTarget := by
    simpa [runActions?, activeResult.labels_eq] using
      segment.pivot_run
  obtain ⟨residual, hsymbolic, hresidualInstance,
      hargumentCount, hresidualSupported, hsize⟩ :=
    exists_supportedSchemaResidual_of_noVariableBefore
      hg hsupported hpadding hnoVariable
      hargumentsLength hargumentsClosed hinstance
      hpivotClosed hpivotRun
  have hresidualWitness : residual.HasPrefixWitness width :=
    hpivotWitness.runActions hg hpadding hsupported.1 hsymbolic
  exact ⟨
    { residual := residual
      symbolic_run := hsymbolic
      instance_matches := hresidualInstance
      argument_count := hargumentCount
      supported := hresidualSupported
      hasPrefixWitness := hresidualWitness
      size_le := hsize }⟩

/-- Word-specific reflection form of one selected exposed-successor row. -/
public theorem
    BalancingSegment.exists_schemaExposedSuccessorResult_of_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hexposureBound : g.exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
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
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hpivotInstance :
      (pivotSchema.instantiate arguments).UnfoldingEquivalent pivot)
    (position : g.SuccessorPosition)
    (hnoVariable :
      g.NoVariableBefore pivotSchema
        (g.exposingWord hnormal position))
    {children : List ℕ} {child : ℕ}
    (hroot : active.rootApplication? =
      some (position.1.val, children))
    (hchild : children[position.2.val]? = some child) :
    Nonempty (segment.SchemaExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem child pivotSchema arguments arity width) := by
  let word := g.exposingWord hnormal position
  have hwordExposure : g.ExposesSuccessor position word :=
    g.exposingWord_exposes hnormal position
  have hwordLength : word.length < bound :=
    lt_of_lt_of_le
      (g.exposingWord_length_lt_exposureBound hnormal position)
      hexposureBound
  obtain ⟨activeTarget, pivotTarget, hactiveRun,
      hactiveMatches, hpivotRun⟩ :=
    segment.exists_pivotTarget_for_exposedSuccessor
      hg hactive position hwordExposure hwordLength hroot hchild
  have hderivation :
      CertificateDerivable g initialLeft initialRight []
        (.pair (stem ++ word.map Sum.inl)
          activeTarget pivotTarget) :=
    houter.follow_runActions
      (preservesGroundSteps_of_wellFormed hg) hequivalent
      hactiveRun hpivotRun
  obtain ⟨pivotResidual, hpivotSymbolic, hpivotMatch,
      hargumentCount, hpivotResidualSupported, hpivotSize⟩ :=
    exists_supportedSchemaResidual_of_noVariableBefore
      hg hpivotSupported hpadding hnoVariable
      hargumentsLength hargumentsClosed hpivotInstance
      (RegularTerm.referenceClosed_of_ground hpivot) hpivotRun
  have hpivotResidualWitness :
      pivotResidual.HasPrefixWitness width :=
    hpivotWitness.runActions hg hpadding hpivotSupported.1
      hpivotSymbolic
  exact ⟨
    { word := word
      word_length_lt := hwordLength
      activeTarget := activeTarget
      pivotTarget := pivotTarget
      active_run := hactiveRun
      active_matches := hactiveMatches
      pivot_run := hpivotRun
      shorter_derivation := hderivation
      pivotResidual := pivotResidual
      pivot_symbolic_run := hpivotSymbolic
      pivot_instance_matches := hpivotMatch
      argument_count := hargumentCount
      pivot_supported := hpivotResidualSupported
      pivot_hasPrefixWitness := hpivotResidualWitness
      pivot_size_le := hpivotSize }⟩

/-- Complete successor-family form with one no-variable proof for every
normal-form exposing word. -/
public theorem
    BalancingSegment.exists_schemaExposedSuccessorFamily_of_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hexposureBound : g.exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
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
    {X : ℕ} {children : List ℕ}
    (hnoVariable :
      ∀ position, position.1.val = X →
        g.NoVariableBefore pivotSchema
          (g.exposingWord hnormal position))
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hpivotInstance :
      (pivotSchema.instantiate arguments).UnfoldingEquivalent pivot)
    (hroot : active.rootApplication? = some (X, children)) :
    Nonempty (segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) := by
  classical
  have hrank : g.ranks[X]? = some children.length :=
    hactive.root_rank_arity hroot
  have hX : X < g.ranks.length :=
    (List.getElem?_eq_some_iff.mp hrank).1
  let symbol : Fin g.ranks.length := ⟨X, hX⟩
  have hsymbolRank :
      g.ranks.get symbol = children.length := by
    apply Option.some.inj
    exact (List.getElem?_eq_getElem hX).symm.trans hrank
  have hexists : ∀ i : Fin children.length,
      Nonempty (segment.SchemaExposedSuccessorResult
        (initialLeft := initialLeft) (initialRight := initialRight)
        stem children[i.val] pivotSchema arguments arity width) := by
    intro i
    let childPosition : Fin (g.ranks.get symbol) :=
      ⟨i.val, by rw [hsymbolRank]; exact i.isLt⟩
    let position : g.SuccessorPosition := ⟨symbol, childPosition⟩
    apply segment
      |>.exists_schemaExposedSuccessorResult_of_noVariableBefore
        hg hnormal hexposureBound hactive hpivot houter
        hequivalent hpivotSupported hpivotWitness hpadding
        hargumentsLength hargumentsClosed
        hpivotInstance position (hnoVariable position rfl)
    · simpa [position, symbol] using hroot
    · change children[i.val]? = some children[i.val]
      exact List.getElem?_eq_getElem i.isLt
  exact ⟨
    { row := fun i => Classical.choice (hexists i) }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
