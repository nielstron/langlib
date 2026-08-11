module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DepthPrefixTailOccurrences
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SupportedVariableRoots
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CertificateRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationSupport

@[expose]
public section

/-!
# Reflecting a run through one fixed tail tuple

If no proper prefix of a concrete run reaches a boundary occurrence at depth
`depth`, the run cannot expose a variable of the compiled depth prefix.
Consequently the whole run reflects symbolically while retaining the one
fixed tuple of depth-prefix tails.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- No proper prefix of an ordinary word exposes a depth-`depth` boundary
occurrence of `term`. -/
@[expose] public def NoDepthExposureBefore
    (g : EncodedFirstOrderGrammar Action)
    (term : RegularTerm) (depth : ℕ) (word : List Action) : Prop :=
  ∀ stem suffix,
    word = stem ++ suffix →
    suffix ≠ [] →
    ¬g.ExposesAtDepth term (stem.map Sum.inl) depth

/-- If the complete ordinary word has no prefix exposing depth `depth`, then
in particular no proper prefix does. -/
public theorem noDepthExposureBefore_of_not_exposesBy
    {g : EncodedFirstOrderGrammar Action}
    {term : RegularTerm} {depth : ℕ} {word : List Action}
    (hmissing :
      ¬g.ExposesBy term (word.map Sum.inl) depth) :
    g.NoDepthExposureBefore term depth word := by
  intro stem suffix hword _hsuffix hexposes
  apply hmissing
  refine ⟨stem.map Sum.inl, suffix.map Sum.inl, ?_, hexposes⟩
  simpa [hword] using (List.map_append Sum.inl stem suffix).symm

/-- Absence of concrete depth-boundary exposure implies absence of symbolic
variable exposure in the compiled prefix. -/
public theorem depthPrefix_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) {word : List Action}
    (hnoExposure : g.NoDepthExposureBefore term depth word) :
    g.NoVariableBefore
      (term.depthPrefix depth).head.toRegularTerm word := by
  let decomposition := term.depthPrefix depth
  let schema := decomposition.head.toRegularTerm
  let arguments := decomposition.paddedArguments g.ranks filler
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid term depth
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hterm depth
  have hschemaSupported :
      RegularTerm.SupportedByPrefix g.ranks
        (decomposition.schemaArity g.ranks)
        decomposition.tails.length schema := by
    exact FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  have hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks :=
    RegularTerm.depthPrefix_paddedArguments_ground
      hterm hfiller depth
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent term :=
    RegularTerm.depthPrefix_compiled_unfoldingEquivalent
      hterm hfiller depth
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed hschemaSupported.1)
      hargumentsClosed
  intro stem suffix hword hsuffix residual x
    hstemRun hresidualVariable
  have hresidualSupported :=
    hschemaSupported.residual hg hpadding hstemRun
  have hresidualRoot :
      residual.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hresidualVariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  have hxTails : x < decomposition.tails.length :=
    hresidualSupported.variableIndex_lt_width_of_root hresidualRoot
  let tail := decomposition.tails[x]
  have htailGet : decomposition.tails[x]? = some tail :=
    List.getElem?_eq_getElem hxTails
  have hargumentGet : arguments[x]? = some tail := by
    unfold arguments DepthPrefix.paddedArguments
    rw [List.getElem?_append_left hxTails]
    exact htailGet
  have hresidualNode :
      residual.nodeAt? residual.root = some (.inl x) := by
    simpa [RegularTerm.rootNode?] using hresidualRoot
  have hresidualInstanceTail :
      (residual.instantiate arguments).UnfoldingEquivalent tail :=
    RegularTerm.instantiate_unfoldingEquivalent_argument
      hresidualNode hargumentGet
      (RegularTerm.referenceClosed_of_ground
        (hargumentsGround tail
          (List.mem_of_getElem? hargumentGet)))
  obtain ⟨instantiatedStem, hinstantiatedStemRun,
      hresidualInstantiation⟩ :=
    g.runActions?_instantiate hg stem hschemaSupported.1
      hargumentsClosed hstemRun
  obtain ⟨termStem, htermStemRun, htermStemEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      hinstanceEquivalent.symm
      (RegularTerm.referenceClosed_of_ground hterm)
      hinstanceClosed hinstantiatedStemRun
  have htermStemTail :
      termStem.UnfoldingEquivalent tail :=
    htermStemEquivalent.trans
      (hresidualInstantiation.symm.trans hresidualInstanceTail)
  have htailSubterm :
      term.SubtermAtDepth depth tail :=
    RegularTerm.depthPrefix_tails_subtermAtDepth
      hterm depth tail (List.getElem_mem hxTails)
  apply hnoExposure stem suffix hword hsuffix
  exact ⟨tail, termStem, htailSubterm,
    by simpa [runActions?] using htermStemRun,
    htermStemTail⟩

/-- One symbolic residual over a fixed depth-prefix argument tuple. -/
public structure FixedTailResidual
    (g : EncodedFirstOrderGrammar Action)
    (term filler : RegularTerm) (depth : ℕ)
    (word : List Action) (target : RegularTerm) where
  residual : RegularTerm
  symbolic_run :
    g.runActions? word
      (term.depthPrefix depth).head.toRegularTerm = some residual
  instance_matches :
    (residual.instantiate
      ((term.depthPrefix depth).paddedArguments g.ranks filler))
        |>.UnfoldingEquivalent target
  supported :
    RegularTerm.SupportedByPrefix g.ranks
      ((term.depthPrefix depth).schemaArity g.ranks)
      (term.depthPrefix depth).tails.length residual
  hasPrefixWitness :
    residual.HasPrefixWitness (term.depthPrefix depth).tails.length
  size_le :
    residual.nodes.length ≤
      g.residualNodeBound word.length
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) depth)

/-- A concrete run with no earlier depth-boundary exposure is represented by
a supported symbolic residual over the one fixed tail tuple. -/
public theorem exists_fixedTailResidual
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler target : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) {word : List Action}
    (hrun : g.runActions? word term = some target)
    (hnoExposure : g.NoDepthExposureBefore term depth word) :
    Nonempty (FixedTailResidual g term filler depth word target) := by
  let decomposition := term.depthPrefix depth
  let schema := decomposition.head.toRegularTerm
  let arguments := decomposition.paddedArguments g.ranks filler
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid term depth
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hterm depth
  have hschemaSupported :
      RegularTerm.SupportedByPrefix g.ranks
        (decomposition.schemaArity g.ranks)
        decomposition.tails.length schema :=
    FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  have hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks :=
    RegularTerm.depthPrefix_paddedArguments_ground
      hterm hfiller depth
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent term :=
    RegularTerm.depthPrefix_compiled_unfoldingEquivalent
      hterm hfiller depth
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed hschemaSupported.1)
      hargumentsClosed
  obtain ⟨instanceTarget, hinstanceRun, hinstanceTargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      hinstanceEquivalent hinstanceClosed
      (RegularTerm.referenceClosed_of_ground hterm) hrun
  obtain ⟨residual, hsymbolic, hresidualMatch⟩ :=
    runActions?_reflects_instantiation_of_noVariableBefore
      hg word ⟨_, hschemaSupported.1⟩ hargumentsClosed
      hinstanceRun
      (by
        simpa [schema, decomposition] using
          depthPrefix_noVariableBefore hg hterm hfiller
            depth hnoExposure)
  have hresidualSupported :=
    hschemaSupported.residual hg hpadding hsymbolic
  have hsourceWitness :
      schema.HasPrefixWitness decomposition.tails.length :=
    FiniteHead.toRegularTerm_hasPrefixWitness hvalid
  have hresidualWitness :=
    hsourceWitness.runActions hg hpadding hschemaSupported.1 hsymbolic
  have hinitialSize :=
    RegularTerm.depthPrefix_schema_nodes_length_le hterm depth
  have hsize :=
    g.runActions?_nodes_length_le hg
      ⟨decomposition.schemaArity g.ranks, hschemaSupported.1⟩
      hinitialSize hsymbolic
  exact ⟨
    { residual := residual
      symbolic_run := by simpa [schema, decomposition] using hsymbolic
      instance_matches := by
        simpa [arguments, decomposition] using
          hresidualMatch.trans hinstanceTargetEquivalent
      supported := by simpa [decomposition] using hresidualSupported
      hasPrefixWitness := by
        simpa [schema, decomposition] using hresidualWitness
      size_le := by simpa [decomposition] using hsize }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
