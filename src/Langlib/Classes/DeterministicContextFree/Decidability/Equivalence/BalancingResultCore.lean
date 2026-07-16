module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.NonSinkingReflection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OrdinaryGroundRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FinitePrefixCoverage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinking
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SupportedVariableRoots

@[expose]
public section

/-!
# The symbolic active side of a balancing result

A non-sinking balancing segment never reaches one of the boundary variables
of the active term's depth-one prefix before its final label.  Consequently
the whole concrete segment reflects to an ordinary run of that finite prefix.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- The tails of a depth-one prefix are exactly the immediate pointed
children, in order. -/
public theorem depthPrefix_one_tails_of_rootApplication
    {term : RegularTerm} {X : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (X, children)) :
    (term.depthPrefix 1).tails =
      children.map term.withRoot := by
  rw [show 1 = 0 + 1 by omega,
    depthPrefix_succ_of_rootApplication hroot]
  rw [DepthPrefix.assemble_tails]
  simp only [depthPrefix_zero]
  simp only [List.flatMap_map]
  change (children.map fun child => [term.withRoot child]).flatten =
    children.map term.withRoot
  clear hroot X
  induction children with
  | nil => rfl
  | cons child children ih => simp [ih]

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The finite-prefix residual obtained from the active side of a balancing
segment. -/
public structure BalancingSegment.ActivePrefixResidual
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (filler : RegularTerm) where
  actions : List Action
  labels_eq : labels = actions.map Sum.inl
  actions_length : actions.length = bound
  residual : RegularTerm
  symbolic_run :
    g.runActions? actions
        (active.depthPrefix 1).head.toRegularTerm =
      some residual
  instance_matches :
    (residual.instantiate
        ((active.depthPrefix 1).paddedArguments g.ranks filler))
      |>.UnfoldingEquivalent segment.active_target
  supported :
    RegularTerm.SupportedByPrefix g.ranks
      ((active.depthPrefix 1).schemaArity g.ranks)
      (active.depthPrefix 1).tails.length residual
  arity_le :
    (active.depthPrefix 1).schemaArity g.ranks ≤
      max (RegularTerm.depthPrefixTailBound g.ranks 1)
        (g.ranks.foldr max 0)
  size_le :
    residual.nodes.length ≤
      g.residualNodeBound actions.length
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) 1)

/-- A balancing segment reflects to a supported symbolic run of the active
term's depth-one prefix. -/
public theorem BalancingSegment.exists_activePrefixResidual
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {active pivot : RegularTerm}
    {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    {filler : RegularTerm} (hfiller : filler.Ground g.ranks) :
    Nonempty (segment.ActivePrefixResidual filler) := by
  let decomposition := active.depthPrefix 1
  let schema := decomposition.head.toRegularTerm
  let arguments := decomposition.paddedArguments g.ranks filler
  have hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  obtain ⟨actions, hlabels⟩ :=
    hgroundSteps.exists_actions_of_ground_run
      hactive segment.active_run
  have hactionsLength : actions.length = bound := by
    have hlength := segment.word_length
    rw [hlabels, List.length_map] at hlength
    exact hlength
  have hactiveRun :
      g.runActions? actions active = some segment.active_target := by
    simpa [runActions?, hlabels] using segment.active_run
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid active 1
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hactive 1
  have hschemaSupported :
      RegularTerm.SupportedByPrefix g.ranks
        (decomposition.schemaArity g.ranks)
        decomposition.tails.length schema := by
    simpa [decomposition, schema, DepthPrefix.schemaArity] using
      (FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked)
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  have hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks := by
    exact RegularTerm.depthPrefix_paddedArguments_ground
      hactive hfiller 1
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hschemaWellFormed := hschemaSupported.1
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent active := by
    exact RegularTerm.depthPrefix_compiled_unfoldingEquivalent
      hactive hfiller 1
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed hschemaWellFormed)
      hargumentsClosed
  obtain ⟨instanceTarget, hinstanceRun, hinstanceTargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      hinstanceEquivalent hinstanceClosed
      (RegularTerm.referenceClosed_of_ground hactive)
      hactiveRun
  obtain ⟨X, children, hactiveRoot⟩ :=
    hactive.exists_rootApplication
  have htails :
      decomposition.tails = children.map active.withRoot := by
    simpa [decomposition] using
      RegularTerm.depthPrefix_one_tails_of_rootApplication hactiveRoot
  have hnoVariable : g.NoVariableBefore schema actions := by
    intro stem suffix hword hsuffix residual x
      hstemRun hresidualVariable
    have hresidualSupported :=
      hschemaSupported.residual hg hpadding hstemRun
    have hresidualRoot :
        residual.rootNode? = some (.inl x) := by
      exact rootNode?_variable_of_unfoldingEquivalent
        hresidualVariable.symm
        (RegularTerm.variableTerm_rootNode? x)
    have hxTails : x < decomposition.tails.length :=
      hresidualSupported.variableIndex_lt_width_of_root
        hresidualRoot
    have hxChildren : x < children.length := by
      simpa [htails] using hxTails
    have hstemNonempty : stem ≠ [] := by
      intro hnil
      subst stem
      simp only [runActions?, List.map_nil, run?_nil] at hstemRun
      have hresidualEq : schema = residual := Option.some.inj hstemRun
      rw [← hresidualEq] at hresidualVariable
      subst residual
      have hschemaVariable :
          schema.rootNode? = some (.inl x) :=
        rootNode?_variable_of_unfoldingEquivalent
          hresidualVariable.symm
          (RegularTerm.variableTerm_rootNode? x)
      have hhead : decomposition.head =
          .app X (DepthPrefix.collectHeads
            (children.map fun child =>
              (active.withRoot child).depthPrefix 0) 0) := by
        unfold decomposition
        rw [show 1 = 0 + 1 by omega,
          RegularTerm.depthPrefix_succ_of_rootApplication hactiveRoot]
        rfl
      obtain ⟨schemaChildren, hschemaApplication⟩ :
          ∃ schemaChildren,
            schema.rootApplication? = some (X, schemaChildren) := by
        unfold schema
        rw [hhead]
        exact ⟨_, FiniteHead.toRegularTerm_app_rootApplication? _ _⟩
      simp [RegularTerm.rootApplication?, hschemaVariable] at hschemaApplication
    have hschemaTemplate :
        schema.UnfoldingEquivalent
          (RegularTerm.symbolTemplate X children.length) := by
      simpa [schema, decomposition] using
        depthPrefix_one_head_unfoldingEquivalent_symbolTemplate
          hactive hactiveRoot
    obtain ⟨templateResidual, htemplateRun,
        htemplateMatches⟩ :=
      exists_runActions_of_unfoldingEquivalent hg
        hschemaTemplate.symm
        (RegularTerm.symbolTemplate_referenceClosed X children.length)
        (RegularTerm.referenceClosed_of_wellFormed
          hschemaWellFormed)
        hstemRun
    have htemplateRoot :
        templateResidual.rootNode? = some (.inl x) :=
      rootNode?_variable_of_unfoldingEquivalent
        htemplateMatches.symm hresidualRoot
    have hrootSinks :
        g.RootSinksBy active (stem.map Sum.inl) :=
      ⟨X, children, stem, [], hactiveRoot, by simp,
        ⟨
          { child := ⟨x, hxChildren⟩
            target := templateResidual
            actions_nonempty := hstemNonempty
            run := htemplateRun
            target_root := htemplateRoot }⟩⟩
    apply segment.no_early_root_sink
      (stem.map Sum.inl) (suffix.map Sum.inl)
    · calc
        labels = actions.map Sum.inl := hlabels
        _ = (stem.map Sum.inl) ++ (suffix.map Sum.inl) := by
          simp [hword]
    · simpa using hsuffix
    · exact hrootSinks
  obtain ⟨residual, hsymbolicRun, hresidualMatch⟩ :=
    runActions?_reflects_instantiation_of_noVariableBefore
      hg actions ⟨_, hschemaWellFormed⟩ hargumentsClosed
      hinstanceRun hnoVariable
  have hresidualSupported :=
    hschemaSupported.residual hg hpadding hsymbolicRun
  have harity :=
    RegularTerm.depthPrefix_schemaArity_le hactive 1
  have hinitialSize :=
    RegularTerm.depthPrefix_schema_nodes_length_le hactive 1
  have hresidualSize :=
    g.runActions?_nodes_length_le hg
      ⟨decomposition.schemaArity g.ranks, hschemaWellFormed⟩
      hinitialSize hsymbolicRun
  exact ⟨
    { actions := actions
      labels_eq := hlabels
      actions_length := hactionsLength
      residual := residual
      symbolic_run := by simpa [schema, decomposition] using hsymbolicRun
      instance_matches := by
        simpa [arguments, decomposition] using
          hresidualMatch.trans hinstanceTargetEquivalent
      supported := by
        simpa [decomposition] using hresidualSupported
      arity_le := by simpa [decomposition] using harity
      size_le := by simpa [decomposition] using hresidualSize }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
