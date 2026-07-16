module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.NonSinkingReflection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinking
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SupportedVariableRoots

@[expose]
public section

/-!
# Root-syntactic non-sinking reflection

If a proper symbolic prefix of the depth-one head of a ground term reaches a
variable, then the same action prefix is an open computation from the term's
root-symbol template to one of its literal parameters.  Thus failure of
`RootSinksBy` gives the `NoVariableBefore` premise needed to reflect a
concrete prelude without appealing to the strictly stronger semantic
`SinksBy` predicate.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- If a concrete ordinary word does not root-sink from a ground term, its
symbolic execution over the depth-one prefix cannot reach a variable before
the end. -/
public theorem depthPrefix_one_noVariableBefore_of_not_rootSinksBy
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term : RegularTerm}
    (hterm : term.Ground g.ranks)
    {word : List Action}
    (hnotSinks : ¬g.RootSinksBy term (word.map Sum.inl)) :
    g.NoVariableBefore
      (term.depthPrefix 1).head.toRegularTerm word := by
  let decomposition := term.depthPrefix 1
  let schema := decomposition.head.toRegularTerm
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid term 1
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hterm 1
  have hschemaSupported :
      RegularTerm.SupportedByPrefix g.ranks
        (decomposition.schemaArity g.ranks)
        decomposition.tails.length schema :=
    FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  intro stem suffix hword _hsuffix residual x
    hstemRun hresidualVariable
  have hresidualSupported :=
    hschemaSupported.residual hg hpadding hstemRun
  have hresidualRoot :
      residual.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hresidualVariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  obtain ⟨rootSymbol, children, hroot⟩ :=
    hterm.exists_rootApplication
  have hschemaTemplate :
      schema.UnfoldingEquivalent
        (RegularTerm.symbolTemplate rootSymbol children.length) := by
    simpa [schema, decomposition] using
      depthPrefix_one_head_unfoldingEquivalent_symbolTemplate
        hterm hroot
  by_cases hstemEmpty : stem = []
  · subst stem
    simp [runActions?] at hstemRun
    subst residual
    have htemplateRoot :
        (RegularTerm.symbolTemplate rootSymbol children.length
            ).rootApplication? =
          some (rootSymbol,
            (List.range children.length).map (fun i => i + 1)) :=
      RegularTerm.symbolTemplate_rootApplication? _ _
    obtain ⟨schemaChildren, hschemaRoot, _hchildren⟩ :=
      RegularTerm.rootApplication?_of_unfoldingEquivalent
        hschemaTemplate.symm htemplateRoot
    have hschemaRootNode :
        schema.rootNode? =
          some (.inr (rootSymbol, schemaChildren)) := by
      exact RegularTerm.nodeAt?_root_of_rootApplication?
        hschemaRoot
    rw [hschemaRootNode] at hresidualRoot
    simp at hresidualRoot
  · have hxWidth :
        x < decomposition.tails.length :=
      hresidualSupported.variableIndex_lt_width_of_root
        hresidualRoot
    have htails :
        decomposition.tails =
          children.map term.withRoot := by
      dsimp [decomposition]
      rw [show 1 = 0 + 1 by omega,
        RegularTerm.depthPrefix_succ_of_rootApplication hroot,
        DepthPrefix.assemble_tails]
      simp only [RegularTerm.depthPrefix_zero,
        List.flatMap_map]
      change
        (children.map fun child => [term.withRoot child]).flatten =
          children.map term.withRoot
      have hflatten :
          ∀ nodes : List ℕ,
            (nodes.map fun child => [term.withRoot child]).flatten =
              nodes.map term.withRoot := by
        intro nodes
        induction nodes with
        | nil => rfl
        | cons child nodes ih => simp [ih]
      exact hflatten children
    have hxChildren : x < children.length := by
      rw [htails, List.length_map] at hxWidth
      exact hxWidth
    have hrank :
        g.ranks[rootSymbol]? = some children.length :=
      hterm.root_rank_arity hroot
    have htemplateWellFormed :
        (RegularTerm.symbolTemplate rootSymbol children.length)
          |>.WellFormed g.ranks children.length :=
      RegularTerm.symbolTemplate_wellFormed hrank
    obtain ⟨target, htargetRun, htargetResidual⟩ :=
      exists_runActions_of_unfoldingEquivalent hg
        hschemaTemplate.symm
        (RegularTerm.referenceClosed_of_wellFormed
          htemplateWellFormed)
        (RegularTerm.referenceClosed_of_wellFormed
          hschemaSupported.1)
        hstemRun
    have htargetVariable :
        target.UnfoldingEquivalent
          (RegularTerm.variableTerm x) :=
      htargetResidual.trans hresidualVariable
    have htargetRoot :
        target.rootNode? = some (.inl x) :=
      rootNode?_variable_of_unfoldingEquivalent
        htargetVariable.symm
        (RegularTerm.variableTerm_rootNode? x)
    apply hnotSinks
    refine ⟨rootSymbol, children, stem, suffix.map Sum.inl,
      hroot, ?_, ?_⟩
    · simp [hword]
    · exact ⟨
        { child := ⟨x, hxChildren⟩
          target := target
          actions_nonempty := hstemEmpty
          run := htargetRun
          target_root := htargetRoot }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
