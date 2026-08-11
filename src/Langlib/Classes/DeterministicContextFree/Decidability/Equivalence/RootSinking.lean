module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DepthExposure
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CertificateRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ExposedEquations
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteHeadPrefixes
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.IdentitySubstitution
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinkingCore

@[expose]
public section

/-!
# Replaying syntactic root-sinking witnesses

The lightweight witness lives in `RootSinkingCore`, below balancing.  This
module sits above finite-prefix execution and proves that the retained open
run replays on every schema with the same root symbol and arity, selecting a
literal immediate child without any faithfulness assumption.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The endpoint of a root-sinking step denotes its selected parameter. -/
public theorem RootSinkingStep.target_matches
    {g : EncodedFirstOrderGrammar Action}
    {rootSymbol rank : ℕ} {actions : List Action}
    (step : RootSinkingStep g rootSymbol rank actions) :
    step.target.UnfoldingEquivalent
      (RegularTerm.variableTerm step.child.val) :=
  unfoldingEquivalent_variableTerm_of_rootNode? step.target_root

private theorem collectHeads_depthPrefix_zero_map_toRegularTerm
    (term : RegularTerm) :
    ∀ (children : List ℕ) (offset : ℕ),
      (DepthPrefix.collectHeads
          (children.map fun child =>
            (term.withRoot child).depthPrefix 0)
          offset).map FiniteHead.toRegularTerm =
        (List.range children.length).map fun i =>
          RegularTerm.variableTerm (offset + i)
  | [], _offset => rfl
  | _child :: children, offset => by
      simp only [List.map_cons, RegularTerm.depthPrefix_zero,
        DepthPrefix.collectHeads, FiniteHead.shiftVariables,
        FiniteHead.toRegularTerm, List.length_cons]
      change
        RegularTerm.variableTerm offset ::
            (DepthPrefix.collectHeads
              (children.map fun child =>
                (term.withRoot child).depthPrefix 0)
              (offset + 1)).map FiniteHead.toRegularTerm =
          (List.range (children.length + 1)).map fun i =>
            RegularTerm.variableTerm (offset + i)
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map,
        Function.comp_apply, Nat.add_zero]
      rw [collectHeads_depthPrefix_zero_map_toRegularTerm
        term children (offset + 1)]
      congr 1
      apply List.map_congr_left
      intro i _hi
      congr 1
      omega

/-- The compiled depth-one head of a ground application is just its canonical
root symbol template, up to unreachable graph-layout differences. -/
public theorem depthPrefix_one_head_unfoldingEquivalent_symbolTemplate
    {term : RegularTerm} {ranks : List ℕ}
    (hterm : term.Ground ranks)
    {rootSymbol : ℕ} {children : List ℕ}
    (hroot :
      term.rootApplication? = some (rootSymbol, children)) :
    (term.depthPrefix 1).head.toRegularTerm.UnfoldingEquivalent
      (RegularTerm.symbolTemplate rootSymbol children.length) := by
  let childPrefixes :=
    children.map fun child =>
      (term.withRoot child).depthPrefix 0
  have hdecomposition :
      term.depthPrefix 1 =
        DepthPrefix.assemble rootSymbol childPrefixes := by
    simpa [childPrefixes] using
      RegularTerm.depthPrefix_succ_of_rootApplication hroot 0
  have harguments :
      (DepthPrefix.collectHeads childPrefixes 0).map
          FiniteHead.toRegularTerm =
        RegularTerm.identityArguments children.length := by
    simpa [childPrefixes, RegularTerm.identityArguments] using
      collectHeads_depthPrefix_zero_map_toRegularTerm
        term children 0
  have hrank :
      ranks[rootSymbol]? = some children.length :=
    hterm.root_rank_arity hroot
  have hchildPrefixesLength :
      childPrefixes.length = children.length := by
    simp [childPrefixes]
  rw [hdecomposition]
  simpa [DepthPrefix.assemble, FiniteHead.toRegularTerm,
    harguments, hchildPrefixesLength] using
      (RegularTerm.instantiate_identity_unfoldingEquivalent
        (RegularTerm.symbolTemplate_wellFormed hrank))

/-- Replay one open root-sinking step on any reference-closed schema with
the same ranked root. -/
public theorem RootSinkingStep.replay_of_root
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {rootSymbol : ℕ} {children : List ℕ} {actions : List Action}
    (step : RootSinkingStep
      g rootSymbol children.length actions)
    {schema : RegularTerm}
    (hschemaClosed : schema.ReferenceClosed)
    (hrank :
      g.ranks[rootSymbol]? = some children.length)
    (hroot :
      schema.rootApplication? = some (rootSymbol, children)) :
    ∃ target child,
      child ∈ children ∧
        schema.DescendantAt 1 child ∧
        g.runActions? actions schema = some target ∧
        target.UnfoldingEquivalent (schema.withRoot child) := by
  let arguments := children.map schema.withRoot
  let child := children[step.child.val]
  have hchildrenBound :=
    RegularTerm.rootApplication_children_lt hschemaClosed hroot
  have hchildMem : child ∈ children :=
    List.getElem_mem step.child.isLt
  have hchildBound : child < schema.nodes.length :=
    hchildrenBound child hchildMem
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    obtain ⟨index, hindex, rfl⟩ :=
      List.mem_map.mp hargument
    exact RegularTerm.withRoot_referenceClosed hschemaClosed
      (hchildrenBound index hindex)
  have htemplateWellFormed :
      (RegularTerm.symbolTemplate rootSymbol children.length)
        |>.WellFormed g.ranks children.length :=
    RegularTerm.symbolTemplate_wellFormed hrank
  obtain ⟨templateTarget, htemplateRun,
      htargetInstantiation⟩ :=
    g.runActions?_instantiate hg actions htemplateWellFormed
      hargumentsClosed step.run
  have htemplateInstance :
      ((RegularTerm.symbolTemplate rootSymbol children.length)
          |>.instantiate arguments).UnfoldingEquivalent schema := by
    simpa [arguments] using
      RegularTerm.symbolTemplate_instantiate_unfoldingEquivalent
        hschemaClosed hroot
  have htemplateInstanceClosed :
      ((RegularTerm.symbolTemplate rootSymbol children.length)
          |>.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed
        htemplateWellFormed)
      hargumentsClosed
  obtain ⟨target, htargetRun, htargetTemplate⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      htemplateInstance.symm hschemaClosed
      htemplateInstanceClosed htemplateRun
  have hargument :
      arguments[step.child.val]? =
        some (schema.withRoot child) := by
    simp [arguments, child, step.child.isLt]
  have htargetNode :
      step.target.nodeAt? step.target.root =
        some (.inl step.child.val) := by
    simpa [RegularTerm.rootNode?] using step.target_root
  have htargetChild :
      (step.target.instantiate arguments).UnfoldingEquivalent
        (schema.withRoot child) :=
    RegularTerm.instantiate_unfoldingEquivalent_argument
      htargetNode hargument
      (RegularTerm.withRoot_referenceClosed
        hschemaClosed hchildBound)
  refine ⟨target, child, hchildMem, ?_, htargetRun, ?_⟩
  · exact .child .root
      (RegularTerm.nodeAt?_root_of_rootApplication? hroot)
      hchildMem
  · exact htargetTemplate.trans
      (htargetInstantiation.symm.trans htargetChild)

/-- Well-formed-schema specialization of `replay_of_root`. -/
public theorem RootSinkingStep.replay
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {rootSymbol : ℕ} {children : List ℕ} {actions : List Action}
    (step : RootSinkingStep
      g rootSymbol children.length actions)
    {schema : RegularTerm} {variableBound : ℕ}
    (hschema : schema.WellFormed g.ranks variableBound)
    (hroot :
      schema.rootApplication? = some (rootSymbol, children)) :
    ∃ target child,
      child ∈ children ∧
        schema.DescendantAt 1 child ∧
        g.runActions? actions schema = some target ∧
        target.UnfoldingEquivalent (schema.withRoot child) := by
  have hrank :
      g.ranks[rootSymbol]? = some children.length := by
    obtain ⟨rank, hrank, hlength⟩ :=
      rank_arity_of_wellFormed hschema
        (RegularTerm.nodeAt?_root_of_rootApplication? hroot)
    simpa [hlength] using hrank
  exact step.replay_of_root hg
    (RegularTerm.referenceClosed_of_wellFormed hschema)
    hrank hroot

/-- Ground-schema specialization of `replay_of_root`. -/
public theorem RootSinkingStep.replay_ground
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {rootSymbol : ℕ} {children : List ℕ} {actions : List Action}
    (step : RootSinkingStep
      g rootSymbol children.length actions)
    {schema : RegularTerm}
    (hschema : schema.Ground g.ranks)
    (hroot :
      schema.rootApplication? = some (rootSymbol, children)) :
    ∃ target child,
      child ∈ children ∧
        schema.DescendantAt 1 child ∧
        g.runActions? actions schema = some target ∧
        target.UnfoldingEquivalent (schema.withRoot child) :=
  step.replay_of_root hg
    (RegularTerm.referenceClosed_of_ground hschema)
    (hschema.root_rank_arity hroot) hroot

/-- Replay a root-sinking prefix on its attached well-formed source. -/
public theorem RootSinksBy.exists_schemaChild
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source : RegularTerm} {word : List (Label Action)}
    (hsource : ∃ variableBound,
      source.WellFormed g.ranks variableBound)
    (hsinks : g.RootSinksBy source word) :
    ∃ actions suffix target child,
      word = actions.map Sum.inl ++ suffix ∧
        actions ≠ [] ∧
        source.DescendantAt 1 child ∧
        g.runActions? actions source = some target ∧
        target.UnfoldingEquivalent (source.withRoot child) := by
  obtain ⟨rootSymbol, children, actions, suffix,
      hroot, hword, ⟨step⟩⟩ := hsinks
  obtain ⟨target, child, _hchildMem, hchild,
      hrun, htarget⟩ :=
    step.replay hg (Classical.choose_spec hsource) hroot
  exact ⟨actions, suffix, target, child, hword,
    step.actions_nonempty, hchild, hrun, htarget⟩

/-- Replay a root-sinking prefix on its attached ground source. -/
public theorem RootSinksBy.exists_schemaChild_of_ground
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source : RegularTerm} {word : List (Label Action)}
    (hsource : source.Ground g.ranks)
    (hsinks : g.RootSinksBy source word) :
    ∃ actions suffix target child,
      word = actions.map Sum.inl ++ suffix ∧
        actions ≠ [] ∧
        source.DescendantAt 1 child ∧
        g.runActions? actions source = some target ∧
        target.UnfoldingEquivalent (source.withRoot child) := by
  obtain ⟨rootSymbol, children, actions, suffix,
      hroot, hword, ⟨step⟩⟩ := hsinks
  obtain ⟨target, child, _hchildMem, hchild,
      hrun, htarget⟩ :=
    step.replay_ground hg hsource hroot
  exact ⟨actions, suffix, target, child, hword,
    step.actions_nonempty, hchild, hrun, htarget⟩

/-- Forget the open computation on a well-formed source. -/
public theorem RootSinksBy.toSinksBy
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source : RegularTerm} {word : List (Label Action)}
    (hsource : ∃ variableBound,
      source.WellFormed g.ranks variableBound)
    (hsinks : g.RootSinksBy source word) :
    g.SinksBy source word := by
  obtain ⟨actions, suffix, target, child, hword,
      hnonempty, hchild, hrun, htarget⟩ :=
    hsinks.exists_schemaChild hg hsource
  refine ⟨actions.map Sum.inl, suffix, hword, ?_, ?_⟩
  · simpa using hnonempty
  · exact ⟨source.withRoot child, target,
      ⟨child, hchild, rfl⟩,
      by simpa [runActions?] using hrun,
      htarget⟩

/-- Forget the open computation on a ground source. -/
public theorem RootSinksBy.toSinksBy_of_ground
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source : RegularTerm} {word : List (Label Action)}
    (hsource : source.Ground g.ranks)
    (hsinks : g.RootSinksBy source word) :
    g.SinksBy source word := by
  obtain ⟨actions, suffix, target, child, hword,
      hnonempty, hchild, hrun, htarget⟩ :=
    hsinks.exists_schemaChild_of_ground hg hsource
  refine ⟨actions.map Sum.inl, suffix, hword, ?_, ?_⟩
  · simpa using hnonempty
  · exact ⟨source.withRoot child, target,
      ⟨child, hchild, rfl⟩,
      by simpa [runActions?] using hrun,
      htarget⟩

/-- A source-attached package retaining both the syntactic witness and its
semantic replay. -/
public structure RootSinksByAt
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action)) : Prop where
  rootSinks : g.RootSinksBy source word
  sinks : g.SinksBy source word

namespace RootSinksByAt

public theorem of_rootSinks
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source : RegularTerm} {word : List (Label Action)}
    (hsource : ∃ variableBound,
      source.WellFormed g.ranks variableBound)
    (hsinks : g.RootSinksBy source word) :
    g.RootSinksByAt source word :=
  ⟨hsinks, hsinks.toSinksBy hg hsource⟩

public theorem of_rootSinks_ground
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source : RegularTerm} {word : List (Label Action)}
    (hsource : source.Ground g.ranks)
    (hsinks : g.RootSinksBy source word) :
    g.RootSinksByAt source word :=
  ⟨hsinks, hsinks.toSinksBy_of_ground hg hsource⟩

public theorem toSinksBy
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    (hsinks : g.RootSinksByAt source word) :
    g.SinksBy source word :=
  hsinks.sinks

end RootSinksByAt

end EncodedFirstOrderGrammar

end DCFEquivalence
