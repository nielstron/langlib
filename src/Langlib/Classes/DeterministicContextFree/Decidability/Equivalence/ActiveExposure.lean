module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveParameterReindexing
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ExposedCertificateRuns

@[expose]
public section

/-!
# Exposed variables lie in the active prefix

An exposed symbolic residual can only depend on an argument on which its source
schema semantically depends.  Consequently, for schemas supported by the first
`width` arguments, the variable selected by the exposed-equation lemma lies
strictly below `width`.  This is the fact which permits moving that variable to
the final active slot before tail elimination.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Replace one position of the identity substitution by a fresh variable. -/
@[expose] public def freshenedIdentityArguments
    (arity x : ℕ) : List RegularTerm :=
  (identityArguments arity).set x (variableTerm arity)

@[simp] public theorem freshenedIdentityArguments_length
    (arity x : ℕ) :
    (freshenedIdentityArguments arity x).length = arity := by
  simp [freshenedIdentityArguments]

public theorem freshenedIdentityArguments_getElem?_eq
    {arity x : ℕ} (hx : x < arity) :
    (freshenedIdentityArguments arity x)[x]? =
      some (variableTerm arity) := by
  simp [freshenedIdentityArguments, hx]

public theorem freshenedIdentityArguments_getElem?_ne
    {arity x i : ℕ} (hi : i < arity) (hix : i ≠ x) :
    (freshenedIdentityArguments arity x)[i]? =
      some (variableTerm i) := by
  rw [freshenedIdentityArguments,
    List.getElem?_set_ne (fun hxi => hix hxi.symm)]
  exact identityArguments_getElem? hi

public theorem freshenedIdentityArguments_referenceClosed
    {arity x : ℕ} (hx : x < arity) :
    ∀ argument ∈ freshenedIdentityArguments arity x,
      argument.ReferenceClosed := by
  intro argument hargument
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hargument
  have hiBound : i < arity := by
    have := (List.getElem?_eq_some_iff.mp hi).choose
    simpa using this
  by_cases hix : i = x
  · subst i
    rw [freshenedIdentityArguments_getElem?_eq hx] at hi
    cases Option.some.inj hi
    exact variableTerm_referenceClosed arity
  · rw [freshenedIdentityArguments_getElem?_ne hiBound hix] at hi
    cases Option.some.inj hi
    exact variableTerm_referenceClosed i

/-- The ordinary residual of a prefix-supported schema still depends
semantically only on that same active prefix.  No structural well-formedness
claim is made for the residual graph, since root rewriting may retain harmless
RHS garbage at a larger raw variable bound. -/
public theorem SupportedByPrefix.residual_instances_unfoldingEquivalent
    {Action : Type} [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema residual : RegularTerm} {arity width : ℕ}
    (hsupported : SupportedByPrefix g.ranks arity width schema)
    {word : List Action}
    (hrun : g.runActions? word schema = some residual)
    {leftArguments rightArguments : List RegularTerm}
    (hleftLength : leftArguments.length = arity)
    (hrightLength : rightArguments.length = arity)
    (hleftClosed : ∀ argument ∈ leftArguments,
      argument.ReferenceClosed)
    (hrightClosed : ∀ argument ∈ rightArguments,
      argument.ReferenceClosed)
    (harguments : ArgumentsEquivalentThrough width
      leftArguments rightArguments) :
    (residual.instantiate leftArguments).UnfoldingEquivalent
      (residual.instantiate rightArguments) := by
  have hsourceEquivalent := hsupported.2.2 leftArguments rightArguments
    hleftLength hrightLength hleftClosed hrightClosed harguments
  have hschemaClosed := referenceClosed_of_wellFormed hsupported.1
  have hleftSourceClosed := instantiate_referenceClosed
    hschemaClosed hleftClosed
  have hrightSourceClosed := instantiate_referenceClosed
    hschemaClosed hrightClosed
  obtain ⟨leftConcrete, hleftConcreteRun,
      hleftResidualConcrete⟩ :=
    g.runActions?_instantiate hg word hsupported.1 hleftClosed hrun
  obtain ⟨rightConcrete, hrightConcreteRun,
      hrightResidualConcrete⟩ :=
    g.runActions?_instantiate hg word hsupported.1 hrightClosed hrun
  obtain ⟨transportedLeft, htransportedLeftRun,
      htransportedTargets⟩ :=
    EncodedFirstOrderGrammar.exists_runActions_of_unfoldingEquivalent
      hg hsourceEquivalent hleftSourceClosed hrightSourceClosed
        hrightConcreteRun
  have htargetsEqual : transportedLeft = leftConcrete := by
    apply Option.some.inj
    exact htransportedLeftRun.symm.trans hleftConcreteRun
  subst transportedLeft
  exact hleftResidualConcrete.trans
    (htransportedTargets.trans hrightResidualConcrete.symm)

/-- Ordinary symbolic execution preserves prefix support when the common
padded arity is large enough for every grammar rule. -/
public theorem SupportedByPrefix.residual
    {Action : Type} [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema residual : RegularTerm} {arity width : ℕ}
    (hsupported : SupportedByPrefix g.ranks arity width schema)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    {word : List Action}
    (hrun : g.runActions? word schema = some residual) :
    SupportedByPrefix g.ranks arity width residual := by
  refine ⟨g.runActions?_preserves_wellFormed_padded hg hpadding word
      hsupported.1 hrun, hsupported.2.1, ?_⟩
  intro leftArguments rightArguments hleftLength hrightLength
    hleftClosed hrightClosed harguments
  exact hsupported.residual_instances_unfoldingEquivalent hg hrun
    hleftLength hrightLength hleftClosed hrightClosed harguments

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private theorem identity_freshened_agree_through
    {arity width x : ℕ} (hx : x < arity)
    (hinactive : width ≤ x) :
    RegularTerm.ArgumentsEquivalentThrough width
      (RegularTerm.identityArguments arity)
      (RegularTerm.freshenedIdentityArguments arity x) := by
  intro i hi
  have hiArity : i < arity := by omega
  have hix : i ≠ x := by omega
  refine ⟨RegularTerm.variableTerm i, RegularTerm.variableTerm i,
    RegularTerm.identityArguments_getElem? hiArity,
    RegularTerm.freshenedIdentityArguments_getElem?_ne hiArity hix,
    RegularTerm.unfoldingEquivalent_refl _⟩

private theorem variableTerms_not_unfoldingEquivalent
    {x y : ℕ} (hxy : x ≠ y) :
    ¬(RegularTerm.variableTerm x).UnfoldingEquivalent
      (RegularTerm.variableTerm y) := by
  intro hequivalent
  have hroot := rootNode?_variable_of_unfoldingEquivalent
    hequivalent (RegularTerm.variableTerm_rootNode? x)
  rw [RegularTerm.variableTerm_rootNode? y] at hroot
  exact hxy (by simpa using hroot.symm)

/-- Once the exposed variable is known to lie below the schema arity,
prefix-support alone forces it into the semantically active prefix.  This
form separates the support argument from the way arity membership is proved;
in particular marker arguments establish the latter using groundness in the
marker extension rather than in the original grammar. -/
public theorem ExposedEquation.variableIndex_lt_width_of_lt
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity width : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : RegularTerm.SupportedByPrefix g.ranks arity width left)
    (hright : RegularTerm.SupportedByPrefix g.ranks arity width right)
    (equation : ExposedEquation g left right arguments)
    (hxArity : equation.variableIndex < arity) :
    equation.variableIndex < width := by
  by_contra hxWidth
  have hinactive : width ≤ equation.variableIndex :=
    Nat.le_of_not_gt hxWidth
  have hidentityClosed :=
    RegularTerm.identityArguments_referenceClosed arity
  have hfreshClosed :=
    RegularTerm.freshenedIdentityArguments_referenceClosed hxArity
  have hagree := identity_freshened_agree_through hxArity hinactive
  rcases equation.orientation with hleftOrientation | hrightOrientation
  · have hresiduals :=
      hleft.residual_instances_unfoldingEquivalent hg
        equation.left_run
        (RegularTerm.identityArguments_length arity)
        (RegularTerm.freshenedIdentityArguments_length arity
          equation.variableIndex)
        hidentityClosed hfreshClosed hagree
    have hroot : equation.leftResidual.nodeAt?
        equation.leftResidual.root =
          some (.inl equation.variableIndex) := by
      simpa [RegularTerm.rootNode?] using hleftOrientation.1
    have hidentityArgument :=
      RegularTerm.instantiate_unfoldingEquivalent_argument hroot
        (RegularTerm.identityArguments_getElem? hxArity)
        (RegularTerm.variableTerm_referenceClosed equation.variableIndex)
    have hfreshArgument :=
      RegularTerm.instantiate_unfoldingEquivalent_argument hroot
        (RegularTerm.freshenedIdentityArguments_getElem?_eq hxArity)
        (RegularTerm.variableTerm_referenceClosed arity)
    exact variableTerms_not_unfoldingEquivalent (by omega)
      (hidentityArgument.symm.trans (hresiduals.trans hfreshArgument))

  · have hresiduals :=
      hright.residual_instances_unfoldingEquivalent hg
        equation.right_run
        (RegularTerm.identityArguments_length arity)
        (RegularTerm.freshenedIdentityArguments_length arity
          equation.variableIndex)
        hidentityClosed hfreshClosed hagree
    have hroot : equation.rightResidual.nodeAt?
        equation.rightResidual.root =
          some (.inl equation.variableIndex) := by
      simpa [RegularTerm.rootNode?] using hrightOrientation.1
    have hidentityArgument :=
      RegularTerm.instantiate_unfoldingEquivalent_argument hroot
        (RegularTerm.identityArguments_getElem? hxArity)
        (RegularTerm.variableTerm_referenceClosed equation.variableIndex)
    have hfreshArgument :=
      RegularTerm.instantiate_unfoldingEquivalent_argument hroot
        (RegularTerm.freshenedIdentityArguments_getElem?_eq hxArity)
        (RegularTerm.variableTerm_referenceClosed arity)
    exact variableTerms_not_unfoldingEquivalent (by omega)
      (hidentityArgument.symm.trans (hresiduals.trans hfreshArgument))

/-- An equation exposed from prefix-supported schemas necessarily selects one
of the semantically active arguments. -/
public theorem ExposedEquation.variableIndex_lt_width
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity width : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : RegularTerm.SupportedByPrefix g.ranks arity width left)
    (hright : RegularTerm.SupportedByPrefix g.ranks arity width right)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (equation : ExposedEquation g left right arguments) :
    equation.variableIndex < width := by
  apply equation.variableIndex_lt_width_of_lt g hg hleft hright
  exact equation.variableIndex_lt g hg hleft.1 hright.1
    hargumentsLength hargumentsGround

/-- All data produced by exposing an inequivalent active schema pair, bundled
with the concrete certificate targets reached from the represented ground
pair.  The exposed variable is guaranteed to lie in the active prefix. -/
public structure ActiveExposedCertificate
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (width : ℕ)
    {stem : List (Label Action)}
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width stem)
    where
  equation : ExposedEquation g coverage.schema.left
    coverage.schema.right coverage.arguments
  variableIndex_lt_width : equation.variableIndex < width
  targets : ExposedCertificateTargets g initialLeft initialRight width
    coverage equation
  argument : RegularTerm
  argument_at : coverage.arguments[equation.variableIndex]? = some argument
  orientation :
    ((equation.leftResidual.rootNode? =
          some (.inl equation.variableIndex) ∧
        targets.leftTarget.UnfoldingEquivalent argument ∧
        ¬ equation.rightResidual.UnfoldingEquivalent
          equation.leftResidual) ∨
      (equation.rightResidual.rootNode? =
          some (.inl equation.variableIndex) ∧
        targets.rightTarget.UnfoldingEquivalent argument ∧
        ¬ equation.leftResidual.UnfoldingEquivalent
          equation.rightResidual))

/-- If the open schemas of an active presentation are inequivalent, expose an
actual active argument and replay the exposing word in the certificate
calculus. -/
public theorem ActiveSchemaCoverage.exists_activeExposedCertificate
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {width : ℕ}
    {stem : List (Label Action)}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width stem)
    (hinequivalent :
      ¬ g.TraceEquivalent coverage.schema.left coverage.schema.right) :
    Nonempty (ActiveExposedCertificate g initialLeft initialRight width
      coverage) := by
  have hinstanceEquivalent :=
    coverage.instantiated_traceEquivalent laws hinitialEquivalent
  obtain ⟨equation⟩ := exists_exposedEquation_of_not_traceEquivalent
    g hg coverage.left_supported.1 coverage.right_supported.1
      coverage.argument_count coverage.arguments_areGround
        hinstanceEquivalent hinequivalent
  have hactive := equation.variableIndex_lt_width g hg
    coverage.left_supported coverage.right_supported
      coverage.argument_count coverage.arguments_areGround
  obtain ⟨targets⟩ := coverage.exposedCertificateTargets hg laws
    hgroundSteps hinitialEquivalent equation
  have hvariable : equation.variableIndex < coverage.arguments.length := by
    rw [coverage.argument_count]
    exact hactive.trans_le coverage.left_supported.2.1
  obtain ⟨argument, hargument, horientation⟩ :=
    targets.orientation_with_argument hvariable
  exact ⟨
    { equation := equation
      variableIndex_lt_width := hactive
      targets := targets
      argument := argument
      argument_at := hargument
      orientation := horientation }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
