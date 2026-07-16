module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CertificateRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ExposedEquations

@[expose]
public section

/-!
# Replaying exposed equations in the certificate calculus

The exposed-equation lemma executes an ordinary word on the open schemas.
An active stair, however, carries a derivation of ground residuals which are
only unfolding-equivalent to the corresponding common schema instance.  This
file transports the symbolic runs through substitution and unfolding
equivalence, then appends the resulting concrete runs to the existing
certificate derivation.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Concrete certificate targets realizing one symbolic exposed equation. -/
public structure ExposedCertificateTargets
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (width : ℕ)
    {stem : List (Label Action)}
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width stem)
    (equation : ExposedEquation g coverage.schema.left
      coverage.schema.right coverage.arguments) where
  leftTarget : RegularTerm
  rightTarget : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight []
    (.pair (stem ++ equation.word.map Sum.inl) leftTarget rightTarget)
  left_matches : leftTarget.UnfoldingEquivalent
    (equation.leftResidual.instantiate coverage.arguments)
  right_matches : rightTarget.UnfoldingEquivalent
    (equation.rightResidual.instantiate coverage.arguments)

/-- Replay an exposed open-schema equation from the actual ground pair carried
by an active-schema coverage. -/
public theorem ActiveSchemaCoverage.exposedCertificateTargets
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {width : ℕ}
    {stem : List (Label Action)}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width stem)
    (equation : ExposedEquation g coverage.schema.left
      coverage.schema.right coverage.arguments) :
    Nonempty (ExposedCertificateTargets g initialLeft initialRight width
      coverage equation) := by
  have hschemaWellFormed := coverage.schema_wellFormed
  unfold basisPairWellFormedCode at hschemaWellFormed
  rw [Bool.and_eq_true] at hschemaWellFormed
  have hleftSchemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschemaWellFormed.1
  have hrightSchemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschemaWellFormed.2
  have hargumentsClosed := coverage.arguments_referenceClosed
  have hleftInstanceClosed := RegularTerm.instantiate_referenceClosed
    hleftSchemaClosed hargumentsClosed
  have hrightInstanceClosed := RegularTerm.instantiate_referenceClosed
    hrightSchemaClosed hargumentsClosed
  have hpairGround := groundPairCode_of_pair_derivable coverage.derivation
  unfold groundPairCode at hpairGround
  rw [Bool.and_eq_true] at hpairGround
  have hleftClosed := RegularTerm.referenceClosed_of_ground
    ((RegularTerm.groundCode_eq_true_iff g.ranks coverage.left).mp
      hpairGround.1)
  have hrightClosed := RegularTerm.referenceClosed_of_ground
    ((RegularTerm.groundCode_eq_true_iff g.ranks coverage.right).mp
      hpairGround.2)
  have hleftCoverageInstance : coverage.left.UnfoldingEquivalent
      (coverage.schema.left.instantiate coverage.arguments) :=
    (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
      coverage.left_matches
  have hrightCoverageInstance : coverage.right.UnfoldingEquivalent
      (coverage.schema.right.instantiate coverage.arguments) :=
    (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
      coverage.right_matches
  obtain ⟨leftConcrete, hleftConcreteRun,
      hleftResidualConcrete⟩ :=
    g.runActions?_instantiate hg equation.word hschemaWellFormed.1
      hargumentsClosed equation.left_run
  obtain ⟨rightConcrete, hrightConcreteRun,
      hrightResidualConcrete⟩ :=
    g.runActions?_instantiate hg equation.word hschemaWellFormed.2
      hargumentsClosed equation.right_run
  obtain ⟨leftTarget, hleftTargetRun, hleftTargetConcrete⟩ :=
    exists_runActions_of_unfoldingEquivalent hg hleftCoverageInstance
      hleftClosed hleftInstanceClosed hleftConcreteRun
  obtain ⟨rightTarget, hrightTargetRun, hrightTargetConcrete⟩ :=
    exists_runActions_of_unfoldingEquivalent hg hrightCoverageInstance
      hrightClosed hrightInstanceClosed hrightConcreteRun
  have hderivation := coverage.derivation.follow_runActions_of_initial
    laws hgroundSteps hinitialEquivalent hleftTargetRun hrightTargetRun
  exact ⟨
    { leftTarget := leftTarget
      rightTarget := rightTarget
      derivation := hderivation
      left_matches := hleftTargetConcrete.trans
        hleftResidualConcrete.symm
      right_matches := hrightTargetConcrete.trans
        hrightResidualConcrete.symm }⟩

/-- Once the exposed variable is known to be an actual argument position, the
corresponding concrete target denotes precisely that ground argument. -/
public theorem ExposedCertificateTargets.orientation_with_argument
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width : ℕ}
    {stem : List (Label Action)}
    {coverage : ActiveSchemaCoverage g initialLeft initialRight width stem}
    {equation : ExposedEquation g coverage.schema.left
      coverage.schema.right coverage.arguments}
    (targets : ExposedCertificateTargets g initialLeft initialRight width
      coverage equation)
    (hvariable : equation.variableIndex < coverage.arguments.length) :
    ∃ argument,
      coverage.arguments[equation.variableIndex]? = some argument ∧
      ((equation.leftResidual.rootNode? =
            some (.inl equation.variableIndex) ∧
          targets.leftTarget.UnfoldingEquivalent argument ∧
          ¬ equation.rightResidual.UnfoldingEquivalent
            equation.leftResidual) ∨
        (equation.rightResidual.rootNode? =
            some (.inl equation.variableIndex) ∧
          targets.rightTarget.UnfoldingEquivalent argument ∧
          ¬ equation.leftResidual.UnfoldingEquivalent
            equation.rightResidual)) := by
  let argument := coverage.arguments[equation.variableIndex]
  have hargument : coverage.arguments[equation.variableIndex]? =
      some argument := List.getElem?_eq_getElem hvariable
  have hargumentClosed := coverage.arguments_referenceClosed argument
    (List.mem_of_getElem? hargument)
  refine ⟨argument, hargument, ?_⟩
  rcases equation.orientation with hleft | hright
  · left
    have hroot : equation.leftResidual.nodeAt?
        equation.leftResidual.root =
          some (.inl equation.variableIndex) := by
      simpa [RegularTerm.rootNode?] using hleft.1
    have hresidualArgument :=
      RegularTerm.instantiate_unfoldingEquivalent_argument
        hroot hargument hargumentClosed
    exact ⟨hleft.1, targets.left_matches.trans hresidualArgument,
      hleft.2⟩
  · right
    have hroot : equation.rightResidual.nodeAt?
        equation.rightResidual.root =
          some (.inl equation.variableIndex) := by
      simpa [RegularTerm.rootNode?] using hright.1
    have hresidualArgument :=
      RegularTerm.instantiate_unfoldingEquivalent_argument
        hroot hargument hargumentClosed
    exact ⟨hright.1, targets.right_matches.trans hresidualArgument,
      hright.2⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
