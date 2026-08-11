module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveExposure

@[expose]
public section

/-!
# Uniform bounds for exposed equations

Width reduction chooses an exposed equation at the first level of a regular
stair.  Although the ground argument tuple varies with the path, the open
schema pair comes from a fixed finite bounded enumeration.  We choose one
shortest distinguishing word per inequivalent bounded pair and take the
maximum of the argument-independent residual bound along those words.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One fixed shortest distinguishing word for an inequivalent schema pair.
The value on an equivalent pair is irrelevant. -/
noncomputable def chosenOffendingWord
    (g : EncodedFirstOrderGrammar Action) (pair : BasisPair) :
    List (Label Action) := by
  classical
  by_cases hinequivalent :
      ¬g.TraceEquivalent pair.left pair.right
  · exact Classical.choose
      (g.exists_offendingWord_of_not_traceEquivalent hinequivalent)
  · exact []

public theorem chosenOffendingWord_spec
    (g : EncodedFirstOrderGrammar Action) {pair : BasisPair}
    (hinequivalent : ¬g.TraceEquivalent pair.left pair.right) :
    g.OffendingWord pair.left pair.right
      (g.chosenOffendingWord pair) := by
  classical
  unfold chosenOffendingWord
  simp only [hinequivalent, ↓reduceDIte]
  exact Classical.choose_spec
    (g.exists_offendingWord_of_not_traceEquivalent hinequivalent)

/-- The cost bound attached to the chosen offending word of one pair. -/
noncomputable def schemaExposureBound
    (g : EncodedFirstOrderGrammar Action) (pair : BasisPair) : ℕ :=
  g.exposedEquationBound pair.left pair.right
    (g.chosenOffendingWord pair)

/-- A single exposure bound for every schema pair of presentation size at
most `bound`. -/
noncomputable def boundedExposureBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  ((g.basisPairsUpTo bound).map g.schemaExposureBound).foldr max 0

public theorem schemaExposureBound_le_boundedExposureBound
    (g : EncodedFirstOrderGrammar Action) {bound : ℕ}
    {pair : BasisPair} (hpair : pair ∈ g.basisPairsUpTo bound) :
    g.schemaExposureBound pair ≤ g.boundedExposureBound bound := by
  apply List.le_max_of_le
  · exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
  · exact le_rfl

/-- A bounded active coverage whose schemas are inequivalent has an exposed
certificate with cost bounded solely by its numerical presentation bound. -/
public theorem BoundedActiveSchemaCoverage.exists_boundedActiveExposedCertificate
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {stem : List (Label Action)}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (bounded : BoundedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments stem)
    (hinequivalent : ¬g.TraceEquivalent
      bounded.coverage.schema.left bounded.coverage.schema.right) :
    ∃ exposed : ActiveExposedCertificate g initialLeft initialRight width
        bounded.coverage,
      exposed.equation.presentationCost ≤
        g.boundedExposureBound bound := by
  let coverage := bounded.coverage
  have hpair : coverage.schema ∈ g.basisPairsUpTo bound := by
    apply (g.mem_basisPairsUpTo_iff bound coverage.schema).mpr
    exact ⟨bounded.arity_le, bounded.left_size_le,
      bounded.right_size_le, coverage.schema_wellFormed⟩
  have hoffending := g.chosenOffendingWord_spec hinequivalent
  obtain ⟨equation, hequationBound⟩ :=
    g.exists_boundedExposedEquation_of_offending hg
      coverage.left_supported.1 coverage.right_supported.1
      coverage.argument_count coverage.arguments_areGround
      (coverage.instantiated_traceEquivalent laws hinitialEquivalent)
      (g.chosenOffendingWord coverage.schema) hoffending
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
  refine ⟨
    { equation := equation
      variableIndex_lt_width := hactive
      targets := targets
      argument := argument
      argument_at := hargument
      orientation := horientation }, ?_⟩
  exact hequationBound.trans
    (g.schemaExposureBound_le_boundedExposureBound hpair)

end EncodedFirstOrderGrammar

end DCFEquivalence
