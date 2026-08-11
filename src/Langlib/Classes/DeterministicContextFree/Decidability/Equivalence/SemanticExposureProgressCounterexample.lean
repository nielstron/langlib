module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinking
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationSupport

@[expose]
public section

/-!
# Semantic exposure does not imply progress-making exposure

`ExposesBy` intentionally identifies a reached term with any semantically
equal occurrence in the source unfolding.  On a cyclic regular term, the
empty word can therefore expose arbitrarily large depths.  In contrast,
`RepeatedlySinksBy` consumes a nonempty word at every positive depth.

This file records the small counterexample independently of the structured
pivot construction.
-/

namespace DCFEquivalence

namespace SemanticExposureProgressCounterexample

/-- The regular infinite unary term `X(X(X(...)))`. -/
@[expose] public def unaryCycle : RegularTerm :=
  ([.inr (0, [0])], 0)

/-- The unique graph node occurs at every unfolding depth. -/
public theorem unaryCycle_descendantAt (depth : ℕ) :
    unaryCycle.DescendantAt depth 0 := by
  induction depth with
  | zero =>
      exact .root
  | succ depth ih =>
      simpa [unaryCycle, Nat.succ_eq_add_one] using
        (RegularTerm.DescendantAt.child ih (by rfl) (by simp))

/-- Consequently, the cycle is its own subterm at every depth. -/
public theorem unaryCycle_subtermAtDepth (depth : ℕ) :
    unaryCycle.SubtermAtDepth depth unaryCycle := by
  exact ⟨0, unaryCycle_descendantAt depth, rfl⟩

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A one-symbol normal-form grammar whose sole action projects the sole
argument. -/
@[expose] public def projectionGrammar :
    EncodedFirstOrderGrammar Unit :=
  ([1], [(0, (), RegularTerm.variableTerm 0)])

public theorem projectionGrammar_wellFormed :
    projectionGrammar.WellFormed := by
  rfl

public theorem unaryCycle_ground :
    unaryCycle.Ground projectionGrammar.ranks := by
  refine ⟨by rfl, [0],
    by simp [unaryCycle, RegularTerm.nodes], ?_⟩
  constructor
  · simp [unaryCycle, RegularTerm.root]
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact ⟨0, [0], rfl, by simp⟩

public theorem projectionGrammar_exposingNormalForm :
    projectionGrammar.ExposingNormalForm := by
  rintro ⟨⟨X, hX⟩, ⟨i, hi⟩⟩
  have hXzero : X = 0 := by
    simpa [projectionGrammar,
      EncodedFirstOrderGrammar.ranks] using hX
  subst X
  have hizero : i = 0 := by
    simpa [projectionGrammar,
      EncodedFirstOrderGrammar.ranks] using hi
  subst i
  refine ⟨[()], ?_⟩
  let argument :=
    (RegularTerm.symbolTemplate 0 1).withRoot 1
  let target :=
    (RegularTerm.variableTerm 0).instantiate [argument]
  refine ⟨target, ?_, ?_⟩
  · rfl
  · have htargetArgument :
        target.UnfoldingEquivalent argument := by
      apply RegularTerm.instantiate_unfoldingEquivalent_argument
      · rfl
      · simp [argument]
      · exact RegularTerm.withRoot_referenceClosed
          (RegularTerm.symbolTemplate_referenceClosed 0 1)
          (by simp [RegularTerm.symbolTemplate, RegularTerm.nodes])
    have hargumentRoot :
        argument.rootNode? = some (.inl 0) := by
      rfl
    exact htargetArgument.trans
      (RegularTerm.unfoldingEquivalent_variableTerm_of_rootNode
        hargumentRoot)

/-- For every grammar, the empty computation semantically exposes every depth
of the unary cycle. -/
public theorem unaryCycle_exposesBy_nil
    (g : EncodedFirstOrderGrammar Action) (depth : ℕ) :
    g.ExposesBy unaryCycle [] depth := by
  apply g.exposesBy_of_exposesAtDepth
  exact ⟨unaryCycle, unaryCycle,
    unaryCycle_subtermAtDepth depth, by simp,
    RegularTerm.unfoldingEquivalent_refl unaryCycle⟩

/-- No positive repeated-sinking depth can be witnessed by the empty word. -/
public theorem unaryCycle_not_repeatedlySinksBy_nil
    (g : EncodedFirstOrderGrammar Action) (depth : ℕ) (hdepth : 0 < depth) :
    ¬g.RepeatedlySinksBy unaryCycle [] depth := by
  intro hsinks
  have := hsinks.depth_le_length
  simp at this
  omega

/-- The direct semantic-to-progress implication already fails at depth one,
even if the progress witness may choose an arbitrarily larger depth. -/
public theorem not_semanticExposureHasProgressWitness_nil
    (g : EncodedFirstOrderGrammar Action) :
    ¬(∀ depth,
        g.ExposesBy unaryCycle [] depth →
          ∃ progressDepth,
            depth ≤ progressDepth ∧
              g.RepeatedlySinksBy unaryCycle [] progressDepth) := by
  intro hreflection
  obtain ⟨progressDepth, hdepth, hsinks⟩ :=
    hreflection 1 (unaryCycle_exposesBy_nil g 1)
  exact unaryCycle_not_repeatedlySinksBy_nil g progressDepth
    (by omega) hsinks

/-- Well-formedness, groundness, and exposing normal form do not repair the
gap.  Even allowing the witness to choose a later index fails for the constant
empty-word family. -/
public theorem exposingNormalForm_does_not_force_progressReflection :
    projectionGrammar.WellFormed ∧
      projectionGrammar.ExposingNormalForm ∧
      unaryCycle.Ground projectionGrammar.ranks ∧
      ¬(∀ depth,
          projectionGrammar.ExposesBy unaryCycle [] depth →
            ∃ progressCount progressDepth,
              depth ≤ progressDepth ∧
                projectionGrammar.RepeatedlySinksBy unaryCycle
                  ((fun _ : ℕ => []) progressCount) progressDepth) := by
  refine ⟨projectionGrammar_wellFormed,
    projectionGrammar_exposingNormalForm, unaryCycle_ground, ?_⟩
  intro hreflection
  obtain ⟨_progressCount, progressDepth, hdepth, hsinks⟩ :=
    hreflection 1
      (unaryCycle_exposesBy_nil projectionGrammar 1)
  exact unaryCycle_not_repeatedlySinksBy_nil
    projectionGrammar progressDepth (by omega) hsinks

end EncodedFirstOrderGrammar

end SemanticExposureProgressCounterexample

end DCFEquivalence
