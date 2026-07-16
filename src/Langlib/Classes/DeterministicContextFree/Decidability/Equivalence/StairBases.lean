module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GrammarNormalForm
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalBasisSoundness

@[expose]
public section

/-!
# Stair bases and the width-zero completeness step

This is the semantic interface used in Propositions 39--40 of Jančar's
arXiv:1010.4760v4.  A stair sequence repeatedly presents derived residuals by
bounded finite heads over one fixed tuple of ground tails.  The heads need not
be sound.  Width zero is special: there are no tails, so equivalence of the
single represented residual makes the closed head pair a sound basis row.

The theorem `sufficientBound_of_stairBase_zero` is the first genuine
grammar-global completeness theorem: one bound works for every equivalent
ground initial pair.  The later balancing argument constructs a stair base of
finite width, and tail elimination reduces that width to zero.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A derived pair represented by a finite schema over a fixed tuple of ground
tails.  Unlike `SoundMatch`, this carries no semantic soundness premise. -/
public structure OpenSchemaCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (arguments : List RegularTerm)
    (word : List (Label Action)) where
  schema : BasisPair
  left : RegularTerm
  right : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight []
    (.pair word left right)
  word_nonempty : word ≠ []
  schema_wellFormed : g.basisPairWellFormedCode schema = true
  argument_count : arguments.length = schema.arity
  arguments_ground : g.groundArgumentsCode arguments = true
  left_matches : RegularTerm.unfoldingEquivalentCode left
    (schema.left.instantiate arguments) = true
  right_matches : RegularTerm.unfoldingEquivalentCode right
    (schema.right.instantiate arguments) = true

/-- A bounded open-schema presentation. -/
public structure BoundedOpenSchemaCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound : ℕ)
    (arguments : List RegularTerm)
    (word : List (Label Action))
    extends OpenSchemaCoverage g initialLeft initialRight arguments word where
  arity_le : schema.arity ≤ bound
  left_size_le : schema.left.nodes.length ≤ bound
  right_size_le : schema.right.nodes.length ≤ bound

/-- A path reaches a bounded sound basis instance. -/
@[expose] public def EventuallyBoundedSound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound : ℕ)
    (path : TracePath g initialLeft initialRight) : Prop :=
  ∃ n, Nonempty (BoundedSoundCoverage g initialLeft initialRight
    bound (path.word n))

/-- The unbounded alternative in a stair base.  All presentations use the
same `width` ground tails; their finite heads have the grammar-dependent bound
`growth j` at the `j`th selected prefix. -/
public structure StairSequence
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (width : ℕ) (growth : ℕ → ℕ)
    (path : TracePath g initialLeft initialRight) where
  arguments : List RegularTerm
  argument_width : arguments.length = width
  arguments_ground : g.groundArgumentsCode arguments = true
  levels : ℕ → ℕ
  levels_strictMono : StrictMono levels
  covered : ∀ j, Nonempty
    (BoundedOpenSchemaCoverage g initialLeft initialRight (growth j)
      arguments (path.word (levels j)))

/-- A grammar has a stair base of width `width` when one growth function works
for every equivalent ground pair and every infinite common trace. -/
@[expose] public def HasStairBase
    (g : EncodedFirstOrderGrammar Action) (width : ℕ) : Prop :=
  ∃ growth : ℕ → ℕ,
    ∀ initialLeft initialRight,
      g.groundPairCode initialLeft initialRight = true →
      g.TraceEquivalent initialLeft initialRight →
      ∀ path : TracePath g initialLeft initialRight,
        g.EventuallyBoundedSound initialLeft initialRight (growth 0) path ∨
        Nonempty (StairSequence g initialLeft initialRight width growth path)

/-- One presentation bound whose bounded sound basis proves every equivalent
ground query. -/
@[expose] public def SufficientBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  ∀ initialLeft initialRight,
    g.groundPairCode initialLeft initialRight = true →
    g.TraceEquivalent initialLeft initialRight →
    CertificateDerivable g initialLeft initialRight
      (g.boundedSoundBasis bound) (.nop [])

omit [DecidableEq Action] in
private theorem referenceClosed_of_groundArgumentsCode
    (g : EncodedFirstOrderGrammar Action) {arguments : List RegularTerm}
    (harguments : g.groundArgumentsCode arguments = true) :
    ∀ argument ∈ arguments, argument.ReferenceClosed := by
  unfold groundArgumentsCode at harguments
  have hall := List.all_eq_true.mp harguments
  intro argument hargument
  exact RegularTerm.referenceClosed_of_ground
    ((RegularTerm.groundCode_eq_true_iff g.ranks argument).mp
      (hall argument hargument))

/-- A width-zero open presentation of a residual of an equivalent pair is a
sound basis match. -/
public def OpenSchemaCoverage.soundCoverage_of_noArguments
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    {word : List (Label Action)}
    (coverage : OpenSchemaCoverage g initialLeft initialRight [] word) :
    SoundCoverage g initialLeft initialRight word := by
  have hresidualEquivalent : g.TraceEquivalent coverage.left coverage.right :=
    coverage.derivation.pair_traceEquivalent_of_initial laws hinitialEquivalent
  have hground := groundPairCode_of_pair_derivable coverage.derivation
  unfold groundPairCode at hground
  rw [Bool.and_eq_true] at hground
  have hleftClosed : coverage.left.ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground
      ((RegularTerm.groundCode_eq_true_iff g.ranks coverage.left).mp hground.1)
  have hrightClosed : coverage.right.ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground
      ((RegularTerm.groundCode_eq_true_iff g.ranks coverage.right).mp hground.2)
  have hschemaWellFormed := coverage.schema_wellFormed
  unfold basisPairWellFormedCode at hschemaWellFormed
  rw [Bool.and_eq_true] at hschemaWellFormed
  have hschemaLeftClosed := RegularTerm.referenceClosed_of_wellFormed
    hschemaWellFormed.1
  have hschemaRightClosed := RegularTerm.referenceClosed_of_wellFormed
    hschemaWellFormed.2
  have hleftInstanceClosed :
      (coverage.schema.left.instantiate []).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed hschemaLeftClosed (by simp)
  have hrightInstanceClosed :
      (coverage.schema.right.instantiate []).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed hschemaRightClosed (by simp)
  have hleftSemantic : g.TraceEquivalent coverage.left
      (coverage.schema.left.instantiate []) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode hleftClosed
      hleftInstanceClosed coverage.left_matches
  have hrightSemantic : g.TraceEquivalent coverage.right
      (coverage.schema.right.instantiate []) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode hrightClosed
      hrightInstanceClosed coverage.right_matches
  have hschemaEquivalent : g.TraceEquivalent
      (coverage.schema.left.instantiate [])
      (coverage.schema.right.instantiate []) :=
    hleftSemantic.symm.trans (hresidualEquivalent.trans hrightSemantic)
  have hsound : g.SoundBasisPair coverage.schema := by
    refine ⟨?_, ?_⟩
    · exact coverage.schema_wellFormed
    · intro arguments hlength _hground
      have hzero : arguments.length = 0 :=
        hlength.trans coverage.argument_count.symm
      have : arguments = [] := List.length_eq_zero_iff.mp hzero
      subst arguments
      exact hschemaEquivalent
  exact
    { left := coverage.left
      right := coverage.right
      derivation := coverage.derivation
      match_data :=
        { schema := coverage.schema
          arguments := []
          word_nonempty := coverage.word_nonempty
          sound := hsound
          argument_count := coverage.argument_count
          arguments_ground := coverage.arguments_ground
          left_matches := coverage.left_matches
          right_matches := coverage.right_matches } }

/-- The width-zero case of the stair argument.  The first stair head has no
tails, hence is itself sound. -/
public theorem everyDerivationPathCovered_of_stairBase_zero
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {growth : ℕ → ℕ}
    (hstair :
      ∀ initialLeft initialRight,
        g.groundPairCode initialLeft initialRight = true →
        g.TraceEquivalent initialLeft initialRight →
        ∀ path : TracePath g initialLeft initialRight,
          g.EventuallyBoundedSound initialLeft initialRight (growth 0) path ∨
          Nonempty (StairSequence g initialLeft initialRight 0 growth path))
    {initialLeft initialRight : RegularTerm}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hequivalent : g.TraceEquivalent initialLeft initialRight) :
    g.EveryDerivationPathCovered initialLeft initialRight (growth 0) := by
  intro path
  rcases hstair initialLeft initialRight hground hequivalent path with
    hbounded | hsequence
  · exact hbounded
  · obtain ⟨sequence⟩ := hsequence
    obtain ⟨coverage⟩ := sequence.covered 0
    have harguments : sequence.arguments = [] :=
      List.length_eq_zero_iff.mp sequence.argument_width
    have coverage' : BoundedOpenSchemaCoverage g initialLeft initialRight
        (growth 0) [] (path.word (sequence.levels 0)) := by
      simpa [harguments] using coverage
    let soundCoverage :=
      coverage'.toOpenSchemaCoverage.soundCoverage_of_noArguments
        laws hequivalent
    refine ⟨sequence.levels 0, ⟨?_⟩⟩
    exact
      { left := soundCoverage.left
        right := soundCoverage.right
        derivation := soundCoverage.derivation.rebasePair
        match_data :=
          { schema := soundCoverage.match_data.schema
            arguments := soundCoverage.match_data.arguments
            word_nonempty := soundCoverage.match_data.word_nonempty
            sound := soundCoverage.match_data.sound
            arity_le := coverage'.arity_le
            left_size_le := coverage'.left_size_le
            right_size_le := coverage'.right_size_le
            argument_count := soundCoverage.match_data.argument_count
            arguments_ground := soundCoverage.match_data.arguments_ground
            left_matches := soundCoverage.match_data.left_matches
            right_matches := soundCoverage.match_data.right_matches } }

/-- A width-zero stair base yields one grammar-global sufficient presentation
bound. -/
public theorem sufficientBound_of_stairBase_zero
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    (hstair : g.HasStairBase 0) :
    ∃ bound, g.SufficientBound bound := by
  obtain ⟨growth, hstair⟩ := hstair
  refine ⟨growth 0, ?_⟩
  intro initialLeft initialRight hground hequivalent
  apply g.derivable_nop_of_everyDerivationPathCovered laws hgroundSteps
    hground hequivalent
  exact everyDerivationPathCovered_of_stairBase_zero laws hstair
    hground hequivalent

end EncodedFirstOrderGrammar

end DCFEquivalence
