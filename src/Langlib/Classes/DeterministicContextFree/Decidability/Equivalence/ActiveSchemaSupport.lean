module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveStairBases
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.IdentitySubstitution

@[expose]
public section

/-!
# Regular schemas supported by an active argument prefix

Tail elimination ties a unary context into a cyclic regular term, so the
finite-head syntax used to construct the first stair is not closed under the
operation.  `SupportedByPrefix` is the semantic invariant needed afterwards:
the denoted instance depends only on the first `width` arguments, while the
remaining positions exist solely to make the raw graph structurally valid.

At width zero, prefix support and identity substitution show that a schema is
equivalent to every one of its ground padded instances.  Thus the corrected
open-sound width-zero argument applies to arbitrary regular schemas, including
the unary limits produced by tail elimination.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Two argument tuples agree semantically through the first `width`
positions.  The existential form avoids dependent `getElem` transports. -/
@[expose] public def ArgumentsEquivalentThrough
    (width : ℕ) (left right : List RegularTerm) : Prop :=
  ∀ i, i < width →
    ∃ leftArgument rightArgument,
      left[i]? = some leftArgument ∧
      right[i]? = some rightArgument ∧
      leftArgument.UnfoldingEquivalent rightArgument

public theorem argumentsEquivalentThrough_zero
    (left right : List RegularTerm) :
    ArgumentsEquivalentThrough 0 left right := by
  intro i hi
  omega

/-- An open regular schema is supported by the first `width` arguments when
changing only its inactive suffix cannot change the denoted regular tree. -/
@[expose] public def SupportedByPrefix
    (ranks : List ℕ) (arity width : ℕ) (schema : RegularTerm) : Prop :=
  schema.WellFormed ranks arity ∧ width ≤ arity ∧
    ∀ leftArguments rightArguments,
      leftArguments.length = arity →
      rightArguments.length = arity →
      (∀ argument ∈ leftArguments, argument.ReferenceClosed) →
      (∀ argument ∈ rightArguments, argument.ReferenceClosed) →
      ArgumentsEquivalentThrough width leftArguments rightArguments →
      (schema.instantiate leftArguments).UnfoldingEquivalent
        (schema.instantiate rightArguments)

end RegularTerm

/-- Evaluation of a finite head respects semantic agreement of every active
argument it can reach. -/
public theorem FiniteHead.evaluate_unfoldingEquivalent_of_prefix
    {head : FiniteHead} {width : ℕ}
    {leftArguments rightArguments : List RegularTerm}
    (hactive : head.VariablesBelow width)
    (hleftClosed : ∀ argument ∈ leftArguments,
      argument.ReferenceClosed)
    (hrightClosed : ∀ argument ∈ rightArguments,
      argument.ReferenceClosed)
    (harguments : RegularTerm.ArgumentsEquivalentThrough width
      leftArguments rightArguments) :
    (head.evaluate leftArguments).UnfoldingEquivalent
      (head.evaluate rightArguments) := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (∀ child ∈ heads, child.VariablesBelow width) →
      List.Forall₂ RegularTerm.UnfoldingEquivalent
        (heads.map fun child => child.evaluate leftArguments)
        (heads.map fun child => child.evaluate rightArguments)) with
  | var index =>
      have hindex : index < width := by
        simpa [FiniteHead.VariablesBelow] using hactive
      obtain ⟨leftArgument, rightArgument, hleft, hright, hequivalent⟩ :=
        harguments index hindex
      simpa [FiniteHead.evaluate, hleft, hright] using hequivalent
  | app symbol children ih =>
      have hchildren : ∀ child ∈ children,
          child.VariablesBelow width := by
        simpa [FiniteHead.VariablesBelow] using hactive
      have hequivalentChildren := ih hchildren
      have hresult := RegularTerm.instantiate_unfoldingEquivalent
        (RegularTerm.symbolTemplate_referenceClosed symbol children.length)
        hequivalentChildren
        (by
          intro argument hargument
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
          exact FiniteHead.evaluate_referenceClosed child leftArguments
            hleftClosed)
        (by
          intro argument hargument
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
          exact FiniteHead.evaluate_referenceClosed child rightArguments
            hrightClosed)
      simpa [FiniteHead.evaluate] using hresult
  | nil => exact .nil
  | cons child children ihChild ihChildren hactiveChildren =>
      apply List.Forall₂.cons
      · exact ihChild (hactiveChildren child (by simp))
      · exact ihChildren fun item hitem =>
          hactiveChildren item (by simp [hitem])

/-- A finite head whose variables lie below `width` gives a regular schema
supported by that active prefix. -/
public theorem FiniteHead.toRegularTerm_supportedByPrefix
    {head : FiniteHead} {ranks : List ℕ} {width : ℕ}
    (hactive : head.VariablesBelow width)
    (hranked : head.RankedBy ranks) :
    RegularTerm.SupportedByPrefix ranks
      (max width (ranks.foldr max 0)) width head.toRegularTerm := by
  refine ⟨?_, Nat.le_max_left _ _, ?_⟩
  · apply (FiniteHead.toRegularTerm_wellFormed hranked).mono
    exact FiniteHead.retainedVariableBound_le hactive hranked
  · intro leftArguments rightArguments hleftLength hrightLength
      hleftClosed hrightClosed harguments
    have hactiveLeft : head.VariablesBelow leftArguments.length := by
      apply hactive.mono
      rw [hleftLength]
      exact Nat.le_max_left _ _
    have hactiveRight : head.VariablesBelow rightArguments.length := by
      apply hactive.mono
      rw [hrightLength]
      exact Nat.le_max_left _ _
    have hleftCompile :=
      FiniteHead.toRegularTerm_instantiate_unfoldingEquivalent_evaluate
        head leftArguments hactiveLeft hranked hleftClosed
    have hrightCompile :=
      FiniteHead.toRegularTerm_instantiate_unfoldingEquivalent_evaluate
        head rightArguments hactiveRight hranked hrightClosed
    exact hleftCompile.trans
      ((FiniteHead.evaluate_unfoldingEquivalent_of_prefix
        hactive hleftClosed hrightClosed harguments).trans
          hrightCompile.symm)

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A derived pair represented by arbitrary regular schemas whose unfoldings
depend only on an active prefix of their padded argument tuple. -/
public structure ActiveSchemaCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (width : ℕ)
    (word : List (Label Action)) where
  left : RegularTerm
  right : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight []
    (.pair word left right)
  schema : BasisPair
  arguments : List RegularTerm
  word_nonempty : word ≠ []
  schema_wellFormed : g.basisPairWellFormedCode schema = true
  rank_padding : g.ranks.foldr max 0 ≤ schema.arity
  left_supported : RegularTerm.SupportedByPrefix g.ranks
    schema.arity width schema.left
  right_supported : RegularTerm.SupportedByPrefix g.ranks
    schema.arity width schema.right
  argument_count : arguments.length = schema.arity
  arguments_ground : g.groundArgumentsCode arguments = true
  left_matches : RegularTerm.unfoldingEquivalentCode left
    (schema.left.instantiate arguments) = true
  right_matches : RegularTerm.unfoldingEquivalentCode right
    (schema.right.instantiate arguments) = true

namespace ActiveSchemaCoverage

public theorem arguments_referenceClosed
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width word}
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width word) :
    ∀ argument ∈ coverage.arguments, argument.ReferenceClosed := by
  have harguments := coverage.arguments_ground
  unfold groundArgumentsCode at harguments
  have hall := List.all_eq_true.mp harguments
  intro argument hargument
  exact RegularTerm.referenceClosed_of_ground
    ((RegularTerm.groundCode_eq_true_iff g.ranks argument).mp
      (hall argument hargument))

/-- The executable ground-argument side condition exposes the corresponding
propositional fact for every actual argument. -/
public theorem arguments_areGround
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width word}
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width word) :
    ∀ argument ∈ coverage.arguments, argument.Ground g.ranks := by
  have harguments := coverage.arguments_ground
  unfold groundArgumentsCode at harguments
  have hall := List.all_eq_true.mp harguments
  intro argument hargument
  exact (RegularTerm.groundCode_eq_true_iff g.ranks argument).mp
    (hall argument hargument)

/-- The common ground instance carried by an active-schema coverage is
trace-equivalent whenever the initial query is. -/
public theorem instantiated_traceEquivalent
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm} {width word}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width word) :
    g.TraceEquivalent
      (coverage.schema.left.instantiate coverage.arguments)
      (coverage.schema.right.instantiate coverage.arguments) := by
  have hresidualEquivalent : g.TraceEquivalent coverage.left coverage.right :=
    coverage.derivation.pair_traceEquivalent_of_initial laws hinitialEquivalent
  have hground := groundPairCode_of_pair_derivable coverage.derivation
  unfold groundPairCode at hground
  rw [Bool.and_eq_true] at hground
  have hleftGround :=
    (RegularTerm.groundCode_eq_true_iff g.ranks coverage.left).mp hground.1
  have hrightGround :=
    (RegularTerm.groundCode_eq_true_iff g.ranks coverage.right).mp hground.2
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
  have hleftResidualInstance : g.TraceEquivalent coverage.left
      (coverage.schema.left.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode
      (RegularTerm.referenceClosed_of_ground hleftGround)
      hleftInstanceClosed coverage.left_matches
  have hrightResidualInstance : g.TraceEquivalent coverage.right
      (coverage.schema.right.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode
      (RegularTerm.referenceClosed_of_ground hrightGround)
      hrightInstanceClosed coverage.right_matches
  exact hleftResidualInstance.symm.trans
    (hresidualEquivalent.trans hrightResidualInstance)

/-- At active width zero, each open schema is equivalent to its actual padded
ground instance. -/
public theorem schema_unfoldingEquivalent_instance_of_width_zero
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {word}
    (coverage : ActiveSchemaCoverage g initialLeft initialRight 0 word)
    (schema : RegularTerm)
    (hsupported : RegularTerm.SupportedByPrefix g.ranks
      coverage.schema.arity 0 schema) :
    schema.UnfoldingEquivalent
      (schema.instantiate coverage.arguments) := by
  have hidentityClosed :=
    RegularTerm.identityArguments_referenceClosed coverage.schema.arity
  have hactualIdentity := hsupported.2.2
    coverage.arguments (RegularTerm.identityArguments coverage.schema.arity)
    coverage.argument_count
    (RegularTerm.identityArguments_length coverage.schema.arity)
    (arguments_referenceClosed coverage) hidentityClosed
    (RegularTerm.argumentsEquivalentThrough_zero _ _)
  have hidentity := RegularTerm.instantiate_identity_unfoldingEquivalent
    hsupported.1
  exact (hactualIdentity.trans hidentity).symm

/-- A zero-width regular active presentation is an open-sound basis row. -/
public theorem openSoundPair_of_width_zero
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm} {word}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (coverage : ActiveSchemaCoverage g initialLeft initialRight 0 word) :
    g.OpenSoundBasisPair coverage.schema := by
  refine ⟨coverage.schema_wellFormed, ?_⟩
  have hresidualEquivalent : g.TraceEquivalent coverage.left coverage.right :=
    coverage.derivation.pair_traceEquivalent_of_initial laws hinitialEquivalent
  have hground := groundPairCode_of_pair_derivable coverage.derivation
  unfold groundPairCode at hground
  rw [Bool.and_eq_true] at hground
  have hleftGround :=
    (RegularTerm.groundCode_eq_true_iff g.ranks coverage.left).mp hground.1
  have hrightGround :=
    (RegularTerm.groundCode_eq_true_iff g.ranks coverage.right).mp hground.2
  have hschemaWellFormed := coverage.schema_wellFormed
  unfold basisPairWellFormedCode at hschemaWellFormed
  rw [Bool.and_eq_true] at hschemaWellFormed
  have hleftSchemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschemaWellFormed.1
  have hrightSchemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschemaWellFormed.2
  have hargumentsClosed := arguments_referenceClosed coverage
  have hleftInstanceClosed := RegularTerm.instantiate_referenceClosed
    hleftSchemaClosed hargumentsClosed
  have hrightInstanceClosed := RegularTerm.instantiate_referenceClosed
    hrightSchemaClosed hargumentsClosed
  have hleftResidualInstance : g.TraceEquivalent coverage.left
      (coverage.schema.left.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode
      (RegularTerm.referenceClosed_of_ground hleftGround)
      hleftInstanceClosed coverage.left_matches
  have hrightResidualInstance : g.TraceEquivalent coverage.right
      (coverage.schema.right.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode
      (RegularTerm.referenceClosed_of_ground hrightGround)
      hrightInstanceClosed coverage.right_matches
  have hleftOpenUE := coverage.schema_unfoldingEquivalent_instance_of_width_zero
    coverage.schema.left coverage.left_supported
  have hrightOpenUE := coverage.schema_unfoldingEquivalent_instance_of_width_zero
    coverage.schema.right coverage.right_supported
  have hleftOpenInstance : g.TraceEquivalent coverage.schema.left
      (coverage.schema.left.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode hleftSchemaClosed
      hleftInstanceClosed
      ((RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr hleftOpenUE)
  have hrightOpenInstance : g.TraceEquivalent coverage.schema.right
      (coverage.schema.right.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode hrightSchemaClosed
      hrightInstanceClosed
      ((RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr hrightOpenUE)
  exact hleftOpenInstance.trans
    (hleftResidualInstance.symm.trans
      (hresidualEquivalent.trans
        (hrightResidualInstance.trans hrightOpenInstance.symm)))

end ActiveSchemaCoverage

/-- Every finite-head presentation supplies the stronger regular-schema
support invariant used after tail elimination. -/
public def ActiveHeadCoverage.toActiveSchemaCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight tails filler word}
    (coverage : ActiveHeadCoverage g initialLeft initialRight tails filler word) :
    ActiveSchemaCoverage g initialLeft initialRight tails.length word :=
  { left := coverage.left
    right := coverage.right
    derivation := coverage.derivation
    schema := coverage.schema
    arguments := coverage.arguments
    word_nonempty := coverage.word_nonempty
    schema_wellFormed := coverage.schema_wellFormed
    rank_padding := Nat.le_max_right _ _
    left_supported :=
      FiniteHead.toRegularTerm_supportedByPrefix
        coverage.left_active coverage.left_ranked
    right_supported :=
      FiniteHead.toRegularTerm_supportedByPrefix
        coverage.right_active coverage.right_ranked
    argument_count := by
      exact g.activePaddedArguments_length tails filler
    arguments_ground := coverage.arguments_ground
    left_matches := coverage.left_matches
    right_matches := coverage.right_matches }

end EncodedFirstOrderGrammar

end DCFEquivalence
