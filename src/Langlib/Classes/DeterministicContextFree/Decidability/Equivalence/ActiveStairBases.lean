module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BasisPathCompactness

@[expose]
public section

/-!
# Stair bases with active tails and padded schema arity

Finite-head compilation retains harmless unreachable template variables.  The
arity of a structurally well-formed compiled schema can therefore be larger
than the number of tails on which its unfolding actually depends.  This file
separates those two quantities: `tails.length` is the active width, while the
schema is padded to the maximum of that width and the greatest grammar rank.

The width-zero theorem below is the corrected form of Proposition 40.  It
shows that a presentation with no active tails is an *open*-sound basis row,
despite its padded arity.  Consequently one fixed finite basis of bounded
open-sound rows covers every path supplied by a width-zero stair base.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- With no supplied arguments, no graph reference is redirected. -/
@[simp] public theorem resolveRHSRef_nil
    (term : RegularTerm) (i : ℕ) :
    term.resolveRHSRef [] i = i := by
  unfold resolveRHSRef
  split <;> simp [argumentRoot?]

@[simp] private theorem instantiateNode_nil
    (term : RegularTerm) (node : RawNode) :
    term.instantiateNode [] node = node := by
  cases node with
  | inl x => rfl
  | inr app =>
      rcases app with ⟨symbol, children⟩
      simp only [instantiateNode]
      congr 2
      induction children with
      | nil => rfl
      | cons child children ih =>
          simp [resolveRHSRef_nil, ih]

private theorem map_instantiateNode_nil
    (term : RegularTerm) (nodes : List RawNode) :
    nodes.map (term.instantiateNode []) = nodes := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simp [instantiateNode_nil, ih]

/-- Instantiating no variables leaves a graph presentation unchanged. -/
@[simp] public theorem instantiate_nil (term : RegularTerm) :
    term.instantiate [] = term := by
  apply Prod.ext
  · change term.nodes.map (term.instantiateNode []) ++ [] = term.nodes
    simp [map_instantiateNode_nil]
  · change term.resolveRHSRef [] term.root = term.root
    exact resolveRHSRef_nil term term.root

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The common padded arity used by finite heads over `tails`. -/
@[expose] public def activeSchemaArity
    (g : EncodedFirstOrderGrammar Action) (tails : List RegularTerm) : ℕ :=
  max tails.length (g.ranks.foldr max 0)

/-- Ground arguments used to instantiate a compiled finite head.  Positions
after the active tails are structural padding and are unreachable. -/
@[expose] public def activePaddedArguments
    (g : EncodedFirstOrderGrammar Action) (tails : List RegularTerm)
    (filler : RegularTerm) : List RegularTerm :=
  tails ++ List.replicate (g.activeSchemaArity tails - tails.length) filler

@[simp] public theorem activePaddedArguments_length
    (g : EncodedFirstOrderGrammar Action) (tails : List RegularTerm)
    (filler : RegularTerm) :
    (g.activePaddedArguments tails filler).length =
      g.activeSchemaArity tails := by
  simp [activePaddedArguments, activeSchemaArity]

/-- The compiled basis row associated with two finite heads over a common
active tail tuple. -/
@[expose] public def activeHeadPair
    (g : EncodedFirstOrderGrammar Action) (tails : List RegularTerm)
    (leftHead rightHead : FiniteHead) : BasisPair :=
  (g.activeSchemaArity tails, leftHead.toRegularTerm,
    rightHead.toRegularTerm)

/-- A derived residual pair represented by bounded finite heads over a fixed
tuple of active ground tails.  Derivability is kept over the empty basis, so
the same presentation can later be rebased to the one finite basis selected
after the global bound is known. -/
public structure ActiveHeadCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (tails : List RegularTerm) (filler : RegularTerm)
    (word : List (Label Action)) where
  leftHead : FiniteHead
  rightHead : FiniteHead
  left : RegularTerm
  right : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight []
    (.pair word left right)
  word_nonempty : word ≠ []
  left_active : leftHead.VariablesBelow tails.length
  right_active : rightHead.VariablesBelow tails.length
  left_ranked : leftHead.RankedBy g.ranks
  right_ranked : rightHead.RankedBy g.ranks
  tails_ground : ∀ tail ∈ tails, tail.Ground g.ranks
  filler_ground : filler.Ground g.ranks
  left_matches : RegularTerm.unfoldingEquivalentCode left
    (leftHead.toRegularTerm.instantiate
      (g.activePaddedArguments tails filler)) = true
  right_matches : RegularTerm.unfoldingEquivalentCode right
    (rightHead.toRegularTerm.instantiate
      (g.activePaddedArguments tails filler)) = true

namespace ActiveHeadCoverage

/-- The basis schema denoted by an active finite-head presentation. -/
@[expose] public def schema
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight tails filler word}
    (coverage : ActiveHeadCoverage g initialLeft initialRight tails filler word) :
    BasisPair :=
  g.activeHeadPair tails coverage.leftHead coverage.rightHead

/-- The padded argument tuple attached to an active presentation. -/
@[expose] public def arguments
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight tails filler word}
    (_coverage : ActiveHeadCoverage g initialLeft initialRight tails filler word) :
    List RegularTerm :=
  g.activePaddedArguments tails filler

public theorem schema_wellFormed
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight tails filler word}
    (coverage : ActiveHeadCoverage g initialLeft initialRight tails filler word) :
    g.basisPairWellFormedCode coverage.schema = true := by
  unfold schema activeHeadPair basisPairWellFormedCode
  rw [Bool.and_eq_true]
  constructor
  · apply (FiniteHead.toRegularTerm_wellFormed coverage.left_ranked).mono
    exact FiniteHead.retainedVariableBound_le
      coverage.left_active coverage.left_ranked
  · apply (FiniteHead.toRegularTerm_wellFormed coverage.right_ranked).mono
    exact FiniteHead.retainedVariableBound_le
      coverage.right_active coverage.right_ranked

public theorem arguments_ground
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight tails filler word}
    (coverage : ActiveHeadCoverage g initialLeft initialRight tails filler word) :
    g.groundArgumentsCode coverage.arguments = true := by
  unfold arguments groundArgumentsCode
  apply List.all_eq_true.mpr
  intro argument hargument
  apply (RegularTerm.groundCode_eq_true_iff g.ranks argument).mpr
  simp only [activePaddedArguments, List.mem_append,
    List.mem_replicate] at hargument
  rcases hargument with htail | ⟨_count, rfl⟩
  · exact coverage.tails_ground argument htail
  · exact coverage.filler_ground

/-- With no active tails, a compiled finite head is unfolding-equivalent to
every padded instance of itself.  Padding positions are unreachable. -/
public theorem head_unfoldingEquivalent_instance_of_noActiveTails
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight filler word}
    (coverage : ActiveHeadCoverage g initialLeft initialRight [] filler word)
    (head : FiniteHead)
    (hactive : head.VariablesBelow 0)
    (hranked : head.RankedBy g.ranks) :
    head.toRegularTerm.UnfoldingEquivalent
      (head.toRegularTerm.instantiate
        (g.activePaddedArguments [] filler)) := by
  have hclosed : ∀ argument ∈ ([] : List RegularTerm),
      argument.ReferenceClosed := by simp
  have hleft := FiniteHead.toRegularTerm_instantiate_unfoldingEquivalent_evaluate
    head ([] : List RegularTerm) hactive hranked hclosed
  have hright := DepthPrefix.compiled_unfoldingEquivalent_evaluate
    (decomposition := ({ head := head, tails := [] } : DepthPrefix))
    hactive hranked (filler := filler) (by simp)
    (RegularTerm.referenceClosed_of_ground coverage.filler_ground)
  rw [RegularTerm.instantiate_nil] at hleft
  exact hleft.trans hright.symm

/-- A width-zero presentation of an equivalent residual pair is an open-sound
basis row.  This is the key point that remains true with padded arity. -/
public theorem openSoundPair_of_noActiveTails
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight filler word}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (coverage : ActiveHeadCoverage g initialLeft initialRight [] filler word) :
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
  have hargumentsGround := coverage.arguments_ground
  have hargumentsClosed : ∀ argument ∈ coverage.arguments,
      argument.ReferenceClosed := by
    unfold groundArgumentsCode at hargumentsGround
    have hall := List.all_eq_true.mp hargumentsGround
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      ((RegularTerm.groundCode_eq_true_iff g.ranks argument).mp
        (hall argument hargument))
  have hleftSchemaClosed :=
    FiniteHead.toRegularTerm_referenceClosed coverage.leftHead
  have hrightSchemaClosed :=
    FiniteHead.toRegularTerm_referenceClosed coverage.rightHead
  have hleftInstanceClosed := RegularTerm.instantiate_referenceClosed
    hleftSchemaClosed hargumentsClosed
  have hrightInstanceClosed := RegularTerm.instantiate_referenceClosed
    hrightSchemaClosed hargumentsClosed
  have hleftResidualInstance : g.TraceEquivalent coverage.left
      (coverage.leftHead.toRegularTerm.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode
      (RegularTerm.referenceClosed_of_ground hleftGround)
      hleftInstanceClosed coverage.left_matches
  have hrightResidualInstance : g.TraceEquivalent coverage.right
      (coverage.rightHead.toRegularTerm.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode
      (RegularTerm.referenceClosed_of_ground hrightGround)
      hrightInstanceClosed coverage.right_matches
  have hleftOpenInstanceUE :=
    coverage.head_unfoldingEquivalent_instance_of_noActiveTails
      coverage.leftHead coverage.left_active coverage.left_ranked
  have hrightOpenInstanceUE :=
    coverage.head_unfoldingEquivalent_instance_of_noActiveTails
      coverage.rightHead coverage.right_active coverage.right_ranked
  have hleftOpenInstance : g.TraceEquivalent coverage.leftHead.toRegularTerm
      (coverage.leftHead.toRegularTerm.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode hleftSchemaClosed
      hleftInstanceClosed
      ((RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        hleftOpenInstanceUE)
  have hrightOpenInstance : g.TraceEquivalent coverage.rightHead.toRegularTerm
      (coverage.rightHead.toRegularTerm.instantiate coverage.arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode hrightSchemaClosed
      hrightInstanceClosed
      ((RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        hrightOpenInstanceUE)
  exact hleftOpenInstance.trans
    (hleftResidualInstance.symm.trans
      (hresidualEquivalent.trans
        (hrightResidualInstance.trans hrightOpenInstance.symm)))

end ActiveHeadCoverage

/-- A uniformly bounded active finite-head presentation. -/
public structure BoundedActiveHeadCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound : ℕ)
    (tails : List RegularTerm) (filler : RegularTerm)
    (word : List (Label Action))
    extends ActiveHeadCoverage g initialLeft initialRight tails filler word where
  arity_le : toActiveHeadCoverage.schema.arity ≤ bound
  left_size_le : toActiveHeadCoverage.schema.left.nodes.length ≤ bound
  right_size_le : toActiveHeadCoverage.schema.right.nodes.length ≤ bound

/-- A derived bounded presentation whose schema is already open-sound. -/
public structure BoundedOpenSoundCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound : ℕ)
    (word : List (Label Action)) where
  left : RegularTerm
  right : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight []
    (.pair word left right)
  schema : BasisPair
  arguments : List RegularTerm
  word_nonempty : word ≠ []
  arity_le : schema.arity ≤ bound
  left_size_le : schema.left.nodes.length ≤ bound
  right_size_le : schema.right.nodes.length ≤ bound
  open_sound : g.OpenSoundBasisPair schema
  argument_count : arguments.length = schema.arity
  arguments_ground : g.groundArgumentsCode arguments = true
  left_matches : RegularTerm.unfoldingEquivalentCode left
    (schema.left.instantiate arguments) = true
  right_matches : RegularTerm.unfoldingEquivalentCode right
    (schema.right.instantiate arguments) = true

/-- A path reaches an open-sound row under the supplied bound. -/
@[expose] public def EventuallyBoundedOpenSound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound : ℕ)
    (path : TracePath g initialLeft initialRight) : Prop :=
  ∃ n, Nonempty (BoundedOpenSoundCoverage g initialLeft initialRight
    bound (path.word n))

/-- The unbounded alternative in an active stair base.  Every level uses the
same active tails and filler; only the bounded finite heads change. -/
public structure ActiveStairSequence
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (width : ℕ) (growth : ℕ → ℕ)
    (path : TracePath g initialLeft initialRight) where
  tails : List RegularTerm
  filler : RegularTerm
  active_width : tails.length = width
  levels : ℕ → ℕ
  levels_strictMono : StrictMono levels
  covered : ∀ j, Nonempty
    (BoundedActiveHeadCoverage g initialLeft initialRight (growth j)
      tails filler (path.word (levels j)))

/-- A grammar has an active stair base of width `width` when one growth
function works for every equivalent ground pair and common infinite path. -/
@[expose] public def HasActiveStairBase
    (g : EncodedFirstOrderGrammar Action) (width : ℕ) : Prop :=
  ∃ growth : ℕ → ℕ,
    ∀ initialLeft initialRight,
      g.groundPairCode initialLeft initialRight = true →
      g.TraceEquivalent initialLeft initialRight →
      ∀ path : TracePath g initialLeft initialRight,
        g.EventuallyBoundedOpenSound initialLeft initialRight
          (growth 0) path ∨
        Nonempty (ActiveStairSequence g initialLeft initialRight
          width growth path)

public def BoundedOpenSoundCoverage.toBasisCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {bound : ℕ} {word}
    (coverage : BoundedOpenSoundCoverage g initialLeft initialRight bound word) :
    BasisCoverage g initialLeft initialRight
      (g.boundedOpenSoundBasis bound) word := by
  refine
    { left := coverage.left
      right := coverage.right
      derivation := coverage.derivation.rebasePair
      schema := coverage.schema
      arguments := coverage.arguments
      word_nonempty := coverage.word_nonempty
      schema_wellFormed := coverage.open_sound.1
      argument_count := coverage.argument_count
      arguments_ground := coverage.arguments_ground
      left_matches := coverage.left_matches
      right_matches := coverage.right_matches
      schema_mem := ?_ }
  exact (g.mem_boundedOpenSoundBasis_iff bound coverage.schema).mpr
    ⟨coverage.arity_le, coverage.left_size_le, coverage.right_size_le,
      coverage.open_sound⟩

/-- The width-zero case of the active stair argument: every path reaches the
same bounded finite basis of original open-sound schemas. -/
public theorem everyPathCoveredBy_of_activeStairBase_zero
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {growth : ℕ → ℕ}
    (hstair :
      ∀ initialLeft initialRight,
        g.groundPairCode initialLeft initialRight = true →
        g.TraceEquivalent initialLeft initialRight →
        ∀ path : TracePath g initialLeft initialRight,
          g.EventuallyBoundedOpenSound initialLeft initialRight
            (growth 0) path ∨
          Nonempty (ActiveStairSequence g initialLeft initialRight
            0 growth path))
    {initialLeft initialRight : RegularTerm}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hequivalent : g.TraceEquivalent initialLeft initialRight) :
    g.EveryPathCoveredBy initialLeft initialRight
      (g.boundedOpenSoundBasis (growth 0)) := by
  intro path
  rcases hstair initialLeft initialRight hground hequivalent path with
    hbounded | hsequence
  · obtain ⟨n, ⟨coverage⟩⟩ := hbounded
    exact ⟨n, ⟨coverage.toBasisCoverage⟩⟩
  · obtain ⟨sequence⟩ := hsequence
    obtain ⟨coverage⟩ := sequence.covered 0
    have htails : sequence.tails = [] :=
      List.length_eq_zero_iff.mp sequence.active_width
    have coverage' : BoundedActiveHeadCoverage g initialLeft initialRight
        (growth 0) [] sequence.filler
        (path.word (sequence.levels 0)) := by
      simpa [htails] using coverage
    let schema := coverage'.schema
    have hopen : g.OpenSoundBasisPair schema :=
      coverage'.toActiveHeadCoverage.openSoundPair_of_noActiveTails
        laws hequivalent
    have hmem : schema ∈ g.boundedOpenSoundBasis (growth 0) := by
      apply (g.mem_boundedOpenSoundBasis_iff (growth 0) schema).mpr
      exact ⟨coverage'.arity_le, coverage'.left_size_le,
        coverage'.right_size_le, hopen⟩
    refine ⟨sequence.levels 0, ⟨?_⟩⟩
    exact
      { left := coverage'.left
        right := coverage'.right
        derivation := coverage'.derivation.rebasePair
        schema := schema
        schema_mem := hmem
        arguments := coverage'.arguments
        word_nonempty := coverage'.word_nonempty
        schema_wellFormed := hopen.1
        argument_count := by
          change (g.activePaddedArguments [] sequence.filler).length =
            g.activeSchemaArity []
          exact g.activePaddedArguments_length [] sequence.filler
        arguments_ground := coverage'.arguments_ground
        left_matches := coverage'.left_matches
        right_matches := coverage'.right_matches }

/-- A width-zero active stair base gives direct finite-basis derivations for
all equivalent ground queries, using one fixed original open-sound basis. -/
public theorem derivable_nop_of_activeStairBase_zero
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    (hstair : g.HasActiveStairBase 0) :
    ∃ bound,
      ∀ initialLeft initialRight,
        g.groundPairCode initialLeft initialRight = true →
        g.TraceEquivalent initialLeft initialRight →
        CertificateDerivable g initialLeft initialRight
          (g.boundedOpenSoundBasis bound) (.nop []) := by
  obtain ⟨growth, hstair⟩ := hstair
  refine ⟨growth 0, ?_⟩
  intro initialLeft initialRight hground hequivalent
  apply g.derivable_nop_of_everyPathCoveredBy laws hgroundSteps
    hground hequivalent
  exact everyPathCoveredBy_of_activeStairBase_zero laws hstair
    hground hequivalent

end EncodedFirstOrderGrammar

end DCFEquivalence
