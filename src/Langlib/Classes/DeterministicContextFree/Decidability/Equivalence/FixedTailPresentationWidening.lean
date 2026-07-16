module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedBaseBalancingStairIntegration

@[expose]
public section

/-!
# Uniform widening of fixed-tail stair presentations

Path-local fixed-tail constructions may use fewer active variables and a
smaller padded arity than the grammar-wide bounds chosen for the global stair
base.  This file widens those presentations without changing their reachable
instances:

* reachable prefix witnesses are monotone in the active width;
* the declared schema arity is increased without changing either schema
  graph;
* the fixed argument tuple is extended by ground filler copies; and
* prefix-witness invariance proves that the appended inactive arguments do
  not change either instantiated regular tree.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- A reachable support using variables below `small` also witnesses every
larger active-variable bound. -/
public theorem PrefixWitness.mono
    {term : RegularTerm} {small large : ℕ} {support : List ℕ}
    (hwitness : term.PrefixWitness small support)
    (hwidth : small ≤ large) :
    term.PrefixWitness large support := by
  refine ⟨hwitness.1, ?_⟩
  intro i hi
  rcases hwitness.2 i hi with hvariable | happlication
  · obtain ⟨x, hnode, hx⟩ := hvariable
    exact Or.inl ⟨x, hnode, hx.trans_le hwidth⟩
  · exact Or.inr happlication

/-- Existential reachable-prefix witnesses are monotone in their width. -/
public theorem HasPrefixWitness.mono
    {term : RegularTerm} {small large : ℕ}
    (hwitness : term.HasPrefixWitness small)
    (hwidth : small ≤ large) :
    term.HasPrefixWitness large := by
  obtain ⟨support, hsupport⟩ := hwitness
  exact ⟨support, hsupport.mono hwidth⟩

/-- Append enough copies of `filler` to reach a selected declared arity. -/
@[expose] public def padInactiveArguments
    (arguments : List RegularTerm) (filler : RegularTerm)
    (targetArity : ℕ) : List RegularTerm :=
  arguments ++
    List.replicate (targetArity - arguments.length) filler

@[simp] public theorem padInactiveArguments_length
    {arguments : List RegularTerm} {filler : RegularTerm}
    {targetArity : ℕ}
    (harity : arguments.length ≤ targetArity) :
    (padInactiveArguments arguments filler targetArity).length =
      targetArity := by
  simp [padInactiveArguments, Nat.add_sub_of_le harity]

/-- Properties of every original argument and of the filler are preserved by
inactive padding. -/
public theorem padInactiveArguments_forall
    {arguments : List RegularTerm} {filler : RegularTerm}
    {targetArity : ℕ} {P : RegularTerm → Prop}
    (harguments : ∀ argument ∈ arguments, P argument)
    (hfiller : P filler) :
    ∀ argument ∈ padInactiveArguments arguments filler targetArity,
      P argument := by
  intro argument hargument
  simp only [padInactiveArguments, List.mem_append,
    List.mem_replicate] at hargument
  rcases hargument with hargument | ⟨_count, rfl⟩
  · exact harguments argument hargument
  · exact hfiller

/-- The original tuple agrees with its inactive padding through every
position already present in the original tuple. -/
public theorem argumentsEquivalentThrough_padInactiveArguments
    {arguments : List RegularTerm} {filler : RegularTerm}
    {targetArity width : ℕ}
    (hwidth : width ≤ arguments.length) :
    ArgumentsEquivalentThrough width arguments
      (padInactiveArguments arguments filler targetArity) := by
  intro i hi
  have hiArguments : i < arguments.length := hi.trans_le hwidth
  let argument := arguments[i]
  have hargument : arguments[i]? = some argument :=
    List.getElem?_eq_getElem hiArguments
  refine ⟨argument, argument, hargument, ?_,
    unfoldingEquivalent_refl argument⟩
  unfold padInactiveArguments
  rw [List.getElem?_append_left hiArguments]
  exact hargument

end RegularTerm

namespace BasisPair

/-- Increase only the declared parameter arity of a basis schema pair. -/
@[expose] public def widenArity
    (pair : BasisPair) (targetArity : ℕ) : BasisPair :=
  (targetArity, pair.left, pair.right)

@[simp] public theorem widenArity_arity
    (pair : BasisPair) (targetArity : ℕ) :
    (pair.widenArity targetArity).arity = targetArity := rfl

@[simp] public theorem widenArity_left
    (pair : BasisPair) (targetArity : ℕ) :
    (pair.widenArity targetArity).left = pair.left := rfl

@[simp] public theorem widenArity_right
    (pair : BasisPair) (targetArity : ℕ) :
    (pair.widenArity targetArity).right = pair.right := rfl

end BasisPair

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace WitnessedActiveSchemaCoverage

/-- Widen one witnessed active-schema coverage to exact larger active-width
and arity bounds.  The schema graphs are unchanged; only their declared arity
and the inactive suffix of the argument tuple are enlarged. -/
public def widen
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {sourceWidth targetWidth targetArity : ℕ}
    {word : List (Label Action)}
    (source : WitnessedActiveSchemaCoverage g
      initialLeft initialRight sourceWidth word)
    (filler : RegularTerm)
    (hfiller : filler.Ground g.ranks)
    (hwidth : sourceWidth ≤ targetWidth)
    (harity : source.coverage.schema.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    WitnessedActiveSchemaCoverage g
      initialLeft initialRight targetWidth word := by
  let schema := source.coverage.schema.widenArity targetArity
  let arguments := RegularTerm.padInactiveArguments
    source.coverage.arguments filler targetArity
  have hsourceWellFormed := source.coverage.schema_wellFormed
  unfold basisPairWellFormedCode at hsourceWellFormed
  rw [Bool.and_eq_true] at hsourceWellFormed
  have hleftWellFormed :
      source.coverage.schema.left.WellFormed
        g.ranks targetArity :=
    RegularTerm.WellFormed.mono harity hsourceWellFormed.1
  have hrightWellFormed :
      source.coverage.schema.right.WellFormed
        g.ranks targetArity :=
    RegularTerm.WellFormed.mono harity hsourceWellFormed.2
  have hargumentsArity :
      source.coverage.arguments.length ≤ targetArity := by
    rw [source.coverage.argument_count]
    exact harity
  have hargumentsGround :
      ∀ argument ∈ source.coverage.arguments,
        argument.Ground g.ranks :=
    source.coverage.arguments_areGround
  have hargumentsClosed :
      ∀ argument ∈ source.coverage.arguments,
        argument.ReferenceClosed :=
    source.coverage.arguments_referenceClosed
  have hfillerClosed : filler.ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground hfiller
  have hpaddedGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks := by
    exact RegularTerm.padInactiveArguments_forall
      hargumentsGround hfiller
  have hpaddedClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    exact RegularTerm.padInactiveArguments_forall
      hargumentsClosed hfillerClosed
  have hsourceWidth :
      sourceWidth ≤ source.coverage.arguments.length := by
    rw [source.coverage.argument_count]
    exact source.coverage.left_supported.2.1
  have hargumentsEquivalent :
      RegularTerm.ArgumentsEquivalentThrough sourceWidth
        source.coverage.arguments arguments := by
    exact
      RegularTerm.argumentsEquivalentThrough_padInactiveArguments
        hsourceWidth
  have hleftInstance :
      (source.coverage.schema.left.instantiate
          source.coverage.arguments).UnfoldingEquivalent
        (source.coverage.schema.left.instantiate arguments) :=
    source.left_witness.instantiate_unfoldingEquivalent_of_prefix
      hargumentsClosed hpaddedClosed hargumentsEquivalent
  have hrightInstance :
      (source.coverage.schema.right.instantiate
          source.coverage.arguments).UnfoldingEquivalent
        (source.coverage.schema.right.instantiate arguments) :=
    source.right_witness.instantiate_unfoldingEquivalent_of_prefix
      hargumentsClosed hpaddedClosed hargumentsEquivalent
  have hleftMatches :
      source.coverage.left.UnfoldingEquivalent
        (source.coverage.schema.left.instantiate arguments) :=
    (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
      source.coverage.left_matches |>.trans hleftInstance
  have hrightMatches :
      source.coverage.right.UnfoldingEquivalent
        (source.coverage.schema.right.instantiate arguments) :=
    (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
      source.coverage.right_matches |>.trans hrightInstance
  let coverage : ActiveSchemaCoverage g initialLeft initialRight
      targetWidth word :=
    { left := source.coverage.left
      right := source.coverage.right
      derivation := source.coverage.derivation
      schema := schema
      arguments := arguments
      word_nonempty := source.coverage.word_nonempty
      schema_wellFormed := by
        unfold schema BasisPair.widenArity basisPairWellFormedCode
        rw [Bool.and_eq_true]
        exact ⟨hleftWellFormed, hrightWellFormed⟩
      rank_padding := by
        exact source.coverage.rank_padding.trans harity
      left_supported := by
        simpa [schema] using
          (source.left_witness.mono hwidth).supportedByPrefix
            hleftWellFormed htargetWidth
      right_supported := by
        simpa [schema] using
          (source.right_witness.mono hwidth).supportedByPrefix
            hrightWellFormed htargetWidth
      argument_count := by
        simpa [schema, arguments] using
          RegularTerm.padInactiveArguments_length hargumentsArity
      arguments_ground := by
        unfold groundArgumentsCode
        apply List.all_eq_true.mpr
        intro argument hargument
        exact (RegularTerm.groundCode_eq_true_iff
          g.ranks argument).mpr (hpaddedGround argument hargument)
      left_matches := by
        exact (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by simpa [schema] using hleftMatches)
      right_matches := by
        exact (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by simpa [schema] using hrightMatches) }
  exact
    { coverage := coverage
      left_witness := by
        simpa [coverage, schema] using source.left_witness.mono hwidth
      right_witness := by
        simpa [coverage, schema] using source.right_witness.mono hwidth }

end WitnessedActiveSchemaCoverage

namespace BoundedWitnessedActiveSchemaCoverage

/-- Widen a bounded witnessed coverage, also enlarging its numerical
presentation bound enough to contain the selected exact arity. -/
public def widen
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {sourceBound sourceWidth targetBound targetWidth targetArity : ℕ}
    {arguments : List RegularTerm} {word : List (Label Action)}
    (source : BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight sourceBound sourceWidth arguments word)
    (filler : RegularTerm)
    (hfiller : filler.Ground g.ranks)
    (hwidth : sourceWidth ≤ targetWidth)
    (harity :
      source.witnessed.coverage.schema.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity)
    (hbound : sourceBound ≤ targetBound)
    (htargetArityBound : targetArity ≤ targetBound) :
    BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
      targetBound targetWidth
      (RegularTerm.padInactiveArguments arguments filler targetArity)
      word := by
  let widened := source.witnessed.widen filler hfiller
    hwidth harity htargetWidth
  exact
    { witnessed := widened
      arguments_eq := by
        change RegularTerm.padInactiveArguments
            source.witnessed.coverage.arguments filler targetArity =
          RegularTerm.padInactiveArguments arguments filler targetArity
        rw [source.arguments_eq]
      arity_le := by
        simpa [widened, WitnessedActiveSchemaCoverage.widen] using
          htargetArityBound
      left_size_le := by
        have := source.left_size_le.trans hbound
        simpa [widened, WitnessedActiveSchemaCoverage.widen] using this
      right_size_le := by
        have := source.right_size_le.trans hbound
        simpa [widened, WitnessedActiveSchemaCoverage.widen] using this }

end BoundedWitnessedActiveSchemaCoverage

namespace WitnessedRegularActiveStairSequence

/-- Widen every level of a witnessed regular stair to one exact common active
width and schema arity.  The new growth bound is the pointwise maximum of the
old bound and the selected arity. -/
public def widen
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {sourceWidth targetWidth targetArity : ℕ}
    {growth : ℕ → ℕ}
    {path : TracePath g initialLeft initialRight}
    (source : WitnessedRegularActiveStairSequence g
      initialLeft initialRight sourceWidth growth path)
    (filler : RegularTerm)
    (hfiller : filler.Ground g.ranks)
    (hwidth : sourceWidth ≤ targetWidth)
    (harity : source.arguments.length ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      targetWidth (fun j => max targetArity (growth j)) path := by
  refine
    { arguments := RegularTerm.padInactiveArguments
        source.arguments filler targetArity
      levels := source.levels
      levels_strictMono := source.levels_strictMono
      covered := ?_ }
  intro j
  obtain ⟨coverage⟩ := source.covered j
  have hcoverageArity :
      coverage.witnessed.coverage.schema.arity ≤ targetArity := by
    calc
      coverage.witnessed.coverage.schema.arity =
          coverage.witnessed.coverage.arguments.length :=
        coverage.witnessed.coverage.argument_count.symm
      _ = source.arguments.length :=
        congrArg List.length coverage.arguments_eq
      _ ≤ targetArity := harity
  exact ⟨coverage.widen filler hfiller hwidth
    hcoverageArity htargetWidth
    (Nat.le_max_right targetArity (growth j))
    (Nat.le_max_left targetArity (growth j))⟩

end WitnessedRegularActiveStairSequence

namespace LeftBalancingSubsequence

/-- Widen the canonical fixed-base left-balancing stair to selected
grammar-wide active-width and arity bounds. -/
public def
    toWitnessedRegularActiveStairSequence_of_fixedBaseNonSinking_widened
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound targetWidth targetArity : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : LeftBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (hdepth : segmentBound ≤ presentation.depth)
    (hnever : ∀ j,
      g.NeverSinksFromBase
        (subsequence.pivot 0) (presentation.actions j))
    (hwidth : presentation.width ≤ targetWidth)
    (harity : presentation.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      targetWidth
      (fun j => max targetArity
        (g.fixedBalancingPresentationBound segmentBound
          presentation.arity (presentation.schemaGrowth j)))
      path := by
  let source :=
    subsequence
      |>.toWitnessedRegularActiveStairSequence_of_fixedBaseNonSinking
        hg hnormal hexposureBound hground hinitial hfiller presentation
        hdepth hnever
  apply source.widen filler hfiller hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

end LeftBalancingSubsequence

namespace RightBalancingSubsequence

/-- Symmetric widening of the canonical fixed-base right-balancing stair. -/
public def
    toWitnessedRegularActiveStairSequence_of_fixedBaseNonSinking_widened
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound targetWidth targetArity : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : RightBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (hdepth : segmentBound ≤ presentation.depth)
    (hnever : ∀ j,
      g.NeverSinksFromBase
        (subsequence.pivot 0) (presentation.actions j))
    (hwidth : presentation.width ≤ targetWidth)
    (harity : presentation.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      targetWidth
      (fun j => max targetArity
        (g.fixedBalancingPresentationBound segmentBound
          presentation.arity (presentation.schemaGrowth j)))
      path := by
  let source :=
    subsequence
      |>.toWitnessedRegularActiveStairSequence_of_fixedBaseNonSinking
        hg hnormal hexposureBound hground hinitial hfiller presentation
        hdepth hnever
  apply source.widen filler hfiller hwidth
  · change presentation.arguments.length ≤ targetArity
    rw [presentation.arguments_length]
    exact harity
  · exact htargetWidth

end RightBalancingSubsequence

end EncodedFirstOrderGrammar

end DCFEquivalence
