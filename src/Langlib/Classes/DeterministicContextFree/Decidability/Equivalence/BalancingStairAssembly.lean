module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingOpportunitySequence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RegularStairBases

@[expose]
public section

/-!
# Assembling selected balancing levels into a regular stair

The semantic pivot argument supplies one bounded active-schema coverage at
each selected segment endpoint.  Once all those coverages use one fixed
argument tuple, the remaining passage to `RegularActiveStairSequence` is
purely structural.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Reindex a bounded coverage along equality of its accumulated word. -/
public def BoundedActiveSchemaCoverage.castWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word word' : List (Label Action)}
    (coverage : BoundedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments word)
    (hword : word = word') :
    BoundedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments word' := by
  subst word'
  exact coverage

/-- Fixed-argument endpoint coverages on a selected balancing sequence form a
regular active stair sequence. -/
public def BalancingOpportunitySequence.toRegularActiveStairSequence
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {segmentBound width : ℕ}
    (sequence : BalancingOpportunitySequence path segmentBound)
    (growth : ℕ → ℕ) (arguments : List RegularTerm)
    (hcovered : ∀ j, Nonempty
      (BoundedActiveSchemaCoverage g initialLeft initialRight
        (growth j) width arguments
        (path.word (sequence.endLevels j)))) :
    RegularActiveStairSequence g initialLeft initialRight
      width growth path :=
  { arguments := arguments
    levels := sequence.endLevels
    levels_strictMono := sequence.endLevels_strictMono
    covered := hcovered }

/-- The same assembly theorem in the word shape naturally produced by a
balancing-result constructor: path stem followed by the selected segment. -/
public def BalancingOpportunitySequence.toRegularActiveStairSequence_of_segments
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {segmentBound width : ℕ}
    (sequence : BalancingOpportunitySequence path segmentBound)
    (growth : ℕ → ℕ) (arguments : List RegularTerm)
    (hcovered : ∀ j, Nonempty
      (BoundedActiveSchemaCoverage g initialLeft initialRight
        (growth j) width arguments
        (path.word (sequence.starts j) ++
          path.segmentWord (sequence.starts j) segmentBound))) :
    RegularActiveStairSequence g initialLeft initialRight
      width growth path := by
  apply sequence.toRegularActiveStairSequence growth arguments
  intro j
  obtain ⟨coverage⟩ := hcovered j
  exact ⟨coverage.castWord (sequence.word_endLevels j).symm⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
