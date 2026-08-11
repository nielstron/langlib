module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingStairAssembly
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationSupport

@[expose]
public section

/-!
# Assembling witnessed balancing levels into a stair

The schema-level balancing construction retains finite reachable-prefix
witnesses at every selected endpoint.  Once all endpoint coverages use one
fixed argument tuple, assembling them into the witnessed stair required by
width reduction is purely structural.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Reindex a bounded witnessed coverage along equality of its accumulated
word. -/
public def BoundedWitnessedActiveSchemaCoverage.castWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word word' : List (Label Action)}
    (coverage : BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight bound width arguments word)
    (hword : word = word') :
    BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight bound width arguments word' := by
  subst word'
  exact coverage

/-- Fixed-argument witnessed endpoint coverages on a selected balancing
sequence form a witnessed regular active stair. -/
public def BalancingOpportunitySequence.toWitnessedRegularActiveStairSequence
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound width : ℕ}
    (sequence : BalancingOpportunitySequence path segmentBound)
    (growth : ℕ → ℕ) (arguments : List RegularTerm)
    (hcovered : ∀ j, Nonempty
      (BoundedWitnessedActiveSchemaCoverage g
        initialLeft initialRight (growth j) width arguments
        (path.word (sequence.endLevels j)))) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      width growth path :=
  { arguments := arguments
    levels := sequence.endLevels
    levels_strictMono := sequence.endLevels_strictMono
    covered := hcovered }

/-- Segment-shaped version matching the word produced by a balancing-result
constructor. -/
public def
    BalancingOpportunitySequence.toWitnessedRegularActiveStairSequence_of_segments
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound width : ℕ}
    (sequence : BalancingOpportunitySequence path segmentBound)
    (growth : ℕ → ℕ) (arguments : List RegularTerm)
    (hcovered : ∀ j, Nonempty
      (BoundedWitnessedActiveSchemaCoverage g
        initialLeft initialRight (growth j) width arguments
        (path.word (sequence.starts j) ++
          path.segmentWord (sequence.starts j) segmentBound))) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      width growth path := by
  apply sequence.toWitnessedRegularActiveStairSequence growth arguments
  intro j
  obtain ⟨coverage⟩ := hcovered j
  exact ⟨coverage.castWord (sequence.word_endLevels j).symm⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
