module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingWindowDichotomy
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedReachabilityRepeat

@[expose]
public section

/-!
# Cofinal balancing opportunities

The pivot-path construction begins with a purely order-theoretic split.  If a
path suffix has no balancing opportunity, bounded sinking yields a semantic
repeat.  Otherwise balancing opportunities occur cofinally, and classical
choice selects a non-overlapping sequence of them.  This file packages
the second half and the logical handoff from the first half.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A balancing segment on either side of a common trace path. -/
public inductive PathBalancingSegment
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (bound start : ℕ) : Type
  | left
      (segment : BalancingSegment g bound
        (path.left start) (path.right start)
        (path.segmentWord start bound))
  | right
      (segment : BalancingSegment g bound
        (path.right start) (path.left start)
        (path.segmentWord start bound))

/-- A fixed path position admits a balancing segment on at least one side. -/
@[expose] public def TracePath.HasBalancingOpportunity
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (bound start : ℕ) : Prop :=
  Nonempty (PathBalancingSegment path bound start)

/-- Balancing opportunities occur beyond every path threshold. -/
@[expose] public def TracePath.HasCofinalBalancingOpportunities
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (bound : ℕ) : Prop :=
  ∀ threshold, ∃ start, threshold ≤ start ∧
    path.HasBalancingOpportunity bound start

/-- A sequence of non-overlapping, oriented balancing segments. -/
public structure BalancingOpportunitySequence
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (bound : ℕ) where
  starts : ℕ → ℕ
  starts_strictMono : StrictMono starts
  separated : ∀ j, starts j + bound ≤ starts (j + 1)
  selected : ∀ j, path.HasBalancingOpportunity bound (starts j)

namespace BalancingOpportunitySequence

/-- The path level reached after executing the selected balancing segment. -/
@[expose] public def endLevels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (sequence : BalancingOpportunitySequence path bound)
    (j : ℕ) : ℕ :=
  sequence.starts j + bound

/-- Selected segment endpoints remain strictly increasing. -/
public theorem endLevels_strictMono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (sequence : BalancingOpportunitySequence path bound) :
    StrictMono sequence.endLevels := by
  intro i j hij
  exact Nat.add_lt_add_right (sequence.starts_strictMono hij) bound

/-- Each selected segment ends before the next selected segment starts. -/
public theorem endLevels_le_next_start
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (sequence : BalancingOpportunitySequence path bound)
    (j : ℕ) :
    sequence.endLevels j ≤ sequence.starts (j + 1) :=
  sequence.separated j

/-- The accumulated word at a selected endpoint is the stem followed by the
segment word. -/
public theorem word_endLevels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (sequence : BalancingOpportunitySequence path bound)
    (j : ℕ) :
    path.word (sequence.endLevels j) =
      path.word (sequence.starts j) ++
        path.segmentWord (sequence.starts j) bound := by
  exact path.word_add (sequence.starts j) bound

end BalancingOpportunitySequence

namespace TracePath

private noncomputable def firstBalancingStart
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hcofinal : path.HasCofinalBalancingOpportunities bound)
    (threshold : ℕ) : ℕ :=
  Classical.choose (hcofinal threshold)

private theorem firstBalancingStart_ge
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hcofinal : path.HasCofinalBalancingOpportunities bound)
    (threshold : ℕ) :
    threshold ≤ firstBalancingStart hcofinal threshold :=
  (Classical.choose_spec (hcofinal threshold)).1

private theorem firstBalancingStart_selected
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hcofinal : path.HasCofinalBalancingOpportunities bound)
    (threshold : ℕ) :
    path.HasBalancingOpportunity bound
      (firstBalancingStart hcofinal threshold) :=
  (Classical.choose_spec (hcofinal threshold)).2

private noncomputable def balancingStarts
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hcofinal : path.HasCofinalBalancingOpportunities bound) : ℕ → ℕ
  | 0 => firstBalancingStart hcofinal 0
  | j + 1 => firstBalancingStart hcofinal
      (balancingStarts hcofinal j + bound)

private theorem balancingStarts_separated
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hcofinal : path.HasCofinalBalancingOpportunities bound)
    (j : ℕ) :
    balancingStarts hcofinal j + bound ≤
      balancingStarts hcofinal (j + 1) := by
  rw [balancingStarts]
  exact firstBalancingStart_ge hcofinal _

private theorem balancingStarts_selected
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hcofinal : path.HasCofinalBalancingOpportunities bound)
    (j : ℕ) :
    path.HasBalancingOpportunity bound (balancingStarts hcofinal j) := by
  cases j with
  | zero =>
      exact firstBalancingStart_selected hcofinal 0
  | succ j =>
      rw [balancingStarts]
      exact firstBalancingStart_selected hcofinal _

/-- Positive-length cofinal opportunities admit a non-overlapping selected
sequence. -/
public theorem exists_balancingOpportunitySequence
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hbound : 0 < bound)
    (hcofinal : path.HasCofinalBalancingOpportunities bound) :
    Nonempty (BalancingOpportunitySequence path bound) := by
  let starts := balancingStarts hcofinal
  have hseparated : ∀ j, starts j + bound ≤ starts (j + 1) := by
    intro j
    exact balancingStarts_separated hcofinal j
  have hstrict : StrictMono starts := by
    apply strictMono_nat_of_lt_succ
    intro j
    exact (Nat.lt_add_of_pos_right hbound).trans_le (hseparated j)
  exact ⟨
    { starts := starts
      starts_strictMono := hstrict
      separated := hseparated
      selected := balancingStarts_selected hcofinal }⟩

/-- If every suffix without a balancing opportunity would force a repeat,
then a nonrepeating path has cofinal balancing opportunities. -/
public theorem hasCofinalBalancingOpportunities_of_noRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hnoRepeat : ¬path.HasRepeat)
    (hterminal : ∀ threshold,
      (∀ start, threshold ≤ start →
        ¬path.HasBalancingOpportunity bound start) →
      path.HasRepeat) :
    path.HasCofinalBalancingOpportunities bound := by
  classical
  intro threshold
  by_contra hnone
  apply hnoRepeat
  apply hterminal threshold
  intro start hstart hopportunity
  apply hnone
  exact ⟨start, hstart, hopportunity⟩

/-- Proposition 48's terminal-repeat branch and positive exposure length
together produce the selected opportunity sequence used by Proposition 49. -/
public theorem exists_balancingOpportunitySequence_of_noRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (hbound : 0 < bound)
    (hnoRepeat : ¬path.HasRepeat)
    (hterminal : ∀ threshold,
      (∀ start, threshold ≤ start →
        ¬path.HasBalancingOpportunity bound start) →
      path.HasRepeat) :
    Nonempty (BalancingOpportunitySequence path bound) := by
  apply path.exists_balancingOpportunitySequence hbound
  exact path.hasCofinalBalancingOpportunities_of_noRepeat
    hnoRepeat hterminal

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
