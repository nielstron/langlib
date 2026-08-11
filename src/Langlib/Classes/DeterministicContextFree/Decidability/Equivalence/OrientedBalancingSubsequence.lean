module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingOpportunitySequence

@[expose]
public section

/-!
# An infinite balancing subsequence with one fixed orientation

An arbitrary cofinal opportunity sequence may alternate left and right
segments, so consecutive pivots need not lie on one run.  Since there are only
two orientations, one orientation occurs infinitely often.  Passing to that
subsequence puts every pivot on one fixed side of the original trace path and
therefore yields an actual pivot run between all selected pivots.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Infinitely many selected opportunities are left-balancing. -/
public structure LeftBalancingSubsequence
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (sequence : BalancingOpportunitySequence path bound) where
  indices : ℕ → ℕ
  indices_strictMono : StrictMono indices
  segment : ∀ j, BalancingSegment g bound
    (path.left (sequence.starts (indices j)))
    (path.right (sequence.starts (indices j)))
    (path.segmentWord (sequence.starts (indices j)) bound)

/-- Infinitely many selected opportunities are right-balancing. -/
public structure RightBalancingSubsequence
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (sequence : BalancingOpportunitySequence path bound) where
  indices : ℕ → ℕ
  indices_strictMono : StrictMono indices
  segment : ∀ j, BalancingSegment g bound
    (path.right (sequence.starts (indices j)))
    (path.left (sequence.starts (indices j)))
    (path.segmentWord (sequence.starts (indices j)) bound)

/-- One orientation occurs infinitely often in every infinite opportunity
sequence. -/
public theorem BalancingOpportunitySequence.exists_orientedSubsequence
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    (sequence : BalancingOpportunitySequence path bound) :
    Nonempty (LeftBalancingSubsequence sequence) ∨
      Nonempty (RightBalancingSubsequence sequence) := by
  classical
  let HasLeft : ℕ → Prop := fun j =>
    Nonempty (BalancingSegment g bound
      (path.left (sequence.starts j))
      (path.right (sequence.starts j))
      (path.segmentWord (sequence.starts j) bound))
  by_cases hleft : ∀ N, ∃ n > N, HasLeft n
  · obtain ⟨indices, hindices, hselected⟩ :=
      Nat.exists_strictMono_subsequence hleft
    left
    exact ⟨
      { indices := indices
        indices_strictMono := hindices
        segment := fun j => Classical.choice (hselected j) }⟩
  · push_neg at hleft
    obtain ⟨threshold, hthreshold⟩ := hleft
    let indices : ℕ → ℕ := fun j => threshold + 1 + j
    have hindices : StrictMono indices := by
      intro i j hij
      simp [indices]
      omega
    have hright : ∀ j, BalancingSegment g bound
        (path.right (sequence.starts (indices j)))
        (path.left (sequence.starts (indices j)))
        (path.segmentWord (sequence.starts (indices j)) bound) := by
      intro j
      let selected :=
        Classical.choice (sequence.selected (indices j))
      cases selected with
      | left segment =>
          exact False.elim
            (hthreshold (indices j) (by
              simp only [indices]
              omega) ⟨segment⟩)
      | right segment => exact segment
    right
    exact ⟨
      { indices := indices
        indices_strictMono := hindices
        segment := hright }⟩

namespace LeftBalancingSubsequence

/-- Path level of the `j`th left-balancing opportunity. -/
@[expose] public def levels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : LeftBalancingSubsequence sequence) (j : ℕ) : ℕ :=
  sequence.starts (subsequence.indices j)

public theorem levels_strictMono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : LeftBalancingSubsequence sequence) :
    StrictMono subsequence.levels :=
  sequence.starts_strictMono.comp subsequence.indices_strictMono

/-- The left-balancing pivots all lie on the right residual stream. -/
@[expose] public def pivot
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : LeftBalancingSubsequence sequence) (j : ℕ) :
    RegularTerm :=
  path.right (subsequence.levels j)

/-- Earlier pivots execute the intervening right-side path word to every later
pivot. -/
public theorem pivot_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : LeftBalancingSubsequence sequence)
    {i j : ℕ} (hij : i ≤ j) :
    g.run?
        (path.segmentWord (subsequence.levels i)
          (subsequence.levels j - subsequence.levels i))
        (subsequence.pivot i) =
      some (subsequence.pivot j) := by
  have hlevels : subsequence.levels i ≤ subsequence.levels j :=
    subsequence.levels_strictMono.monotone hij
  simpa [pivot, Nat.add_sub_of_le hlevels] using
    path.right_segment_run (subsequence.levels i)
      (subsequence.levels j - subsequence.levels i)

/-- Every selected segment still ends before the next retained opportunity. -/
public theorem end_le_next_level
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : LeftBalancingSubsequence sequence) (j : ℕ) :
    subsequence.levels j + bound ≤ subsequence.levels (j + 1) := by
  have hindexStep :
      subsequence.indices j + 1 ≤ subsequence.indices (j + 1) := by
    exact Nat.add_one_le_iff.mpr
      (subsequence.indices_strictMono (by omega))
  exact (sequence.separated (subsequence.indices j)).trans
    (sequence.starts_strictMono.monotone hindexStep)

end LeftBalancingSubsequence

namespace RightBalancingSubsequence

/-- Path level of the `j`th right-balancing opportunity. -/
@[expose] public def levels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : RightBalancingSubsequence sequence) (j : ℕ) : ℕ :=
  sequence.starts (subsequence.indices j)

public theorem levels_strictMono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : RightBalancingSubsequence sequence) :
    StrictMono subsequence.levels :=
  sequence.starts_strictMono.comp subsequence.indices_strictMono

/-- The right-balancing pivots all lie on the left residual stream. -/
@[expose] public def pivot
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : RightBalancingSubsequence sequence) (j : ℕ) :
    RegularTerm :=
  path.left (subsequence.levels j)

/-- Earlier pivots execute the intervening left-side path word to every later
pivot. -/
public theorem pivot_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : RightBalancingSubsequence sequence)
    {i j : ℕ} (hij : i ≤ j) :
    g.run?
        (path.segmentWord (subsequence.levels i)
          (subsequence.levels j - subsequence.levels i))
        (subsequence.pivot i) =
      some (subsequence.pivot j) := by
  have hlevels : subsequence.levels i ≤ subsequence.levels j :=
    subsequence.levels_strictMono.monotone hij
  simpa [pivot, Nat.add_sub_of_le hlevels] using
    path.left_segment_run (subsequence.levels i)
      (subsequence.levels j - subsequence.levels i)

/-- Every selected segment still ends before the next retained opportunity. -/
public theorem end_le_next_level
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : RightBalancingSubsequence sequence) (j : ℕ) :
    subsequence.levels j + bound ≤ subsequence.levels (j + 1) := by
  have hindexStep :
      subsequence.indices j + 1 ≤ subsequence.indices (j + 1) := by
    exact Nat.add_one_le_iff.mpr
      (subsequence.indices_strictMono (by omega))
  exact (sequence.separated (subsequence.indices j)).trans
    (sequence.starts_strictMono.monotone hindexStep)

end RightBalancingSubsequence

end EncodedFirstOrderGrammar

end DCFEquivalence
