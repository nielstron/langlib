module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotExposureRebasing

@[expose]
public section

/-!
# Localizing a cut in an accumulated pivot word

An exposing prefix selected inside the accumulated pivot word may originally
be witnessed by an arbitrarily late pivot endpoint.  The list-theoretic lemma
below relocates it to the first endpoint of the single edge containing the
cut.  This is the form needed by the `M₂` window theorem: the remaining word
is either empty or literally a suffix of one pivot edge.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain.PivotTrajectory

/-- Any prefix of an accumulated pivot word can be witnessed at an endpoint
where the remainder is either empty or the suffix of the immediately
preceding edge. -/
public theorem exists_endpoint_cut
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    {start : ℕ} {first remainder : List (Label Action)}
    (hprefix : trajectory.prefixWord start = first ++ remainder) :
    ∃ next localizedRemainder,
      trajectory.prefixWord next = first ++ localizedRemainder ∧
        (localizedRemainder = [] ∨
          ∃ j offset,
            next = j + 1 ∧
              offset ≤ (trajectory.edgeWords j).length ∧
              first = trajectory.prefixWord j ++
                (trajectory.edgeWords j).take offset ∧
              localizedRemainder =
                (trajectory.edgeWords j).drop offset) := by
  induction start generalizing first remainder with
  | zero =>
      simp [prefixWord] at hprefix
      rcases hprefix with ⟨rfl, rfl⟩
      exact ⟨0, [], rfl, Or.inl rfl⟩
  | succ j ih =>
      let previous := trajectory.prefixWord j
      let edge := trajectory.edgeWords j
      have hfull : previous ++ edge = first ++ remainder := by
        simpa [prefixWord, previous, edge] using hprefix
      have hfirstLe : first.length ≤ previous.length + edge.length := by
        have hlength := congrArg List.length hfull
        simp only [List.length_append] at hlength
        omega
      by_cases hwithin : first.length ≤ previous.length
      · have hfirstTake : first = previous.take first.length := by
          calc
            first = (previous ++ edge).take first.length := by
              rw [hfull]
              simp
            _ = previous.take first.length :=
              List.take_append_of_le_length hwithin
        have hprevious :
            previous = first ++ previous.drop first.length := by
          calc
            previous = previous.take first.length ++
                previous.drop first.length :=
              (List.take_append_drop first.length previous).symm
            _ = first ++ previous.drop first.length := by
              rw [← hfirstTake]
        obtain ⟨next, localizedRemainder, hnext, hshape⟩ :=
          ih hprevious
        exact ⟨next, localizedRemainder, hnext, hshape⟩
      · let offset := first.length - previous.length
        have hpreviousLt : previous.length < first.length :=
          Nat.lt_of_not_ge hwithin
        have hoffset : offset ≤ edge.length := by
          dsimp [offset]
          omega
        have hfirstCurrent :
            first = previous ++ edge.take offset := by
          calc
            first = (previous ++ edge).take first.length := by
              rw [hfull]
              simp
            _ = previous.take first.length ++
                edge.take (first.length - previous.length) :=
              List.take_append
            _ = previous ++ edge.take offset := by
              rw [List.take_of_length_le (Nat.le_of_lt hpreviousLt)]
        refine ⟨j + 1, edge.drop offset, ?_, Or.inr ?_⟩
        · rw [prefixWord]
          calc
            previous ++ edge =
                (previous ++ edge.take offset) ++ edge.drop offset := by
              rw [List.append_assoc, List.take_append_drop]
            _ = first ++ edge.drop offset := by
              rw [hfirstCurrent]
        · exact ⟨j, offset, rfl, hoffset, hfirstCurrent, rfl⟩

end TracePath.StructuredPivotChain.PivotTrajectory

end EncodedFirstOrderGrammar

end DCFEquivalence
