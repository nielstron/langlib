module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotProgressRebasing
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotCutLocalization

@[expose]
public section

/-!
# Localizing an operational maximal rebase within one `M₂` window

The maximal repeated-sinking prefix can end inside an accumulated pivot
edge.  Localizing that cut to the immediately following endpoint makes the
initial rebased word an exact suffix of one canonical windowed edge.
Maximality excludes the sinking branch of the edge-position dichotomy, so
that suffix has length at most `M₂`.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain.WindowedPivotTrajectory

/-- Localize an operational maximal rebase and bound its word to the
immediately following pivot by the grammar-uniform `M₂` constant. -/
public theorem exists_localizedProgressRebase_labels_zero_length_le
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
    (trajectory : chain.WindowedPivotTrajectory)
    (hbound : 0 < bound)
    (rebase :
      trajectory.toPivotTrajectory.MaximalProgressRebase) :
    ∃ localized :
        trajectory.toPivotTrajectory.MaximalProgressRebase,
      (localized.labels 0).length ≤
        g.structuredPivotM2Bound bound := by
  let ordinary := trajectory.toPivotTrajectory
  obtain ⟨next, localizedRemainder, hnext, hshape⟩ :=
    ordinary.exists_endpoint_cut rebase.prefix_eq
  let localized : ordinary.MaximalProgressRebase :=
    { maximalDepth := rebase.maximalDepth
      start := next
      consumed := rebase.consumed
      remainder := localizedRemainder
      prefix_eq := hnext
      base := rebase.base
      exactRun := rebase.exactRun }
  have hinitialRemainder :
      localizedRemainder.length ≤
        g.structuredPivotM2Bound bound := by
    rcases hshape with hempty | hedge
    · simp [hempty]
    · obtain ⟨j, offset, hnextIndex, hoffset, hconsumed,
          hremainder⟩ := hedge
      subst next
      have hconsumedRun :
          g.run? ((ordinary.edgeWords j).take offset)
              (ordinary.representatives j) =
            some rebase.base := by
        have hrun := rebase.consumed_run
        rw [hconsumed, g.run?_append,
          ordinary.prefixWord_run j] at hrun
        exact hrun
      let position : trajectory.EdgePosition j :=
        { offset := offset
          offset_le := hoffset
          term := rebase.base
          run := hconsumedRun }
      have hnoSinking : ∀ word remainder,
          (ordinary.edgeWords j).drop position.offset =
              word ++ remainder →
            ¬g.SinksBy position.term word := by
        intro word remainder hword hsinks
        have hsinksFull :
            g.SinksBy localized.base (localized.labels 0) := by
          have hlabels :
              localized.labels 0 = localizedRemainder := by
            simp [localized,
              TracePath.StructuredPivotChain.PivotTrajectory.MaximalProgressRebase.labels,
              TracePath.StructuredPivotChain.PivotTrajectory.edgeSegment]
          rw [hlabels, hremainder]
          rw [show position.offset = offset from rfl] at hword
          rw [hword]
          exact hsinks.append remainder
        have hprogress :
            g.RepeatedlySinksBy
              (ordinary.representatives 0)
              (ordinary.prefixWord localized.start)
              (localized.maximalDepth.depth + 1) := by
          rw [localized.prefix_eq]
          have hsinksRemainder :
              g.SinksBy localized.base localized.remainder := by
            simpa [TracePath.StructuredPivotChain.PivotTrajectory.MaximalProgressRebase.labels,
              TracePath.StructuredPivotChain.PivotTrajectory.edgeSegment] using
              hsinksFull
          exact localized.exactRun
            |>.repeatedlySinksBy_succ_of_sinksBy hsinksRemainder
        have hle := localized.maximalDepth.maximal
          (localized.maximalDepth.depth + 1)
          ⟨localized.start, hprogress⟩
        omega
      have hlength :=
        trajectory.edgeRemaining_length_le_m2_of_noSinkingPrefix
          hbound j position hnoSinking
      simpa [position, hremainder] using hlength
  refine ⟨localized, ?_⟩
  simpa [localized,
    TracePath.StructuredPivotChain.PivotTrajectory.MaximalProgressRebase.labels,
    TracePath.StructuredPivotChain.PivotTrajectory.edgeSegment] using
      hinitialRemainder

/-- The canonical windowed trajectory therefore always admits an
operational maximal rebase whose initial word is `M₂`-bounded whenever the
path has no derived repeat. -/
public theorem
    exists_maximalProgressRebase_labels_zero_length_le_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial)
    (trajectory : chain.WindowedPivotTrajectory)
    (hnoRepeat : ¬path.HasDerivedRepeat) :
    ∃ rebase :
        trajectory.toPivotTrajectory.MaximalProgressRebase,
      (rebase.labels 0).length ≤
        g.structuredPivotM2Bound bound := by
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
  obtain ⟨rebase⟩ :=
    trajectory.exists_maximalProgressRebase_of_noDerivedRepeat
      hg hnormal hground hinitial hexposureBound chain hnoRepeat
  exact trajectory.exists_localizedProgressRebase_labels_zero_length_le
    hbound rebase

end TracePath.StructuredPivotChain.WindowedPivotTrajectory

end EncodedFirstOrderGrammar

end DCFEquivalence
