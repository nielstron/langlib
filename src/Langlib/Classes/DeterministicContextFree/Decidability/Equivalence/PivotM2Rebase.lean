module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotCutLocalization
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window

@[expose]
public section

/-!
# An `M₂`-localized maximal-exposure rebase

The maximal exposing prefix is localized to the endpoint immediately after
the edge containing its cut.  Its initial remainder is then an actual edge
suffix.  The `M₂` dichotomy bounds that suffix: a sinking alternative would
contradict maximality of the exposed depth.

This theorem intentionally makes no claim about later edges.  A sink relative
to a later pivot is not automatically a sink relative to the fixed rebased
base; controlling all later accumulated labels is the separate finite-cover
part of the global `M₂` argument.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain.WindowedPivotTrajectory

/-- Localize an arbitrary maximal exposure rebase and bound the word from its
fixed base to the immediately following pivot by one `M₂` block. -/
public theorem exists_localizedRebase_remainder_length_le
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
    (rebase : trajectory.toPivotTrajectory.MaximalExposureRebase) :
    ∃ localized : trajectory.toPivotTrajectory.MaximalExposureRebase,
      (localized.labels 0).length ≤
        g.structuredPivotM2Bound bound := by
  let ordinary := trajectory.toPivotTrajectory
  obtain ⟨next, localizedRemainder, hnext, hshape⟩ :=
    ordinary.exists_endpoint_cut rebase.prefix_eq
  let localized : ordinary.MaximalExposureRebase :=
    { maximalExposure := rebase.maximalExposure
      start := next
      first := rebase.first
      remainder := localizedRemainder
      prefix_eq := hnext
      subterm := rebase.subterm
      base := rebase.base
      subterm_at := rebase.subterm_at
      first_run := rebase.first_run
      base_matches := rebase.base_matches }
  have hinitialRemainder : localizedRemainder.length ≤
      g.structuredPivotM2Bound bound := by
    rcases hshape with hempty | hedge
    · simp [hempty]
    · obtain ⟨j, offset, hnextIndex, hoffset, hfirst, hremainder⟩ :=
        hedge
      subst next
      have hfirstRun :
          g.run? ((ordinary.edgeWords j).take offset)
              (ordinary.representatives j) =
            some rebase.base := by
        have hrun := rebase.first_run
        rw [hfirst, g.run?_append, ordinary.prefixWord_run j] at hrun
        exact hrun
      let position : trajectory.EdgePosition j :=
        { offset := offset
          offset_le := hoffset
          term := rebase.base
          run := hfirstRun }
      have hnoSinking : ∀ word remainder,
          (ordinary.edgeWords j).drop position.offset =
              word ++ remainder →
            ¬g.SinksBy position.term word := by
        intro word remainder hword hsinks
        apply localized.not_exposes_positive 0 1 (by omega)
        obtain ⟨initialSegment, suffix, hsinkWord, _hnonempty,
            hexact⟩ := hsinks
        refine ⟨initialSegment, suffix ++ remainder, ?_, hexact⟩
        calc
          localized.labels 0 = localizedRemainder := by
            simp [localized,
              TracePath.StructuredPivotChain.PivotTrajectory.MaximalExposureRebase.labels,
              TracePath.StructuredPivotChain.PivotTrajectory.edgeSegment]
          _ = (ordinary.edgeWords j).drop offset := hremainder
          _ = word ++ remainder := by simpa [position] using hword
          _ = (initialSegment ++ suffix) ++ remainder := by
            rw [hsinkWord]
          _ = initialSegment ++ (suffix ++ remainder) :=
            List.append_assoc _ _ _
      have hlength := trajectory.edgeRemaining_length_le_m2_of_noSinkingPrefix
        hbound j position hnoSinking
      simpa [position, hremainder] using hlength
  refine ⟨localized, ?_⟩
  simpa [localized,
    TracePath.StructuredPivotChain.PivotTrajectory.MaximalExposureRebase.labels,
    TracePath.StructuredPivotChain.PivotTrajectory.edgeSegment] using
      hinitialRemainder

end TracePath.StructuredPivotChain.WindowedPivotTrajectory

end EncodedFirstOrderGrammar

end DCFEquivalence
