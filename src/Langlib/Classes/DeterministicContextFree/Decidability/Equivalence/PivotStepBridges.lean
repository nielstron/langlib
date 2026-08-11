module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedBalancingChain

@[expose]
public section

/-!
# Pivot bridges between normalized balancing steps

`DerivedBalancingStep` stores every Proposition-45 result in the normalized
order `(active result, pivot result)`.  Thus the pivot endpoint is always the
right component of the derived target, independently of the orientation used
to construct the step.

For a left-selected segment the old right component follows the whole bridge
directly to the new pivot.  For a right-selected segment the corresponding
direct bridge starts at the old left component; this is precisely the switch
case in the pivot-path argument.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

namespace DerivedBalancingStep

/-- A left-selected normalized step carries the old pivot directly to the
new pivot endpoint. -/
public theorem right_run_to_result_of_left
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : DerivedBalancingStep hg hground hinitial source bound)
    (hside : SelectedBalancingSegment.side step.selected =
      BalancingSide.left) :
    g.run?
        ((source.continuationPath hg hground hinitial).segmentWord
          0 (step.offset + bound))
        source.right = some step.result.coverage.right := by
  let continuation :=
    source.continuationPath hg hground hinitial
  have hprefix := continuation.right_segment_run 0 step.offset
  have hprefix' :
      g.run? (continuation.segmentWord 0 step.offset) source.right =
        some (continuation.right step.offset) := by
    simpa only [Nat.zero_add, continuation.starts_right] using hprefix
  have hsuffix := step.pivot_run_to_result
  cases hselected : step.selected with
  | left segment =>
      rw [continuation.segmentWord_add, g.run?_append, hprefix']
      simpa [SelectedBalancingSegment.pivot, continuation, hselected]
        using hsuffix
  | right segment =>
      simp [SelectedBalancingSegment.side, hselected] at hside

/-- Original-path form of `right_run_to_result_of_left`. -/
public theorem original_right_run_to_result_of_left
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : DerivedBalancingStep hg hground hinitial source bound)
    (hside : SelectedBalancingSegment.side step.selected =
      BalancingSide.left) :
    g.run? (path.segmentWord start (step.offset + bound))
        source.right = some step.result.coverage.right := by
  have hrun := step.right_run_to_result_of_left hside
  rw [source.continuationPath_segmentWord
    hg hground hinitial 0 (step.offset + bound)] at hrun
  simpa using hrun

/-- A right-selected normalized step carries the old active component
directly to the new pivot endpoint.  A separate switch lemma will reconnect
this endpoint to the preceding pivot by the bounded replacement word. -/
public theorem left_run_to_result_of_right
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : DerivedBalancingStep hg hground hinitial source bound)
    (hside : SelectedBalancingSegment.side step.selected =
      BalancingSide.right) :
    g.run?
        ((source.continuationPath hg hground hinitial).segmentWord
          0 (step.offset + bound))
        source.left = some step.result.coverage.right := by
  let continuation :=
    source.continuationPath hg hground hinitial
  have hprefix := continuation.left_segment_run 0 step.offset
  have hprefix' :
      g.run? (continuation.segmentWord 0 step.offset) source.left =
        some (continuation.left step.offset) := by
    simpa only [Nat.zero_add, continuation.starts_left] using hprefix
  have hsuffix := step.pivot_run_to_result
  cases hselected : step.selected with
  | left segment =>
      simp [SelectedBalancingSegment.side, hselected] at hside
  | right segment =>
      rw [continuation.segmentWord_add, g.run?_append, hprefix']
      simpa [SelectedBalancingSegment.pivot, continuation, hselected]
        using hsuffix

/-- Original-path form of `left_run_to_result_of_right`. -/
public theorem original_left_run_to_result_of_right
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : DerivedBalancingStep hg hground hinitial source bound)
    (hside : SelectedBalancingSegment.side step.selected =
      BalancingSide.right) :
    g.run? (path.segmentWord start (step.offset + bound))
        source.left = some step.result.coverage.right := by
  have hrun := step.left_run_to_result_of_right hside
  rw [source.continuationPath_segmentWord
    hg hground hinitial 0 (step.offset + bound)] at hrun
  simpa using hrun

end DerivedBalancingStep

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
