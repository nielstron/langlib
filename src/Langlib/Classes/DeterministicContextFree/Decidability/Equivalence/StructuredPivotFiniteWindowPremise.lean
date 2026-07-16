module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FaithfulFiniteWindowSchemaRecurrence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window

@[expose]
public section

/-!
# The structured pivot edge as a finite-window recurrence premise

The operational `M₂` theorem is stated for label words and positions inside
one structured pivot edge.  The faithful schema recurrence consumes an
ordinary action word together with `BoundedReachOrSinkAlong`.  This file is
the exact conversion between those interfaces.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

namespace StructuredPivotChain

namespace WindowedPivotTrajectory

/-- Every structured pivot edge is an ordinary action word. -/
public theorem exists_actions_edge
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (j : ℕ) :
    ∃ actions : List Action,
      trajectory.toPivotTrajectory.edgeWords j =
        actions.map Sum.inl := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.exists_actions_of_ground_run
    (trajectory.toPivotTrajectory.representative_ground j)
    (trajectory.toPivotTrajectory.edge_run j)

/-- The action presentation of one structured pivot edge satisfies the
finite-window premise at every consumed prefix. -/
public theorem boundedReachOrSinkAlong_of_edge_actions
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hbound : 0 < bound)
    (j : ℕ)
    (actions : List Action)
    (hedge :
      trajectory.toPivotTrajectory.edgeWords j =
        actions.map Sum.inl) :
    g.BoundedReachOrSinkAlong
      (trajectory.toPivotTrajectory.representatives j)
      actions (g.structuredPivotM2Bound bound) := by
  intro consumed remaining current hactions hcurrent
  have hdrop :
      (trajectory.toPivotTrajectory.edgeWords j).drop consumed.length =
        remaining.map Sum.inl := by
    rw [hedge, hactions, List.map_append]
    simp
  have hoffset :
      consumed.length ≤
        (trajectory.toPivotTrajectory.edgeWords j).length := by
    rw [hedge, hactions, List.length_map, List.length_append]
    omega
  let position : trajectory.EdgePosition j :=
    { offset := consumed.length
      offset_le := hoffset
      term := current
      run := by
        have htake :
            (trajectory.toPivotTrajectory.edgeWords j).take
                consumed.length =
              consumed.map Sum.inl := by
          rw [hedge, hactions, List.map_append]
          simp
        simpa [runActions?, htake] using hcurrent }
  rcases trajectory.edgePosition_reachesPivot_or_sinks
      hbound j position with hpivot | hsinks
  · left
    obtain ⟨word, hword, hlength, _hrun⟩ := hpivot
    simpa [position, hword, hdrop] using hlength
  · right
    obtain ⟨word, labelRemainder, hword, hlength, hsinks⟩ :=
      hsinks
    have hmapSplit :
        remaining.map Sum.inl = word ++ labelRemainder := by
      rw [← hdrop]
      simpa [position] using hword
    obtain ⟨sinking, rest, hremaining, hwordMap,
        _hremainderMap⟩ :=
      List.map_eq_append_iff.mp hmapSplit
    refine ⟨sinking, rest, hremaining, ?_, ?_⟩
    · have hwordLength := congrArg List.length hwordMap
      simp at hwordLength
      omega
    · simpa [position, hwordMap] using hsinks

/-- Packaged ordinary edge run together with the exact finite-window
recurrence premise. -/
public theorem exists_actions_boundedReachOrSinkAlong_edge
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hbound : 0 < bound)
    (j : ℕ) :
    ∃ actions : List Action,
      trajectory.toPivotTrajectory.edgeWords j =
          actions.map Sum.inl ∧
        g.runActions? actions
            (trajectory.toPivotTrajectory.representatives j) =
          some (trajectory.toPivotTrajectory.representatives (j + 1)) ∧
        g.BoundedReachOrSinkAlong
          (trajectory.toPivotTrajectory.representatives j)
          actions (g.structuredPivotM2Bound bound) := by
  obtain ⟨actions, hedge⟩ := trajectory.exists_actions_edge j
  refine ⟨actions, hedge, ?_,
    trajectory.boundedReachOrSinkAlong_of_edge_actions
      hbound j actions hedge⟩
  simpa [runActions?, hedge] using
    (trajectory.toPivotTrajectory.edge_run j)

end WindowedPivotTrajectory

end StructuredPivotChain

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
