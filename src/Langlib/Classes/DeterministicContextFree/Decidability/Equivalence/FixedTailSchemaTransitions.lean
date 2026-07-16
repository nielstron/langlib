module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OperationalFixedTailPresentation

@[expose]
public section

/-!
# Successive symbolic transitions in a fixed-tail presentation

The fixed-tail construction initially presents every retained pivot by an
independently reflected run from the common depth-prefix schema.  Along an
accumulated pivot trajectory those reflected residuals nevertheless form one
exact symbolic run: factoring the accumulated action word at two retained
indices factors the corresponding symbolic executions as well.

This is the bridge needed by the direct Proposition-49 schema-growth
recurrence.  It avoids bounding the whole accumulated pivot word.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace FixedTailPivotPresentation

/-- If the action word of one presented pivot extends that of another, the
suffix executes exactly between their residual schemas. -/
public theorem symbolic_run_suffix
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    {first second : ℕ} {suffix : List Action}
    (hactions :
      presentation.actions second =
        presentation.actions first ++ suffix) :
    g.runActions? suffix (presentation.schema first) =
      some (presentation.schema second) := by
  have hfirst :
      g.runActions? (presentation.actions first)
          (base.depthPrefix presentation.depth).head.toRegularTerm =
        some (presentation.schema first) :=
    (presentation.residual first).symbolic_run
  have hsecond :
      g.runActions? (presentation.actions second)
          (base.depthPrefix presentation.depth).head.toRegularTerm =
        some (presentation.schema second) :=
    (presentation.residual second).symbolic_run
  rw [hactions] at hsecond
  unfold runActions? at hfirst hsecond ⊢
  rw [List.map_append, g.run?_append, hfirst] at hsecond
  exact hsecond

end FixedTailPivotPresentation

namespace TracePath.StructuredPivotChain.PivotTrajectory

namespace MaximalProgressRebase

/-- Successive rebased words differ by exactly the next concrete pivot edge. -/
public theorem labels_succ
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (count : ℕ) :
    rebase.labels (count + 1) =
      rebase.labels count ++
        trajectory.edgeWords (rebase.start + count) := by
  simp [labels,
    TracePath.StructuredPivotChain.PivotTrajectory.edgeSegment,
    List.append_assoc]

/-- Every concrete edge after the rebase is an ordinary action word. -/
public theorem exists_actions_edge
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (count : ℕ) :
    ∃ actions : List Action,
      trajectory.edgeWords (rebase.start + count) =
        actions.map Sum.inl := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.exists_actions_of_ground_run
    (trajectory.representative_ground (rebase.start + count))
    (trajectory.edge_run (rebase.start + count))

/-- The ordinary edge word, the corresponding action factorization, and the
exact symbolic transition between successive fixed-tail schemas. -/
public theorem exists_actions_schema_succ_transition
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (presentation : FixedTailPivotPresentation g
      rebase.base filler rebase.labels
      (fun count =>
        trajectory.representatives (rebase.start + count)))
    (count : ℕ) :
    ∃ actions : List Action,
      trajectory.edgeWords (rebase.start + count) =
          actions.map Sum.inl ∧
        presentation.actions (count + 1) =
          presentation.actions count ++ actions ∧
        g.runActions? actions (presentation.schema count) =
          some (presentation.schema (count + 1)) := by
  obtain ⟨actions, hedge⟩ := rebase.exists_actions_edge count
  have hmaps :
      (presentation.actions (count + 1)).map
          (Sum.inl : Action → Label Action) =
        (presentation.actions count ++ actions).map
          (Sum.inl : Action → Label Action) := by
    calc
      (presentation.actions (count + 1)).map Sum.inl =
          rebase.labels (count + 1) :=
        (presentation.labels_eq (count + 1)).symm
      _ = rebase.labels count ++
          trajectory.edgeWords (rebase.start + count) :=
        rebase.labels_succ count
      _ = (presentation.actions count).map Sum.inl ++
          actions.map Sum.inl := by
        rw [presentation.labels_eq count, hedge]
      _ = (presentation.actions count ++ actions).map Sum.inl := by
        rw [List.map_append]
  have hactions :
      presentation.actions (count + 1) =
        presentation.actions count ++ actions :=
    (List.map_inj_right
      (fun _ _ h => Sum.inl.inj h :
        Function.Injective (Sum.inl : Action → Label Action))).mp hmaps
  exact ⟨actions, hedge, hactions,
    presentation.symbolic_run_suffix hactions⟩

/-- The fixed-tail schemas on an operationally rebased trajectory execute
successively along the corresponding ordinary edge words. -/
public theorem exists_actions_schema_succ_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (presentation : FixedTailPivotPresentation g
      rebase.base filler rebase.labels
      (fun count =>
        trajectory.representatives (rebase.start + count)))
    (count : ℕ) :
    ∃ actions : List Action,
      trajectory.edgeWords (rebase.start + count) =
          actions.map Sum.inl ∧
        g.runActions? actions (presentation.schema count) =
          some (presentation.schema (count + 1)) := by
  obtain ⟨actions, hedge, _hactions, hrun⟩ :=
    rebase.exists_actions_schema_succ_transition presentation count
  exact ⟨actions, hedge, hrun⟩

end MaximalProgressRebase

end TracePath.StructuredPivotChain.PivotTrajectory

end EncodedFirstOrderGrammar

end DCFEquivalence
