module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingResultCore

@[expose]
public section

/-!
# The symbolic pivot side of a balancing result

The pivot executes the same ordinary action word as the active side.  Taking a
depth prefix as long as that word therefore yields a supported symbolic
residual whose instance denotes the concrete pivot target, with uniform arity
and graph-size bounds.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The finite-prefix residual obtained from the pivot side of a balancing
segment, synchronized with its active-prefix result. -/
public structure BalancingSegment.PivotPrefixResidual
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (filler : RegularTerm)
    (activeResult : segment.ActivePrefixResidual filler) where
  residual : RegularTerm
  symbolic_run :
    g.runActions? activeResult.actions
        (pivot.depthPrefix bound).head.toRegularTerm =
      some residual
  instance_matches :
    (residual.instantiate
        ((pivot.depthPrefix bound).paddedArguments g.ranks filler))
      |>.UnfoldingEquivalent segment.pivotTarget
  supported :
    RegularTerm.SupportedByPrefix g.ranks
      ((pivot.depthPrefix bound).schemaArity g.ranks)
      (pivot.depthPrefix bound).tails.length residual
  arity_le :
    (pivot.depthPrefix bound).schemaArity g.ranks ≤
      max (RegularTerm.depthPrefixTailBound g.ranks bound)
        (g.ranks.foldr max 0)
  size_le :
    residual.nodes.length ≤
      g.residualNodeBound activeResult.actions.length
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) bound)

/-- The pivot of a balancing segment factors through its depth-`bound`
compiled prefix under the same ordinary action word as the active result. -/
public theorem BalancingSegment.exists_pivotPrefixResidual
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {active pivot : RegularTerm}
    {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hpivot : pivot.Ground g.ranks)
    {filler : RegularTerm} (hfiller : filler.Ground g.ranks)
    (activeResult : segment.ActivePrefixResidual filler) :
    Nonempty (segment.PivotPrefixResidual filler activeResult) := by
  have hpivotRun :
      g.runActions? activeResult.actions pivot =
        some segment.pivotTarget := by
    simpa [runActions?, activeResult.labels_eq] using segment.pivot_run
  have hlength : activeResult.actions.length ≤ bound := by
    exact activeResult.actions_length.le
  obtain ⟨residual, hsymbolic, hinstance,
      hsupported, harity, hsize⟩ :=
    exists_depthPrefix_supported_residual hg hpivot hfiller
      bound hlength hpivotRun
  exact ⟨
    { residual := residual
      symbolic_run := hsymbolic
      instance_matches := hinstance
      supported := hsupported
      arity_le := harity
      size_le := hsize }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
