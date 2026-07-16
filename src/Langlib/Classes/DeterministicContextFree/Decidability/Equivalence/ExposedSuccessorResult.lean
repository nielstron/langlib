module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SuccessorExposureRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotPrefixResidual

@[expose]
public section

/-!
# One exposed-successor row of a balancing result

For one immediate child of the active root, its selected normal-form exposing
word reaches that child before the end of the balancing window.  The pivot
executes the same shorter word, and its target factors through the pivot's
fixed depth-`bound` prefix.  This is one of the `F_i(W)` rows used to replace
the active side's immediate tails.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The shorter derived pair and supported pivot schema associated with one
exposable immediate successor of a balancing active term. -/
public structure BalancingSegment.ExposedSuccessorResult
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {initialLeft initialRight : RegularTerm}
    (stem : List (Label Action)) (filler : RegularTerm) (child : ℕ) where
  word : List Action
  word_exposes :
    ∃ position : g.SuccessorPosition,
      g.ExposesSuccessor position word
  word_length_lt : word.length < bound
  activeTarget : RegularTerm
  pivotTarget : RegularTerm
  active_run : g.runActions? word active = some activeTarget
  active_matches :
    activeTarget.UnfoldingEquivalent (active.withRoot child)
  pivot_run : g.runActions? word pivot = some pivotTarget
  shorter_derivation :
    CertificateDerivable g initialLeft initialRight []
      (.pair (stem ++ word.map Sum.inl) activeTarget pivotTarget)
  pivotResidual : RegularTerm
  pivot_symbolic_run :
    g.runActions? word
        (pivot.depthPrefix bound).head.toRegularTerm =
      some pivotResidual
  pivot_instance_matches :
    (pivotResidual.instantiate
        ((pivot.depthPrefix bound).paddedArguments g.ranks filler))
      |>.UnfoldingEquivalent pivotTarget
  pivot_supported :
    RegularTerm.SupportedByPrefix g.ranks
      ((pivot.depthPrefix bound).schemaArity g.ranks)
      (pivot.depthPrefix bound).tails.length pivotResidual
  pivot_arity_le :
    (pivot.depthPrefix bound).schemaArity g.ranks ≤
      max (RegularTerm.depthPrefixTailBound g.ranks bound)
        (g.ranks.foldr max 0)
  pivot_size_le :
    pivotResidual.nodes.length ≤
      g.residualNodeBound word.length
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) bound)

/-- A selected normal-form exposing word packages one active child and the
matching supported pivot residual under the same shorter derivation. -/
public theorem BalancingSegment.exists_exposedSuccessorResult
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hexposureBound : g.exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    {filler : RegularTerm} (hfiller : filler.Ground g.ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    (position : g.SuccessorPosition)
    {children : List ℕ} {child : ℕ}
    (hroot :
      active.rootApplication? = some (position.1.val, children))
    (hchild : children[position.2.val]? = some child) :
    Nonempty (BalancingSegment.ExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      segment stem filler child) := by
  let word := g.exposingWord hnormal position
  have hwordExposure : g.ExposesSuccessor position word := by
    exact g.exposingWord_exposes hnormal position
  have hwordLength : word.length < bound := by
    exact lt_of_lt_of_le
      (g.exposingWord_length_lt_exposureBound hnormal position)
      hexposureBound
  obtain ⟨activeTarget, pivotTarget, hactiveRun,
      hactiveMatches, hpivotRun⟩ :=
    segment.exists_pivotTarget_for_exposedSuccessor
      hg hactive position hwordExposure hwordLength hroot hchild
  have hderivation :
      CertificateDerivable g initialLeft initialRight []
        (.pair (stem ++ word.map Sum.inl) activeTarget pivotTarget) :=
    houter.follow_runActions
      (preservesGroundSteps_of_wellFormed hg) hequivalent
      hactiveRun hpivotRun
  obtain ⟨pivotResidual, hpivotSymbolic, hpivotInstance,
      hpivotSupported, hpivotArity, hpivotSize⟩ :=
    exists_depthPrefix_supported_residual hg hpivot hfiller
      bound (Nat.le_of_lt hwordLength) hpivotRun
  exact ⟨
    { word := word
      word_exposes := ⟨position, hwordExposure⟩
      word_length_lt := hwordLength
      activeTarget := activeTarget
      pivotTarget := pivotTarget
      active_run := hactiveRun
      active_matches := hactiveMatches
      pivot_run := hpivotRun
      shorter_derivation := hderivation
      pivotResidual := pivotResidual
      pivot_symbolic_run := hpivotSymbolic
      pivot_instance_matches := hpivotInstance
      pivot_supported := hpivotSupported
      pivot_arity_le := hpivotArity
      pivot_size_le := hpivotSize }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
