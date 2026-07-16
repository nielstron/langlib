module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SemanticExposureProgressCounterexample

@[expose]
public section

/-!
# The trajectory-level semantic/progress obstruction

Once repeated-sinking depths are bounded, the proposed semantic-to-progress
reflection is incompatible with a cyclic initial representative that is
semantically exposed at arbitrarily large depths by the empty trajectory
prefix.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain

namespace WindowedPivotTrajectory

/-- Bounded progress plus unbounded semantic exposure at the empty prefix
refutes `SemanticExposureHasProgressWitness` directly. -/
public theorem not_semanticExposureHasProgressWitness_of_unboundedAtZero
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
    (hbounded : trajectory.HasBoundedRepeatedSinkingDepths)
    (hunboundedAtZero : ∀ depth,
      g.ExposesBy
        (trajectory.toPivotTrajectory.representatives 0)
        (trajectory.toPivotTrajectory.prefixWord 0)
        depth) :
    ¬trajectory.SemanticExposureHasProgressWitness := by
  obtain ⟨depthBound, hdepthBound⟩ := hbounded
  intro hreflection
  obtain ⟨progressCount, progressDepth, hdepth, hprogress⟩ :=
    hreflection 0 (depthBound + 1)
      (hunboundedAtZero (depthBound + 1))
  have hle :=
    hdepthBound progressCount progressDepth hprogress
  omega

/-- The explicit unary cycle from the predicate-level counterexample realizes
the unbounded-at-zero obstruction whenever it is the initial representative. -/
public theorem not_semanticExposureHasProgressWitness_of_unaryCycle
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
    (hbounded : trajectory.HasBoundedRepeatedSinkingDepths)
    (hcycle :
      trajectory.toPivotTrajectory.representatives 0 =
        SemanticExposureProgressCounterexample.unaryCycle) :
    ¬trajectory.SemanticExposureHasProgressWitness := by
  apply trajectory.not_semanticExposureHasProgressWitness_of_unboundedAtZero
    hbounded
  intro depth
  rw [hcycle]
  simpa [
    TracePath.StructuredPivotChain.PivotTrajectory.prefixWord] using
      (DCFEquivalence.SemanticExposureProgressCounterexample.EncodedFirstOrderGrammar.unaryCycle_exposesBy_nil
        g depth)

/-- In particular, on a nonrepeating path the missing reflection cannot be
proved until unbounded empty-prefix semantic self-exposure is independently
excluded. -/
public theorem not_semanticExposureHasProgressWitness_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain
      hg hground hinitial bound initial)
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    (hunboundedAtZero : ∀ depth,
      g.ExposesBy
        (trajectory.toPivotTrajectory.representatives 0)
        (trajectory.toPivotTrajectory.prefixWord 0)
        depth) :
    ¬trajectory.SemanticExposureHasProgressWitness := by
  apply trajectory.not_semanticExposureHasProgressWitness_of_unboundedAtZero
    (trajectory.hasBoundedRepeatedSinkingDepths_of_noDerivedRepeat
      hg hnormal hground hinitial hexposureBound chain hnoRepeat)
    hunboundedAtZero

end WindowedPivotTrajectory

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
