module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerUniformBounds
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window

@[expose]
public section

/-!
# A count-independent `M₂` bound for marker extensions

The operational `M₂` theorem may be applied inside any critical-marker
extension, but the marker-stable stair requires one growth function for all
marker counts.  This file dominates every numerical component of the
extension's `M₂` constant by a formula using only the original grammar's
maximum rank and `max rhsNodeBound 1`.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Closed count-independent depth envelope for a symbolic run. -/
@[expose] public def criticalMarkerResidualUnfoldingDepthBound
    (g : EncodedFirstOrderGrammar Action)
    (steps initial : ℕ) : ℕ :=
  steps * g.criticalMarkerRhsNodeBound + initial

public theorem withCriticalMarkers_residualUnfoldingDepthBound_le
    (g : EncodedFirstOrderGrammar Action)
    (count steps initial : ℕ) :
    (g.withCriticalMarkers count).residualUnfoldingDepthBound
        steps initial ≤
      g.criticalMarkerResidualUnfoldingDepthBound steps initial := by
  rw [residualUnfoldingDepthBound_eq]
  unfold criticalMarkerResidualUnfoldingDepthBound
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left steps
      (g.withCriticalMarkers_rhsNodeBound_le count)) initial

omit [DecidableEq Action] in
public theorem criticalMarkerResidualUnfoldingDepthBound_mono_steps
    (g : EncodedFirstOrderGrammar Action)
    {steps steps' initial : ℕ} (hsteps : steps ≤ steps') :
    g.criticalMarkerResidualUnfoldingDepthBound steps initial ≤
      g.criticalMarkerResidualUnfoldingDepthBound steps' initial := by
  unfold criticalMarkerResidualUnfoldingDepthBound
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right g.criticalMarkerRhsNodeBound hsteps) initial

@[expose] public def criticalMarkerStructuredPivotSwitchDepthBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  g.criticalMarkerResidualUnfoldingDepthBound bound
      (FiniteHead.compiledDepthBound (g.ranks.foldr max 0) 1) + 1

@[expose] public def criticalMarkerStructuredPivotCloseBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  g.criticalMarkerStructuredPivotSwitchDepthBound bound * bound

@[expose] public def criticalMarkerStructuredPivotShortPrefixBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  bound + g.criticalMarkerStructuredPivotCloseBound bound

@[expose] public def criticalMarkerStructuredPivotPreludeDepthBound
    (g : EncodedFirstOrderGrammar Action) (short : ℕ) : ℕ :=
  g.criticalMarkerResidualUnfoldingDepthBound short
    (FiniteHead.compiledDepthBound (g.ranks.foldr max 0) 1)

@[expose] public def criticalMarkerStructuredPivotSinkDepth
    (g : EncodedFirstOrderGrammar Action) (short : ℕ) : ℕ :=
  g.criticalMarkerStructuredPivotPreludeDepthBound short + 1

/-- Original-grammar envelope for the full marker-extension `M₂` constant. -/
@[expose] public def criticalMarkerStructuredPivotM2Bound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  let short := g.criticalMarkerStructuredPivotShortPrefixBound bound
  short + g.criticalMarkerStructuredPivotSinkDepth short * bound

public theorem withCriticalMarkers_structuredPivotSwitchDepthBound_le
    (g : EncodedFirstOrderGrammar Action) (count bound : ℕ) :
    (g.withCriticalMarkers count).structuredPivotSwitchDepthBound bound ≤
      g.criticalMarkerStructuredPivotSwitchDepthBound bound := by
  unfold structuredPivotSwitchDepthBound
    criticalMarkerStructuredPivotSwitchDepthBound
  rw [g.withCriticalMarkers_rankMax count]
  exact Nat.add_le_add_right
    (g.withCriticalMarkers_residualUnfoldingDepthBound_le count bound
      (FiniteHead.compiledDepthBound (g.ranks.foldr max 0) 1)) 1

public theorem withCriticalMarkers_structuredPivotCloseBound_le
    (g : EncodedFirstOrderGrammar Action) (count bound : ℕ) :
    (g.withCriticalMarkers count).structuredPivotCloseBound bound ≤
      g.criticalMarkerStructuredPivotCloseBound bound := by
  unfold structuredPivotCloseBound criticalMarkerStructuredPivotCloseBound
  exact Nat.mul_le_mul_right bound
    (g.withCriticalMarkers_structuredPivotSwitchDepthBound_le count bound)

public theorem withCriticalMarkers_structuredPivotShortPrefixBound_le
    (g : EncodedFirstOrderGrammar Action) (count bound : ℕ) :
    (g.withCriticalMarkers count).structuredPivotShortPrefixBound bound ≤
      g.criticalMarkerStructuredPivotShortPrefixBound bound := by
  unfold structuredPivotShortPrefixBound
    criticalMarkerStructuredPivotShortPrefixBound
  exact Nat.add_le_add_left
    (g.withCriticalMarkers_structuredPivotCloseBound_le count bound) bound

public theorem withCriticalMarkers_structuredPivotPreludeDepthBound_le
    (g : EncodedFirstOrderGrammar Action) (count bound : ℕ) :
    (g.withCriticalMarkers count).structuredPivotPreludeDepthBound
        ((g.withCriticalMarkers count).structuredPivotShortPrefixBound bound) ≤
      g.criticalMarkerStructuredPivotPreludeDepthBound
        (g.criticalMarkerStructuredPivotShortPrefixBound bound) := by
  unfold structuredPivotPreludeDepthBound
    criticalMarkerStructuredPivotPreludeDepthBound
  rw [g.withCriticalMarkers_rankMax count]
  exact
    (g.withCriticalMarkers_residualUnfoldingDepthBound_le count
      ((g.withCriticalMarkers count).structuredPivotShortPrefixBound bound)
      (FiniteHead.compiledDepthBound (g.ranks.foldr max 0) 1)).trans
      (g.criticalMarkerResidualUnfoldingDepthBound_mono_steps
        (g.withCriticalMarkers_structuredPivotShortPrefixBound_le
          count bound))

public theorem withCriticalMarkers_structuredPivotSinkDepth_le
    (g : EncodedFirstOrderGrammar Action) (count bound : ℕ) :
    (g.withCriticalMarkers count).structuredPivotSinkDepth
        ((g.withCriticalMarkers count).structuredPivotShortPrefixBound bound) ≤
      g.criticalMarkerStructuredPivotSinkDepth
        (g.criticalMarkerStructuredPivotShortPrefixBound bound) := by
  unfold structuredPivotSinkDepth criticalMarkerStructuredPivotSinkDepth
  exact Nat.add_le_add_right
    (g.withCriticalMarkers_structuredPivotPreludeDepthBound_le count bound) 1

/-- The concrete `M₂` constant of every marker extension is bounded by one
constant computed from the original grammar. -/
public theorem withCriticalMarkers_structuredPivotM2Bound_le
    (g : EncodedFirstOrderGrammar Action) (count bound : ℕ) :
    (g.withCriticalMarkers count).structuredPivotM2Bound bound ≤
      g.criticalMarkerStructuredPivotM2Bound bound := by
  unfold structuredPivotM2Bound structuredPivotM2Window
    criticalMarkerStructuredPivotM2Bound
  dsimp
  exact Nat.add_le_add
    (g.withCriticalMarkers_structuredPivotShortPrefixBound_le count bound)
    (Nat.mul_le_mul_right bound
      (g.withCriticalMarkers_structuredPivotSinkDepth_le count bound))

end EncodedFirstOrderGrammar

end DCFEquivalence
