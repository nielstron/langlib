module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerStructuredPivotStairAssembly

@[expose]
public section

/-!
# Count-independent numerical bounds for critical-marker extensions

Fresh critical markers are nullary and their only right-hand side is a
one-node self-loop.  Thus they preserve the maximum grammar rank and increase
the maximum right-hand-side graph size by at most one.  This file propagates
those two facts through the residual-size recurrences used by fixed-tail and
balancing presentations.  Every resulting envelope depends only on the
original grammar, never on the number of fresh markers.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private theorem foldr_max_map_le
    {α : Type} (xs : List α) (f : α → ℕ) (bound : ℕ)
    (hbound : ∀ x ∈ xs, f x ≤ bound) :
    (xs.map f).foldr max 0 ≤ bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact max_le (hbound x (by simp))
        (ih (fun y hy => hbound y (by simp [hy])))

/-- Marker rules have one-node right-hand sides, so the extension's raw RHS
bound is at most the maximum of the original bound and one. -/
public theorem withCriticalMarkers_rhsNodeBound_le
    (g : EncodedFirstOrderGrammar Action) (count : ℕ) :
    (g.withCriticalMarkers count).rhsNodeBound ≤
      max g.rhsNodeBound 1 := by
  unfold rhsNodeBound
  apply foldr_max_map_le
  intro rule hrule
  rw [withCriticalMarkers_rawRules, List.mem_append] at hrule
  rcases hrule with hlifted | hmarker
  · obtain ⟨originalRule, horiginal, rfl⟩ := List.mem_map.mp hlifted
    change originalRule.rhs.nodes.length ≤ max g.rhsNodeBound 1
    have horiginalLe : originalRule.rhs.nodes.length ≤
        g.rhsNodeBound := by
      unfold rhsNodeBound
      exact List.le_max_of_le
        (List.mem_map.mpr ⟨originalRule, horiginal, rfl⟩)
        (le_refl _)
    exact horiginalLe.trans (Nat.le_max_left _ _)
  · obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hmarker
    simp [criticalMarkerRule, RawRule.rhs, criticalMarker,
      RegularTerm.nodes]

/-- RHS-size parameter used by every count-independent marker envelope. -/
@[expose] public def criticalMarkerRhsNodeBound
    (g : EncodedFirstOrderGrammar Action) : ℕ :=
  max g.rhsNodeBound 1

/-- Count-independent analogue of `residualNodeBound`. -/
@[expose] public def criticalMarkerResidualNodeBound
    (g : EncodedFirstOrderGrammar Action) : ℕ → ℕ → ℕ
  | 0, initial => initial
  | steps + 1, initial =>
      g.criticalMarkerResidualNodeBound steps
        (g.criticalMarkerRhsNodeBound +
          (g.ranks.foldr max 0) * initial)

/-- Count-independent analogue of the step-monotone residual envelope. -/
@[expose] public def criticalMarkerResidualNodeEnvelope
    (g : EncodedFirstOrderGrammar Action) : ℕ → ℕ → ℕ
  | 0, initial => initial
  | steps + 1, initial =>
      max (g.criticalMarkerResidualNodeEnvelope steps initial)
        (g.criticalMarkerRhsNodeBound +
          (g.ranks.foldr max 0) *
            g.criticalMarkerResidualNodeEnvelope steps initial)

/-- The marker residual recurrence is monotone in its initial graph bound. -/
public theorem criticalMarkerResidualNodeBound_mono_initial
    (g : EncodedFirstOrderGrammar Action)
    {steps initial initial' : ℕ} (hinitial : initial ≤ initial') :
    g.criticalMarkerResidualNodeBound steps initial ≤
      g.criticalMarkerResidualNodeBound steps initial' := by
  induction steps generalizing initial initial' with
  | zero => exact hinitial
  | succ steps ih =>
      simp only [criticalMarkerResidualNodeBound]
      apply ih
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left (g.ranks.foldr max 0) hinitial)
        g.criticalMarkerRhsNodeBound

/-- Every raw residual bound in any marker extension is below the original
grammar's marker envelope. -/
public theorem withCriticalMarkers_residualNodeBound_le
    (g : EncodedFirstOrderGrammar Action) (count steps initial : ℕ) :
    (g.withCriticalMarkers count).residualNodeBound steps initial ≤
      g.criticalMarkerResidualNodeBound steps initial := by
  induction steps generalizing initial with
  | zero => exact le_refl _
  | succ steps ih =>
      simp only [residualNodeBound, criticalMarkerResidualNodeBound]
      apply (ih _).trans
      apply g.criticalMarkerResidualNodeBound_mono_initial
      rw [withCriticalMarkers_rankMax]
      exact Nat.add_le_add
        (g.withCriticalMarkers_rhsNodeBound_le count)
        (le_refl _)

/-- Every step-monotone residual envelope in any marker extension is below
the corresponding original-grammar envelope. -/
public theorem withCriticalMarkers_residualNodeEnvelope_le
    (g : EncodedFirstOrderGrammar Action) (count steps initial : ℕ) :
    (g.withCriticalMarkers count).residualNodeEnvelope steps initial ≤
      g.criticalMarkerResidualNodeEnvelope steps initial := by
  induction steps with
  | zero => exact le_refl _
  | succ steps ih =>
      simp only [residualNodeEnvelope, criticalMarkerResidualNodeEnvelope]
      apply max_le_max ih
      rw [withCriticalMarkers_rankMax]
      exact Nat.add_le_add
        (g.withCriticalMarkers_rhsNodeBound_le count)
        (Nat.mul_le_mul_left (g.ranks.foldr max 0) ih)

/-- The marker residual envelope is monotone in its initial graph bound. -/
public theorem criticalMarkerResidualNodeEnvelope_mono_initial
    (g : EncodedFirstOrderGrammar Action)
    {steps initial initial' : ℕ} (hinitial : initial ≤ initial') :
    g.criticalMarkerResidualNodeEnvelope steps initial ≤
      g.criticalMarkerResidualNodeEnvelope steps initial' := by
  induction steps with
  | zero => exact hinitial
  | succ steps ih =>
      simp only [criticalMarkerResidualNodeEnvelope]
      exact max_le_max ih
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left (g.ranks.foldr max 0) ih)
          g.criticalMarkerRhsNodeBound)

omit [DecidableEq Action] in
/-- `depthPrefixTailBound` depends on a rank table only through its maximum
rank. -/
public theorem RegularTerm.depthPrefixTailBound_congr_rankMax
    {ranks ranks' : List ℕ}
    (hrank : ranks.foldr max 0 = ranks'.foldr max 0) (depth : ℕ) :
    RegularTerm.depthPrefixTailBound ranks depth =
      RegularTerm.depthPrefixTailBound ranks' depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [RegularTerm.depthPrefixTailBound, hrank, ih]

/-- Adding critical markers leaves the fixed-tail width bound unchanged. -/
public theorem withCriticalMarkers_fixedTailWidthBound
    (g : EncodedFirstOrderGrammar Action) (count depth : ℕ) :
    (g.withCriticalMarkers count).fixedTailWidthBound depth =
      g.fixedTailWidthBound depth := by
  unfold fixedTailWidthBound
  exact RegularTerm.depthPrefixTailBound_congr_rankMax
    (g.withCriticalMarkers_rankMax count) depth

/-- Adding critical markers leaves the fixed-tail padded arity unchanged. -/
public theorem withCriticalMarkers_fixedTailArityBound
    (g : EncodedFirstOrderGrammar Action) (count depth : ℕ) :
    (g.withCriticalMarkers count).fixedTailArityBound depth =
      g.fixedTailArityBound depth := by
  unfold fixedTailArityBound
  rw [g.withCriticalMarkers_fixedTailWidthBound count depth,
    g.withCriticalMarkers_rankMax count]

/-- Count-independent fixed-tail schema-size envelope. -/
@[expose] public def criticalMarkerFixedTailSchemaBound
    (g : EncodedFirstOrderGrammar Action)
    (depth actionBound : ℕ) : ℕ :=
  g.criticalMarkerResidualNodeEnvelope actionBound
    (FiniteHead.compiledDepthBound
      (g.ranks.foldr max 0) depth)

/-- Every marker-extension fixed-tail schema bound is below the original
grammar's count-independent envelope. -/
public theorem withCriticalMarkers_fixedTailSchemaBound_le
    (g : EncodedFirstOrderGrammar Action)
    (count depth actionBound : ℕ) :
    (g.withCriticalMarkers count).fixedTailSchemaBound depth actionBound ≤
      g.criticalMarkerFixedTailSchemaBound depth actionBound := by
  unfold fixedTailSchemaBound criticalMarkerFixedTailSchemaBound
  rw [g.withCriticalMarkers_rankMax count]
  exact g.withCriticalMarkers_residualNodeEnvelope_le
    count actionBound
      (FiniteHead.compiledDepthBound (g.ranks.foldr max 0) depth)

/-- Count-independent presentation envelope for a fixed-argument balancing
row in a marker extension. -/
@[expose] public def criticalMarkerFixedBalancingPresentationBound
    (g : EncodedFirstOrderGrammar Action)
    (segmentBound arity schemaBound : ℕ) : ℕ :=
  max arity
    (max
      (g.criticalMarkerResidualNodeBound segmentBound
          (FiniteHead.compiledDepthBound
            (g.ranks.foldr max 0) 1) +
        (g.ranks.foldr max 0) *
          (g.criticalMarkerResidualNodeEnvelope
            segmentBound schemaBound + 1))
      (g.criticalMarkerResidualNodeBound segmentBound schemaBound))

/-- Every marker-extension balancing presentation bound is below the
original grammar's count-independent envelope. -/
public theorem withCriticalMarkers_fixedBalancingPresentationBound_le
    (g : EncodedFirstOrderGrammar Action)
    (count segmentBound arity schemaBound : ℕ) :
    (g.withCriticalMarkers count).fixedBalancingPresentationBound
        segmentBound arity schemaBound ≤
      g.criticalMarkerFixedBalancingPresentationBound
        segmentBound arity schemaBound := by
  unfold fixedBalancingPresentationBound
    criticalMarkerFixedBalancingPresentationBound
  rw [g.withCriticalMarkers_rankMax count]
  apply max_le_max (le_refl _)
  apply max_le_max
  · exact Nat.add_le_add
      (g.withCriticalMarkers_residualNodeBound_le count segmentBound
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) 1))
      (Nat.mul_le_mul_left (g.ranks.foldr max 0)
        (Nat.add_le_add_right
          (g.withCriticalMarkers_residualNodeEnvelope_le
            count segmentBound schemaBound) 1))
  · exact g.withCriticalMarkers_residualNodeBound_le
      count segmentBound schemaBound

/-- Increasing only the external arity increases the uniform marker
presentation envelope. -/
public theorem criticalMarkerFixedBalancingPresentationBound_mono_arity
    (g : EncodedFirstOrderGrammar Action)
    (segmentBound schemaBound : ℕ) {arity arity' : ℕ}
    (harity : arity ≤ arity') :
    g.criticalMarkerFixedBalancingPresentationBound
        segmentBound arity schemaBound ≤
      g.criticalMarkerFixedBalancingPresentationBound
        segmentBound arity' schemaBound := by
  unfold criticalMarkerFixedBalancingPresentationBound
  exact max_le_max harity (le_refl _)

/-- Increasing the supplied fixed-tail schema envelope increases the uniform
marker presentation bound. -/
public theorem criticalMarkerFixedBalancingPresentationBound_mono_schema
    (g : EncodedFirstOrderGrammar Action)
    (segmentBound arity : ℕ) {schemaBound schemaBound' : ℕ}
    (hschema : schemaBound ≤ schemaBound') :
    g.criticalMarkerFixedBalancingPresentationBound
        segmentBound arity schemaBound ≤
      g.criticalMarkerFixedBalancingPresentationBound
        segmentBound arity schemaBound' := by
  unfold criticalMarkerFixedBalancingPresentationBound
  apply max_le_max (le_refl _)
  apply max_le_max
  · exact Nat.add_le_add_left
      (Nat.mul_le_mul_left (g.ranks.foldr max 0)
        (Nat.add_le_add_right
          (g.criticalMarkerResidualNodeEnvelope_mono_initial
            (steps := segmentBound) hschema) 1))
      (g.criticalMarkerResidualNodeBound segmentBound
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) 1))
  · exact g.criticalMarkerResidualNodeBound_mono_initial
      (steps := segmentBound) hschema

/-- The complete fixed-tail presentation bound of every marker extension is
dominated by one bound computed solely from the original grammar. -/
public theorem withCriticalMarkers_fixedTailBalancingPresentationBound_le
    (g : EncodedFirstOrderGrammar Action)
    (count segmentBound depth actionBound : ℕ) :
    (g.withCriticalMarkers count).fixedBalancingPresentationBound
        segmentBound
        ((g.withCriticalMarkers count).fixedTailArityBound depth)
        ((g.withCriticalMarkers count).fixedTailSchemaBound depth actionBound) ≤
      g.criticalMarkerFixedBalancingPresentationBound
        segmentBound
        (g.fixedTailArityBound depth)
        (g.criticalMarkerFixedTailSchemaBound depth actionBound) := by
  rw [g.withCriticalMarkers_fixedTailArityBound count depth]
  exact
    (g.withCriticalMarkers_fixedBalancingPresentationBound_le
      count segmentBound (g.fixedTailArityBound depth)
        ((g.withCriticalMarkers count).fixedTailSchemaBound depth actionBound)).trans
      (g.criticalMarkerFixedBalancingPresentationBound_mono_schema
        segmentBound (g.fixedTailArityBound depth)
        (g.withCriticalMarkers_fixedTailSchemaBound_le
          count depth actionBound))

end EncodedFirstOrderGrammar

end DCFEquivalence
