module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaBalancingSchemaComposition

@[expose]
public section

/-!
# Uniform graph-size bounds for fixed-argument balancing

The raw residual recurrence is monotone in its initial graph bound, but it
need not be monotone in the number of steps when every grammar rank is zero.
The envelope below explicitly retains every earlier bound.  It is therefore
monotone in both parameters and uniformly bounds all shorter successor runs.

These arithmetic facts give a presentation-size bound for the family of
fixed-argument pivot residuals and for the active schema obtained by
substituting that family.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A step-monotone envelope for `residualNodeBound`. -/
@[expose] public def residualNodeEnvelope
    (g : EncodedFirstOrderGrammar Action) : ℕ → ℕ → ℕ
  | 0, initial => initial
  | steps + 1, initial =>
      max (g.residualNodeEnvelope steps initial)
        (g.rhsNodeBound +
          (g.ranks.foldr max 0) *
            g.residualNodeEnvelope steps initial)

/-- The raw residual recurrence is monotone in its initial graph bound. -/
public theorem residualNodeBound_mono_initial
    (g : EncodedFirstOrderGrammar Action)
    {steps initial initial' : ℕ} (hinitial : initial ≤ initial') :
    g.residualNodeBound steps initial ≤
      g.residualNodeBound steps initial' := by
  induction steps generalizing initial initial' with
  | zero =>
      simpa [residualNodeBound] using hinitial
  | succ steps ih =>
      simp only [residualNodeBound]
      apply ih
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left
          (g.ranks.foldr max 0) hinitial)
        g.rhsNodeBound

/-- Successor unfolding of the raw recurrence, with the affine update moved
outside the preceding iterations. -/
public theorem residualNodeBound_succ
    (g : EncodedFirstOrderGrammar Action)
    (steps initial : ℕ) :
    g.residualNodeBound (steps + 1) initial =
      g.rhsNodeBound +
        (g.ranks.foldr max 0) *
          g.residualNodeBound steps initial := by
  induction steps generalizing initial with
  | zero => simp [residualNodeBound]
  | succ steps ih =>
      change
        g.residualNodeBound (steps + 1)
            (g.rhsNodeBound +
              (g.ranks.foldr max 0) * initial) =
          g.rhsNodeBound +
            (g.ranks.foldr max 0) *
              g.residualNodeBound steps
                (g.rhsNodeBound +
                  (g.ranks.foldr max 0) * initial)
      exact ih _

/-- The monotone envelope is itself monotone in the initial graph bound. -/
public theorem residualNodeEnvelope_mono_initial
    (g : EncodedFirstOrderGrammar Action)
    {steps initial initial' : ℕ} (hinitial : initial ≤ initial') :
    g.residualNodeEnvelope steps initial ≤
      g.residualNodeEnvelope steps initial' := by
  induction steps with
  | zero =>
      simpa [residualNodeEnvelope] using hinitial
  | succ steps ih =>
      simp only [residualNodeEnvelope]
      exact max_le_max ih
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left
            (g.ranks.foldr max 0) ih)
          g.rhsNodeBound)

/-- Increasing the step budget by one can only increase the envelope. -/
public theorem residualNodeEnvelope_le_succ
    (g : EncodedFirstOrderGrammar Action)
    (steps initial : ℕ) :
    g.residualNodeEnvelope steps initial ≤
      g.residualNodeEnvelope (steps + 1) initial := by
  simp only [residualNodeEnvelope]
  exact Nat.le_max_left _ _

/-- The envelope is monotone in the step budget. -/
public theorem residualNodeEnvelope_mono_steps
    (g : EncodedFirstOrderGrammar Action)
    {steps steps' initial : ℕ} (hsteps : steps ≤ steps') :
    g.residualNodeEnvelope steps initial ≤
      g.residualNodeEnvelope steps' initial := by
  induction steps', hsteps using Nat.le_induction with
  | base => exact le_refl _
  | succ steps' hsteps' ih =>
      exact ih.trans
        (g.residualNodeEnvelope_le_succ steps' initial)

/-- Every raw residual bound is below its step-monotone envelope. -/
public theorem residualNodeBound_le_residualNodeEnvelope
    (g : EncodedFirstOrderGrammar Action)
    (steps initial : ℕ) :
    g.residualNodeBound steps initial ≤
      g.residualNodeEnvelope steps initial := by
  induction steps with
  | zero => exact le_refl _
  | succ steps ih =>
      rw [g.residualNodeBound_succ]
      simp only [residualNodeEnvelope]
      exact (Nat.add_le_add_left
        (Nat.mul_le_mul_left
          (g.ranks.foldr max 0) ih)
        g.rhsNodeBound).trans
          (Nat.le_max_right _ _)

/-- A raw run with smaller step and initial bounds fits in a single envelope. -/
public theorem residualNodeBound_le_residualNodeEnvelope_of_le
    (g : EncodedFirstOrderGrammar Action)
    {steps steps' initial initial' : ℕ}
    (hsteps : steps ≤ steps') (hinitial : initial ≤ initial') :
    g.residualNodeBound steps initial ≤
      g.residualNodeEnvelope steps' initial' := by
  exact (g.residualNodeBound_le_residualNodeEnvelope steps initial).trans
    ((g.residualNodeEnvelope_mono_steps hsteps).trans
      (g.residualNodeEnvelope_mono_initial hinitial))

/-- One numerical bound simultaneously covering the external arity and both
schemas in a fixed-argument balancing result. -/
@[expose] public def fixedBalancingPresentationBound
    (g : EncodedFirstOrderGrammar Action)
    (segmentBound arity schemaBound : ℕ) : ℕ :=
  max arity
    (max
      (g.residualNodeBound segmentBound
          (FiniteHead.compiledDepthBound
            (g.ranks.foldr max 0) 1) +
        (g.ranks.foldr max 0) *
          (g.residualNodeEnvelope segmentBound schemaBound + 1))
      (g.residualNodeBound segmentBound schemaBound))

/-- The fixed external arity is included in the common presentation bound. -/
public theorem le_fixedBalancingPresentationBound_arity
    (g : EncodedFirstOrderGrammar Action)
    (segmentBound arity schemaBound : ℕ) :
    arity ≤
      g.fixedBalancingPresentationBound
        segmentBound arity schemaBound := by
  exact Nat.le_max_left _ _

namespace BalancingSegment.SchemaExposedSuccessorFamily

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {initialLeft initialRight : RegularTerm}
  {stem : List (Label Action)} {filler : RegularTerm}
  {children : List ℕ} {pivotSchema : RegularTerm}
  {arguments : List RegularTerm} {arity width : ℕ}

private theorem list_sum_le_length_mul
    (values : List ℕ) (sizeBound : ℕ)
    (hbound : ∀ value ∈ values, value ≤ sizeBound) :
    values.sum ≤ values.length * sizeBound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.sum_cons, List.length_cons]
      have hhead := hbound value (by simp)
      have htail := ih (fun tail htail =>
        hbound tail (by simp [htail]))
      rw [Nat.succ_mul]
      simpa [Nat.add_comm] using Nat.add_le_add htail hhead

/-- Every fixed-argument pivot residual fits the uniform shorter-run
envelope, once the incoming pivot schema has a numerical graph bound. -/
public theorem pivotResiduals_nodes_length_le
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    {schemaBound : ℕ}
    (hpivotSchema : pivotSchema.nodes.length ≤ schemaBound) :
    ∀ residual ∈ family.pivotResiduals,
      residual.nodes.length ≤
        g.residualNodeEnvelope bound schemaBound := by
  intro residual hresidual
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hresidual
  let index : Fin children.length := ⟨i, by
    simpa [family.pivotResiduals_length] using hi⟩
  have hresidualEq :
      residual = (family.row index).pivotResidual := by
    exact hget.symm.trans (family.pivotResiduals_getElem index)
  rw [hresidualEq]
  exact (family.row index).pivot_size_le.trans
    (g.residualNodeBound_le_residualNodeEnvelope_of_le
      (Nat.le_of_lt (family.row index).word_length_lt)
      hpivotSchema)

/-- The total graph size of all fixed-argument pivot residuals is bounded by
the family cardinality times the uniform shorter-run envelope. -/
public theorem pivotResiduals_nodes_sum_le
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    {schemaBound : ℕ}
    (hpivotSchema : pivotSchema.nodes.length ≤ schemaBound) :
    (family.pivotResiduals.map
      fun residual => residual.nodes.length).sum ≤
        children.length *
          g.residualNodeEnvelope bound schemaBound := by
  have hsum := list_sum_le_length_mul
    (family.pivotResiduals.map
      fun residual => residual.nodes.length)
    (g.residualNodeEnvelope bound schemaBound)
    (by
      intro size hsize
      obtain ⟨residual, hresidual, rfl⟩ :=
        List.mem_map.mp hsize
      exact family.pivotResiduals_nodes_length_le
        hpivotSchema residual hresidual)
  simpa [family.pivotResiduals_length] using hsum

/-- Adding one-node dummy padding contributes exactly one graph node per
padding position. -/
public theorem pivotResiduals_variablePadding_nodes_sum_le
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    {schemaBound padding : ℕ}
    (hpivotSchema : pivotSchema.nodes.length ≤ schemaBound) :
    ((family.pivotResiduals ++
        List.replicate padding (RegularTerm.variableTerm 0)).map
      fun context => context.nodes.length).sum ≤
        children.length *
          g.residualNodeEnvelope bound schemaBound + padding := by
  rw [List.map_append, List.sum_append]
  apply Nat.add_le_add
  · exact family.pivotResiduals_nodes_sum_le hpivotSchema
  · simp

/-- Instantiating an arbitrary outer schema by the pivot residual family and
one-node padding has a uniform additive graph-size bound. -/
public theorem instantiate_pivotResiduals_variablePadding_nodes_length_le
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (outer : RegularTerm) {schemaBound padding : ℕ}
    (hpivotSchema : pivotSchema.nodes.length ≤ schemaBound) :
    (outer.instantiate
      (family.pivotResiduals ++
        List.replicate padding (RegularTerm.variableTerm 0))).nodes.length ≤
      outer.nodes.length +
        children.length *
          g.residualNodeEnvelope bound schemaBound + padding := by
  rw [RegularTerm.instantiate_nodes_length]
  simpa [Nat.add_assoc] using
    Nat.add_le_add_left
      (family.pivotResiduals_variablePadding_nodes_sum_le
        (padding := padding) hpivotSchema)
      outer.nodes.length

/-- The complete fixed-argument active composition has a grammar- and
schema-bound presentation size. -/
public theorem composedActiveSchema_nodes_length_le
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (activeResult : segment.ActivePrefixResidual filler)
    {schemaBound : ℕ}
    (hpivotSchema : pivotSchema.nodes.length ≤ schemaBound) :
    (family.composedActiveSchema activeResult).nodes.length ≤
      g.residualNodeBound bound
          (FiniteHead.compiledDepthBound
            (g.ranks.foldr max 0) 1) +
        (g.ranks.foldr max 0) *
          (g.residualNodeEnvelope bound schemaBound + 1) := by
  have hchildrenMax :
      children.length ≤ g.ranks.foldr max 0 := by
    have hrank : g.ranks[X]? = some children.length :=
      hactive.root_rank_arity hroot
    exact List.le_max_of_le
      (List.mem_of_getElem? hrank) (le_refl _)
  have hpadding :
      (active.depthPrefix 1).schemaArity g.ranks -
          children.length ≤
        g.ranks.foldr max 0 := by
    rw [family.active_schemaArity_eq_rankMax hactive hroot]
    exact Nat.sub_le _ _
  have hfamily :
      children.length *
          g.residualNodeEnvelope bound schemaBound +
        ((active.depthPrefix 1).schemaArity g.ranks -
          children.length) ≤
        (g.ranks.foldr max 0) *
          (g.residualNodeEnvelope bound schemaBound + 1) := by
    calc
      children.length *
            g.residualNodeEnvelope bound schemaBound +
          ((active.depthPrefix 1).schemaArity g.ranks -
            children.length)
          ≤ (g.ranks.foldr max 0) *
              g.residualNodeEnvelope bound schemaBound +
            (g.ranks.foldr max 0) :=
        Nat.add_le_add
          (Nat.mul_le_mul_right
            (g.residualNodeEnvelope bound schemaBound)
            hchildrenMax)
          hpadding
      _ = (g.ranks.foldr max 0) *
            (g.residualNodeEnvelope bound schemaBound + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
  have hcontexts :
      (family.activeCompositionContexts.map
        fun context => context.nodes.length).sum ≤
          (g.ranks.foldr max 0) *
            (g.residualNodeEnvelope bound schemaBound + 1) := by
    exact (family.pivotResiduals_variablePadding_nodes_sum_le
      (padding :=
        (active.depthPrefix 1).schemaArity g.ranks -
          children.length)
      hpivotSchema).trans hfamily
  rw [composedActiveSchema, RegularTerm.instantiate_nodes_length]
  apply Nat.add_le_add
  · simpa [activeResult.actions_length] using activeResult.size_le
  · exact hcontexts

/-- The composed active schema fits the common fixed-balancing presentation
bound, which also reserves room for the external arity and pivot side. -/
public theorem composedActiveSchema_nodes_length_le_fixedBalancingPresentationBound
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (activeResult : segment.ActivePrefixResidual filler)
    {schemaBound : ℕ}
    (hpivotSchema : pivotSchema.nodes.length ≤ schemaBound) :
    (family.composedActiveSchema activeResult).nodes.length ≤
      g.fixedBalancingPresentationBound bound arity schemaBound := by
  exact (family.composedActiveSchema_nodes_length_le
    hactive hroot activeResult hpivotSchema).trans
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))

end BalancingSegment.SchemaExposedSuccessorFamily

/-- The direct fixed-argument pivot residual is bounded monotonically by any
numerical bound on its input pivot schema. -/
public theorem BalancingSegment.SchemaPivotResidual.nodes_length_le
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {filler : RegularTerm}
    {activeResult : segment.ActivePrefixResidual filler}
    {pivotSchema : RegularTerm} {arguments : List RegularTerm}
    {arity width schemaBound : ℕ}
    (pivotResult : segment.SchemaPivotResidual activeResult
      pivotSchema arguments arity width)
    (hpivotSchema : pivotSchema.nodes.length ≤ schemaBound) :
    pivotResult.residual.nodes.length ≤
      g.residualNodeBound bound schemaBound := by
  exact pivotResult.size_le.trans
    (by
      rw [activeResult.actions_length]
      exact g.residualNodeBound_mono_initial hpivotSchema)

/-- The direct pivot residual fits the common fixed-balancing presentation
bound. -/
public theorem BalancingSegment.SchemaPivotResidual.nodes_length_le_fixedBalancingPresentationBound
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {filler : RegularTerm}
    {activeResult : segment.ActivePrefixResidual filler}
    {pivotSchema : RegularTerm} {arguments : List RegularTerm}
    {arity width schemaBound : ℕ}
    (pivotResult : segment.SchemaPivotResidual activeResult
      pivotSchema arguments arity width)
    (hpivotSchema : pivotSchema.nodes.length ≤ schemaBound) :
    pivotResult.residual.nodes.length ≤
      g.fixedBalancingPresentationBound bound arity schemaBound := by
  exact (pivotResult.nodes_length_le hpivotSchema).trans
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

end EncodedFirstOrderGrammar

end DCFEquivalence
