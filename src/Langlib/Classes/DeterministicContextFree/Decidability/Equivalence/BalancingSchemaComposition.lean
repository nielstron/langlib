module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingSuccessorFamily
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotPrefixResidual

@[expose]
public section

/-!
# Composed schemas of a balancing result

The active residual is a schema over the immediate active successors.  Each
such successor is replaced by the pivot residual selected by its fixed
exposing word.  Padding positions are filled by a sanitized constant context.
The resulting left schema and the direct pivot residual are both structurally
supported by the pivot depth-prefix tails.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace BalancingSegment.ExposedSuccessorFamily

/-- Context tuple plugged into the active residual: one pivot residual for
every immediate child, followed by inactive constant padding. -/
@[expose] public noncomputable def activeCompositionContexts
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)} {filler : RegularTerm}
    {children : List ℕ}
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children) : List RegularTerm :=
  family.pivotResiduals ++
    List.replicate
      ((active.depthPrefix 1).schemaArity g.ranks - children.length)
      (RegularTerm.variableTerm 0)

/-- The left regular schema of the balancing result. -/
@[expose] public noncomputable def composedActiveSchema
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)} {filler : RegularTerm}
    {children : List ℕ}
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (activeResult : segment.ActivePrefixResidual filler) : RegularTerm :=
  activeResult.residual.instantiate family.activeCompositionContexts

end BalancingSegment.ExposedSuccessorFamily

namespace BalancingSegment.ExposedSuccessorFamily

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {initialLeft initialRight : RegularTerm}
  {stem : List (Label Action)} {filler : RegularTerm}
  {children : List ℕ}

/-- A depth-one active prefix has padded arity equal to the greatest grammar
rank, because its genuine tails are exactly one root-successor tuple. -/
public theorem active_schemaArity_eq_rankMax
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children)) :
    (active.depthPrefix 1).schemaArity g.ranks =
      g.ranks.foldr max 0 := by
  have htails :=
    RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
  have hrank : g.ranks[X]? = some children.length :=
    hactive.root_rank_arity hroot
  have hchildrenMax :
      children.length ≤ g.ranks.foldr max 0 :=
    List.le_max_of_le (List.mem_of_getElem? hrank) (le_refl _)
  simp [DepthPrefix.schemaArity, htails,
    Nat.max_eq_right hchildrenMax]

public theorem activeCompositionContexts_length
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children)) :
    family.activeCompositionContexts.length =
      (active.depthPrefix 1).schemaArity g.ranks := by
  have harity := family.active_schemaArity_eq_rankMax hactive hroot
  have hrank : g.ranks[X]? = some children.length :=
    hactive.root_rank_arity hroot
  have hchildrenMax :
      children.length ≤ g.ranks.foldr max 0 :=
    List.le_max_of_le (List.mem_of_getElem? hrank) (le_refl _)
  simp [activeCompositionContexts,
    family.pivotResiduals_length, harity]
  omega

/-- Replacing the active successor prefix leaves precisely the original filler
padding in the concrete active argument tuple. -/
public theorem replaceArgumentPrefix_activeArguments
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hroot : active.rootApplication? = some (X, children)) :
    RegularTerm.replaceArgumentPrefix
        ((active.depthPrefix 1).paddedArguments g.ranks filler)
        family.pivotTargets =
      family.pivotTargets ++
        List.replicate
          ((active.depthPrefix 1).schemaArity g.ranks - children.length)
          filler := by
  have htails :=
    RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
  simp [RegularTerm.replaceArgumentPrefix,
    DepthPrefix.paddedArguments, htails,
    family.pivotTargets_length]

/-- The active symbolic residual retains the structural witness of the
immediate-successor prefix. -/
public theorem activeResidual_hasPrefixWitness
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed) (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (activeResult : segment.ActivePrefixResidual filler) :
    activeResult.residual.HasPrefixWitness children.length := by
  let decomposition := active.depthPrefix 1
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid active 1
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hactive 1
  have hwitness :
      decomposition.head.toRegularTerm.HasPrefixWitness
        decomposition.tails.length :=
    FiniteHead.toRegularTerm_hasPrefixWitness hvalid
  have hwellFormed :
      decomposition.head.toRegularTerm.WellFormed g.ranks
        (decomposition.schemaArity g.ranks) :=
    decomposition.head_wellFormed_schemaArity hvalid hranked
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  have hresidual :=
    hwitness.runActions hg hpadding hwellFormed
      (by simpa [decomposition] using activeResult.symbolic_run)
  have htails :=
    RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
  simpa [decomposition, htails] using hresidual

/-- Every context in the composed active tuple is well formed at the common
pivot-prefix arity. -/
public theorem activeCompositionContexts_wellFormed
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children)) :
    ∀ context ∈ family.activeCompositionContexts,
      context.WellFormed g.ranks
        ((pivot.depthPrefix bound).schemaArity g.ranks) := by
  intro context hcontext
  simp only [activeCompositionContexts,
    List.mem_append] at hcontext
  rcases hcontext with hresidual | hpaddingContext
  · exact family.pivotResiduals_wellFormed context hresidual
  · have hcontextEq : context = RegularTerm.variableTerm 0 := by
      simpa using (List.eq_of_mem_replicate hpaddingContext)
    subst context
    have hpaddingCount :
        0 <
          (active.depthPrefix 1).schemaArity g.ranks -
            children.length := by
      have hnonempty :=
        List.ne_nil_of_mem hpaddingContext
      apply Nat.pos_of_ne_zero
      simpa using hnonempty
    have harity := family.active_schemaArity_eq_rankMax hactive hroot
    have hpivotArity :
        g.ranks.foldr max 0 ≤
          (pivot.depthPrefix bound).schemaArity g.ranks := by
      exact Nat.le_max_right _ _
    have hpositive :
        1 ≤ (pivot.depthPrefix bound).schemaArity g.ranks := by
      omega
    exact RegularTerm.variableTerm_wellFormed hpositive

/-- The composed active schema is structurally supported by the genuine pivot
tails. -/
public theorem composedActiveSchema_supported
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed) (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (activeResult : segment.ActivePrefixResidual filler) :
    (family.composedActiveSchema activeResult).SupportedByPrefix
      g.ranks ((pivot.depthPrefix bound).schemaArity g.ranks)
      (pivot.depthPrefix bound).tails.length := by
  let contexts := family.activeCompositionContexts
  have hcontextsLength :
      contexts.length =
        (active.depthPrefix 1).schemaArity g.ranks := by
    exact family.activeCompositionContexts_length hactive hroot
  have houterWellFormed :
      activeResult.residual.WellFormed g.ranks contexts.length := by
    rw [hcontextsLength]
    exact activeResult.supported.1
  have hcontextsWellFormed :
      ∀ context ∈ contexts,
        context.WellFormed g.ranks
          ((pivot.depthPrefix bound).schemaArity g.ranks) := by
    exact family.activeCompositionContexts_wellFormed
      hactive hroot
  have hcontextsWitness :
      ∀ x, x < children.length →
        ∃ context,
          contexts[x]? = some context ∧
            context.HasPrefixWitness
              (pivot.depthPrefix bound).tails.length := by
    intro x hx
    let index : Fin children.length := ⟨x, hx⟩
    refine ⟨(family.row index).pivotResidual, ?_, ?_⟩
    · have hpivotBound : x < family.pivotResiduals.length := by
        simpa using hx
      calc
        contexts[x]? = family.pivotResiduals[x]? := by
          exact List.getElem?_append_left hpivotBound
        _ = some family.pivotResiduals[x] :=
          List.getElem?_eq_getElem hpivotBound
        _ = some (family.row index).pivotResidual := by
          exact congrArg some (family.pivotResiduals_getElem index)
    · exact family.row_pivotResidual_hasPrefixWitness hg hpivot index
  have hsourceWitness :=
    family.activeResidual_hasPrefixWitness hg hactive hroot activeResult
  have hcontextsArity :
      contexts.length ≤
        (pivot.depthPrefix bound).schemaArity g.ranks := by
    rw [hcontextsLength,
      family.active_schemaArity_eq_rankMax hactive hroot]
    exact Nat.le_max_right _ _
  have hwidthArity :
      (pivot.depthPrefix bound).tails.length ≤
        (pivot.depthPrefix bound).schemaArity g.ranks :=
    Nat.le_max_left _ _
  exact hsourceWitness.instantiate_supportedByPrefix
    houterWellFormed hcontextsWellFormed hcontextsWitness
    hcontextsArity hwidthArity

/-- Structural witness underlying `composedActiveSchema_supported`. -/
public theorem composedActiveSchema_hasPrefixWitness
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed) (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (activeResult : segment.ActivePrefixResidual filler) :
    (family.composedActiveSchema activeResult).HasPrefixWitness
      (pivot.depthPrefix bound).tails.length := by
  let contexts := family.activeCompositionContexts
  have hcontextsClosed :
      ∀ context ∈ contexts, context.ReferenceClosed := by
    intro context hcontext
    exact RegularTerm.referenceClosed_of_wellFormed
      (family.activeCompositionContexts_wellFormed
        hactive hroot context hcontext)
  have hcontextsWitness :
      ∀ x, x < children.length →
        ∃ context,
          contexts[x]? = some context ∧
            context.HasPrefixWitness
              (pivot.depthPrefix bound).tails.length := by
    intro x hx
    let index : Fin children.length := ⟨x, hx⟩
    refine ⟨(family.row index).pivotResidual, ?_, ?_⟩
    · have hpivotBound : x < family.pivotResiduals.length := by
        simpa using hx
      calc
        contexts[x]? = family.pivotResiduals[x]? := by
          exact List.getElem?_append_left hpivotBound
        _ = some family.pivotResiduals[x] :=
          List.getElem?_eq_getElem hpivotBound
        _ = some (family.row index).pivotResidual := by
          exact congrArg some (family.pivotResiduals_getElem index)
    · exact family.row_pivotResidual_hasPrefixWitness hg hpivot index
  obtain ⟨support, hsupport⟩ :=
    family.activeResidual_hasPrefixWitness hg hactive hroot activeResult
  exact hsupport.instantiate
    (RegularTerm.referenceClosed_of_wellFormed activeResult.supported.1)
    hcontextsClosed hcontextsWitness

/-- The direct pivot residual has the matching structural witness. -/
public theorem pivotResidual_hasPrefixWitness
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed) (hpivot : pivot.Ground g.ranks)
    (activeResult : segment.ActivePrefixResidual filler)
    (pivotResult : segment.PivotPrefixResidual filler activeResult) :
    pivotResult.residual.HasPrefixWitness
      (pivot.depthPrefix bound).tails.length := by
  let decomposition := pivot.depthPrefix bound
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid pivot bound
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hpivot bound
  have hwitness :
      decomposition.head.toRegularTerm.HasPrefixWitness
        decomposition.tails.length :=
    FiniteHead.toRegularTerm_hasPrefixWitness hvalid
  have hwellFormed :
      decomposition.head.toRegularTerm.WellFormed g.ranks
        (decomposition.schemaArity g.ranks) :=
    decomposition.head_wellFormed_schemaArity hvalid hranked
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  exact hwitness.runActions hg hpadding hwellFormed
    (by simpa [decomposition] using pivotResult.symbolic_run)

/-- The composed context tuple and the concrete replacement tuple agree on
every active immediate-successor slot.  Inactive padding is deliberately
ignored. -/
public theorem composedActiveContexts_equivalentThrough
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children) :
    RegularTerm.ArgumentsEquivalentThrough children.length
      (RegularTerm.composedContexts family.activeCompositionContexts
        ((pivot.depthPrefix bound).paddedArguments g.ranks filler))
      (family.pivotTargets ++
        List.replicate
          ((active.depthPrefix 1).schemaArity g.ranks - children.length)
          filler) := by
  let pivotArguments :=
    (pivot.depthPrefix bound).paddedArguments g.ranks filler
  intro i hi
  let index : Fin children.length := ⟨i, hi⟩
  refine ⟨(family.row index).pivotResidual.instantiate pivotArguments,
    (family.row index).pivotTarget, ?_, ?_, ?_⟩
  · have hresidualBound : i < family.pivotResiduals.length := by
      simpa using hi
    have hmappedBound :
        i <
          (family.pivotResiduals.map fun residual =>
            residual.instantiate pivotArguments).length := by
      simpa using hresidualBound
    calc
      (RegularTerm.composedContexts family.activeCompositionContexts
          pivotArguments)[i]? =
          (family.pivotResiduals.map fun residual =>
            residual.instantiate pivotArguments)[i]? := by
        simp only [RegularTerm.composedContexts,
          activeCompositionContexts, List.map_append]
        exact List.getElem?_append_left hmappedBound
      _ = some
          (family.pivotResiduals[i].instantiate pivotArguments) := by
        simp [List.getElem?_map,
          List.getElem?_eq_getElem hresidualBound]
      _ = some
          ((family.row index).pivotResidual.instantiate
            pivotArguments) := by
        exact congrArg some
          (congrArg (fun residual => residual.instantiate pivotArguments)
            (family.pivotResiduals_getElem index))
  · have htargetBound : i < family.pivotTargets.length := by
      simpa using hi
    calc
      (family.pivotTargets ++
          List.replicate
            ((active.depthPrefix 1).schemaArity g.ranks -
              children.length) filler)[i]? =
          family.pivotTargets[i]? :=
        List.getElem?_append_left htargetBound
      _ = some family.pivotTargets[i] :=
        List.getElem?_eq_getElem htargetBound
      _ = some (family.row index).pivotTarget := by
        exact congrArg some (family.pivotTargets_getElem index)
  · simpa [pivotArguments] using
      (family.row index).pivot_instance_matches

end BalancingSegment.ExposedSuccessorFamily

end EncodedFirstOrderGrammar

end DCFEquivalence
