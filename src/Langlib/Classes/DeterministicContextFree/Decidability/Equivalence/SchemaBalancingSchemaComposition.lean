module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaBalancingSuccessorFamily
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.MultipleArgumentReplacement
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PrefixSupportComposition

@[expose]
public section

/-!
# Composed balancing schemas over fixed arguments

This is the fixed-argument form of the balancing-result schema construction.
Every pivot residual is already expressed over one externally chosen argument
tuple.  Substituting those residuals into the active residual therefore keeps
that tuple unchanged, which is the invariant needed along the pivot path.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace BalancingSegment.SchemaExposedSuccessorFamily

/-- Context tuple plugged into the active residual.  Inactive padding uses a
one-node dummy context, so its presentation size is independent of the
concrete filler and of the fixed argument tuple. -/
@[expose] public noncomputable def activeCompositionContexts
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    {children : List ℕ} {pivotSchema : RegularTerm}
    {arguments : List RegularTerm} {arity width : ℕ}
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) : List RegularTerm :=
  family.pivotResiduals ++
    List.replicate
      ((active.depthPrefix 1).schemaArity g.ranks - children.length)
      (RegularTerm.variableTerm 0)

/-- The left regular schema of a fixed-argument balancing result. -/
@[expose] public noncomputable def composedActiveSchema
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)} {filler : RegularTerm}
    {children : List ℕ} {pivotSchema : RegularTerm}
    {arguments : List RegularTerm} {arity width : ℕ}
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (activeResult : segment.ActivePrefixResidual filler) : RegularTerm :=
  activeResult.residual.instantiate family.activeCompositionContexts

end BalancingSegment.SchemaExposedSuccessorFamily

namespace BalancingSegment.SchemaExposedSuccessorFamily

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {initialLeft initialRight : RegularTerm}
  {stem : List (Label Action)} {filler : RegularTerm}
  {children : List ℕ} {pivotSchema : RegularTerm}
  {arguments : List RegularTerm} {arity width : ℕ}

/-- A depth-one active prefix has padded arity equal to the greatest grammar
rank. -/
public theorem active_schemaArity_eq_rankMax
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
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
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
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

/-- Replacing the active successor prefix leaves precisely the filler padding
of the concrete depth-one instance. -/
public theorem replaceArgumentPrefix_activeArguments
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
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
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
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

/-- Every context in the composed tuple is well formed at the externally
fixed arity. -/
public theorem activeCompositionContexts_wellFormed
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (hpadding : g.ranks.foldr max 0 ≤ arity) :
    ∀ context ∈ family.activeCompositionContexts,
      context.WellFormed g.ranks arity := by
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
      have hnonempty := List.ne_nil_of_mem hpaddingContext
      apply Nat.pos_of_ne_zero
      simpa using hnonempty
    have harity := family.active_schemaArity_eq_rankMax hactive hroot
    have hpositive : 1 ≤ arity := by omega
    exact RegularTerm.variableTerm_wellFormed hpositive

/-- The composed active schema remains supported by the same externally
fixed prefix. -/
public theorem composedActiveSchema_supported
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (hg : g.WellFormed) (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hwidthArity : width ≤ arity)
    (activeResult : segment.ActivePrefixResidual filler) :
    (family.composedActiveSchema activeResult).SupportedByPrefix
      g.ranks arity width := by
  let contexts := family.activeCompositionContexts
  have hcontextsLength :
      contexts.length =
        (active.depthPrefix 1).schemaArity g.ranks :=
    family.activeCompositionContexts_length hactive hroot
  have houterWellFormed :
      activeResult.residual.WellFormed g.ranks contexts.length := by
    rw [hcontextsLength]
    exact activeResult.supported.1
  have hcontextsWellFormed :
      ∀ context ∈ contexts,
        context.WellFormed g.ranks arity := by
    exact family.activeCompositionContexts_wellFormed
      hactive hroot hpadding
  have hcontextsWitness :
      ∀ x, x < children.length →
        ∃ context,
          contexts[x]? = some context ∧
            context.HasPrefixWitness width := by
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
    · exact (family.row index).pivot_hasPrefixWitness
  have hsourceWitness :=
    family.activeResidual_hasPrefixWitness hg hactive hroot activeResult
  have hcontextsArity : contexts.length ≤ arity := by
    rw [hcontextsLength,
      family.active_schemaArity_eq_rankMax hactive hroot]
    exact hpadding
  exact hsourceWitness.instantiate_supportedByPrefix
    houterWellFormed hcontextsWellFormed hcontextsWitness
    hcontextsArity hwidthArity

/-- Structural witness underlying `composedActiveSchema_supported`. -/
public theorem composedActiveSchema_hasPrefixWitness
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (hg : g.WellFormed) (hactive : active.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (activeResult : segment.ActivePrefixResidual filler) :
    (family.composedActiveSchema activeResult).HasPrefixWitness width := by
  let contexts := family.activeCompositionContexts
  have hcontextsClosed :
      ∀ context ∈ contexts, context.ReferenceClosed := by
    intro context hcontext
    exact RegularTerm.referenceClosed_of_wellFormed
      (family.activeCompositionContexts_wellFormed
        hactive hroot hpadding context hcontext)
  have hcontextsWitness :
      ∀ x, x < children.length →
        ∃ context,
          contexts[x]? = some context ∧
            context.HasPrefixWitness width := by
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
    · exact (family.row index).pivot_hasPrefixWitness
  obtain ⟨support, hsupport⟩ :=
    family.activeResidual_hasPrefixWitness hg hactive hroot activeResult
  exact hsupport.instantiate
    (RegularTerm.referenceClosed_of_wellFormed activeResult.supported.1)
    hcontextsClosed hcontextsWitness

/-- The composed contexts instantiated by the fixed tuple agree with the
concrete replacement targets on every active successor slot. -/
public theorem composedActiveContexts_equivalentThrough
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) :
    RegularTerm.ArgumentsEquivalentThrough children.length
      (RegularTerm.composedContexts family.activeCompositionContexts
        arguments)
      (family.pivotTargets ++
        List.replicate
          ((active.depthPrefix 1).schemaArity g.ranks - children.length)
          filler) := by
  intro i hi
  let index : Fin children.length := ⟨i, hi⟩
  refine ⟨(family.row index).pivotResidual.instantiate arguments,
    (family.row index).pivotTarget, ?_, ?_, ?_⟩
  · have hresidualBound : i < family.pivotResiduals.length := by
      simpa using hi
    have hmappedBound :
        i <
          (family.pivotResiduals.map fun residual =>
            residual.instantiate arguments).length := by
      simpa using hresidualBound
    calc
      (RegularTerm.composedContexts family.activeCompositionContexts
          arguments)[i]? =
          (family.pivotResiduals.map fun residual =>
            residual.instantiate arguments)[i]? := by
        simp only [RegularTerm.composedContexts,
          activeCompositionContexts, List.map_append]
        exact List.getElem?_append_left hmappedBound
      _ = some
          (family.pivotResiduals[i].instantiate arguments) := by
        simp [List.getElem?_map,
          List.getElem?_eq_getElem hresidualBound]
      _ = some
          ((family.row index).pivotResidual.instantiate arguments) := by
        exact congrArg some
          (congrArg (fun residual => residual.instantiate arguments)
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
  · exact (family.row index).pivot_instance_matches

end BalancingSegment.SchemaExposedSuccessorFamily

end EncodedFirstOrderGrammar

end DCFEquivalence
