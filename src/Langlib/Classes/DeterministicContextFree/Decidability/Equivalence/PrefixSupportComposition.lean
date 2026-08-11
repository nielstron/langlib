module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationSupport

@[expose]
public section

/-!
# Composing prefix-supported regular schemas

The active side of a balancing result is an outer residual whose active
variables name immediate successors.  Substituting one pivot residual context
for every such variable transfers support from the active-successor prefix to
the pivot-tail prefix.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Substitution transfers a structural prefix witness through every context
reachable from the outer witness. -/
public theorem HasPrefixWitness.instantiate_supportedByPrefix
    {ranks : List ℕ} {outer : RegularTerm}
    {sourceWidth targetArity targetWidth : ℕ}
    {contexts : List RegularTerm}
    (houterWitness : outer.HasPrefixWitness sourceWidth)
    (houterWellFormed : outer.WellFormed ranks contexts.length)
    (hcontextsWellFormed : ∀ context ∈ contexts,
      context.WellFormed ranks targetArity)
    (hcontextsWitness : ∀ x, x < sourceWidth →
      ∃ context,
        contexts[x]? = some context ∧
          context.HasPrefixWitness targetWidth)
    (hcontextsLength : contexts.length ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    (outer.instantiate contexts).SupportedByPrefix
      ranks targetArity targetWidth := by
  obtain ⟨outerSupport, houterSupport⟩ := houterWitness
  have hcontextsClosed :
      ∀ context ∈ contexts, context.ReferenceClosed := by
    intro context hcontext
    exact referenceClosed_of_wellFormed
      (hcontextsWellFormed context hcontext)
  have hresultWitness :
      (outer.instantiate contexts).HasPrefixWitness targetWidth :=
    houterSupport.instantiate
      (referenceClosed_of_wellFormed houterWellFormed)
      hcontextsClosed hcontextsWitness
  have hresultWellFormedMax :=
    instantiate_wellFormed_max houterWellFormed hcontextsWellFormed
  have hresultWellFormed :
      (outer.instantiate contexts).WellFormed ranks targetArity := by
    simpa [Nat.max_eq_right hcontextsLength] using hresultWellFormedMax
  exact hresultWitness.supportedByPrefix
    hresultWellFormed htargetWidth

end RegularTerm

end DCFEquivalence
