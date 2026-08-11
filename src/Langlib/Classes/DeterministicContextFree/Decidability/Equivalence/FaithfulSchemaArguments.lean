module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerCancellation

@[expose]
public section

/-!
# Argument tuples faithful for open unfolding

The `M₂` descent argument compares schemas after instantiation.  Such a
comparison can be reflected back to open schemas only for a faithful
substitution.  Arbitrary fixed tails are not faithful: equal or cyclic tails
can collapse distinct open contexts.  The canonical tuple of pairwise
distinct critical markers is faithful.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Instantiation by `arguments` reflects unfolding equality for all
well-formed schemas at the advertised arity. -/
@[expose] public def UnfoldingFaithfulArguments
    (g : EncodedFirstOrderGrammar Action)
    (arity : ℕ) (arguments : List RegularTerm) : Prop :=
  arguments.length = arity ∧
    ∀ {left right : RegularTerm},
      left.WellFormed g.ranks arity →
      right.WellFormed g.ranks arity →
      (left.instantiate arguments).UnfoldingEquivalent
        (right.instantiate arguments) →
      left.UnfoldingEquivalent right

namespace UnfoldingFaithfulArguments

public theorem reflect
    {g : EncodedFirstOrderGrammar Action}
    {arity : ℕ} {arguments : List RegularTerm}
    (hfaithful :
      g.UnfoldingFaithfulArguments arity arguments)
    {left right : RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hinstance :
      (left.instantiate arguments).UnfoldingEquivalent
      (right.instantiate arguments)) :
    left.UnfoldingEquivalent right :=
  hfaithful.2 hleft hright hinstance

/-- Faithfulness transports backwards across pointwise semantic
equivalence of substitutions.  In particular, a retagging cannot both make
an arbitrary tuple faithful and preserve every well-formed schema instance:
that would imply that the original tuple was faithful already. -/
public theorem of_pointwise_instantiationEquivalent
    {g : EncodedFirstOrderGrammar Action}
    {arity : ℕ}
    {original tagged : List RegularTerm}
    (htagged :
      g.UnfoldingFaithfulArguments arity tagged)
    (horiginalLength : original.length = arity)
    (htransport : ∀ {schema : RegularTerm},
      schema.WellFormed g.ranks arity →
      (schema.instantiate original).UnfoldingEquivalent
        (schema.instantiate tagged)) :
    g.UnfoldingFaithfulArguments arity original := by
  refine ⟨horiginalLength, ?_⟩
  intro left right hleft hright horiginal
  apply htagged.reflect hleft hright
  exact (htransport hleft).symm.trans
    (horiginal.trans (htransport hright))

end UnfoldingFaithfulArguments

/-- Pairwise distinct fresh critical markers form the canonical faithful
substitution. -/
public theorem criticalArguments_unfoldingFaithful
    (g : EncodedFirstOrderGrammar Action) (arity : ℕ) :
    g.UnfoldingFaithfulArguments arity
      (g.criticalArguments arity) := by
  refine ⟨g.criticalArguments_length arity, ?_⟩
  intro left right hleft hright hcritical
  exact g.unfoldingEquivalent_of_criticalInstantiation
    hleft hright hcritical

end EncodedFirstOrderGrammar

end DCFEquivalence
