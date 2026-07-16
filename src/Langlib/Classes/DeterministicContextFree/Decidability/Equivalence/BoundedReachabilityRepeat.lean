module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveStairExistence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedSemanticReachability

@[expose]
public section

/-!
# Repetition from bounded pointed reachability

If every residual on each side of a common trace path is semantically reachable
within one fixed number of steps from a pointed subgraph of one fixed finite
base, then both residual streams have finite semantic covers.  Pigeonhole on
their product yields a repeated residual pair.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Uniform bounded reachability from pointed subgraphs of two fixed bases
forces a semantic repeat on the common trace path. -/
public theorem TracePath.hasRepeat_of_bounded_pointed_reachability
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight leftBase rightBase : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (bound : ℕ)
    (hleft : ∀ n,
      ∃ source ∈ leftBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (path.left n).UnfoldingEquivalent reached)
    (hright : ∀ n,
      ∃ source ∈ rightBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (path.right n).UnfoldingEquivalent reached) :
    path.HasRepeat := by
  apply path.hasRepeat_of_finite_semantic_cover
    (g.reachableWithin bound leftBase.pointedSubterms)
    (g.reachableWithin bound rightBase.pointedSubterms)
  · intro n
    obtain ⟨source, hsource, labels, reached,
        hlength, hrun, hequivalent⟩ := hleft n
    exact exists_mem_reachableWithin_of_semantic_run
      hsource hlength hrun hequivalent
  · intro n
    obtain ⟨source, hsource, labels, reached,
        hlength, hrun, hequivalent⟩ := hright n
    exact exists_mem_reachableWithin_of_semantic_run
      hsource hlength hrun hequivalent

end EncodedFirstOrderGrammar

end DCFEquivalence
