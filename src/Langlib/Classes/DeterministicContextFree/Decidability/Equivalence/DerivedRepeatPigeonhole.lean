module

public import Mathlib.Data.Fintype.Pigeonhole
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedRepeat
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedSemanticReachability

@[expose]
public section

/-!
# Pigeonhole criteria for derived repeats

The M₂ argument produces balancing-result pairs in the certificate calculus,
not necessarily the raw residual pair of the trace path.  A fixed finite
semantic cover of both components along infinitely many increasing prefix
levels therefore yields a `HasDerivedRepeat`.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Finite semantic covers of certificate-derived pairs at strictly
increasing path levels force a derived repeat. -/
public theorem TracePath.hasDerivedRepeat_of_finite_semantic_cover
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (pairs : ∀ n, path.DerivedPairAt (levels n))
    (leftCover rightCover : List RegularTerm)
    (hleft : ∀ n, ∃ representative ∈ leftCover,
      (pairs n).left.UnfoldingEquivalent representative)
    (hright : ∀ n, ∃ representative ∈ rightCover,
      (pairs n).right.UnfoldingEquivalent representative) :
    path.HasDerivedRepeat := by
  classical
  have hleftIndex : ∀ n, ∃ i : Fin leftCover.length,
      (pairs n).left.UnfoldingEquivalent leftCover[i] := by
    intro n
    obtain ⟨representative, hrepresentative, hequivalent⟩ := hleft n
    obtain ⟨i, hi, hget⟩ :=
      List.mem_iff_getElem.mp hrepresentative
    exact ⟨⟨i, hi⟩, by simpa [hget] using hequivalent⟩
  have hrightIndex : ∀ n, ∃ i : Fin rightCover.length,
      (pairs n).right.UnfoldingEquivalent rightCover[i] := by
    intro n
    obtain ⟨representative, hrepresentative, hequivalent⟩ := hright n
    obtain ⟨i, hi, hget⟩ :=
      List.mem_iff_getElem.mp hrepresentative
    exact ⟨⟨i, hi⟩, by simpa [hget] using hequivalent⟩
  choose leftIndex hleftEquivalent using hleftIndex
  choose rightIndex hrightEquivalent using hrightIndex
  letI : Fintype (Fin leftCover.length × Fin rightCover.length) :=
    Fintype.ofList
      ((List.finRange leftCover.length).flatMap fun i =>
        (List.finRange rightCover.length).map fun j => (i, j))
      (by
        rintro ⟨i, j⟩
        simp)
  letI : Finite (Fin leftCover.length × Fin rightCover.length) :=
    Fintype.finite
      (inferInstance :
        Fintype (Fin leftCover.length × Fin rightCover.length))
  obtain ⟨i, j, hij, hindices⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n => (leftIndex n, rightIndex n))
  have hleftIndexEq : leftIndex i = leftIndex j :=
    congrArg Prod.fst hindices
  have hrightIndexEq : rightIndex i = rightIndex j :=
    congrArg Prod.snd hindices
  have hleftRepeat :
      (pairs i).left.UnfoldingEquivalent (pairs j).left := by
    exact (hleftEquivalent i).trans
      (hleftIndexEq ▸ (hleftEquivalent j).symm)
  have hrightRepeat :
      (pairs i).right.UnfoldingEquivalent (pairs j).right := by
    exact (hrightEquivalent i).trans
      (hrightIndexEq ▸ (hrightEquivalent j).symm)
  by_cases hijOrder : i < j
  · exact ⟨levels i, levels j, pairs i, pairs j,
      hlevels hijOrder, hleftRepeat, hrightRepeat⟩
  · have hji : j < i := by omega
    exact ⟨levels j, levels i, pairs j, pairs i,
      hlevels hji, hleftRepeat.symm, hrightRepeat.symm⟩

/-- Observation-46 style criterion: if every derived balancing-result pair is
determined up to unfolding equivalence by metadata drawn from one fixed finite
list, then two derived pairs repeat.  The intended metadata packages the pivot
representative, balancing word, active root symbol, and orientation. -/
public theorem TracePath.hasDerivedRepeat_of_finite_metadata
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (pairs : ∀ n, path.DerivedPairAt (levels n))
    {Metadata : Type}
    (metadata : ℕ → Metadata)
    (metadataCover : List Metadata)
    (hmetadata : ∀ n, metadata n ∈ metadataCover)
    (leftOf rightOf : Metadata → RegularTerm)
    (hleft : ∀ n,
      (pairs n).left.UnfoldingEquivalent (leftOf (metadata n)))
    (hright : ∀ n,
      (pairs n).right.UnfoldingEquivalent (rightOf (metadata n))) :
    path.HasDerivedRepeat := by
  apply path.hasDerivedRepeat_of_finite_semantic_cover
    levels hlevels pairs
    (metadataCover.map leftOf) (metadataCover.map rightOf)
  · intro n
    exact ⟨leftOf (metadata n),
      List.mem_map.mpr ⟨metadata n, hmetadata n, rfl⟩,
      hleft n⟩
  · intro n
    exact ⟨rightOf (metadata n),
      List.mem_map.mpr ⟨metadata n, hmetadata n, rfl⟩,
      hright n⟩

/-- M₂-style uniform bounded reachability from pointed subgraphs of fixed
bases gives the finite covers required for a derived repeat. -/
public theorem TracePath.hasDerivedRepeat_of_bounded_pointed_reachability
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight leftBase rightBase : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (pairs : ∀ n, path.DerivedPairAt (levels n))
    (bound : ℕ)
    (hleft : ∀ n,
      ∃ source ∈ leftBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (pairs n).left.UnfoldingEquivalent reached)
    (hright : ∀ n,
      ∃ source ∈ rightBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (pairs n).right.UnfoldingEquivalent reached) :
    path.HasDerivedRepeat := by
  apply path.hasDerivedRepeat_of_finite_semantic_cover
    levels hlevels pairs
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

/-- The finite-cover M₂ criterion directly yields the bound-one open-sound
branch used by the stair-base construction. -/
public theorem TracePath.eventuallyBoundedOpenSound_of_derived_finite_semantic_cover
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (pairs : ∀ n, path.DerivedPairAt (levels n))
    (leftCover rightCover : List RegularTerm)
    (hleft : ∀ n, ∃ representative ∈ leftCover,
      (pairs n).left.UnfoldingEquivalent representative)
    (hright : ∀ n, ∃ representative ∈ rightCover,
      (pairs n).right.UnfoldingEquivalent representative) :
    g.EventuallyBoundedOpenSound initialLeft initialRight 1 path := by
  apply path.eventuallyBoundedOpenSound_of_hasDerivedRepeat
  exact path.hasDerivedRepeat_of_finite_semantic_cover
    levels hlevels pairs leftCover rightCover hleft hright

/-- Finite balancing-result metadata directly yields the bound-one open-sound
branch. -/
public theorem TracePath.eventuallyBoundedOpenSound_of_derived_finite_metadata
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (pairs : ∀ n, path.DerivedPairAt (levels n))
    {Metadata : Type}
    (metadata : ℕ → Metadata)
    (metadataCover : List Metadata)
    (hmetadata : ∀ n, metadata n ∈ metadataCover)
    (leftOf rightOf : Metadata → RegularTerm)
    (hleft : ∀ n,
      (pairs n).left.UnfoldingEquivalent (leftOf (metadata n)))
    (hright : ∀ n,
      (pairs n).right.UnfoldingEquivalent (rightOf (metadata n))) :
    g.EventuallyBoundedOpenSound initialLeft initialRight 1 path := by
  apply path.eventuallyBoundedOpenSound_of_hasDerivedRepeat
  exact path.hasDerivedRepeat_of_finite_metadata
    levels hlevels pairs metadata metadataCover hmetadata
      leftOf rightOf hleft hright

/-- Bounded pointed reconstruction of derived balancing-result pairs directly
yields the bound-one open-sound branch. -/
public theorem TracePath.eventuallyBoundedOpenSound_of_derived_bounded_pointed_reachability
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight leftBase rightBase : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (pairs : ∀ n, path.DerivedPairAt (levels n))
    (bound : ℕ)
    (hleft : ∀ n,
      ∃ source ∈ leftBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (pairs n).left.UnfoldingEquivalent reached)
    (hright : ∀ n,
      ∃ source ∈ rightBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (pairs n).right.UnfoldingEquivalent reached) :
    g.EventuallyBoundedOpenSound initialLeft initialRight 1 path := by
  apply path.eventuallyBoundedOpenSound_of_hasDerivedRepeat
  exact path.hasDerivedRepeat_of_bounded_pointed_reachability
    levels hlevels pairs bound hleft hright

end EncodedFirstOrderGrammar

end DCFEquivalence
