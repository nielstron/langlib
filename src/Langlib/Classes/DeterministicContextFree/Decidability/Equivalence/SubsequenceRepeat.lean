module

public import Mathlib.Data.Fintype.Pigeonhole
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedReachabilityRepeat
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingOpportunitySequence

@[expose]
public section

/-!
# Repetition from a finite cover on an infinite subsequence

The M₂ argument does not need a finite cover at every trace-path level.  It
only needs one at the infinitely many selected balancing endpoints.  These
lemmas isolate that exact pigeonhole principle.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One uniform bounded reconstruction of both residual components at a
chosen family of levels. -/
@[expose] public def TracePath.HasUniformBoundedPointedReconstructionAt
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) : Prop :=
  ∃ (reachabilityBound : ℕ) (leftBase rightBase : RegularTerm),
    (∀ n,
      ∃ source ∈ leftBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ reachabilityBound ∧
          g.run? labels source = some reached ∧
          (path.left (levels n)).UnfoldingEquivalent reached) ∧
    (∀ n,
      ∃ source ∈ rightBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ reachabilityBound ∧
          g.run? labels source = some reached ∧
          (path.right (levels n)).UnfoldingEquivalent reached)

/-- Finite semantic covers on any strictly increasing sequence of path levels
force a repeated residual pair. -/
public theorem TracePath.hasRepeat_of_subsequence_finite_semantic_cover
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (leftCover rightCover : List RegularTerm)
    (hleft : ∀ n, ∃ representative ∈ leftCover,
      (path.left (levels n)).UnfoldingEquivalent representative)
    (hright : ∀ n, ∃ representative ∈ rightCover,
      (path.right (levels n)).UnfoldingEquivalent representative) :
    path.HasRepeat := by
  classical
  have hleftIndex : ∀ n, ∃ i : Fin leftCover.length,
      (path.left (levels n)).UnfoldingEquivalent leftCover[i] := by
    intro n
    obtain ⟨representative, hrepresentative, hequivalent⟩ := hleft n
    obtain ⟨i, hi, hget⟩ :=
      List.mem_iff_getElem.mp hrepresentative
    exact ⟨⟨i, hi⟩, by simpa [hget] using hequivalent⟩
  have hrightIndex : ∀ n, ∃ i : Fin rightCover.length,
      (path.right (levels n)).UnfoldingEquivalent rightCover[i] := by
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
      (path.left (levels i)).UnfoldingEquivalent
        (path.left (levels j)) := by
    exact (hleftEquivalent i).trans
      (hleftIndexEq ▸ (hleftEquivalent j).symm)
  have hrightRepeat :
      (path.right (levels i)).UnfoldingEquivalent
        (path.right (levels j)) := by
    exact (hrightEquivalent i).trans
      (hrightIndexEq ▸ (hrightEquivalent j).symm)
  by_cases hijOrder : i < j
  · exact ⟨levels i, levels j, hlevels hijOrder,
      hleftRepeat, hrightRepeat⟩
  · have hji : j < i := by omega
    exact ⟨levels j, levels i, hlevels hji,
      hleftRepeat.symm, hrightRepeat.symm⟩

/-- Uniform bounded reachability from pointed subgraphs, required only at a
strict subsequence of levels, already forces repetition. -/
public theorem TracePath.hasRepeat_of_subsequence_bounded_pointed_reachability
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight leftBase rightBase : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (bound : ℕ)
    (hleft : ∀ n,
      ∃ source ∈ leftBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (path.left (levels n)).UnfoldingEquivalent reached)
    (hright : ∀ n,
      ∃ source ∈ rightBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (path.right (levels n)).UnfoldingEquivalent reached) :
    path.HasRepeat := by
  apply path.hasRepeat_of_subsequence_finite_semantic_cover
    levels hlevels
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

/-- A uniform bounded reconstruction at strictly increasing levels forces a
repeat. -/
public theorem TracePath.hasRepeat_of_uniformBoundedPointedReconstructionAt
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    {levels : ℕ → ℕ} (hlevels : StrictMono levels)
    (hreconstruction :
      path.HasUniformBoundedPointedReconstructionAt levels) :
    path.HasRepeat := by
  obtain ⟨bound, leftBase, rightBase, hleft, hright⟩ :=
    hreconstruction
  exact path.hasRepeat_of_subsequence_bounded_pointed_reachability
    levels hlevels bound hleft hright

/-- A nonrepeating path admits no uniform M₂-style reconstruction at any
strictly increasing family of levels. -/
public theorem TracePath.no_uniformBoundedPointedReconstructionAt_of_noRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    {levels : ℕ → ℕ} (hlevels : StrictMono levels)
    (hnoRepeat : ¬path.HasRepeat) :
    ¬path.HasUniformBoundedPointedReconstructionAt levels := by
  intro hreconstruction
  exact hnoRepeat
    (path.hasRepeat_of_uniformBoundedPointedReconstructionAt
      hlevels hreconstruction)

/-- M₂-style bounded reconstruction at the selected balancing endpoints is
already enough for the terminal contradiction; no information about
intermediate path levels is required. -/
public theorem BalancingOpportunitySequence.hasRepeat_of_endpoint_bounded_pointed_reachability
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight leftBase rightBase : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (sequence : BalancingOpportunitySequence path segmentBound)
    (reachabilityBound : ℕ)
    (hleft : ∀ n,
      ∃ source ∈ leftBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ reachabilityBound ∧
          g.run? labels source = some reached ∧
          (path.left (sequence.endLevels n)).UnfoldingEquivalent reached)
    (hright : ∀ n,
      ∃ source ∈ rightBase.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ reachabilityBound ∧
          g.run? labels source = some reached ∧
          (path.right (sequence.endLevels n)).UnfoldingEquivalent reached) :
    path.HasRepeat :=
  path.hasRepeat_of_subsequence_bounded_pointed_reachability
    sequence.endLevels sequence.endLevels_strictMono
    reachabilityBound hleft hright

/-- Premise-free no-repeat consequence: along a nonrepeating path, the
selected balancing endpoints cannot admit one common M₂-style bounded
reconstruction from two finite pointed bases. -/
public theorem BalancingOpportunitySequence.no_uniform_endpoint_reconstruction_of_noRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (sequence : BalancingOpportunitySequence path segmentBound)
    (hnoRepeat : ¬path.HasRepeat) :
    ¬∃ (reachabilityBound : ℕ)
        (leftBase rightBase : RegularTerm),
      (∀ n,
        ∃ source ∈ leftBase.pointedSubterms,
          ∃ labels reached,
            labels.length ≤ reachabilityBound ∧
            g.run? labels source = some reached ∧
            (path.left (sequence.endLevels n)).UnfoldingEquivalent
              reached) ∧
      (∀ n,
        ∃ source ∈ rightBase.pointedSubterms,
          ∃ labels reached,
            labels.length ≤ reachabilityBound ∧
            g.run? labels source = some reached ∧
            (path.right (sequence.endLevels n)).UnfoldingEquivalent
              reached) := by
  rintro ⟨reachabilityBound, leftBase, rightBase, hleft, hright⟩
  exact hnoRepeat
    (sequence.hasRepeat_of_endpoint_bounded_pointed_reachability
      reachabilityBound hleft hright)

end EncodedFirstOrderGrammar

end DCFEquivalence
