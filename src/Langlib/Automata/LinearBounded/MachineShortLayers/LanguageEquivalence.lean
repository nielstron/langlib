module

public import Langlib.Automata.LinearBounded.MachineShortLayers.Acyclicity
public import Langlib.Automata.LinearBounded.AcyclicClock.LanguageEquivalence

@[expose]
public section

/-!
# Full LBA expressiveness with two short biunique layers

Compose three already verified transformations:

1. the operational clock compiler makes the complete raw configuration graph acyclic;
2. `boundedDegree` supplies a width-uniform exact partition into two biunique layers and unique
   transition labels;
3. `shortLayers` replaces each edge by the local color word `c, opposite(c), 0, 1`.

The result recognizes the original language at the same tape width as the acyclic presentation,
has both directed configuration degrees at most two, and neither supplied layer contains a path
of three edges.  This is a nondeterministic normal form, not a determinization theorem.
-/

open Set

/-- Languages recognized by globally acyclic LBAs carrying a width-uniform exact two-layer
partition whose layers are biunique and contain no path of three edges. -/
public def is_AcyclicDegreeTwoShortBiUniqueLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.ConfigurationAcyclic ∧
      M.ConfigurationDegreeAtMostTwo ∧
      M.HasTwoShortBiUniqueStepPartition ∧
      LBA.LanguageEnd M = L

/-- The corresponding language class. -/
public def AcyclicDegreeTwoShortBiUniqueLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    Set (Language T) :=
  setOf is_AcyclicDegreeTwoShortBiUniqueLBA

/-- Forgetting the structural witnesses gives an ordinary LBA presentation. -/
public theorem is_LBA_of_is_AcyclicDegreeTwoShortBiUniqueLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicDegreeTwoShortBiUniqueLBA L) :
    is_LBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M,
      hacyclic, hdegree, hlayers, hM⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- Forgetting only the short-path field gives the previously established globally acyclic,
degree-two, two-biunique-layer normal form. -/
public theorem is_AcyclicDegreeTwoBiUniqueLBA_of_is_AcyclicDegreeTwoShortBiUniqueLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicDegreeTwoShortBiUniqueLBA L) :
    is_AcyclicDegreeTwoBiUniqueLBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M,
      hacyclic, hdegree, hlayers, hM⟩
  rcases hlayers with ⟨layer, hcover, hsub, hbiUnique, hshort⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M,
    hacyclic, hdegree, ⟨layer, hcover, hsub, hbiUnique⟩, hM⟩

/-- The new language class is directly contained in the previous two-biunique normal form. -/
public theorem AcyclicDegreeTwoShortBiUniqueLBA_subset_AcyclicDegreeTwoBiUniqueLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (AcyclicDegreeTwoShortBiUniqueLBA : Set (Language T)) ⊆
      AcyclicDegreeTwoBiUniqueLBA :=
  fun _ hL =>
    is_AcyclicDegreeTwoBiUniqueLBA_of_is_AcyclicDegreeTwoShortBiUniqueLBA hL

/-- Every LBA language has the globally acyclic, degree-two, short-two-layer normal form. -/
public theorem is_AcyclicDegreeTwoShortBiUniqueLBA_of_is_LBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_LBA L) :
    is_AcyclicDegreeTwoShortBiUniqueLBA L := by
  rcases is_AcyclicLBA_of_is_LBA hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hacyclic, hM⟩
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  refine
    ⟨Γ,
      LBA.ShortLayerState (LBA.EndAlpha T Γ)
        (LBA.IncomingState (LBA.EndAlpha T Γ)
          (LBA.BinaryBranchState (LBA.EndAlpha T Γ) Λ)),
      hΓ, inferInstance, hdecΓ, Classical.decEq _,
      M.boundedDegree.shortLayers,
      M.boundedDegree_shortLayers_configurationAcyclic hacyclic,
      M.boundedDegree_shortLayers_configurationDegreeAtMostTwo,
      M.boundedDegree_shortLayers_hasTwoShortBiUniqueStepPartition, ?_⟩
  exact M.languageEnd_boundedDegree_shortLayers_eq.trans hM

/-- The short-two-layer normal form is equivalent to the ordinary LBA presentation. -/
public theorem is_LBA_iff_is_AcyclicDegreeTwoShortBiUniqueLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA L ↔ is_AcyclicDegreeTwoShortBiUniqueLBA L :=
  ⟨is_AcyclicDegreeTwoShortBiUniqueLBA_of_is_LBA,
    is_LBA_of_is_AcyclicDegreeTwoShortBiUniqueLBA⟩

/-- Globally acyclic degree-two LBAs with two short biunique layers recognize exactly `LBA`. -/
public theorem AcyclicDegreeTwoShortBiUniqueLBA_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (AcyclicDegreeTwoShortBiUniqueLBA : Set (Language T)) = LBA := by
  ext L
  exact (is_LBA_iff_is_AcyclicDegreeTwoShortBiUniqueLBA L).symm

/-- The first LBA problem remains unchanged on the short-two-layer normal form. -/
public theorem lba_eq_dlba_iff_acyclicDegreeTwoShortBiUniqueLBA_subset
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((AcyclicDegreeTwoShortBiUniqueLBA : Set (Language T)) ⊆ DLBA) := by
  rw [AcyclicDegreeTwoShortBiUniqueLBA_eq_LBA]
  constructor
  · intro heq
    rw [heq]
  · intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

end
