module

public import Langlib.Automata.LinearBounded.AcyclicClock.LanguageEquivalence
public import Langlib.Automata.LinearBounded.MachineThreeMatchings.Structural

@[expose]
public section

/-!
# The acyclic degree-two three-matching LBA class

Composing the existing globally acyclic clock, simultaneous degree-two serializer, and the
same-width phase split gives a particularly rigid normal form for every LBA language.  At every
tape width its entire raw configuration graph is acyclic, has indegree and outdegree at most two,
and has one width-uniform exact partition into three directed matchings.

This remains a nondeterministic normal form.  It does not select an accepting branch, and
determinizing this restricted class is exactly the first LBA problem.
-/

/-- Languages having a globally acyclic, directed-degree-two LBA presentation together with a
width-uniform exact three-color partition of every configuration relation into directed
matchings. -/
public def is_AcyclicDegreeTwoThreeMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.ConfigurationAcyclic ∧
      M.ConfigurationDegreeAtMostTwo ∧
      M.HasThreeMatchingStepPartition ∧
      LBA.LanguageEnd M = L

/-- The acyclic degree-two three-directed-matching LBA language class. -/
public def AcyclicDegreeTwoThreeMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_AcyclicDegreeTwoThreeMatchingLBA

/-- Forgetting the structural witnesses gives an ordinary LBA presentation. -/
public theorem is_LBA_of_is_AcyclicDegreeTwoThreeMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicDegreeTwoThreeMatchingLBA L) : is_LBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M,
      _hacyclic, _hdegree, _hlayers, hM⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- Every LBA language has an equivalent presentation in the acyclic degree-two three-matching
normal form.  The final three-matching split preserves the tape alphabet and tape width of the
preceding acyclic degree-two presentation. -/
public theorem is_AcyclicDegreeTwoThreeMatchingLBA_of_is_LBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_LBA L) : is_AcyclicDegreeTwoThreeMatchingLBA L := by
  have hnormal := (is_LBA_iff_is_AcyclicDegreeTwoBiUniqueLBA L).1 hL
  rcases hnormal with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M,
      hacyclic, hdegree, hlayers, hM⟩
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  refine ⟨Γ, LBA.ThreeMatchingState Λ,
    hΓ, inferInstance, hdecΓ, inferInstance, M.threeMatchings,
    M.configurationAcyclic_threeMatchings hacyclic,
    M.configurationDegreeAtMostTwo_threeMatchings hdegree,
    M.threeMatchings_hasThreeMatchingStepPartition hlayers, ?_⟩
  exact M.languageEnd_threeMatchings_eq.trans hM

/-- The rigid three-matching normal form recognizes exactly the ordinary LBA languages. -/
public theorem is_LBA_iff_is_AcyclicDegreeTwoThreeMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA L ↔ is_AcyclicDegreeTwoThreeMatchingLBA L :=
  ⟨is_AcyclicDegreeTwoThreeMatchingLBA_of_is_LBA,
    is_LBA_of_is_AcyclicDegreeTwoThreeMatchingLBA⟩

/-- Acyclic directed-degree-two LBAs with three exact directed-matching layers recognize
exactly `LBA`. -/
public theorem AcyclicDegreeTwoThreeMatchingLBA_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (AcyclicDegreeTwoThreeMatchingLBA : Set (Language T)) = LBA := by
  ext L
  exact (is_LBA_iff_is_AcyclicDegreeTwoThreeMatchingLBA L).symm

/-- Determinizing even the acyclic degree-two three-matching normal form is exactly the first
LBA problem. -/
public theorem lba_eq_dlba_iff_acyclicDegreeTwoThreeMatchingLBA_subset
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((AcyclicDegreeTwoThreeMatchingLBA : Set (Language T)) ⊆ DLBA) := by
  rw [AcyclicDegreeTwoThreeMatchingLBA_eq_LBA]
  constructor
  · intro heq
    rw [heq]
  · intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

end
