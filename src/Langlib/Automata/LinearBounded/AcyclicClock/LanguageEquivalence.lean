module

public import Langlib.Automata.LinearBounded.AcyclicClock.AcyclicityReduction
public import Langlib.Automata.LinearBounded.AcyclicClock.MacroSoundness

@[expose]
public section

/-!
# Exact language preservation by the globally acyclic compiler

The operational clock compiler is globally acyclic on every raw configuration and recognizes
exactly the source language.  Consequently every LBA language has a presentation whose complete
configuration graph is acyclic at every tape width.  Composing with the degree serializers gives
the same result while simultaneously bounding indegree and outdegree by two and exposing a
width-uniform partition of the step relation into two partial bijections.

These are nondeterministic normal forms.  They do not choose a successful branch and therefore do
not turn an LBA into a DLBA.  Indeed, the final equivalences show that determinizing even either
restricted class is exactly the open first LBA problem.
-/

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- The concrete compiler is globally configuration-acyclic and recognizes exactly the source
language. -/
public theorem machine_acyclic_and_language_eq
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    (machine M).ConfigurationAcyclic ∧
      LBA.LanguageEnd (machine M) = LBA.LanguageEnd M :=
  ⟨machine_configurationAcyclic M, languageEnd_machine_eq M⟩

end LBA.AcyclicClock

/-- The class of languages having a globally configuration-acyclic LBA presentation. -/
public def AcyclicLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    Set (Language T) :=
  setOf is_AcyclicLBA

/-- The class of languages having a globally acyclic LBA presentation whose configuration
indegree and outdegree are both at most two. -/
public def AcyclicBoundedDegreeLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    Set (Language T) :=
  setOf is_AcyclicBoundedDegreeLBA

/-- Compile any finite LBA into an equivalent LBA whose entire raw configuration graph is
acyclic at every tape width. -/
public theorem is_AcyclicLBA_of_is_LBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_LBA L) :
    is_AcyclicLBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  refine
    ⟨LBA.AcyclicClock.WorkCell T Γ Λ, LBA.AcyclicClock.State Λ,
      inferInstance, inferInstance, inferInstance, inferInstance,
      LBA.AcyclicClock.machine M,
      LBA.AcyclicClock.machine_configurationAcyclic M, ?_⟩
  exact LBA.AcyclicClock.languageEnd_machine_eq M |>.trans hM

/-- Globally acyclic LBA presentations recognize exactly the ordinary LBA languages. -/
public theorem is_LBA_iff_is_AcyclicLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA L ↔ is_AcyclicLBA L :=
  ⟨is_AcyclicLBA_of_is_LBA, is_LBA_of_is_AcyclicLBA⟩

/-- Every LBA language has an equivalent globally acyclic presentation with both directed
configuration degrees at most two. -/
public theorem is_LBA_iff_is_AcyclicBoundedDegreeLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA L ↔ is_AcyclicBoundedDegreeLBA L := by
  rw [is_LBA_iff_is_AcyclicLBA,
    is_AcyclicLBA_iff_is_AcyclicBoundedDegreeLBA]

/-- Every LBA language has an equivalent globally acyclic, degree-two presentation whose entire
configuration relation is partitioned by two uniform biunique layers. -/
public theorem is_LBA_iff_is_AcyclicDegreeTwoBiUniqueLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA L ↔ is_AcyclicDegreeTwoBiUniqueLBA L := by
  rw [is_LBA_iff_is_AcyclicLBA,
    is_AcyclicLBA_iff_is_AcyclicDegreeTwoBiUniqueLBA]

/-- Globally acyclic LBAs recognize exactly `LBA`. -/
public theorem AcyclicLBA_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (AcyclicLBA : Set (Language T)) = LBA := by
  ext L
  exact (is_LBA_iff_is_AcyclicLBA L).symm

/-- Globally acyclic degree-two LBAs recognize exactly `LBA`. -/
public theorem AcyclicBoundedDegreeLBA_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (AcyclicBoundedDegreeLBA : Set (Language T)) = LBA := by
  ext L
  exact (is_LBA_iff_is_AcyclicBoundedDegreeLBA L).symm

/-- Globally acyclic, degree-two LBAs with a two-biunique-layer partition recognize exactly
`LBA`. -/
public theorem AcyclicDegreeTwoBiUniqueLBA_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (AcyclicDegreeTwoBiUniqueLBA : Set (Language T)) = LBA := by
  ext L
  exact (is_LBA_iff_is_AcyclicDegreeTwoBiUniqueLBA L).symm

/-- The first LBA problem is unchanged when restricted to globally acyclic LBA
presentations. -/
public theorem lba_eq_dlba_iff_acyclicLBA_subset
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((AcyclicLBA : Set (Language T)) ⊆ DLBA) := by
  rw [AcyclicLBA_eq_LBA]
  constructor
  · intro heq
    rw [heq]
  · intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

/-- Even globally acyclic LBA configuration graphs with both indegree and outdegree at most two
retain the full first LBA problem. -/
public theorem lba_eq_dlba_iff_acyclicBoundedDegreeLBA_subset
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((AcyclicBoundedDegreeLBA : Set (Language T)) ⊆ DLBA) := by
  rw [AcyclicBoundedDegreeLBA_eq_LBA]
  constructor
  · intro heq
    rw [heq]
  · intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

/-- The first LBA problem remains unchanged even after requiring global acyclicity, both degree
bounds, and the explicit two-partial-bijection layer family supplied by the compiler. -/
public theorem lba_eq_dlba_iff_acyclicDegreeTwoBiUniqueLBA_subset
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((AcyclicDegreeTwoBiUniqueLBA : Set (Language T)) ⊆ DLBA) := by
  rw [AcyclicDegreeTwoBiUniqueLBA_eq_LBA]
  constructor
  · intro heq
    rw [heq]
  · intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

end
