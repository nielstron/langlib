module

public import Langlib.Automata.LinearBounded.MachineTwoMatchings.Reversible
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.SequentialUnionLanguage
public import Langlib.Automata.LinearBounded.Equivalence.DeterministicEndmarkerToFlag

@[expose]
public section

/-!
# Determinizing exact-two-matching LBA presentations

An exact two-matching configuration relation has only one genuine choice: its first edge.
`ClockedBranchUnion` makes the finite family of pinned branches globally acyclic, and
`sequentialUnion` tries those branches one after another while restoring an immutable input
track.  The resulting endmarker machine is functional.  Deterministic endmarker folding then
produces a marker-free DLBA presentation.

This proves a restricted determinization theorem for `TwoMatchingLBA`; it makes no claim that an
arbitrary LBA admits an exact-two-matching presentation.
-/

namespace LBA.MachineTwoMatchings

variable {T Γ Λ : Type}
  [Fintype T] [DecidableEq T]
  [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- Every exact-two-matching endmarker machine has a deterministic-LBA language.  No acyclicity
premise is needed: the guarded clock wrapper supplies it before sequential scheduling. -/
public theorem is_DLBA_languageEnd_of_twoMatching
    (M : Machine (EndAlpha T Γ) Λ) (hlayers : M.HasTwoMatchingStepPartition) :
    is_DLBA (LanguageEnd M) := by
  rw [← languageEnd_sequentialUnion_clockedBranchUnion_eq M hlayers]
  exact is_DLBA_languageEnd_of_functional
    (sequentialUnion (ClockedBranchUnion.machine M))
    (sequentialUnion_clockedBranchUnion_functional M)

/-- The direct acyclic scheduler is also a deterministic presentation, without inserting the
clocked branch-union wrapper. -/
public theorem is_DLBA_languageEnd_of_acyclic_twoMatching
    (M : Machine (EndAlpha T Γ) Λ)
    (hacyclic : M.ConfigurationAcyclic)
    (hlayers : M.HasTwoMatchingStepPartition) :
    is_DLBA (LanguageEnd M) := by
  rw [← languageEnd_sequentialUnion_eq_of_twoMatching M hacyclic hlayers]
  exact is_DLBA_languageEnd_of_functional
    (sequentialUnion M) (sequentialUnion_functional M)

end LBA.MachineTwoMatchings

/-- Every language with an exact-two-matching LBA presentation is deterministic
context-sensitive. -/
public theorem is_DLBA_of_is_TwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_TwoMatchingLBA L) : is_DLBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hlayers, hM⟩
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  rw [← hM]
  exact LBA.MachineTwoMatchings.is_DLBA_languageEnd_of_twoMatching M hlayers

/-- Class-level restricted determinization theorem. -/
public theorem twoMatchingLBA_subset_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (TwoMatchingLBA : Set (Language T)) ⊆ DLBA :=
  fun _ hL => is_DLBA_of_is_TwoMatchingLBA hL

/-- Every language with an all-raw-configuration-biunique LBA presentation is deterministic.
`ReversibleTriviality.lean` later shows that this particular clamped-model class contains only
the empty and universal languages; the useful content here is the more general two-matching
theorem above. -/
public theorem is_DLBA_of_is_ReversibleLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_ReversibleLBA L) : is_DLBA L :=
  is_DLBA_of_is_TwoMatchingLBA
    (is_TwoMatchingLBA_of_is_ReversibleLBA hL)

/-- Class-level all-raw-configuration-biunique corollary. -/
public theorem reversibleLBA_subset_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (ReversibleLBA : Set (Language T)) ⊆ DLBA :=
  fun _ hL => is_DLBA_of_is_ReversibleLBA hL

/-- The acyclic exact-two-matching subclass is deterministic as an immediate corollary. -/
public theorem is_DLBA_of_is_AcyclicTwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicTwoMatchingLBA L) : is_DLBA L :=
  is_DLBA_of_is_TwoMatchingLBA
    (is_TwoMatchingLBA_of_is_AcyclicTwoMatchingLBA hL)

/-- Class-level acyclic corollary. -/
public theorem acyclicTwoMatchingLBA_subset_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (AcyclicTwoMatchingLBA : Set (Language T)) ⊆ DLBA :=
  fun _ hL => is_DLBA_of_is_AcyclicTwoMatchingLBA hL

end
