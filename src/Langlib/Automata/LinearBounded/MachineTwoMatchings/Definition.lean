module

public import Langlib.Automata.LinearBounded.MachineTwoMatchings.BranchFunctional

@[expose]
public section

/-!
# The two-matching LBA classes

These classes isolate LBAs whose complete raw configuration relation, at every tape width, is
covered exactly by two directed matchings.  No separate degree premise is needed: each matching
is functional, so the union already has outdegree at most two, while the one-branch theorem is
stronger along reachable paths.  `AcyclicTwoMatchingLBA` records the additional global DAG
promise used by the direct sequential-trial construction.
-/

/-- A language with an LBA presentation whose complete width-bounded step relations are exact
unions of two directed matchings. -/
public def is_TwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.HasTwoMatchingStepPartition ∧
      LBA.LanguageEnd M = L

/-- The exact-two-directed-matching LBA language class. -/
public def TwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_TwoMatchingLBA

/-- A language with a globally acyclic LBA presentation whose complete width-bounded step
relations are exact unions of two directed matchings. -/
public def is_AcyclicTwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.ConfigurationAcyclic ∧
      M.HasTwoMatchingStepPartition ∧
      LBA.LanguageEnd M = L

/-- The acyclic exact-two-directed-matching LBA language class. -/
public def AcyclicTwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_AcyclicTwoMatchingLBA

/-- Forgetting global acyclicity embeds the acyclic class into the general two-matching class. -/
public theorem is_TwoMatchingLBA_of_is_AcyclicTwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicTwoMatchingLBA L) : is_TwoMatchingLBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hacyclic, hlayers, hM⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hlayers, hM⟩

/-- Every exact-two-matching presentation is, after forgetting the layers, an ordinary LBA. -/
public theorem is_LBA_of_is_TwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_TwoMatchingLBA L) : is_LBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hlayers, hM⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- Class-level form of forgetting the global acyclicity witness. -/
public theorem acyclicTwoMatchingLBA_subset_twoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (AcyclicTwoMatchingLBA : Set (Language T)) ⊆ TwoMatchingLBA :=
  fun _ hL => is_TwoMatchingLBA_of_is_AcyclicTwoMatchingLBA hL

/-- Exact-two-matching presentations are a restricted subclass of ordinary LBAs. -/
public theorem twoMatchingLBA_subset_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (TwoMatchingLBA : Set (Language T)) ⊆ LBA :=
  fun _ hL => is_LBA_of_is_TwoMatchingLBA hL

/-- Forgetting the acyclicity and matching witnesses gives an ordinary LBA presentation. -/
public theorem is_LBA_of_is_AcyclicTwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicTwoMatchingLBA L) : is_LBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hacyclic, _hlayers, hM⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- Every presentation in the class satisfies the width-independent one-genuine-branch search
specification. -/
public theorem exists_oneChoicePresentation_of_is_TwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_TwoMatchingLBA L) :
    ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
      (_ : DecidableEq Γ) (_ : DecidableEq Λ)
      (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
      M.HasTwoMatchingStepPartition ∧
        LBA.LanguageEnd M = L ∧
        ∀ input,
          LBA.BoundedNondeterminism.acceptsWithChoiceEventsSearch M
              (LBA.initCfgEnd M input) 1 = true ↔
            LBA.LanguageEnd M input := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hlayers, hM⟩
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  refine ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hlayers, hM, ?_⟩
  intro input
  exact LBA.BoundedNondeterminism.acceptsWithChoiceEventsSearch_one_eq_true_iff
    M hlayers (LBA.initCfgEnd M input)

/-- Every acyclic presentation in the class satisfies the same width-independent one-genuine-
branch search specification, while retaining its global DAG witness. -/
public theorem exists_oneChoicePresentation_of_is_AcyclicTwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicTwoMatchingLBA L) :
    ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
      (_ : DecidableEq Γ) (_ : DecidableEq Λ)
      (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
      M.ConfigurationAcyclic ∧
        M.HasTwoMatchingStepPartition ∧
        LBA.LanguageEnd M = L ∧
        ∀ input,
          LBA.BoundedNondeterminism.acceptsWithChoiceEventsSearch M
              (LBA.initCfgEnd M input) 1 = true ↔
            LBA.LanguageEnd M input := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hacyclic, hlayers, hM⟩
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  refine ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M,
    hacyclic, hlayers, hM, ?_⟩
  intro input
  exact LBA.BoundedNondeterminism.acceptsWithChoiceEventsSearch_one_eq_true_iff
    M hlayers (LBA.initCfgEnd M input)

end
