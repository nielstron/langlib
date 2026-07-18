module

public import Langlib.Automata.LinearBounded.DeterministicSweeping.Simulation
public import Langlib.Automata.LinearBounded.DeterministicSweeping.Sweeping

@[expose]
public section

/-!
# Sweeping deterministic LBAs characterize deterministic LBAs

Every deterministic linearly bounded automaton has an equivalent deterministic presentation
whose physical head changes genuine direction only at a tape endpoint.  The construction keeps
exactly the input-sized tape: it enlarges the finite tape alphabet and finite control, performs
an initialization sweep, and subsequently simulates one source transition per complete sweep.

The sweeping promise is the strong trace predicate from `LBA.Machine.SweepingViaEmbed`, applied
to the standard deterministic-to-nondeterministic view.  It therefore covers every finite
prefix from every canonical nonempty input, including rejecting computations.  The named DLBA
language class retains its separate Boolean decision for the empty word.

This is a normal-form theorem *within* deterministic linear space.  It does not turn a
nondeterministic LBA into a deterministic machine and hence has no bearing on the open equality
`LBA = DLBA`.
-/

/-- A language has a sweeping deterministic-LBA presentation when it is recognized using the
canonical `Option (T ⊕ Γ)` input embedding and every finite trace from a canonical nonempty
input is sweeping.  The separate Boolean is the presentation's decision for the empty word. -/
@[expose]
public def is_SweepingDLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (acceptEmpty : Bool)
    (M : DLBA.Machine (Option (T ⊕ Γ)) Λ),
    M.SweepingViaEmbed (fun t => some (Sum.inl t)) ∧
      DLBA.LanguageRecognized M (fun t => some (Sum.inl t)) acceptEmpty = L

/-- Languages recognized by deterministic LBAs satisfying the strong sweeping promise. -/
@[expose]
public def SweepingDLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_SweepingDLBA

/-- Forgetting the sweeping promise gives an ordinary DLBA presentation. -/
public theorem is_SweepingDLBA_imp_is_DLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_SweepingDLBA L) : is_DLBA L := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, acceptEmpty, M, _hsweeping, hM⟩ := hL
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, acceptEmpty, M, hM⟩

/-- Sweeping deterministic-LBA languages are deterministic-LBA languages. -/
public theorem SweepingDLBA_subset_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (SweepingDLBA : Set (Language T)) ⊆ DLBA :=
  fun _ hL => is_SweepingDLBA_imp_is_DLBA hL

/-- Every DLBA language has a same-width deterministic presentation whose every finite trace
from a canonical nonempty input is sweeping. -/
public theorem is_DLBA_imp_is_SweepingDLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_DLBA L) : is_SweepingDLBA L := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, acceptEmpty, M, hM⟩ := hL
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  let embed : T → Option (T ⊕ Γ) := fun t => some (.inl t)
  refine ⟨
    DLBA.DeterministicSweeping.Cell (Option (T ⊕ Γ)) Λ,
    DLBA.DeterministicSweeping.Phase Λ,
    inferInstance, inferInstance, inferInstance, inferInstance,
    acceptEmpty,
    DLBA.DeterministicSweeping.machine M embed,
    DLBA.DeterministicSweeping.machine_sweepingViaEmbed M embed,
    ?_⟩
  calc
    DLBA.LanguageRecognized
        (DLBA.DeterministicSweeping.machine M embed)
        DLBA.DeterministicSweeping.inputEmbed acceptEmpty =
        DLBA.LanguageRecognized M embed acceptEmpty := by
      funext word
      simp only [DLBA.LanguageRecognized]
      rw [DLBA.DeterministicSweeping.machine_languageViaEmbed]
    _ = L := hM

/-- Every deterministic-LBA language is recognized by a sweeping deterministic LBA. -/
public theorem DLBA_subset_SweepingDLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (DLBA : Set (Language T)) ⊆ SweepingDLBA :=
  fun _ hL => is_DLBA_imp_is_SweepingDLBA hL

/-- Sweeping and unrestricted deterministic LBAs recognize exactly the same named language
class. -/
public theorem SweepingDLBA_eq_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (SweepingDLBA : Set (Language T)) = DLBA :=
  Set.Subset.antisymm SweepingDLBA_subset_DLBA DLBA_subset_SweepingDLBA

/-- Pointwise form of the deterministic sweeping characterization. -/
public theorem is_SweepingDLBA_iff_is_DLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_SweepingDLBA L ↔ is_DLBA L :=
  ⟨is_SweepingDLBA_imp_is_DLBA, is_DLBA_imp_is_SweepingDLBA⟩

/-- Base-class-first pointwise form of the deterministic sweeping characterization. -/
public theorem is_DLBA_iff_is_SweepingDLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_DLBA L ↔ is_SweepingDLBA L :=
  (is_SweepingDLBA_iff_is_DLBA L).symm

/-- Membership form of the exact deterministic sweeping class equality. -/
public theorem mem_SweepingDLBA_iff_mem_DLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    L ∈ (SweepingDLBA : Set (Language T)) ↔ L ∈ DLBA :=
  is_SweepingDLBA_iff_is_DLBA L

end
