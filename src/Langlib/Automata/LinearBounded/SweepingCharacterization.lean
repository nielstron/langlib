module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.LBA

@[expose]
public section

/-!
# Sweeping marker-free LBAs characterize marker-free LBAs

This file packages the semantic sweeping promise on concrete bounded-tape traces as a language
class.  A presentation is sweeping when every trace from every canonically encoded nonempty
input changes genuine head direction only at a physical endpoint.  The promise therefore covers
rejecting traces and finite prefixes, not only chosen accepting computations.

The certified-row round trip gives every marker-free LBA language such a presentation.  No
nonemptiness or cardinality hypothesis is imposed on either finite auxiliary alphabet.
-/

/-- A language has a sweeping marker-free LBA presentation when it is recognized using the
canonical `Option (T ⊕ Γ)` input embedding and every concrete trace from an encoded input is
sweeping.  Both the work alphabet and state type are arbitrary finite types. -/
@[expose]
public def is_SweepingLBA_pos
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (Option (T ⊕ Γ)) Λ),
    M.SweepingViaEmbed (fun t => some (Sum.inl t)) ∧
      LBA.LanguageViaEmbed M (fun t => some (Sum.inl t)) = L

/-- Languages recognized by sweeping marker-free LBAs on their input-sized tape. -/
@[expose]
public def SweepingLBA_pos
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_SweepingLBA_pos

/-- Forgetting the all-traces sweeping promise gives an ordinary marker-free LBA
presentation. -/
public theorem is_SweepingLBA_pos_imp_is_LBA_pos
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_SweepingLBA_pos L) : is_LBA_pos L := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hsweeping, hM⟩ := hL
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- Sweeping marker-free LBA languages are marker-free LBA languages. -/
public theorem SweepingLBA_pos_subset_LBA_pos
    {T : Type} [Fintype T] [DecidableEq T] :
    (SweepingLBA_pos : Set (Language T)) ⊆ LBA_pos :=
  fun _ hL => is_SweepingLBA_pos_imp_is_LBA_pos hL

/-- Every marker-free LBA language has a presentation whose every concrete trace is sweeping.

The construction exposes the source machine's configuration graph as a certified row system and
then uses the sweeping row-system compiler. -/
public theorem is_LBA_pos_imp_is_SweepingLBA_pos
    {T : Type} [hT : Fintype T] [hdecT : DecidableEq T] {L : Language T}
    (hL : is_LBA_pos L) : is_SweepingLBA_pos L := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩ := hL
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  let embed : T → Option (T ⊕ Γ) := fun t => some (.inl t)
  let S := LBA.certifiedRowSystem M embed
  refine ⟨
    CertifiedRowSystem.WorkCell
      (LBA.RowCell T (Option (T ⊕ Γ)) Λ) LBA.RowCert,
    CertifiedRowSystem.State (LBA.RowScan Λ) (LBA.RowFinal Λ),
    inferInstance, inferInstance, inferInstance, inferInstance,
    CertifiedRowSystem.machine S,
    CertifiedRowSystem.machine_sweepingViaEmbed S,
    ?_⟩
  calc
    LBA.LanguageViaEmbed (CertifiedRowSystem.machine S)
        (fun t => some (Sum.inl t)) =
        S.rowReachLanguage :=
      CertifiedRowSystem.languageViaEmbed_machine_eq_rowReachLanguage S
    _ = LBA.LanguageViaEmbed M embed :=
      LBA.certifiedRowSystem_rowReachLanguage M embed
    _ = L := hM

/-- Every marker-free LBA language is recognized by a sweeping marker-free LBA. -/
public theorem LBA_pos_subset_SweepingLBA_pos
    {T : Type} [Fintype T] [DecidableEq T] :
    (LBA_pos : Set (Language T)) ⊆ SweepingLBA_pos :=
  fun _ hL => is_LBA_pos_imp_is_SweepingLBA_pos hL

/-- Sweeping and unrestricted marker-free LBAs recognize exactly the same named language
class. -/
public theorem SweepingLBA_pos_eq_LBA_pos
    {T : Type} [Fintype T] [DecidableEq T] :
    (SweepingLBA_pos : Set (Language T)) = LBA_pos :=
  Set.Subset.antisymm SweepingLBA_pos_subset_LBA_pos
    LBA_pos_subset_SweepingLBA_pos

/-- Pointwise form of the exact sweeping characterization. -/
public theorem is_SweepingLBA_pos_iff_is_LBA_pos
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_SweepingLBA_pos L ↔ is_LBA_pos L :=
  ⟨is_SweepingLBA_pos_imp_is_LBA_pos,
    is_LBA_pos_imp_is_SweepingLBA_pos⟩

/-- The conventional base-class-first orientation of the pointwise characterization. -/
public theorem is_LBA_pos_iff_is_SweepingLBA_pos
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA_pos L ↔ is_SweepingLBA_pos L :=
  (is_SweepingLBA_pos_iff_is_LBA_pos L).symm

/-- Membership form of the exact equality between the two named classes. -/
public theorem mem_SweepingLBA_pos_iff_mem_LBA_pos
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    L ∈ (SweepingLBA_pos : Set (Language T)) ↔ L ∈ LBA_pos :=
  is_SweepingLBA_pos_iff_is_LBA_pos L

end
