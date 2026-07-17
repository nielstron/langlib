module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.LBA
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Determinize
public import Langlib.Automata.DeterministicLinearBounded.Inclusion.LinearBounded
public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Powerset

@[expose]
public section

/-!
# The first LBA problem as certified-row reachability

A finite `CertifiedRowSystem` presents an implicit directed graph whose vertices are
fixed-width rows.  Its edge relation is checked by a finite left-to-right verifier, and its
language asks whether a final row is reachable from the row encoding the input.

This file proves that determinizing all such row-reachability languages is exactly the positive
(nonempty-input) form of the first LBA problem:

* every finite certified row system compiles to an input-sized nondeterministic LBA;
* every input-sized nondeterministic LBA has an equivalent certified row system exposing its
  configuration graph.

The theorem does not resolve the problem.  It isolates the unresolved operation as deterministic
reachability in a finite, locally certified, exponentially large row graph.  Determinizing the
one-step verifier by subset construction is insufficient: path selection remains nondeterministic.
-/

/-- Every finite certified-row reachability language over `T` has a deterministic-LBA
presentation.  This is a convenient exact formulation of the unresolved reachability step. -/
public def EveryCertifiedRowReachLanguageIsDLBA
    (T : Type) [Fintype T] [DecidableEq T] : Prop :=
  ∀ (A C Q F : Type)
    [Fintype A] [Fintype C] [Fintype Q] [Fintype F]
    [DecidableEq A] [DecidableEq C] [DecidableEq Q] [DecidableEq F]
    (S : CertifiedRowSystem T A C Q F),
    is_DLBA S.rowReachLanguage

/-- Every finite certified-row reachability language whose local edge verifier has no
certificate choice has a deterministic-LBA presentation.

With certificate alphabet `Unit`, the verifier's state update is deterministic once the old and
new rows are fixed.  The successor row itself is still chosen nondeterministically, so this
property retains precisely the global path-selection issue. -/
public def EveryUnitCertificateRowReachLanguageIsDLBA
    (T : Type) [Fintype T] [DecidableEq T] : Prop :=
  ∀ (A Q F : Type)
    [Fintype A] [Fintype Q] [Fintype F]
    [DecidableEq A] [DecidableEq Q] [DecidableEq F]
    (S : CertifiedRowSystem T A Unit Q F),
    is_DLBA S.rowReachLanguage

/-- Allowing a finite certificate alphabet in the local edge verifier does not change the
determinization problem.  The ordinary subset construction replaces every such verifier by an
equivalent `Unit`-certificate verifier while preserving the row-reachability language exactly. -/
public theorem everyCertifiedRowReach_iff_unitCertificateRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    EveryCertifiedRowReachLanguageIsDLBA T ↔
      EveryUnitCertificateRowReachLanguageIsDLBA T := by
  constructor
  · intro hrows A Q F hA hQ hF hdA hdQ hdF S
    letI := hA
    letI := hQ
    letI := hF
    letI := hdA
    letI := hdQ
    letI := hdF
    exact hrows A Unit Q F S
  · intro hrows A C Q F hA hC hQ hF hdA hdC hdQ hdF S
    letI := hA
    letI := hC
    letI := hQ
    letI := hF
    letI := hdA
    letI := hdC
    letI := hdQ
    letI := hdF
    have hdet : is_DLBA S.determinize.rowReachLanguage :=
      hrows A (Finset Q) F S.determinize
    rwa [S.rowReachLanguage_determinize] at hdet

/-- Determinizing every positive LBA language is equivalent to determinizing the reachability
language of every finite certified row system.

The forward direction uses the certified-row-to-LBA compiler.  The reverse direction exposes an
arbitrary LBA's configurations as rows, applies the assumed deterministic presentation, and uses
the exact row-language correspondence. -/
public theorem lba_pos_subset_dlba_iff_certifiedRowReach
    {T : Type} [hT : Fintype T] [hdecT : DecidableEq T] :
    (∀ L : Language T, is_LBA_pos L → is_DLBA L) ↔
      EveryCertifiedRowReachLanguageIsDLBA T := by
  constructor
  · intro hdet A C Q F hA hC hQ hF hdA hdC hdQ hdF S
    letI := hA
    letI := hC
    letI := hQ
    letI := hF
    letI := hdA
    letI := hdC
    letI := hdQ
    letI := hdF
    exact hdet S.rowReachLanguage
      (CertifiedRowSystem.is_LBA_pos_rowReachLanguage S)
  · intro hrows L hL
    obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ := hL
    haveI := hΓ
    haveI := hΛ
    haveI := hdΓ
    haveI := hdΛ
    letI : Fintype (T ⊕ Γ) := @instFintypeSum T Γ hT hΓ
    let htape : Fintype (Option (T ⊕ Γ)) := inferInstance
    letI : Fintype (LBA.RowCell T (Option (T ⊕ Γ)) Λ) :=
      @LBA.instFintypeRowCell T (Option (T ⊕ Γ)) Λ hT htape hΛ
    letI : DecidableEq (LBA.RowCell T (Option (T ⊕ Γ)) Λ) :=
      inferInstance
    let S :=
      LBA.certifiedRowSystem M
        (fun t : T => (some (Sum.inl t) : Option (T ⊕ Γ)))
    have hdet : is_DLBA S.rowReachLanguage :=
      hrows
        (LBA.RowCell T (Option (T ⊕ Γ)) Λ)
        LBA.RowCert
        (LBA.RowScan Λ)
        (LBA.RowFinal Λ)
        S
    have hrow :
        S.rowReachLanguage =
          LBA.LanguageViaEmbed M
            (fun t : T => (some (Sum.inl t) : Option (T ⊕ Γ))) :=
      LBA.certifiedRowSystem_rowReachLanguage M
        (fun t : T => (some (Sum.inl t) : Option (T ⊕ Γ)))
    rw [hrow, hM] at hdet
    exact hdet

/-- A deterministic-LBA presentation can freely change its decision on the empty word while
keeping the same machine for every nonempty word. -/
private theorem is_DLBA_of_eq_on_nonempty
    {T : Type} [Fintype T] [DecidableEq T]
    {K L : Language T} (hK : is_DLBA K)
    (hKL : ∀ w : List T, w ≠ [] → (w ∈ K ↔ w ∈ L)) :
    is_DLBA L := by
  classical
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, _acceptEmpty, M, hM⟩ := hK
  letI := hΓ
  letI := hΛ
  letI := hdΓ
  letI := hdΛ
  refine ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, decide ([] ∈ L), M, ?_⟩
  funext w
  by_cases hw : w = []
  · subst w
    apply propext
    simp [DLBA.LanguageRecognized, DLBA.LanguageViaEmbed]
    rfl
  · calc
      DLBA.LanguageRecognized M (fun t => some (Sum.inl t))
          (decide ([] ∈ L)) w =
          DLBA.LanguageRecognized M (fun t => some (Sum.inl t))
            _acceptEmpty w := by
              apply propext
              simp [DLBA.LanguageRecognized, hw]
      _ = K w := congrFun hM w
      _ = L w := propext (hKL w hw)

/-- The full first LBA problem is equivalent to the certified-row reachability formulation.

The empty word does not create an extra obstacle.  An endmarker LBA is first converted to its
marker-free positive core; after determinizing that core, the explicit DLBA empty-word bit is set
to match the original language. -/
public theorem lba_subset_dlba_iff_certifiedRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) ⊆ DLBA) ↔
      EveryCertifiedRowReachLanguageIsDLBA T := by
  classical
  rw [← lba_pos_subset_dlba_iff_certifiedRowReach]
  constructor
  · intro hfull L hpos
    exact hfull (CS_subset_LBA (is_LBA_pos_imp_isCS hpos))
  · intro hpos L hL
    obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ := hL
    letI := hΓ
    letI := hΛ
    letI := hdΓ
    letI := hdΛ
    let b : Bool := decide (LBA.Accepts M (LBA.initCfgEnd M []))
    have hb : b = true ↔ LBA.Accepts M (LBA.initCfgEnd M []) := by
      simp [b]
    let K : Language T :=
      LBA.LanguageViaEmbed (LBA.flagMachine M)
        (fun t : T => some (Sum.inl t))
    have hKpos : is_LBA_pos K := by
      exact ⟨LBA.FoldCell T Γ, LBA.FState Λ, inferInstance, inferInstance,
        inferInstance, inferInstance, LBA.flagMachine M, rfl⟩
    have hKdet : is_DLBA K := hpos K hKpos
    apply is_DLBA_of_eq_on_nonempty hKdet
    intro w hw
    have hfull :
        LBA.LanguageRecognized (LBA.flagMachine M)
            (fun t : T => some (Sum.inl t)) b = L :=
      (LBA.language_flagMachine_eq M b hb).trans hM
    have hwEq := congrFun hfull w
    simpa [K, LBA.LanguageRecognized, hw] using hwEq

/-- Equality of the two automaton language classes is exactly deterministic
certified-row reachability.  The reverse inclusion `DLBA ⊆ LBA` is unconditional. -/
public theorem lba_eq_dlba_iff_certifiedRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      EveryCertifiedRowReachLanguageIsDLBA T := by
  rw [Set.Subset.antisymm_iff]
  simp only [DLBA_subset_LBA, and_true]
  exact lba_subset_dlba_iff_certifiedRowReach

/-- The full first LBA problem is already equivalent to deterministic-LBA reachability for
certified row systems with a deterministic local edge verifier.  Thus certificate guessing in
one-step verification is eliminable; the unresolved nondeterminism is the choice of a path through
the exponentially large row graph. -/
public theorem lba_subset_dlba_iff_unitCertificateRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) ⊆ DLBA) ↔
      EveryUnitCertificateRowReachLanguageIsDLBA T :=
  lba_subset_dlba_iff_certifiedRowReach.trans
    everyCertifiedRowReach_iff_unitCertificateRowReach

/-- The exact equality question already occurs for row systems with deterministic local
edge verification. -/
public theorem lba_eq_dlba_iff_unitCertificateRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      EveryUnitCertificateRowReachLanguageIsDLBA T :=
  lba_eq_dlba_iff_certifiedRowReach.trans
    everyCertifiedRowReach_iff_unitCertificateRowReach

end
