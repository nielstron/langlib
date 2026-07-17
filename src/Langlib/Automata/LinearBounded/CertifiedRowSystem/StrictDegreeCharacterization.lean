module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.BoundedDegree
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Characterization
import Mathlib.Tactic

@[expose]
public section

/-!
# The first LBA problem under simultaneous strict restrictions

This file combines three exact normalizations:

* incoming/outgoing serialization gives an equivalent LBA whose configuration graph has both
  directed degrees at most two;
* the LBA row presentation inherits those bounds, because its raw initialization edge targets a
  base-phase configuration with at most one machine predecessor;
* certificate determinization and strict clocking preserve the row relation and both degree
  bounds, while strict clocking makes it acyclic.

Consequently the first LBA problem is already equivalent to deterministic reachability for
acyclic, unit-certified row systems whose entire row relation has indegree and outdegree at most
two.
-/

open Classical

namespace CertifiedRowSystem

/-- Certificate determinization preserves every uniform directed-degree bound because it
preserves the row relation exactly. -/
public theorem rowDirectedDegreeAtMost_determinize
    {I A C Q F : Type*} [Fintype C] [DecidableEq Q]
    {bound : ℕ∞} (D : CertifiedRowSystem I A C Q F)
    (hdegree : RowDirectedDegreeAtMost bound D) :
    RowDirectedDegreeAtMost bound D.determinize := by
  constructor
  · intro old
    simpa only [D.rowStep_determinize_iff] using hdegree.1 old
  · intro new
    simpa only [D.rowStep_determinize_iff] using hdegree.2 new

/-- Deterministic-LBA reachability for the simultaneously restricted row systems. -/
public def EveryAcyclicDegreeTwoUnitCertificateRowReachLanguageIsDLBA
    (T : Type) [Fintype T] [DecidableEq T] : Prop :=
  ∀ (A Q F : Type)
    [Fintype A] [Fintype Q] [Fintype F]
    [DecidableEq A] [DecidableEq Q] [DecidableEq F]
    (D : CertifiedRowSystem T A Unit Q F),
    RowAcyclic D →
    RowDirectedDegreeAtMost 2 D →
    is_DLBA D.rowReachLanguage

/-- The full first LBA inclusion problem is unchanged even after imposing acyclicity,
unit certificates, and simultaneous row indegree/outdegree two. -/
public theorem lba_subset_dlba_iff_acyclicDegreeTwoUnitCertificateRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) ⊆ DLBA) ↔
      EveryAcyclicDegreeTwoUnitCertificateRowReachLanguageIsDLBA T := by
  constructor
  · intro hfull A Q F hA hQ hF hdA hdQ hdF D _ _
    letI := hA
    letI := hQ
    letI := hF
    letI := hdA
    letI := hdQ
    letI := hdF
    exact
      (lba_subset_dlba_iff_unitCertificateRowReach.mp hfull)
        A Q F D
  · intro hrestricted
    apply lba_subset_dlba_iff_certifiedRowReach.mpr
    apply lba_pos_subset_dlba_iff_certifiedRowReach.mp
    intro L hL
    obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ := hL
    letI := hΓ
    letI := hΛ
    letI := hdΓ
    letI := hdΛ
    let embed : T → Option (T ⊕ Γ) :=
      fun t => some (Sum.inl t)
    have hinjective : Function.Injective embed := by
      intro x y hxy
      simpa [embed] using hxy
    let B := M.boundedDegree
    let D₀ := LBA.certifiedRowSystem B embed
    let D := D₀.determinize
    have hdegree₀ : RowDirectedDegreeAtMost 2 D₀ := by
      exact LBA.CertifiedRows.certifiedRowSystem_rowDirectedDegreeAtMostTwo
        B embed hinjective
          M.boundedDegree_configurationDegreeAtMostTwo
          M.boundedDegree_initialConfigurationIndegreeAtMostOne
    have hdegree : RowDirectedDegreeAtMost 2 D :=
      rowDirectedDegreeAtMost_determinize D₀ hdegree₀
    have hclockDegree :
        RowDirectedDegreeAtMost 2 (strictAcyclicize D) :=
      rowDirectedDegreeAtMost_strictAcyclicize D hdegree
    have hdet :
        is_DLBA (strictAcyclicize D).rowReachLanguage :=
      hrestricted _ _ _ (strictAcyclicize D)
        (rowAcyclic_strictAcyclicize D) hclockDegree
    have hrows :
        (strictAcyclicize D).rowReachLanguage =
          LBA.LanguageViaEmbed M embed := by
      calc
        (strictAcyclicize D).rowReachLanguage =
            D.rowReachLanguage :=
          rowReachLanguage_strictAcyclicize D
        _ = D₀.rowReachLanguage :=
          D₀.rowReachLanguage_determinize
        _ = LBA.LanguageViaEmbed B embed :=
          LBA.certifiedRowSystem_rowReachLanguage B embed
        _ = LBA.LanguageViaEmbed M embed :=
          M.languageViaEmbed_boundedDegree_eq embed
    rw [hrows, hM] at hdet
    exact hdet

/-- Equality of LBA and DLBA is exactly deterministic reachability for acyclic,
unit-certified row relations with both directed degrees at most two. -/
public theorem lba_eq_dlba_iff_acyclicDegreeTwoUnitCertificateRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      EveryAcyclicDegreeTwoUnitCertificateRowReachLanguageIsDLBA T := by
  rw [Set.Subset.antisymm_iff]
  simp only [DLBA_subset_LBA, and_true]
  exact lba_subset_dlba_iff_acyclicDegreeTwoUnitCertificateRowReach

end CertifiedRowSystem

end
