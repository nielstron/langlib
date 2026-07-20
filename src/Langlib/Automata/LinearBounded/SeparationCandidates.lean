module

public import Langlib.Automata.LinearBounded.MatchingLayerHierarchy
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.StrictDegreeCharacterization
public import Langlib.Automata.LinearBounded.EncodedMembership
public import Langlib.Automata.LinearBounded.LinearChoiceLanguage

@[expose]
public section

/-!
# Candidate languages for separating LBA from DLBA

This file packages several equivalent, fully proved interfaces for the first LBA problem.  It
does not postulate a separating language or a pumping lemma.  Instead, it records exactly what a
candidate must satisfy and turns any independently proved deterministic-LBA invariant into a
sound separation criterion.

The candidate search may be restricted without loss to either of two concrete normal forms:

* globally acyclic, directed-degree-two LBAs with three exact matching layers;
* acyclic, directed-degree-two certified row systems with `Unit` certificates.

Equivalently, a separator is precisely a language that requires the third matching layer: three
layers present every LBA language, whereas two layers present exactly the DLBA languages.
-/

open Classical

/-- A language separating nondeterministic from deterministic linear-bounded automata. -/
public def IsLBADLBASeparator
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  is_LBA L ∧ ¬ is_DLBA L

/-- A separator exists exactly when the two language classes are unequal. -/
public theorem exists_lbaDLBASeparator_iff_ne
    {T : Type} [Fintype T] [DecidableEq T] :
    (∃ L : Language T, IsLBADLBASeparator L) ↔
      (LBA : Set (Language T)) ≠ DLBA := by
  constructor
  · rintro ⟨L, hLBA, hnotDLBA⟩ heq
    apply hnotDLBA
    change L ∈ (DLBA : Set (Language T))
    rw [← heq]
    exact hLBA
  · intro hne
    by_contra hnone
    apply hne
    apply Set.Subset.antisymm
    · intro L hLBA
      by_contra hnotDLBA
      exact hnone ⟨L, hLBA, hnotDLBA⟩
    · exact DLBA_subset_LBA

/-! ## The exact encoded candidate family -/

/-- For an ordinary local LBA code, separation reduces pointwise to failure of deterministic-LBA
recognizability: `languageOf` is already proved to denote an LBA language for every total code,
including the zero-state convention. -/
public theorem isLBADLBASeparator_languageOf_iff
    {T : Type} [Fintype T] [DecidableEq T]
    (code : LBA.EncodedMembership.Code T) :
    IsLBADLBASeparator (LBA.EncodedMembership.languageOf code) ↔
      ¬ is_DLBA (LBA.EncodedMembership.languageOf code) := by
  constructor
  · exact And.right
  · intro hnotDLBA
    exact ⟨LBA.EncodedMembership.is_LBA_languageOf code, hnotDLBA⟩

/-- A separator exists exactly when some ordinary numeric LBA code denotes a language outside
DLBA.  Adequacy of `languageOf` supplies the code in the forward direction; soundness supplies
the LBA half of the separator in the reverse direction. -/
public theorem exists_lbaDLBASeparator_iff_encodedLanguage
    {T : Type} [Fintype T] [DecidableEq T] :
    (∃ L : Language T, IsLBADLBASeparator L) ↔
      ∃ code : LBA.EncodedMembership.Code T,
        ¬ is_DLBA (LBA.EncodedMembership.languageOf code) := by
  constructor
  · rintro ⟨L, hLBA, hnotDLBA⟩
    obtain ⟨code, hcode⟩ :=
      LBA.EncodedMembership.exists_code_languageOf_eq_of_is_LBA hLBA
    refine ⟨code, ?_⟩
    rw [hcode]
    exact hnotDLBA
  · rintro ⟨code, hnotDLBA⟩
    exact ⟨LBA.EncodedMembership.languageOf code,
      (isLBADLBASeparator_languageOf_iff code).2 hnotDLBA⟩

/-- Class inequality is equivalently witnessed by one ordinary encoded LBA language that has no
DLBA presentation. -/
public theorem lba_ne_dlba_iff_exists_encodedLanguage
    {T : Type} [Fintype T] [DecidableEq T] :
    (LBA : Set (Language T)) ≠ DLBA ↔
      ∃ code : LBA.EncodedMembership.Code T,
        ¬ is_DLBA (LBA.EncodedMembership.languageOf code) := by
  rw [← exists_lbaDLBASeparator_iff_ne]
  exact exists_lbaDLBASeparator_iff_encodedLanguage

/-- Dually, equality holds exactly when every language in the adequate ordinary-code family has
a deterministic-LBA presentation.  This remains a statement about a family indexed by codes,
not a claim that the joint code-and-word evaluator is itself one complete LBA language. -/
public theorem lba_eq_dlba_iff_every_encodedLanguage
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ∀ code : LBA.EncodedMembership.Code T,
        is_DLBA (LBA.EncodedMembership.languageOf code) := by
  constructor
  · intro heq code
    have hL : LBA.EncodedMembership.languageOf code ∈
        (LBA : Set (Language T)) :=
      LBA.EncodedMembership.is_LBA_languageOf code
    rw [heq] at hL
    exact hL
  · intro hcodes
    apply Set.Subset.antisymm ?_ DLBA_subset_LBA
    intro L hL
    obtain ⟨code, hcode⟩ :=
      LBA.EncodedMembership.exists_code_languageOf_eq_of_is_LBA hL
    rw [← hcode]
    exact hcodes code

/-- The separator predicate can be checked against the acyclic degree-two three-matching normal
form pointwise: every LBA language has such a presentation, and forgetting the presentation
gives an LBA witness. -/
public theorem isLBADLBASeparator_iff_acyclicDegreeTwoThreeMatching
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    IsLBADLBASeparator L ↔
      is_AcyclicDegreeTwoThreeMatchingLBA L ∧ ¬ is_DLBA L := by
  rw [IsLBADLBASeparator, is_LBA_iff_is_AcyclicDegreeTwoThreeMatchingLBA]

/-- Thus a separator exists exactly when one exists inside the rigid acyclic degree-two
three-matching normal form. -/
public theorem exists_lbaDLBASeparator_iff_acyclicDegreeTwoThreeMatching
    {T : Type} [Fintype T] [DecidableEq T] :
    (∃ L : Language T, IsLBADLBASeparator L) ↔
      ∃ L : Language T,
        is_AcyclicDegreeTwoThreeMatchingLBA L ∧ ¬ is_DLBA L := by
  apply exists_congr
  exact isLBADLBASeparator_iff_acyclicDegreeTwoThreeMatching

/-- A language requires the third exact matching layer when it has a three-layer presentation
but no two-layer presentation. -/
public def RequiresThreeMatchingLayers
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  is_KMatchingLBA 3 L ∧ ¬ is_KMatchingLBA 2 L

/-- Requiring the third matching layer is exactly the LBA-versus-DLBA separator predicate. -/
public theorem requiresThreeMatchingLayers_iff_isLBADLBASeparator
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    RequiresThreeMatchingLayers L ↔ IsLBADLBASeparator L := by
  change
    (L ∈ (KMatchingLBA 3 : Set (Language T)) ∧
        L ∉ (KMatchingLBA 2 : Set (Language T))) ↔
      (L ∈ (LBA : Set (Language T)) ∧ L ∉ (DLBA : Set (Language T)))
  rw [KMatchingLBA_three_eq_LBA, KMatchingLBA_two_eq_DLBA]

/-- A language requiring three matching layers exists exactly if LBA differs from DLBA. -/
public theorem exists_requiresThreeMatchingLayers_iff_lba_ne_dlba
    {T : Type} [Fintype T] [DecidableEq T] :
    (∃ L : Language T, RequiresThreeMatchingLayers L) ↔
      (LBA : Set (Language T)) ≠ DLBA := by
  rw [← exists_lbaDLBASeparator_iff_ne]
  apply exists_congr
  exact requiresThreeMatchingLayers_iff_isLBADLBASeparator

/-- Equivalently, a language requires three matching layers exactly when the third and second
levels of the matching-layer hierarchy are unequal. -/
public theorem exists_requiresThreeMatchingLayers_iff_matchingClasses_ne
    {T : Type} [Fintype T] [DecidableEq T] :
    (∃ L : Language T, RequiresThreeMatchingLayers L) ↔
      (KMatchingLBA 3 : Set (Language T)) ≠ KMatchingLBA 2 := by
  rw [KMatchingLBA_three_eq_LBA, KMatchingLBA_two_eq_DLBA]
  exact exists_requiresThreeMatchingLayers_iff_lba_ne_dlba

/-- A proposed deterministic-LBA pumping invariant consists of a semantic language property
together with a proof that every DLBA language has that property.  Storing the necessity proof
prevents an encoding or an unproved conjecture from being treated as a separation argument. -/
public structure DLBAPumpingInvariant
    (T : Type) [Fintype T] [DecidableEq T] where
  property : Language T → Prop
  necessary_of_is_DLBA : ∀ {L : Language T}, is_DLBA L → property L

public instance DLBAPumpingInvariant.instCoeFun
    {T : Type} [Fintype T] [DecidableEq T] :
    CoeFun (DLBAPumpingInvariant T) (fun _ => Language T → Prop) where
  coe invariant := invariant.property

/-- Refuting a proved DLBA invariant rules out every deterministic-LBA presentation. -/
public theorem DLBAPumpingInvariant.not_is_DLBA_of_not
    {T : Type} [Fintype T] [DecidableEq T]
    (invariant : DLBAPumpingInvariant T) {L : Language T}
    (hrefute : ¬ invariant L) : ¬ is_DLBA L := by
  intro hDLBA
  exact hrefute (invariant.necessary_of_is_DLBA hDLBA)

/-- An LBA language refuting a proved DLBA invariant is a separator. -/
public theorem DLBAPumpingInvariant.isLBADLBASeparator_of_is_LBA_of_not
    {T : Type} [Fintype T] [DecidableEq T]
    (invariant : DLBAPumpingInvariant T) {L : Language T}
    (hLBA : is_LBA L) (hrefute : ¬ invariant L) :
  IsLBADLBASeparator L :=
  ⟨hLBA, invariant.not_is_DLBA_of_not hrefute⟩

/-- The checked linear accepting-choice property is one concrete DLBA pumping invariant.  The
necessity theorem is sharp at the presentation level: the canonical endmarker translation of a
DLBA is functional and therefore uses zero genuine branch events. -/
public def linearChoiceInvariant
    (T : Type) [Fintype T] [DecidableEq T] : DLBAPumpingInvariant T where
  property := is_LinearChoiceLBA
  necessary_of_is_DLBA := is_LinearChoiceLBA_of_is_DLBA

/-- The proposed anti-pumping condition `RequiresSuperlinearChoice` is therefore a sound
language-separation criterion.  It quantifies over every equivalent finite LBA presentation. -/
public theorem isLBADLBASeparator_of_requiresSuperlinearChoice
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : RequiresSuperlinearChoice L) : IsLBADLBASeparator L :=
  (linearChoiceInvariant T).isLBADLBASeparator_of_is_LBA_of_not hL.1 hL.2

/-- Any witness to the superlinear-choice anti-pumping condition would disprove class equality. -/
public theorem lba_ne_dlba_of_exists_requiresSuperlinearChoice
    {T : Type} [Fintype T] [DecidableEq T]
    (hcandidate : ∃ L : Language T, RequiresSuperlinearChoice L) :
    (LBA : Set (Language T)) ≠ DLBA := by
  apply exists_lbaDLBASeparator_iff_ne.mp
  obtain ⟨L, hL⟩ := hcandidate
  exact ⟨L, isLBADLBASeparator_of_requiresSuperlinearChoice hL⟩

namespace CertifiedRowSystem

/-- Every finite certified-row reachability language is an LBA language.  The compiled positive
LBA already proves context sensitivity, and the canonical endmarker characterization then
handles the empty word (which row-reachability rejects by definition). -/
public theorem is_LBA_rowReachLanguage
    {I A C Q F : Type} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype Q] [DecidableEq Q] [Fintype F] [DecidableEq F]
    (D : CertifiedRowSystem I A C Q F) :
    is_LBA D.rowReachLanguage :=
  CS_subset_LBA
    (is_LBA_pos_imp_isCS (is_LBA_pos_rowReachLanguage D))

end CertifiedRowSystem

/-- A language presented as reachability in an acyclic, unit-certified row relation whose
indegree and outdegree are both at most two. -/
public def is_AcyclicDegreeTwoUnitCertificateRowReachLanguage
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (A Q F : Type) (_ : Fintype A) (_ : Fintype Q) (_ : Fintype F)
    (_ : DecidableEq A) (_ : DecidableEq Q) (_ : DecidableEq F)
    (D : CertifiedRowSystem T A Unit Q F),
    CertifiedRowSystem.RowAcyclic D ∧
      CertifiedRowSystem.RowDirectedDegreeAtMost 2 D ∧
      D.rowReachLanguage = L

/-- A concrete restricted row system presents a language in the candidate class. -/
public theorem is_AcyclicDegreeTwoUnitCertificateRowReachLanguage_rowReachLanguage
    {T A Q F : Type} [Fintype T] [DecidableEq T]
    [Fintype A] [Fintype Q] [Fintype F]
    [DecidableEq A] [DecidableEq Q] [DecidableEq F]
    (D : CertifiedRowSystem T A Unit Q F)
    (hacyclic : CertifiedRowSystem.RowAcyclic D)
    (hdegree : CertifiedRowSystem.RowDirectedDegreeAtMost 2 D) :
    is_AcyclicDegreeTwoUnitCertificateRowReachLanguage D.rowReachLanguage :=
  ⟨A, Q, F, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, D, hacyclic, hdegree, rfl⟩

/-- Every language in the restricted certified-row candidate class is an LBA language. -/
public theorem is_LBA_of_is_AcyclicDegreeTwoUnitCertificateRowReachLanguage
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicDegreeTwoUnitCertificateRowReachLanguage L) :
    is_LBA L := by
  rcases hL with
    ⟨A, Q, F, hA, hQ, hF, hdecA, hdecQ, hdecF, D,
      _hacyclic, _hdegree, hlanguage⟩
  letI := hA
  letI := hQ
  letI := hF
  letI := hdecA
  letI := hdecQ
  letI := hdecF
  rw [← hlanguage]
  exact D.is_LBA_rowReachLanguage

/-- A restricted certified-row language refuting a proved DLBA invariant is a separator. -/
public theorem DLBAPumpingInvariant.isLBADLBASeparator_of_restrictedRowReach_of_not
    {T : Type} [Fintype T] [DecidableEq T]
    (invariant : DLBAPumpingInvariant T) {L : Language T}
    (hrow : is_AcyclicDegreeTwoUnitCertificateRowReachLanguage L)
    (hrefute : ¬ invariant L) : IsLBADLBASeparator L :=
  invariant.isLBADLBASeparator_of_is_LBA_of_not
    (is_LBA_of_is_AcyclicDegreeTwoUnitCertificateRowReachLanguage hrow) hrefute

/-- Direct system-level form of the restricted-row separation criterion. -/
public theorem DLBAPumpingInvariant.isLBADLBASeparator_rowReachLanguage
    {T A Q F : Type} [Fintype T] [DecidableEq T]
    [Fintype A] [Fintype Q] [Fintype F]
    [DecidableEq A] [DecidableEq Q] [DecidableEq F]
    (invariant : DLBAPumpingInvariant T)
    (D : CertifiedRowSystem T A Unit Q F)
    (hacyclic : CertifiedRowSystem.RowAcyclic D)
    (hdegree : CertifiedRowSystem.RowDirectedDegreeAtMost 2 D)
    (hrefute : ¬ invariant D.rowReachLanguage) :
    IsLBADLBASeparator D.rowReachLanguage :=
  invariant.isLBADLBASeparator_of_restrictedRowReach_of_not
    (is_AcyclicDegreeTwoUnitCertificateRowReachLanguage_rowReachLanguage
      D hacyclic hdegree)
    hrefute

/-- Existence of an LBA/DLBA separator is unchanged when candidate languages are restricted to
acyclic, degree-two, unit-certificate row reachability.  This is an existential version of the
strict certified-row characterization, not an assumption that a separator exists. -/
public theorem exists_lbaDLBASeparator_iff_restrictedRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    (∃ L : Language T, IsLBADLBASeparator L) ↔
      ∃ L : Language T,
        is_AcyclicDegreeTwoUnitCertificateRowReachLanguage L ∧
          ¬ is_DLBA L := by
  constructor
  · intro hseparator
    by_contra hnone
    have hEvery :
        CertifiedRowSystem.EveryAcyclicDegreeTwoUnitCertificateRowReachLanguageIsDLBA T := by
      intro A Q F hA hQ hF hdecA hdecQ hdecF D hacyclic hdegree
      letI := hA
      letI := hQ
      letI := hF
      letI := hdecA
      letI := hdecQ
      letI := hdecF
      by_contra hnotDLBA
      apply hnone
      exact ⟨D.rowReachLanguage,
        is_AcyclicDegreeTwoUnitCertificateRowReachLanguage_rowReachLanguage
          D hacyclic hdegree,
        hnotDLBA⟩
    have heq : (LBA : Set (Language T)) = DLBA :=
      CertifiedRowSystem.lba_eq_dlba_iff_acyclicDegreeTwoUnitCertificateRowReach.mpr
        hEvery
    exact (exists_lbaDLBASeparator_iff_ne.mp hseparator) heq
  · rintro ⟨L, hrow, hnotDLBA⟩
    exact ⟨L,
      is_LBA_of_is_AcyclicDegreeTwoUnitCertificateRowReachLanguage hrow,
      hnotDLBA⟩

end
