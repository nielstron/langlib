module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.HistoryComplement

@[expose]
public section

/-!
# Semantic completeness of bundled histories

The certificate stored on a destination row is exactly the witness hidden in
`CertifiedRowSystem.RowStep`.  This file packages that observation in both
directions and characterizes nonemptiness of the alternating-history language
by ordinary row reachability.
-/

open Relation

namespace ContextFree.MalformedHistories

variable {I A C Q F VState : Type}

/-- Valid bundled histories with an arbitrary predicate on the underlying
first row.  The first row still has to carry no incoming certificate. -/
def bundledValidLanguageWith
    (S : CertifiedRowSystem I A C Q F)
    (Initial : List A → Prop) : Language (Symbol (BundledCell A C)) :=
  validLanguage
    (fun row => IsFirstBundledRow row ∧ Initial (underlyingRow row))
    (BundledFinal (systemFinalVerifier S)) (BundledStep S)

/-- The first row has no incoming transition certificate. -/
def bundleFirstRow (row : List A) : List (BundledCell A C) :=
  row.map fun a => (a, none)

@[simp] theorem underlyingRow_bundleFirstRow (row : List A) :
    underlyingRow (bundleFirstRow (C := C) row) = row := by
  simp [bundleFirstRow, underlyingRow, Function.comp_def]

@[simp] theorem bundleFirstRow_isFirst (row : List A) :
    IsFirstBundledRow (bundleFirstRow (C := C) row) := by
  rw [isFirstBundledRow_iff_forall]
  simp [bundleFirstRow]

/-- Attach a complete incoming certificate to a destination row.  The
mismatched cases are irrelevant: `RowStep` itself proves equal lengths. -/
def bundleCertificate : List A → List C → List (BundledCell A C)
  | [], [] => []
  | a :: row, c :: cert => (a, some c) :: bundleCertificate row cert
  | _, _ => []

theorem bundleCertificate_eq_of_length_eq
    {row : List A} {cert : List C} (hlen : row.length = cert.length) :
    underlyingRow (bundleCertificate row cert) = row ∧
      incomingCertificate (bundleCertificate row cert) = some cert := by
  induction row generalizing cert with
  | nil =>
      cases cert <;> simp_all [bundleCertificate, underlyingRow,
        incomingCertificate]
  | cons a row ih =>
      cases cert with
      | nil => simp at hlen
      | cons c cert =>
          have hlen' : row.length = cert.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen
          obtain ⟨hrow, hcert⟩ := ih hlen'
          constructor
          · change a :: underlyingRow (bundleCertificate row cert) = a :: row
            rw [hrow]
          · simp [bundleCertificate, hcert]

/-- A certified unbundled row step can always be realized by putting its
certificate on the destination row. -/
theorem bundledStep_of_rowStep
    (S : CertifiedRowSystem I A C Q F)
    {old new : List A} {oldBundled : List (BundledCell A C)}
    (hold : underlyingRow oldBundled = old)
    (hstep : S.RowStep old new) :
    ∃ newBundled,
      underlyingRow newBundled = new ∧ BundledStep S oldBundled newBundled := by
  obtain ⟨cert, q, heval, hdone⟩ := hstep
  have hlens := S.evalStep_nil_iff heval
  have hbundle := bundleCertificate_eq_of_length_eq
    (A := A) (C := C) (row := new) (cert := cert)
      (hlens.1.symm.trans hlens.2)
  refine ⟨bundleCertificate new cert, hbundle.1, ?_⟩
  apply (bundledStep_iff S oldBundled (bundleCertificate new cert)).mpr
  refine ⟨cert, q, hbundle.2, ?_, hdone⟩
  rw [hold, hbundle.1]
  exact heval

/-- Every ordinary reachable row has a bundled reachable representative. -/
theorem bundledReach_of_rowReach
    (S : CertifiedRowSystem I A C Q F) {first last : List A}
    (hreach : ReflTransGen S.RowStep first last) :
    ∃ lastBundled,
      underlyingRow lastBundled = last ∧
        ReflTransGen (BundledStep S)
          (bundleFirstRow (C := C) first) lastBundled := by
  induction hreach with
  | refl =>
      exact ⟨bundleFirstRow first, underlyingRow_bundleFirstRow first,
        ReflTransGen.refl⟩
  | tail hreach hstep ih =>
      obtain ⟨oldBundled, hold, hbundledReach⟩ := ih
      obtain ⟨newBundled, hnew, hbundledStep⟩ :=
        bundledStep_of_rowStep S hold hstep
      exact ⟨newBundled, hnew, hbundledReach.tail hbundledStep⟩

/-- Erasing incoming certificates maps every bundled path to an ordinary row
path. -/
theorem rowReach_of_bundledReach
    (S : CertifiedRowSystem I A C Q F)
    {first last : List (BundledCell A C)}
    (hreach : ReflTransGen (BundledStep S) first last) :
    ReflTransGen S.RowStep (underlyingRow first) (underlyingRow last) := by
  apply hreach.lift underlyingRow
  intro old new hstep
  obtain ⟨cert, q, -, heval, hdone⟩ :=
    (bundledStep_iff S old new).mp hstep
  exact ⟨cert, q, heval, hdone⟩

/-- Nonemptiness of the alternating bundled-history language is exactly
reachability from a nonempty row accepted by the supplied initial verifier to
a final row of the certified system. -/
theorem bundledValidLanguageWith_nonempty_iff
    (S : CertifiedRowSystem I A C Q F)
    (Initial : List A → Prop) :
    (bundledValidLanguageWith S Initial).Nonempty ↔
      ∃ first : List A, first ≠ [] ∧ Initial first ∧
        ∃ last : List A,
          ReflTransGen S.RowStep first last ∧ S.Final last := by
  constructor
  · rintro ⟨word, hword⟩
    obtain ⟨history, hrep, hinitial, hfinal, hchain⟩ := hword
    have hbundledReach : ReflTransGen (BundledStep S)
        history.first history.last := by
      apply List.relationReflTransGen_of_exists_isChain_cons history.2
      · simpa [Rows.toList, Rows.first] using hchain
      · exact (Rows.last_eq_getLast_toList history).symm
    have hreach := rowReach_of_bundledReach S hbundledReach
    refine ⟨underlyingRow history.first, ?_, hinitial.2,
      underlyingRow history.last, hreach, ?_⟩
    · intro hempty
      have hfirstBundled : history.first ≠ [] :=
        (rectangular_iff_first_ne_and_length_chain history).mp hrep.1 |>.1
      apply hfirstBundled
      apply List.eq_nil_of_length_eq_zero
      have hlen := congrArg List.length hempty
      simpa [underlyingRow] using hlen
    · exact (systemFinalVerifier_accepts_iff S _).mp hfinal
  · rintro ⟨first, hfirst, hinitial, last, hreach, hfinal⟩
    obtain ⟨lastBundled, hlast, hbundledReach⟩ :=
      bundledReach_of_rowReach S hreach
    obtain ⟨tail, hchain, hgetLast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen hbundledReach
    let history : Rows (BundledCell A C) :=
      (bundleFirstRow first, tail)
    refine ⟨encode history.toList, history, ?_, ?_, ?_, ?_⟩
    · constructor
      · rw [rectangular_iff_first_ne_and_length_chain]
        constructor
        · simpa [history, Rows.first, bundleFirstRow] using hfirst
        · exact hchain.imp fun _ _ h => bundledStep_length S h
      · rfl
    · refine ⟨bundleFirstRow_isFirst first, ?_⟩
      change Initial (underlyingRow (bundleFirstRow (C := C) first))
      simpa using hinitial
    · apply (systemFinalVerifier_accepts_iff S _).mpr
      rw [Rows.last_eq_getLast_toList]
      dsimp [history, Rows.toList]
      rw [hgetLast, hlast]
      exact hfinal
    · simpa [history, Rows.toList] using hchain

/-- Row-verifier form of `bundledValidLanguageWith_nonempty_iff`. -/
theorem bundledValidLanguage_nonempty_iff
    (S : CertifiedRowSystem I A C Q F)
    (InitialVerifier : RowVerifier A VState) :
    (bundledValidLanguage S InitialVerifier
        (systemFinalVerifier S)).Nonempty ↔
      ∃ first : List A, first ≠ [] ∧ InitialVerifier.Accepts first ∧
        ∃ last : List A,
          ReflTransGen S.RowStep first last ∧ S.Final last := by
  simpa [bundledValidLanguageWith, bundledValidLanguage, BundledInitial,
    BundledFinal] using
    (bundledValidLanguageWith_nonempty_iff S InitialVerifier.Accepts)

end ContextFree.MalformedHistories
