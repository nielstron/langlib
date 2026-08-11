module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories
public import Langlib.Automata.LinearBounded.CertifiedRowSystem
public import Mathlib.Data.Fintype.Option

@[expose]
public section

/-!
# Finite verifiers for alternating histories

Certificates are stored on the destination row of a transition.  Consequently
an adjacent-row checker sees the old cell, the new cell, and its certificate in
one aligned stack comparison; it never has to complement an existential choice
of certificates.
-/

namespace ContextFree.MalformedHistories

variable {I A C Q F : Type}

/-- A row cell together with the certificate for the transition entering this
row.  The first row uses `none` in every cell. -/
abbrev BundledCell (A C : Type) := A × Option C

@[simp] theorem card_bundledCell [Fintype A] [Fintype C] :
    Fintype.card (BundledCell A C) =
      Fintype.card A * (Fintype.card C + 1) := by
  simp [BundledCell, Fintype.card_prod, Fintype.card_option]

@[simp] theorem card_bundledHistorySymbol [Fintype A] [Fintype C] :
    Fintype.card (Symbol (BundledCell A C)) =
      Fintype.card A * (Fintype.card C + 1) + 1 := by
  rw [card_symbol, card_bundledCell]

/-- Strip the incoming-certificate annotation from a bundled row. -/
def underlyingRow (row : List (BundledCell A C)) : List A :=
  row.map Prod.fst

/-- Read a complete certificate row.  A single missing annotation rejects. -/
def incomingCertificate : List (BundledCell A C) → Option (List C)
  | [] => some []
  | (_, none) :: _ => none
  | (_, some c) :: row => (incomingCertificate row).map (c :: ·)

@[simp] theorem incomingCertificate_nil :
    incomingCertificate ([] : List (BundledCell A C)) = some [] := rfl

@[simp] theorem incomingCertificate_cons_none (a : A)
    (row : List (BundledCell A C)) :
    incomingCertificate ((a, none) :: row) = none := rfl

@[simp] theorem incomingCertificate_cons_some (a : A) (c : C)
    (row : List (BundledCell A C)) :
    incomingCertificate ((a, some c) :: row) =
      (incomingCertificate row).map (c :: ·) := rfl

theorem incomingCertificate_eq_some_iff
    (row : List (BundledCell A C)) (cert : List C) :
    incomingCertificate row = some cert ↔
      row.map Prod.snd = cert.map some := by
  induction row generalizing cert with
  | nil => cases cert <;> simp [incomingCertificate]
  | cons x row ih =>
      rcases x with ⟨a, none | c⟩
      · cases cert <;> simp [incomingCertificate]
      · cases cert with
        | nil => simp [incomingCertificate]
        | cons d cert => simp [incomingCertificate, ih, and_comm]

/-- The distinguished first-row annotation condition. -/
def IsFirstBundledRow (row : List (BundledCell A C)) : Prop :=
  row.map Prod.snd = List.replicate row.length none

theorem isFirstBundledRow_iff_forall (row : List (BundledCell A C)) :
    IsFirstBundledRow row ↔ ∀ x ∈ row, x.2 = none := by
  rw [IsFirstBundledRow, List.eq_replicate_iff]
  simp only [List.length_map, true_and]
  constructor
  · intro h x hx
    exact h x.2 (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h o ho
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
    exact h x hx

/-- Boolean row predicate presented by a finite left-to-right state machine. -/
structure RowVerifier (A F : Type) where
  start : F
  step : F → A → F
  done : F → Bool

namespace RowVerifier

def eval (V : RowVerifier A F) (row : List A) : F :=
  row.foldl V.step V.start

def Accepts (V : RowVerifier A F) (row : List A) : Prop :=
  V.done (V.eval row) = true

end RowVerifier

/-- Boolean version of the `CertifiedRowSystem` transition relation, with the
certificate read from the destination row. -/
def bundledStepBool (S : CertifiedRowSystem I A C Q F)
    (old new : List (BundledCell A C)) : Bool :=
  match incomingCertificate new with
  | none => false
  | some cert =>
      match S.evalStep S.stepStart (underlyingRow old) (underlyingRow new) cert with
      | none => false
      | some q => S.stepDone q

def BundledStep (S : CertifiedRowSystem I A C Q F)
    (old new : List (BundledCell A C)) : Prop :=
  bundledStepBool S old new = true

theorem bundledStep_iff (S : CertifiedRowSystem I A C Q F)
    (old new : List (BundledCell A C)) :
    BundledStep S old new ↔
      ∃ cert q, incomingCertificate new = some cert ∧
        S.evalStep S.stepStart (underlyingRow old) (underlyingRow new) cert = some q ∧
        S.stepDone q = true := by
  cases hcert : incomingCertificate new with
  | none => simp [BundledStep, bundledStepBool, hcert]
  | some cert =>
      cases hq : S.evalStep S.stepStart
          (underlyingRow old) (underlyingRow new) cert with
      | none => simp [BundledStep, bundledStepBool, hcert, hq]
      | some q => simp [BundledStep, bundledStepBool, hcert, hq]

theorem bundledStep_length (S : CertifiedRowSystem I A C Q F)
    {old new : List (BundledCell A C)} (h : BundledStep S old new) :
    old.length = new.length := by
  obtain ⟨cert, q, hcert, heval, -⟩ := (bundledStep_iff S old new).mp h
  have hlens := S.evalStep_nil_iff heval
  simpa [underlyingRow] using hlens.1

/-- Lift a finite-state predicate on unannotated rows to the first bundled row. -/
def BundledInitial (V : RowVerifier A F)
    (row : List (BundledCell A C)) : Prop :=
  IsFirstBundledRow row ∧ V.Accepts (underlyingRow row)

/-- Lift a finite-state predicate on unannotated rows to the final bundled row.
Incoming certificate annotations are irrelevant here. -/
def BundledFinal (V : RowVerifier A F)
    (row : List (BundledCell A C)) : Prop :=
  V.Accepts (underlyingRow row)

end ContextFree.MalformedHistories
