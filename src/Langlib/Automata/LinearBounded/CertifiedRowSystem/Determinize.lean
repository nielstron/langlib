module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem
import Mathlib.Tactic

@[expose]
public section

/-!
# Determinizing certified row relations

A `CertifiedRowSystem` presents its row relation by a finite-state verifier that may guess one
certificate symbol per cell.  This file applies the ordinary subset construction to that verifier.
The resulting system has `Unit` certificates: after reading an aligned pair of rows, its verifier
state is exactly the finite set of source-verifier states obtainable from all certificate prefixes.

This is useful when both an edge and the absence of an edge must be checked in linear space.  In
particular, the inductive-counting proof of context-sensitive complement closure uses the
determinized verifier in its negative branch.
-/

open Classical

namespace CertifiedRowSystem

variable {I A C Q F : Type*}

/-- One subset-construction transition for a certified row verifier. -/
public noncomputable def detStepCell [Fintype C]
    (S : CertifiedRowSystem I A C Q F) (states : Finset Q) (old new : A) : Finset Q :=
  states.biUnion fun q => Finset.univ.image fun cert => S.stepCell q old new cert

@[simp] theorem mem_detStepCell [Fintype C] [DecidableEq Q]
    (S : CertifiedRowSystem I A C Q F) (states : Finset Q) (old new : A) (q' : Q) :
    q' ∈ S.detStepCell states old new ↔
      ∃ q ∈ states, ∃ cert : C, S.stepCell q old new cert = q' := by
  classical
  simp [detStepCell]

/-- Run the determinized verifier on two aligned rows. -/
public noncomputable def evalDetStep [Fintype C]
    (S : CertifiedRowSystem I A C Q F) : Finset Q → List A → List A → Option (Finset Q)
  | states, [], [] => some states
  | states, old :: olds, new :: news =>
      S.evalDetStep (S.detStepCell states old new) olds news
  | _, _, _ => none

/-- The determinized state set contains `q'` exactly when some certificate row takes some initial
verifier state in `states` to `q'`. -/
theorem mem_evalDetStep_iff [Fintype C] [DecidableEq Q]
    (S : CertifiedRowSystem I A C Q F) (states : Finset Q)
    (old new : List A) (out : Finset Q) (q' : Q) :
    S.evalDetStep states old new = some out →
      (q' ∈ out ↔ ∃ q ∈ states, ∃ cert : List C, S.evalStep q old new cert = some q') := by
  classical
  induction old generalizing states new out q' with
  | nil =>
      cases new with
      | nil =>
          intro h
          simp only [evalDetStep, Option.some.injEq] at h
          subst out
          constructor
          · intro hq
            exact ⟨q', hq, [], by simp [evalStep]⟩
          · rintro ⟨q, hq, cert, heval⟩
            cases cert with
            | nil =>
                simp only [evalStep, Option.some.injEq] at heval
                subst q'
                exact hq
            | cons c cs => simp [evalStep] at heval
      | cons new news => simp [evalDetStep]
  | cons old olds ih =>
      cases new with
      | nil => simp [evalDetStep]
      | cons new news =>
          intro h
          rw [ih (S.detStepCell states old new) news out q' h]
          constructor
          · rintro ⟨q₁, hq₁, certs, heval⟩
            rw [mem_detStepCell] at hq₁
            obtain ⟨q₀, hq₀, cert, hstep⟩ := hq₁
            refine ⟨q₀, hq₀, cert :: certs, ?_⟩
            simp only [evalStep]
            rwa [hstep]
          · rintro ⟨q₀, hq₀, certs, heval⟩
            cases certs with
            | nil => simp [evalStep] at heval
            | cons cert certs =>
                simp only [evalStep] at heval
                refine ⟨S.stepCell q₀ old new cert, ?_, certs, heval⟩
                rw [mem_detStepCell]
                exact ⟨q₀, hq₀, cert, rfl⟩

/-- The subset construction turns a certified system into an equivalent system whose certificate
alphabet is `Unit`. -/
public noncomputable def determinize [Fintype C] [DecidableEq Q]
    (S : CertifiedRowSystem I A C Q F) :
    CertifiedRowSystem I A Unit (Finset Q) F where
  inputCell := S.inputCell
  stepStart := {S.stepStart}
  stepCell states old new _ := S.detStepCell states old new
  stepDone states := decide (∃ q ∈ states, S.stepDone q = true)
  finalStart := S.finalStart
  finalCell := S.finalCell
  finalDone := S.finalDone

theorem evalStep_determinize [Fintype C] [DecidableEq Q]
    (S : CertifiedRowSystem I A C Q F) (states : Finset Q)
    (old new : List A) (cert : List Unit) :
    cert.length = old.length →
    old.length = new.length →
    (S.determinize.evalStep states old new cert = S.evalDetStep states old new) := by
  classical
  induction old generalizing states new cert with
  | nil =>
      intro hcert hnew
      have hcertNil : cert = [] := List.length_eq_zero_iff.mp (by simpa using hcert)
      have hnewNil : new = [] := List.length_eq_zero_iff.mp (by simpa using hnew.symm)
      subst cert
      subst new
      rfl
  | cons old olds ih =>
      cases new with
      | nil => simp
      | cons new news =>
          cases cert with
          | nil => simp
          | cons _ certs =>
              intro hcert hnew
              simp only [evalStep, determinize, evalDetStep]
              apply ih
              · simpa using hcert
              · simpa using hnew

theorem evalDetStep_eq_some_of_length [Fintype C] [DecidableEq Q]
    (S : CertifiedRowSystem I A C Q F) (states : Finset Q)
    (old new : List A) (hlen : old.length = new.length) :
    ∃ out, S.evalDetStep states old new = some out := by
  classical
  induction old generalizing states new with
  | nil =>
      have hnew : new = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst new
      exact ⟨states, rfl⟩
  | cons old olds ih =>
      cases new with
      | nil => simp at hlen
      | cons new news =>
          obtain ⟨out, hout⟩ := ih (S.detStepCell states old new) news (by simpa using hlen)
          exact ⟨out, hout⟩

/-- Determinization preserves the certified row relation exactly. -/
public theorem rowStep_determinize_iff [Fintype C] [DecidableEq Q]
    (S : CertifiedRowSystem I A C Q F) (old new : List A) :
    S.determinize.RowStep old new ↔ S.RowStep old new := by
  classical
  constructor
  · rintro ⟨cert, states, heval, hdone⟩
    have hlens := S.determinize.evalStep_nil_iff heval
    have hdet : S.evalDetStep {S.stepStart} old new = some states := by
      rw [← S.evalStep_determinize {S.stepStart} old new cert hlens.2.symm hlens.1]
      exact heval
    have hdone' : ∃ q ∈ states, S.stepDone q = true := by
      exact of_decide_eq_true (by simpa only [determinize] using hdone)
    obtain ⟨q, hq, hqdone⟩ := hdone'
    rw [S.mem_evalDetStep_iff {S.stepStart} old new states q hdet] at hq
    obtain ⟨q₀, hq₀, cert₀, heval₀⟩ := hq
    simp only [Finset.mem_singleton] at hq₀
    subst q₀
    exact ⟨cert₀, q, heval₀, hqdone⟩
  · rintro ⟨cert, q, heval, hdone⟩
    have hlens := S.evalStep_nil_iff heval
    let unitCert : List Unit := List.replicate old.length ()
    have hunitLen : unitCert.length = old.length := by simp [unitCert]
    obtain ⟨states, hstates⟩ :=
      S.evalDetStep_eq_some_of_length {S.stepStart} old new hlens.1
    refine ⟨unitCert, states, ?_, ?_⟩
    · simpa only [determinize] using
        (show S.determinize.evalStep {S.stepStart} old new unitCert = some states by
          rw [S.evalStep_determinize {S.stepStart} old new unitCert hunitLen hlens.1]
          exact hstates)
    · change decide (∃ q' ∈ states, S.stepDone q' = true) = true
      apply decide_eq_true
      refine ⟨q, ?_, hdone⟩
      rw [S.mem_evalDetStep_iff {S.stepStart} old new states q hstates]
      exact ⟨S.stepStart, by simp, cert, heval⟩

/-- Determinization preserves the reachability language. -/
public theorem rowReachLanguage_determinize [Fintype C] [DecidableEq Q]
    (S : CertifiedRowSystem I A C Q F) :
    S.determinize.rowReachLanguage = S.rowReachLanguage := by
  funext w
  apply propext
  constructor
  · rintro ⟨hne, row, hreach, hfinal⟩
    refine ⟨hne, row, ?_, hfinal⟩
    simpa only [determinize] using hreach.mono fun old new hstep =>
      (S.rowStep_determinize_iff old new).1 hstep
  · rintro ⟨hne, row, hreach, hfinal⟩
    refine ⟨hne, row, ?_, hfinal⟩
    simpa only [determinize] using hreach.mono fun old new hstep =>
      (S.rowStep_determinize_iff old new).2 hstep

end CertifiedRowSystem
