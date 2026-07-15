module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem
import Mathlib.Tactic

@[expose]
public section

/-!
# Linear-bounded automata as certified row systems

This file presents the computation graph of a marker-free nondeterministic LBA as a
`CertifiedRowSystem`.  A configuration is represented by one row of cells.  The control state is
repeated in every cell and a Boolean marks the unique head position; this makes one LBA step
checkable by a finite left-to-right scan.
-/

open List Relation Classical

namespace LBA

variable {I Γ Λ : Type*}

/-- A raw input cell, or one cell of an encoded LBA configuration.  Configuration rows repeat the
control state in every cell and mark the unique head position with `head = true`. -/
public inductive RowCell (I Γ Λ : Type*) where
  | raw (input : I)
  | cfg (symbol : Γ) (head : Bool) (state : Λ)
  deriving DecidableEq

public instance [Fintype I] [Fintype Γ] [Fintype Λ] : Fintype (RowCell I Γ Λ) :=
  Fintype.ofEquiv (I ⊕ (Γ × Bool × Λ))
    { toFun := fun
        | .inl i => .raw i
        | .inr (a, h, q) => .cfg a h q
      invFun := fun
        | .raw i => .inl i
        | .cfg a h q => .inr (a, h, q)
      left_inv := by rintro (_ | ⟨_, _, _⟩) <;> rfl
      right_inv := by intro x; cases x <;> rfl }

/-- A certificate only has to identify the direction used at the source head. -/
public inductive RowCert where
  | plain
  | head (dir : DLBA.Dir)
  deriving DecidableEq, Fintype

/-- State of the left-to-right verifier for one row transition. -/
public inductive RowScan (Λ : Type*) where
  | start
  | initRest
  | before (oldState newState : Λ)
  | expectLeft (oldState newState : Λ)
  | expectRight (oldState newState : Λ)
  | after (oldState newState : Λ)
  | rightClamp (oldState newState : Λ)
  | bad
  deriving DecidableEq

public instance [Fintype Λ] : Fintype (RowScan Λ) := by
  let e : (Unit ⊕ Unit ⊕ (Λ × Λ) ⊕ (Λ × Λ) ⊕ (Λ × Λ) ⊕
      (Λ × Λ) ⊕ (Λ × Λ) ⊕ Unit) ≃ RowScan Λ :=
    { toFun := fun
        | .inl _ => .start
        | .inr (.inl _) => .initRest
        | .inr (.inr (.inl p)) => .before p.1 p.2
        | .inr (.inr (.inr (.inl p))) => .expectLeft p.1 p.2
        | .inr (.inr (.inr (.inr (.inl p)))) => .expectRight p.1 p.2
        | .inr (.inr (.inr (.inr (.inr (.inl p))))) => .after p.1 p.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl p)))))) => .rightClamp p.1 p.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))) => .bad
      invFun := fun
        | .start => .inl ()
        | .initRest => .inr (.inl ())
        | .before q q' => .inr (.inr (.inl (q, q')))
        | .expectLeft q q' => .inr (.inr (.inr (.inl (q, q'))))
        | .expectRight q q' => .inr (.inr (.inr (.inr (.inl (q, q')))))
        | .after q q' => .inr (.inr (.inr (.inr (.inr (.inl (q, q'))))))
        | .rightClamp q q' => .inr (.inr (.inr (.inr (.inr (.inr (.inl (q, q')))))))
        | .bad => .inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))
      left_inv := by rintro (_ | _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _) <;> rfl
      right_inv := by intro x; cases x <;> rfl }
  exact Fintype.ofEquiv _ e

/-- State of the regular accepting-row checker. -/
public inductive RowFinal (Λ : Type*) where
  | start
  | noHead (state : Λ)
  | oneHead (state : Λ)
  | bad
  deriving DecidableEq

public instance [Fintype Λ] : Fintype (RowFinal Λ) :=
  Fintype.ofEquiv (Unit ⊕ Λ ⊕ Λ ⊕ Unit)
    { toFun := fun
        | .inl _ => .start
        | .inr (.inl q) => .noHead q
        | .inr (.inr (.inl q)) => .oneHead q
        | .inr (.inr (.inr _)) => .bad
      invFun := fun
        | .start => .inl ()
        | .noHead q => .inr (.inl q)
        | .oneHead q => .inr (.inr (.inl q))
        | .bad => .inr (.inr (.inr ()))
      left_inv := by rintro (_ | _ | _ | _) <;> rfl
      right_inv := by intro x; cases x <;> rfl }

public noncomputable def RowScan.transitionOK
    (M : LBA.Machine Γ Λ) (q : Λ) (a : Γ) (q' : Λ) (b : Γ) (d : DLBA.Dir) : Bool :=
  decide ((q', b, d) ∈ M.transition q a)

/-- Scan the first pair of configuration cells. -/
public noncomputable def RowScan.scanFirst (M : LBA.Machine Γ Λ)
    (a : Γ) (h : Bool) (q : Λ) (b : Γ) (h' : Bool) (q' : Λ) (cert : RowCert) :
    RowScan Λ :=
  match h, h', cert with
  | false, false, .plain => if a = b then .before q q' else .bad
  | false, true, .plain => if a = b then .expectLeft q q' else .bad
  | true, false, .head .right =>
      if transitionOK M q a q' b .right then .expectRight q q' else .bad
  | true, true, .head .stay =>
      if transitionOK M q a q' b .stay then .after q q' else .bad
  | true, true, .head .left =>
      if transitionOK M q a q' b .left then .after q q' else .bad
  | true, true, .head .right =>
      if transitionOK M q a q' b .right then .rightClamp q q' else .bad
  | _, _, _ => .bad

/-- Scan a pair strictly before the source head. -/
public noncomputable def RowScan.scanBefore (M : LBA.Machine Γ Λ) (q q' : Λ)
    (a : Γ) (h : Bool) (r : Λ) (b : Γ) (h' : Bool) (r' : Λ) (cert : RowCert) :
    RowScan Λ :=
  if r ≠ q ∨ r' ≠ q' then .bad else
    match h, h', cert with
    | false, false, .plain => if a = b then .before q q' else .bad
    | false, true, .plain => if a = b then .expectLeft q q' else .bad
    | true, false, .head .right =>
        if transitionOK M q a q' b .right then .expectRight q q' else .bad
    | true, true, .head .stay =>
        if transitionOK M q a q' b .stay then .after q q' else .bad
    | true, true, .head .right =>
        if transitionOK M q a q' b .right then .rightClamp q q' else .bad
    | _, _, _ => .bad

/-- The cellwise verifier.  Interior left and right moves use one pending scanner state so the
destination head is checked on the adjacent cell. -/
public noncomputable def RowScan.scanCell [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) :
    RowScan Λ → RowCell I Γ Λ → RowCell I Γ Λ → RowCert → RowScan Λ
  | .start, .raw i, .cfg b true q', .plain =>
      if b = embed i ∧ q' = M.initial then .initRest else .bad
  | .start, .cfg a h q, .cfg b h' q', cert => scanFirst M a h q b h' q' cert
  | .initRest, .raw i, .cfg b false q', .plain =>
      if b = embed i ∧ q' = M.initial then .initRest else .bad
  | .before q q', .cfg a h r, .cfg b h' r', cert =>
      scanBefore M q q' a h r b h' r' cert
  | .expectLeft q q', .cfg a true r, .cfg b false r', .head .left =>
      if r = q ∧ r' = q' ∧ transitionOK M q a q' b .left then .after q q' else .bad
  | .expectRight q q', .cfg a false r, .cfg b true r', .plain =>
      if r = q ∧ r' = q' ∧ a = b then .after q q' else .bad
  | .after q q', .cfg a false r, .cfg b false r', .plain =>
      if r = q ∧ r' = q' ∧ a = b then .after q q' else .bad
  | _, _, _, _ => .bad

public def RowScan.done : RowScan Λ → Bool
  | .initRest | .after _ _ | .rightClamp _ _ => true
  | _ => false

public def RowFinal.next [DecidableEq Λ] : RowFinal Λ → RowCell I Γ Λ → RowFinal Λ
  | .start, .cfg _ false q => .noHead q
  | .start, .cfg _ true q => .oneHead q
  | .noHead q, .cfg _ false r => if r = q then .noHead q else .bad
  | .noHead q, .cfg _ true r => if r = q then .oneHead q else .bad
  | .oneHead q, .cfg _ false r => if r = q then .oneHead q else .bad
  | _, _ => .bad

public def RowFinal.done (M : LBA.Machine Γ Λ) : RowFinal Λ → Bool
  | .oneHead q => M.accept q
  | _ => false

/-- The certified row system whose reachable rows are precisely the configurations reachable by
`M` from the canonically embedded, nonempty input. -/
public noncomputable def certifiedRowSystem [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) :
    CertifiedRowSystem I (RowCell I Γ Λ) RowCert (RowScan Λ) (RowFinal Λ) where
  inputCell := .raw
  stepStart := .start
  stepCell := RowScan.scanCell M embed
  stepDone := RowScan.done
  finalStart := .start
  finalCell := RowFinal.next
  finalDone := RowFinal.done M

@[simp] theorem certifiedRowSystem_stepCell [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) :
    (certifiedRowSystem M embed).stepCell = RowScan.scanCell M embed := rfl

@[simp] theorem certifiedRowSystem_stepDone [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) :
    (certifiedRowSystem M embed).stepDone = RowScan.done := rfl

@[simp] theorem certifiedRowSystem_finalCell [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) :
    (certifiedRowSystem M embed).finalCell = RowFinal.next := rfl

@[simp] theorem certifiedRowSystem_finalDone [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) :
    (certifiedRowSystem M embed).finalDone = RowFinal.done M := rfl

/-! ## Semantic row relations -/

/-- A block of non-head configuration cells carrying the same control state. -/
public def noHeadCells (q : Λ) (xs : List Γ) : List (RowCell I Γ Λ) :=
  xs.map fun a => .cfg a false q

@[simp] private lemma noHeadCells_same_eq_iff (q : Λ) (xs ys : List Γ) :
    noHeadCells (I := I) q xs = noHeadCells q ys ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [noHeadCells]
  | cons x xs ih =>
      cases ys with
      | nil => simp [noHeadCells]
      | cons y ys =>
          constructor
          · intro h
            rcases List.cons.inj h with ⟨hxy, htail⟩
            have hxy' : x = y := by simpa using hxy
            exact congrArg₂ List.cons hxy' ((ih ys).1 htail)
          · intro h
            rcases List.cons.inj h with ⟨hxy, htail⟩
            subst y
            exact congrArg (List.cons (.cfg x false q)) ((ih ys).2 htail)

/-- The intended semantic transition between rows. -/
public inductive RowMove (M : LBA.Machine Γ Λ) (embed : I → Γ) :
    List (RowCell I Γ Λ) → List (RowCell I Γ Λ) → Prop
  | init (i : I) (is : List I) :
      RowMove M embed
        ((i :: is).map .raw)
        (.cfg (embed i) true M.initial :: noHeadCells M.initial (is.map embed))
  | stay (q q' : Λ) (a b : Γ) (left right : List Γ)
      (hstep : (q', b, .stay) ∈ M.transition q a) :
      RowMove M embed
        (noHeadCells q left ++ .cfg a true q :: noHeadCells q right)
        (noHeadCells q' left ++ .cfg b true q' :: noHeadCells q' right)
  | leftClamp (q q' : Λ) (a b : Γ) (right : List Γ)
      (hstep : (q', b, .left) ∈ M.transition q a) :
      RowMove M embed
        (.cfg a true q :: noHeadCells q right)
        (.cfg b true q' :: noHeadCells q' right)
  | rightClamp (q q' : Λ) (a b : Γ) (left : List Γ)
      (hstep : (q', b, .right) ∈ M.transition q a) :
      RowMove M embed
        (noHeadCells q left ++ [.cfg a true q])
        (noHeadCells q' left ++ [.cfg b true q'])
  | left (q q' : Λ) (x a b : Γ) (left right : List Γ)
      (hstep : (q', b, .left) ∈ M.transition q a) :
      RowMove M embed
        (noHeadCells q left ++ .cfg x false q :: .cfg a true q :: noHeadCells q right)
        (noHeadCells q' left ++ .cfg x true q' :: .cfg b false q' :: noHeadCells q' right)
  | right (q q' : Λ) (a b x : Γ) (left right : List Γ)
      (hstep : (q', b, .right) ∈ M.transition q a) :
      RowMove M embed
        (noHeadCells q left ++ .cfg a true q :: .cfg x false q :: noHeadCells q right)
        (noHeadCells q' left ++ .cfg b false q' :: .cfg x true q' :: noHeadCells q' right)

private def scanAccepts [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (s : RowScan Λ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) : Prop :=
  ∃ out, (certifiedRowSystem M embed).evalStep s old new cert = some out ∧ RowScan.done out = true

private lemma scanAccepts_cons [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (s : RowScan Λ)
    (a b : RowCell I Γ Λ) (c : RowCert)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed s (a :: old) (b :: new) (c :: cert) ↔
      scanAccepts M embed (RowScan.scanCell M embed s a b c) old new cert := by
  rfl

@[simp] private lemma not_scanAccepts_length_mismatch_left
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (s : RowScan Λ)
    (a : RowCell I Γ Λ) (old : List (RowCell I Γ Λ)) (cert : List RowCert) :
    ¬ scanAccepts M embed s (a :: old) [] cert := by
  simp [scanAccepts, CertifiedRowSystem.evalStep]

@[simp] private lemma not_scanAccepts_length_mismatch_right
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (s : RowScan Λ)
    (b : RowCell I Γ Λ) (new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    ¬ scanAccepts M embed s [] (b :: new) cert := by
  cases cert <;> simp [scanAccepts, CertifiedRowSystem.evalStep]

@[simp] private lemma not_scanAccepts_cert_mismatch
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (s : RowScan Λ)
    (a : RowCell I Γ Λ) (old : List (RowCell I Γ Λ))
    (b : RowCell I Γ Λ) (new : List (RowCell I Γ Λ)) :
    ¬ scanAccepts M embed s (a :: old) (b :: new) [] := by
  simp [scanAccepts, CertifiedRowSystem.evalStep]

@[simp] private lemma evalStep_bad [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    (certifiedRowSystem M embed).evalStep .bad old new cert =
      if old.length = new.length ∧ old.length = cert.length then some .bad else none := by
  induction old generalizing new cert with
  | nil => cases new <;> cases cert <;> simp [CertifiedRowSystem.evalStep]
  | cons a old ih =>
      cases new <;> cases cert <;>
        simp [CertifiedRowSystem.evalStep, RowScan.scanCell, ih]

private lemma evalStep_bad_not_done [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) {out : RowScan Λ}
    (h : (certifiedRowSystem M embed).evalStep .bad old new cert = some out) :
    RowScan.done out = false := by
  rw [evalStep_bad] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst out
    rfl
  · simp at h

@[simp] private lemma not_scanAccepts_bad [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    ¬ scanAccepts M embed .bad old new cert := by
  rintro ⟨out, hout, hdone⟩
  rw [evalStep_bad_not_done M embed old new cert hout] at hdone
  contradiction

private lemma scanAccepts_rightClamp_iff [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed (.rightClamp q q') old new cert ↔ old = [] ∧ new = [] ∧ cert = [] := by
  constructor
  · rintro ⟨out, hout, hdone⟩
    cases old with
    | nil =>
        cases new <;> cases cert <;> simp [CertifiedRowSystem.evalStep] at hout
        exact ⟨rfl, rfl, rfl⟩
    | cons a old =>
        cases new with
        | nil => simp [CertifiedRowSystem.evalStep] at hout
        | cons b new =>
            cases cert with
            | nil => simp [CertifiedRowSystem.evalStep] at hout
            | cons c cert =>
                have hbad :
                    (certifiedRowSystem M embed).evalStep .bad old new cert = some out := by
                  simpa [CertifiedRowSystem.evalStep, RowScan.scanCell] using hout
                rw [evalStep_bad_not_done M embed old new cert hbad] at hdone
                contradiction
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨.rightClamp q q', rfl, rfl⟩

@[simp] private lemma raw_cons_ne_noHeadCells (i : I) (tail : List (RowCell I Γ Λ))
    (q : Λ) (xs : List Γ) :
    RowCell.raw i :: tail ≠ noHeadCells q xs := by
  cases xs <;> simp [noHeadCells]

@[simp] private lemma cfg_cons_eq_noHeadCells_iff
    (a : Γ) (h : Bool) (r : Λ) (tail : List (RowCell I Γ Λ))
    (q : Λ) (xs : List Γ) :
    RowCell.cfg a h r :: tail = noHeadCells q xs ↔
      ∃ ys : List Γ,
        xs = a :: ys ∧ h = false ∧ r = q ∧ tail = noHeadCells q ys := by
  cases xs with
  | nil => simp [noHeadCells]
  | cons x xs =>
      constructor
      · intro heq
        have hp := List.cons.inj heq
        have hc : a = x ∧ h = false ∧ r = q := by simpa using hp.1
        rcases hc with ⟨rfl, hh, hr⟩
        exact ⟨xs, rfl, hh, hr, hp.2⟩
      · rintro ⟨ys, hxs, hh, hr, ht⟩
        rcases List.cons.inj hxs with ⟨rfl, rfl⟩
        rw [hh, hr, ht]
        rfl

@[simp] private lemma cert_cons_eq_replicate_iff
    (c : RowCert) (tail : List RowCert) (xs : List Γ) :
    c :: tail = List.replicate xs.length .plain ↔
      ∃ a ys, xs = a :: ys ∧ c = .plain ∧
        tail = List.replicate ys.length .plain := by
  cases xs <;> simp [List.replicate_succ]

@[simp] private lemma scanAccepts_after_iff [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed (.after q q') old new cert ↔
      ∃ xs : List Γ, old = noHeadCells q xs ∧ new = noHeadCells q' xs ∧
        cert = List.replicate xs.length .plain := by
  induction old generalizing new cert with
  | nil =>
      cases new <;> cases cert <;>
        simp [scanAccepts, CertifiedRowSystem.evalStep, RowScan.done, noHeadCells]
  | cons oldHead oldTail ih =>
      cases oldHead with
      | raw i =>
          cases new <;> cases cert <;>
            simp [scanAccepts_cons, RowScan.scanCell, noHeadCells] <;> aesop
      | cfg a h r =>
          cases h <;> cases new with
          | nil => cases cert <;> simp [scanAccepts, CertifiedRowSystem.evalStep, noHeadCells]
          | cons newHead newTail =>
              cases newHead with
              | raw i =>
                  cases cert <;>
                    simp [scanAccepts_cons, RowScan.scanCell, noHeadCells] <;> aesop
              | cfg b h' r' =>
                  cases h' <;> cases cert with
                  | nil => simp [scanAccepts, CertifiedRowSystem.evalStep, noHeadCells]
                  | cons c certTail =>
                      cases c <;>
                        simp [scanAccepts_cons, RowScan.scanCell, noHeadCells, ih, and_assoc] <;>
                          aesop

private lemma scanAccepts_expectRight_iff
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed (.expectRight q q') old new cert ↔
      ∃ x xs,
        old = .cfg x false q :: noHeadCells q xs ∧
        new = .cfg x true q' :: noHeadCells q' xs ∧
        cert = .plain :: List.replicate xs.length .plain := by
  cases old with
  | nil => cases new <;> cases cert <;>
      simp [scanAccepts, CertifiedRowSystem.evalStep, RowScan.done]
  | cons oldHead oldTail =>
      cases oldHead <;> cases new with
      | nil => cases cert <;> simp [scanAccepts, CertifiedRowSystem.evalStep]
      | cons newHead newTail =>
          cases newHead <;> cases cert with
          | nil => simp [scanAccepts, CertifiedRowSystem.evalStep]
          | cons c certTail =>
              cases c <;> simp [scanAccepts_cons, RowScan.scanCell, noHeadCells] <;> aesop

private lemma scanAccepts_expectLeft_iff
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed (.expectLeft q q') old new cert ↔
      ∃ a b xs,
        (q', b, .left) ∈ M.transition q a ∧
        old = .cfg a true q :: noHeadCells q xs ∧
        new = .cfg b false q' :: noHeadCells q' xs ∧
        cert = .head .left :: List.replicate xs.length .plain := by
  cases old with
  | nil => cases new <;> cases cert <;>
      simp [scanAccepts, CertifiedRowSystem.evalStep, RowScan.done]
  | cons oldHead oldTail =>
      cases oldHead <;> cases new with
      | nil => cases cert <;> simp [scanAccepts, CertifiedRowSystem.evalStep]
      | cons newHead newTail =>
          cases newHead <;> cases cert with
          | nil => simp [scanAccepts, CertifiedRowSystem.evalStep]
          | cons c certTail =>
              cases c <;> simp [scanAccepts_cons, RowScan.scanCell,
                RowScan.transitionOK, noHeadCells] <;> aesop

private def rawCells (xs : List I) : List (RowCell I Γ Λ) :=
  xs.map .raw

@[simp] private lemma cfg_cons_ne_rawCells
    (a : Γ) (h : Bool) (q : Λ) (tail : List (RowCell I Γ Λ)) (xs : List I) :
    RowCell.cfg a h q :: tail ≠ rawCells xs := by
  cases xs <;> simp [rawCells]

@[simp] private lemma raw_cons_eq_rawCells_iff
    (i : I) (tail : List (RowCell I Γ Λ)) (xs : List I) :
    RowCell.raw i :: tail = rawCells xs ↔
      ∃ is, xs = i :: is ∧ tail = rawCells is := by
  cases xs with
  | nil => simp [rawCells]
  | cons j js =>
      constructor
      · intro heq
        rcases List.cons.inj heq with ⟨hhead, htail⟩
        have hij : i = j := by simpa using hhead
        subst j
        exact ⟨js, rfl, htail⟩
      · rintro ⟨is, hxs, htail⟩
        rcases List.cons.inj hxs with ⟨rfl, rfl⟩
        rw [htail]
        rfl

private lemma scanAccepts_initRest_cons_iff
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (i : I) (b : Γ) (q : Λ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed .initRest
        (.raw i :: old) (.cfg b false q :: new) (.plain :: cert) ↔
      b = embed i ∧ q = M.initial ∧ scanAccepts M embed .initRest old new cert := by
  rw [scanAccepts_cons]
  simp only [RowScan.scanCell]
  by_cases h : b = embed i ∧ q = M.initial
  · simp [h]
  · rw [if_neg h]
    constructor
    · exact fun hacc => (not_scanAccepts_bad M embed _ _ _ hacc).elim
    · rintro ⟨hb, hq, _⟩
      exact (h ⟨hb, hq⟩).elim

@[simp] private lemma scanAccepts_initRest_iff
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed .initRest old new cert ↔
      ∃ xs : List I,
        old = rawCells xs ∧
        new = noHeadCells M.initial (xs.map embed) ∧
        cert = List.replicate xs.length .plain := by
  induction old generalizing new cert with
  | nil =>
      cases new <;> cases cert <;>
        simp [scanAccepts, CertifiedRowSystem.evalStep, RowScan.done, rawCells, noHeadCells]
  | cons oldHead oldTail ih =>
      cases oldHead with
      | cfg a marked q =>
          cases new <;> cases cert <;>
            simp [scanAccepts_cons, RowScan.scanCell, rawCells, noHeadCells,
              not_scanAccepts_bad]
      | raw i =>
          cases new with
          | nil => cases cert <;>
              simp [scanAccepts, CertifiedRowSystem.evalStep, rawCells, noHeadCells]
          | cons newHead newTail =>
              cases newHead with
              | raw j =>
                  cases cert <;>
                    simp [scanAccepts_cons, RowScan.scanCell, rawCells, noHeadCells,
                      not_scanAccepts_bad]
              | cfg b marked q =>
                  cases marked with
                  | true =>
                      cases cert <;>
                        simp [scanAccepts_cons, RowScan.scanCell, rawCells, noHeadCells,
                          not_scanAccepts_bad]
                  | false =>
                      cases cert with
                      | nil => simp [scanAccepts, CertifiedRowSystem.evalStep,
                          rawCells, noHeadCells]
                      | cons c certTail =>
                          cases c with
                          | head d =>
                              simp [scanAccepts_cons, RowScan.scanCell, rawCells,
                                noHeadCells, not_scanAccepts_bad]
                          | plain =>
                              rw [scanAccepts_initRest_cons_iff, ih]
                              constructor
                              · rintro ⟨hb, hq, xs, hold, hnew, hcert⟩
                                refine ⟨i :: xs, ?_, ?_, ?_⟩
                                · simp [rawCells, hold]
                                · rw [hb, hq, hnew]
                                  rfl
                                · simpa [List.replicate_succ] using
                                    congrArg (List.cons .plain) hcert
                              · rintro ⟨ys, hold, hnew, hcert⟩
                                obtain ⟨xs, rfl, holdTail⟩ :=
                                  (raw_cons_eq_rawCells_iff i oldTail ys).1 hold
                                have hnew0 : (b = embed i ∧ q = M.initial) ∧
                                    newTail = noHeadCells M.initial (xs.map embed) := by
                                  simpa [noHeadCells] using hnew
                                have hnew' : b = embed i ∧ q = M.initial ∧
                                    newTail = noHeadCells M.initial (xs.map embed) :=
                                  ⟨hnew0.1.1, hnew0.1.2, hnew0.2⟩
                                have hcert' : certTail =
                                    List.replicate xs.length .plain := by
                                  simpa [List.replicate_succ] using hcert
                                exact ⟨hnew'.1, hnew'.2.1, xs, holdTail,
                                  hnew'.2.2, hcert'⟩

/-- A genuine configuration move whose source head is not clamped at the left boundary. -/
private inductive ConfigMove (M : LBA.Machine Γ Λ) (q q' : Λ) :
    List (RowCell I Γ Λ) → List (RowCell I Γ Λ) → Prop
  | stay (a b : Γ) (left right : List Γ)
      (hstep : (q', b, .stay) ∈ M.transition q a) :
      ConfigMove M q q'
        (noHeadCells q left ++ .cfg a true q :: noHeadCells q right)
        (noHeadCells q' left ++ .cfg b true q' :: noHeadCells q' right)
  | rightClamp (a b : Γ) (left : List Γ)
      (hstep : (q', b, .right) ∈ M.transition q a) :
      ConfigMove M q q'
        (noHeadCells q left ++ [.cfg a true q])
        (noHeadCells q' left ++ [.cfg b true q'])
  | left (x a b : Γ) (left right : List Γ)
      (hstep : (q', b, .left) ∈ M.transition q a) :
      ConfigMove M q q'
        (noHeadCells q left ++ .cfg x false q :: .cfg a true q :: noHeadCells q right)
        (noHeadCells q' left ++ .cfg x true q' :: .cfg b false q' :: noHeadCells q' right)
  | right (a b x : Γ) (left right : List Γ)
      (hstep : (q', b, .right) ∈ M.transition q a) :
      ConfigMove M q q'
        (noHeadCells q left ++ .cfg a true q :: .cfg x false q :: noHeadCells q right)
        (noHeadCells q' left ++ .cfg b false q' :: .cfg x true q' :: noHeadCells q' right)

private lemma ConfigMove.prepend (M : LBA.Machine Γ Λ) (q q' : Λ) (x : Γ)
    {old new : List (RowCell I Γ Λ)} (h : ConfigMove M q q' old new) :
    ConfigMove M q q' (.cfg x false q :: old) (.cfg x false q' :: new) := by
  cases h with
  | stay a b left right hstep =>
      simpa [noHeadCells] using ConfigMove.stay (I := I) a b (x :: left) right hstep
  | rightClamp a b left hstep =>
      simpa [noHeadCells] using ConfigMove.rightClamp (I := I) a b (x :: left) hstep
  | left y a b left right hstep =>
      simpa [noHeadCells] using ConfigMove.left (I := I) y a b (x :: left) right hstep
  | right a b y left right hstep =>
      simpa [noHeadCells] using ConfigMove.right (I := I) a b y (x :: left) right hstep

private lemma ConfigMove.toRowMove (M : LBA.Machine Γ Λ) (embed : I → Γ)
    (q q' : Λ) {old new : List (RowCell I Γ Λ)}
    (h : ConfigMove M q q' old new) : RowMove M embed old new := by
  cases h with
  | stay a b left right hstep => exact RowMove.stay q q' a b left right hstep
  | rightClamp a b left hstep => exact RowMove.rightClamp q q' a b left hstep
  | left x a b left right hstep => exact RowMove.left q q' x a b left right hstep
  | right a b x left right hstep => exact RowMove.right q q' a b x left right hstep

private lemma scanAccepts_before_prepend
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ) (x : Γ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed (.before q q')
        (.cfg x false q :: old) (.cfg x false q' :: new) (.plain :: cert) ↔
      scanAccepts M embed (.before q q') old new cert := by
  simp [scanAccepts_cons, RowScan.scanCell, RowScan.scanBefore]

private lemma scanAccepts_before_prefix
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ) (left : List Γ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert) :
    scanAccepts M embed (.before q q')
        (noHeadCells q left ++ old) (noHeadCells q' left ++ new)
        (List.replicate left.length .plain ++ cert) ↔
      scanAccepts M embed (.before q q') old new cert := by
  induction left with
  | nil => rfl
  | cons x left ih =>
      simpa [noHeadCells, List.replicate_succ, scanAccepts_before_prepend] using ih

private lemma scanAccepts_before_of_configMove
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ)
    {old new : List (RowCell I Γ Λ)} (h : ConfigMove M q q' old new) :
    ∃ cert, scanAccepts M embed (.before q q') old new cert := by
  cases h with
  | stay a b left right hstep =>
      refine ⟨List.replicate left.length .plain ++
        .head .stay :: List.replicate right.length .plain, ?_⟩
      rw [scanAccepts_before_prefix]
      simp [scanAccepts_cons, RowScan.scanCell, RowScan.scanBefore,
        RowScan.transitionOK, hstep]
  | rightClamp a b left hstep =>
      refine ⟨List.replicate left.length .plain ++ [.head .right], ?_⟩
      rw [scanAccepts_before_prefix]
      simp [scanAccepts_cons, RowScan.scanCell, RowScan.scanBefore,
        RowScan.transitionOK, hstep, scanAccepts_rightClamp_iff]
  | left x a b left right hstep =>
      refine ⟨List.replicate left.length .plain ++
        .plain :: .head .left :: List.replicate right.length .plain, ?_⟩
      rw [scanAccepts_before_prefix]
      simp [scanAccepts_cons, RowScan.scanCell, RowScan.scanBefore,
        RowScan.transitionOK, hstep, noHeadCells] <;>
        exact ⟨right, rfl, rfl, rfl⟩
  | right a b x left right hstep =>
      refine ⟨List.replicate left.length .plain ++
        .head .right :: .plain :: List.replicate right.length .plain, ?_⟩
      rw [scanAccepts_before_prefix]
      simp [scanAccepts_cons, RowScan.scanCell, RowScan.scanBefore,
        RowScan.transitionOK, hstep, noHeadCells] <;>
        exact ⟨right, rfl, rfl, rfl⟩

private lemma configMove_of_scanAccepts_before
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert)
    (hacc : scanAccepts M embed (.before q q') old new cert) :
    ConfigMove M q q' old new := by
  induction old generalizing new cert with
  | nil =>
      cases new <;> cases cert <;>
        simp [scanAccepts, CertifiedRowSystem.evalStep, RowScan.done] at hacc
  | cons oldHead oldTail ih =>
      cases new with
      | nil => simp at hacc
      | cons newHead newTail =>
          cases cert with
          | nil => simp at hacc
          | cons c certTail =>
              cases oldHead with
              | raw i => simp [scanAccepts_cons, RowScan.scanCell] at hacc
              | cfg a oldMarked r =>
                  cases newHead with
                  | raw i => simp [scanAccepts_cons, RowScan.scanCell] at hacc
                  | cfg b newMarked r' =>
                      have hstates : r = q ∧ r' = q' := by
                        by_contra hn
                        have hbad : r ≠ q ∨ r' ≠ q' := by tauto
                        have hbadAcc : scanAccepts M embed .bad oldTail newTail certTail := by
                          simpa [scanAccepts_cons, RowScan.scanCell, RowScan.scanBefore,
                            hbad] using hacc
                        exact (not_scanAccepts_bad M embed _ _ _ hbadAcc).elim
                      rcases hstates with ⟨hr, hr'⟩
                      subst r
                      subst r'
                      cases oldMarked with
                      | false =>
                          cases newMarked with
                          | false =>
                              cases c with
                              | plain =>
                                  by_cases hab : a = b
                                  · subst b
                                    have htail : scanAccepts M embed (.before q q')
                                        oldTail newTail certTail := by
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanBefore] using hacc
                                    exact (ih newTail certTail htail).prepend M q q' a
                                  · exfalso
                                    simpa [scanAccepts_cons, RowScan.scanCell,
                                      RowScan.scanBefore, hab, not_scanAccepts_bad] using hacc
                              | head d =>
                                  exfalso
                                  cases d <;> simpa [scanAccepts_cons, RowScan.scanCell,
                                    RowScan.scanBefore, not_scanAccepts_bad] using hacc
                          | true =>
                              cases c with
                              | plain =>
                                  by_cases hab : a = b
                                  · subst b
                                    have htail : scanAccepts M embed (.expectLeft q q')
                                        oldTail newTail certTail := by
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanBefore] using hacc
                                    obtain ⟨a', b', xs, htrans, rfl, rfl, rfl⟩ :=
                                      (scanAccepts_expectLeft_iff M embed q q' _ _ _).1 htail
                                    simpa [noHeadCells] using
                                      (ConfigMove.left (I := I) a a' b' [] xs htrans)
                                  · exfalso
                                    simpa [scanAccepts_cons, RowScan.scanCell,
                                      RowScan.scanBefore, hab, not_scanAccepts_bad] using hacc
                              | head d =>
                                  exfalso
                                  cases d <;> simpa [scanAccepts_cons, RowScan.scanCell,
                                    RowScan.scanBefore, not_scanAccepts_bad] using hacc
                      | true =>
                          cases newMarked with
                          | false =>
                              cases c with
                              | plain =>
                                  exfalso
                                  simpa [scanAccepts_cons, RowScan.scanCell,
                                    RowScan.scanBefore, not_scanAccepts_bad] using hacc
                              | head d =>
                                  cases d with
                                  | left =>
                                      exfalso
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanBefore, not_scanAccepts_bad] using hacc
                                  | stay =>
                                      exfalso
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanBefore, not_scanAccepts_bad] using hacc
                                  | right =>
                                      by_cases htrans :
                                          (q', b, .right) ∈ M.transition q a
                                      · have htail : scanAccepts M embed (.expectRight q q')
                                            oldTail newTail certTail := by
                                          simpa [scanAccepts_cons, RowScan.scanCell,
                                            RowScan.scanBefore, RowScan.transitionOK,
                                            htrans] using hacc
                                        obtain ⟨x, xs, rfl, rfl, rfl⟩ :=
                                          (scanAccepts_expectRight_iff M embed q q' _ _ _).1 htail
                                        simpa [noHeadCells] using
                                          (ConfigMove.right (I := I) a b x [] xs htrans)
                                      · exfalso
                                        simpa [scanAccepts_cons, RowScan.scanCell,
                                          RowScan.scanBefore, RowScan.transitionOK, htrans,
                                          not_scanAccepts_bad] using hacc
                          | true =>
                              cases c with
                              | plain =>
                                  exfalso
                                  simpa [scanAccepts_cons, RowScan.scanCell,
                                    RowScan.scanBefore, not_scanAccepts_bad] using hacc
                              | head d =>
                                  cases d with
                                  | left =>
                                      exfalso
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanBefore, not_scanAccepts_bad] using hacc
                                  | right =>
                                      by_cases htrans :
                                          (q', b, .right) ∈ M.transition q a
                                      · have htail : scanAccepts M embed (.rightClamp q q')
                                            oldTail newTail certTail := by
                                          simpa [scanAccepts_cons, RowScan.scanCell,
                                            RowScan.scanBefore, RowScan.transitionOK,
                                            htrans] using hacc
                                        obtain ⟨rfl, rfl, rfl⟩ :=
                                          (scanAccepts_rightClamp_iff M embed q q' _ _ _).1 htail
                                        simpa [noHeadCells] using
                                          (ConfigMove.rightClamp (I := I) a b [] htrans)
                                      · exfalso
                                        simpa [scanAccepts_cons, RowScan.scanCell,
                                          RowScan.scanBefore, RowScan.transitionOK, htrans,
                                          not_scanAccepts_bad] using hacc
                                  | stay =>
                                      by_cases htrans :
                                          (q', b, .stay) ∈ M.transition q a
                                      · have htail : scanAccepts M embed (.after q q')
                                            oldTail newTail certTail := by
                                          simpa [scanAccepts_cons, RowScan.scanCell,
                                            RowScan.scanBefore, RowScan.transitionOK,
                                            htrans] using hacc
                                        obtain ⟨xs, rfl, rfl, rfl⟩ :=
                                          (scanAccepts_after_iff M embed q q' _ _ _).1 htail
                                        simpa [noHeadCells] using
                                          (ConfigMove.stay (I := I) a b [] xs htrans)
                                      · exfalso
                                        simpa [scanAccepts_cons, RowScan.scanCell,
                                          RowScan.scanBefore, RowScan.transitionOK, htrans,
                                          not_scanAccepts_bad] using hacc

private lemma rowMove_of_scanAccepts_start
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ)
    (old new : List (RowCell I Γ Λ)) (cert : List RowCert)
    (hacc : scanAccepts M embed .start old new cert) :
    RowMove M embed old new := by
  cases old with
  | nil =>
      cases new <;> cases cert <;>
        simp [scanAccepts, CertifiedRowSystem.evalStep, RowScan.done] at hacc
  | cons oldHead oldTail =>
      cases new with
      | nil => simp at hacc
      | cons newHead newTail =>
          cases cert with
          | nil => simp at hacc
          | cons c certTail =>
              cases oldHead with
              | raw i =>
                  cases newHead with
                  | raw j =>
                      cases c <;>
                        simp [scanAccepts_cons, RowScan.scanCell, not_scanAccepts_bad] at hacc
                  | cfg b marked q =>
                      cases marked with
                      | false =>
                          cases c <;>
                            simp [scanAccepts_cons, RowScan.scanCell,
                              not_scanAccepts_bad] at hacc
                      | true =>
                          cases c with
                          | head d =>
                              simp [scanAccepts_cons, RowScan.scanCell,
                                not_scanAccepts_bad] at hacc
                          | plain =>
                              by_cases hinit : b = embed i ∧ q = M.initial
                              · rcases hinit with ⟨rfl, rfl⟩
                                have htail : scanAccepts M embed .initRest
                                    oldTail newTail certTail := by
                                  simpa [scanAccepts_cons, RowScan.scanCell] using hacc
                                obtain ⟨w, rfl, rfl, rfl⟩ :=
                                  (scanAccepts_initRest_iff M embed _ _ _).1 htail
                                simpa [rawCells] using
                                  (RowMove.init (M := M) (embed := embed) i w)
                              · exfalso
                                simpa [scanAccepts_cons, RowScan.scanCell, hinit,
                                  not_scanAccepts_bad] using hacc
              | cfg a oldMarked r =>
                  cases newHead with
                  | raw i => simp [scanAccepts_cons, RowScan.scanCell] at hacc
                  | cfg b newMarked r' =>
                      cases oldMarked with
                      | false =>
                          cases newMarked with
                          | false =>
                              cases c with
                              | plain =>
                                  by_cases hab : a = b
                                  · subst b
                                    have htail : scanAccepts M embed (.before r r')
                                        oldTail newTail certTail := by
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanFirst] using hacc
                                    exact ConfigMove.toRowMove M embed r r'
                                      ((configMove_of_scanAccepts_before M embed r r'
                                        oldTail newTail certTail htail).prepend M r r' a)
                                  · exfalso
                                    simpa [scanAccepts_cons, RowScan.scanCell,
                                      RowScan.scanFirst, hab, not_scanAccepts_bad] using hacc
                              | head d =>
                                  exfalso
                                  cases d <;> simpa [scanAccepts_cons, RowScan.scanCell,
                                    RowScan.scanFirst, not_scanAccepts_bad] using hacc
                          | true =>
                              cases c with
                              | plain =>
                                  by_cases hab : a = b
                                  · subst b
                                    have htail : scanAccepts M embed (.expectLeft r r')
                                        oldTail newTail certTail := by
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanFirst] using hacc
                                    obtain ⟨a', b', xs, htrans, rfl, rfl, rfl⟩ :=
                                      (scanAccepts_expectLeft_iff M embed r r' _ _ _).1 htail
                                    simpa [noHeadCells] using
                                      (RowMove.left (M := M) (embed := embed) r r' a a' b'
                                        [] xs htrans)
                                  · exfalso
                                    simpa [scanAccepts_cons, RowScan.scanCell,
                                      RowScan.scanFirst, hab, not_scanAccepts_bad] using hacc
                              | head d =>
                                  exfalso
                                  cases d <;> simpa [scanAccepts_cons, RowScan.scanCell,
                                    RowScan.scanFirst, not_scanAccepts_bad] using hacc
                      | true =>
                          cases newMarked with
                          | false =>
                              cases c with
                              | plain =>
                                  exfalso
                                  simpa [scanAccepts_cons, RowScan.scanCell,
                                    RowScan.scanFirst, not_scanAccepts_bad] using hacc
                              | head d =>
                                  cases d with
                                  | left =>
                                      exfalso
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanFirst, not_scanAccepts_bad] using hacc
                                  | stay =>
                                      exfalso
                                      simpa [scanAccepts_cons, RowScan.scanCell,
                                        RowScan.scanFirst, not_scanAccepts_bad] using hacc
                                  | right =>
                                      by_cases htrans :
                                          (r', b, .right) ∈ M.transition r a
                                      · have htail : scanAccepts M embed (.expectRight r r')
                                            oldTail newTail certTail := by
                                          simpa [scanAccepts_cons, RowScan.scanCell,
                                            RowScan.scanFirst, RowScan.transitionOK,
                                            htrans] using hacc
                                        obtain ⟨x, xs, rfl, rfl, rfl⟩ :=
                                          (scanAccepts_expectRight_iff M embed r r' _ _ _).1 htail
                                        simpa [noHeadCells] using
                                          (RowMove.right (M := M) (embed := embed) r r' a b x
                                            [] xs htrans)
                                      · exfalso
                                        simpa [scanAccepts_cons, RowScan.scanCell,
                                          RowScan.scanFirst, RowScan.transitionOK, htrans,
                                          not_scanAccepts_bad] using hacc
                          | true =>
                              cases c with
                              | plain =>
                                  exfalso
                                  simpa [scanAccepts_cons, RowScan.scanCell,
                                    RowScan.scanFirst, not_scanAccepts_bad] using hacc
                              | head d =>
                                  cases d with
                                  | left =>
                                      by_cases htrans :
                                          (r', b, .left) ∈ M.transition r a
                                      · have htail : scanAccepts M embed (.after r r')
                                            oldTail newTail certTail := by
                                          simpa [scanAccepts_cons, RowScan.scanCell,
                                            RowScan.scanFirst, RowScan.transitionOK,
                                            htrans] using hacc
                                        obtain ⟨xs, rfl, rfl, rfl⟩ :=
                                          (scanAccepts_after_iff M embed r r' _ _ _).1 htail
                                        simpa [noHeadCells] using
                                          (RowMove.leftClamp (M := M) (embed := embed)
                                            r r' a b xs htrans)
                                      · exfalso
                                        simpa [scanAccepts_cons, RowScan.scanCell,
                                          RowScan.scanFirst, RowScan.transitionOK, htrans,
                                          not_scanAccepts_bad] using hacc
                                  | right =>
                                      by_cases htrans :
                                          (r', b, .right) ∈ M.transition r a
                                      · have htail : scanAccepts M embed (.rightClamp r r')
                                            oldTail newTail certTail := by
                                          simpa [scanAccepts_cons, RowScan.scanCell,
                                            RowScan.scanFirst, RowScan.transitionOK,
                                            htrans] using hacc
                                        obtain ⟨rfl, rfl, rfl⟩ :=
                                          (scanAccepts_rightClamp_iff M embed r r' _ _ _).1 htail
                                        simpa [noHeadCells] using
                                          (RowMove.rightClamp (M := M) (embed := embed)
                                            r r' a b [] htrans)
                                      · exfalso
                                        simpa [scanAccepts_cons, RowScan.scanCell,
                                          RowScan.scanFirst, RowScan.transitionOK, htrans,
                                          not_scanAccepts_bad] using hacc
                                  | stay =>
                                      by_cases htrans :
                                          (r', b, .stay) ∈ M.transition r a
                                      · have htail : scanAccepts M embed (.after r r')
                                            oldTail newTail certTail := by
                                          simpa [scanAccepts_cons, RowScan.scanCell,
                                            RowScan.scanFirst, RowScan.transitionOK,
                                            htrans] using hacc
                                        obtain ⟨xs, rfl, rfl, rfl⟩ :=
                                          (scanAccepts_after_iff M embed r r' _ _ _).1 htail
                                        simpa [noHeadCells] using
                                          (RowMove.stay (M := M) (embed := embed)
                                            r r' a b [] xs htrans)
                                      · exfalso
                                        simpa [scanAccepts_cons, RowScan.scanCell,
                                          RowScan.scanFirst, RowScan.transitionOK, htrans,
                                          not_scanAccepts_bad] using hacc

private lemma scanAccepts_start_of_prefixed_configMove
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (q q' : Λ) (x : Γ)
    {old new : List (RowCell I Γ Λ)} (h : ConfigMove M q q' old new) :
    ∃ cert, scanAccepts M embed .start
      (.cfg x false q :: old) (.cfg x false q' :: new) cert := by
  obtain ⟨cert, hcert⟩ := scanAccepts_before_of_configMove M embed q q' h
  refine ⟨.plain :: cert, ?_⟩
  simpa [scanAccepts_cons, RowScan.scanCell, RowScan.scanFirst] using hcert

private lemma scanAccepts_start_of_rowMove
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ)
    {old new : List (RowCell I Γ Λ)} (h : RowMove M embed old new) :
    ∃ cert, scanAccepts M embed .start old new cert := by
  cases h with
  | init i is =>
      refine ⟨.plain :: List.replicate is.length .plain, ?_⟩
      simp only [List.map_cons]
      rw [scanAccepts_cons]
      rw [show RowScan.scanCell M embed .start (.raw i)
          (.cfg (embed i) true M.initial) .plain = .initRest by
        simp [RowScan.scanCell]]
      exact (scanAccepts_initRest_iff M embed _ _ _).2
        ⟨is, rfl, rfl, rfl⟩
  | stay q q' a b left right hstep =>
      cases left with
      | nil =>
          refine ⟨.head .stay :: List.replicate right.length .plain, ?_⟩
          simp only [noHeadCells, List.map_nil, List.nil_append]
          rw [scanAccepts_cons]
          rw [show RowScan.scanCell M embed .start (.cfg a true q)
              (.cfg b true q') (.head .stay) = .after q q' by
            simp [RowScan.scanCell, RowScan.scanFirst, RowScan.transitionOK, hstep]]
          exact (scanAccepts_after_iff M embed q q' _ _ _).2
            ⟨right, rfl, rfl, rfl⟩
      | cons x left =>
          simpa [noHeadCells] using scanAccepts_start_of_prefixed_configMove M embed q q' x
            (ConfigMove.stay (I := I) a b left right hstep)
  | leftClamp q q' a b right hstep =>
      refine ⟨.head .left :: List.replicate right.length .plain, ?_⟩
      simp only [noHeadCells, List.map_nil, List.nil_append]
      rw [scanAccepts_cons]
      rw [show RowScan.scanCell M embed .start (.cfg a true q)
          (.cfg b true q') (.head .left) = .after q q' by
        simp [RowScan.scanCell, RowScan.scanFirst, RowScan.transitionOK, hstep]]
      exact (scanAccepts_after_iff M embed q q' _ _ _).2
        ⟨right, rfl, rfl, rfl⟩
  | rightClamp q q' a b left hstep =>
      cases left with
      | nil =>
          refine ⟨[.head .right], ?_⟩
          simp only [noHeadCells, List.map_nil, List.nil_append]
          rw [scanAccepts_cons]
          rw [show RowScan.scanCell M embed .start (.cfg a true q)
              (.cfg b true q') (.head .right) = .rightClamp q q' by
            simp [RowScan.scanCell, RowScan.scanFirst, RowScan.transitionOK, hstep]]
          exact (scanAccepts_rightClamp_iff M embed q q' _ _ _).2
            ⟨rfl, rfl, rfl⟩
      | cons x left =>
          simpa [noHeadCells] using scanAccepts_start_of_prefixed_configMove M embed q q' x
            (ConfigMove.rightClamp (I := I) a b left hstep)
  | left q q' x a b left right hstep =>
      cases left with
      | nil =>
          refine ⟨.plain :: .head .left :: List.replicate right.length .plain, ?_⟩
          simp only [noHeadCells, List.map_nil, List.nil_append]
          rw [scanAccepts_cons]
          rw [show RowScan.scanCell M embed .start (.cfg x false q)
              (.cfg x true q') .plain = .expectLeft q q' by
            simp [RowScan.scanCell, RowScan.scanFirst]]
          rw [scanAccepts_cons]
          rw [show RowScan.scanCell M embed (.expectLeft q q') (.cfg a true q)
              (.cfg b false q') (.head .left) = .after q q' by
            simp [RowScan.scanCell, RowScan.transitionOK, hstep]]
          exact (scanAccepts_after_iff M embed q q' _ _ _).2
            ⟨right, rfl, rfl, rfl⟩
      | cons y left =>
          simpa [noHeadCells] using scanAccepts_start_of_prefixed_configMove M embed q q' y
            (ConfigMove.left (I := I) x a b left right hstep)
  | right q q' a b x left right hstep =>
      cases left with
      | nil =>
          refine ⟨.head .right :: .plain :: List.replicate right.length .plain, ?_⟩
          simp only [noHeadCells, List.map_nil, List.nil_append]
          rw [scanAccepts_cons]
          rw [show RowScan.scanCell M embed .start (.cfg a true q)
              (.cfg b false q') (.head .right) = .expectRight q q' by
            simp [RowScan.scanCell, RowScan.scanFirst, RowScan.transitionOK, hstep]]
          rw [scanAccepts_cons]
          rw [show RowScan.scanCell M embed (.expectRight q q') (.cfg x false q)
              (.cfg x true q') .plain = .after q q' by
            simp [RowScan.scanCell]]
          exact (scanAccepts_after_iff M embed q q' _ _ _).2
            ⟨right, rfl, rfl, rfl⟩
      | cons y left =>
          simpa [noHeadCells] using scanAccepts_start_of_prefixed_configMove M embed q q' y
            (ConfigMove.right (I := I) a b x left right hstep)

/-- The local scanner accepts exactly the intended raw initialization or one LBA row move. -/
public theorem certifiedRowSystem_rowStep_iff
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ)
    (old new : List (RowCell I Γ Λ)) :
    (certifiedRowSystem M embed).RowStep old new ↔ RowMove M embed old new := by
  constructor
  · rintro ⟨cert, out, heval, hdone⟩
    exact rowMove_of_scanAccepts_start M embed old new cert ⟨out, heval, hdone⟩
  · intro hmove
    obtain ⟨cert, out, heval, hdone⟩ := scanAccepts_start_of_rowMove M embed hmove
    exact ⟨cert, out, heval, hdone⟩

/-! ## Bisimulation with bounded-tape configurations -/

/-- A well-formed configuration row, split immediately before and after its unique head. -/
public def configCells (q : Λ) (left : List Γ) (a : Γ) (right : List Γ) :
    List (RowCell I Γ Λ) :=
  noHeadCells q left ++ .cfg a true q :: noHeadCells q right

/-- The tape contents of a bounded configuration as an ordinary list. -/
public def tapeList {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) : List Γ :=
  List.ofFn cfg.tape.contents

/-- Symbols strictly to the left of the head. -/
public def leftSymbols {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) : List Γ :=
  (tapeList cfg).take cfg.tape.head.val

/-- Symbols strictly to the right of the head. -/
public def rightSymbols {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) : List Γ :=
  (tapeList cfg).drop (cfg.tape.head.val + 1)

/-- Canonical row encoding of a bounded-tape configuration. -/
public def configRow {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) : List (RowCell I Γ Λ) :=
  configCells cfg.state (leftSymbols cfg) cfg.tape.read (rightSymbols cfg)

@[simp] theorem configRow_length {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    (configRow (I := I) cfg).length = n + 1 := by
  have hsplit : (leftSymbols cfg).length + 1 + (rightSymbols cfg).length = n + 1 := by
    simp [leftSymbols, rightSymbols, tapeList]
    omega
  simp [configRow, configCells, noHeadCells]
  omega

private lemma configCells_eq_iff (q q' : Λ) (left left' : List Γ) (a a' : Γ)
    (right right' : List Γ) :
    configCells (I := I) q left a right = configCells q' left' a' right' ↔
      q = q' ∧ left = left' ∧ a = a' ∧ right = right' := by
  induction left generalizing q q' left' a a' right right' with
  | nil =>
      cases left' with
      | nil =>
          constructor
          · intro h
            rcases List.cons.inj h with ⟨hhead, htail⟩
            have hhead' : a = a' ∧ q = q' := by simpa using hhead
            rcases hhead' with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl, rfl, (noHeadCells_same_eq_iff q right right').1 htail⟩
          · rintro ⟨hq, _, ha, hright⟩
            subst q'
            subst a'
            subst right'
            rfl
      | cons y ys => simp [configCells, noHeadCells]
  | cons x left ih =>
      cases left' with
      | nil => simp [configCells, noHeadCells]
      | cons y ys =>
          constructor
          · intro h
            rcases List.cons.inj h with ⟨hhead, htail⟩
            have hhead' : x = y ∧ q = q' := by simpa using hhead
            rcases hhead' with ⟨rfl, rfl⟩
            rcases (ih q q ys a a' right right').1 htail with
              ⟨_, hleft, ha, hright⟩
            exact ⟨rfl, congrArg (List.cons x) hleft, ha, hright⟩
          · rintro ⟨hq, hleft, ha, hright⟩
            subst q'
            rcases List.cons.inj hleft with ⟨hxy, htail⟩
            subst y
            subst ys
            subst a'
            subst right'
            rfl

private lemma tapeList_split {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    tapeList cfg = leftSymbols cfg ++ cfg.tape.read :: rightSymbols cfg := by
  rw [← List.take_append_drop cfg.tape.head.val (tapeList cfg)]
  congr 1
  rw [← List.cons_getElem_drop_succ (n := cfg.tape.head.val)
    (h := by simp [tapeList]; omega)]
  congr 1
  unfold tapeList
  rw [List.getElem_ofFn]
  rfl

@[simp] private lemma leftSymbols_length {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    (leftSymbols cfg).length = cfg.tape.head.val := by
  simp [leftSymbols, tapeList]

@[simp] private lemma rightSymbols_length {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    (rightSymbols cfg).length = n - cfg.tape.head.val := by
  simp [rightSymbols, tapeList]

private lemma ofFn_update {X : Type*} {n : ℕ} (f : Fin (n + 1) → X)
    (i : Fin (n + 1)) (x : X) :
    List.ofFn (Function.update f i x) = (List.ofFn f).set i.val x := by
  apply List.ext_getElem
  · simp
  · intro j hj _
    have hj' : j < n + 1 := by simpa using hj
    rw [List.getElem_ofFn, List.getElem_set]
    by_cases hi : i.val = j
    · rw [if_pos hi, show (⟨j, hj'⟩ : Fin (n + 1)) = i from Fin.ext hi.symm,
        Function.update_self]
    · rw [if_neg hi, List.getElem_ofFn,
        Function.update_of_ne (fun he => hi (congrArg Fin.val he).symm)]

private lemma tapeList_write_move {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (q' : Λ) (b : Γ) (d : DLBA.Dir) :
    tapeList (⟨q', (cfg.tape.write b).moveHead d⟩ : DLBA.Cfg Γ Λ n) =
      (tapeList cfg).set cfg.tape.head.val b := by
  simp only [tapeList, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
  exact ofFn_update cfg.tape.contents cfg.tape.head b

private lemma tapeList_set_head {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) (b : Γ) :
    (tapeList cfg).set cfg.tape.head.val b =
      leftSymbols cfg ++ b :: rightSymbols cfg := by
  exact List.set_eq_take_cons_drop b (by simp [tapeList]; omega)

private lemma tapeList_get_head {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    (tapeList cfg)[cfg.tape.head.val]'(by simp [tapeList]; omega) =
      cfg.tape.read := by
  unfold tapeList
  rw [List.getElem_ofFn]
  rfl

private lemma configRow_eq_of_split {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (left : List Γ) (a : Γ) (right : List Γ)
    (htape : tapeList cfg = left ++ a :: right)
    (hhead : cfg.tape.head.val = left.length) :
    configRow (I := I) cfg = configCells cfg.state left a right := by
  apply (configCells_eq_iff cfg.state cfg.state (leftSymbols cfg) left
    cfg.tape.read a (rightSymbols cfg) right).2
  have hleft : leftSymbols cfg = left := by
    simp [leftSymbols, hhead, htape]
  have hright : rightSymbols cfg = right := by
    simp [rightSymbols, hhead, htape]
  have ha : cfg.tape.read = a := by
    have hget' : (tapeList cfg)[left.length]'(by rw [htape]; simp) =
        cfg.tape.read := by
      simpa only [hhead] using tapeList_get_head cfg
    simpa [htape] using hget'.symm
  exact ⟨rfl, hleft, ha, hright⟩

/-- Every bounded-tape LBA step is represented by one semantic row move. -/
public theorem rowMove_configRow_of_step
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ Λ n} (hstep : LBA.Step M cfg cfg') :
    RowMove M embed (configRow cfg) (configRow cfg') := by
  obtain ⟨q', b, d, htrans, rfl⟩ := hstep
  let next : DLBA.Cfg Γ Λ n := ⟨q', (cfg.tape.write b).moveHead d⟩
  have htape : tapeList next = leftSymbols cfg ++ b :: rightSymbols cfg := by
    rw [show tapeList next = (tapeList cfg).set cfg.tape.head.val b by
      simpa [next] using tapeList_write_move cfg q' b d]
    exact tapeList_set_head cfg b
  cases d with
  | stay =>
      have hhead : next.tape.head.val = (leftSymbols cfg).length := by
        simp [next, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      have hnew := configRow_eq_of_split (I := I) next (leftSymbols cfg) b
        (rightSymbols cfg) htape hhead
      change RowMove M embed
        (configCells cfg.state (leftSymbols cfg) cfg.tape.read (rightSymbols cfg))
        (configRow next)
      rw [hnew]
      exact RowMove.stay cfg.state q' cfg.tape.read b
        (leftSymbols cfg) (rightSymbols cfg) htrans
  | left =>
      by_cases hzero : cfg.tape.head.val = 0
      · have hleft : leftSymbols cfg = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp [hzero]
        have hhead : next.tape.head.val = 0 := by
          simp [next, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hzero]
        have hnew := configRow_eq_of_split (I := I) next [] b
          (rightSymbols cfg) (by simpa [hleft] using htape) (by simpa using hhead)
        change RowMove M embed
          (configCells cfg.state (leftSymbols cfg) cfg.tape.read (rightSymbols cfg))
          (configRow next)
        rw [hleft, hnew]
        exact RowMove.leftClamp cfg.state q' cfg.tape.read b (rightSymbols cfg) htrans
      · have hpos : 0 < cfg.tape.head.val := Nat.pos_of_ne_zero hzero
        have hleftne : leftSymbols cfg ≠ [] := by
          intro he
          have := leftSymbols_length cfg
          rw [he] at this
          simp at this
          omega
        let left := (leftSymbols cfg).dropLast
        let x := (leftSymbols cfg).getLast hleftne
        have hleft : leftSymbols cfg = left ++ [x] := by
          exact (List.dropLast_append_getLast hleftne).symm
        have hlen : cfg.tape.head.val = left.length + 1 := by
          rw [← leftSymbols_length cfg, hleft]
          simp
        have htape' : tapeList next = left ++ x :: b :: rightSymbols cfg := by
          rw [htape, hleft]
          simp
        have hhead : next.tape.head.val = left.length := by
          simp [next, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hpos, hlen]
        have hnew := configRow_eq_of_split (I := I) next left x
          (b :: rightSymbols cfg) htape' hhead
        change RowMove M embed
          (configCells cfg.state (leftSymbols cfg) cfg.tape.read (rightSymbols cfg))
          (configRow next)
        rw [hleft, hnew]
        simpa [configCells, noHeadCells] using
          (RowMove.left (I := I) (M := M) (embed := embed) cfg.state q' x
            cfg.tape.read b left (rightSymbols cfg) htrans)
  | right =>
      by_cases hlast : cfg.tape.head.val = n
      · have hright : rightSymbols cfg = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp [hlast]
        have hhead : next.tape.head.val = (leftSymbols cfg).length := by
          simp [next, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hlast]
        have hnew := configRow_eq_of_split (I := I) next (leftSymbols cfg) b []
          (by simpa [hright] using htape) hhead
        change RowMove M embed
          (configCells cfg.state (leftSymbols cfg) cfg.tape.read (rightSymbols cfg))
          (configRow next)
        rw [hright, hnew]
        exact RowMove.rightClamp cfg.state q' cfg.tape.read b (leftSymbols cfg) htrans
      · have hlt : cfg.tape.head.val < n := by omega
        cases hright : rightSymbols cfg with
        | nil =>
            have := rightSymbols_length cfg
            rw [hright] at this
            simp at this
            omega
        | cons x right =>
            have htape' : tapeList next =
                (leftSymbols cfg ++ [b]) ++ x :: right := by
              rw [htape, hright]
              simp
            have hhead : next.tape.head.val = (leftSymbols cfg ++ [b]).length := by
              simp [next, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hlt]
            have hnew := configRow_eq_of_split (I := I) next
              (leftSymbols cfg ++ [b]) x right htape' hhead
            change RowMove M embed
              (configCells cfg.state (leftSymbols cfg) cfg.tape.read (rightSymbols cfg))
              (configRow next)
            rw [hright, hnew]
            simpa [configCells, noHeadCells] using
              (RowMove.right (I := I) (M := M) (embed := embed) cfg.state q'
                cfg.tape.read b x (leftSymbols cfg) right htrans)

private lemma configRow_write_stay {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (b : Γ) :
    configRow (I := I) (⟨q', (cfg.tape.write b).moveHead .stay⟩ : DLBA.Cfg Γ Λ n) =
      configCells q' (leftSymbols cfg) b (rightSymbols cfg) := by
  apply configRow_eq_of_split
  · rw [tapeList_write_move, tapeList_set_head]
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private lemma configRow_write_leftClamp {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (q' : Λ) (b : Γ) (hzero : cfg.tape.head.val = 0) :
    configRow (I := I) (⟨q', (cfg.tape.write b).moveHead .left⟩ : DLBA.Cfg Γ Λ n) =
      configCells q' [] b (rightSymbols cfg) := by
  have hleft : leftSymbols cfg = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [hzero]
  apply configRow_eq_of_split
  · rw [tapeList_write_move, tapeList_set_head, hleft]
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hzero]

private lemma configRow_write_rightClamp {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (q' : Λ) (b : Γ) (hlast : cfg.tape.head.val = n) :
    configRow (I := I) (⟨q', (cfg.tape.write b).moveHead .right⟩ : DLBA.Cfg Γ Λ n) =
      configCells q' (leftSymbols cfg) b [] := by
  have hright : rightSymbols cfg = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [hlast]
  apply configRow_eq_of_split
  · rw [tapeList_write_move, tapeList_set_head, hright]
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hlast]

private lemma configRow_write_left {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (q' : Λ) (b x : Γ) (left : List Γ)
    (hleft : leftSymbols cfg = left ++ [x]) :
    configRow (I := I) (⟨q', (cfg.tape.write b).moveHead .left⟩ : DLBA.Cfg Γ Λ n) =
      configCells q' left x (b :: rightSymbols cfg) := by
  have hpos : 0 < cfg.tape.head.val := by
    rw [← leftSymbols_length cfg, hleft]
    simp
  have hlen : cfg.tape.head.val = left.length + 1 := by
    rw [← leftSymbols_length cfg, hleft]
    simp
  apply configRow_eq_of_split
  · rw [tapeList_write_move, tapeList_set_head, hleft]
    simp
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hpos, hlen]

private lemma configRow_write_right {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (q' : Λ) (b x : Γ) (right : List Γ)
    (hright : rightSymbols cfg = x :: right) :
    configRow (I := I) (⟨q', (cfg.tape.write b).moveHead .right⟩ : DLBA.Cfg Γ Λ n) =
      configCells q' (leftSymbols cfg ++ [b]) x right := by
  have hlt : cfg.tape.head.val < n := by
    have hlen := rightSymbols_length cfg
    rw [hright] at hlen
    simp at hlen
    omega
  apply configRow_eq_of_split
  · rw [tapeList_write_move, tapeList_set_head, hright]
    simp
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hlt]

/-- Soundness of semantic row moves from a well-formed configuration row. -/
public theorem step_of_rowMove_configRow
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) {row : List (RowCell I Γ Λ)}
    (hmove : RowMove M embed (configRow cfg) row) :
    ∃ cfg' : DLBA.Cfg Γ Λ n, LBA.Step M cfg cfg' ∧ row = configRow cfg' := by
  generalize hold : configRow cfg = old at hmove
  cases hmove with
  | init i is =>
      cases hleft : leftSymbols cfg with
      | nil => simp [configRow, configCells, hleft, noHeadCells] at hold
      | cons x xs => simp [configRow, configCells, hleft, noHeadCells] at hold
  | stay q q' a b left right htrans =>
      have hinv := (configCells_eq_iff (I := I) cfg.state q (leftSymbols cfg) left
        cfg.tape.read a (rightSymbols cfg) right).1 (by simpa [configRow] using hold)
      rcases hinv with ⟨hstate, hleft, ha, hright⟩
      subst q
      subst left
      subst a
      subst right
      refine ⟨⟨q', (cfg.tape.write b).moveHead .stay⟩,
        ⟨q', b, .stay, htrans, rfl⟩, ?_⟩
      exact (configRow_write_stay (I := I) cfg q' b).symm
  | leftClamp q q' a b right htrans =>
      have hinv := (configCells_eq_iff (I := I) cfg.state q (leftSymbols cfg) []
        cfg.tape.read a (rightSymbols cfg) right).1 (by simpa [configRow] using hold)
      rcases hinv with ⟨hstate, hleft, ha, hright⟩
      subst q
      subst a
      subst right
      have hzero : cfg.tape.head.val = 0 := by
        rw [← leftSymbols_length cfg, hleft]
        simp
      refine ⟨⟨q', (cfg.tape.write b).moveHead .left⟩,
        ⟨q', b, .left, htrans, rfl⟩, ?_⟩
      exact (configRow_write_leftClamp (I := I) cfg q' b hzero).symm
  | rightClamp q q' a b left htrans =>
      have hinv := (configCells_eq_iff (I := I) cfg.state q (leftSymbols cfg) left
        cfg.tape.read a (rightSymbols cfg) []).1 (by simpa [configRow] using hold)
      rcases hinv with ⟨hstate, hleft, ha, hright⟩
      subst q
      subst left
      subst a
      have hlast : cfg.tape.head.val = n := by
        have hlen := rightSymbols_length cfg
        rw [hright] at hlen
        simp at hlen
        omega
      refine ⟨⟨q', (cfg.tape.write b).moveHead .right⟩,
        ⟨q', b, .right, htrans, rfl⟩, ?_⟩
      exact (configRow_write_rightClamp (I := I) cfg q' b hlast).symm
  | left q q' x a b left right htrans =>
      have hold' : configCells (I := I) cfg.state (leftSymbols cfg) cfg.tape.read
          (rightSymbols cfg) = configCells (I := I) q (left ++ [x]) a right := by
        simpa [configRow, configCells, noHeadCells] using hold
      have hinv := (configCells_eq_iff (I := I) cfg.state q (leftSymbols cfg)
        (left ++ [x]) cfg.tape.read a (rightSymbols cfg) right).1 hold'
      rcases hinv with ⟨hstate, hleft, ha, hright⟩
      subst q
      subst a
      subst right
      refine ⟨⟨q', (cfg.tape.write b).moveHead .left⟩,
        ⟨q', b, .left, htrans, rfl⟩, ?_⟩
      simpa [configCells, noHeadCells] using
        (configRow_write_left (I := I) cfg q' b x left hleft).symm
  | right q q' a b x left right htrans =>
      have hold' : configCells (I := I) cfg.state (leftSymbols cfg) cfg.tape.read
          (rightSymbols cfg) = configCells (I := I) q left a (x :: right) := by
        simpa [configRow, configCells, noHeadCells] using hold
      have hinv := (configCells_eq_iff (I := I) cfg.state q (leftSymbols cfg) left
        cfg.tape.read a (rightSymbols cfg) (x :: right)).1 hold'
      rcases hinv with ⟨hstate, hleft, ha, hright⟩
      subst q
      subst left
      subst a
      refine ⟨⟨q', (cfg.tape.write b).moveHead .right⟩,
        ⟨q', b, .right, htrans, rfl⟩, ?_⟩
      simpa [configCells, noHeadCells] using
        (configRow_write_right (I := I) cfg q' b x right hright).symm

private lemma foldl_noHead_from_noHead [DecidableEq Λ] (q : Λ) (xs : List Γ) :
    (noHeadCells (I := I) q xs).foldl RowFinal.next (.noHead q) = .noHead q := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [noHeadCells, RowFinal.next] using ih

private lemma foldl_noHead_from_oneHead [DecidableEq Λ] (q : Λ) (xs : List Γ) :
    (noHeadCells (I := I) q xs).foldl RowFinal.next (.oneHead q) = .oneHead q := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [noHeadCells, RowFinal.next] using ih

private lemma evalFinal_configCells [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ)
    (q : Λ) (left : List Γ) (a : Γ) (right : List Γ) :
    (certifiedRowSystem M embed).evalFinal .start (configCells q left a right) =
      .oneHead q := by
  unfold CertifiedRowSystem.evalFinal certifiedRowSystem
  change (configCells (I := I) q left a right).foldl RowFinal.next .start =
    .oneHead q
  cases left with
  | nil =>
      simp only [configCells, noHeadCells, List.map_nil, List.nil_append,
        List.foldl_cons, RowFinal.next]
      exact foldl_noHead_from_oneHead q right
  | cons x left =>
      change (noHeadCells (I := I) q (x :: left) ++
        RowCell.cfg a true q :: noHeadCells q right).foldl RowFinal.next .start = .oneHead q
      rw [List.foldl_append]
      have hp : (noHeadCells (I := I) q (x :: left)).foldl RowFinal.next .start =
          .noHead q := by
        change (noHeadCells (I := I) q left).foldl RowFinal.next
          (RowFinal.next .start (RowCell.cfg x false q)) = .noHead q
        change (noHeadCells (I := I) q left).foldl RowFinal.next (.noHead q) =
          .noHead q
        exact foldl_noHead_from_noHead q left
      rw [hp]
      simp only [List.foldl_cons, RowFinal.next]
      exact foldl_noHead_from_oneHead q right

/-- A canonical configuration row is final exactly when its LBA state is accepting. -/
@[simp] public theorem certifiedRowSystem_final_configRow_iff
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) :
    (certifiedRowSystem M embed).Final (configRow cfg) ↔ M.accept cfg.state = true := by
  unfold CertifiedRowSystem.Final certifiedRowSystem
  change RowFinal.done M
      ((certifiedRowSystem M embed).evalFinal .start
        (configCells (I := I) cfg.state (leftSymbols cfg) cfg.tape.read
          (rightSymbols cfg))) = true ↔ M.accept cfg.state = true
  rw [evalFinal_configCells (I := I) M embed]
  rfl

private lemma tapeList_initCfgList (M : LBA.Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    tapeList (LBA.initCfgList M w hw) = w := by
  unfold tapeList LBA.initCfgList LBA.loadList
  have hlen : w.length - 1 + 1 = w.length := by
    have := List.length_pos_of_ne_nil hw
    omega
  rw [List.ofFn_congr hlen]
  simpa using List.ofFn_get w

/-- The canonical initial configuration row is the initialization target of the raw input row. -/
public theorem configRow_initCfgList
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (i : I) (is : List I)
    (hw : (i :: is).map embed ≠ []) :
    configRow (I := I) (LBA.initCfgList M ((i :: is).map embed) hw) =
      .cfg (embed i) true M.initial :: noHeadCells M.initial (is.map embed) := by
  have htape : tapeList (LBA.initCfgList M ((i :: is).map embed) hw) =
      [] ++ embed i :: is.map embed := by
    simpa using tapeList_initCfgList M ((i :: is).map embed) hw
  exact configRow_eq_of_split (I := I) _ [] (embed i) (is.map embed) htape (by rfl)

/-- Lift an LBA run pointwise to the certified row relation. -/
public theorem rowReach_configRow_of_reaches
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ Λ n} (hreach : LBA.Reaches M cfg cfg') :
    Relation.ReflTransGen (certifiedRowSystem M embed).RowStep
      (configRow cfg) (configRow cfg') := by
  induction hreach with
  | refl => exact .refl
  | tail hreach hstep ih =>
      exact ih.tail ((certifiedRowSystem_rowStep_iff M embed _ _).2
        (rowMove_configRow_of_step M embed hstep))

private lemma foldl_bad [DecidableEq Λ] (xs : List (RowCell I Γ Λ)) :
    xs.foldl RowFinal.next (.bad : RowFinal Λ) = .bad := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [RowFinal.next] using ih

private lemma not_final_raw [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (w : List I) (hw : w ≠ []) :
    ¬ (certifiedRowSystem M embed).Final (w.map .raw) := by
  cases w with
  | nil => contradiction
  | cons i is =>
      intro hfinal
      unfold CertifiedRowSystem.Final certifiedRowSystem at hfinal
      change RowFinal.done M
        ((is.map (RowCell.raw (Γ := Γ) (Λ := Λ))).foldl RowFinal.next .bad) = true
        at hfinal
      rw [foldl_bad] at hfinal
      simp [RowFinal.done] at hfinal

private lemma rowMove_raw_eq_init
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (w : List I) (hw : w ≠ [])
    (hwEmbed : w.map embed ≠ []) {row : List (RowCell I Γ Λ)}
    (hmove : RowMove M embed (w.map .raw) row) :
    row = configRow (LBA.initCfgList M (w.map embed) hwEmbed) := by
  cases w with
  | nil => contradiction
  | cons i is =>
      generalize hold : (i :: is).map (RowCell.raw (I := I) (Γ := Γ) (Λ := Λ)) = old at hmove
      cases hmove with
      | init j js =>
          have hinput : i :: is = j :: js :=
            (Function.Injective.list_map (fun _ _ h => RowCell.raw.inj h)) hold
          cases hinput
          exact (configRow_initCfgList M embed i is hwEmbed).symm
      | stay q q' a b left right htrans =>
          cases left <;> simp [noHeadCells] at hold
      | leftClamp q q' a b right htrans =>
          simp [noHeadCells] at hold
      | rightClamp q q' a b left htrans =>
          cases left <;> simp [noHeadCells] at hold
      | left q q' x a b left right htrans =>
          cases left <;> simp [noHeadCells] at hold
      | right q q' a b x left right htrans =>
          cases left <;> simp [noHeadCells] at hold

private lemma reachable_row_invariant
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) (w : List I)
    (hw : w ≠ []) (hwEmbed : w.map embed ≠ [])
    {row : List (RowCell I Γ Λ)}
    (hpath : Relation.ReflTransGen (certifiedRowSystem M embed).RowStep
      (w.map .raw) row) :
    row = w.map .raw ∨
      ∃ cfg : DLBA.Cfg Γ Λ ((w.map embed).length - 1),
        LBA.Reaches M (LBA.initCfgList M (w.map embed) hwEmbed) cfg ∧
        row = configRow cfg := by
  induction hpath with
  | refl => exact Or.inl rfl
  | tail hpath hstep ih =>
      rcases ih with hraw | ⟨cfg, hreach, hcfg⟩
      · subst hraw
        have hmove := (certifiedRowSystem_rowStep_iff M embed _ _).1 hstep
        exact Or.inr ⟨LBA.initCfgList M (w.map embed) hwEmbed, .refl,
          rowMove_raw_eq_init M embed w hw hwEmbed hmove⟩
      · subst hcfg
        have hmove := (certifiedRowSystem_rowStep_iff M embed _ _).1 hstep
        obtain ⟨cfg', hnext, rfl⟩ := step_of_rowMove_configRow M embed cfg hmove
        exact Or.inr ⟨cfg', hreach.tail hnext, rfl⟩

/-- The certified row system presents exactly the nonempty language of the original LBA. -/
public theorem certifiedRowSystem_rowReachLanguage
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : I → Γ) :
    (certifiedRowSystem M embed).rowReachLanguage = LBA.LanguageViaEmbed M embed := by
  funext w
  apply propext
  constructor
  · rintro ⟨hw, row, hpath, hfinal⟩
    have hwEmbed : w.map embed ≠ [] := by simpa using hw
    rcases reachable_row_invariant M embed w hw hwEmbed hpath with hraw |
      ⟨cfg, hreach, hcfg⟩
    · subst row
      exact (not_final_raw M embed w hw hfinal).elim
    · refine ⟨hwEmbed, cfg, hreach, ?_⟩
      apply (certifiedRowSystem_final_configRow_iff M embed cfg).1
      simpa [hcfg] using hfinal
  · rintro ⟨hwEmbed, cfg, hreach, haccept⟩
    have hw : w ≠ [] := by
      intro hnil
      subst w
      simp at hwEmbed
    cases w with
    | nil => contradiction
    | cons i is =>
        refine ⟨by simp, configRow (I := I) cfg, ?_,
          (certifiedRowSystem_final_configRow_iff M embed cfg).2 haccept⟩
        have hinitRow := configRow_initCfgList M embed i is hwEmbed
        have hinitMove : RowMove M embed
            ((i :: is).map .raw)
            (.cfg (embed i) true M.initial :: noHeadCells M.initial (is.map embed)) :=
          RowMove.init i is
        have hinitStep : (certifiedRowSystem M embed).RowStep
            ((i :: is).map .raw)
            (configRow (LBA.initCfgList M ((i :: is).map embed) hwEmbed)) := by
          rw [hinitRow]
          exact (certifiedRowSystem_rowStep_iff M embed _ _).2 hinitMove
        exact Relation.ReflTransGen.head hinitStep
          (rowReach_configRow_of_reaches M embed hreach)


end LBA
