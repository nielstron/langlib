module

public import Langlib.Automata.LinearBounded.Positive
import Mathlib.Tactic

@[expose]
public section

/-!
# Certified row systems and linearly bounded automata

A `CertifiedRowSystem` describes a length-preserving relation on finite rows.  A successor row is
certified one cell at a time by a finite left-to-right verifier.  This file compiles every such
system to a nondeterministic LBA.  The machine keeps two row tracks on the input-sized tape.  It
guesses and verifies the inactive track in one sweep, and changes the active track only after the
whole certificate has been accepted.

The construction is useful for space-bound arguments whose configurations have already been packed
into a fixed number of logical slots per input cell: the packed cell is the row alphabet `A`, while
`C` contains the finite local annotation witnessing one simulated step.
-/

open List Relation Classical

/-- A finite-state, cellwise-certified, length-preserving row transition system.

`stepCell q old new cert` is the verifier state after checking one aligned pair of cells.  A row
step is valid when some certificate row makes the final verifier state satisfy `stepDone`.
`finalCell` and `finalDone` similarly specify the regular set of target rows. -/
public structure CertifiedRowSystem (I A C Q F : Type*) where
  inputCell : I → A
  stepStart : Q
  stepCell : Q → A → A → C → Q
  stepDone : Q → Bool
  finalStart : F
  finalCell : F → A → F
  finalDone : F → Bool

namespace CertifiedRowSystem

variable {I A C Q F : Type*} (S : CertifiedRowSystem I A C Q F)

/-- Run the step verifier on three aligned lists.  A length mismatch rejects with `none`. -/
def evalStep : Q → List A → List A → List C → Option Q
  | q, [], [], [] => some q
  | q, a :: as, b :: bs, c :: cs => evalStep (S.stepCell q a b c) as bs cs
  | _, _, _, _ => none

/-- The length-preserving row relation certified by `evalStep`. -/
public def RowStep (old new : List A) : Prop :=
  ∃ cert q, S.evalStep S.stepStart old new cert = some q ∧ S.stepDone q = true

/-- Run the finite-state target-row checker. -/
def evalFinal (q : F) (row : List A) : F :=
  row.foldl S.finalCell q

/-- The regular target predicate for rows. -/
public def Final (row : List A) : Prop :=
  S.finalDone (S.evalFinal S.finalStart row) = true

/-- The nonempty input language obtained by row reachability from the cellwise input encoding. -/
public def rowReachLanguage : Language I :=
  fun w => w ≠ [] ∧ ∃ row,
    Relation.ReflTransGen S.RowStep (w.map S.inputCell) row ∧ S.Final row

@[simp] lemma evalStep_nil_iff {q q' : Q} {as bs : List A} {cs : List C} :
    S.evalStep q as bs cs = some q' → as.length = bs.length ∧ as.length = cs.length := by
  intro h
  induction as generalizing q bs cs with
  | nil => cases bs <;> cases cs <;> simp_all [evalStep]
  | cons a as ih =>
      cases bs with
      | nil => simp [evalStep] at h
      | cons b bs =>
          cases cs with
          | nil => simp [evalStep] at h
          | cons c cs =>
              simp only [evalStep] at h
              obtain ⟨h₁, h₂⟩ := ih h
              constructor <;> simp_all

lemma rowStep_length {old new : List A} (h : S.RowStep old new) :
    old.length = new.length := by
  obtain ⟨cert, q, heval, -⟩ := h
  exact (S.evalStep_nil_iff heval).1

/-! ## The compiled machine -/

/-- One physical work cell.  Boundary bits are installed during initialization.  Both row tracks
are optional only so the finite work alphabet remains inhabited without imposing `Inhabited A`;
every active track in a well-formed run is populated. -/
private structure WorkCell (A C : Type*) where
  left : Bool
  right : Bool
  track0 : Option A
  track1 : Option A
  cert : Option C
  deriving DecidableEq, Fintype

private inductive Side where
  | zero
  | one
  deriving DecidableEq, Fintype

private def Side.other : Side → Side
  | .zero => .one
  | .one => .zero

private def WorkCell.track (s : Side) (c : WorkCell A C) : Option A :=
  match s with
  | .zero => c.track0
  | .one => c.track1

private def WorkCell.writeOther (s : Side) (a : A) (cert : C)
    (c : WorkCell A C) : WorkCell A C :=
  match s with
  | .zero => { c with track1 := some a, cert := some cert }
  | .one => { c with track0 := some a, cert := some cert }

private def inputWorkCell (S : CertifiedRowSystem I A C Q F) (left : Bool) (i : I) :
    WorkCell A C :=
  ⟨left, false, some (S.inputCell i), none, none⟩

private inductive State (Q F : Type*) where
  | initFirst
  | initSweep
  | initBack
  | ready (side : Side)
  | step (side : Side) (q : Q)
  | final (side : Side) (q : F)
  | back (side : Side)
  | accept
  deriving DecidableEq

private instance [Fintype Q] [Fintype F] : Fintype (State Q F) := by
  classical
  exact Fintype.ofEquiv
    (Unit ⊕ Unit ⊕ Unit ⊕ Side ⊕ (Side × Q) ⊕ (Side × F) ⊕ Side ⊕ Unit)
    { toFun := fun x => match x with
        | .inl _ => .initFirst
        | .inr (.inl _) => .initSweep
        | .inr (.inr (.inl _)) => .initBack
        | .inr (.inr (.inr (.inl s))) => .ready s
        | .inr (.inr (.inr (.inr (.inl sq)))) => .step sq.1 sq.2
        | .inr (.inr (.inr (.inr (.inr (.inl sf))))) => .final sf.1 sf.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl s)))))) => .back s
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))) => .accept
      invFun := fun x => match x with
        | .initFirst => .inl ()
        | .initSweep => .inr (.inl ())
        | .initBack => .inr (.inr (.inl ()))
        | .ready s => .inr (.inr (.inr (.inl s)))
        | .step s q => .inr (.inr (.inr (.inr (.inl (s, q)))))
        | .final s q => .inr (.inr (.inr (.inr (.inr (.inl (s, q))))))
        | .back s => .inr (.inr (.inr (.inr (.inr (.inr (.inl s))))))
        | .accept => .inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))
      left_inv := fun x => by
        rcases x with _|_|_|_| ⟨_, _⟩ | ⟨_, _⟩ | _ | _ <;> rfl
      right_inv := fun x => by cases x <;> rfl }

private abbrev TapeCell (I A C : Type*) := Option (I ⊕ WorkCell A C)

private def stepChoices (S : CertifiedRowSystem I A C Q F) (side : Side) (q : Q)
    (w : WorkCell A C) : Set (State Q F × TapeCell I A C × DLBA.Dir) :=
  {z | ∃ old new cert,
    w.track side = some old ∧
    let q' := S.stepCell q old new cert
    let w' := w.writeOther side new cert
    if w.right then
      S.stepDone q' = true ∧
        z = (.back side, some (.inr w'), .left)
    else
      z = (.step side q', some (.inr w'), .right)}

private def finalChoice (S : CertifiedRowSystem I A C Q F) (side : Side) (q : F)
    (w : WorkCell A C) : Set (State Q F × TapeCell I A C × DLBA.Dir) :=
  match w.track side with
  | none => ∅
  | some a =>
      let q' := S.finalCell q a
      if w.right then
        if S.finalDone q' then {(.accept, some (.inr w), .stay)} else ∅
      else {(.final side q', some (.inr w), .right)}

private def transition (S : CertifiedRowSystem I A C Q F) :
    State Q F → TapeCell I A C → Set (State Q F × TapeCell I A C × DLBA.Dir)
  | .initFirst, some (.inl i) =>
      {(.initSweep, some (.inr (inputWorkCell S true i)), .right)}
  | .initFirst, _ => ∅
  | .initSweep, some (.inl i) =>
      {(.initSweep, some (.inr (inputWorkCell S false i)), .right)}
  | .initSweep, some (.inr w) =>
      {(.initBack, some (.inr { w with right := true }), .left)}
  | .initSweep, _ => ∅
  | .initBack, some (.inr w) =>
      if w.left then {(.ready .zero, some (.inr w), .stay)}
      else {(.initBack, some (.inr w), .left)}
  | .initBack, _ => ∅
  | .ready side, some (.inr w) =>
      if w.left then
        stepChoices S side S.stepStart w ∪ finalChoice S side S.finalStart w
      else ∅
  | .ready _, _ => ∅
  | .step side q, some (.inr w) => stepChoices S side q w
  | .step _ _, _ => ∅
  | .final side q, some (.inr w) => finalChoice S side q w
  | .final _ _, _ => ∅
  | .back side, some (.inr w) =>
      if w.left then {(.ready side.other, some (.inr w), .stay)}
      else {(.back side, some (.inr w), .left)}
  | .back _, _ => ∅
  | .accept, _ => ∅

private def machine (S : CertifiedRowSystem I A C Q F) :
    LBA.Machine (TapeCell I A C) (State Q F) where
  transition := transition S
  accept := fun q => match q with | .accept => true | _ => false
  initial := .initFirst

/-! ### Canonical tapes and verifier prefixes -/

private def markedCell {n : ℕ} (k : Fin (n + 1))
    (a₀ a₁ : Option A) (cert : Option C) : TapeCell I A C :=
  some (.inr
    ⟨decide (k.val = 0), decide (k.val = n), a₀, a₁, cert⟩)

private def markedTape {n : ℕ} (a₀ a₁ : Fin (n + 1) → Option A)
    (cert : Fin (n + 1) → Option C) : Fin (n + 1) → TapeCell I A C :=
  fun k => markedCell k (a₀ k) (a₁ k) (cert k)

private def trackFn (side : Side) (a₀ a₁ : Fin (n + 1) → Option A) :
    Fin (n + 1) → Option A :=
  match side with
  | .zero => a₀
  | .one => a₁

private def optionRow (a : Fin (n + 1) → Option A) : List A :=
  (List.ofFn a).filterMap id

private abbrev ScanSymbol (A C : Type*) := Option A × Option A × Option C

private def scanSymbol (S : CertifiedRowSystem I A C Q F) (q : Q) :
    ScanSymbol A C → Option Q
  | (some old, some new, some cert) => some (S.stepCell q old new cert)
  | _ => none

private def scanOptions (S : CertifiedRowSystem I A C Q F) :
    Q → List (ScanSymbol A C) → Option Q
  | q, [] => some q
  | q, x :: xs => (scanSymbol S q x).bind fun q' => scanOptions S q' xs

private def scanTape (_S : CertifiedRowSystem I A C Q F) {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C) :
    List (ScanSymbol A C) :=
  List.ofFn fun k => (trackFn side a₀ a₁ k, trackFn side.other a₀ a₁ k, cert k)

private def scanFinalOptions (S : CertifiedRowSystem I A C Q F) :
    F → List (Option A) → Option F
  | q, [] => some q
  | q, some a :: as => scanFinalOptions S (S.finalCell q a) as
  | _, none :: _ => none

private lemma scanOptions_append (q : Q) (xs ys : List (ScanSymbol A C)) :
    scanOptions S q (xs ++ ys) =
      (scanOptions S q xs).bind fun q' => scanOptions S q' ys := by
  induction xs generalizing q with
  | nil => simp [scanOptions]
  | cons x xs ih =>
      simp only [List.cons_append, scanOptions]
      cases h : scanSymbol S q x <;> simp [ih]

private lemma scanOptions_append_some {q q' : Q} {xs : List (ScanSymbol A C)}
    (h : scanOptions S q xs = some q') (old new : A) (cert : C) :
    scanOptions S q (xs ++ [(some old, some new, some cert)]) =
      some (S.stepCell q' old new cert) := by
  rw [scanOptions_append, h]
  simp [scanOptions, scanSymbol]

private lemma scanFinalOptions_append (q : F) (xs ys : List (Option A)) :
    scanFinalOptions S q (xs ++ ys) =
      (scanFinalOptions S q xs).bind fun q' => scanFinalOptions S q' ys := by
  induction xs generalizing q with
  | nil => simp [scanFinalOptions]
  | cons x xs ih =>
      cases x <;> simp [scanFinalOptions, ih]

private lemma scanFinalOptions_append_some {q q' : F} {xs : List (Option A)}
    (h : scanFinalOptions S q xs = some q') (a : A) :
    scanFinalOptions S q (xs ++ [some a]) = some (S.finalCell q' a) := by
  rw [scanFinalOptions_append, h]
  simp [scanFinalOptions]

private lemma scanOptions_sound {q q' : Q} {xs : List (ScanSymbol A C)}
    (h : scanOptions S q xs = some q') :
    S.evalStep q
      (xs.filterMap fun x => x.1)
      (xs.filterMap fun x => x.2.1)
      (xs.filterMap fun x => x.2.2) = some q' := by
  induction xs generalizing q with
  | nil => simpa [scanOptions, evalStep] using h
  | cons x xs ih =>
      rcases x with ⟨old, new, cert⟩
      cases old with
      | none => simp [scanOptions, scanSymbol] at h
      | some old =>
          cases new with
          | none => simp [scanOptions, scanSymbol] at h
          | some new =>
              cases cert with
              | none => simp [scanOptions, scanSymbol] at h
              | some cert =>
                  simp only [scanOptions, scanSymbol, Option.bind_some] at h
                  simpa [evalStep] using ih h

private lemma scanFinalOptions_sound {q q' : F} {xs : List (Option A)}
    (h : scanFinalOptions S q xs = some q') :
    S.evalFinal q (xs.filterMap id) = q' := by
  induction xs generalizing q with
  | nil => simpa [scanFinalOptions, evalFinal] using Option.some.inj h
  | cons x xs ih =>
      cases x with
      | none => simp [scanFinalOptions] at h
      | some a =>
          simp only [scanFinalOptions] at h
          simpa [evalFinal] using ih h

private lemma take_succ_ofFn {α : Type*} {n : ℕ} (f : Fin (n + 1) → α)
    (head : Fin (n + 1)) :
    (List.ofFn f).take (head.val + 1) =
      (List.ofFn f).take head.val ++ [f head] := by
  rw [← List.take_concat_get' (List.ofFn f) head.val (by
    rw [List.length_ofFn]; exact head.isLt), List.getElem_ofFn, Fin.eta]

private lemma update_markedTape {n : ℕ} (a₀ a₁ : Fin (n + 1) → Option A)
    (cert : Fin (n + 1) → Option C) (side : Side) (head : Fin (n + 1))
    (new : A) (c : C) :
    Function.update (markedTape (I := I) a₀ a₁ cert) head
        (some (.inr ((⟨decide (head.val = 0), decide (head.val = n),
          a₀ head, a₁ head, cert head⟩ : WorkCell A C).writeOther side new c))) =
      markedTape (I := I)
        (if side = .one then Function.update a₀ head (some new) else a₀)
        (if side = .zero then Function.update a₁ head (some new) else a₁)
        (Function.update cert head (some c)) := by
  funext k
  by_cases hk : k = head
  · subst k
    cases side <;>
      simp [markedTape, markedCell, WorkCell.writeOther, Function.update_self]
  · simp [markedTape, markedCell, Function.update_of_ne hk]
    cases side <;> simp [hk]

private lemma machine_accept_iff (q : State Q F) :
    (machine S).accept q = true ↔ q = .accept := by
  cases q <;> simp [machine]

private lemma step_mk {n : ℕ} {cfg : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    {q' : State Q F} {a : TapeCell I A C} {d : DLBA.Dir}
    (h : (q', a, d) ∈ transition S cfg.state cfg.tape.read) :
    LBA.Step (machine S) cfg ⟨q', (cfg.tape.write a).moveHead d⟩ :=
  ⟨q', a, d, h, rfl⟩

/-! ### Initialization -/

private def tmpCell {n : ℕ} (input : Fin (n + 1) → I) (k : Fin (n + 1)) :
    TapeCell I A C :=
  some (.inr (inputWorkCell S (decide (k.val = 0)) (input k)))

private def initTapeAt {n : ℕ} (input : Fin (n + 1) → I) (i : ℕ)
    (k : Fin (n + 1)) : TapeCell I A C :=
  if k.val < i then tmpCell S input k else some (.inl (input k))

private lemma initTapeAt_update {n : ℕ} (input : Fin (n + 1) → I)
    (i : Fin (n + 1)) :
    Function.update (initTapeAt S input i.val) i (tmpCell S input i) =
      initTapeAt S input (i.val + 1) := by
  funext k
  rw [Function.update_apply]
  by_cases hk : k = i
  · subst k; simp [initTapeAt]
  · have hkv : k.val ≠ i.val := fun h => hk (Fin.ext h)
    rw [if_neg hk]
    simp only [initTapeAt]
    by_cases hki : k.val < i.val
    · rw [if_pos hki, if_pos (by omega)]
    · rw [if_neg hki, if_neg (by omega)]

private lemma initTapeAt_full {n : ℕ} (input : Fin (n + 1) → I) :
    initTapeAt S input (n + 1) = tmpCell S input := by
  funext k
  simp only [initTapeAt]
  rw [if_pos k.isLt]

private lemma cfg_eq {n : ℕ} {s s' : State Q F}
    {c c' : Fin (n + 1) → TapeCell I A C} {h h' : Fin (n + 1)}
    (hs : s = s') (hc : c = c') (hh : h = h') :
    (⟨s, ⟨c, h⟩⟩ : DLBA.Cfg (TapeCell I A C) (State Q F) n) = ⟨s', ⟨c', h'⟩⟩ := by
  subst hs; subst hc; subst hh; rfl

private lemma convert_step_right {n : ℕ} (input : Fin (n + 1) → I)
    (i : Fin (n + 1)) (hpos : 0 < i.val) (hlt : i.val < n) :
    LBA.Step (machine S)
      ⟨.initSweep, ⟨initTapeAt S input i.val, i⟩⟩
      ⟨.initSweep, ⟨initTapeAt S input (i.val + 1), ⟨i.val + 1, by omega⟩⟩⟩ := by
  refine ⟨.initSweep, tmpCell S input i, .right, ?_, ?_⟩
  · simp only [machine, DLBA.BoundedTape.read]
    rw [show initTapeAt S input i.val i = some (.inl (input i)) by
      simp [initTapeAt]]
    simp [transition, tmpCell, inputWorkCell, hpos.ne']
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt,
      initTapeAt_update]

private lemma convert_step_last {n : ℕ} (input : Fin (n + 1) → I)
    (i : Fin (n + 1)) (hpos : 0 < i.val) (hin : i.val = n) :
    LBA.Step (machine S)
      ⟨.initSweep, ⟨initTapeAt S input i.val, i⟩⟩
      ⟨.initSweep, ⟨initTapeAt S input (i.val + 1), i⟩⟩ := by
  refine ⟨.initSweep, tmpCell S input i, .right, ?_, ?_⟩
  · simp only [machine, DLBA.BoundedTape.read]
    rw [show initTapeAt S input i.val i = some (.inl (input i)) by
      simp [initTapeAt]]
    simp [transition, tmpCell, inputWorkCell, hpos.ne']
  · have hnot : ¬ i.val < n := by omega
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_neg hnot,
      initTapeAt_update]

private lemma convert_sweep {n : ℕ} (input : Fin (n + 1) → I) :
    ∀ i : Fin (n + 1), 1 ≤ i.val →
      LBA.Reaches (machine S)
        ⟨.initSweep, ⟨initTapeAt S input i.val, i⟩⟩
        ⟨.initSweep, ⟨initTapeAt S input (n + 1), Fin.last n⟩⟩ := by
  suffices H : ∀ d, ∀ i : Fin (n + 1), 1 ≤ i.val → n - i.val = d →
      LBA.Reaches (machine S)
        ⟨.initSweep, ⟨initTapeAt S input i.val, i⟩⟩
        ⟨.initSweep, ⟨initTapeAt S input (n + 1), Fin.last n⟩⟩ from
    fun i hi => H (n - i.val) i hi rfl
  intro d
  induction d with
  | zero =>
      intro i hi hdist
      have hin : i.val = n := by have := i.isLt; omega
      have hilast : i = Fin.last n := Fin.ext (by simp [hin])
      have hcfg :
          (⟨State.initSweep, ⟨initTapeAt S input (i.val + 1), i⟩⟩ :
              DLBA.Cfg (TapeCell I A C) (State Q F) n) =
            ⟨.initSweep, ⟨initTapeAt S input (n + 1), Fin.last n⟩⟩ := by
        rw [hilast]
        simp only [Fin.val_last]
      exact Relation.ReflTransGen.single
        (hcfg ▸ convert_step_last S input i (by omega) hin)
  | succ d ih =>
      intro i hi hdist
      have hlt : i.val < n := by omega
      have hnext : n - (i.val + 1) = d := by omega
      let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
      have hj : j.val = i.val + 1 := rfl
      exact Relation.ReflTransGen.head
        (convert_step_right S input i (by omega) hlt)
        (ih j (by omega) (by simpa [hj] using hnext))

private lemma init_to_tmp {n : ℕ} (input : Fin (n + 1) → I) :
    LBA.Reaches (machine S)
      ⟨.initFirst, ⟨initTapeAt S input 0, 0⟩⟩
      ⟨.initSweep, ⟨tmpCell S input, Fin.last n⟩⟩ := by
  let i₀ : Fin (n + 1) := ⟨0, n.succ_pos⟩
  have hmem : (State.initSweep, tmpCell S input i₀, DLBA.Dir.right) ∈
      transition S .initFirst (initTapeAt S input 0 i₀) := by
    simp [i₀, initTapeAt, tmpCell, transition, inputWorkCell]
  have hupd : Function.update (initTapeAt S input 0) i₀ (tmpCell S input i₀) =
      initTapeAt S input 1 := initTapeAt_update S input i₀
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · apply Relation.ReflTransGen.single
    refine ⟨.initSweep, tmpCell S input i₀, .right, hmem, ?_⟩
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    refine cfg_eq rfl ?_ (Fin.ext (by simp))
    have hi₀ : i₀ = 0 := Fin.ext rfl
    rw [← hi₀, hupd]
    exact (initTapeAt_full S input).symm
  · refine Relation.ReflTransGen.head
      (b := ⟨State.initSweep, ⟨initTapeAt S input 1, ⟨1, by omega⟩⟩⟩) ?_ ?_
    · refine ⟨.initSweep, tmpCell S input i₀, .right, hmem, ?_⟩
      simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      apply cfg_eq rfl hupd.symm
      simp [hn]
    · have hone : (1 : ℕ) ≤ (⟨1, by omega⟩ : Fin (n + 1)).val := by simp
      simpa [initTapeAt_full] using convert_sweep S input ⟨1, by omega⟩ hone

private lemma tmp_to_marked {n : ℕ} (input : Fin (n + 1) → I) :
    ∃ head : Fin (n + 1),
      LBA.Step (machine S)
        ⟨.initSweep, ⟨tmpCell S input, Fin.last n⟩⟩
        ⟨.initBack,
          ⟨markedTape (I := I) (fun k => some (S.inputCell (input k)))
              (fun _ => none) (fun _ => none), head⟩⟩ := by
  let W : WorkCell A C :=
    ⟨decide ((Fin.last n).val = 0), false,
      some (S.inputCell (input (Fin.last n))), none, none⟩
  let out : TapeCell I A C := some (.inr { W with right := true })
  let head : Fin (n + 1) :=
    if h : 0 < n then ⟨n - 1, by omega⟩ else Fin.last n
  refine ⟨head, ⟨.initBack, out, .left, ?_, ?_⟩⟩
  · change (.initBack, out, .left) ∈ transition S .initSweep (tmpCell S input (Fin.last n))
    simp [tmpCell, transition, W, out, inputWorkCell]
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    apply cfg_eq rfl
    · funext k
      simp only [Function.update_apply]
      by_cases hk : k = Fin.last n
      · subst k
        simp [out, W, markedTape, markedCell]
      · rw [if_neg hk]
        have hkn : k.val ≠ n := fun h => hk (Fin.ext (by simpa using h))
        simp [markedTape, markedCell, tmpCell, inputWorkCell, hkn]
    · simp [head]

private lemma initBack_reaches {n : ℕ}
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C)
    (head : Fin (n + 1)) :
    LBA.Reaches (machine S)
      ⟨.initBack, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩
      ⟨.ready .zero, ⟨markedTape (I := I) a₀ a₁ cert, 0⟩⟩ := by
  suffices H : ∀ m, ∀ head : Fin (n + 1), head.val = m →
      LBA.Reaches (machine S)
        ⟨.initBack, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩
        ⟨.ready .zero, ⟨markedTape (I := I) a₀ a₁ cert, 0⟩⟩ from
    H head.val head rfl
  intro m
  induction m with
  | zero =>
      intro head hh
      have heq : head = 0 := Fin.ext (by simpa using hh)
      subst head
      apply Relation.ReflTransGen.single
      refine ⟨.ready .zero, markedTape (I := I) a₀ a₁ cert 0, .stay, ?_, ?_⟩
      · simp only [machine, DLBA.BoundedTape.read]
        simp [markedTape, markedCell, transition]
      · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, Function.update_eq_self]
  | succ m ih =>
      intro head hh
      have hpos : 0 < head.val := by omega
      let prev : Fin (n + 1) := ⟨head.val - 1, by omega⟩
      refine Relation.ReflTransGen.head (b :=
        ⟨State.initBack, ⟨markedTape (I := I) a₀ a₁ cert, prev⟩⟩) ?_ ?_
      · refine ⟨.initBack, markedTape (I := I) a₀ a₁ cert head, .left, ?_, ?_⟩
        · simp only [machine, DLBA.BoundedTape.read]
          simp [markedTape, markedCell, transition, hpos.ne']
        · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
            Function.update_eq_self, hpos, prev]
      · exact ih prev (by simp [prev]; omega)

private lemma init_reaches {n : ℕ} (input : Fin (n + 1) → I) :
    LBA.Reaches (machine S)
      ⟨.initFirst, ⟨fun k => some (.inl (input k)), 0⟩⟩
      ⟨.ready .zero,
        ⟨markedTape (I := I) (fun k => some (S.inputCell (input k)))
          (fun _ => none) (fun _ => none), 0⟩⟩ := by
  have hraw : (fun k => some (.inl (input k)) : Fin (n + 1) → TapeCell I A C) =
      initTapeAt S input 0 := by funext k; simp [initTapeAt]
  rw [hraw]
  refine (init_to_tmp S input).trans ?_
  obtain ⟨head, hmark⟩ := tmp_to_marked S input
  exact Relation.ReflTransGen.head hmark
    (initBack_reaches S _ _ _ head)

/-! ### Completeness of one certified sweep -/

private def prefixWrite {X : Type*} {n : ℕ} (base : Fin (n + 1) → Option X)
    (target : Fin (n + 1) → X) (i : ℕ) : Fin (n + 1) → Option X :=
  fun k => if k.val < i then some (target k) else base k

@[simp] private lemma prefixWrite_zero {X : Type*} {n : ℕ}
    (base : Fin (n + 1) → Option X) (target : Fin (n + 1) → X) :
    prefixWrite base target 0 = base := by
  funext k
  simp [prefixWrite]

private lemma prefixWrite_update {X : Type*} {n : ℕ}
    (base : Fin (n + 1) → Option X) (target : Fin (n + 1) → X)
    (head : Fin (n + 1)) :
    Function.update (prefixWrite base target head.val) head (some (target head)) =
      prefixWrite base target (head.val + 1) := by
  funext k
  rw [Function.update_apply]
  by_cases hk : k = head
  · subst k; simp [prefixWrite]
  · have hkv : k.val ≠ head.val := fun h => hk (Fin.ext h)
    rw [if_neg hk]
    simp only [prefixWrite]
    by_cases hlt : k.val < head.val
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

private lemma prefixWrite_full {X : Type*} {n : ℕ}
    (base : Fin (n + 1) → Option X) (target : Fin (n + 1) → X) :
    prefixWrite base target (n + 1) = fun k => some (target k) := by
  funext k
  simp [prefixWrite, k.isLt]

private def stepTrack0At {n : ℕ} (side : Side)
    (a₀ : Fin (n + 1) → Option A) (new : Fin (n + 1) → A) (i : ℕ) :=
  match side with
  | .zero => a₀
  | .one => prefixWrite a₀ new i

private def stepTrack1At {n : ℕ} (side : Side)
    (a₁ : Fin (n + 1) → Option A) (new : Fin (n + 1) → A) (i : ℕ) :=
  match side with
  | .zero => prefixWrite a₁ new i
  | .one => a₁

private def stepCertAt {n : ℕ} (cert₀ : Fin (n + 1) → Option C)
    (cert : Fin (n + 1) → C) (i : ℕ) :=
  prefixWrite cert₀ cert i

@[simp] private lemma stepTrack0At_zero {n : ℕ} (side : Side)
    (a₀ : Fin (n + 1) → Option A) (new : Fin (n + 1) → A) :
    stepTrack0At side a₀ new 0 = a₀ := by cases side <;> simp [stepTrack0At]

@[simp] private lemma stepTrack1At_zero {n : ℕ} (side : Side)
    (a₁ : Fin (n + 1) → Option A) (new : Fin (n + 1) → A) :
    stepTrack1At side a₁ new 0 = a₁ := by cases side <;> simp [stepTrack1At]

@[simp] private lemma stepCertAt_zero {n : ℕ}
    (cert₀ : Fin (n + 1) → Option C) (cert : Fin (n + 1) → C) :
    stepCertAt cert₀ cert 0 = cert₀ := by simp [stepCertAt]

private def stepTapeAt {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert₀ : Fin (n + 1) → Option C)
    (new : Fin (n + 1) → A) (cert : Fin (n + 1) → C) (i : ℕ) :=
  markedTape (I := I) (stepTrack0At side a₀ new i) (stepTrack1At side a₁ new i)
    (stepCertAt cert₀ cert i)

private lemma stepTapeAt_update {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert₀ : Fin (n + 1) → Option C)
    (new : Fin (n + 1) → A) (cert : Fin (n + 1) → C)
    (head : Fin (n + 1)) :
    Function.update (stepTapeAt (I := I) side a₀ a₁ cert₀ new cert head.val) head
      (some (.inr
        ((⟨decide (head.val = 0), decide (head.val = n),
          stepTrack0At side a₀ new head.val head,
          stepTrack1At side a₁ new head.val head,
          stepCertAt cert₀ cert head.val head⟩ : WorkCell A C).writeOther
            side (new head) (cert head)))) =
    stepTapeAt (I := I) side a₀ a₁ cert₀ new cert (head.val + 1) := by
  simp only [stepTapeAt]
  rw [update_markedTape]
  cases side <;>
    simp [stepTrack0At, stepTrack1At, stepCertAt, prefixWrite_update]

private lemma stepTapeAt_full {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert₀ : Fin (n + 1) → Option C)
    (new : Fin (n + 1) → A) (cert : Fin (n + 1) → C) :
    stepTapeAt (I := I) side a₀ a₁ cert₀ new cert (n + 1) =
      markedTape (I := I)
        (if side = .one then (fun k => some (new k)) else a₀)
        (if side = .zero then (fun k => some (new k)) else a₁)
        (fun k => some (cert k)) := by
  cases side <;>
    simp [stepTapeAt, stepTrack0At, stepTrack1At, stepCertAt, prefixWrite_full]

private lemma stepTapeAt_zero {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert₀ : Fin (n + 1) → Option C)
    (new : Fin (n + 1) → A) (cert : Fin (n + 1) → C) :
    stepTapeAt (I := I) side a₀ a₁ cert₀ new cert 0 =
      markedTape (I := I) a₀ a₁ cert₀ := by
  cases side <;>
    simp [stepTapeAt, stepTrack0At, stepTrack1At, stepCertAt]

private def desiredScan {n : ℕ} (old new : Fin (n + 1) → A)
    (cert : Fin (n + 1) → C) : List (ScanSymbol A C) :=
  List.ofFn fun k => (some (old k), some (new k), some (cert k))

private lemma desiredScan_eval {n : ℕ} (q : Q) (old new : Fin (n + 1) → A)
    (cert : Fin (n + 1) → C) :
    scanOptions S q (desiredScan old new cert) =
      S.evalStep q (List.ofFn old) (List.ofFn new) (List.ofFn cert) := by
  induction n generalizing q with
  | zero => simp [desiredScan, scanOptions, scanSymbol, evalStep, List.ofFn_succ]
  | succ n ih =>
      rw [show desiredScan old new cert =
          (some (old 0), some (new 0), some (cert 0)) ::
            desiredScan (fun k => old k.succ) (fun k => new k.succ)
              (fun k => cert k.succ) by
        simp [desiredScan, List.ofFn_succ]]
      simp only [scanOptions, scanSymbol, Option.bind_some]
      rw [show List.ofFn old = old 0 :: List.ofFn (fun k => old k.succ) by
          simp [List.ofFn_succ],
        show List.ofFn new = new 0 :: List.ofFn (fun k => new k.succ) by
          simp [List.ofFn_succ],
        show List.ofFn cert = cert 0 :: List.ofFn (fun k => cert k.succ) by
          simp [List.ofFn_succ], evalStep]
      exact ih (fun k => old k.succ) (fun k => new k.succ) (fun k => cert k.succ)
        (q := S.stepCell q (old 0) (new 0) (cert 0))

private lemma desiredScan_take_succ {n : ℕ} (old new : Fin (n + 1) → A)
    (cert : Fin (n + 1) → C) (head : Fin (n + 1)) :
    (desiredScan old new cert).take (head.val + 1) =
      (desiredScan old new cert).take head.val ++
        [(some (old head), some (new head), some (cert head))] := by
  simpa [desiredScan] using
    (take_succ_ofFn
      (fun k => (some (old k), some (new k), some (cert k))) head)

private lemma step_sweep_from {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert₀ : Fin (n + 1) → Option C)
    (old new : Fin (n + 1) → A) (cert : Fin (n + 1) → C)
    (hactive : trackFn side a₀ a₁ = fun k => some (old k))
    (q : Q) (head : Fin (n + 1)) (hpos : 1 ≤ head.val)
    (hq : scanOptions S S.stepStart ((desiredScan old new cert).take head.val) = some q)
    (qend : Q)
    (hend : scanOptions S S.stepStart (desiredScan old new cert) = some qend)
    (hdone : S.stepDone qend = true) :
    ∃ backHead : Fin (n + 1),
      LBA.Reaches (machine S)
        ⟨.step side q,
          ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert head.val, head⟩⟩
        ⟨.back side,
          ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert (n + 1), backHead⟩⟩ := by
  suffices H : ∀ d, ∀ (q : Q) (head : Fin (n + 1)), 1 ≤ head.val → n - head.val = d →
      scanOptions S S.stepStart ((desiredScan old new cert).take head.val) = some q →
      ∃ backHead : Fin (n + 1),
        LBA.Reaches (machine S)
          ⟨.step side q,
            ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert head.val, head⟩⟩
          ⟨.back side,
            ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert (n + 1), backHead⟩⟩ from
    H (n - head.val) q head hpos rfl hq
  intro d
  induction d with
  | zero =>
      intro q head hpos hdist hq
      have hlast : head.val = n := by have := head.isLt; omega
      have hscanSucc :
          scanOptions S S.stepStart ((desiredScan old new cert).take (head.val + 1)) =
            some (S.stepCell q (old head) (new head) (cert head)) := by
        rw [desiredScan_take_succ]
        exact scanOptions_append_some S hq _ _ _
      have hfull : (desiredScan old new cert).take (head.val + 1) =
          desiredScan old new cert := by
        apply (List.take_eq_self_iff _).2
        simp [desiredScan]
        omega
      have hqend : S.stepCell q (old head) (new head) (cert head) = qend := by
        rw [hfull, hend] at hscanSucc
        exact (Option.some.inj hscanSucc).symm
      let w : WorkCell A C :=
        ⟨decide (head.val = 0), decide (head.val = n),
          stepTrack0At side a₀ new head.val head,
          stepTrack1At side a₁ new head.val head,
          stepCertAt cert₀ cert head.val head⟩
      let out : TapeCell I A C := some (.inr (w.writeOther side (new head) (cert head)))
      let backHead : Fin (n + 1) :=
        if h : 0 < head.val then ⟨head.val - 1, by omega⟩ else head
      refine ⟨backHead, Relation.ReflTransGen.single ⟨.back side, out, .left, ?_, ?_⟩⟩
      · simp only [machine, DLBA.BoundedTape.read]
        change (.back side, out, .left) ∈ stepChoices S side q w
        refine ⟨old head, new head, cert head, ?_, ?_⟩
        · cases side <;> simpa [w, WorkCell.track, stepTrack0At, stepTrack1At] using
            congrFun hactive head
        · simp [w, out, hlast, hqend, hdone]
      · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        apply cfg_eq rfl
        · dsimp [out, w]
          simpa [hlast] using (stepTapeAt_update side a₀ a₁ cert₀ new cert head).symm
        · apply Fin.ext
          have hp : 0 < head.val := by omega
          simp [backHead, hp]
  | succ d ih =>
      intro q head hpos hdist hq
      have hlt : head.val < n := by omega
      let q' := S.stepCell q (old head) (new head) (cert head)
      let next : Fin (n + 1) := ⟨head.val + 1, by omega⟩
      have hq' : scanOptions S S.stepStart
          ((desiredScan old new cert).take next.val) = some q' := by
        rw [show next.val = head.val + 1 from rfl, desiredScan_take_succ]
        exact scanOptions_append_some S hq _ _ _
      obtain ⟨backHead, hrest⟩ := ih q' next (by simp [next])
        (by simp [next]; omega) hq'
      have hstep : LBA.Step (machine S)
          ⟨.step side q,
            ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert head.val, head⟩⟩
          ⟨.step side q',
            ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert next.val, next⟩⟩ := by
        refine ⟨.step side q',
        some (.inr
          ((⟨decide (head.val = 0), decide (head.val = n),
            stepTrack0At side a₀ new head.val head,
            stepTrack1At side a₁ new head.val head,
            stepCertAt cert₀ cert head.val head⟩ : WorkCell A C).writeOther
              side (new head) (cert head))), .right, ?_, ?_⟩
        · simp only [machine, DLBA.BoundedTape.read]
          change _ ∈ stepChoices S side q
            ⟨decide (head.val = 0), decide (head.val = n),
              stepTrack0At side a₀ new head.val head,
              stepTrack1At side a₁ new head.val head,
              stepCertAt cert₀ cert head.val head⟩
          refine ⟨old head, new head, cert head, ?_, ?_⟩
          · cases side <;> simpa [WorkCell.track, stepTrack0At, stepTrack1At] using
              congrFun hactive head
          · simp [q', hlt.ne]
        · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt]
          exact cfg_eq rfl (stepTapeAt_update side a₀ a₁ cert₀ new cert head).symm rfl
      exact ⟨backHead, Relation.ReflTransGen.head hstep hrest⟩

private lemma back_reaches {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C)
    (head : Fin (n + 1)) :
    LBA.Reaches (machine S)
      ⟨.back side, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩
      ⟨.ready side.other, ⟨markedTape (I := I) a₀ a₁ cert, 0⟩⟩ := by
  suffices H : ∀ m, ∀ head : Fin (n + 1), head.val = m →
      LBA.Reaches (machine S)
        ⟨.back side, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩
        ⟨.ready side.other, ⟨markedTape (I := I) a₀ a₁ cert, 0⟩⟩ from
    H head.val head rfl
  intro m
  induction m with
  | zero =>
      intro head hh
      have heq : head = 0 := Fin.ext (by simpa using hh)
      subst head
      apply Relation.ReflTransGen.single
      refine ⟨.ready side.other, markedTape (I := I) a₀ a₁ cert 0, .stay, ?_, ?_⟩
      · simp only [machine, DLBA.BoundedTape.read]
        simp [markedTape, markedCell, transition]
      · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, Function.update_eq_self]
  | succ m ih =>
      intro head hh
      have hpos : 0 < head.val := by omega
      let prev : Fin (n + 1) := ⟨head.val - 1, by omega⟩
      refine Relation.ReflTransGen.head (b :=
        ⟨State.back side, ⟨markedTape (I := I) a₀ a₁ cert, prev⟩⟩) ?_ ?_
      · refine ⟨.back side, markedTape (I := I) a₀ a₁ cert head, .left, ?_, ?_⟩
        · simp only [machine, DLBA.BoundedTape.read]
          simp [markedTape, markedCell, transition, hpos.ne']
        · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
            Function.update_eq_self, hpos, prev]
      · exact ih prev (by simp [prev]; omega)

private lemma simulate_step {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert₀ : Fin (n + 1) → Option C)
    (old new : Fin (n + 1) → A) (cert : Fin (n + 1) → C)
    (hactive : trackFn side a₀ a₁ = fun k => some (old k))
    (qend : Q)
    (heval : S.evalStep S.stepStart (List.ofFn old) (List.ofFn new) (List.ofFn cert) =
      some qend)
    (hdone : S.stepDone qend = true) :
    LBA.Reaches (machine S)
      ⟨.ready side, ⟨markedTape (I := I) a₀ a₁ cert₀, 0⟩⟩
      ⟨.ready side.other,
        ⟨markedTape (I := I)
          (if side = .one then (fun k => some (new k)) else a₀)
          (if side = .zero then (fun k => some (new k)) else a₁)
          (fun k => some (cert k)), 0⟩⟩ := by
  have hend : scanOptions S S.stepStart (desiredScan old new cert) = some qend := by
    rw [desiredScan_eval]
    exact heval
  let q₁ := S.stepCell S.stepStart (old 0) (new 0) (cert 0)
  let out : TapeCell I A C := some (.inr
    ((⟨true, decide (n = 0), a₀ 0, a₁ 0, cert₀ 0⟩ : WorkCell A C).writeOther
      side (new 0) (cert 0)))
  have hfirstMem :
      (if n = 0 then (State.back side, out, DLBA.Dir.left)
        else (State.step side q₁, out, DLBA.Dir.right)) ∈
      transition S (.ready side) (markedTape (I := I) a₀ a₁ cert₀ 0) := by
    simp only [markedTape, markedCell, Fin.val_zero]
    change _ ∈ stepChoices S side S.stepStart
      ⟨true, decide (0 = n), a₀ 0, a₁ 0, cert₀ 0⟩ ∪ _
    apply Or.inl
    refine ⟨old 0, new 0, cert 0, ?_, ?_⟩
    · cases side <;> simpa [WorkCell.track] using congrFun hactive 0
    · by_cases hn : n = 0
      · subst n
        have hq : q₁ = qend := by
          have := hend
          simp [desiredScan, scanOptions, scanSymbol, List.ofFn_succ] at this
          exact this
        simp [q₁, out, hq, hdone]
      · have h0n : 0 ≠ n := Ne.symm hn
        simp [hn, h0n, q₁, out]
  by_cases hn : n = 0
  · subst n
    have hwrite :
        (DLBA.BoundedTape.write
          (⟨markedTape (I := I) a₀ a₁ cert₀, (0 : Fin 1)⟩ :
            DLBA.BoundedTape (TapeCell I A C) 0) out).moveHead .left =
          ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert 1, 0⟩ := by
      simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      apply congrArg₂ DLBA.BoundedTape.mk
      · have hup := stepTapeAt_update (I := I) side a₀ a₁ cert₀ new cert (0 : Fin 1)
        simpa [stepTapeAt_zero, out, eq_comm] using hup
      · rfl
    have hstep : LBA.Step (machine S)
        ⟨.ready side, ⟨markedTape (I := I) a₀ a₁ cert₀, 0⟩⟩
        ⟨.back side, ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert 1, 0⟩⟩ := by
      refine ⟨.back side, out, .left, ?_, ?_⟩
      · simpa using hfirstMem
      · congr 1
        exact hwrite.symm
    rw [stepTapeAt_full] at hstep
    exact Relation.ReflTransGen.head hstep
      (back_reaches S side _ _ _ 0)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let head₁ : Fin (n + 1) := ⟨1, by omega⟩
    have hstep : LBA.Step (machine S)
        ⟨.ready side, ⟨markedTape (I := I) a₀ a₁ cert₀, 0⟩⟩
        ⟨.step side q₁,
          ⟨stepTapeAt (I := I) side a₀ a₁ cert₀ new cert 1, head₁⟩⟩ := by
      refine ⟨.step side q₁, out, .right, ?_, ?_⟩
      · simpa [hn] using hfirstMem
      · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        have hup := stepTapeAt_update (I := I) side a₀ a₁ cert₀ new cert
          (0 : Fin (n + 1))
        exact cfg_eq rfl (by simpa [stepTapeAt_zero, out, eq_comm] using hup.symm)
          (Fin.ext (by simp [head₁, hnpos]))
    have hq₁ : scanOptions S S.stepStart ((desiredScan old new cert).take head₁.val) =
        some q₁ := by
      simp [head₁, desiredScan, List.ofFn_succ, scanOptions, scanSymbol, q₁]
    obtain ⟨backHead, hsweep⟩ := step_sweep_from S side a₀ a₁ cert₀ old new cert hactive
      q₁ head₁ (by simp [head₁]) hq₁ qend hend hdone
    rw [stepTapeAt_full] at hsweep
    exact Relation.ReflTransGen.head hstep
      (hsweep.trans (back_reaches S side _ _ _ backHead))

/-! ### Completeness of the target-row sweep -/

private def desiredFinal {n : ℕ} (row : Fin (n + 1) → A) : List (Option A) :=
  List.ofFn fun k => some (row k)

private lemma desiredFinal_eval {n : ℕ} (q : F) (row : Fin (n + 1) → A) :
    scanFinalOptions S q (desiredFinal row) = some (S.evalFinal q (List.ofFn row)) := by
  induction n generalizing q with
  | zero => simp [desiredFinal, scanFinalOptions, evalFinal, List.ofFn_succ]
  | succ n ih =>
      rw [show desiredFinal row = some (row 0) :: desiredFinal (fun k => row k.succ) by
        simp [desiredFinal, List.ofFn_succ], scanFinalOptions]
      rw [show List.ofFn row = row 0 :: List.ofFn (fun k => row k.succ) by
        simp [List.ofFn_succ], evalFinal]
      simpa [evalFinal] using
        (ih (fun k => row k.succ) (q := S.finalCell q (row 0)))

private lemma desiredFinal_take_succ {n : ℕ} (row : Fin (n + 1) → A)
    (head : Fin (n + 1)) :
    (desiredFinal row).take (head.val + 1) =
      (desiredFinal row).take head.val ++ [some (row head)] := by
  simpa [desiredFinal] using take_succ_ofFn (fun k => some (row k)) head

private lemma final_sweep_from {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert₀ : Fin (n + 1) → Option C)
    (row : Fin (n + 1) → A)
    (hactive : trackFn side a₀ a₁ = fun k => some (row k))
    (q : F) (head : Fin (n + 1)) (hpos : 1 ≤ head.val)
    (hq : scanFinalOptions S S.finalStart ((desiredFinal row).take head.val) = some q)
    (qend : F)
    (hend : scanFinalOptions S S.finalStart (desiredFinal row) = some qend)
    (hdone : S.finalDone qend = true) :
    LBA.Reaches (machine S)
      ⟨.final side q, ⟨markedTape (I := I) a₀ a₁ cert₀, head⟩⟩
      ⟨.accept, ⟨markedTape (I := I) a₀ a₁ cert₀, Fin.last n⟩⟩ := by
  suffices H : ∀ d, ∀ (q : F) (head : Fin (n + 1)), 1 ≤ head.val → n - head.val = d →
      scanFinalOptions S S.finalStart ((desiredFinal row).take head.val) = some q →
      LBA.Reaches (machine S)
        ⟨.final side q, ⟨markedTape (I := I) a₀ a₁ cert₀, head⟩⟩
        ⟨.accept, ⟨markedTape (I := I) a₀ a₁ cert₀, Fin.last n⟩⟩ from
    H (n - head.val) q head hpos rfl hq
  intro d
  induction d with
  | zero =>
      intro q head hpos hdist hq
      have hlast : head.val = n := by have := head.isLt; omega
      have hscan : scanFinalOptions S S.finalStart
          ((desiredFinal row).take (head.val + 1)) =
            some (S.finalCell q (row head)) := by
        rw [desiredFinal_take_succ]
        exact scanFinalOptions_append_some S hq _
      have hfull : (desiredFinal row).take (head.val + 1) = desiredFinal row := by
        apply (List.take_eq_self_iff _).2
        simp [desiredFinal]
        omega
      have hqend : S.finalCell q (row head) = qend := by
        rw [hfull, hend] at hscan
        exact (Option.some.inj hscan).symm
      apply Relation.ReflTransGen.single
      refine ⟨.accept, markedTape (I := I) a₀ a₁ cert₀ head, .stay, ?_, ?_⟩
      · simp only [machine, DLBA.BoundedTape.read]
        change (.accept, markedTape (I := I) a₀ a₁ cert₀ head, .stay) ∈
          finalChoice S side q
            ⟨decide (head.val = 0), decide (head.val = n), a₀ head, a₁ head, cert₀ head⟩
        cases side with
        | zero =>
            have ha : a₀ head = some (row head) := by
              simpa [trackFn] using congrFun hactive head
            simp [finalChoice, WorkCell.track, ha, hlast, hqend, hdone,
              markedTape, markedCell]
        | one =>
            have ha : a₁ head = some (row head) := by
              simpa [trackFn] using congrFun hactive head
            simp [finalChoice, WorkCell.track, ha, hlast, hqend, hdone,
              markedTape, markedCell]
      · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
          Function.update_eq_self]
        apply cfg_eq rfl rfl
        exact Fin.ext (by simp [hlast])
  | succ d ih =>
      intro q head hpos hdist hq
      have hlt : head.val < n := by omega
      let q' := S.finalCell q (row head)
      let next : Fin (n + 1) := ⟨head.val + 1, by omega⟩
      have hq' : scanFinalOptions S S.finalStart
          ((desiredFinal row).take next.val) = some q' := by
        rw [show next.val = head.val + 1 from rfl, desiredFinal_take_succ]
        exact scanFinalOptions_append_some S hq _
      have hstep : LBA.Step (machine S)
          ⟨.final side q, ⟨markedTape (I := I) a₀ a₁ cert₀, head⟩⟩
          ⟨.final side q', ⟨markedTape (I := I) a₀ a₁ cert₀, next⟩⟩ := by
        refine ⟨.final side q', markedTape (I := I) a₀ a₁ cert₀ head, .right, ?_, ?_⟩
        · simp only [machine, DLBA.BoundedTape.read]
          change _ ∈ finalChoice S side q
            ⟨decide (head.val = 0), decide (head.val = n), a₀ head, a₁ head, cert₀ head⟩
          cases side with
          | zero =>
              have ha : a₀ head = some (row head) := by
                simpa [trackFn] using congrFun hactive head
              simp [finalChoice, WorkCell.track, ha, q', hlt.ne, markedTape, markedCell]
          | one =>
              have ha : a₁ head = some (row head) := by
                simpa [trackFn] using congrFun hactive head
              simp [finalChoice, WorkCell.track, ha, q', hlt.ne, markedTape, markedCell]
        · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
            Function.update_eq_self, hlt, next]
      exact Relation.ReflTransGen.head hstep
        (ih q' next (by simp [next]) (by simp [next]; omega) hq')

private lemma simulate_final {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert₀ : Fin (n + 1) → Option C)
    (row : Fin (n + 1) → A)
    (hactive : trackFn side a₀ a₁ = fun k => some (row k))
    (hfinal : S.Final (List.ofFn row)) :
    LBA.Accepts (machine S)
      ⟨.ready side, ⟨markedTape (I := I) a₀ a₁ cert₀, 0⟩⟩ := by
  let qend := S.evalFinal S.finalStart (List.ofFn row)
  have hend : scanFinalOptions S S.finalStart (desiredFinal row) = some qend :=
    desiredFinal_eval S _ _
  have hdone : S.finalDone qend = true := hfinal
  let q₁ := S.finalCell S.finalStart (row 0)
  by_cases hn : n = 0
  · subst n
    have hq : q₁ = qend := by
      have := hend
      simpa [desiredFinal, scanFinalOptions, List.ofFn_succ, q₁] using Option.some.inj this
    let cfgacc : DLBA.Cfg (TapeCell I A C) (State Q F) 0 :=
      ⟨.accept, ⟨markedTape (I := I) a₀ a₁ cert₀, 0⟩⟩
    refine ⟨cfgacc, Relation.ReflTransGen.single ?_, by simp [machine, cfgacc]⟩
    refine ⟨.accept, markedTape (I := I) a₀ a₁ cert₀ 0, .stay, ?_, ?_⟩
    · simp only [machine, DLBA.BoundedTape.read]
      change _ ∈ transition S (.ready side) (markedTape (I := I) a₀ a₁ cert₀ 0)
      simp only [markedTape, markedCell, Fin.val_zero]
      simp only [transition]
      rw [if_pos (by simp)]
      apply Or.inr
      cases side with
      | zero =>
          have ha : a₀ 0 = some (row 0) := by simpa [trackFn] using congrFun hactive 0
          simp [finalChoice, WorkCell.track, ha, q₁, hq, hdone]
      | one =>
          have ha : a₁ 0 = some (row 0) := by simpa [trackFn] using congrFun hactive 0
          simp [finalChoice, WorkCell.track, ha, q₁, hq, hdone]
    · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, Function.update_eq_self, cfgacc]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let head₁ : Fin (n + 1) := ⟨1, by omega⟩
    have hstep : LBA.Step (machine S)
        ⟨.ready side, ⟨markedTape (I := I) a₀ a₁ cert₀, 0⟩⟩
        ⟨.final side q₁, ⟨markedTape (I := I) a₀ a₁ cert₀, head₁⟩⟩ := by
      refine ⟨.final side q₁, markedTape (I := I) a₀ a₁ cert₀ 0, .right, ?_, ?_⟩
      · simp only [machine, DLBA.BoundedTape.read]
        change _ ∈ transition S (.ready side) (markedTape (I := I) a₀ a₁ cert₀ 0)
        simp only [markedTape, markedCell, Fin.val_zero]
        simp only [transition]
        rw [if_pos (by simp)]
        apply Or.inr
        have h0n : 0 ≠ n := Ne.symm hn
        cases side with
        | zero =>
            have ha : a₀ 0 = some (row 0) := by simpa [trackFn] using congrFun hactive 0
            simp [finalChoice, WorkCell.track, ha, q₁, h0n]
        | one =>
            have ha : a₁ 0 = some (row 0) := by simpa [trackFn] using congrFun hactive 0
            simp [finalChoice, WorkCell.track, ha, q₁, h0n]
      · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
          Function.update_eq_self, hnpos, head₁]
    have hq₁ : scanFinalOptions S S.finalStart
        ((desiredFinal row).take head₁.val) = some q₁ := by
      simp [head₁, desiredFinal, List.ofFn_succ, scanFinalOptions, q₁]
    let cfgacc : DLBA.Cfg (TapeCell I A C) (State Q F) n :=
      ⟨.accept, ⟨markedTape (I := I) a₀ a₁ cert₀, Fin.last n⟩⟩
    refine ⟨cfgacc, Relation.ReflTransGen.head hstep ?_, by simp [machine, cfgacc]⟩
    exact final_sweep_from S side a₀ a₁ cert₀ row hactive q₁ head₁
      (by simp [head₁]) hq₁ qend hend hdone

/-! ### Completeness for semantic row paths -/

private def listFn {X : Type*} {n : ℕ} (xs : List X) (h : xs.length = n + 1) :
    Fin (n + 1) → X :=
  fun k => xs.get ⟨k.val, by rw [h]; exact k.isLt⟩

private lemma ofFn_listFn {X : Type*} {n : ℕ} (xs : List X) (h : xs.length = n + 1) :
    List.ofFn (listFn xs h) = xs := by
  apply List.ext_get (by simp [h])
  intro i hi₁ hi₂
  rw [List.get_ofFn]
  unfold listFn
  apply congrArg xs.get
  apply Fin.ext
  rfl

private lemma simulate_path_from {n : ℕ} {first last : List A}
    (side : Side) (a₀ a₁ : Fin (n + 1) → Option A)
    (cert₀ : Fin (n + 1) → Option C) (row : Fin (n + 1) → A)
    (hfirst : first = List.ofFn row)
    (hactive : trackFn side a₀ a₁ = fun k => some (row k))
    (hpath : Relation.ReflTransGen S.RowStep first last) :
    ∃ (side' : Side) (a₀' a₁' : Fin (n + 1) → Option A)
      (cert' : Fin (n + 1) → Option C) (row' : Fin (n + 1) → A),
      last = List.ofFn row' ∧
      trackFn side' a₀' a₁' = (fun k => some (row' k)) ∧
      LBA.Reaches (machine S)
        ⟨.ready side, ⟨markedTape (I := I) a₀ a₁ cert₀, 0⟩⟩
        ⟨.ready side', ⟨markedTape (I := I) a₀' a₁' cert', 0⟩⟩ := by
  induction hpath with
  | refl =>
      exact ⟨side, a₀, a₁, cert₀, row, hfirst, hactive, Relation.ReflTransGen.refl⟩
  | @tail mid last hprefix hstep ih =>
      obtain ⟨side₁, a₀₁, a₁₁, cert₁, row₁, hmid, hactive₁, hreach₁⟩ := ih
      obtain ⟨certList, qend, heval, hdone⟩ := hstep
      have hlens := S.evalStep_nil_iff heval
      have hmidlen : mid.length = n + 1 := by rw [hmid, List.length_ofFn]
      have hlastlen : last.length = n + 1 := by omega
      have hcertlen : certList.length = n + 1 := by omega
      let row₂ : Fin (n + 1) → A := listFn last hlastlen
      let cert₂ : Fin (n + 1) → C := listFn certList hcertlen
      have hrow₂ : List.ofFn row₂ = last := ofFn_listFn last hlastlen
      have hcert₂ : List.ofFn cert₂ = certList := ofFn_listFn certList hcertlen
      have heval₂ : S.evalStep S.stepStart (List.ofFn row₁) (List.ofFn row₂)
          (List.ofFn cert₂) = some qend := by
        rw [← hmid, hrow₂, hcert₂]
        exact heval
      let a₀₂ : Fin (n + 1) → Option A :=
        if side₁ = .one then (fun k => some (row₂ k)) else a₀₁
      let a₁₂ : Fin (n + 1) → Option A :=
        if side₁ = .zero then (fun k => some (row₂ k)) else a₁₁
      let certOut : Fin (n + 1) → Option C := fun k => some (cert₂ k)
      have hreach₂ : LBA.Reaches (machine S)
          ⟨.ready side₁, ⟨markedTape (I := I) a₀₁ a₁₁ cert₁, 0⟩⟩
          ⟨.ready side₁.other, ⟨markedTape (I := I) a₀₂ a₁₂ certOut, 0⟩⟩ := by
        simpa [a₀₂, a₁₂, certOut] using
          simulate_step S side₁ a₀₁ a₁₁ cert₁ row₁ row₂ cert₂ hactive₁ qend heval₂ hdone
      have hactive₂ : trackFn side₁.other a₀₂ a₁₂ = fun k => some (row₂ k) := by
        cases side₁ <;> simp [a₀₂, a₁₂, trackFn, Side.other]
      exact ⟨side₁.other, a₀₂, a₁₂, certOut, row₂, hrow₂.symm, hactive₂,
        hreach₁.trans hreach₂⟩

private lemma complete_from_fin {n : ℕ} (input : Fin (n + 1) → I)
    {last : List A}
    (hpath : Relation.ReflTransGen S.RowStep
      (List.ofFn fun k => S.inputCell (input k)) last)
    (hfinal : S.Final last) :
    LBA.Accepts (machine S)
      ⟨.initFirst, ⟨fun k => some (.inl (input k)), 0⟩⟩ := by
  let row₀ : Fin (n + 1) → A := fun k => S.inputCell (input k)
  let a₀ : Fin (n + 1) → Option A := fun k => some (row₀ k)
  let a₁ : Fin (n + 1) → Option A := fun _ => none
  let cert₀ : Fin (n + 1) → Option C := fun _ => none
  obtain ⟨side, a₀', a₁', cert', row', hlast, hactive, hreach⟩ :=
    simulate_path_from S .zero a₀ a₁ cert₀ row₀ rfl rfl hpath
  have hfinal' : S.Final (List.ofFn row') := by simpa [hlast] using hfinal
  have hinit := init_reaches S input
  have hinit' : LBA.Reaches (machine S)
      ⟨.initFirst, ⟨fun k => some (.inl (input k)), 0⟩⟩
      ⟨.ready .zero, ⟨markedTape (I := I) a₀ a₁ cert₀, 0⟩⟩ := by
    simpa [a₀, a₁, cert₀, row₀] using hinit
  obtain ⟨cfgacc, hacc, hstate⟩ := simulate_final S side a₀' a₁' cert' row' hactive hfinal'
  exact ⟨cfgacc, (hinit'.trans hreach).trans hacc, hstate⟩

/-! ### Soundness infrastructure -/

private def writeTrack0 (side : Side) (a₀ : Fin (n + 1) → Option A)
    (head : Fin (n + 1)) (new : A) : Fin (n + 1) → Option A :=
  if side = .one then Function.update a₀ head (some new) else a₀

private def writeTrack1 (side : Side) (a₁ : Fin (n + 1) → Option A)
    (head : Fin (n + 1)) (new : A) : Fin (n + 1) → Option A :=
  if side = .zero then Function.update a₁ head (some new) else a₁

private def writeCert (cert : Fin (n + 1) → Option C) (head : Fin (n + 1)) (c : C) :
    Fin (n + 1) → Option C :=
  Function.update cert head (some c)

private lemma update_markedTape_write (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C)
    (head : Fin (n + 1)) (new : A) (c : C) :
    Function.update (markedTape (I := I) a₀ a₁ cert) head
      (some (.inr
        ((⟨decide (head.val = 0), decide (head.val = n), a₀ head, a₁ head,
          cert head⟩ : WorkCell A C).writeOther side new c))) =
      markedTape (I := I) (writeTrack0 side a₀ head new)
        (writeTrack1 side a₁ head new) (writeCert cert head c) := by
  simpa [writeTrack0, writeTrack1, writeCert] using
    update_markedTape (I := I) a₀ a₁ cert side head new c

private lemma trackFn_write_same (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (head : Fin (n + 1)) (new : A) :
    trackFn side (writeTrack0 side a₀ head new) (writeTrack1 side a₁ head new) =
      trackFn side a₀ a₁ := by
  cases side <;> simp [trackFn, writeTrack0, writeTrack1]

private lemma trackFn_write_other (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (head : Fin (n + 1)) (new : A) :
    trackFn side.other (writeTrack0 side a₀ head new) (writeTrack1 side a₁ head new) =
      Function.update (trackFn side.other a₀ a₁) head (some new) := by
  cases side <;> simp [trackFn, Side.other, writeTrack0, writeTrack1]

private lemma scanTape_write_take (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C)
    (head : Fin (n + 1)) (new : A) (c : C) :
    (scanTape S side (writeTrack0 side a₀ head new) (writeTrack1 side a₁ head new)
      (writeCert cert head c)).take head.val =
        (scanTape S side a₀ a₁ cert).take head.val := by
  apply List.ext_getElem
  · simp [scanTape]
  · intro i hi₁ hi₂
    have hi : i < head.val := by
      simpa [scanTape, List.length_take, Nat.min_eq_left
        (Nat.le_of_lt_succ head.isLt)] using hi₁
    have hin : i < n + 1 := by omega
    let k : Fin (n + 1) := ⟨i, hin⟩
    have hne : k ≠ head := by
      intro h
      have := congrArg Fin.val h
      simp [k] at this
      omega
    simp only [List.getElem_take, scanTape, List.getElem_ofFn]
    cases side <;>
      simp [trackFn, Side.other, writeTrack0, writeTrack1, writeCert,
        Function.update_of_ne hne, k]

private lemma scanTape_take_succ (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C)
    (head : Fin (n + 1)) :
    (scanTape S side a₀ a₁ cert).take (head.val + 1) =
      (scanTape S side a₀ a₁ cert).take head.val ++
        [(trackFn side a₀ a₁ head, trackFn side.other a₀ a₁ head, cert head)] := by
  simpa [scanTape] using take_succ_ofFn
    (fun k => (trackFn side a₀ a₁ k, trackFn side.other a₀ a₁ k, cert k)) head

private lemma scanTape_write_take_succ (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C)
    (head : Fin (n + 1)) (old new : A) (c : C)
    (hactive : trackFn side a₀ a₁ head = some old) :
    (scanTape S side (writeTrack0 side a₀ head new) (writeTrack1 side a₁ head new)
      (writeCert cert head c)).take (head.val + 1) =
        (scanTape S side a₀ a₁ cert).take head.val ++
          [(some old, some new, some c)] := by
  rw [scanTape_take_succ, scanTape_write_take]
  simp [trackFn_write_same, trackFn_write_other, writeCert, hactive]

private lemma scanTape_oldRow (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C) :
    (scanTape S side a₀ a₁ cert).filterMap (fun x => x.1) =
      optionRow (trackFn side a₀ a₁) := by
  rw [show (scanTape S side a₀ a₁ cert).filterMap (fun x => x.1) =
      ((scanTape S side a₀ a₁ cert).map (fun x => x.1)).filterMap id by
    rw [List.filterMap_map]; rfl]
  unfold scanTape optionRow
  rw [List.map_ofFn]
  apply congrArg (List.filterMap id)
  apply congrArg List.ofFn
  funext k
  rfl

private lemma scanTape_newRow (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C) :
    (scanTape S side a₀ a₁ cert).filterMap (fun x => x.2.1) =
      optionRow (trackFn side.other a₀ a₁) := by
  rw [show (scanTape S side a₀ a₁ cert).filterMap (fun x => x.2.1) =
      ((scanTape S side a₀ a₁ cert).map (fun x => x.2.1)).filterMap id by
    rw [List.filterMap_map]; rfl]
  unfold scanTape optionRow
  rw [List.map_ofFn]
  apply congrArg (List.filterMap id)
  apply congrArg List.ofFn
  funext k
  rfl

private lemma scanTape_certRow (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C) :
    (scanTape S side a₀ a₁ cert).filterMap (fun x => x.2.2) = optionRow cert := by
  rw [show (scanTape S side a₀ a₁ cert).filterMap (fun x => x.2.2) =
      ((scanTape S side a₀ a₁ cert).map (fun x => x.2.2)).filterMap id by
    rw [List.filterMap_map]; rfl]
  unfold scanTape optionRow
  rw [List.map_ofFn]
  apply congrArg (List.filterMap id)
  apply congrArg List.ofFn
  funext k
  rfl

private lemma optionRow_some {n : ℕ} (f : Fin (n + 1) → A) :
    optionRow (fun k => some (f k)) = List.ofFn f := by
  unfold optionRow
  rw [show List.ofFn (fun k => some (f k)) = (List.ofFn f).map some by
    rw [List.map_ofFn]; rfl]
  generalize List.ofFn f = xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Phase-indexed invariant for runs from a fixed nonempty input row. -/
private inductive SoundClaim {n : ℕ} (input : Fin (n + 1) → I) :
    DLBA.Cfg (TapeCell I A C) (State Q F) n → Prop
  | initFirst : SoundClaim input
      ⟨.initFirst, ⟨initTapeAt S input 0, 0⟩⟩
  | initSweep (i : ℕ) (head : Fin (n + 1))
      (hi : 1 ≤ i)
      (hhead : (head.val = i ∧ i ≤ n) ∨ (head.val = n ∧ i = n + 1)) :
      SoundClaim input ⟨.initSweep, ⟨initTapeAt S input i, head⟩⟩
  | initBack (head : Fin (n + 1)) : SoundClaim input
      ⟨.initBack,
        ⟨markedTape (I := I) (fun k => some (S.inputCell (input k)))
          (fun _ => none) (fun _ => none), head⟩⟩
  | ready (side : Side) (a₀ a₁ : Fin (n + 1) → Option A)
      (cert : Fin (n + 1) → Option C)
      (hpath : Relation.ReflTransGen S.RowStep
        (List.ofFn fun k => S.inputCell (input k))
        (optionRow (trackFn side a₀ a₁))) :
      SoundClaim input ⟨.ready side, ⟨markedTape (I := I) a₀ a₁ cert, 0⟩⟩
  | step (side : Side) (q : Q) (a₀ a₁ : Fin (n + 1) → Option A)
      (cert : Fin (n + 1) → Option C) (head : Fin (n + 1))
      (hpath : Relation.ReflTransGen S.RowStep
        (List.ofFn fun k => S.inputCell (input k))
        (optionRow (trackFn side a₀ a₁)))
      (hscan : scanOptions S S.stepStart
        ((scanTape S side a₀ a₁ cert).take head.val) = some q) :
      SoundClaim input ⟨.step side q, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩
  | final (side : Side) (q : F) (a₀ a₁ : Fin (n + 1) → Option A)
      (cert : Fin (n + 1) → Option C) (head : Fin (n + 1))
      (hpath : Relation.ReflTransGen S.RowStep
        (List.ofFn fun k => S.inputCell (input k))
        (optionRow (trackFn side a₀ a₁)))
      (hscan : scanFinalOptions S S.finalStart
        ((List.ofFn (trackFn side a₀ a₁)).take head.val) = some q) :
      SoundClaim input ⟨.final side q, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩
  | back (side : Side) (a₀ a₁ : Fin (n + 1) → Option A)
      (cert : Fin (n + 1) → Option C) (head : Fin (n + 1))
      (hpath : Relation.ReflTransGen S.RowStep
        (List.ofFn fun k => S.inputCell (input k))
        (optionRow (trackFn side.other a₀ a₁))) :
      SoundClaim input ⟨.back side, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩
  | accept (side : Side) (a₀ a₁ : Fin (n + 1) → Option A)
      (cert : Fin (n + 1) → Option C) (head : Fin (n + 1))
      (hpath : Relation.ReflTransGen S.RowStep
        (List.ofFn fun k => S.inputCell (input k))
        (optionRow (trackFn side a₀ a₁)))
      (hfinal : S.Final (optionRow (trackFn side a₀ a₁))) :
      SoundClaim input ⟨.accept, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩

private lemma sound_initFirst_step {n : ℕ} (input : Fin (n + 1) → I)
    {cfg' : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    (hstep : LBA.Step (machine S)
      ⟨.initFirst, ⟨initTapeAt S input 0, 0⟩⟩ cfg') :
    SoundClaim S input cfg' := by
  obtain ⟨q', sym, dir, hmem, rfl⟩ := hstep
  simp only [machine, DLBA.BoundedTape.read] at hmem
  simp [initTapeAt, transition] at hmem
  obtain ⟨rfl, rfl, rfl⟩ := hmem
  have hupd : Function.update (initTapeAt S input 0) (0 : Fin (n + 1))
      (some (.inr (inputWorkCell S true (input 0)))) = initTapeAt S input 1 := by
    simpa [tmpCell] using initTapeAt_update S input (0 : Fin (n + 1))
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hupd]
  by_cases hn : 0 < n
  · rw [dif_pos (by simpa using hn)]
    exact SoundClaim.initSweep 1 ⟨1, by omega⟩ (by omega) (Or.inl ⟨rfl, by omega⟩)
  · rw [dif_neg (by simpa using hn)]
    have hn0 : n = 0 := by omega
    subst n
    exact SoundClaim.initSweep 1 0 (by omega) (Or.inr ⟨rfl, rfl⟩)

private lemma sound_initSweep_step {n : ℕ} (input : Fin (n + 1) → I)
    (i : ℕ) (head : Fin (n + 1)) (hi : 1 ≤ i)
    (hhead : (head.val = i ∧ i ≤ n) ∨ (head.val = n ∧ i = n + 1))
    {cfg' : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    (hstep : LBA.Step (machine S)
      ⟨.initSweep, ⟨initTapeAt S input i, head⟩⟩ cfg') :
    SoundClaim S input cfg' := by
  obtain ⟨q', sym, dir, hmem, rfl⟩ := hstep
  simp only [machine, DLBA.BoundedTape.read] at hmem
  rcases hhead with ⟨hhi, hin⟩ | ⟨hhn, hin⟩
  · have hcell : initTapeAt S input i head = some (.inl (input head)) := by
      simp [initTapeAt, hhi]
    rw [hcell, transition] at hmem
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hout : some (.inr (inputWorkCell S false (input head))) = tmpCell S input head := by
      simp [tmpCell, inputWorkCell, show head.val ≠ 0 by omega]
    have hupd : Function.update (initTapeAt S input i) head
        (some (.inr (inputWorkCell S false (input head)))) =
          initTapeAt S input (i + 1) := by
      rw [hout, ← hhi]
      exact initTapeAt_update S input head
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hupd]
    by_cases hlt : head.val < n
    · rw [dif_pos hlt]
      exact SoundClaim.initSweep (i + 1) ⟨head.val + 1, by omega⟩ (by omega)
        (Or.inl ⟨by simp; omega, by omega⟩)
    · rw [dif_neg hlt]
      exact SoundClaim.initSweep (i + 1) head (by omega)
        (Or.inr ⟨by omega, by omega⟩)
  · have hcell : initTapeAt S input i head =
        some (.inr
          ⟨decide (head.val = 0), false, some (S.inputCell (input head)), none, none⟩) := by
      simp [initTapeAt, tmpCell, inputWorkCell]
      omega
    rw [hcell, transition] at hmem
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hc : Function.update (initTapeAt S input i) head
        (some (.inr
          ⟨decide (head.val = 0), true, some (S.inputCell (input head)), none, none⟩)) =
      markedTape (I := I) (fun k => some (S.inputCell (input k)))
        (fun _ => none) (fun _ => none) := by
      funext k
      simp only [Function.update_apply]
      by_cases hk : k = head
      · subst k
        simp [markedTape, markedCell]
        omega
      · rw [if_neg hk]
        have hkn : k.val ≠ n := fun h => hk (Fin.ext (h.trans hhn.symm))
        have hkle : k.val ≤ n := Nat.le_of_lt_succ k.isLt
        simp [initTapeAt, tmpCell, inputWorkCell, markedTape, markedCell, hin, hkn]
        omega
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hc]
    exact SoundClaim.initBack _

private lemma sound_initBack_step {n : ℕ} (input : Fin (n + 1) → I)
    (head : Fin (n + 1))
    {cfg' : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    (hstep : LBA.Step (machine S)
      ⟨.initBack,
        ⟨markedTape (I := I) (fun k => some (S.inputCell (input k)))
          (fun _ => none) (fun _ => none), head⟩⟩ cfg') :
    SoundClaim S input cfg' := by
  obtain ⟨q', sym, dir, hmem, rfl⟩ := hstep
  simp only [machine, DLBA.BoundedTape.read] at hmem
  by_cases hzero : head.val = 0
  · simp [markedTape, markedCell, transition, hzero] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hhead : head = 0 := Fin.ext (by simpa using hzero)
    subst head
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    rw [show some (.inr
          ⟨true, decide (0 = n), some (S.inputCell (input 0)), none, none⟩) =
        markedTape (I := I) (fun k => some (S.inputCell (input k)))
          (fun _ => none) (fun _ => none) 0 by
      simp [markedTape, markedCell], Function.update_eq_self]
    apply SoundClaim.ready
    simpa [trackFn, optionRow_some] using
      (Relation.ReflTransGen.refl : Relation.ReflTransGen S.RowStep
        (List.ofFn fun k => S.inputCell (input k))
        (List.ofFn fun k => S.inputCell (input k)))
  · simp [markedTape, markedCell, transition, hzero] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hpos : 0 < head.val := by omega
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    rw [show some (.inr
          ⟨false, decide (head.val = n), some (S.inputCell (input head)), none, none⟩) =
        markedTape (I := I) (fun k => some (S.inputCell (input k)))
          (fun _ => none) (fun _ => none) head by
      simp [markedTape, markedCell, hzero], Function.update_eq_self, dif_pos hpos]
    exact SoundClaim.initBack ⟨head.val - 1, by omega⟩

private lemma rowStep_of_full_scan {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (cert : Fin (n + 1) → Option C)
    (q : Q) (hscan : scanOptions S S.stepStart (scanTape S side a₀ a₁ cert) = some q)
    (hdone : S.stepDone q = true) :
    S.RowStep (optionRow (trackFn side a₀ a₁))
      (optionRow (trackFn side.other a₀ a₁)) := by
  refine ⟨optionRow cert, q, ?_, hdone⟩
  have heval := scanOptions_sound S hscan
  simpa [scanTape_oldRow, scanTape_newRow, scanTape_certRow] using heval

private lemma final_of_full_scan {n : ℕ} (side : Side)
    (a₀ a₁ : Fin (n + 1) → Option A) (q : F)
    (hscan : scanFinalOptions S S.finalStart (List.ofFn (trackFn side a₀ a₁)) = some q)
    (hdone : S.finalDone q = true) :
    S.Final (optionRow (trackFn side a₀ a₁)) := by
  have heval := scanFinalOptions_sound S hscan
  unfold Final optionRow
  rw [heval]
  exact hdone

private lemma sound_ready_step {n : ℕ} (input : Fin (n + 1) → I)
    (side : Side) (a₀ a₁ : Fin (n + 1) → Option A)
    (cert : Fin (n + 1) → Option C)
    (hpath : Relation.ReflTransGen S.RowStep
      (List.ofFn fun k => S.inputCell (input k))
      (optionRow (trackFn side a₀ a₁)))
    {cfg' : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    (hstep : LBA.Step (machine S)
      ⟨.ready side, ⟨markedTape (I := I) a₀ a₁ cert, 0⟩⟩ cfg') :
    SoundClaim S input cfg' := by
  obtain ⟨q', sym, dir, hmem, rfl⟩ := hstep
  simp only [machine, DLBA.BoundedTape.read] at hmem
  simp only [markedTape, markedCell, Fin.val_zero, transition] at hmem
  rw [if_pos (by simp)] at hmem
  rcases hmem with hchoice | hfinal
  · simp only [stepChoices, Set.mem_setOf_eq] at hchoice
    obtain ⟨old, new, c, hactiveCell, hout⟩ := hchoice
    have hactive0 : trackFn side a₀ a₁ 0 = some old := by
      cases side <;> simpa [WorkCell.track, trackFn] using hactiveCell
    let a₀' := writeTrack0 side a₀ (0 : Fin (n + 1)) new
    let a₁' := writeTrack1 side a₁ (0 : Fin (n + 1)) new
    let cert' := writeCert cert (0 : Fin (n + 1)) c
    let qnew := S.stepCell S.stepStart old new c
    have hscanPrefix : scanOptions S S.stepStart
        ((scanTape S side a₀' a₁' cert').take 1) = some qnew := by
      have ht := scanTape_write_take_succ S side a₀ a₁ cert
        (0 : Fin (n + 1)) old new c hactive0
      rw [show (scanTape S side a₀' a₁' cert').take 1 =
          (scanTape S side a₀ a₁ cert).take 0 ++ [(some old, some new, some c)] by
        simpa [a₀', a₁', cert'] using ht]
      simp [scanOptions, scanSymbol, qnew]
    by_cases hn : n = 0
    · subst n
      rw [if_pos (by simp)] at hout
      obtain ⟨hdone, hout⟩ := hout
      simp only [Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl, rfl⟩ := hout
      have hfull : (scanTape S side a₀' a₁' cert').take 1 =
          scanTape S side a₀' a₁' cert' := by
        apply (List.take_eq_self_iff _).2
        simp [scanTape]
      have hscan : scanOptions S S.stepStart (scanTape S side a₀' a₁' cert') =
          some qnew := by rw [← hfull]; exact hscanPrefix
      have hrow := rowStep_of_full_scan S side a₀' a₁' cert' qnew hscan hdone
      simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      have hu : Function.update (markedTape (I := I) a₀ a₁ cert) 0
          (some (.inr
            ((⟨decide True, decide True, a₀ 0, a₁ 0, cert 0⟩ : WorkCell A C).writeOther
              side new c))) = markedTape (I := I) a₀' a₁' cert' := by
        simpa [a₀', a₁', cert'] using
          update_markedTape_write (I := I) side a₀ a₁ cert (0 : Fin 1) new c
      rw [hu]
      rw [dif_neg (by simp : ¬ (0 : Fin 1).val > 0)]
      have hsame : trackFn side a₀' a₁' = trackFn side a₀ a₁ := by
        simpa [a₀', a₁'] using
          trackFn_write_same (A := A) side a₀ a₁ (0 : Fin 1) new
      rw [hsame] at hrow
      exact SoundClaim.back side a₀' a₁' cert' 0 (hpath.tail hrow)
    · have h0n : 0 ≠ n := Ne.symm hn
      rw [if_neg (by simp [h0n])] at hout
      simp only [Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl, rfl⟩ := hout
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      have hu : Function.update (markedTape (I := I) a₀ a₁ cert) 0
          (some (.inr
            ((⟨decide True, decide (0 = n), a₀ 0, a₁ 0, cert 0⟩ : WorkCell A C).writeOther
              side new c))) = markedTape (I := I) a₀' a₁' cert' := by
        simpa [a₀', a₁', cert'] using
          update_markedTape_write (I := I) side a₀ a₁ cert (0 : Fin (n + 1)) new c
      rw [hu, dif_pos (by simpa using hnpos)]
      have hsame : trackFn side a₀' a₁' = trackFn side a₀ a₁ := by
        simpa [a₀', a₁'] using
          trackFn_write_same (A := A) side a₀ a₁ (0 : Fin (n + 1)) new
      exact SoundClaim.step side qnew a₀' a₁' cert' ⟨1, by omega⟩
        (by rw [hsame]; exact hpath)
        (by simpa [a₀', a₁', cert'] using hscanPrefix)
  · cases ha : trackFn side a₀ a₁ 0 with
    | none =>
        have hw : WorkCell.track side
            ⟨decide True, decide (0 = n), a₀ 0, a₁ 0, cert 0⟩ = none := by
          calc
            _ = trackFn side a₀ a₁ 0 := by cases side <;> rfl
            _ = none := ha
        rw [finalChoice, hw] at hfinal
        simp at hfinal
    | some old =>
        let qnew := S.finalCell S.finalStart old
        have hscanPrefix : scanFinalOptions S S.finalStart
            ((List.ofFn (trackFn side a₀ a₁)).take 1) = some qnew := by
          rw [show (List.ofFn (trackFn side a₀ a₁)).take 1 =
              (List.ofFn (trackFn side a₀ a₁)).take 0 ++ [some old] by
            simp [ha]]
          simp [scanFinalOptions, ha, qnew]
        by_cases hn : n = 0
        · subst n
          have hw : WorkCell.track side
              ⟨decide True, decide (0 = 0), a₀ 0, a₁ 0, cert 0⟩ = some old := by
            calc
              _ = trackFn side a₀ a₁ 0 := by cases side <;> rfl
              _ = some old := ha
          rw [finalChoice, hw] at hfinal
          have hdone : S.finalDone qnew = true := by
            by_contra hne
            simp [qnew, hne] at hfinal
          simp [qnew, hdone] at hfinal
          obtain ⟨rfl, rfl, rfl⟩ := hfinal
          have hfull : (List.ofFn (trackFn side a₀ a₁)).take 1 =
              List.ofFn (trackFn side a₀ a₁) := by
            apply (List.take_eq_self_iff _).2
            simp
          have hscan : scanFinalOptions S S.finalStart
              (List.ofFn (trackFn side a₀ a₁)) = some qnew := by
            rw [← hfull]; exact hscanPrefix
          have hfin := final_of_full_scan S side a₀ a₁ qnew hscan hdone
          simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
          have hu : Function.update (markedTape (I := I) a₀ a₁ cert) 0
              (some (.inr ⟨true, true, a₀ 0, a₁ 0, cert 0⟩)) =
                markedTape (I := I) a₀ a₁ cert := by
            rw [show some (.inr ⟨true, true, a₀ 0, a₁ 0, cert 0⟩) =
                markedTape (I := I) a₀ a₁ cert 0 by simp [markedTape, markedCell],
              Function.update_eq_self]
          rw [hu]
          exact SoundClaim.accept side a₀ a₁ cert 0 hpath hfin
        · have h0n : 0 ≠ n := Ne.symm hn
          have hw : WorkCell.track side
              ⟨decide True, decide (0 = n), a₀ 0, a₁ 0, cert 0⟩ = some old := by
            calc
              _ = trackFn side a₀ a₁ 0 := by cases side <;> rfl
              _ = some old := ha
          rw [finalChoice, hw] at hfinal
          simp [h0n] at hfinal
          obtain ⟨rfl, rfl, rfl⟩ := hfinal
          have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
          have hu : Function.update (markedTape (I := I) a₀ a₁ cert) 0
              (some (.inr ⟨true, false, a₀ 0, a₁ 0, cert 0⟩)) =
                markedTape (I := I) a₀ a₁ cert := by
            rw [show some (.inr ⟨true, false, a₀ 0, a₁ 0, cert 0⟩) =
                markedTape (I := I) a₀ a₁ cert 0 by
              simp [markedTape, markedCell, h0n], Function.update_eq_self]
          rw [hu, dif_pos (by simpa using hnpos)]
          exact SoundClaim.final side qnew a₀ a₁ cert ⟨1, by omega⟩ hpath
            (by simpa using hscanPrefix)

private lemma sound_step_step {n : ℕ} (input : Fin (n + 1) → I)
    (side : Side) (q : Q) (a₀ a₁ : Fin (n + 1) → Option A)
    (cert : Fin (n + 1) → Option C) (head : Fin (n + 1))
    (hpath : Relation.ReflTransGen S.RowStep
      (List.ofFn fun k => S.inputCell (input k))
      (optionRow (trackFn side a₀ a₁)))
    (hscan : scanOptions S S.stepStart
      ((scanTape S side a₀ a₁ cert).take head.val) = some q)
    {cfg' : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    (hstep : LBA.Step (machine S)
      ⟨.step side q, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩ cfg') :
    SoundClaim S input cfg' := by
  obtain ⟨q', sym, dir, hmem, rfl⟩ := hstep
  simp only [machine, DLBA.BoundedTape.read, markedTape, markedCell, transition] at hmem
  simp only [stepChoices, Set.mem_setOf_eq] at hmem
  obtain ⟨old, new, c, hactiveCell, hout⟩ := hmem
  have hactive : trackFn side a₀ a₁ head = some old := by
    cases side <;> simpa [WorkCell.track, trackFn] using hactiveCell
  let a₀' := writeTrack0 side a₀ head new
  let a₁' := writeTrack1 side a₁ head new
  let cert' := writeCert cert head c
  let qnew := S.stepCell q old new c
  have hscan' : scanOptions S S.stepStart
      ((scanTape S side a₀' a₁' cert').take (head.val + 1)) = some qnew := by
    have ht := scanTape_write_take_succ S side a₀ a₁ cert head old new c hactive
    rw [show (scanTape S side a₀' a₁' cert').take (head.val + 1) =
        (scanTape S side a₀ a₁ cert).take head.val ++ [(some old, some new, some c)] by
      simpa [a₀', a₁', cert'] using ht]
    exact scanOptions_append_some S hscan old new c
  by_cases hlast : head.val = n
  · rw [if_pos (by simp [hlast])] at hout
    obtain ⟨hdone, hout⟩ := hout
    simp only [Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl, rfl⟩ := hout
    have hfull : (scanTape S side a₀' a₁' cert').take (head.val + 1) =
        scanTape S side a₀' a₁' cert' := by
      apply (List.take_eq_self_iff _).2
      simp [scanTape, hlast]
    have hscanFull : scanOptions S S.stepStart (scanTape S side a₀' a₁' cert') =
        some qnew := by rw [← hfull]; exact hscan'
    have hrow := rowStep_of_full_scan S side a₀' a₁' cert' qnew hscanFull hdone
    have hsame : trackFn side a₀' a₁' = trackFn side a₀ a₁ := by
      simpa [a₀', a₁'] using trackFn_write_same (A := A) side a₀ a₁ head new
    rw [hsame] at hrow
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    have hu : Function.update (markedTape (I := I) a₀ a₁ cert) head
        (some (.inr
          ((⟨decide (head.val = 0), decide (head.val = n), a₀ head, a₁ head,
            cert head⟩ : WorkCell A C).writeOther side new c))) =
          markedTape (I := I) a₀' a₁' cert' := by
      simpa [a₀', a₁', cert'] using
        update_markedTape_write (I := I) side a₀ a₁ cert head new c
    rw [hu]
    by_cases hpos : 0 < head.val
    · rw [dif_pos hpos]
      exact SoundClaim.back side a₀' a₁' cert' ⟨head.val - 1, by omega⟩
        (hpath.tail hrow)
    · rw [dif_neg hpos]
      exact SoundClaim.back side a₀' a₁' cert' head (hpath.tail hrow)
  · have hlt : head.val < n := by have := head.isLt; omega
    rw [if_neg (by simp [hlast])] at hout
    simp only [Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl, rfl⟩ := hout
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    have hu : Function.update (markedTape (I := I) a₀ a₁ cert) head
        (some (.inr
          ((⟨decide (head.val = 0), decide (head.val = n), a₀ head, a₁ head,
            cert head⟩ : WorkCell A C).writeOther side new c))) =
          markedTape (I := I) a₀' a₁' cert' := by
      simpa [a₀', a₁', cert'] using
        update_markedTape_write (I := I) side a₀ a₁ cert head new c
    rw [hu, dif_pos hlt]
    have hsame : trackFn side a₀' a₁' = trackFn side a₀ a₁ := by
      simpa [a₀', a₁'] using trackFn_write_same (A := A) side a₀ a₁ head new
    exact SoundClaim.step side qnew a₀' a₁' cert' ⟨head.val + 1, by omega⟩
      (by rw [hsame]; exact hpath) (by simpa using hscan')

private lemma sound_final_step {n : ℕ} (input : Fin (n + 1) → I)
    (side : Side) (q : F) (a₀ a₁ : Fin (n + 1) → Option A)
    (cert : Fin (n + 1) → Option C) (head : Fin (n + 1))
    (hpath : Relation.ReflTransGen S.RowStep
      (List.ofFn fun k => S.inputCell (input k))
      (optionRow (trackFn side a₀ a₁)))
    (hscan : scanFinalOptions S S.finalStart
      ((List.ofFn (trackFn side a₀ a₁)).take head.val) = some q)
    {cfg' : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    (hstep : LBA.Step (machine S)
      ⟨.final side q, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩ cfg') :
    SoundClaim S input cfg' := by
  obtain ⟨q', sym, dir, hmem, rfl⟩ := hstep
  simp only [machine, DLBA.BoundedTape.read, markedTape, markedCell, transition] at hmem
  cases ha : trackFn side a₀ a₁ head with
  | none =>
      have hw : WorkCell.track side
          ⟨decide (head.val = 0), decide (head.val = n), a₀ head, a₁ head, cert head⟩ = none := by
        calc
          _ = trackFn side a₀ a₁ head := by cases side <;> rfl
          _ = none := ha
      rw [finalChoice, hw] at hmem
      simp at hmem
  | some old =>
      have hw : WorkCell.track side
          ⟨decide (head.val = 0), decide (head.val = n), a₀ head, a₁ head, cert head⟩ =
            some old := by
        calc
          _ = trackFn side a₀ a₁ head := by cases side <;> rfl
          _ = some old := ha
      rw [finalChoice, hw] at hmem
      let qnew := S.finalCell q old
      have hscan' : scanFinalOptions S S.finalStart
          ((List.ofFn (trackFn side a₀ a₁)).take (head.val + 1)) = some qnew := by
        have ht := take_succ_ofFn (trackFn side a₀ a₁) head
        rw [ht, ha]
        exact scanFinalOptions_append_some S hscan old
      by_cases hlast : head.val = n
      · have hdone : S.finalDone qnew = true := by
          by_contra hne
          simp [hlast, qnew, hne] at hmem
        simp [hlast, qnew, hdone] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        have hfull : (List.ofFn (trackFn side a₀ a₁)).take (head.val + 1) =
            List.ofFn (trackFn side a₀ a₁) := by
          apply (List.take_eq_self_iff _).2
          simp [hlast]
        have hscanFull : scanFinalOptions S S.finalStart
            (List.ofFn (trackFn side a₀ a₁)) = some qnew := by
          rw [← hfull]; exact hscan'
        have hfin := final_of_full_scan S side a₀ a₁ qnew hscanFull hdone
        simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        have hu : Function.update (markedTape (I := I) a₀ a₁ cert) head
            (some (.inr
              ⟨decide (n = 0), true, a₀ head, a₁ head, cert head⟩)) =
                markedTape (I := I) a₀ a₁ cert := by
          rw [show some (.inr
                ⟨decide (n = 0), true, a₀ head, a₁ head, cert head⟩) =
              markedTape (I := I) a₀ a₁ cert head by
            simp [markedTape, markedCell, hlast], Function.update_eq_self]
        rw [hu]
        exact SoundClaim.accept side a₀ a₁ cert head hpath hfin
      · have hlt : head.val < n := by have := head.isLt; omega
        simp [hlast] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        have hu : Function.update (markedTape (I := I) a₀ a₁ cert) head
            (some (.inr
              ⟨decide (head = 0), false, a₀ head, a₁ head, cert head⟩)) =
                markedTape (I := I) a₀ a₁ cert := by
          rw [show some (.inr
                ⟨decide (head = 0), false, a₀ head, a₁ head, cert head⟩) =
              markedTape (I := I) a₀ a₁ cert head by
            simp [markedTape, markedCell, hlast], Function.update_eq_self]
        rw [hu, dif_pos hlt]
        exact SoundClaim.final side qnew a₀ a₁ cert ⟨head.val + 1, by omega⟩ hpath
          (by simpa using hscan')

private lemma sound_back_step {n : ℕ} (input : Fin (n + 1) → I)
    (side : Side) (a₀ a₁ : Fin (n + 1) → Option A)
    (cert : Fin (n + 1) → Option C) (head : Fin (n + 1))
    (hpath : Relation.ReflTransGen S.RowStep
      (List.ofFn fun k => S.inputCell (input k))
      (optionRow (trackFn side.other a₀ a₁)))
    {cfg' : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    (hstep : LBA.Step (machine S)
      ⟨.back side, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩ cfg') :
    SoundClaim S input cfg' := by
  obtain ⟨q', sym, dir, hmem, rfl⟩ := hstep
  simp only [machine, DLBA.BoundedTape.read] at hmem
  by_cases hzero : head.val = 0
  · simp [markedTape, markedCell, transition, hzero] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hhead : head = 0 := Fin.ext (by simpa using hzero)
    subst head
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    have hu : Function.update (markedTape (I := I) a₀ a₁ cert) 0
        (some (.inr ⟨true, decide (0 = n), a₀ 0, a₁ 0, cert 0⟩)) =
          markedTape (I := I) a₀ a₁ cert := by
      rw [show some (.inr ⟨true, decide (0 = n), a₀ 0, a₁ 0, cert 0⟩) =
          markedTape (I := I) a₀ a₁ cert 0 by simp [markedTape, markedCell],
        Function.update_eq_self]
    rw [hu]
    exact SoundClaim.ready side.other a₀ a₁ cert hpath
  · simp [markedTape, markedCell, transition, hzero] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    have hpos : 0 < head.val := by omega
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    have hu : Function.update (markedTape (I := I) a₀ a₁ cert) head
        (some (.inr ⟨false, decide (head.val = n), a₀ head, a₁ head, cert head⟩)) =
          markedTape (I := I) a₀ a₁ cert := by
      rw [show some (.inr
            ⟨false, decide (head.val = n), a₀ head, a₁ head, cert head⟩) =
          markedTape (I := I) a₀ a₁ cert head by
        simp [markedTape, markedCell, hzero], Function.update_eq_self]
    rw [hu, dif_pos hpos]
    exact SoundClaim.back side a₀ a₁ cert ⟨head.val - 1, by omega⟩ hpath

private lemma sound_accept_step {n : ℕ} (input : Fin (n + 1) → I)
    (_side : Side) (a₀ a₁ : Fin (n + 1) → Option A)
    (cert : Fin (n + 1) → Option C) (head : Fin (n + 1))
    {cfg' : DLBA.Cfg (TapeCell I A C) (State Q F) n}
    (hstep : LBA.Step (machine S)
      ⟨.accept, ⟨markedTape (I := I) a₀ a₁ cert, head⟩⟩ cfg') :
    SoundClaim S input cfg' := by
  obtain ⟨q', sym, dir, hmem, -⟩ := hstep
  simp [machine, transition, DLBA.BoundedTape.read] at hmem

private lemma sound_invariant {n : ℕ} (input : Fin (n + 1) → I)
    (cfg : DLBA.Cfg (TapeCell I A C) (State Q F) n)
    (hreach : LBA.Reaches (machine S)
      ⟨.initFirst, ⟨initTapeAt S input 0, 0⟩⟩ cfg) :
    SoundClaim S input cfg := by
  induction hreach with
  | refl => exact SoundClaim.initFirst
  | @tail cfg₁ cfg₂ hreach hstep ih =>
      cases ih with
      | initFirst => exact sound_initFirst_step S input hstep
      | initSweep i head hi hhead =>
          exact sound_initSweep_step S input i head hi hhead hstep
      | initBack head => exact sound_initBack_step S input head hstep
      | ready side a₀ a₁ cert hpath =>
          exact sound_ready_step S input side a₀ a₁ cert hpath hstep
      | step side q a₀ a₁ cert head hpath hscan =>
          exact sound_step_step S input side q a₀ a₁ cert head hpath hscan hstep
      | final side q a₀ a₁ cert head hpath hscan =>
          exact sound_final_step S input side q a₀ a₁ cert head hpath hscan hstep
      | back side a₀ a₁ cert head hpath =>
          exact sound_back_step S input side a₀ a₁ cert head hpath hstep
      | accept side a₀ a₁ cert head hpath hfinal =>
          exact sound_accept_step S input side a₀ a₁ cert head hstep

private lemma sound_from_fin {n : ℕ} (input : Fin (n + 1) → I)
    (hacc : LBA.Accepts (machine S)
      ⟨.initFirst, ⟨fun k => some (.inl (input k)), 0⟩⟩) :
    ∃ row, Relation.ReflTransGen S.RowStep
      (List.ofFn fun k => S.inputCell (input k)) row ∧ S.Final row := by
  obtain ⟨cfgacc, hreach, haccept⟩ := hacc
  have hraw : (fun k => some (.inl (input k)) : Fin (n + 1) → TapeCell I A C) =
      initTapeAt S input 0 := by funext k; simp [initTapeAt]
  rw [hraw] at hreach
  have hclaim := sound_invariant S input cfgacc hreach
  have hstate : cfgacc.state = State.accept :=
    (machine_accept_iff S cfgacc.state).1 haccept
  cases hclaim with
  | initFirst => simp at hstate
  | initSweep => simp at hstate
  | initBack => simp at hstate
  | ready => simp at hstate
  | step => simp at hstate
  | final => simp at hstate
  | back => simp at hstate
  | accept side a₀ a₁ cert head hpath hfinal =>
      exact ⟨optionRow (trackFn side a₀ a₁), hpath, hfinal⟩

/-! ## Correctness and the public compiler theorem -/

private theorem machine_language_eq
    [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype Q] [DecidableEq Q]
    [Fintype F] [DecidableEq F] :
    LBA.LanguageViaEmbed (machine S) (fun i => some (.inl i)) = S.rowReachLanguage := by
  funext w
  apply propext
  constructor
  · rintro ⟨hne, hacc⟩
    have hwne : w ≠ [] := by
      intro hw
      subst w
      simp at hne
    set L := w.map (fun i => (some (.inl i) : TapeCell I A C)) with hL
    have hLlen : L.length = w.length := by simp [hL]
    have hLpos : 0 < L.length := List.length_pos_of_ne_nil hne
    set n := L.length - 1 with hn
    have hn1 : n + 1 = w.length := by omega
    have hbound : ∀ k : Fin (n + 1), k.val < w.length := fun k => by
      have := k.isLt; omega
    let input : Fin (n + 1) → I := fun k => w.get ⟨k.val, hbound k⟩
    have htape : (LBA.loadList L hne).contents =
        (fun k => some (.inl (input k)) : Fin (n + 1) → TapeCell I A C) := by
      funext k
      simp [LBA.loadList, hL, input, List.get_eq_getElem]
    have hbridge : LBA.initCfgList (machine S) L hne =
        (⟨State.initFirst, ⟨fun k => some (.inl (input k)), 0⟩⟩ :
          DLBA.Cfg (TapeCell I A C) (State Q F) n) := by
      exact cfg_eq rfl htape (Fin.ext (by simp))
    rw [hbridge] at hacc
    obtain ⟨row, hpath, hfinal⟩ := sound_from_fin S input hacc
    have hinput : List.ofFn input = w := by
      have hwlen : w.length = n + 1 := hn1.symm
      rw [show input = listFn w hwlen by
        funext k
        apply congrArg w.get
        apply Fin.ext
        rfl]
      exact ofFn_listFn w hwlen
    have hstart : List.ofFn (fun k => S.inputCell (input k)) = w.map S.inputCell := by
      change List.ofFn (S.inputCell ∘ input) = _
      rw [← List.map_ofFn, hinput]
    rw [hstart] at hpath
    exact ⟨hwne, row, hpath, hfinal⟩
  · rintro ⟨hwne, row, hpath, hfinal⟩
    have hne : w.map (fun i => (some (.inl i) : TapeCell I A C)) ≠ [] := by
      simpa using hwne
    refine ⟨hne, ?_⟩
    set L := w.map (fun i => (some (.inl i) : TapeCell I A C)) with hL
    have hLlen : L.length = w.length := by simp [hL]
    have hLpos : 0 < L.length := List.length_pos_of_ne_nil hne
    set n := L.length - 1 with hn
    have hn1 : n + 1 = w.length := by omega
    have hbound : ∀ k : Fin (n + 1), k.val < w.length := fun k => by
      have := k.isLt; omega
    let input : Fin (n + 1) → I := fun k => w.get ⟨k.val, hbound k⟩
    have hinput : List.ofFn input = w := by
      have hwlen : w.length = n + 1 := hn1.symm
      rw [show input = listFn w hwlen by
        funext k
        apply congrArg w.get
        apply Fin.ext
        rfl]
      exact ofFn_listFn w hwlen
    have hstart : List.ofFn (fun k => S.inputCell (input k)) = w.map S.inputCell := by
      change List.ofFn (S.inputCell ∘ input) = _
      rw [← List.map_ofFn, hinput]
    rw [← hstart] at hpath
    have hcomplete := complete_from_fin S input (last := row)
      hpath hfinal
    have htape : (LBA.loadList L hne).contents =
        (fun k => some (.inl (input k)) : Fin (n + 1) → TapeCell I A C) := by
      funext k
      simp [LBA.loadList, hL, input, List.get_eq_getElem]
    have hbridge : LBA.initCfgList (machine S) L hne =
        (⟨State.initFirst, ⟨fun k => some (.inl (input k)), 0⟩⟩ :
          DLBA.Cfg (TapeCell I A C) (State Q F) n) := by
      exact cfg_eq rfl htape (Fin.ext (by simp))
    have hbridge' : LBA.initCfgList (machine S)
        (w.map (fun i => (some (.inl i) : TapeCell I A C))) hne =
        (⟨State.initFirst, ⟨fun k => some (.inl (input k)), 0⟩⟩ :
          DLBA.Cfg (TapeCell I A C) (State Q F) n) := by
      simpa [hL] using hbridge
    rw [hbridge']
    exact hcomplete

/-- Every finite certified row system is recognized by an input-sized nondeterministic LBA. -/
public theorem is_LBA_pos_rowReachLanguage
    {I₀ A₀ C₀ Q₀ F₀ : Type} (S₀ : CertifiedRowSystem I₀ A₀ C₀ Q₀ F₀)
    [Fintype I₀] [DecidableEq I₀] [Fintype A₀] [DecidableEq A₀]
    [Fintype C₀] [DecidableEq C₀] [Fintype Q₀] [DecidableEq Q₀]
    [Fintype F₀] [DecidableEq F₀] :
    is_LBA_pos S₀.rowReachLanguage := by
  refine ⟨WorkCell A₀ C₀, State Q₀ F₀, inferInstance, inferInstance, inferInstance,
    inferInstance, machine S₀, ?_⟩
  exact machine_language_eq S₀

end CertifiedRowSystem
