module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Utilities.ClosurePredicates
public import Mathlib.Computability.DFA
import Mathlib.Tactic

@[expose]
public section

/-!
# Context-Sensitive Languages Are Closed Under Intersection With Regular Languages

The construction works at the LBA level.  Before simulating the LBA for the
context-sensitive language, a finite-control scan evaluates a DFA on the untouched input.
If the DFA rejects there is no successor computation.  If it accepts, the machine rewinds to
the left endmarker and starts the original LBA on exactly its original initial tape.
-/

namespace CSIntersectionRegular

open LBA Classical

variable {T Γ Λ Q : Type*}

private inductive InterState (Q Λ : Type*) where
  | scan : Q → InterState Q Λ
  | rewind : InterState Q Λ
  | run : Λ → InterState Q Λ
deriving Fintype, DecidableEq

private noncomputable def interTransition (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) :
    InterState Q Λ → LBA.EndAlpha T Γ →
      Set (InterState Q Λ × LBA.EndAlpha T Γ × DLBA.Dir)
  | .scan q, .inr false => {(.scan q, LBA.leftMark, .right)}
  | .scan q, .inl (some (.inl a)) =>
      {(.scan (D.step q a), .inl (some (.inl a)), .right)}
  | .scan q, .inr true =>
      if q ∈ D.accept then {(.rewind, LBA.rightMark, .left)} else ∅
  | .scan _, .inl _ => ∅
  | .rewind, .inr false => {(.run M.initial, LBA.leftMark, .stay)}
  | .rewind, a => {(.rewind, a, .left)}
  | .run q, a => {x | ∃ p ∈ M.transition q a, x = (.run p.1, p.2.1, p.2.2)}

private noncomputable def interMachine (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) :
    LBA.Machine (LBA.EndAlpha T Γ) (InterState Q Λ) where
  transition := interTransition D M
  accept
    | .run q => M.accept q
    | _ => false
  initial := .scan D.start

private def runCfg {n : ℕ} (c : DLBA.Cfg (LBA.EndAlpha T Γ) Λ n) :
    DLBA.Cfg (LBA.EndAlpha T Γ) (InterState Q Λ) n :=
  ⟨.run c.state, c.tape⟩

private lemma cfg_ext {A S : Type*} {n : ℕ} {x y : DLBA.Cfg A S n}
    (hs : x.state = y.state) (hc : x.tape.contents = y.tape.contents)
    (hh : x.tape.head = y.tape.head) : x = y := by
  rcases x with ⟨xs, xc, xh⟩
  rcases y with ⟨ys, yc, yh⟩
  simp_all

private lemma write_read_same {A : Type*} {n : ℕ} (t : DLBA.BoundedTape A n) :
    (t.write t.read).contents = t.contents := by
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.read]
  exact Function.update_eq_self _ _

@[simp] private lemma loadEnd_zero (w : List T) :
    (LBA.loadEnd (Γ := Γ) w).contents ⟨0, by omega⟩ = LBA.leftMark := by
  simp [LBA.loadEnd]

@[simp] private lemma loadEnd_input (w : List T) (i : ℕ) (hi : i < w.length) :
    (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩ =
      Sum.inl (some (Sum.inl w[i])) := by
  simp [LBA.loadEnd, hi]

@[simp] private lemma loadEnd_right (w : List T) :
    (LBA.loadEnd (Γ := Γ) w).contents ⟨w.length + 1, by omega⟩ = LBA.rightMark := by
  simp [LBA.loadEnd]

private noncomputable def scanCfg (D : DFA T Q) (w : List T)
    (i : ℕ) (hi : i ≤ w.length) :
    DLBA.Cfg (LBA.EndAlpha T Γ) (InterState Q Λ) (w.length + 1) :=
  ⟨.scan (D.evalFrom D.start (w.take i)),
    ⟨(LBA.loadEnd (Γ := Γ) w).contents, ⟨i + 1, by omega⟩⟩⟩

private noncomputable def rewindCfg (w : List T) (i : ℕ) (hi : i ≤ w.length) :
    DLBA.Cfg (LBA.EndAlpha T Γ) (InterState Q Λ) (w.length + 1) :=
  ⟨.rewind, ⟨(LBA.loadEnd (Γ := Γ) w).contents, ⟨i, by omega⟩⟩⟩

private lemma initial_scan_step (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T) :
    LBA.Step (interMachine D M) (LBA.initCfgEnd (interMachine D M) w)
      (scanCfg (Γ := Γ) (Λ := Λ) D w 0 (Nat.zero_le _)) := by
  refine ⟨.scan D.start, LBA.leftMark, .right, ?_, ?_⟩
  · change _ ∈ interTransition D M (.scan D.start) LBA.leftMark
    rfl
  · apply cfg_ext
    · simp [scanCfg]
    · simp only [scanCfg, LBA.initCfgEnd, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Γ) w).contents =
        Function.update (LBA.loadEnd (Γ := Γ) w).contents ⟨0, by omega⟩ LBA.leftMark
      rw [← loadEnd_zero (Γ := Γ) w, Function.update_eq_self]
    · apply Fin.ext
      simp [LBA.initCfgEnd, LBA.loadEnd, scanCfg, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]

private lemma scan_step (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T)
    (i : ℕ) (hi : i < w.length) :
    LBA.Step (interMachine D M)
      (scanCfg (Γ := Γ) (Λ := Λ) D w i hi.le)
      (scanCfg (Γ := Γ) (Λ := Λ) D w (i + 1) hi) := by
  let a := w[i]
  refine ⟨.scan (D.step (D.evalFrom D.start (w.take i)) a),
    Sum.inl (some (Sum.inl a)), .right, ?_, ?_⟩
  · have hread :
        (scanCfg (Γ := Γ) (Λ := Λ) D w i hi.le).tape.read =
          Sum.inl (some (Sum.inl a)) := by
        simp [scanCfg, DLBA.BoundedTape.read, a, loadEnd_input, hi]
    rw [hread]
    change _ ∈ interTransition D M (.scan (D.evalFrom D.start (w.take i)))
      (Sum.inl (some (Sum.inl a)))
    rfl
  · apply cfg_ext
    · simp only [scanCfg, a]
      rw [← DFA.evalFrom_append_singleton, List.take_concat_get' w i hi]
    · simp only [scanCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Γ) w).contents =
        Function.update (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩
          (Sum.inl (some (Sum.inl a)))
      rw [show Sum.inl (some (Sum.inl a)) =
          (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩ by
        symm; exact loadEnd_input (Γ := Γ) w i hi,
        Function.update_eq_self]
    · apply Fin.ext
      simp only [scanCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      rw [dif_pos (by omega)]

private lemma scan_reach (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T)
    (i : ℕ) (hi : i ≤ w.length) :
    LBA.Reaches (interMachine D M)
      (scanCfg (Γ := Γ) (Λ := Λ) D w 0 (Nat.zero_le _))
      (scanCfg (Γ := Γ) (Λ := Λ) D w i hi) := by
  induction i with
  | zero => exact Relation.ReflTransGen.refl
  | succ i ih =>
      exact (ih (by omega)).tail (scan_step D M w i (by omega))

private lemma scan_right_step (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T)
    (hD : w ∈ D.accepts) :
    LBA.Step (interMachine D M)
      (scanCfg (Γ := Γ) (Λ := Λ) D w w.length le_rfl)
      (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w w.length le_rfl) := by
  refine ⟨.rewind, LBA.rightMark, .left, ?_, ?_⟩
  · have hacc : D.eval w ∈ D.accept := (DFA.mem_accepts D).mp hD
    have hread :
        (scanCfg (Γ := Γ) (Λ := Λ) D w w.length le_rfl).tape.read =
          LBA.rightMark := by
      simp [scanCfg, DLBA.BoundedTape.read]
    rw [hread]
    change _ ∈ interTransition D M (.scan (D.evalFrom D.start (w.take w.length)))
      LBA.rightMark
    rw [List.take_length]
    change D.evalFrom D.start w ∈ D.accept at hacc
    simp [interTransition, hacc]
  · apply cfg_ext
    · rfl
    · simp only [scanCfg, rewindCfg, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Γ) w).contents =
        Function.update (LBA.loadEnd (Γ := Γ) w).contents ⟨w.length + 1, by omega⟩
          LBA.rightMark
      rw [← loadEnd_right (Γ := Γ) w, Function.update_eq_self]
    · apply Fin.ext
      simp [scanCfg, rewindCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private lemma rewind_step (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T)
    (i : ℕ) (hi : i < w.length) :
    LBA.Step (interMachine D M)
      (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w (i + 1) (by omega))
      (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w i hi.le) := by
  refine ⟨.rewind, Sum.inl (some (Sum.inl w[i])), .left, ?_, ?_⟩
  · have hread :
        (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w (i + 1) (by omega)).tape.read =
          Sum.inl (some (Sum.inl w[i])) := by
      simp [rewindCfg, DLBA.BoundedTape.read, loadEnd_input, hi]
    rw [hread]
    change _ ∈ interTransition D M .rewind (Sum.inl (some (Sum.inl w[i])))
    rfl
  · apply cfg_ext
    · rfl
    · simp only [rewindCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Γ) w).contents =
        Function.update (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩
          (Sum.inl (some (Sum.inl w[i])))
      rw [show Sum.inl (some (Sum.inl w[i])) =
          (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩ by
        symm; exact loadEnd_input (Γ := Γ) w i hi,
        Function.update_eq_self]
    · apply Fin.ext
      simp [rewindCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private lemma rewind_reach (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T)
    (i : ℕ) (hi : i ≤ w.length) :
    LBA.Reaches (interMachine D M)
      (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w i hi)
      (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w 0 (Nat.zero_le _)) := by
  induction i with
  | zero => exact Relation.ReflTransGen.refl
  | succ i ih =>
      exact Relation.ReflTransGen.head (rewind_step D M w i (by omega)) (ih (by omega))

private lemma rewind_zero_step (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T) :
    LBA.Step (interMachine D M)
      (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w 0 (Nat.zero_le _))
      (runCfg (Q := Q) (LBA.initCfgEnd M w)) := by
  refine ⟨.run M.initial, LBA.leftMark, .stay, ?_, ?_⟩
  · change _ ∈ interTransition D M .rewind LBA.leftMark
    rfl
  · apply cfg_ext
    · rfl
    · exact (write_read_same _).symm
    · apply Fin.ext
      rfl

private lemma init_reach_run (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T)
    (hD : w ∈ D.accepts) :
    LBA.Reaches (interMachine D M) (LBA.initCfgEnd (interMachine D M) w)
      (runCfg (Q := Q) (LBA.initCfgEnd M w)) := by
  exact (Relation.ReflTransGen.single (initial_scan_step D M w)).trans
    ((scan_reach D M w w.length le_rfl).trans
      ((Relation.ReflTransGen.single (scan_right_step D M w hD)).trans
        ((rewind_reach D M w w.length le_rfl).trans
          (Relation.ReflTransGen.single (rewind_zero_step D M w)))))

private def InterInv (D : DFA T Q) (M : LBA.Machine (LBA.EndAlpha T Γ) Λ)
    (w : List T) (c : DLBA.Cfg (LBA.EndAlpha T Γ) (InterState Q Λ) (w.length + 1)) : Prop :=
  LBA.initCfgEnd (interMachine D M) w = c ∨
  (∃ (i : ℕ) (hi : i ≤ w.length),
    scanCfg (Γ := Γ) (Λ := Λ) D w i hi = c) ∨
  (w ∈ D.accepts ∧ ∃ (i : ℕ) (hi : i ≤ w.length),
    rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w i hi = c) ∨
  (w ∈ D.accepts ∧ ∃ cM : DLBA.Cfg (LBA.EndAlpha T Γ) Λ (w.length + 1),
    LBA.Reaches M (LBA.initCfgEnd M w) cM ∧ runCfg (Q := Q) cM = c)

private lemma interInv_step (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T)
    {c c' : DLBA.Cfg (LBA.EndAlpha T Γ) (InterState Q Λ) (w.length + 1)}
    (hc : InterInv D M w c) (hstep : LBA.Step (interMachine D M) c c') :
    InterInv D M w c' := by
  rcases hstep with ⟨q', a, d, hmem, rfl⟩
  rcases hc with hinit | hscan | hrewind | hrun
  · rw [← hinit] at hmem ⊢
    have hread : (LBA.initCfgEnd (interMachine D M) w).tape.read = LBA.leftMark := by
      change (LBA.loadEnd (Γ := Γ) w).contents
        (LBA.loadEnd (Γ := Γ) w).head = LBA.leftMark
      exact loadEnd_zero (Γ := Γ) w
    rw [hread] at hmem
    change (q', a, d) ∈ interTransition D M (.scan D.start) LBA.leftMark at hmem
    simp only [interTransition, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    right; left
    refine ⟨0, Nat.zero_le _, ?_⟩
    apply cfg_ext
    · simp [scanCfg]
    · simp only [scanCfg, LBA.initCfgEnd, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      change (LBA.loadEnd (Γ := Γ) w).contents =
        Function.update (LBA.loadEnd (Γ := Γ) w).contents ⟨0, by omega⟩ LBA.leftMark
      rw [← loadEnd_zero (Γ := Γ) w, Function.update_eq_self]
    · apply Fin.ext
      simp [LBA.initCfgEnd, LBA.loadEnd, scanCfg, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
  · rcases hscan with ⟨i, hi, hci⟩
    rw [← hci] at hmem ⊢
    by_cases hilast : i = w.length
    · subst i
      have hread :
          (scanCfg (Γ := Γ) (Λ := Λ) D w w.length le_rfl).tape.read =
            LBA.rightMark := by simp [scanCfg, DLBA.BoundedTape.read]
      rw [hread] at hmem
      change (q', a, d) ∈
        interTransition D M (.scan (D.evalFrom D.start (w.take w.length))) LBA.rightMark at hmem
      rw [List.take_length] at hmem
      simp only [interTransition] at hmem
      split at hmem
      · rename_i hacc
        simp only [Set.mem_singleton_iff] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        right; right; left
        refine ⟨(DFA.mem_accepts D).mpr (by simpa [DFA.eval] using hacc),
          w.length, le_rfl, ?_⟩
        apply cfg_ext
        · rfl
        · simp only [scanCfg, rewindCfg, DLBA.BoundedTape.write,
            DLBA.BoundedTape.moveHead]
          change (LBA.loadEnd (Γ := Γ) w).contents =
            Function.update (LBA.loadEnd (Γ := Γ) w).contents
              ⟨w.length + 1, by omega⟩ LBA.rightMark
          rw [← loadEnd_right (Γ := Γ) w, Function.update_eq_self]
        · apply Fin.ext
          simp [scanCfg, rewindCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      · simp at hmem
    · have hi' : i < w.length := lt_of_le_of_ne hi hilast
      let x := w[i]
      have hread :
          (scanCfg (Γ := Γ) (Λ := Λ) D w i hi).tape.read =
            Sum.inl (some (Sum.inl x)) := by
        simp [scanCfg, DLBA.BoundedTape.read, x, loadEnd_input, hi']
      rw [hread] at hmem
      change (q', a, d) ∈
        interTransition D M (.scan (D.evalFrom D.start (w.take i)))
          (Sum.inl (some (Sum.inl x))) at hmem
      simp only [interTransition, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      right; left
      refine ⟨i + 1, hi', ?_⟩
      apply cfg_ext
      · simp only [scanCfg, x]
        rw [← DFA.evalFrom_append_singleton, List.take_concat_get' w i hi']
      · simp only [scanCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        change (LBA.loadEnd (Γ := Γ) w).contents =
          Function.update (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩
            (Sum.inl (some (Sum.inl x)))
        rw [show Sum.inl (some (Sum.inl x)) =
            (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩ by
          symm; exact loadEnd_input (Γ := Γ) w i hi',
          Function.update_eq_self]
      · apply Fin.ext
        simp only [scanCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        rw [dif_pos (by omega)]
  · rcases hrewind with ⟨hD, i, hi, hci⟩
    rw [← hci] at hmem ⊢
    rcases i with _ | i
    · have hread :
          (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w 0 (Nat.zero_le _)).tape.read =
            LBA.leftMark := by
        exact loadEnd_zero (Γ := Γ) w
      rw [hread] at hmem
      change (q', a, d) ∈ interTransition D M .rewind LBA.leftMark at hmem
      simp only [interTransition, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      right; right; right
      refine ⟨hD, LBA.initCfgEnd M w, Relation.ReflTransGen.refl, ?_⟩
      apply cfg_ext
      · rfl
      · simp only [rewindCfg, runCfg, LBA.initCfgEnd, DLBA.BoundedTape.write,
          DLBA.BoundedTape.moveHead]
        change (LBA.loadEnd (Γ := Γ) w).contents =
          Function.update (LBA.loadEnd (Γ := Γ) w).contents ⟨0, by omega⟩ LBA.leftMark
        rw [← loadEnd_zero (Γ := Γ) w, Function.update_eq_self]
      · apply Fin.ext; rfl
    · have hi' : i < w.length := by omega
      have hread :
          (rewindCfg (Γ := Γ) (Q := Q) (Λ := Λ) w (i + 1) hi).tape.read =
            Sum.inl (some (Sum.inl w[i])) := by
        simp [rewindCfg, DLBA.BoundedTape.read, loadEnd_input, hi']
      rw [hread] at hmem
      change (q', a, d) ∈
        interTransition D M .rewind (Sum.inl (some (Sum.inl w[i]))) at hmem
      simp only [interTransition, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      right; right; left
      refine ⟨hD, i, hi'.le, ?_⟩
      apply cfg_ext
      · rfl
      · simp only [rewindCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        change (LBA.loadEnd (Γ := Γ) w).contents =
          Function.update (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩
            (Sum.inl (some (Sum.inl w[i])))
        rw [show Sum.inl (some (Sum.inl w[i])) =
            (LBA.loadEnd (Γ := Γ) w).contents ⟨i + 1, by omega⟩ by
          symm; exact loadEnd_input (Γ := Γ) w i hi',
          Function.update_eq_self]
      · apply Fin.ext
        simp only [rewindCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        rw [dif_pos (by omega)]
        simp
  · rcases hrun with ⟨hD, cM, hreach, hci⟩
    rw [← hci] at hmem ⊢
    change (q', a, d) ∈ interTransition D M (.run cM.state) cM.tape.read at hmem
    rcases hmem with ⟨p, hp, heq⟩
    rcases p with ⟨p, b, e⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    right; right; right
    let cM' : DLBA.Cfg (LBA.EndAlpha T Γ) Λ (w.length + 1) :=
      ⟨p, (cM.tape.write a).moveHead d⟩
    refine ⟨hD, cM', hreach.tail ?_, rfl⟩
    exact ⟨p, a, d, hp, rfl⟩

private lemma interInv_reaches (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T)
    {c : DLBA.Cfg (LBA.EndAlpha T Γ) (InterState Q Λ) (w.length + 1)}
    (h : LBA.Reaches (interMachine D M) (LBA.initCfgEnd (interMachine D M) w) c) :
    InterInv D M w c := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih => exact interInv_step D M w ih hstep

private lemma run_step (D : DFA T Q) (M : LBA.Machine (LBA.EndAlpha T Γ) Λ)
    {n : ℕ} {c c' : DLBA.Cfg (LBA.EndAlpha T Γ) Λ n}
    (h : LBA.Step M c c') :
    LBA.Step (interMachine D M) (runCfg (Q := Q) c) (runCfg (Q := Q) c') := by
  rcases h with ⟨q', a, d, hmem, rfl⟩
  refine ⟨.run q', a, d, ?_, rfl⟩
  exact ⟨(q', a, d), hmem, rfl⟩

private lemma run_reaches (D : DFA T Q) (M : LBA.Machine (LBA.EndAlpha T Γ) Λ)
    {n : ℕ} {c c' : DLBA.Cfg (LBA.EndAlpha T Γ) Λ n}
    (h : LBA.Reaches M c c') :
    LBA.Reaches (interMachine D M) (runCfg (Q := Q) c) (runCfg (Q := Q) c') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (run_step D M hstep)

private theorem inter_accepts_iff (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (w : List T) :
    LBA.Accepts (interMachine D M) (LBA.initCfgEnd (interMachine D M) w) ↔
      LBA.Accepts M (LBA.initCfgEnd M w) ∧ w ∈ D.accepts := by
  constructor
  · rintro ⟨c, hreach, hacc⟩
    have hinv := interInv_reaches D M w hreach
    rcases hinv with hinit | hscan | hrewind | hrun
    · rw [← hinit] at hacc
      simp [interMachine, LBA.initCfgEnd] at hacc
    · rcases hscan with ⟨i, hi, hci⟩
      rw [← hci] at hacc
      simp [interMachine, scanCfg] at hacc
    · rcases hrewind with ⟨_hD, i, hi, hci⟩
      rw [← hci] at hacc
      simp [interMachine, rewindCfg] at hacc
    · rcases hrun with ⟨hD, cM, hM, hci⟩
      rw [← hci] at hacc
      exact ⟨⟨cM, hM, hacc⟩, hD⟩
  · rintro ⟨⟨cM, hreach, hacc⟩, hD⟩
    refine ⟨runCfg (Q := Q) cM, ?_, hacc⟩
    exact (init_reach_run D M w hD).trans (run_reaches D M hreach)

private theorem interMachine_language (D : DFA T Q)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) :
    LBA.LanguageEnd (interMachine D M) = LBA.LanguageEnd M ⊓ D.accepts := by
  ext w
  exact inter_accepts_iff D M w

end CSIntersectionRegular

open CSIntersectionRegular

variable {T : Type} [Fintype T] [DecidableEq T]

/-- The intersection of a context-sensitive language and a regular language is
context-sensitive (over the library's standard finite alphabets). -/
public theorem CS_inter_regular (L R : Language T) (hL : is_CS L) (hR : R.IsRegular) :
    is_CS (L ⊓ R) := by
  classical
  have hLBA : is_LBA L := CS_subset_LBA hL
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hML⟩ := hLBA
  obtain ⟨Q, hQ, D, hDR⟩ := hR
  letI : Fintype Γ := hΓ
  letI : Fintype Λ := hΛ
  letI : DecidableEq Γ := hdΓ
  letI : DecidableEq Λ := hdΛ
  letI : Fintype Q := hQ
  letI : DecidableEq Q := Classical.decEq Q
  have hinter : is_LBA (L ⊓ R) := by
    refine ⟨Γ, InterState Q Λ, inferInstance, inferInstance, inferInstance, inferInstance,
      interMachine D M, ?_⟩
    rw [interMachine_language, hML, hDR]
  exact LBA_subset_CS hinter

/-- Context-sensitive languages are closed under intersection with regular languages. -/
public theorem CS_closedUnderIntersectionWithRegular :
    ClosedUnderIntersectionWithRegular (α := T) is_CS := by
  intro L hL R hR
  exact CS_inter_regular L R hL hR

end
