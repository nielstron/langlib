import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose

/-! # Fixed-state finalizer

Tiny utility machine that preserves the tape and halts in a known state.
This is useful after composing machines whose tape behavior is known but whose
halting state is intentionally abstracted by `TM0RealizesBlock`.
-/

open Turing

inductive FinalizeSt where
  | start
  | done
  deriving DecidableEq, Fintype

instance : Inhabited FinalizeSt := ⟨.start⟩

def finalizeMachine {Γ : Type} [Inhabited Γ] : TM0.Machine Γ FinalizeSt :=
  fun q a =>
    match q with
    | .start => some (.done, TM0.Stmt.write a)
    | .done => none

theorem finalize_step_start {Γ : Type} [Inhabited Γ] (T : Tape Γ) :
    TM0.step finalizeMachine ⟨FinalizeSt.start, T⟩ =
      some ⟨FinalizeSt.done, T⟩ := by
  cases T
  simp [TM0.step, finalizeMachine, Tape.write]

theorem finalize_step_done {Γ : Type} [Inhabited Γ] (T : Tape Γ) :
    TM0.step finalizeMachine ⟨FinalizeSt.done, T⟩ = none := by
  simp [TM0.step, finalizeMachine]

theorem finalize_evalFromCfg {Γ : Type} [Inhabited Γ] (T : Tape Γ) :
    (TM0Seq.evalFromCfg finalizeMachine ⟨FinalizeSt.start, T⟩).Dom ∧
    ∀ h, (TM0Seq.evalFromCfg finalizeMachine ⟨FinalizeSt.start, T⟩).get h =
      ⟨FinalizeSt.done, T⟩ := by
  have hstep := finalize_step_start T
  have hhalt := finalize_step_done T
  have hmem : ⟨FinalizeSt.done, T⟩ ∈
      TM0Seq.evalFromCfg finalizeMachine ⟨FinalizeSt.start, T⟩ := by
    exact Turing.mem_eval.mpr ⟨Relation.ReflTransGen.single hstep, hhalt⟩
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, hmem⟩
  · intro h
    exact Part.get_eq_of_mem hmem h

theorem compose_finalize_evalCfg {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l l' : List Γ)
    (hM_dom : (TM0Seq.evalCfg M l).Dom)
    (hM_tape : ((TM0Seq.evalCfg M l).get hM_dom).Tape = Tape.mk₁ l') :
    letI : Inhabited (Λ ⊕ FinalizeSt) := ⟨Sum.inl default⟩
    let Mcomp : TM0.Machine Γ (Λ ⊕ FinalizeSt) :=
      @TM0Seq.compose Γ Λ inferInstance FinalizeSt inferInstance M finalizeMachine
    (TM0Seq.evalCfg Mcomp l).Dom ∧
    ∀ h, (TM0Seq.evalCfg Mcomp l).get h =
      ⟨Sum.inr FinalizeSt.done, Tape.mk₁ l'⟩ := by
  letI : Inhabited (Λ ⊕ FinalizeSt) := ⟨Sum.inl default⟩
  let Mcomp : TM0.Machine Γ (Λ ⊕ FinalizeSt) :=
    @TM0Seq.compose Γ Λ inferInstance FinalizeSt inferInstance M finalizeMachine
  let c := (TM0Seq.evalCfg M l).get hM_dom
  have hc_mem : c ∈ TM0Seq.evalCfg M l := Part.get_mem hM_dom
  have hc_eval := Turing.mem_eval.mp hc_mem
  have hreach_c : Reaches (TM0.step M) (TM0.init l) c := hc_eval.1
  have hhalt_c : TM0.step M c = none := hc_eval.2
  have hreach_phase1 :
      Reaches (TM0.step Mcomp)
        (TM0.init l)
        ⟨Sum.inl c.q, c.Tape⟩ := by
    simpa [Mcomp, TM0Seq.evalCfg, TM0.init] using
      TM0Seq.compose_phase1_reaches M finalizeMachine c l hreach_c
  have hstep_done :
      TM0.step Mcomp ⟨Sum.inl c.q, c.Tape⟩ =
        some ⟨Sum.inr FinalizeSt.done, c.Tape⟩ := by
    change TM0.step (@TM0Seq.compose Γ Λ inferInstance FinalizeSt inferInstance M finalizeMachine)
        ⟨Sum.inl c.q, c.Tape⟩ =
      some ⟨Sum.inr FinalizeSt.done, c.Tape⟩
    rw [TM0Seq.compose_step_on_halt M finalizeMachine c.q c.Tape hhalt_c]
    change Option.map (fun c₂ : TM0.Cfg Γ FinalizeSt =>
        ({ q := Sum.inr c₂.q, Tape := c₂.Tape } : TM0.Cfg Γ (Λ ⊕ FinalizeSt)))
        (TM0.step finalizeMachine ⟨FinalizeSt.start, c.Tape⟩) =
      some ⟨Sum.inr FinalizeSt.done, c.Tape⟩
    rw [finalize_step_start c.Tape]
    rfl
  have hreach_done :
      Reaches (TM0.step Mcomp)
        (TM0.init l)
        ⟨Sum.inr FinalizeSt.done, c.Tape⟩ :=
    hreach_phase1.tail hstep_done
  have hhalt_done :
      TM0.step Mcomp
        ⟨Sum.inr FinalizeSt.done, c.Tape⟩ = none := by
    simp [Mcomp, TM0.step, TM0Seq.compose, finalizeMachine]
  have hmem : ⟨Sum.inr FinalizeSt.done, Tape.mk₁ l'⟩ ∈
      TM0Seq.evalCfg Mcomp l := by
    rw [← hM_tape]
    exact Turing.mem_eval.mpr ⟨hreach_done, hhalt_done⟩
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, hmem⟩
  · intro h
    exact Part.get_eq_of_mem hmem h
