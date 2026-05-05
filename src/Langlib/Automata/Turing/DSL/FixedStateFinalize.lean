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
