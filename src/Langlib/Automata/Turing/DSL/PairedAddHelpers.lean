import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinaryArithmetic
import Langlib.Automata.Turing.DSL.BinarySuccessor

/-! # Helper: While-loop TM0 combinator -/

open Turing PartrecToTM2 TM2to1

/-- While-loop TM0 machine. Runs M repeatedly; when M halts at state
    `q_continue`, restarts M. When M halts at any other state, halts. -/
noncomputable def tm0WhileLoop {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    [DecidableEq Λ]
    (M : TM0.Machine Γ Λ) (q_continue : Λ) : TM0.Machine Γ Λ := fun q a =>
  match M q a with
  | some (q', s) => some (q', s)
  | none => if q = q_continue then M default a else none

theorem tm0WhileLoop_step_some {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    [DecidableEq Λ]
    (M : TM0.Machine Γ Λ) (q_continue : Λ)
    (q : Λ) (a : Γ) (q' : Λ) (s : TM0.Stmt Γ)
    (h : M q a = some (q', s)) :
    tm0WhileLoop M q_continue q a = some (q', s) := by
  simp [tm0WhileLoop, h]

theorem tm0WhileLoop_halt {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    [DecidableEq Λ]
    (M : TM0.Machine Γ Λ) (q_continue : Λ)
    (q : Λ) (a : Γ) (hne : q ≠ q_continue) (h : M q a = none) :
    tm0WhileLoop M q_continue q a = none := by
  simp [tm0WhileLoop, h, hne]

theorem tm0WhileLoop_reaches_of_M {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    [DecidableEq Λ]
    (M : TM0.Machine Γ Λ) (q_continue : Λ)
    (c₁ c₂ : TM0.Cfg Γ Λ)
    (h : Reaches (TM0.step M) c₁ c₂) :
    Reaches (TM0.step (tm0WhileLoop M q_continue)) c₁ c₂ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h₁₂ ih =>
    refine ih.tail ?_
    simp only [TM0.step, tm0WhileLoop] at h₁₂ ⊢
    revert h₁₂
    cases hM : M _ _ with
    | none => simp
    | some p => simp
