module

public import Mathlib.Computability.PostTuringMachine
public import Mathlib.Computability.Language
@[expose]
public section

/-! # Tape-symbol acceptance for recursive languages (definition)

The class of recursive languages is usually presented (`is_Recursive`) by an
always-halting TM0 that signals acceptance through its **final control state**. An
equally natural convention is for the machine to signal acceptance through the
**symbol left under the head** when it halts. This file defines that variant,
`is_Recursive_byTape`; the equivalence with the state-based `is_Recursive` is proved
in `Automata.Recursive.Equivalence.TapeCharacterization`.

The tape convention matches `is_Recursive` / `is_TM`: the tape alphabet is
`Option (T ⊕ Γ)` with `none` the blank, `some (Sum.inl t)` an input symbol, and the
input word `w : List T` written as `w.map (fun t => some (Sum.inl t))`.
-/

open Turing

variable {T : Type}

/-- A language is recursive *by the tape-acceptance convention* if some always-halting
TM0 leaves a designated `acceptSym` under the head exactly on the words of `L`. -/
@[expose]
public def is_Recursive_byTape (L : Language T) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ) (_ : DecidableEq Γ)
    (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine (Option (T ⊕ Γ)) Λ) (acceptSym : Option (T ⊕ Γ)),
    (∀ w : List T,
      (Turing.eval (TM0.step M) (TM0.init (w.map fun t => some (Sum.inl t)))).Dom) ∧
    (∀ w : List T,
      ∀ h : (Turing.eval (TM0.step M)
          (TM0.init (w.map fun t => some (Sum.inl t)))).Dom,
        w ∈ L ↔
          ((Turing.eval (TM0.step M)
            (TM0.init (w.map fun t => some (Sum.inl t)))).get h).Tape.head = acceptSym)
