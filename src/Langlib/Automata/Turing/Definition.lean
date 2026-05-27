import Mathlib

/-! # Equivalence of Unrestricted Grammars and Turing Machines

This file defines the grammar construction for simulating TM0 machines, and states
the equivalence between unrestricted (Type-0) grammars and Turing machines.

The correctness proofs and the main equivalence theorem are in `TMtoGrammarHelpers.lean`.

## Main definitions

- `is_TM`: A language is TM-recognizable if there exists a finite-state
  Turing machine (using Mathlib's `Turing.TM0` model) that halts on input
  `w` iff `w ∈ L`.
-/
open Turing

/-! ### Definition of TM-Recognizability -/

/-- A language `L` over finite input alphabet `T` is **TM-recognizable** if
there exists a finite work alphabet `Γ` and a finite-state Turing machine
(in Mathlib's `Turing.TM0` model) over tape alphabet `Option (T ⊕ Γ)` that
halts on input `w` if and only if `w ∈ L`.

The tape alphabet is `Option (T ⊕ Γ)` where:
- `none` represents the blank symbol
- `some (Sum.inl t)` represents an input symbol `t : T`
- `some (Sum.inr γ)` represents a work symbol `γ : Γ`

The input word `w : List T` is written on the tape by the fixed inclusion
`T ↪ T ⊕ Γ`, producing `w.map (fun t => some (Sum.inl t))`.  The recognizer
may choose only the finite work alphabet and the machine, not an arbitrary
preprocessing map on input symbols. -/
def is_TM {T : Type} [Fintype T] (L : Language T) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ)
    (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : Turing.TM0.Machine (Option (T ⊕ Γ)) Λ),
    ∀ w : List T,
      w ∈ L ↔ (Turing.TM0.eval M (w.map (fun t => some (Sum.inl t)))).Dom

def TM {T : Type} [Fintype T] : Set (Language T) := setOf is_TM
