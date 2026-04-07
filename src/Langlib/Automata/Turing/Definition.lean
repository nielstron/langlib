import Mathlib

/-! # Equivalence of Unrestricted Grammars and Turing Machines

This file defines the grammar construction for simulating TM0 machines, and states
the equivalence between unrestricted (Type-0) grammars and Turing machines.

The correctness proofs and the main equivalence theorem are in `TMtoGrammarHelpers.lean`.

## Main definitions

- `is_TM`: A language is TM-recognizable if there exists a finite-state
  Turing machine (using Mathlib's `Turing.TM0` model) that halts on input `w` iff `w ∈ L`.
-/
open Turing

/-! ### Definition of TM-Recognizability -/

/-- A language `L` over alphabet `T` is **TM-recognizable** if there exists a
finite-state Turing machine (in Mathlib's `Turing.TM0` model) that halts on input `w`
if and only if `w ∈ L`.

We use `Option T` as the tape alphabet (`none` = blank), and encode the input word
`w : List T` as `w.map some` on the tape. -/
def is_TM {T : Type} (L : Language T) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : Turing.TM0.Machine (Option T) Λ),
    ∀ w : List T, w ∈ L ↔ (Turing.TM0.eval M (w.map Option.some)).Dom

def TM : Set (Language T) := setOf is_TM
