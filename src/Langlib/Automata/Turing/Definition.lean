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

/-- A language `L` over alphabet `T` is **TM-recognizable** if there exists
a fintype `Γ` of tape symbols and a finite-state Turing machine
(in Mathlib's `Turing.TM0` model) over tape alphabet `Option Γ` that
halts on input `w` if and only if `w ∈ L`.

The tape alphabet is `Option Γ` where:
- `none` represents the blank symbol
- `some γ` represents a tape symbol `γ : Γ`

The input word `w : List T` is encoded on the tape via an encoding
function `encode : T → Γ`, producing `w.map (fun x => some (encode x))`.

This generalizes the standard definition by allowing the tape alphabet
and encoding function to be chosen freely, matching the role of
nonterminals in unrestricted grammars. -/
def is_TM {T : Type} (L : Language T) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ)
    (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : Turing.TM0.Machine (Option Γ) Λ)
    (encode : T → Γ),
    ∀ w : List T, w ∈ L ↔ (Turing.TM0.eval M (w.map (fun t => some (encode t)))).Dom

def TM : Set (Language T) := setOf is_TM
