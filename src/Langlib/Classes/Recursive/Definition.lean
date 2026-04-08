import Mathlib
import Langlib.Automata.Turing.Definition

/-! # Recursive (Decidable) Languages

This file defines the class of **recursive** (decidable) languages, characterised
by the existence of a Turing machine that *decides* the language: the machine always
halts, and it accepts exactly the words in the language.

## Main definitions

- `is_Recursive` — a language is recursive if there exists a TM₀ machine that always
  halts together with a Boolean acceptance predicate on states, such that `w ∈ L` iff
  the machine halts in a state `q` with `accept q = true`.
- `Recursive` — the class of all recursive languages.
-/

open Turing

variable {T : Type}

/-- A language `L` over alphabet `T` is **recursive** (decidable) if there exists a
finite-state Turing machine (in Mathlib's `Turing.TM0` model) that **always halts**,
together with a Boolean predicate `accept` on states, such that `w ∈ L` iff the
machine halts in a state `q` with `accept q = true`.

The machine uses `Option T` as the tape alphabet (`none` = blank) and encodes the
input word `w : List T` as `w.map some` on the tape. -/
def is_Recursive {T : Type} (L : Language T) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine (Option T) Λ) (accept : Λ → Bool),
    (∀ w : List T,
      (Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).Dom) ∧
    (∀ w : List T,
      ∀ h : (Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).Dom,
        w ∈ L ↔
          accept
            ((Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).get h).q = true)

/-- The class of recursive (decidable) languages. -/
def Recursive : Set (Language T) := setOf is_Recursive
