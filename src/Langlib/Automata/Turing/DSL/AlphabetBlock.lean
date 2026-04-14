import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.DSL.AlphabetSim

/-! # Block Encoding for TM0 Alphabet Simulation

This file provides the key alphabet simulation theorem: any TM0 machine
over a `Fintype` alphabet `Γ` can be simulated by a TM0 machine over
`Option T` for any `Fintype T`.

## Main Results

- `tm0_block_sim` — The core block encoding simulation theorem.

## Overview

The standard approach in TM theory is **block encoding**: each symbol of `Γ`
is encoded as a block of `k` symbols from `Option T`, where `k` is chosen
so that `|Option T|^k ≥ |Γ|`. The simulating machine reads/writes blocks
of `k` symbols to simulate single-step transitions of the original machine.

## Architecture Note

This theorem, combined with the search compilation in `Compile.lean`,
gives the full `is_TM` result: any searchable language is TM-recognizable
over `Option (T ⊕ Γ)`.

## Note on the generalized `is_TM`

With the generalized `is_TM` definition (allowing auxiliary tape symbols `Γ`),
the block encoding is less critical for many results (e.g.,
`is_Recursive_implies_is_TM` can be proved directly via `TM0AlphabetSim`).
However, for the `RE ⊆ TM` direction, the encoding conversion from the
compilation chain's internal format to `w.map (fun x => some (Sum.inl x))`
remains necessary. The block encoding provides one approach to this conversion.
-/

open Turing

/-- **Block encoding simulation**: A TM0 over any `Fintype` alphabet `Γ`
with `Fintype` states can be simulated by a TM0 over `Option T`.

This is the standard block encoding result from TM theory. Given
`M : TM0.Machine Γ Λ` and an input encoding `enc : List T → List Γ`,
there exists a TM0 `M'` over `Option T` that recognizes the same language
when the input is provided as `w.map Option.some`.

The key assumptions are:
- `Fintype Γ`, `Fintype Λ`: the original machine has finite alphabet and states
- `Primcodable T`, `Primcodable Γ`: the alphabets have computable encodings
- `Computable encode_word`: the input encoding is computable

Together these ensure that the halting set `{w | (TM0.eval M (enc w)).Dom}`
is recursively enumerable, and therefore recognizable by a TM0 over any
alphabet with ≥ 2 symbols (in particular, `Option T` for nonempty `T`).

For `IsEmpty T` (the degenerate case where `List T = {[]}`), the result
is trivial since there is only one possible input. -/
theorem tm0_block_sim {T : Type} [DecidableEq T] [Fintype T]
    [Primcodable T]
    {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Primcodable Γ]
    {Λ : Type} [Inhabited Λ] [Fintype Λ]
    (M : TM0.Machine Γ Λ)
    (encode_word : List T → List Γ)
    (henc : Computable encode_word) :
    ∃ (Λ' : Type) (_ : Inhabited Λ') (_ : Fintype Λ')
      (M' : TM0.Machine (Option T) Λ'),
      ∀ w : List T,
        (TM0.eval M (encode_word w)).Dom ↔
        (TM0.eval M' (w.map Option.some)).Dom := by
  sorry
