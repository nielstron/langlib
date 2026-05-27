import Mathlib
import Langlib.Automata.Turing.DSL.PartrecCodeToTM0

/-! # Partrec Chain Alphabet Fragments

This file provides basic definitions and lemmas for working with the
chain tape alphabet `ChainΓ`:

- `γ'ToChainΓ` and `chainConsBottom`: distinguished cells
- `chainBinaryRepr`: binary representation of natural numbers as ChainΓ cells
- Basic non-defaultness properties used by the direct code bridge

## Key results

- `chainConsBottom_ne_default`: the cons-bottom marker is a valid nonblank cell.
- `chainBinaryRepr_zero`: zero is represented by the empty fragment.
- `chainBinaryRepr_ne_default`: every encoded natural-number cell is nonblank.
-/

open Turing PartrecToTM2 TM2to1

/-! ### Instances -/

noncomputable instance instDecEqChainΓ' : DecidableEq ChainΓ :=
  instDecidableEqProd (α := Bool) (β := (K' → Option Γ'))

/-! ### Distinguished ChainΓ cells -/

/-- Map a Γ' value to its corresponding ChainΓ cell (without bottom marker). -/
noncomputable def γ'ToChainΓ (γ' : Γ') : ChainΓ :=
  (false, Function.update (fun _ => none) K'.main (some γ'))

/-- The ChainΓ cell for the bottom marker with cons. -/
noncomputable def chainConsBottom : ChainΓ :=
  (true, Function.update (fun _ => none) K'.main (some Γ'.cons))

/-- `chainConsBottom` is non-default. -/
theorem chainConsBottom_ne_default : chainConsBottom ≠ (default : ChainΓ) := by
  simp +decide

/-! ### Binary Representation -/

/-- Binary representation of n as ChainΓ cells (LSB first, no markers). -/
noncomputable def chainBinaryRepr (n : ℕ) : List ChainΓ :=
  (trNat n).map γ'ToChainΓ

/-- `chainBinaryRepr 0` is the empty list. -/
theorem chainBinaryRepr_zero : chainBinaryRepr 0 = [] := by
  simp +decide

/-- All elements of `chainBinaryRepr n` are non-default. -/
theorem chainBinaryRepr_ne_default (n : ℕ) :
    ∀ g ∈ chainBinaryRepr n, g ≠ (default : ChainΓ) := by
  intro g hg
  obtain ⟨ γ', _, rfl ⟩ := List.mem_map.mp hg
  cases γ' <;> simp +decide
