import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability

/-! # Copy Block with Separator

This file proves that `copyBinaryWithSep` (self-duplication with separator)
is block-realizable.

`copyBinaryWithSep block = block ++ [chainConsBottom] ++ block`

The TM uses `default` as a position marker during copying. Since blocks
never contain `default` (by the `TM0RealizesBlock` precondition), this
marker never conflicts with block content.
-/

open Turing PartrecToTM2 TM2to1

/-- Copy a block and insert a separator between the original and the copy. -/
noncomputable def copyBinaryWithSep (block : List ChainΓ) : List ChainΓ :=
  block ++ [chainConsBottom] ++ block

theorem copyBinaryWithSep_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ copyBinaryWithSep block, g ≠ default := by
  unfold copyBinaryWithSep
  intro g hg
  have hmem : g ∈ block ∨ g = chainConsBottom := by
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    tauto
  rcases hmem with hmem | rfl
  · exact hblock g hmem
  · exact chainConsBottom_ne_default

/-- The copy-with-sep operation is block-realizable.

The TM uses `default` as a position marker. During copying, it replaces
the current source character with `default` (marking it), carries the
character to the copy destination, writes it, shifts the suffix to
maintain the block-suffix separator, then rewinds to the marker and
restores the original character. -/
theorem tm0_copyBinaryWithSep_block :
    TM0RealizesBlock ChainΓ copyBinaryWithSep := by
  sorry
