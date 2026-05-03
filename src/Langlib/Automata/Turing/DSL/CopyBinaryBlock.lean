import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability

/-! # Copy Block with Separator — General Machine

This file defines a **general copy-with-separator machine** that copies
everything before a boundary separator `sep1`, inserting a different
separator `sep2` between the original and the copy:

  `copyWithSep sep2 block = block ++ [sep2] ++ block`

The concrete TM0 uses `default` as a position marker during copying.
Since blocks never contain `default` (by the `TM0RealizesBlock` /
`TM0RealizesBlockSep` preconditions), the marker never conflicts with
block content.

## Specialization

`copyBinaryWithSep` is the specialization to `ChainΓ` with
`sep2 = chainConsBottom`, used by `duplicateNormalizedPaired` for squaring.
-/

open Turing PartrecToTM2 TM2to1

/-! ### General Copy-with-Separator -/

/-- Copy a block and insert separator `sep2` between the original and the copy.

This is the general version: it works for any alphabet and any choice of
inserted separator. -/
def copyWithSep {Γ : Type} (sep2 : Γ) (block : List Γ) : List Γ :=
  block ++ [sep2] ++ block

theorem copyWithSep_ne_default {Γ : Type} [Inhabited Γ] {sep2 : Γ}
    (hsep2 : sep2 ≠ default) (block : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ copyWithSep sep2 block, g ≠ default := by
  unfold copyWithSep
  intro g hg
  have hmem : g ∈ block ∨ g = sep2 := by
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    tauto
  rcases hmem with hmem | rfl
  · exact hblock g hmem
  · exact hsep2

/-- The general copy-with-sep operation is block-sep-realizable.

Given a tape `block ++ [sep1] ++ suffix`, the TM transforms it to
`(block ++ [sep2] ++ block) ++ [sep1] ++ suffix`.

The TM uses `default` as a position marker: it replaces the current
source character with `default` (marking it), carries the character to
the copy destination, writes it, shifts the suffix to maintain the
block-suffix separator, then rewinds to the marker and restores the
original character.

Preconditions: `sep1`, `sep2`, and `default` are all distinct. -/
theorem tm0_copyWithSep_blockSep {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep1 sep2 : Γ}
    (hsep1 : sep1 ≠ default)
    (hsep2 : sep2 ≠ default)
    (h12 : sep1 ≠ sep2) :
    TM0RealizesBlockSep Γ sep1 (copyWithSep sep2) := by
  sorry

/-- The general copy-with-sep operation is block-realizable.

Specialization to `sep1 = default`: copies everything before the first
blank, inserting `sep2` between the original and the copy. -/
theorem tm0_copyWithSep_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep2 : Γ} (hsep2 : sep2 ≠ default) :
    TM0RealizesBlock Γ (copyWithSep sep2) := by
  sorry

/-! ### Specialization to `ChainΓ` with `chainConsBottom` -/

/-- Copy a block and insert `chainConsBottom` between the original and the copy.

This is the `ChainΓ`-specific version used for squaring:
`copyBinaryWithSep block = block ++ [chainConsBottom] ++ block`. -/
noncomputable def copyBinaryWithSep (block : List ChainΓ) : List ChainΓ :=
  copyWithSep chainConsBottom block

theorem copyBinaryWithSep_eq_copyWithSep :
    copyBinaryWithSep = copyWithSep (Γ := ChainΓ) chainConsBottom := by
  rfl

theorem copyBinaryWithSep_unfold (block : List ChainΓ) :
    copyBinaryWithSep block = block ++ [chainConsBottom] ++ block := by
  rfl

theorem copyBinaryWithSep_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ copyBinaryWithSep block, g ≠ default :=
  copyWithSep_ne_default chainConsBottom_ne_default block hblock

/-- The copy-with-sep operation specialized to `ChainΓ` is block-realizable.

Derived from the general `tm0_copyWithSep_block`. -/
theorem tm0_copyBinaryWithSep_block :
    TM0RealizesBlock ChainΓ copyBinaryWithSep := by
  exact tm0_copyWithSep_block chainConsBottom_ne_default
