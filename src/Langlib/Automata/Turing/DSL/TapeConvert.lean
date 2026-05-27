import Langlib.Automata.Turing.DSL.DirectBridge

/-! # Legacy Tape Conversion Compatibility

The previous tape-conversion bridge tried to compute `Encodable.encode w` on
the tape before running the Partrec chain. That route relied on an unsound
separator-lifting obligation. The active proof now goes through
`DirectBridge.lean`, which composes the user code with a code-level list
encoder and only performs a finite per-symbol tape conversion.

This file remains as a small compatibility layer for downstream imports that
used the old blank-preserving embedding names.
-/

open Turing

noncomputable abbrev blankPreservingEmb {T Γ₀ : Type}
    [DecidableEq Γ₀] [Inhabited Γ₀] (γ : Γ₀) : Option (T ⊕ Γ₀) :=
  directBlankEmb (T := T) γ

noncomputable abbrev blankPreservingInv {T Γ₀ : Type} [Inhabited Γ₀]
    (a : Option (T ⊕ Γ₀)) : Γ₀ :=
  directBlankInv (T := T) a

theorem blankPreservingEmb_default {T Γ₀ : Type}
    [DecidableEq Γ₀] [Inhabited Γ₀] :
    blankPreservingEmb (T := T) (default : Γ₀) =
      (default : Option (T ⊕ Γ₀)) :=
  directBlankEmb_default

theorem blankPreservingInv_emb {T Γ₀ : Type}
    [DecidableEq Γ₀] [Inhabited Γ₀] (γ : Γ₀) :
    blankPreservingInv (T := T) (blankPreservingEmb γ) = γ :=
  directBlankInv_emb γ

theorem blankPreservingEmb_ne_default {T Γ₀ : Type}
    [DecidableEq Γ₀] [Inhabited Γ₀] (γ : Γ₀) (hγ : γ ≠ default) :
    blankPreservingEmb (T := T) γ = some (Sum.inr γ) :=
  directBlankEmb_ne_default γ hγ
