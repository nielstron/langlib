import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.DSL.AlphabetSim
import Langlib.Automata.Turing.DSL.Compile

/-! # Encoding Bridge: from arbitrary-encoding TMs to `is_TM`

The compilation chain (Partrec → Code → TM2 → TM1 → TM0) produces a TM0
machine whose input is encoded via `Encodable.encode` and the chain's tape
format (`trInit`, `trList`). The `is_TM` definition, however, requires the
input to be given in "identity encoding": `w.map (fun x => some (Sum.inl x))`.

This file bridges that gap.

## Main results

- `code_implies_isTM` — any `ToPartrec.Code`-semidecidable language over a
  `Fintype` alphabet satisfies `is_TM`.

## Strategy

Given Code `c` with `w ∈ L ↔ (c.eval [Encodable.encode w]).Dom`, and a
TM0 machine `M₀` from `code_to_tm0_fintype` with
`(c.eval [n]).Dom ↔ (TM0.eval M₀ (encode_input n)).Dom`, we need:

  `w ∈ L ↔ (TM0.eval M' (w.map (fun x => some (Sum.inl x)))).Dom`

for some `M' : TM0.Machine (Option (T ⊕ Γ)) Λ`.

The combined TM `M'` operates in three phases:

**Phase 1 (Encode)**: Read `w` symbol-by-symbol from the identity-encoded
tape. Since `T` is `Fintype`, each symbol `t` has a fixed `Encodable.encode t`.
Iteratively compute `Encodable.encode w` on the tape in unary using
`Nat.pair`, storing intermediate results in a work area (using `Γ` symbols).

**Phase 2 (Format)**: Convert the unary number `Encodable.encode w` into
the chain's tape format `encode_input (Encodable.encode w)`, i.e., apply
`PartrecToTM2.trList` and `TM2to1.trInit` formatting.

**Phase 3 (Simulate)**: Simulate the chain's TM0 machine `M₀` on the
formatted tape via alphabet embedding (using `blankPreservingEmb`/`embedTM0`
below).

Since `T` is `Fintype`, all operations in Phases 1–2 use finitely many
states, and the overall TM satisfies `is_TM`.

## Remaining work

The proof of `code_implies_isTM` is marked `sorry`. Completing it requires
explicitly constructing the Phase 1–2 TM0 programs (particularly the
arithmetic for `Nat.pair` and the binary-format conversion for `trList`/
`trInit`) and proving their correctness. This is a substantial but standard
TM construction exercise.
-/

open Turing

/-! ### Helper: Alphabet embedding with blank preservation

We embed `Γ₀` into `Option (T ⊕ Γ₀)` via:
- `default : Γ₀` ↦ `none` (blank → blank)
- `γ ≠ default` ↦ `some (Sum.inr γ)`

This ensures the blank symbol is preserved, which is required by the
alphabet simulation framework (`AlphabetSim.lean`). -/

noncomputable def blankPreservingEmb {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    (γ : Γ₀) : Option (T ⊕ Γ₀) :=
  if γ = default then none else some (Sum.inr γ)

noncomputable def blankPreservingInv {T Γ₀ : Type} [Inhabited Γ₀]
    (a : Option (T ⊕ Γ₀)) : Γ₀ :=
  match a with
  | some (Sum.inr γ) => γ
  | _ => default

theorem blankPreservingEmb_default {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀] :
    blankPreservingEmb (T := T) (default : Γ₀) = (default : Option (T ⊕ Γ₀)) := by
  unfold blankPreservingEmb
  simp [show (default : Option (T ⊕ Γ₀)) = none from rfl]

theorem blankPreservingInv_emb {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    (γ : Γ₀) : blankPreservingInv (T := T) (blankPreservingEmb γ) = γ := by
  unfold blankPreservingEmb blankPreservingInv
  split <;> simp_all

/-- Embed a TM0 machine from `Γ₀` into `Option (T ⊕ Γ₀)`, preserving
the blank symbol. -/
noncomputable def embedTM0 {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ₀ Λ) :
    @TM0.Machine (Option (T ⊕ Γ₀)) Λ ⟨default⟩ :=
  TM0AlphabetSim.liftMachine M
    (blankPreservingEmb (T := T))
    (blankPreservingInv (T := T))

/-- The embedded TM preserves halting behavior. -/
theorem embedTM0_eval_dom {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ₀ Λ) (l : List Γ₀) :
    (TM0.eval M l).Dom ↔
    (@TM0.eval (Option (T ⊕ Γ₀)) Λ ⟨default⟩ _
      (embedTM0 M)
      (l.map (blankPreservingEmb (T := T)))).Dom :=
  TM0AlphabetSim.lift_eval_dom M _ _
    (blankPreservingInv_emb (T := T))
    (blankPreservingEmb_default (T := T))
    l

/-! ### The main encoding bridge -/

/-- **Encoding Bridge**: Any language over a `Fintype` alphabet that is
semidecidable via a `ToPartrec.Code` satisfies `is_TM`.

Given a Code `c` such that `w ∈ L ↔ (c.eval [Encodable.encode w]).Dom`,
we construct a TM0 over `Option (T ⊕ Γ)` with identity encoding that
recognizes `L`.

The proof constructs a combined TM in three phases:
1. **Encode**: Compute `Encodable.encode w` from the identity-encoded input.
2. **Format**: Convert the encoded number to the chain's tape format.
3. **Simulate**: Run the chain's TM0 via alphabet simulation.

See the module documentation for details. -/
theorem code_implies_isTM {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (L : Language T)
    (c : Turing.ToPartrec.Code)
    (hL : ∀ w : List T, w ∈ L ↔ (c.eval [Encodable.encode w]).Dom) :
    is_TM L := by
  sorry
