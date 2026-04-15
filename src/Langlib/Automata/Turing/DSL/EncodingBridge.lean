import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.DSL.AlphabetSim
import Langlib.Automata.Turing.DSL.Compile

/-! # Encoding Bridge: from Code-semidecidable languages to `is_TM`

The compilation chain (Partrec → Code → TM2 → TM1 → TM0) produces a TM0
machine whose input is encoded via `Encodable.encode` and the chain's tape
format (`trInit`, `trList`). The `is_TM` definition, however, requires the
input to be given in "identity encoding": `w.map (fun x => some (Sum.inl x))`.

This file bridges that gap.

## Proved building blocks

1. **Encoding Identity** (`list_encode_eq`):
   `Encodable.encode (w : List T) = Encodable.encode (w.map Encodable.encode : List ℕ)`.
   This means encoding the whole list at once equals encoding element-by-element.

2. **Alphabet Embedding** (`embedTM0` / `embedTM0_eval_dom`):
   Lifts a TM0 from `Γ₀` to `Option (T ⊕ Γ₀)` while preserving halting,
   using a blank-preserving embedding.

3. **Generalized Chain** (`code_to_tm0_fintype_general` in `ParrecChain.lean`):
   The chain works with arbitrary `v : List ℕ` input, not just `[n]`.
   The tape format `trInit K'.main (trList v)` decomposes per-element:
   `trList v = v.bind (fun n => trNat n ++ [cons])`.

## Remaining sorry: `identity_encoding_bridge`

The one remaining gap is converting identity-encoded input to the chain's
tape format. This requires a TM0 that:

1. Reads `w = [t₁, ..., tₙ]` from the tape (identity encoding)
2. Computes `Encodable.encode w` via iterated `Nat.pair`
3. Formats the result as `trInit K'.main (trList [Encodable.encode w])`
4. Simulates the chain TM via alphabet embedding

Step 2 requires binary arithmetic on the tape. This is a standard but
substantial TM construction (~300-500 lines).

**Note on the multi-element approach**: One might hope to avoid `Nat.pair`
by passing `w.map Encodable.encode` (per-element encodings) to the chain
instead of `[Encodable.encode w]` (single number). However, the Code model
(`ToPartrec.Code.eval`) cannot distinguish `[]` from `[0]` as inputs
(both have `headI = 0`, `tail = []`), so Code composition for variable-length
list encoding is not possible within the Code formalism. The generalized
chain (`code_to_tm0_fintype_general`) is proved but cannot be leveraged
here without a Code that folds list encoding.
-/

open Turing

/-! ### Building Block 1: Encoding Identity -/

/-- The encoding of a list `w : List T` equals the encoding of the list
of element-wise encodings `w.map Encodable.encode : List ℕ`.

This holds because `Encodable.encode (n : ℕ) = n` (the encoding of a
natural number is itself). -/
theorem list_encode_eq {T : Type} [Encodable T] (w : List T) :
    Encodable.encode w = Encodable.encode (w.map Encodable.encode : List ℕ) := by
  induction w <;> simp_all +decide

/-! ### Building Block 2: Alphabet Embedding -/

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
    TM0.Machine (Option (T ⊕ Γ₀)) Λ :=
  TM0AlphabetSim.liftMachine M
    (blankPreservingEmb (T := T))
    (blankPreservingInv (T := T))

/-- The embedded TM preserves halting behavior. -/
theorem embedTM0_eval_dom {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ₀ Λ) (l : List Γ₀) :
    (TM0.eval M l).Dom ↔
    (TM0.eval (embedTM0 (T := T) M)
      (l.map (blankPreservingEmb (T := T)))).Dom :=
  TM0AlphabetSim.lift_eval_dom M _ _
    (blankPreservingInv_emb (T := T))
    (blankPreservingEmb_default (T := T))
    l

/-! ### Building Block 3: Chain-to-Identity Encoding Bridge -/

/-- **Chain-to-identity encoding bridge**: Given the chain's TM0 `M₀` over
`ChainΓ`, there exists a TM0 over `Option (T ⊕ Γ)` with identity encoding
that simulates it.

The chain encoding `trInit K'.main (trList [n])` decomposes as:
- `trList [n] = trNat n ++ [Γ'.cons]` (binary digits + cons marker)
- `trInit K'.main` reverses and wraps with stack markers
- `trNat n` is little-endian binary using `Γ'.bit0`/`Γ'.bit1`

The construction requires a TM that reads identity-encoded `w`, computes
`Encodable.encode w` via iterated `Nat.pair` (binary arithmetic on the
tape), formats the result into the chain's tape layout, and simulates
`M₀` via `embedTM0`. Computing `Nat.pair` requires binary multiplication,
comparison, addition, and subtraction — standard but substantial. -/
theorem chain_encoding_bridge {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    {Λ₀ : Type} [Inhabited Λ₀] [Fintype Λ₀]
    (M₀ : TM0.Machine ChainΓ Λ₀) :
    ∃ (Γ : Type) (_ : Fintype Γ)
      (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ)) Λ),
      ∀ w : List T,
        (TM0.eval M₀
          (TM2to1.trInit PartrecToTM2.K'.main
            (PartrecToTM2.trList [Encodable.encode w]))).Dom ↔
        (TM0.eval M (w.map (fun x => some (Sum.inl x)))).Dom := by
  sorry

/-! ### Main Theorem -/

/-- **Code implies is_TM**: Any language over a `Fintype` alphabet that is
semidecidable via a `ToPartrec.Code` satisfies `is_TM`.

**Proof**: `code_to_tm0_fintype` gives a chain TM0 `M₀` over `ChainΓ` with
the concrete encoding `trInit K'.main (trList [n])`. Then
`chain_encoding_bridge` converts to identity encoding. -/
theorem code_implies_isTM {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (L : Language T)
    (c : Turing.ToPartrec.Code)
    (hL : ∀ w : List T, w ∈ L ↔ (c.eval [Encodable.encode w]).Dom) :
    is_TM L := by
  obtain ⟨Λ₀, hΛ₀i, hΛ₀f, M₀, hM₀⟩ := code_to_tm0_fintype c
  obtain ⟨Γ, hΓf, Λ, hΛi, hΛf, M, hM⟩ :=
    chain_encoding_bridge (T := T) M₀
  exact ⟨Γ, hΓf, Λ, hΛi, hΛf, M, fun w => by
    rw [hL, hM₀ (Encodable.encode w), hM w]⟩
