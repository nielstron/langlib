import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.DSL.AlphabetSim
import Langlib.Automata.Turing.DSL.Compile
import Langlib.Automata.Turing.DSL.TM0Compose
import Langlib.Automata.Turing.DSL.TapeConvert

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
   using a blank-preserving embedding (defined in `TapeConvert.lean`).

3. **Generalized Chain** (`code_to_tm0_fintype_general` in `ParrecChain.lean`):
   The chain works with arbitrary `v : List ℕ` input, not just `[n]`.
   The tape format `trInit K'.main (trList v)` decomposes per-element:
   `trList v = v.bind (fun n => trNat n ++ [cons])`.

4. **Sequential Composition** (`TM0Seq.compose` in `TM0Compose.lean`):
   Two TM0 machines can be sequentially composed. If M₁ halts producing
   tape T, the composed machine halts iff M₂ halts starting from T.

5. **Halting Converter Composition** (`tm0Realizes_compose_eval` in
   `TapeConvert.lean`): If a TM0 realizes a total function `f`, we can
   compose it with any machine `M₂` so the result halts on `l` iff
   `M₂` halts on `f l`.

## Architecture of `chain_encoding_bridge`

The bridge is proved by composing two machines:

- **Converter TM** (`converter_tm_exists`): A TM0 over `Option (T ⊕ ChainΓ)`
  that reads identity-encoded `w` and writes the chain tape format
  `(chainEncode T w).map blankPreservingEmb`.
  This machine always halts. Derived from `chain_converter_fn_realizes` in
  `TapeConvert.lean`.

- **Embedded chain TM** (`embedTM0 M₀`): The chain machine `M₀` lifted from
  `ChainΓ` to `Option (T ⊕ ChainΓ)` via blank-preserving embedding.

Sequential composition (`TM0Seq.compose`) chains these: first the converter
produces the chain-format tape, then `embedTM0 M₀` runs on it.

## Converter TM construction

The converter reads identity-encoded `w = [t₁, ..., tₙ]` and computes
`Encodable.encode w` via iterated `Nat.pair`:

- `Encodable.encode [] = 0`
- `Encodable.encode (t :: ts) = Nat.pair (Encodable.encode t) (Encodable.encode ts) + 1`

This requires binary arithmetic on the tape:
1. **Binary successor** (increment): propagate carry through little-endian bits
2. **Binary addition**: add two binary numbers via repeated increment/decrement
3. **Binary multiplication**: compute via repeated addition
4. **Binary comparison**: needed for `Nat.pair a b = if a < b then b*b+a else a*a+a+b`
5. **Nat.pair**: combine the above operations
6. **List fold**: iterate `Nat.pair` over the element encodings

Since `T` is `Fintype`, each `Encodable.encode t` is a fixed constant that
can be hardcoded in the TM's finite state.
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

/-! ### Building Block 3: Converter TM -/

/-- **Converter TM existence**: There exists a TM0 over `Option (T ⊕ ChainΓ)`
that reads identity-encoded input `w` and produces the chain tape format
on the tape.

Derived from `converter_fn_realizes` and `converter_fn_on_identity`
(both in `TapeConvert.lean`). -/
theorem converter_tm_exists {T : Type} [DecidableEq T] [Fintype T] [Primcodable T] :
    ∃ (Λ_conv : Type) (_ : Inhabited Λ_conv) (_ : Fintype Λ_conv)
      (M_conv : TM0.Machine (Option (T ⊕ ChainΓ)) Λ_conv),
      ∀ w : List T,
        (TM0Seq.evalCfg M_conv (w.map (fun x => some (Sum.inl x)))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M_conv (w.map (fun x => some (Sum.inl x)))).Dom),
          ((TM0Seq.evalCfg M_conv (w.map (fun x => some (Sum.inl x)))).get h).Tape =
            Tape.mk₁ ((chainEncode T w).map
                (blankPreservingEmb (T := T))) := by
  exact chain_converter_fn_realizes (T := T)

/-! ### Building Block 4: Chain-to-Identity Encoding Bridge -/

set_option maxHeartbeats 800000

/-- **Chain-to-identity encoding bridge**: Given the chain's TM0 `M₀` over
`ChainΓ`, there exists a TM0 over `Option (T ⊕ Γ)` with identity encoding
that simulates it.

**Proof**: We compose two machines via `TM0Seq.compose`:
1. The converter TM (`converter_tm_exists`) transforms identity-encoded
   input into the chain's tape format.
2. The embedded chain TM (`embedTM0 M₀`) simulates `M₀` on the
   chain-format tape.

By `TM0Seq.compose_dom_iff'`, the composition halts on identity input iff
`embedTM0 M₀` halts on the converter's output. By `embedTM0_eval_dom`,
this is equivalent to `M₀` halting on the original chain input. -/
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
  obtain ⟨Λ_conv, hΛci, hΛcf, M_conv, hconv⟩ := converter_tm_exists (T := T)
  refine ⟨ChainΓ, inferInstance, Λ_conv ⊕ Λ₀, ⟨Sum.inl default⟩, inferInstance,
    TM0Seq.compose M_conv (embedTM0 (T := T) M₀), fun w => ?_⟩
  have h1 := (hconv w).1
  have h2 := (hconv w).2 h1
  rw [show chainEncode T w = TM2to1.trInit PartrecToTM2.K'.main
    (PartrecToTM2.trList [Encodable.encode w]) from rfl] at h2
  rw [TM0Seq.compose_dom_iff' M_conv (embedTM0 (T := T) M₀) _ _ h1 h2]
  exact embedTM0_eval_dom M₀ _

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
  exact ⟨T ⊕ Γ, inferInstance, Λ, hΛi, hΛf, M, Sum.inl, fun w => by
    rw [hL, hM₀ (Encodable.encode w)]; exact hM w⟩
