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

## Remaining sorry

`code_implies_isTM` requires constructing a TM0 over `Option (T ⊕ Γ)` that,
given identity-encoded `w`, simulates the chain's TM0 on
`encode_input (Encodable.encode w)`. This involves:

1. **Reading identity-encoded input**: The TM reads `w = [t₁, ..., tₙ]`
   from the tape where each `tᵢ` is represented as `some (Sum.inl tᵢ)`.

2. **Computing `Encodable.encode w`**: Since `T` is `Fintype`, each
   `Encodable.encode tᵢ` is bounded by `Fintype.card T - 1`. The encoding
   is computed by iterated `Nat.pair`: `encode (t :: ts) = (Nat.pair (encode t)
   (encode ts)).succ`. This requires binary multiplication and comparison
   on the tape (for `Nat.pair a b = if a ≤ b then b² + a else a² + a - b`).

3. **Formatting as chain tape**: Convert the binary representation to the
   chain's `trInit K'.main (trList [·])` format.

4. **Simulating the chain TM**: Run the chain's TM0 using the alphabet
   embedding (already proved via `embedTM0_eval_dom`).

Step 2 is the core difficulty: it requires implementing binary arithmetic
(multiplication, comparison, addition, subtraction) on a TM tape. This is
a standard but substantial construction (~500 lines).
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

/-! ### Main Theorem -/

/-- **Code implies is_TM**: Any language over a `Fintype` alphabet that is
semidecidable via a `ToPartrec.Code` satisfies `is_TM`.

Given a Code `c` such that `w ∈ L ↔ (c.eval [Encodable.encode w]).Dom`,
we construct a TM0 over `Option (T ⊕ Γ)` with identity encoding that
recognizes `L`.

**Proof strategy**: Use `code_to_tm0_fintype c` to get a chain TM0 `M₀`
over `Γ₀`, then construct a TM over `Option (T ⊕ Γ₀)` that:
1. Preprocesses identity-encoded `w` into `encode_input (Encodable.encode w)`
   embedded via `blankPreservingEmb` (requires tape-based `Nat.pair` arithmetic)
2. Simulates `M₀` via `embedTM0` (already proved)

The equivalence chain is:
  `w ∈ L ↔ c.eval [encode w] ↔ TM0.eval M₀ (encode_input (encode w))
         ↔ TM0.eval M_emb (encode_input (encode w)).map emb
         ↔ TM0.eval M (w.map identity_encode)` -/
theorem code_implies_isTM {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (L : Language T)
    (c : Turing.ToPartrec.Code)
    (hL : ∀ w : List T, w ∈ L ↔ (c.eval [Encodable.encode w]).Dom) :
    is_TM L := by
  sorry
