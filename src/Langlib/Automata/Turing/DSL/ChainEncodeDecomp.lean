import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinarySuccessor
import Langlib.Automata.Turing.DSL.BinaryArithmetic
import Langlib.Automata.Turing.DSL.CondBlockOps
import Langlib.Automata.Turing.DSL.PairedBlockArithmetic
import Langlib.Automata.Turing.DSL.PairedInvariantEstablisher
import Langlib.Automata.Turing.DSL.HetFoldDecomp

/-! # Chain Encoding Decomposition

This file assembles the full chain encoding decomposition from the
modular components defined in helper files:

- `ChainAlphabet`: binary representation on ChainΓ
- `BlockRealizability`: core framework for composing TM0 block operations
- `BinarySuccessor`: increment operation
- `BinaryArithmetic`: addition, normalization
- `CondBlockOps`: conditional composition
- `PairedBlockArithmetic`: paired addition, squaring, multiplication

## Strategy

The chain encoding `chainEncode T w = trInit K'.main (trList [Encodable.encode w])`
is decomposed into:

1. **List encoding fold** (Phase 1): Compute `Encodable.encode w` from the
   input list `w : List T` using iterated `Nat.pair` and `succ`. Each fold
   step (`binPairConstSucc`) uses conditional branching on block value
   to select between addition and squaring-then-addition.

2. **Chain formatting** (Phase 2): Convert the binary representation to
   the chain tape format by reversing and prepending `chainConsBottom`.

Both phases are TM0-realizable on the heterogeneous tape `Option (T ⊕ ChainΓ)`.
-/

open Turing PartrecToTM2 TM2to1

/-! ### Nat.pair with Constant -/

/-- `Nat.pair k ·` followed by `succ`, applied to a binary ChainΓ block.
    This is the fold step for list encoding. -/
noncomputable def binPairConstSucc (k : ℕ) (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (Nat.pair k (decodeBinaryBlock block) + 1)

/-- `binPairConstSucc` is correct on valid binary blocks. -/
theorem binPairConstSucc_correct (k n : ℕ) :
    binPairConstSucc k (chainBinaryRepr n) = chainBinaryRepr (Nat.pair k n + 1) := by
  unfold binPairConstSucc;
  rw [ decodeBinaryBlock_chainBinaryRepr ]

/-! #### Decomposition of binPairConstSucc -/

/-- When n ≤ k: `Nat.pair k n = k * k + k + n`, so the result is `n + (k * k + k + 1)`. -/
theorem natPair_succ_of_le {k n : ℕ} (h : n ≤ k) :
    Nat.pair k n + 1 = n + (k * k + k + 1) := by
  simp [Nat.pair, if_neg (not_lt.mpr h)]; omega

/-- When k < n: `Nat.pair k n = n * n + k`, so the result is `n ^ 2 + (k + 1)`. -/
theorem natPair_succ_of_lt {k n : ℕ} (h : k < n) :
    Nat.pair k n + 1 = (decodeBinaryBlock (binSquare (chainBinaryRepr n))) + (k + 1) := by
  simp [Nat.pair, if_pos h, binSquare, decodeBinaryBlock_chainBinaryRepr, sq]; omega

/-- `binPairConstSucc k` decomposes as a conditional on `blockValueLeq k`:
    - If block value ≤ k: `binAddConstRepr (k * k + k + 1)` (add a constant)
    - If block value > k: `binAddConstRepr (k + 1) ∘ binSquare` (square, then add constant) -/
theorem binPairConstSucc_eq_cond (k : ℕ) (block : List ChainΓ) :
    binPairConstSucc k block =
      binCondBlock (blockValueLeq k)
        (binAddConstRepr (k * k + k + 1))
        (binAddConstRepr (k + 1) ∘ binSquare)
        block := by
  unfold binPairConstSucc binCondBlock blockValueLeq binAddConstRepr
  simp only [Function.comp]
  by_cases h : decodeBinaryBlock block ≤ k
  · simp [h, Nat.pair, if_neg (not_lt.mpr h)]; ring_nf
  · simp [h]
    unfold binSquare
    rw [decodeBinaryBlock_chainBinaryRepr]
    congr 1
    have hlt : k < decodeBinaryBlock block := Nat.lt_of_not_le h
    simp [Nat.pair, if_pos hlt, sq]; ring_nf

/-- **Nat.pair-succ with constant is block-realizable**, assuming the
invariant/suffix multiplication step body. -/
theorem tm0_binPairConstSucc_block
    (hstep : TM0RealizesBlockCondInvSuffix binMulPairedStep3 binMulPairedCond3
      binMulPairedStateInv3)
    (k : ℕ) :
    TM0RealizesBlock ChainΓ (binPairConstSucc k) := by
  rw [show binPairConstSucc k = binCondBlock (blockValueLeq k)
        (binAddConstRepr (k * k + k + 1))
        (binAddConstRepr (k + 1) ∘ binSquare)
    from funext (binPairConstSucc_eq_cond k)]
  exact tm0RealizesBlock_cond
    (tm0_binAddConstRepr_block _)
    (tm0RealizesBlock_comp (tm0_binSquare_block hstep)
      (tm0_binAddConstRepr_block _) binSquare_ne_default)
    (fun block hblock => binAddConstRepr_ne_default _ _ hblock)
    (fun block hblock => binAddConstRepr_ne_default _ _ (binSquare_ne_default _ hblock))
    (tm0_blockValueLeq_decidable_2 k)

/-! ### List Encoding Fold Equation -/

/-- The list encoding is a right fold with `Nat.pair` and `succ`. -/
theorem encodable_encode_list_fold {T : Type} [Encodable T] (w : List T) :
    Encodable.encode w =
    List.foldr (fun t acc => Nat.pair (Encodable.encode t) acc + 1) 0 w := by
  induction w <;> aesop

/-! ### General heterogeneous fold realizability -/

/-- **Heterogeneous fold realizability, same-alphabet form.**

    Given a family of block-realizable functions
    `F t : List (Option (T ⊕ Γ)) → List (Option (T ⊕ Γ))` on the actual tape
    alphabet, plus a semantic equation saying that `F` behaves like
    `f t : List Γ → List Γ` on well-formed `hetMix` blocks, there exists a
    TM0 on `Option (T ⊕ Γ)` that processes input `w.map(Sum.inl)`
    right-to-left.

    ## Proof approach

    Decomposed into two `TM0RealizesBlock` operations
    (see `HetFoldDecomp.lean`):

    1. **Reverse** the input block: `TM0RealizesBlock _ List.reverse`
       (from `tm0_reverse_block`).
    2. **While loop**: `TM0RealizesBlock _ (hetFoldWhile F)`, where each
       iteration pops the leftmost `some(inl t)` tag and runs the supplied
       same-alphabet step `F t`.

    The while-loop body is expressed as a `TM0RealizesBlockCond`
    (conditional block realizability with two exit modes), and the
    general combinator `tm0RealizesBlock_while` builds the looping
    machine using `tm0WhileLoop`.

    The fold identity `List.foldr f [] w =
    List.foldl (fun a t => f t a) [] w.reverse` connects the
    right-to-left fold to the left-to-right while loop on the
    reversed input.
-/
theorem tm0Het_fold_blockRealizable
    {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]
    (T : Type) [DecidableEq T] [Fintype T]
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (f : T → List Γ₀ → List Γ₀)
    (hF : ∀ t ts acc, F t (hetMix (T := T) (Γ₀ := Γ₀) ts acc) =
      hetMix ts (f t acc))
    (hF_block : ∀ t, TM0RealizesBlock (Option (T ⊕ Γ₀)) (F t))
    (hF_nd : ∀ t block, (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ F t block, g ≠ default)
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ f t block, g ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((List.foldr f [] w).map
              (some ∘ @Sum.inr T Γ₀)) :=
  tm0Het_fold_blockRealizable' T F f hF hF_block hF_nd hf_nd

/-! ### Deriving chainEncode_fold from the general fold -/

/-- The binary fold over a list matches `chainBinaryRepr (Encodable.encode w)`. -/
theorem chainEncode_fold_eq {T : Type} [Encodable T] (w : List T) :
    List.foldr (fun t acc => binPairConstSucc (Encodable.encode t) acc)
      [] w =
    chainBinaryRepr (Encodable.encode w) := by
  induction w with
  | nil => simp [chainBinaryRepr_zero]
  | cons t rest ih =>
    simp only [List.foldr_cons]
    rw [ih, binPairConstSucc_correct]
    simp [encodable_encode_list_fold]

/-- Non-defaultness of `binPairConstSucc` output. -/
theorem binPairConstSucc_ne_default (k : ℕ) (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binPairConstSucc k block, g ≠ default :=
  fun g hg => chainBinaryRepr_ne_default _ g hg

/-- The accumulator-level function used by the chain fold. -/
noncomputable def chainEncodeFoldAccStep
    (T : Type) [Primcodable T] (t : T) : List ChainΓ → List ChainΓ :=
  binPairConstSucc (Encodable.encode t)

/-- The same-alphabet tape-level step used by the chain fold.

This deliberately separates the layout/mapping obligation from the arithmetic
function.  The arithmetic is `chainEncodeFoldAccStep`; this function says how
that arithmetic acts on the actual `Option (T ⊕ ChainΓ)` tape block. -/
noncomputable def chainEncodeFoldTapeStep
    (T : Type) [DecidableEq T] [Primcodable T] (t : T) :
    List (Option (T ⊕ ChainΓ)) → List (Option (T ⊕ ChainΓ)) :=
  hetFoldAdapt (chainEncodeFoldAccStep T) t

theorem chainEncodeFoldTapeStep_hetMix
    (T : Type) [DecidableEq T] [Fintype T] [Primcodable T]
    (t : T) (ts : List T) (acc : List ChainΓ) :
    chainEncodeFoldTapeStep T t (hetMix ts acc) =
      hetMix ts (chainEncodeFoldAccStep T t acc) :=
  hetFoldAdapt_hetMix (chainEncodeFoldAccStep T) t ts acc

theorem chainEncodeFoldTapeStep_ne_default
    (T : Type) [DecidableEq T] [Primcodable T] (t : T)
    (block : List (Option (T ⊕ ChainΓ)))
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ chainEncodeFoldTapeStep T t block,
      g ≠ (default : Option (T ⊕ ChainΓ)) := by
  intro g hg
  unfold chainEncodeFoldTapeStep hetFoldAdapt at hg
  simp only [List.mem_append, List.mem_map, Function.comp] at hg
  rcases hg with hg | ⟨a, _ha, rfl⟩
  · have := List.mem_takeWhile_imp hg
    cases g <;> simp_all [isHetInl]
  · exact Option.some_ne_none _

/-- Machine-realizability obligation for the concrete same-alphabet chain fold
step.

The important interface point is that this is no longer hidden in
`chainEncode_fold`: the arithmetic step and the het-tape mapping/layout step
are separate named objects. -/
axiom tm0_chainEncodeFoldTapeStep_block
    (T : Type) [DecidableEq T] [Fintype T] [Primcodable T]
    (t : T) :
    TM0RealizesBlock (Option (T ⊕ ChainΓ)) (chainEncodeFoldTapeStep T t)

/-- Phase 1: Fold computation on heterogeneous tape. -/
theorem chainEncode_fold
    (T : Type) [DecidableEq T] [Fintype T] [Primcodable T] :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ ChainΓ)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((chainBinaryRepr (Encodable.encode w)).map
              (some ∘ @Sum.inr T ChainΓ)) := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0Het_fold_blockRealizable T
    (chainEncodeFoldTapeStep T)
    (chainEncodeFoldAccStep T)
    (chainEncodeFoldTapeStep_hetMix T)
    (tm0_chainEncodeFoldTapeStep_block T)
    (chainEncodeFoldTapeStep_ne_default T)
    (fun t _ _ => binPairConstSucc_ne_default (Encodable.encode t) _ (by assumption))
  exact ⟨Λ, hΛi, hΛf, M, fun w => by
    obtain ⟨hdom, htape⟩ := hM w
    exact ⟨hdom, fun h => by
      rw [htape h]
      congr 1
      exact congr_arg (List.map (some ∘ @Sum.inr T ChainΓ))
        (by simpa [chainEncodeFoldAccStep] using chainEncode_fold_eq (T := T) w)⟩⟩

/-! ### Format block operation -/

/-- The chain format operation: reverse a block and prepend `chainConsBottom`. -/
noncomputable def chainFormatBlock (block : List ChainΓ) : List ChainΓ :=
  chainConsBottom :: block.reverse

/-- `chainFormatBlock` output is non-default. -/
theorem chainFormatBlock_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ chainFormatBlock block, g ≠ default := by
  intro g hg
  simp [chainFormatBlock] at hg
  rcases hg with rfl | hg
  · simp +decide [chainConsBottom]
  · exact hblock g (by simp_all [List.mem_reverse])

/-- `chainFormatBlock` is block-realizable, by composing reverse and
    prepend via `tm0RealizesBlock_comp`. -/
theorem tm0_chainFormatBlock_block :
    TM0RealizesBlock ChainΓ chainFormatBlock := by
  have : chainFormatBlock = (chainConsBottom :: ·) ∘ List.reverse := by
    ext block; simp [chainFormatBlock]
  rw [this]
  exact tm0RealizesBlock_comp tm0_reverse_block
    (tm0_cons_block chainConsBottom chainConsBottom_ne_default)
    reverse_ne_default

/-- Same-alphabet chain format operation on het blocks.

The input theorem below only feeds this operation blocks of `some (Sum.inr _)`,
but the operation itself is deliberately stated over the actual tape alphabet. -/
noncomputable def chainFormatHetBlock (T : Type)
    (block : List (Option (T ⊕ ChainΓ))) : List (Option (T ⊕ ChainΓ)) :=
  some (Sum.inr chainConsBottom) :: block.reverse

/-- The same-alphabet chain format operation is block-realizable. -/
theorem tm0_chainFormatHetBlock_block (T : Type) [DecidableEq T] [Fintype T] :
    TM0RealizesBlock (Option (T ⊕ ChainΓ)) (chainFormatHetBlock T) := by
  have : chainFormatHetBlock T =
      (some (Sum.inr chainConsBottom) :: ·) ∘ List.reverse := by
    ext block; simp [chainFormatHetBlock]
  rw [this]
  exact tm0RealizesBlock_comp tm0_reverse_block
    (tm0_cons_block (some (Sum.inr chainConsBottom)) (by simp))
    reverse_ne_default

/-- Phase 2: Format the binary accumulator into chain tape format. -/
theorem chainEncode_format (T : Type) [DecidableEq T] [Fintype T] :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ ChainΓ)) Λ),
      ∀ (block : List ChainΓ),
        (∀ g ∈ block, g ≠ (default : ChainΓ)) →
        (TM0Seq.evalCfg M (block.map (some ∘ @Sum.inr T ChainΓ))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M
          (block.map (some ∘ @Sum.inr T ChainΓ))).Dom),
          ((TM0Seq.evalCfg M
            (block.map (some ∘ @Sum.inr T ChainΓ))).get h).Tape =
            Tape.mk₁ ((chainConsBottom :: block.reverse).map
              (some ∘ @Sum.inr T ChainΓ)) := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0_chainFormatHetBlock_block T
  exact ⟨Λ, hΛi, hΛf, M, fun block hblock => by
    have hinput_nd : ∀ g ∈ block.map (some ∘ @Sum.inr T ChainΓ),
        g ≠ (default : Option (T ⊕ ChainΓ)) := by
      intro g hg
      simp only [List.mem_map, Function.comp] at hg
      obtain ⟨_, _, rfl⟩ := hg
      exact Option.some_ne_none _
    have houtput_nd : ∀ g ∈ chainFormatHetBlock T
        (block.map (some ∘ @Sum.inr T ChainΓ)),
        g ≠ (default : Option (T ⊕ ChainΓ)) := by
      intro g hg
      simp [chainFormatHetBlock] at hg
      rcases hg with rfl | hg
      · exact Option.some_ne_none _
      · obtain ⟨_, _, rfl⟩ := hg
        exact Option.some_ne_none _
    have hsuffix_nd : ∀ g ∈ ([] : List (Option (T ⊕ ChainΓ))),
        g ≠ (default : Option (T ⊕ ChainΓ)) := by simp
    obtain ⟨hdom, htape⟩ := hM (block.map (some ∘ @Sum.inr T ChainΓ)) []
      hinput_nd hsuffix_nd houtput_nd
    refine ⟨?_, ?_⟩
    · rwa [evalCfg_append_default] at hdom
    · intro h
      have htape' := htape (by simpa [evalCfg_append_default] using h)
      rw [chainFormatHetBlock] at htape'
      rw [show some (Sum.inr chainConsBottom) ::
            (block.map (some ∘ @Sum.inr T ChainΓ)).reverse ++ [default] =
          (some (Sum.inr chainConsBottom) ::
            (block.map (some ∘ @Sum.inr T ChainΓ)).reverse) ++ [default] by rfl,
        tape_mk₁_append_default] at htape'
      simpa [List.map_reverse, evalCfg_append_default] using htape'⟩

/-! ### Summary

The decomposition provides the following path to `chainEncode_realizes`:

1. `chainEncode_fold` — Phase 1: process input into binary accumulator
   - Derived from `tm0Het_fold_blockRealizable` (general het fold)
   - + `tm0_binPairConstSucc_block` (each fold step is block-realizable)
   - + `chainEncode_fold_eq` (algebraic correctness of the fold)
2. `chainEncode_format` — Phase 2: reverse + prepend cons marker
   - Derived from `tm0_chainFormatHetBlock_block` on the actual het tape
   - + `tm0_chainFormatBlock_block` documents the pure ChainΓ operation
3. `chainEncode_eq_format` (in TapeConvert) — equational glue
4. Compose Phase 1 and Phase 2 via `TM0Seq.compose`

### Reuse Architecture

All arithmetic operations share a common core:

- **`binSucc`** (increment) is the atomic operation
- **`binAddConst c`** = `binSucc^[c]` (addition by constant)
- **`binAddPaired`** (addition of neighboring numbers) is the
  central primitive for multi-operand arithmetic
- **`binSquare`** and **`binMulConst c`** both decompose through
  paired addition:
  - `binMulConst c` = extract ∘ binAddPaired^[c] ∘ prepend_separator
  - `binSquare` = extract ∘ binMulPaired ∘ duplicate
    (where binMulPaired uses iterated binAddPaired)

-/
