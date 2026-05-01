import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinarySuccessor
import Langlib.Automata.Turing.DSL.BinaryArithmetic
import Langlib.Automata.Turing.DSL.CondBlockOps
import Langlib.Automata.Turing.DSL.PairedBlockArithmetic
import Langlib.Automata.Turing.DSL.AlphabetSim

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

/-- **Nat.pair-succ with constant is block-realizable.** -/
theorem tm0_binPairConstSucc_block (k : ℕ) :
    TM0RealizesBlock ChainΓ (binPairConstSucc k) := by
  rw [show binPairConstSucc k = binCondBlock (blockValueLeq k)
        (binAddConstRepr (k * k + k + 1))
        (binAddConstRepr (k + 1) ∘ binSquare)
    from funext (binPairConstSucc_eq_cond k)]
  exact tm0RealizesBlock_cond
    (tm0_binAddConstRepr_block _)
    (tm0RealizesBlock_comp tm0_binSquare_block (tm0_binAddConstRepr_block _) binSquare_ne_default)
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

/-- **Heterogeneous fold realizability.**

    Given a family of block-realizable functions `f t : List Γ → List Γ`
    indexed by `t : T` (Fintype), there exists a TM0 on `Option (T ⊕ Γ)`
    that processes input `w.map(Sum.inl)` right-to-left, applying `f tᵢ`
    to the `Sum.inr` accumulator for each element.

    ## Proof approach (not yet formalized)

    The machine operates as a loop:
    1. **Scan** right to find the rightmost `some (Sum.inl t)` cell.
    2. **Read** the value `t : T` and **erase** it (write `none`).
    3. **Dispatch** based on `t`: for each `t ∈ T`, use the lifted
       machine from `tm0Het_liftBlockToHet T (f t) (hf_block t)` to
       apply `f t` to the `Sum.inr` accumulator.
    4. **Loop** back to step 1.
    5. **Halt** when no `Sum.inl` cells remain.

    Since `T` is a `Fintype`, the dispatch uses finitely many sub-machines,
    and the combined machine has finitely many states. The key building
    blocks are:
    - `tm0Het_liftBlockToHet` (already proven) for each `t ∈ T`
    - A scan machine for finding `Sum.inl` cells
    - A dispatch mechanism (finite case split on `t`)
    - A loop combinator (similar to `tm0WhileLoop` from PairedAddHelpers)
-/
theorem tm0Het_fold_blockRealizable
    {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]
    (T : Type) [DecidableEq T] [Fintype T]
    (f : T → List Γ₀ → List Γ₀)
    (hf_block : ∀ t, TM0RealizesBlock Γ₀ (f t))
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ f t block, g ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((List.foldr f [] w).map
              (some ∘ @Sum.inr T Γ₀)) := by
  sorry

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

/-- Phase 1: Fold computation on heterogeneous tape. -/
theorem chainEncode_fold (T : Type) [DecidableEq T] [Fintype T] [Primcodable T] :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ ChainΓ)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((chainBinaryRepr (Encodable.encode w)).map
              (some ∘ @Sum.inr T ChainΓ)) := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0Het_fold_blockRealizable T
    (fun t => binPairConstSucc (Encodable.encode t))
    (fun t => tm0_binPairConstSucc_block (Encodable.encode t))
    (fun t _ _ => binPairConstSucc_ne_default (Encodable.encode t) _ (by assumption))
  exact ⟨Λ, hΛi, hΛf, M, fun w => by
    obtain ⟨hdom, htape⟩ := hM w
    exact ⟨hdom, fun h => by rw [htape h, chainEncode_fold_eq]⟩⟩

/-! ### Lifting block-realizability to heterogeneous tape -/

/-- Embedding from Γ₀ to Option (T ⊕ Γ₀): default ↦ none, g ↦ some (inr g). -/
noncomputable def hetEmb {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) : Option (T ⊕ Γ₀) :=
  if g = default then none else some (Sum.inr g)

/-- Inverse of hetEmb: none ↦ default, some (inr g) ↦ g, some (inl _) ↦ default. -/
def hetInv {Γ₀ : Type} [Inhabited Γ₀] (T : Type) : Option (T ⊕ Γ₀) → Γ₀
  | none => default
  | some (Sum.inr g) => g
  | some (Sum.inl _) => default

theorem hetInv_hetEmb {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) : hetInv T (hetEmb T g) = g := by
  simp [hetEmb, hetInv]; split_ifs <;> simp_all

theorem hetEmb_default {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) : hetEmb T (default : Γ₀) = (none : Option (T ⊕ Γ₀)) := by
  simp [hetEmb]

theorem hetEmb_ne_default {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) (hg : g ≠ default) :
    hetEmb T g = some (Sum.inr g) := by
  simp [hetEmb, hg]

theorem map_hetEmb_block {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (block : List Γ₀) (hblock : ∀ g ∈ block, g ≠ default) :
    block.map (hetEmb T) = block.map (some ∘ @Sum.inr T Γ₀) := by
  simp only [List.map_inj_left]
  intro g hg
  exact hetEmb_ne_default T g (hblock g hg)

theorem tm0Het_liftBlockToHet
    {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]
    (T : Type) [DecidableEq T]
    (f : List Γ₀ → List Γ₀)
    (hf : TM0RealizesBlock Γ₀ f) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ (block : List Γ₀),
        (∀ g ∈ block, g ≠ default) →
        (∀ g ∈ f block, g ≠ default) →
        (TM0Seq.evalCfg M (block.map (some ∘ @Sum.inr T Γ₀))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M
          (block.map (some ∘ @Sum.inr T Γ₀))).Dom),
          ((TM0Seq.evalCfg M
            (block.map (some ∘ @Sum.inr T Γ₀))).get h).Tape =
            Tape.mk₁ ((f block).map (some ∘ @Sum.inr T Γ₀)) := by
  obtain ⟨ Λ, _, _, M, hM ⟩ := hf;
  refine' ⟨ Λ, _, _, TM0AlphabetSim.liftMachine M ( hetEmb T ) ( hetInv T ), _ ⟩;
  · infer_instance;
  · intro block hblock hfblock
    obtain ⟨h_dom, h_tape⟩ := hM block [] hblock (by simp) hfblock;
    have h_lift : ∃ b₂, TM0AlphabetSim.liftRel (hetEmb T) (hetInv T) (hetInv_hetEmb T) (hetEmb_default T) ((TM0Seq.evalCfg M (block ++ [default])).get h_dom) b₂ ∧ b₂ ∈ TM0Seq.evalCfg (TM0AlphabetSim.liftMachine M (hetEmb T) (hetInv T)) (List.map (some ∘ Sum.inr) block) := by
      convert Turing.tr_eval _ _ _;
      exact TM0.step M;
      exact?;
      exact TM0.init ( block ++ [ default ] );
      · simp +decide [ TM0AlphabetSim.liftRel, TM0.init ];
        rw [ tape_mk₁_append_default ];
        unfold TM0AlphabetSim.embPM; simp +decide [ Tape.map_mk₁ ] ;
        rw [ map_hetEmb_block ];
        assumption;
      · exact?;
    obtain ⟨ b₂, hb₂₁, hb₂₂ ⟩ := h_lift;
    have h_tape_b₂ : b₂.Tape = Tape.mk₁ ((f block ++ [default]).map (TM0AlphabetSim.embPM (hetEmb T) (hetEmb_default T))) := by
      obtain ⟨ h₁, h₂ ⟩ := hb₂₁;
      rw [ h₂, h_tape h_dom ];
      exact?;
    have h_tape_b₂_simplified : b₂.Tape = Tape.mk₁ ((f block).map (some ∘ Sum.inr) ++ [none]) := by
      convert h_tape_b₂ using 2;
      simp +decide [ TM0AlphabetSim.embPM, hetEmb ];
      exact hfblock;
    have h_tape_b₂_final : b₂.Tape = Tape.mk₁ ((f block).map (some ∘ Sum.inr)) := by
      convert tape_mk₁_append_default ( List.map ( some ∘ Sum.inr ) ( f block ) ) using 1;
    cases hb₂₂ ; aesop

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

/-- Phase 2: Format the binary accumulator into chain tape format. -/
theorem chainEncode_format (T : Type) [DecidableEq T] :
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
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0Het_liftBlockToHet T
    chainFormatBlock tm0_chainFormatBlock_block
  exact ⟨Λ, hΛi, hΛf, M, fun block hblock => by
    exact hM block hblock (chainFormatBlock_ne_default block hblock)⟩

/-! ### Summary

The decomposition provides the following path to `chainEncode_realizes`:

1. `chainEncode_fold` — Phase 1: process input into binary accumulator
   - Derived from `tm0Het_fold_blockRealizable` (general het fold)
   - + `tm0_binPairConstSucc_block` (each fold step is block-realizable)
   - + `chainEncode_fold_eq` (algebraic correctness of the fold)
2. `chainEncode_format` — Phase 2: reverse + prepend cons marker
   - Derived from `tm0Het_liftBlockToHet` (lift block-op to het tape)
   - + `tm0_chainFormatBlock_block` (reverse+prepend is block-realizable)
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
