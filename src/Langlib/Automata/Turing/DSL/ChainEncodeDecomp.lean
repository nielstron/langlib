import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinarySuccessor
import Langlib.Automata.Turing.DSL.BinaryArithmetic
import Langlib.Automata.Turing.DSL.CondBlockOps
import Langlib.Automata.Turing.DSL.PairedBlockArithmetic
import Langlib.Automata.Turing.DSL.PairedInvariantEstablisher
import Langlib.Automata.Turing.DSL.HetFoldDecomp
import Langlib.Automata.Turing.DSL.BlockSepPrefix
import Langlib.Automata.Turing.DSL.HetLift

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
    (tm0RealizesBlock_comp
      (tm0_binSquare_block tm0_binMulPairedStep3_blockCondInvSuffix)
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
    (hF_body : TM0RealizesHetFoldBody (T := T) (Γ₀ := Γ₀) F)
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
  tm0Het_fold_blockRealizable' T F f hF hF_body hF_nd hf_nd

/-! ### Algebraic chain-encoding fold facts -/

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

theorem binPairConstSucc_no_of_ne_bits (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (k : ℕ) (block : List ChainΓ) :
    ∀ g ∈ binPairConstSucc k block, g ≠ sep := by
  unfold binPairConstSucc
  exact chainBinaryRepr_no_of_ne_bits sep hsep0 hsep1 _

/-- Separator/any-suffix realization of `binPairConstSucc`, factored through
an any-suffix square realization.

The remaining real obligation for the chain fold is therefore isolated to
`binSquare`: the conditional and constant-addition branches compose without
mentioning a concrete separator. -/
theorem tm0_binPairConstSucc_blockSepAnySuffix_of_square
    {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (k : ℕ)
    (hsquare : TM0RealizesBlockSepAnySuffix ChainΓ sep binSquare) :
    TM0RealizesBlockSepAnySuffix ChainΓ sep (binPairConstSucc k) := by
  rw [show binPairConstSucc k = binCondBlock (blockValueLeq k)
        (binAddConstRepr (k * k + k + 1))
        (binAddConstRepr (k + 1) ∘ binSquare)
    from funext (binPairConstSucc_eq_cond k)]
  exact tm0RealizesBlockSepAnySuffix_cond
    (tm0_binAddConstRepr_blockSepAnySuffix hsep0 hsep1 _)
    (tm0RealizesBlockSepAnySuffix_comp
      hsquare
      (tm0_binAddConstRepr_blockSepAnySuffix hsep0 hsep1 _)
      binSquare_ne_default
      (fun block _hblock => binSquare_no_of_ne_bits sep hsep0 hsep1 block))
    (fun block hblock => binAddConstRepr_ne_default _ _ hblock)
    (fun block _hblock =>
      by
        unfold binAddConstRepr
        exact chainBinaryRepr_no_of_ne_bits sep hsep0 hsep1 _)
    (fun block hblock =>
      binAddConstRepr_ne_default _ _ (binSquare_ne_default _ hblock))
    (fun block _hblock =>
      by
        unfold Function.comp binAddConstRepr
        exact chainBinaryRepr_no_of_ne_bits sep hsep0 hsep1 _)
    (tm0_blockValueLeq_beforeSep_decidable_plain_2 k sep)

theorem tm0_binPairConstSucc_blockAnySuffix (k : ℕ) :
    TM0RealizesBlockAnySuffix ChainΓ (binPairConstSucc k) := by
  exact tm0RealizesBlockAnySuffix_of_sep_default
    (tm0_binPairConstSucc_blockSepAnySuffix_of_square
      (sep := (default : ChainΓ))
      (by
        intro h
        have := congrArg (fun x : ChainΓ => x.2 K'.main) h
        simp [γ'ToChainΓ] at this)
      (by
        intro h
        have := congrArg (fun x : ChainΓ => x.2 K'.main) h
        simp [γ'ToChainΓ] at this)
      k
      (tm0RealizesBlockSepAnySuffix_default_of_block
        (tm0_binSquare_blockAnySuffix
          tm0_binMulPairedStep3_blockCondInvSepAnySuffix_default)))

theorem tm0_binPairConstSucc_blockSepAnySuffix_consBottom (k : ℕ) :
    TM0RealizesBlockSepAnySuffix ChainΓ chainConsBottom
      (binPairConstSucc k) := by
  exact tm0_binPairConstSucc_blockSepAnySuffix_of_square
    (sep := chainConsBottom)
    (by decide)
    (by decide)
    k
    (tm0_binSquare_blockSepAnySuffix_consBottom
      (tm0_binMulPairedStep3_blockCondInvSepAnySuffix
        (outerSep := chainConsBottom)
        (by simpa [binMulStateSep₂] using Ne.symm chainMulSep₂_ne_chainConsBottom)))

/-- The accumulator-level function used by the chain fold. -/
noncomputable def chainEncodeFoldAccStep
    (T : Type) [Primcodable T] (t : T) : List ChainΓ → List ChainΓ :=
  binPairConstSucc (Encodable.encode t)

/-- The same-alphabet tape-level step used by the chain fold.

This deliberately separates the layout/mapping obligation from the arithmetic
function.  The arithmetic is `chainEncodeFoldAccStep`; this function says how
that arithmetic acts on the actual `Option (T ⊕ ChainΓ)` tape block. -/
noncomputable def chainEncodeFoldTapeStepSep
    (T : Type) [DecidableEq T] [Primcodable T]
    (sep : Option (T ⊕ ChainΓ)) (t : T) :
    List (Option (T ⊕ ChainΓ)) → List (Option (T ⊕ ChainΓ)) :=
  hetFoldAdaptSep sep (chainEncodeFoldAccStep T) t

/-- Default separator instantiation of `chainEncodeFoldTapeStepSep`. -/
noncomputable def chainEncodeFoldTapeStep
    (T : Type) [DecidableEq T] [Primcodable T] (t : T) :
    List (Option (T ⊕ ChainΓ)) → List (Option (T ⊕ ChainΓ)) :=
  chainEncodeFoldTapeStepSep T (hetSep (T := T) (Γ₀ := ChainΓ)) t

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
  unfold chainEncodeFoldTapeStep chainEncodeFoldTapeStepSep hetFoldAdaptSep separatedAccLift at hg
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with hfront | hacc
  · rcases hfront with htag | hsep
    · have := List.mem_takeWhile_imp htag
      cases g <;> simp_all [isHetInl]
    · rw [hsep]
      simp [hetSep]
  · rcases hacc with ⟨a, _ha, hg⟩
    rw [← hg]
    simp [hetAccEmb]

/-- The operation induced on the accumulator cells of a het fold body.

The inner block contains only `some (inr γ)` cells. We decode those cells,
run the accumulator arithmetic, and re-embed into the same het alphabet. -/
noncomputable def chainEncodeFoldInnerStep
    (T : Type) [Primcodable T] (t : T) :
    List (Option (T ⊕ ChainΓ)) → List (Option (T ⊕ ChainΓ)) :=
  fun inner =>
    (chainEncodeFoldAccStep T t
      (inner.filterMap (hetAccDecode (T := T)))).map (hetAccEmb (T := T))

theorem filterMap_hetAccDecode_map_hetAccEmb
    (T : Type) (acc : List ChainΓ) :
    (acc.map (hetAccEmb (T := T))).filterMap (hetAccDecode (T := T)) = acc := by
  induction acc with
  | nil => simp
  | cons g acc ih => simp [hetAccEmb, hetAccDecode, ih]

theorem filterMap_hetAccDecode_comp_hetAccEmb
    (T : Type) (acc : List ChainΓ) :
    acc.filterMap (hetAccDecode (T := T) ∘ hetAccEmb (T := T)) = acc := by
  induction acc with
  | nil => simp
  | cons g acc ih => simp [Function.comp, hetAccEmb, hetAccDecode, ih]

theorem chainEncodeFoldInnerStep_on_acc
    (T : Type) [Primcodable T] (t : T) (acc : List ChainΓ) :
    chainEncodeFoldInnerStep T t (acc.map (hetAccEmb (T := T))) =
      (chainEncodeFoldAccStep T t acc).map (hetAccEmb (T := T)) := by
  simp [chainEncodeFoldInnerStep, List.filterMap_map,
    filterMap_hetAccDecode_comp_hetAccEmb]

theorem map_hetInv_hetAccEmb
    (T : Type) (acc : List ChainΓ) :
    acc.map (hetInv T ∘ hetAccEmb (T := T)) = acc := by
  induction acc with
  | nil => rfl
  | cons a acc ih => simp [Function.comp, hetAccEmb, hetInv, ih]

theorem map_hetInv_accBlock_sep_suffix
    (T : Type) (acc : List ChainΓ)
    (suffix : List (Option (T ⊕ ChainΓ))) :
    (((acc.map (hetAccEmb (T := T))) ++
      hetSep (T := T) (Γ₀ := ChainΓ) :: suffix).map (hetInv T)) =
      acc ++ default :: suffix.map (hetInv T) := by
  simp [List.map_append, map_hetInv_hetAccEmb, hetSep, hetInv]

/-- Separator-delimited block realizability with a block invariant.

This is the right shape for het accumulator blocks: a machine can be required
to work only on cells satisfying the layout invariant, instead of pretending
it handles arbitrary cells from the ambient alphabet. -/
def TM0RealizesBlockSepInv (Γ : Type) [Inhabited Γ] (sep : Γ)
    (f : List Γ → List Γ) (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (block suffix : List Γ),
      blockInv block →
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ block, g ≠ sep) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (∀ g ∈ f block, g ≠ sep) →
      (TM0Seq.evalCfg M (block ++ sep :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ sep :: suffix)).Dom),
        ((TM0Seq.evalCfg M (block ++ sep :: suffix)).get h).Tape =
          Tape.mk₁ (f block ++ sep :: suffix)

/-- Default-delimited inner-block realizability with an invariant on the inner
block between the explicit separator and the final blank. -/
def TM0RealizesInnerBlockDefaultSepInv (Γ : Type) [Inhabited Γ] (sep₂ : Γ)
    (f : List Γ → List Γ) (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (pfx inner : List Γ),
      blockInv inner →
      (∀ g ∈ pfx, g ≠ default) →
      (∀ g ∈ pfx, g ≠ sep₂) →
      (∀ g ∈ inner, g ≠ default) →
      (∀ g ∈ inner, g ≠ sep₂) →
      (∀ g ∈ f inner, g ≠ default) →
      (∀ g ∈ f inner, g ≠ sep₂) →
      (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).Dom),
        ((TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).get h).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ [default])

theorem tm0RealizesBlockSepInv_revFRev
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} {f : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockSepInv Γ sep f blockInv)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep) → ∀ g ∈ f block, g ≠ sep) :
    TM0RealizesBlockSepInv Γ sep (List.reverse ∘ f ∘ List.reverse)
      (fun block => blockInv block.reverse) := by
  classical
  obtain ⟨Λ_rev, h_rev_inh, h_rev_fin, M_rev, hM_rev⟩ :=
    (@tm0_reverse_blockSep Γ _ _ _ (sep := sep))
  obtain ⟨Λ_f, h_f_inh, h_f_fin, M_f, hM_f⟩ := hf
  let h12_inh : Inhabited (Λ_rev ⊕ Λ_f) :=
    ⟨Sum.inl (@default _ h_rev_inh)⟩
  let h123_inh : Inhabited ((Λ_rev ⊕ Λ_f) ⊕ Λ_rev) :=
    ⟨Sum.inl (@default _ h12_inh)⟩
  let M12 := @TM0Seq.compose Γ Λ_rev h_rev_inh Λ_f h_f_inh M_rev M_f
  let M123 := @TM0Seq.compose Γ (Λ_rev ⊕ Λ_f) h12_inh Λ_rev h_rev_inh M12 M_rev
  refine ⟨(Λ_rev ⊕ Λ_f) ⊕ Λ_rev, h123_inh,
    @instFintypeSum _ _ (@instFintypeSum _ _ h_rev_fin h_f_fin) h_rev_fin,
    M123, ?_⟩
  intro block suffix hblock_inv hblock_nd hblock_nsep hsuffix_nd hout_nd hout_nsep
  have hrev_nd : ∀ g ∈ block.reverse, g ≠ default :=
    reverse_ne_default block hblock_nd
  have hrev_nsep : ∀ g ∈ block.reverse, g ≠ sep :=
    reverse_ne_sep block hblock_nsep
  have hfblock_nd : ∀ g ∈ f block.reverse, g ≠ default :=
    hf_nd block.reverse hrev_nd
  have hfblock_nsep : ∀ g ∈ f block.reverse, g ≠ sep :=
    hf_nsep block.reverse hrev_nsep
  have hstep1 := hM_rev block suffix hblock_nd hblock_nsep hsuffix_nd hrev_nd hrev_nsep
  have hstep2 := hM_f block.reverse suffix hblock_inv hrev_nd hrev_nsep
    hsuffix_nd hfblock_nd hfblock_nsep
  have hstep3 := hM_rev (f block.reverse) suffix hfblock_nd hfblock_nsep
    hsuffix_nd hout_nd hout_nsep
  have hM12_dom :
      (TM0Seq.evalCfg M12 (block ++ sep :: suffix)).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ Λ_rev h_rev_inh Λ_f h_f_inh
      M_rev M_f (block ++ sep :: suffix) hstep1.1
    convert hstep2.1 using 1
    rw [hstep1.2 hstep1.1]
    rfl
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (block ++ sep :: suffix)).get hM12_dom).Tape =
        Tape.mk₁ (f block.reverse ++ sep :: suffix) := by
    convert @TM0Seq.compose_evalCfg_tape Γ _ Λ_rev h_rev_inh Λ_f h_f_inh
      M_rev M_f
      (block ++ sep :: suffix) (block.reverse ++ sep :: suffix)
      hstep1.1 (hstep1.2 hstep1.1) hstep2.1 hM12_dom using 1
    exact (hstep2.2 hstep2.1).symm
  have hM123_dom :
      (TM0Seq.evalCfg M123 (block ++ sep :: suffix)).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ (Λ_rev ⊕ Λ_f) h12_inh
      Λ_rev h_rev_inh M12 M_rev
      (block ++ sep :: suffix) hM12_dom
    convert hstep3.1 using 1
    rw [hM12_tape]
    rfl
  refine ⟨hM123_dom, ?_⟩
  intro h
  have h_tape := @TM0Seq.compose_evalCfg_tape Γ _ (Λ_rev ⊕ Λ_f) h12_inh
    Λ_rev h_rev_inh M12 M_rev
    (block ++ sep :: suffix) (f block.reverse ++ sep :: suffix)
    hM12_dom hM12_tape hstep3.1 h
  rw [h_tape, hstep3.2 hstep3.1]
  rfl

theorem tm0RealizesBlockSepInv_toInnerDefault
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep₂ : Γ} {f : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hsep₂ : sep₂ ≠ default)
    (hf : TM0RealizesBlockSepInv Γ sep₂ f blockInv)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockDefaultSepInv Γ sep₂ f blockInv := by
  have hrev := @tm0_reverse_blockSep Γ _ _ _ (sep := default)
  have hrfr := tm0RealizesBlockSepInv_revFRev hf hf_nd hf_nsep
  obtain ⟨Λ_rev, h_rev_inh, h_rev_fin, M_rev, hM_rev⟩ := hrev
  obtain ⟨Λ_rfr, h_rfr_inh, h_rfr_fin, M_rfr, hM_rfr⟩ := hrfr
  let h12_inh : Inhabited (Λ_rev ⊕ Λ_rfr) :=
    ⟨Sum.inl (@default _ h_rev_inh)⟩
  let h123_inh : Inhabited ((Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev) :=
    ⟨Sum.inl (@default _ h12_inh)⟩
  let M12 := @TM0Seq.compose Γ Λ_rev h_rev_inh Λ_rfr h_rfr_inh M_rev M_rfr
  let M123 := @TM0Seq.compose Γ (Λ_rev ⊕ Λ_rfr) h12_inh Λ_rev h_rev_inh M12 M_rev
  refine ⟨(Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev, h123_inh,
    @instFintypeSum _ _ (@instFintypeSum _ _ h_rev_fin h_rfr_fin) h_rev_fin,
    M123, ?_⟩
  intro pfx inner hinner_inv hpfx_nd hpfx_nsep₂ hinn_nd hinn_nsep₂ hfinn_nd hfinn_nsep₂
  set outer := pfx ++ sep₂ :: inner with h_outer_def
  have h_outer_rev : outer.reverse = inner.reverse ++ sep₂ :: pfx.reverse :=
    reverse_append_cons pfx sep₂ inner
  set mid := (f inner).reverse ++ sep₂ :: pfx.reverse with h_mid_def
  have h_mid_rev : mid.reverse = pfx ++ sep₂ :: f inner := by
    simp only [mid, reverse_append_cons, List.reverse_reverse]

  have houter_nd : ∀ g ∈ outer, g ≠ default :=
    forall_mem_append_cons.mpr ⟨hpfx_nd, hsep₂, hinn_nd⟩
  have hstep1 := hM_rev outer [] houter_nd houter_nd (by simp)
    (reverse_ne_default outer houter_nd) (reverse_ne_default outer houter_nd)
  have h_rfr_eq : (List.reverse ∘ f ∘ List.reverse) inner.reverse =
      (f inner).reverse := by
    simp [Function.comp, List.reverse_reverse]
  have hrfr_inv : (fun block => blockInv block.reverse) inner.reverse := by
    simpa using hinner_inv
  have hrfr_nd : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ default := by
    rw [h_rfr_eq]
    exact reverse_ne_default (f inner) hfinn_nd
  have hrfr_nsep₂ : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ sep₂ := by
    rw [h_rfr_eq]
    exact reverse_ne_sep (f inner) hfinn_nsep₂
  have hpfx_rev_nd : ∀ g ∈ pfx.reverse, g ≠ default :=
    reverse_ne_default pfx hpfx_nd
  have hstep2 := hM_rfr inner.reverse pfx.reverse
    hrfr_inv
    (reverse_ne_default inner hinn_nd)
    (reverse_ne_sep inner hinn_nsep₂)
    hpfx_rev_nd hrfr_nd hrfr_nsep₂
  have hmid_nd : ∀ g ∈ mid, g ≠ default :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_default (f inner) hfinn_nd, hsep₂,
       reverse_ne_default pfx hpfx_nd⟩
  have hstep3 := hM_rev mid [] hmid_nd hmid_nd (by simp)
    (reverse_ne_default mid hmid_nd) (reverse_ne_default mid hmid_nd)

  have hstep1_tape :
      ((TM0Seq.evalCfg M_rev (outer ++ [default])).get hstep1.1).Tape =
        Tape.mk₁ (inner.reverse ++ sep₂ :: pfx.reverse ++ [default]) := by
    rw [hstep1.2 hstep1.1]
    simp [h_outer_rev]
  have hstep2_dom_trailing :
      (TM0Seq.evalCfg M_rfr
        (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).Dom := by
    rw [evalCfg_append_default]
    exact hstep2.1
  have hstep2_tape_trailing :
      ((TM0Seq.evalCfg M_rfr
        (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).get hstep2_dom_trailing).Tape =
        Tape.mk₁ ((f inner).reverse ++ sep₂ :: pfx.reverse ++ [default]) := by
    have hcfg_eq :
        (TM0Seq.evalCfg M_rfr
          (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).get hstep2_dom_trailing =
          (TM0Seq.evalCfg M_rfr
            (inner.reverse ++ sep₂ :: pfx.reverse)).get hstep2.1 := by
      apply Part.get_eq_get_of_eq
      exact evalCfg_append_default M_rfr (inner.reverse ++ sep₂ :: pfx.reverse)
    rw [hcfg_eq, hstep2.2 hstep2.1]
    rw [h_rfr_eq]
    exact (tape_mk₁_append_default ((f inner).reverse ++ sep₂ :: pfx.reverse)).symm
  have hM12_dom :
      (TM0Seq.evalCfg M12 (outer ++ [default])).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ Λ_rev h_rev_inh Λ_rfr h_rfr_inh
      M_rev M_rfr (outer ++ [default]) hstep1.1
    convert hstep2_dom_trailing using 1
    rw [hstep1_tape]
    rfl
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (outer ++ [default])).get hM12_dom).Tape =
        Tape.mk₁ (mid ++ [default]) := by
    convert @TM0Seq.compose_evalCfg_tape Γ _ Λ_rev h_rev_inh Λ_rfr h_rfr_inh
      M_rev M_rfr
      (outer ++ [default])
      (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])
      hstep1.1 hstep1_tape hstep2_dom_trailing hM12_dom using 1
    rw [hstep2_tape_trailing]
  have hM123_dom :
      (TM0Seq.evalCfg M123 (outer ++ [default])).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ (Λ_rev ⊕ Λ_rfr) h12_inh Λ_rev h_rev_inh
      M12 M_rev (outer ++ [default]) hM12_dom
    convert hstep3.1 using 1
    rw [hM12_tape]
    rfl
  refine ⟨?_, ?_⟩
  · convert hM123_dom using 1
  · intro h
    have h_tape := @TM0Seq.compose_evalCfg_tape Γ _ (Λ_rev ⊕ Λ_rfr) h12_inh
      Λ_rev h_rev_inh M12 M_rev
      (outer ++ [default]) (mid ++ [default])
      hM12_dom hM12_tape hstep3.1 hM123_dom
    have h_final : ((TM0Seq.evalCfg M123 (outer ++ [default])).get hM123_dom).Tape =
        Tape.mk₁ (pfx ++ sep₂ :: f inner ++ [default]) := by
      rw [h_tape, hstep3.2 hstep3.1]
      simp [h_mid_rev]
    have h_get_eq :
        (TM0Seq.evalCfg M123 (pfx ++ sep₂ :: inner ++ [default])).get h =
          (TM0Seq.evalCfg M123 (outer ++ [default])).get hM123_dom := by
      apply Part.get_eq_get_of_eq
      simp [outer, List.append_assoc]
    rw [h_get_eq, h_final]

/-- The concrete invariant for a het accumulator block: every cell is an
embedded accumulator symbol. -/
def isHetAccBlock (T : Type) (block : List (Option (T ⊕ ChainΓ))) : Prop :=
  ∃ acc : List ChainΓ, block = acc.map (hetAccEmb (T := T))

theorem isHetAccBlock_reverse (T : Type)
    (block : List (Option (T ⊕ ChainΓ))) :
    isHetAccBlock T block → isHetAccBlock T block.reverse := by
  rintro ⟨acc, rfl⟩
  exact ⟨acc.reverse, by simp⟩

theorem chainEncodeFoldInnerStep_ne_default
    (T : Type) [Primcodable T] (t : T)
    (block : List (Option (T ⊕ ChainΓ)))
    (_hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ ChainΓ))) :
    ∀ g ∈ chainEncodeFoldInnerStep T t block,
      g ≠ (default : Option (T ⊕ ChainΓ)) := by
  intro g hg
  unfold chainEncodeFoldInnerStep at hg
  rcases List.mem_map.mp hg with ⟨a, _ha, rfl⟩
  simp [hetAccEmb]

theorem filterMap_hetAccDecode_ne_default_of_ne_sep
    (T : Type) (block : List (Option (T ⊕ ChainΓ)))
    (hblock_nsep : ∀ g ∈ block, g ≠ hetSep (T := T) (Γ₀ := ChainΓ)) :
    ∀ g ∈ block.filterMap (hetAccDecode (T := T)),
      g ≠ (default : ChainΓ) := by
  intro g hg hdefault
  rcases List.mem_filterMap.mp hg with ⟨x, hx, hdecode⟩
  subst hdefault
  cases x with
  | none => simp [hetAccDecode] at hdecode
  | some x =>
      cases x with
      | inl t => simp [hetAccDecode] at hdecode
      | inr a =>
          simp [hetAccDecode] at hdecode
          subst hdecode
          exact hblock_nsep (some (Sum.inr default)) hx rfl

theorem chainEncodeFoldInnerStep_ne_sep
    (T : Type) [Primcodable T] (t : T)
    (block : List (Option (T ⊕ ChainΓ)))
    (hblock_nsep : ∀ g ∈ block, g ≠ hetSep (T := T) (Γ₀ := ChainΓ)) :
    ∀ g ∈ chainEncodeFoldInnerStep T t block,
      g ≠ hetSep (T := T) (Γ₀ := ChainΓ) := by
  intro g hg
  unfold chainEncodeFoldInnerStep at hg
  rcases List.mem_map.mp hg with ⟨a, ha, rfl⟩
  have hdecoded_nd :
      ∀ g ∈ block.filterMap (hetAccDecode (T := T)),
        g ≠ (default : ChainΓ) :=
    filterMap_hetAccDecode_ne_default_of_ne_sep T block hblock_nsep
  have ha_nd := binPairConstSucc_ne_default (Encodable.encode t)
    (block.filterMap (hetAccDecode (T := T))) hdecoded_nd a ha
  change hetAccEmb (T := T) a ≠ hetSep (T := T) (Γ₀ := ChainΓ)
  intro h
  injection h with hsum
  injection hsum with hdefault
  exact ha_nd hdefault

theorem chainEncodeFoldInnerStep_preserves_accBlock
    (T : Type) [Primcodable T] (t : T)
    (block : List (Option (T ⊕ ChainΓ))) :
    isHetAccBlock T block →
    isHetAccBlock T (chainEncodeFoldInnerStep T t block) := by
  rintro ⟨acc, rfl⟩
  exact ⟨chainEncodeFoldAccStep T t acc, by
    rw [chainEncodeFoldInnerStep_on_acc]⟩

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
  · simp +decide
  · exact hblock g (by simp_all)

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

This decomposition keeps the reusable arithmetic and chain-formatting pieces
available for direct tape converters:

1. `chainEncode_fold_eq` gives the algebraic fold equation for binary
   accumulator construction.
2. `tm0_binPairConstSucc_blockSepAnySuffix_of_square` isolates the remaining
   square-realization obligation needed by that fold style.
3. `tm0_chainFormatHetBlock_block` realizes the final reverse + cons-marker
   formatting step on the heterogeneous tape representation.

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
