import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinaryArithmetic
import Langlib.Automata.Turing.DSL.DropWhileNeSep
import Langlib.Automata.Turing.DSL.DropFromLastSepMachine
import Langlib.Automata.Turing.DSL.BinaryPredecessor
import Langlib.Automata.Turing.DSL.SplitAtSep
import Langlib.Automata.Turing.DSL.IncBeforeSepMachine
import Langlib.Automata.Turing.DSL.DecAfterSepMachine
import Langlib.Automata.Turing.DSL.HetFoldDecomp
import Langlib.Automata.Turing.DSL.CondBlockOps
import Langlib.Automata.Turing.DSL.DropUntilFirstSepMachine
import Langlib.Automata.Turing.DSL.CopyBlockProof
import Langlib.Automata.Turing.DSL.FixedStateFinalize

/-! # Paired Block Arithmetic — The Central Primitive

This file establishes **paired block addition** (`binAddPaired`) as the
central arithmetic primitive. Two numbers are stored side-by-side on the
tape, separated by `chainConsBottom`; paired addition decodes both sides
and returns the canonical binary representation of their sum.

## Proof of block-realizability for `binAddPaired`

`binAddPaired` is proven block-realizable by decomposing it as:

1. A while loop (`tm0RealizesBlock_while`) that repeatedly decrements the
   left sub-block and increments the right sub-block while the left value is
   positive.
2. Extraction of the final right sub-block.
3. Normalization of that extracted result.

The concrete TM0 machines for the decrement/increment loop body and right
extraction remain as the lower-level postponed proofs.

## Design principle

All operations here are defined purely in terms of `decodeBinaryBlock`
and `chainBinaryRepr` (the decode/encode pipeline). Block-realizability
proofs compose via `tm0RealizesBlock_comp`.
-/

open Turing PartrecToTM2 TM2to1

@[simp]
theorem splitAtConsBottom_chainBinaryRepr_cons' (c : ℕ) (block : List ChainΓ) :
    splitAtConsBottom (chainBinaryRepr c ++ chainConsBottom :: block) =
      (chainBinaryRepr c, block) := by
  simpa using splitAtConsBottom_binary_sep c block

/-! ### Paired Block Addition — The Central Primitive -/

/-- **Paired block addition** (addition of neighboring numbers).
    Split the block at the first `chainConsBottom`, decode both halves,
    add them, and re-encode the sum.

    Given a block encoding `[left][sep][right]`, produces
    `chainBinaryRepr (left + right)`. -/
noncomputable def binAddPaired (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  chainBinaryRepr (decodeBinaryBlock left + decodeBinaryBlock right)

/-- Separator-parametric paired addition.

This is extensionally the same operation as `binAddPaired`, but the separator
between the two addends is not fixed to `chainConsBottom`. -/
noncomputable def binAddPairedSep (sep : ChainΓ) (block : List ChainΓ) :
    List ChainΓ :=
  let (left, right) := splitAtSep sep block
  chainBinaryRepr (decodeBinaryBlock left + decodeBinaryBlock right)

/-- Separator-parametric paired addition that keeps the right operand.

On `left ++ [sep] ++ right`, this produces
`chainBinaryRepr (decode left + decode right) ++ [sep] ++ right`.
This is the operation needed by one multiplication step: update the
accumulator while leaving the addend available for later iterations. -/
noncomputable def binAddPairedKeepRightSep (sep : ChainΓ)
    (block : List ChainΓ) : List ChainΓ :=
  let (_, right) := splitAtSep sep block
  binAddPairedSep sep block ++ sep :: right

/-- Extract the left sub-block (prefix before first `chainConsBottom`). -/
noncomputable def extractPairedLeft (block : List ChainΓ) : List ChainΓ :=
  (splitAtConsBottom block).1

/-- `binAddPaired` preserves non-defaultness. -/
theorem binAddPaired_ne_default (block : List ChainΓ)
    (_h : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binAddPaired block, g ≠ default := by
  unfold binAddPaired
  simp +zetaDelta
  exact fun g hg => chainBinaryRepr_ne_default _ g hg

theorem binAddPairedSep_ne_default (sep : ChainΓ) (block : List ChainΓ)
    (_h : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binAddPairedSep sep block, g ≠ default := by
  unfold binAddPairedSep
  simp +zetaDelta
  exact fun g hg => chainBinaryRepr_ne_default _ g hg

theorem binAddPairedKeepRightSep_ne_default (sep : ChainΓ) (block : List ChainΓ)
    (hsep : sep ≠ default) (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binAddPairedKeepRightSep sep block, g ≠ default := by
  rcases hsplit : splitAtSep sep block with ⟨left, right⟩
  unfold binAddPairedKeepRightSep
  simp [hsplit]
  rintro g (hg | rfl | hg)
  · exact binAddPairedSep_ne_default sep block hblock g hg
  · exact hsep
  · exact hblock g (splitAtSep_snd_subset sep block g (by simpa [hsplit] using hg))

theorem binAddPairedKeepRightSep_eq_cons
    (sep : ChainΓ) (left right : List ChainΓ)
    (hleft_sep : ∀ g ∈ left, g ≠ sep) :
    binAddPairedKeepRightSep sep (left ++ sep :: right) =
      binAddPairedSep sep (left ++ sep :: right) ++ sep :: right := by
  unfold binAddPairedKeepRightSep
  rw [splitAtSep_general_cons sep left right hleft_sep]

/-- `extractPairedLeft` preserves non-defaultness. -/
theorem extractPairedLeft_ne_default (block : List ChainΓ)
    (h : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ extractPairedLeft block, g ≠ default := by
  induction' block with c rest ih;
  · decide +kernel;
  · intro g hg
    exact h g (splitAtConsBottom_fst_subset _ g (by unfold extractPairedLeft at hg; exact hg))

/-! ### Multiplication by Constant -/

/-- Multiply the binary block value by a fixed constant c: n → c * n. -/
noncomputable def binMulConst (c : ℕ) (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (c * decodeBinaryBlock block)

theorem binMulConst_correct (c n : ℕ) :
    binMulConst c (chainBinaryRepr n) = chainBinaryRepr (c * n) := by
  unfold binMulConst; rw [decodeBinaryBlock_chainBinaryRepr]

theorem binMulConst_ne_default (c : ℕ) (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulConst c block, g ≠ default := by
  unfold binMulConst; exact chainBinaryRepr_ne_default _

/- The tempting global theorem

     `TM0RealizesBlock ChainΓ incLeftDecRight`

   is stronger than the paired arithmetic use case needs: it would have to
   implement the identity branch for blocks with no `chainConsBottom`. The
   actual paired-block step should instead use the separator-aware predecessor
   theorem `tm0_incBeforeSep_present_blockSep` under a well-formedness
   invariant saying that the paired separator is present. -/

/-- Paired-block well-formedness fragment needed by the left/right transfer:
    the default-delimited block contains the internal `chainConsBottom`
    separator. -/
def hasConsBottom (block : List ChainΓ) : Prop :=
  chainConsBottom ∈ block

/-- The paired separator invariant needed by separator-framed machines:
    there is a first `chainConsBottom`, and the right sub-block after it has
    no second `chainConsBottom`. -/
def pairedSepInv (block : List ChainΓ) : Prop :=
  hasConsBottom block ∧ ∀ g ∈ (splitAtConsBottom block).2, g ≠ chainConsBottom

/-! ### Decrement-left / increment-right decomposition for paired addition -/

/-- Extract the right sub-block (suffix after first `chainConsBottom`). -/
noncomputable def extractPairedRight (block : List ChainΓ) : List ChainΓ :=
  (splitAtConsBottom block).2

/-- `extractPairedRight` preserves non-defaultness. -/
theorem extractPairedRight_ne_default (block : List ChainΓ)
    (h : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ extractPairedRight block, g ≠ default := by
  intro g hg
  unfold extractPairedRight at hg
  have : ∀ {block : List ChainΓ}, ∀ g ∈ (splitAtConsBottom block).2, g ∈ block := by
    intros block g hg
    induction' block with c block ih generalizing g <;>
      simp_all +decide [splitAtConsBottom]
    grind
  exact h g (this g hg)

theorem extractPairedRight_eq_dropUntilFirstSep :
    extractPairedRight = dropUntilFirstSep chainConsBottom := by
  funext block
  induction' block with c rest ih
  · rfl
  · by_cases h : c = chainConsBottom
    · simp [extractPairedRight, splitAtConsBottom, dropUntilFirstSep, h]
    · unfold extractPairedRight at ih
      simp [extractPairedRight, splitAtConsBottom, dropUntilFirstSep, h, ih]

/-- The step function for paired addition: decrement the left sub-block
    and increment the right sub-block. Outside the paired separator invariant,
    this is identity; the concrete implementation only promises the paired
    transfer behavior on invariant blocks. -/
noncomputable def pairedDecrLeftIncrRight (block : List ChainΓ) : List ChainΓ :=
  by
    classical
    exact
      if pairedSepInv block then
        let (left, right) := splitAtConsBottom block
        chainBinaryRepr (decodeBinaryBlock left - 1)
          ++ [chainConsBottom]
          ++ chainBinaryRepr (decodeBinaryBlock right + 1)
      else block

theorem pairedDecrLeftIncrRight_hasConsBottom (block : List ChainΓ)
    (hInv : pairedSepInv block) :
    hasConsBottom (pairedDecrLeftIncrRight block) := by
  unfold hasConsBottom pairedDecrLeftIncrRight
  simp [hInv]

theorem pairedDecrLeftIncrRight_pairedSepInv (block : List ChainΓ)
    (hInv : pairedSepInv block) :
    pairedSepInv (pairedDecrLeftIncrRight block) := by
  constructor
  · exact pairedDecrLeftIncrRight_hasConsBottom block hInv
  · unfold pairedDecrLeftIncrRight
    simp [hInv]
    exact chainBinaryRepr_no_consBottom _

/-- On the two sides of `chainConsBottom`, the paired step is exactly
    normalized predecessor on the left and normalized successor on the right. -/
theorem pairedDecrLeftIncrRight_eq_binPred_binSuccNormalize (block : List ChainΓ)
    (hInv : pairedSepInv block) :
    pairedDecrLeftIncrRight block =
      binPred (splitAtConsBottom block).1 ++ [chainConsBottom] ++
        (binSucc ∘ normalizeBlock) (splitAtConsBottom block).2 := by
  unfold pairedDecrLeftIncrRight binPred normalizeBlock Function.comp
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  simp [hInv, binSucc_correct]

/-- `pairedDecrLeftIncrRight` preserves non-defaultness when the condition holds. -/
theorem pairedDecrLeftIncrRight_ne_default (block : List ChainΓ)
    (_h : ∀ g ∈ block, g ≠ default) (_hcond : ¬ blockValueLeq 0 block) :
    ∀ g ∈ pairedDecrLeftIncrRight block, g ≠ default := by
  unfold pairedDecrLeftIncrRight
  split_ifs with hInv
  · simp +zetaDelta
    rintro g (hg | rfl | hg)
    · exact chainBinaryRepr_ne_default _ g hg
    · exact chainConsBottom_ne_default
    · exact chainBinaryRepr_ne_default _ g hg
  · exact _h

theorem paired_splitAtConsBottom_reconstruct_of_mem (block : List ChainΓ)
    (h : chainConsBottom ∈ block) :
    block = (splitAtConsBottom block).1 ++ chainConsBottom :: (splitAtConsBottom block).2 := by
  simpa using splitAtConsBottom_reconstruct_of_mem block h

/-! ### Invariant-restricted block machines for paired arithmetic -/

def TM0RealizesBlockInv {Γ : Type} [Inhabited Γ]
    (f : List Γ → List Γ) (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (block : List Γ),
      blockInv block →
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ [default])).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ [default])).Dom),
        ((TM0Seq.evalCfg M (block ++ [default])).get h).Tape =
          Tape.mk₁ (f block ++ [default])

def TM0RealizesBlockInvSuffix {Γ : Type} [Inhabited Γ]
    (f : List Γ → List Γ) (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (block suffix : List Γ),
      blockInv block →
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
        ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
          Tape.mk₁ (f block ++ default :: suffix)

def TM0RealizesBlockCondInvSuffix {Γ : Type} [Inhabited Γ]
    (step : List Γ → List Γ) (cond : List Γ → Prop) [DecidablePred cond]
    (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ) (q_cont : Λ),
    ∀ (block suffix : List Γ),
      blockInv block →
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ suffix, g ≠ default) →
      (cond block → ∀ g ∈ step block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
        let cfg := (TM0Seq.evalCfg M (block ++ default :: suffix)).get h
        if cond block then
          cfg.q = q_cont ∧ cfg.Tape = Tape.mk₁ (step block ++ default :: suffix)
        else
          cfg.q ≠ q_cont ∧ cfg.Tape = Tape.mk₁ (block ++ default :: suffix)

theorem tm0RealizesBlockInvSuffix_of_block {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlock Γ f) :
    TM0RealizesBlockInvSuffix f blockInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block suffix _hInv hblock hsuffix hfblock
  exact hM block suffix hblock hsuffix hfblock

theorem tm0RealizesBlockInvSuffix_comp {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockInvSuffix f blockInv)
    (hg : TM0RealizesBlockInvSuffix g blockInv)
    (hf_inv : ∀ block, blockInv block → (∀ x ∈ block, x ≠ default) → blockInv (f block))
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default) :
    TM0RealizesBlockInvSuffix (g ∘ f) blockInv := by
  obtain ⟨Λ_f, hΛfi, hΛff, M_f, hM_f⟩ := hf
  obtain ⟨Λ_g, hΛgi, hΛgf, M_g, hM_g⟩ := hg
  let hsum : Inhabited (Λ_f ⊕ Λ_g) := ⟨Sum.inl (@default _ hΛfi)⟩
  refine ⟨Λ_f ⊕ Λ_g, hsum, inferInstance,
    @TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g, ?_⟩
  intro block suffix hInv hblock hsuffix hgf
  have hfblock_nd := hf_nd block hblock
  obtain ⟨hf_dom, hf_tape⟩ := hM_f block suffix hInv hblock hsuffix hfblock_nd
  obtain ⟨hg_dom, hg_tape⟩ := hM_g (f block) suffix
    (hf_inv block hInv hblock) hfblock_nd hsuffix hgf
  have hg_from_cfg :
      (TM0Seq.evalFromCfg M_g
        ⟨default, ((TM0Seq.evalCfg M_f (block ++ default :: suffix)).get
          hf_dom).Tape⟩).Dom := by
    rw [hf_tape hf_dom]
    show (TM0Seq.evalFromCfg M_g (TM0.init (f block ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hg_dom
  have hcomp_dom :
      (TM0Seq.evalCfg
        (@TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g)
        (block ++ default :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff
      (@TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g)
      (block ++ default :: suffix)).mpr
        (@TM0Seq.compose_dom_of_parts Γ _ Λ_f hΛfi Λ_g hΛgi
          M_f M_g (block ++ default :: suffix) hf_dom hg_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    @TM0Seq.compose_evalCfg_tape Γ _ Λ_f hΛfi Λ_g hΛgi M_f M_g
      (block ++ default :: suffix) (f block ++ default :: suffix)
      hf_dom (hf_tape hf_dom) hg_dom h
  rw [hcomp_tape]
  exact hg_tape hg_dom

theorem tm0RealizesBlockInvSuffix_congr {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockInvSuffix f blockInv)
    (hfg : ∀ block, blockInv block → f block = g block) :
    TM0RealizesBlockInvSuffix g blockInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block suffix hInv hblock hsuffix hgblock
  have hfblock : ∀ x ∈ f block, x ≠ default := by
    simpa [hfg block hInv] using hgblock
  obtain ⟨hdom, htape⟩ := hM block suffix hInv hblock hsuffix hfblock
  refine ⟨hdom, ?_⟩
  intro h
  rw [htape h, hfg block hInv]

theorem tm0RealizesBlockInv_comp {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockInv f blockInv)
    (hg : TM0RealizesBlockInv g blockInv)
    (hf_inv : ∀ block, blockInv block → (∀ x ∈ block, x ≠ default) → blockInv (f block))
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default) :
    TM0RealizesBlockInv (g ∘ f) blockInv := by
  obtain ⟨Λ_f, hΛfi, hΛff, M_f, hM_f⟩ := hf
  obtain ⟨Λ_g, hΛgi, hΛgf, M_g, hM_g⟩ := hg
  let hsum : Inhabited (Λ_f ⊕ Λ_g) := ⟨Sum.inl (@default _ hΛfi)⟩
  refine ⟨Λ_f ⊕ Λ_g, hsum, inferInstance,
    @TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g, ?_⟩
  intro block hInv hblock hgf
  have hfblock_nd := hf_nd block hblock
  obtain ⟨hf_dom, hf_tape⟩ := hM_f block hInv hblock hfblock_nd
  obtain ⟨hg_dom, hg_tape⟩ := hM_g (f block)
    (hf_inv block hInv hblock) hfblock_nd hgf
  have hg_from_cfg :
      (TM0Seq.evalFromCfg M_g
        ⟨default, ((TM0Seq.evalCfg M_f (block ++ [default])).get hf_dom).Tape⟩).Dom := by
    rw [hf_tape hf_dom]
    show (TM0Seq.evalFromCfg M_g (TM0.init (f block ++ [default]))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hg_dom
  have hcomp_dom :
      (TM0Seq.evalCfg
        (@TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g)
        (block ++ [default])).Dom := by
    exact (TM0Seq.evalCfg_dom_iff
      (@TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g)
      (block ++ [default])).mpr
        (@TM0Seq.compose_dom_of_parts Γ _ Λ_f hΛfi Λ_g hΛgi
          M_f M_g (block ++ [default]) hf_dom hg_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    @TM0Seq.compose_evalCfg_tape Γ _ Λ_f hΛfi Λ_g hΛgi M_f M_g
      (block ++ [default]) (f block ++ [default])
      hf_dom (hf_tape hf_dom) hg_dom h
  rw [hcomp_tape]
  exact hg_tape hg_dom

theorem tm0RealizesBlockInv_congr {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockInv f blockInv)
    (hfg : ∀ block, blockInv block → f block = g block) :
    TM0RealizesBlockInv g blockInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block hInv hblock hgblock
  have hfblock : ∀ x ∈ f block, x ≠ default := by
    simpa [hfg block hInv] using hgblock
  obtain ⟨hdom, htape⟩ := hM block hInv hblock hfblock
  refine ⟨hdom, ?_⟩
  intro h
  rw [htape h, hfg block hInv]

theorem tm0RealizesBlockInvSuffix_while
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (step result : List Γ → List Γ) (cond : List Γ → Prop) [DecidablePred cond]
    (blockInv : List Γ → Prop)
    (hbody : TM0RealizesBlockCondInvSuffix step cond blockInv)
    (hinv_step : ∀ block, blockInv block → (∀ g ∈ block, g ≠ default) →
      cond block → blockInv (step block))
    (hstep_nd : ∀ block, (∀ g ∈ block, g ≠ default) → cond block →
      ∀ g ∈ step block, g ≠ default)
    (hresult_eq : ∀ block, (∀ g ∈ block, g ≠ default) → blockInv block →
      ∃ n, result block = blockIterateWhile step cond n block ∧
        ¬cond (blockIterateWhile step cond n block))
    (_hresult_nd : ∀ block, (∀ g ∈ block, g ≠ default) → blockInv block →
      ∀ g ∈ result block, g ≠ default) :
    TM0RealizesBlockInvSuffix result blockInv := by
  obtain ⟨Λ, hΛi, hΛf, M, q_cont, hM⟩ := hbody
  haveI : DecidableEq Λ := Classical.decEq Λ
  refine ⟨Λ, hΛi, hΛf, tm0WhileLoop M q_cont, ?_⟩
  intro block suffix hblockInv hblock hsuffix hresult
  obtain ⟨n, hn_eq, hn_not_cond⟩ := hresult_eq block hblock hblockInv
  suffices key : ∀ (m : ℕ) (blk : List Γ),
    blockInv blk →
    (∀ g ∈ blk, g ≠ default) →
    ¬cond (blockIterateWhile step cond m blk) →
    (TM0Seq.evalCfg (tm0WhileLoop M q_cont) (blk ++ default :: suffix)).Dom ∧
    ∀ (hd : (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
        (blk ++ default :: suffix)).Dom),
      ((TM0Seq.evalCfg (tm0WhileLoop M q_cont)
        (blk ++ default :: suffix)).get hd).Tape =
      Tape.mk₁ (blockIterateWhile step cond m blk ++ default :: suffix) by
    obtain ⟨h_dom, h_tape⟩ := key n block hblockInv hblock hn_not_cond
    exact ⟨h_dom, fun hd => by rw [hn_eq, h_tape hd]⟩
  intro m
  induction m with
  | zero =>
    intro blk hblkInv hblk hn_not
    simp only [blockIterateWhile] at hn_not ⊢
    obtain ⟨h_body_dom, h_body_spec⟩ := hM blk suffix hblkInv hblk hsuffix
      (fun hc => hstep_nd blk hblk hc)
    have h_body_spec' := h_body_spec h_body_dom
    simp only [hn_not, ↓reduceIte] at h_body_spec'
    obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
    obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _
      h_body_dom h_q_ne
    exact ⟨h_dom, fun hd => by rw [h_tape hd, h_tape_eq]⟩
  | succ m ih =>
    intro blk hblkInv hblk hn_not
    by_cases hcond : cond blk
    · rw [blockIterateWhile_succ_true _ _ _ _ hcond] at hn_not ⊢
      have h_step_nd := hstep_nd blk hblk hcond
      have h_step_inv := hinv_step blk hblkInv hblk hcond
      obtain ⟨h_body_dom, h_body_spec⟩ := hM blk suffix hblkInv hblk hsuffix
        (fun _ => h_step_nd)
      have h_body_spec' := h_body_spec h_body_dom
      simp only [hcond, ↓reduceIte] at h_body_spec'
      obtain ⟨h_q_cont, h_tape_step⟩ := h_body_spec'
      obtain ⟨h_W_step_dom, h_W_step_tape⟩ :=
        ih (step blk) h_step_inv h_step_nd hn_not
      obtain ⟨h_W_dom, h_W_tape⟩ := whileLoop_eval_cont M q_cont _ _
        h_body_dom h_q_cont h_tape_step h_W_step_dom
      exact ⟨h_W_dom, fun hd => by rw [h_W_tape hd, h_W_step_tape h_W_step_dom]⟩
    · rw [blockIterateWhile_succ_false _ _ _ _ hcond] at hn_not ⊢
      obtain ⟨h_body_dom, h_body_spec⟩ := hM blk suffix hblkInv hblk hsuffix
        (fun hc => absurd hc hcond)
      have h_body_spec' := h_body_spec h_body_dom
      simp only [hcond, ↓reduceIte] at h_body_spec'
      obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
      obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _
        h_body_dom h_q_ne
      exact ⟨h_dom, fun hd => by rw [h_tape hd, h_tape_eq]⟩

theorem tm0RealizesBlock_comp_invSuffix {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlock Γ f)
    (hg : TM0RealizesBlockInvSuffix g blockInv)
    (hf_inv : ∀ block, (∀ x ∈ block, x ≠ default) → blockInv (f block))
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default) :
    TM0RealizesBlock Γ (g ∘ f) := by
  obtain ⟨Λ_f, hΛfi, hΛff, M_f, hM_f⟩ := hf
  obtain ⟨Λ_g, hΛgi, hΛgf, M_g, hM_g⟩ := hg
  let hsum : Inhabited (Λ_f ⊕ Λ_g) := ⟨Sum.inl (@default _ hΛfi)⟩
  refine ⟨Λ_f ⊕ Λ_g, hsum, inferInstance,
    @TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g, ?_⟩
  intro block suffix hblock hsuffix hgf
  have hfblock_nd := hf_nd block hblock
  obtain ⟨hf_dom, hf_tape⟩ := hM_f block suffix hblock hsuffix hfblock_nd
  obtain ⟨hg_dom, hg_tape⟩ := hM_g (f block) suffix
    (hf_inv block hblock) hfblock_nd hsuffix hgf
  have hg_from_cfg :
      (TM0Seq.evalFromCfg M_g
        ⟨default, ((TM0Seq.evalCfg M_f (block ++ default :: suffix)).get
          hf_dom).Tape⟩).Dom := by
    rw [hf_tape hf_dom]
    show (TM0Seq.evalFromCfg M_g (TM0.init (f block ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hg_dom
  have hcomp_dom :
      (TM0Seq.evalCfg
        (@TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g)
        (block ++ default :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff
      (@TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g)
      (block ++ default :: suffix)).mpr
        (@TM0Seq.compose_dom_of_parts Γ _ Λ_f hΛfi Λ_g hΛgi
          M_f M_g (block ++ default :: suffix) hf_dom hg_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    @TM0Seq.compose_evalCfg_tape Γ _ Λ_f hΛfi Λ_g hΛgi M_f M_g
      (block ++ default :: suffix) (f block ++ default :: suffix)
      hf_dom (hf_tape hf_dom) hg_dom h
  rw [hcomp_tape]
  exact hg_tape hg_dom

noncomputable def pairedDecrLeftOnly (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  binPred left ++ [chainConsBottom] ++ right

noncomputable def pairedIncrRightNormalize (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  left ++ [chainConsBottom] ++ (binSucc ∘ normalizeBlock) right

theorem pairedDecrLeftOnly_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pairedDecrLeftOnly block, g ≠ default := by
  intro g hg
  unfold pairedDecrLeftOnly at hg
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  simp [hsplit] at hg
  rcases hg with hg | rfl | hg
  · exact binPred_ne_default _ (fun x hx =>
      hblock x (splitAtConsBottom_fst_subset block x (by simpa [hsplit] using hx))) g hg
  · exact chainConsBottom_ne_default
  · exact hblock g (splitAtConsBottom_snd_subset block g (by simpa [hsplit] using hg))

theorem pairedIncrRightNormalize_ne_default (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pairedIncrRightNormalize block, g ≠ default := by
  intro g hg
  unfold pairedIncrRightNormalize at hg
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  simp [hsplit] at hg
  rcases hg with hg | rfl | hg
  · exact _hblock g (splitAtConsBottom_fst_subset block g (by simpa [hsplit] using hg))
  · exact chainConsBottom_ne_default
  · exact binSucc_ne_default _ (normalizeBlock_ne_default _) g hg

theorem pairedDecrLeftOnly_pairedSepInv (block : List ChainΓ)
    (hInv : pairedSepInv block) :
    pairedSepInv (pairedDecrLeftOnly block) := by
  unfold pairedSepInv hasConsBottom pairedDecrLeftOnly
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  constructor
  · simp
  · intro g hg
    exact hInv.2 g (by simpa [hsplit] using hg)

theorem pairedIncrRightNormalize_pairedSepInv (block : List ChainΓ)
    (_hInv : pairedSepInv block) :
    pairedSepInv (pairedIncrRightNormalize block) := by
  unfold pairedSepInv hasConsBottom pairedIncrRightNormalize
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  have hleft_nsep : ∀ g ∈ left, g ≠ chainConsBottom := by
    simpa [hsplit] using splitAtConsBottom_fst_no_sep block
  constructor
  · simp
  · rw [splitAtConsBottom_general left ((binSucc ∘ normalizeBlock) right) hleft_nsep]
    exact binSucc_no_consBottom _ (normalizeBlock_no_consBottom right)

theorem tm0_pairedDecrLeftOnly_blockInv :
    TM0RealizesBlockInv pairedDecrLeftOnly pairedSepInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0_incBeforeSep_present_blockSep
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block hInv hblock hfblock
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  have hmem : chainConsBottom ∈ block := hInv.1
  have hblock_reconstruct :
      block = left ++ chainConsBottom :: right := by
    simpa [hsplit] using paired_splitAtConsBottom_reconstruct_of_mem block hmem
  have hleft_nd : ∀ g ∈ left, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_left _ hg)
  have hleft_nsep : ∀ g ∈ left, g ≠ chainConsBottom := by
    simpa [hsplit] using splitAtConsBottom_fst_no_sep block
  have hright_nd : ∀ g ∈ right, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hbinPred_nd : ∀ g ∈ binPred left, g ≠ default :=
    binPred_ne_default left hleft_nd
  have hbinPred_nsep : ∀ g ∈ binPred left, g ≠ chainConsBottom :=
    binPred_no_consBottom left
  obtain ⟨hdom, htape⟩ :=
    hM left right hleft_nd hleft_nsep hright_nd hbinPred_nd hbinPred_nsep
  have hdom' : (TM0Seq.evalCfg M (block ++ [default])).Dom := by
    rw [hblock_reconstruct]
    simpa [List.append_assoc] using
      (show (TM0Seq.evalCfg M ((left ++ chainConsBottom :: right) ++ [default])).Dom from by
        rw [evalCfg_append_default]
        exact hdom)
  refine ⟨hdom', ?_⟩
  intro h
  have hget :
      (TM0Seq.evalCfg M (block ++ [default])).get h =
        (TM0Seq.evalCfg M (left ++ chainConsBottom :: right)).get hdom := by
    apply Part.get_eq_get_of_eq
    rw [hblock_reconstruct]
    simpa [List.append_assoc] using
      (evalCfg_append_default M (left ++ chainConsBottom :: right))
  rw [hget, htape hdom]
  unfold pairedDecrLeftOnly
  rw [hsplit]
  simpa [List.append_assoc] using
    (tape_mk₁_append_default (binPred left ++ chainConsBottom :: right)).symm

theorem tm0_pairedIncrRightNormalize_blockInv :
    TM0RealizesBlockInv pairedIncrRightNormalize pairedSepInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0_binSuccNormalize_afterConsBottom_innerDefault
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block hInv hblock hfblock
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  have hmem : chainConsBottom ∈ block := hInv.1
  have hblock_reconstruct :
      block = left ++ chainConsBottom :: right := by
    simpa [hsplit] using paired_splitAtConsBottom_reconstruct_of_mem block hmem
  have hleft_nd : ∀ g ∈ left, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_left _ hg)
  have hleft_nsep : ∀ g ∈ left, g ≠ chainConsBottom := by
    simpa [hsplit] using splitAtConsBottom_fst_no_sep block
  have hright_nd : ∀ g ∈ right, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hright_nsep : ∀ g ∈ right, g ≠ chainConsBottom := by
    intro g hg
    exact hInv.2 g (by simpa [hsplit] using hg)
  have hf_nd : ∀ g ∈ (binSucc ∘ normalizeBlock) right, g ≠ default :=
    binSucc_ne_default _ (normalizeBlock_ne_default right)
  have hf_nsep : ∀ g ∈ (binSucc ∘ normalizeBlock) right, g ≠ chainConsBottom :=
    binSucc_no_consBottom _ (normalizeBlock_no_consBottom right)
  obtain ⟨hdom, htape⟩ :=
    hM left right hleft_nd hleft_nsep hright_nd hright_nsep hf_nd hf_nsep
  have hdom' : (TM0Seq.evalCfg M (block ++ [default])).Dom := by
    rw [hblock_reconstruct]
    simpa [List.append_assoc] using hdom
  refine ⟨hdom', ?_⟩
  intro h
  have hget :
      (TM0Seq.evalCfg M (block ++ [default])).get h =
        (TM0Seq.evalCfg M (left ++ chainConsBottom :: right ++ [default])).get hdom := by
    apply Part.get_eq_get_of_eq
    rw [hblock_reconstruct]
  rw [hget, htape hdom]
  unfold pairedIncrRightNormalize
  rw [hsplit]
  simp [List.append_assoc]

theorem pairedIncrRightNormalize_decrLeftOnly_eq
    (block : List ChainΓ) (_hInv : pairedSepInv block) :
    pairedIncrRightNormalize (pairedDecrLeftOnly block) =
      pairedDecrLeftIncrRight block := by
  rw [pairedDecrLeftIncrRight_eq_binPred_binSuccNormalize block _hInv]
  unfold pairedIncrRightNormalize pairedDecrLeftOnly
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  simp [Function.comp, List.append_assoc]

theorem tm0_pairedDecrLeftIncrRight_blockInv :
    TM0RealizesBlockInv pairedDecrLeftIncrRight pairedSepInv :=
  tm0RealizesBlockInv_congr
    (tm0RealizesBlockInv_comp
      tm0_pairedDecrLeftOnly_blockInv
      tm0_pairedIncrRightNormalize_blockInv
      (fun block hInv _hblock => pairedDecrLeftOnly_pairedSepInv block hInv)
      pairedDecrLeftOnly_ne_default)
    pairedIncrRightNormalize_decrLeftOnly_eq

/-- The condition for continuing the while loop: the left sub-block is positive. -/
noncomputable abbrev pairedAddCond : List ChainΓ → Prop :=
  fun block => ¬ blockValueLeq 0 block

/-- `decodeBinaryBlock` on the full block equals `decodeBinaryBlock` on the left
    part of `splitAtConsBottom`. -/
theorem decodeBinaryBlock_eq_splitLeft (block : List ChainΓ) :
    decodeBinaryBlock block = decodeBinaryBlock (splitAtConsBottom block).1 := by
  induction' block with c rest ih
  · rfl
  · by_cases hc : c = chainConsBottom <;> simp_all +decide [splitAtConsBottom]
    · unfold chainConsBottom
      simp +decide [decodeBinaryBlock]
    · by_cases hc0 : c = γ'ToChainΓ Γ'.bit0 <;>
        by_cases hc1 : c = γ'ToChainΓ Γ'.bit1 <;>
        simp_all +decide [decodeBinaryBlock]

/-- The while loop result: iterate `pairedDecrLeftIncrRight`
    while the left sub-block is positive. -/
noncomputable def binAddPairedWhile (block : List ChainΓ) : List ChainΓ :=
  let (left, _right) := splitAtConsBottom block
  let n := decodeBinaryBlock left
  blockIterateWhile pairedDecrLeftIncrRight pairedAddCond n block

/-- When the condition holds at every step, `blockIterateWhile` equals
    `Function.iterate`. -/
theorem blockIterateWhile_eq_iterate_of_cond {Γ : Type}
    (step : List Γ → List Γ) (cond : List Γ → Prop) [DecidablePred cond]
    (n : ℕ) (block : List Γ)
    (h : ∀ k, k < n → cond (step^[k] block)) :
    blockIterateWhile step cond n block = step^[n] block := by
  induction' n with n ih generalizing block
  · rfl
  · convert ih (step block) _ using 1
    · exact if_pos (h 0 (Nat.zero_lt_succ _))
    · exact fun k hk => by
        simpa only [← Function.iterate_succ_apply'] using h (k + 1) (Nat.succ_lt_succ hk)

/-
After k iterations of pairedDecrLeftIncrRight, the left and right decode
    values change as expected.
-/
theorem pairedDecrLeftIncrRight_iterate_decode (block : List ChainΓ) (k : ℕ)
    (hInv : pairedSepInv block)
    (hk : k ≤ decodeBinaryBlock (splitAtConsBottom block).1) :
    let result := pairedDecrLeftIncrRight^[k] block
    decodeBinaryBlock (splitAtConsBottom result).1 =
      decodeBinaryBlock (splitAtConsBottom block).1 - k ∧
    decodeBinaryBlock (splitAtConsBottom result).2 =
      decodeBinaryBlock (splitAtConsBottom block).2 + k := by
  induction' k with k ih generalizing block;
  · norm_num +zetaDelta at *;
  · convert ih ( pairedDecrLeftIncrRight block )
      (pairedDecrLeftIncrRight_pairedSepInv block hInv) _ using 1;
    · simp +decide [ pairedDecrLeftIncrRight, hInv ];
      grind +splitIndPred;
    · simp +decide [ pairedDecrLeftIncrRight, hInv ];
      exact Nat.le_sub_one_of_lt hk

/-
The while loop result equals `blockIterateWhile` with appropriate fuel.
-/
theorem binAddPairedWhile_eq_iterate (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default)
    (hInv : pairedSepInv block) :
    ∃ n, binAddPairedWhile block =
        blockIterateWhile pairedDecrLeftIncrRight pairedAddCond n block ∧
      ¬ pairedAddCond
        (blockIterateWhile pairedDecrLeftIncrRight pairedAddCond n block) := by
  unfold binAddPairedWhile pairedAddCond blockValueLeq;
  refine' ⟨ _, rfl, _ ⟩;
  rw [ blockIterateWhile_eq_iterate_of_cond ];
  · have := pairedDecrLeftIncrRight_iterate_decode block
      (decodeBinaryBlock (splitAtConsBottom block).1) hInv le_rfl;
    rw [ decodeBinaryBlock_eq_splitLeft ] ; aesop;
  · intro k hk;
    have := pairedDecrLeftIncrRight_iterate_decode block k hInv ( by linarith );
    rw [ decodeBinaryBlock_eq_splitLeft ] ; omega

/-- Non-defaultness of the while loop result. -/
theorem binAddPairedWhile_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binAddPairedWhile block, g ≠ default := by
  have h_ind : ∀ (n : ℕ) (block : List ChainΓ), (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ blockIterateWhile pairedDecrLeftIncrRight pairedAddCond n block, g ≠ default := by
    intro n block hblock
    induction' n with n ih generalizing block
    · exact hblock
    · by_cases h : pairedAddCond block <;> simp +decide [h, blockIterateWhile]
      · exact ih _ (pairedDecrLeftIncrRight_ne_default _ hblock h)
      · exact hblock
  unfold binAddPairedWhile
  exact h_ind (decodeBinaryBlock (splitAtConsBottom block).1) block hblock


/-- Under the paired separator invariant, paired addition decomposes through the
    invariant-gated transfer loop, right extraction, and normalization. -/
theorem binAddPaired_eq_while_decomp (block : List ChainΓ)
    (hInv : pairedSepInv block) :
    binAddPaired block = (normalizeBlock ∘ extractPairedRight ∘ binAddPairedWhile) block := by
  unfold binAddPaired normalizeBlock extractPairedRight binAddPairedWhile
  have h_iter : ∀ (k : ℕ), k ≤ decodeBinaryBlock (splitAtConsBottom block).1 →
      blockIterateWhile pairedDecrLeftIncrRight pairedAddCond k block =
        pairedDecrLeftIncrRight^[k] block := by
    intro k hk
    induction' k with k ih generalizing block <;>
      simp_all +decide [Function.iterate_succ_apply', blockIterateWhile]
    rw [if_neg]
    · rw [← Function.iterate_succ_apply' pairedDecrLeftIncrRight k block,
        ih (pairedDecrLeftIncrRight block)
          (pairedDecrLeftIncrRight_pairedSepInv block hInv)]
      · rfl
      · have := pairedDecrLeftIncrRight_iterate_decode block 1 hInv (by linarith)
        simp_all +decide
        exact Nat.le_sub_one_of_lt hk
    · contrapose! hk
      exact le_trans (decodeBinaryBlock_eq_splitLeft block ▸ hk) (Nat.zero_le _)
  simp +decide [h_iter _ le_rfl]
  rw [pairedDecrLeftIncrRight_iterate_decode _ _ hInv le_rfl |>.2]
  rw [add_comm]

/-! ### Block-realizability of paired operations -/

/-- The decrement-left / increment-right step is realized on paired blocks.

This is the useful body theorem for paired addition: the separator invariant is
established outside the body and then preserved by every step. -/
theorem tm0_pairedDecrLeftIncrRight_blockCond :
    TM0RealizesBlockInv pairedDecrLeftIncrRight pairedSepInv :=
  tm0_pairedDecrLeftIncrRight_blockInv

/-- Extracting the right sub-block is block-realizable. -/
theorem tm0_extractPairedRight_block :
    TM0RealizesBlock ChainΓ extractPairedRight := by
  rw [extractPairedRight_eq_dropUntilFirstSep]
  exact tm0_dropUntilFirstSep_block chainConsBottom chainConsBottom_ne_default

/-- Non-defaultness of `extractPairedRight ∘ binAddPairedWhile`. -/
theorem extractPairedRight_binAddPairedWhile_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (extractPairedRight ∘ binAddPairedWhile) block, g ≠ default :=
  fun g hg => extractPairedRight_ne_default _ (binAddPairedWhile_ne_default _ hblock) g hg

/-! ### Paired Block Multiplication

`binMulPaired` is the shared multiplication primitive. Its intended machine
uses paired addition as the inner operation: copy the addend into a paired-add
input, add it into an accumulator, decrement the copied multiplier, and loop. -/

/-- Multiply two binary blocks stored as `[left][sep][right]`. -/
noncomputable def binMulPaired (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  chainBinaryRepr (decodeBinaryBlock left * decodeBinaryBlock right)

theorem binMulPaired_ne_default (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulPaired block, g ≠ default := by
  unfold binMulPaired
  simp +zetaDelta
  exact fun g hg => chainBinaryRepr_ne_default _ g hg

/-- Pair two blocks after normalizing both through binary decode/encode. -/
noncomputable def pairNormalizedBlocks (left right : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (decodeBinaryBlock left) ++ [chainConsBottom] ++
    chainBinaryRepr (decodeBinaryBlock right)

/-- Normalize both sides of a paired block, preserving the separator. -/
noncomputable def normalizePairedBlocks (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  pairNormalizedBlocks left right

theorem pairNormalizedBlocks_ne_default (left right : List ChainΓ)
    (_hleft : ∀ g ∈ left, g ≠ default) (_hright : ∀ g ∈ right, g ≠ default) :
    ∀ g ∈ pairNormalizedBlocks left right, g ≠ default := by
  unfold pairNormalizedBlocks
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · exact chainBinaryRepr_ne_default _ g hg
    · rw [List.mem_singleton.mp hg]
      exact chainConsBottom_ne_default
  · exact chainBinaryRepr_ne_default _ g hg

theorem normalizePairedBlocks_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ normalizePairedBlocks block, g ≠ default := by
  unfold normalizePairedBlocks
  exact pairNormalizedBlocks_ne_default _ _
    (fun g hg => hblock g (splitAtConsBottom_fst_subset block g hg))
    (fun g hg => hblock g (splitAtConsBottom_snd_subset block g hg))

theorem tm0_normalizeBlock_afterConsBottom_innerBlockSep {sep₁ : ChainΓ}
    (hsep₁ : sep₁ ≠ default) (hsep₁_cons : sep₁ ≠ chainConsBottom) :
    TM0RealizesInnerBlockSep ChainΓ sep₁ chainConsBottom normalizeBlock := by
  refine tm0RealizesBlockSep_toInnerOuterSep
    hsep₁
    chainConsBottom_ne_default
    hsep₁_cons
    (tm0_normalizeBlockSep (sep := chainConsBottom) (by decide) (by decide))
    (fun block _hblock => normalizeBlock_ne_default block)
    ?_
  intro block _hblock
  exact normalizeBlock_no_consBottom block

theorem tm0_normalizeBlock_afterConsBottom_innerDefault :
    TM0RealizesInnerBlockDefaultSep ChainΓ chainConsBottom normalizeBlock := by
  refine tm0RealizesBlockSep_toInnerDefault
    chainConsBottom_ne_default
    (tm0_normalizeBlockSep (sep := chainConsBottom) (by decide) (by decide))
    (fun block _hblock => normalizeBlock_ne_default block)
    ?_
  intro block _hblock
  exact normalizeBlock_no_consBottom block

/- The tempting total theorem

     `TM0RealizesBlock ChainΓ normalizePairedBlocks`

   is stronger than the arithmetic pipeline needs.  The problematic cases are
   malformed blocks whose right side contains extra paired separators: the
   semantic function normalizes through the first non-bit, while the existing
   separator-framed lifting lemmas require a clean inner block.  Downstream
   multiplication is therefore routed through normalizing initializers that
   build the invariant loop state directly. -/

/-! #### Multiplication as repeated paired addition

The loop state is `[acc][sep][addend][sep][multiplier-copy]`.
The final field is not a new counter: it is a normalized copy of the right
operand, consumed by predecessor during the loop. -/

/-- Initialize multiplication with accumulator `0`, copied left operand as
    addend, and copied right operand as the loop fuel. -/
noncomputable def binMulPairedInit (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr 0 ++ [chainConsBottom] ++ normalizePairedBlocks block

/-- The copied multiplier field of a multiplication loop state. -/
noncomputable def binMulPairedFuel (block : List ChainΓ) : List ChainΓ :=
  (splitAtConsBottom (splitAtConsBottom block).2).2

/-- Continue while the copied multiplier is positive. -/
noncomputable abbrev binMulPairedCond : List ChainΓ → Prop :=
  fun block => ¬ blockValueLeq 0 (binMulPairedFuel block)

/-- Multiplication loop states have three separator-delimited fields:
    accumulator, addend, and fuel.  The fuel field contains no further
    `chainConsBottom`, so the second separator is the last paired separator
    relevant to the loop body. -/
def binMulPairedStateInv (block : List ChainΓ) : Prop :=
  let rest := (splitAtConsBottom block).2
  hasConsBottom block ∧ hasConsBottom rest ∧
    ∀ g ∈ (splitAtConsBottom rest).2, g ≠ chainConsBottom

theorem binMulPairedStateInv_reconstruct (block : List ChainΓ)
    (hInv : binMulPairedStateInv block) :
    block =
      (splitAtConsBottom block).1 ++ [chainConsBottom] ++
        (splitAtConsBottom (splitAtConsBottom block).2).1 ++ [chainConsBottom] ++
        (splitAtConsBottom (splitAtConsBottom block).2).2 := by
  unfold binMulPairedStateInv at hInv
  rcases hsplit : splitAtConsBottom block with ⟨acc, rest⟩
  rcases hrest : splitAtConsBottom rest with ⟨addend, fuel⟩
  have hblock_rec : block = acc ++ chainConsBottom :: rest := by
    simpa [hsplit] using paired_splitAtConsBottom_reconstruct_of_mem block hInv.1
  have hrest_mem : chainConsBottom ∈ rest := by
    simpa [hsplit] using hInv.2.1
  have hrest_rec : rest = addend ++ chainConsBottom :: fuel := by
    simpa [hrest] using paired_splitAtConsBottom_reconstruct_of_mem rest hrest_mem
  rw [hblock_rec, hrest_rec]
  simp [List.append_assoc]

theorem binMulPairedStateInv_acc_no_consBottom (block : List ChainΓ)
    (_hInv : binMulPairedStateInv block) :
    ∀ g ∈ (splitAtConsBottom block).1, g ≠ chainConsBottom :=
  splitAtConsBottom_fst_no_sep block

theorem binMulPairedStateInv_addend_no_consBottom (block : List ChainΓ)
    (_hInv : binMulPairedStateInv block) :
    ∀ g ∈ (splitAtConsBottom (splitAtConsBottom block).2).1,
      g ≠ chainConsBottom :=
  splitAtConsBottom_fst_no_sep (splitAtConsBottom block).2

theorem binMulPairedStateInv_fuel_no_consBottom (block : List ChainΓ)
    (hInv : binMulPairedStateInv block) :
    ∀ g ∈ (splitAtConsBottom (splitAtConsBottom block).2).2,
      g ≠ chainConsBottom := by
  unfold binMulPairedStateInv at hInv
  exact hInv.2.2

theorem binMulPairedStateInv_acc_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (splitAtConsBottom block).1, g ≠ default := by
  intro g hg
  exact hblock g (splitAtConsBottom_fst_subset block g hg)

theorem binMulPairedStateInv_rest_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (splitAtConsBottom block).2, g ≠ default := by
  intro g hg
  exact hblock g (splitAtConsBottom_snd_subset block g hg)

theorem binMulPairedStateInv_addend_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (splitAtConsBottom (splitAtConsBottom block).2).1,
      g ≠ default := by
  intro g hg
  exact binMulPairedStateInv_rest_ne_default block hblock g
    (splitAtConsBottom_fst_subset (splitAtConsBottom block).2 g hg)

theorem binMulPairedStateInv_fuel_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (splitAtConsBottom (splitAtConsBottom block).2).2,
      g ≠ default := by
  intro g hg
  exact binMulPairedStateInv_rest_ne_default block hblock g
    (splitAtConsBottom_snd_subset (splitAtConsBottom block).2 g hg)

/-- One multiplication iteration:
    add `addend` into `acc` using `binAddPaired`, keep `addend`, and decrement
    the copied multiplier. -/
noncomputable def binMulPairedStep (block : List ChainΓ) : List ChainΓ :=
  let (acc, rest) := splitAtConsBottom block
  let (addend, fuel) := splitAtConsBottom rest
  binAddPaired (acc ++ [chainConsBottom] ++ addend)
    ++ [chainConsBottom]
    ++ addend
    ++ [chainConsBottom]
    ++ binPred fuel

/-- Run the repeated-addition loop, fueled by the copied multiplier. -/
noncomputable def binMulPairedWhile (block : List ChainΓ) : List ChainΓ :=
  let (_, right) := splitAtConsBottom block
  blockIterateWhile binMulPairedStep binMulPairedCond
    (decodeBinaryBlock right) (binMulPairedInit block)

/-- Extract the accumulator from a multiplication loop state. -/
noncomputable def binMulPairedResult (block : List ChainΓ) : List ChainΓ :=
  (splitAtConsBottom block).1

theorem binMulPairedInit_ne_default (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulPairedInit block, g ≠ default := by
  unfold binMulPairedInit
  simp +zetaDelta
  rintro g (hg | rfl | hg)
  · exact chainBinaryRepr_ne_default _ g hg
  · exact chainConsBottom_ne_default
  · exact normalizePairedBlocks_ne_default _ _hblock g hg

theorem binMulPairedInit_stateInv (block : List ChainΓ) :
    binMulPairedStateInv (binMulPairedInit block) := by
  unfold binMulPairedStateInv binMulPairedInit normalizePairedBlocks
    pairNormalizedBlocks hasConsBottom
  rw [splitAtConsBottom_binary_sep]
  constructor
  · simp
  constructor
  · simp
  · rw [splitAtConsBottom_binary_sep]
    exact chainBinaryRepr_no_consBottom _

theorem binMulPairedStep_addInput_pairedSepInv (block : List ChainΓ) :
    let acc := (splitAtConsBottom block).1
    let addend := (splitAtConsBottom (splitAtConsBottom block).2).1
    pairedSepInv (acc ++ [chainConsBottom] ++ addend) := by
  dsimp
  constructor
  · unfold hasConsBottom
    simp
  · rw [splitAtConsBottom_general]
    · exact splitAtConsBottom_fst_no_sep (splitAtConsBottom block).2
    · exact splitAtConsBottom_fst_no_sep block

/-! #### Three-separator multiplication state

The old multiplication loop state reused `chainConsBottom` for every boundary:
the paired-add input separator, the accumulator/addend boundary, and the
addend/fuel boundary.  The following parallel definitions use distinct state
separators.  The paired-add subcall still uses `chainConsBottom`, while the loop
state itself is

`[acc][chainMulSep₁][addend][chainMulSep₂][fuel]`.
-/

noncomputable abbrev binMulStateSep₁ : ChainΓ := chainMulSep₁
noncomputable abbrev binMulStateSep₂ : ChainΓ := chainMulSep₂

noncomputable def binMulPairedInit3 (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  chainBinaryRepr 0 ++ [binMulStateSep₁] ++
    normalizeBlock left ++ [binMulStateSep₂] ++ normalizeBlock right

noncomputable def binMulPairedFuel3 (block : List ChainΓ) : List ChainΓ :=
  (splitAtSep binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2).2

noncomputable abbrev binMulPairedCond3 : List ChainΓ → Prop :=
  fun block => ¬ blockValueLeq 0 (binMulPairedFuel3 block)

def binMulPairedStateInv3 (block : List ChainΓ) : Prop :=
  let rest := (splitAtSep binMulStateSep₁ block).2
  binMulStateSep₁ ∈ block ∧ binMulStateSep₂ ∈ rest ∧
    (∀ g ∈ (splitAtSep binMulStateSep₁ block).1, g ≠ binMulStateSep₂) ∧
    (∀ g ∈ (splitAtSep binMulStateSep₂ rest).1, g ≠ binMulStateSep₁) ∧
    (∀ g ∈ (splitAtSep binMulStateSep₂ rest).2, g ≠ binMulStateSep₁) ∧
    (∀ g ∈ (splitAtSep binMulStateSep₂ rest).2, g ≠ binMulStateSep₂)

theorem binMulPairedStateInv3_reconstruct (block : List ChainΓ)
    (hInv : binMulPairedStateInv3 block) :
    block =
      (splitAtSep binMulStateSep₁ block).1 ++ [binMulStateSep₁] ++
        (splitAtSep binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2).1 ++
          [binMulStateSep₂] ++
        (splitAtSep binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2).2 := by
  unfold binMulPairedStateInv3 at hInv
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have hblock_rec : block = acc ++ binMulStateSep₁ :: rest := by
    simpa [hsplit] using
      splitAtSep_reconstruct_of_mem binMulStateSep₁ block hInv.1
  have hrest_mem : binMulStateSep₂ ∈ rest := by
    simpa [hsplit] using hInv.2.1
  have hrest_rec : rest = addend ++ binMulStateSep₂ :: fuel := by
    simpa [hrest] using
      splitAtSep_reconstruct_of_mem binMulStateSep₂ rest hrest_mem
  rw [hblock_rec, hrest_rec]
  simp [hsplit, hrest, List.append_assoc]

theorem binMulPairedStateInv3_acc_no_sep₁ (block : List ChainΓ)
    (_hInv : binMulPairedStateInv3 block) :
    ∀ g ∈ (splitAtSep binMulStateSep₁ block).1, g ≠ binMulStateSep₁ :=
  splitAtSep_fst_no_sep binMulStateSep₁ block

theorem binMulPairedStateInv3_acc_no_sep₂ (block : List ChainΓ)
    (hInv : binMulPairedStateInv3 block) :
    ∀ g ∈ (splitAtSep binMulStateSep₁ block).1, g ≠ binMulStateSep₂ := by
  unfold binMulPairedStateInv3 at hInv
  exact hInv.2.2.1

theorem binMulPairedStateInv3_addend_no_sep₁ (block : List ChainΓ)
    (hInv : binMulPairedStateInv3 block) :
    ∀ g ∈ (splitAtSep binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2).1,
      g ≠ binMulStateSep₁ := by
  unfold binMulPairedStateInv3 at hInv
  exact hInv.2.2.2.1

theorem binMulPairedStateInv3_addend_no_sep₂ (block : List ChainΓ)
    (_hInv : binMulPairedStateInv3 block) :
    ∀ g ∈ (splitAtSep binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2).1,
      g ≠ binMulStateSep₂ :=
  splitAtSep_fst_no_sep binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2

theorem binMulPairedStateInv3_fuel_no_sep₁ (block : List ChainΓ)
    (hInv : binMulPairedStateInv3 block) :
    ∀ g ∈ binMulPairedFuel3 block, g ≠ binMulStateSep₁ := by
  unfold binMulPairedFuel3 binMulPairedStateInv3 at *
  exact hInv.2.2.2.2.1

theorem binMulPairedStateInv3_fuel_no_sep₂ (block : List ChainΓ)
    (hInv : binMulPairedStateInv3 block) :
    ∀ g ∈ binMulPairedFuel3 block, g ≠ binMulStateSep₂ := by
  unfold binMulPairedFuel3 binMulPairedStateInv3 at *
  exact hInv.2.2.2.2.2

theorem binMulPairedStateInv3_acc_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (splitAtSep binMulStateSep₁ block).1, g ≠ default := by
  intro g hg
  exact hblock g (splitAtSep_fst_subset binMulStateSep₁ block g hg)

theorem binMulPairedStateInv3_rest_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (splitAtSep binMulStateSep₁ block).2, g ≠ default := by
  intro g hg
  exact hblock g (splitAtSep_snd_subset binMulStateSep₁ block g hg)

theorem binMulPairedStateInv3_addend_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (splitAtSep binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2).1,
      g ≠ default := by
  intro g hg
  exact binMulPairedStateInv3_rest_ne_default block hblock g
    (splitAtSep_fst_subset binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2 g hg)

theorem binMulPairedStateInv3_fuel_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulPairedFuel3 block, g ≠ default := by
  intro g hg
  unfold binMulPairedFuel3 at hg
  exact binMulPairedStateInv3_rest_ne_default block hblock g
    (splitAtSep_snd_subset binMulStateSep₂ (splitAtSep binMulStateSep₁ block).2 g hg)

noncomputable def binMulPairedStep3 (block : List ChainΓ) : List ChainΓ :=
  let (acc, rest) := splitAtSep binMulStateSep₁ block
  let (addend, fuel) := splitAtSep binMulStateSep₂ rest
  binAddPairedKeepRightSep binMulStateSep₁
      (acc ++ [binMulStateSep₁] ++ addend)
    ++ [binMulStateSep₂]
    ++ binPred fuel

noncomputable def binMulPairedResult3 (block : List ChainΓ) : List ChainΓ :=
  (splitAtSep binMulStateSep₁ block).1

@[simp]
theorem splitAtSep_chainBinaryRepr_sep₁ (c : ℕ) (block : List ChainΓ) :
    splitAtSep binMulStateSep₁ (chainBinaryRepr c ++ [binMulStateSep₁] ++ block) =
      (chainBinaryRepr c, block) := by
  exact splitAtSep_general binMulStateSep₁ (chainBinaryRepr c) block
    (by simpa [binMulStateSep₁] using chainBinaryRepr_no_chainMulSep₁ c)

@[simp]
theorem splitAtSep_chainBinaryRepr_sep₁_cons (c : ℕ) (block : List ChainΓ) :
    splitAtSep binMulStateSep₁ (chainBinaryRepr c ++ binMulStateSep₁ :: block) =
      (chainBinaryRepr c, block) := by
  simpa using splitAtSep_chainBinaryRepr_sep₁ c block

@[simp]
theorem splitAtSep_chainBinaryRepr_sep₂ (c : ℕ) (block : List ChainΓ) :
    splitAtSep binMulStateSep₂ (chainBinaryRepr c ++ [binMulStateSep₂] ++ block) =
      (chainBinaryRepr c, block) := by
  exact splitAtSep_general binMulStateSep₂ (chainBinaryRepr c) block
    (by simpa [binMulStateSep₂] using chainBinaryRepr_no_chainMulSep₂ c)

@[simp]
theorem splitAtSep_chainBinaryRepr_sep₂_cons (c : ℕ) (block : List ChainΓ) :
    splitAtSep binMulStateSep₂ (chainBinaryRepr c ++ binMulStateSep₂ :: block) =
      (chainBinaryRepr c, block) := by
  simpa using splitAtSep_chainBinaryRepr_sep₂ c block

theorem normalizeBlock_no_mulSep₁ (block : List ChainΓ) :
    ∀ g ∈ normalizeBlock block, g ≠ binMulStateSep₁ := by
  unfold normalizeBlock
  simpa [binMulStateSep₁] using
    chainBinaryRepr_no_chainMulSep₁ (decodeBinaryBlock block)

theorem normalizeBlock_no_mulSep₂ (block : List ChainΓ) :
    ∀ g ∈ normalizeBlock block, g ≠ binMulStateSep₂ := by
  unfold normalizeBlock
  simpa [binMulStateSep₂] using
    chainBinaryRepr_no_chainMulSep₂ (decodeBinaryBlock block)

@[simp]
theorem splitAtSep_normalizeBlock_sep₁ (left right : List ChainΓ) :
    splitAtSep binMulStateSep₁ (normalizeBlock left ++ binMulStateSep₁ :: right) =
      (normalizeBlock left, right) := by
  exact splitAtSep_general_cons binMulStateSep₁ (normalizeBlock left) right
    (normalizeBlock_no_mulSep₁ left)

@[simp]
theorem splitAtSep_normalizeBlock_sep₂ (left right : List ChainΓ) :
    splitAtSep binMulStateSep₂ (normalizeBlock left ++ binMulStateSep₂ :: right) =
      (normalizeBlock left, right) := by
  exact splitAtSep_general_cons binMulStateSep₂ (normalizeBlock left) right
    (normalizeBlock_no_mulSep₂ left)

theorem binPred_no_mulSep₁ (block : List ChainΓ) :
    ∀ g ∈ binPred block, g ≠ binMulStateSep₁ := by
  unfold binPred
  simpa [binMulStateSep₁] using
    chainBinaryRepr_no_chainMulSep₁ (decodeBinaryBlock block - 1)

theorem binPred_no_mulSep₂ (block : List ChainΓ) :
    ∀ g ∈ binPred block, g ≠ binMulStateSep₂ := by
  unfold binPred
  simpa [binMulStateSep₂] using
    chainBinaryRepr_no_chainMulSep₂ (decodeBinaryBlock block - 1)

theorem binAddPaired_no_mulSep₁ (block : List ChainΓ) :
    ∀ g ∈ binAddPaired block, g ≠ binMulStateSep₁ := by
  unfold binAddPaired
  simpa [binMulStateSep₁] using
    chainBinaryRepr_no_chainMulSep₁
      (decodeBinaryBlock (splitAtConsBottom block).1 +
        decodeBinaryBlock (splitAtConsBottom block).2)

theorem binAddPaired_no_mulSep₂ (block : List ChainΓ) :
    ∀ g ∈ binAddPaired block, g ≠ binMulStateSep₂ := by
  unfold binAddPaired
  simpa [binMulStateSep₂] using
    chainBinaryRepr_no_chainMulSep₂
      (decodeBinaryBlock (splitAtConsBottom block).1 +
        decodeBinaryBlock (splitAtConsBottom block).2)

theorem binAddPairedSep_no_mulSep₁ (sep : ChainΓ) (block : List ChainΓ) :
    ∀ g ∈ binAddPairedSep sep block, g ≠ binMulStateSep₁ := by
  unfold binAddPairedSep
  rcases splitAtSep sep block with ⟨left, right⟩
  simpa [binMulStateSep₁] using
    chainBinaryRepr_no_chainMulSep₁
      (decodeBinaryBlock left + decodeBinaryBlock right)

theorem binAddPairedSep_no_mulSep₂ (sep : ChainΓ) (block : List ChainΓ) :
    ∀ g ∈ binAddPairedSep sep block, g ≠ binMulStateSep₂ := by
  unfold binAddPairedSep
  rcases splitAtSep sep block with ⟨left, right⟩
  simpa [binMulStateSep₂] using
    chainBinaryRepr_no_chainMulSep₂
      (decodeBinaryBlock left + decodeBinaryBlock right)

theorem binMulPairedInit3_ne_default (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulPairedInit3 block, g ≠ default := by
  unfold binMulPairedInit3
  rcases splitAtConsBottom block with ⟨left, right⟩
  simp
  rintro g (hg | rfl | hg | rfl | hg)
  · exact chainBinaryRepr_ne_default _ g hg
  · exact chainMulSep₁_ne_default
  · exact normalizeBlock_ne_default left g hg
  · exact chainMulSep₂_ne_default
  · exact normalizeBlock_ne_default right g hg

theorem binMulPairedInit3_stateInv (block : List ChainΓ) :
    binMulPairedStateInv3 (binMulPairedInit3 block) := by
  unfold binMulPairedStateInv3 binMulPairedInit3
  rcases splitAtConsBottom block with ⟨left, right⟩
  simp [chainMulSep₁_ne_chainMulSep₂]
  constructor
  · simpa [binMulStateSep₂] using chainBinaryRepr_no_chainMulSep₂ 0
  constructor
  · exact normalizeBlock_no_mulSep₁ left
  constructor
  · exact normalizeBlock_no_mulSep₁ right
  · exact normalizeBlock_no_mulSep₂ right

theorem binMulPairedFuel3_normalized_state (acc addend fuel : ℕ) :
    binMulPairedFuel3
      (chainBinaryRepr acc ++ [binMulStateSep₁] ++ chainBinaryRepr addend ++
        [binMulStateSep₂] ++ chainBinaryRepr fuel) =
      chainBinaryRepr fuel := by
  simp [binMulPairedFuel3, List.append_assoc]

theorem binMulPairedStep3_normalized_state (acc addend fuel : ℕ) :
    binMulPairedStep3
      (chainBinaryRepr acc ++ [binMulStateSep₁] ++ chainBinaryRepr addend ++
        [binMulStateSep₂] ++ chainBinaryRepr fuel) =
    chainBinaryRepr (acc + addend) ++ [binMulStateSep₁] ++ chainBinaryRepr addend ++
      [binMulStateSep₂] ++ chainBinaryRepr (fuel - 1) := by
  simp [binMulPairedStep3, binAddPairedKeepRightSep, binAddPairedSep,
    binPred, List.append_assoc]

theorem binMulPairedStep3_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) (_hcond : binMulPairedCond3 block) :
    ∀ g ∈ binMulPairedStep3 block, g ≠ default := by
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have hacc : ∀ g ∈ acc, g ≠ default := by
    intro g hg
    exact hblock g (splitAtSep_fst_subset binMulStateSep₁ block g
      (by simpa [hsplit] using hg))
  have hrest_block : ∀ g ∈ rest, g ≠ default := by
    intro g hg
    exact hblock g (splitAtSep_snd_subset binMulStateSep₁ block g
      (by simpa [hsplit] using hg))
  have haddend : ∀ g ∈ addend, g ≠ default := by
    intro g hg
    exact hrest_block g (splitAtSep_fst_subset binMulStateSep₂ rest g
      (by simpa [hrest] using hg))
  have hfuel : ∀ g ∈ fuel, g ≠ default := by
    intro g hg
    exact hrest_block g (splitAtSep_snd_subset binMulStateSep₂ rest g
      (by simpa [hrest] using hg))
  have haddInput : ∀ g ∈ acc ++ binMulStateSep₁ :: addend, g ≠ default := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hacc g hg
    · cases hg with
      | head => exact chainMulSep₁_ne_default
      | tail _ hg => exact haddend g hg
  have hkeep_nd :
      ∀ g ∈ binAddPairedKeepRightSep binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend),
        g ≠ default :=
    binAddPairedKeepRightSep_ne_default binMulStateSep₁
      (acc ++ binMulStateSep₁ :: addend)
      chainMulSep₁_ne_default haddInput
  unfold binMulPairedStep3
  simp [hsplit, hrest]
  rintro g (hg | rfl | hg)
  · exact hkeep_nd g hg
  · exact chainMulSep₂_ne_default
  · exact binPred_ne_default _ hfuel g hg

theorem binMulPairedStep3_stateInv (block : List ChainΓ)
    (hInv : binMulPairedStateInv3 block) :
    binMulPairedStateInv3 (binMulPairedStep3 block) := by
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have haddend_no_sep₁ : ∀ g ∈ addend, g ≠ binMulStateSep₁ := by
    simpa [hsplit, hrest] using binMulPairedStateInv3_addend_no_sep₁ block hInv
  have haddend_no_sep₂ : ∀ g ∈ addend, g ≠ binMulStateSep₂ := by
    simpa [hsplit, hrest] using binMulPairedStateInv3_addend_no_sep₂ block hInv
  have hfuel_no_sep₁ : ∀ g ∈ fuel, g ≠ binMulStateSep₁ := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_no_sep₁ block hInv
  have hfuel_no_sep₂ : ∀ g ∈ fuel, g ≠ binMulStateSep₂ := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_no_sep₂ block hInv
  have hacc_no_sep₁ : ∀ g ∈ acc, g ≠ binMulStateSep₁ := by
    simpa [hsplit] using splitAtSep_fst_no_sep binMulStateSep₁ block
  have hkeep :
      binAddPairedKeepRightSep binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend) =
        binAddPairedSep binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend) ++
          binMulStateSep₁ :: addend := by
    exact binAddPairedKeepRightSep_eq_cons binMulStateSep₁ acc addend
      hacc_no_sep₁
  have hstep_split₁ :
      splitAtSep binMulStateSep₁
        (binAddPairedKeepRightSep binMulStateSep₁
            (acc ++ binMulStateSep₁ :: addend) ++
          binMulStateSep₂ :: binPred fuel) =
        (binAddPairedSep binMulStateSep₁
            (acc ++ binMulStateSep₁ :: addend),
          addend ++ binMulStateSep₂ :: binPred fuel) := by
    rw [hkeep]
    simpa [List.append_assoc] using
      splitAtSep_general_cons binMulStateSep₁
        (binAddPairedSep binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend))
        (addend ++ binMulStateSep₂ :: binPred fuel)
        (binAddPairedSep_no_mulSep₁ binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend))
  have hstep_split₂ :
      splitAtSep binMulStateSep₂ (addend ++ binMulStateSep₂ :: binPred fuel) =
        (addend, binPred fuel) := by
    exact splitAtSep_general_cons binMulStateSep₂ addend (binPred fuel)
      haddend_no_sep₂
  unfold binMulPairedStateInv3 binMulPairedStep3
  simp [hsplit, hrest, hstep_split₁, hstep_split₂,
    chainMulSep₁_ne_chainMulSep₂]
  constructor
  · left
    rw [hkeep]
    simp
  constructor
  · exact binAddPairedSep_no_mulSep₂ binMulStateSep₁
      (acc ++ binMulStateSep₁ :: addend)
  constructor
  · exact haddend_no_sep₁
  constructor
  · exact binPred_no_mulSep₁ fuel
  · exact binPred_no_mulSep₂ fuel


/-- A machine that runs a paired-block operation before the next
    `chainConsBottom`.

This is intentionally not `TM0RealizesBlockSep`: the operated segment itself
contains one internal `chainConsBottom`, so the usual no-separator block
premise would be false.  The intended tape shape is
`left ++ sep :: right ++ sep :: suffix`; only `left ++ sep :: right` is
rewritten. -/
def TM0RealizesPairedBeforeConsBottom
    (f : List ChainΓ → List ChainΓ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine ChainΓ Λ),
    ∀ (left right suffix : List ChainΓ),
      (∀ g ∈ left, g ≠ default) →
      (∀ g ∈ left, g ≠ chainConsBottom) →
      (∀ g ∈ right, g ≠ default) →
      (∀ g ∈ right, g ≠ chainConsBottom) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f (left ++ [chainConsBottom] ++ right), g ≠ default) →
      (∀ g ∈ f (left ++ [chainConsBottom] ++ right), g ≠ chainConsBottom) →
      (TM0Seq.evalCfg M
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom),
        ((TM0Seq.evalCfg M
          (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get h).Tape =
          Tape.mk₁ (f (left ++ [chainConsBottom] ++ right) ++
            chainConsBottom :: suffix)

/-- A machine that rewrites a paired block before the next `chainConsBottom`.

Unlike `TM0RealizesPairedBeforeConsBottom`, this allows the output of `f` to
still contain the internal paired separator.  This is the shape for paired-add
loop bodies; the final paired-add operation removes the internal separator. -/
def TM0RealizesPairedBlockBeforeConsBottom
    (f : List ChainΓ → List ChainΓ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine ChainΓ Λ),
    ∀ (left right suffix : List ChainΓ),
      (∀ g ∈ left, g ≠ default) →
      (∀ g ∈ left, g ≠ chainConsBottom) →
      (∀ g ∈ right, g ≠ default) →
      (∀ g ∈ right, g ≠ chainConsBottom) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f (left ++ [chainConsBottom] ++ right), g ≠ default) →
      (TM0Seq.evalCfg M
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom),
        ((TM0Seq.evalCfg M
          (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get h).Tape =
          Tape.mk₁ (f (left ++ [chainConsBottom] ++ right) ++
            chainConsBottom :: suffix)

def TM0RealizesPairedBlockBeforeConsBottomCond
    (step : List ChainΓ → List ChainΓ) (cond : List ChainΓ → Prop)
    [DecidablePred cond] : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine ChainΓ Λ) (q_cont : Λ),
    ∀ (left right suffix : List ChainΓ),
      (∀ g ∈ left, g ≠ default) →
      (∀ g ∈ left, g ≠ chainConsBottom) →
      (∀ g ∈ right, g ≠ default) →
      (∀ g ∈ right, g ≠ chainConsBottom) →
      (∀ g ∈ suffix, g ≠ default) →
      (cond (left ++ [chainConsBottom] ++ right) →
        ∀ g ∈ step (left ++ [chainConsBottom] ++ right), g ≠ default) →
      (TM0Seq.evalCfg M
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom),
        let cfg := (TM0Seq.evalCfg M
          (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get h
        if cond (left ++ [chainConsBottom] ++ right) then
          cfg.q = q_cont ∧
          cfg.Tape = Tape.mk₁
            (step (left ++ [chainConsBottom] ++ right) ++
              chainConsBottom :: suffix)
        else
          cfg.q ≠ q_cont ∧
          cfg.Tape = Tape.mk₁
            (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)

theorem condCompose_fixed_at_halt_true_of_step_local
    {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)
    (q_done : Λ_f) (T T' : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_t, T⟩ = none)
    (h_step : ∃ c₂, TM0.step M_f ⟨default, T⟩ = some c₂)
    (h_f_dom : (TM0Seq.evalFromCfg M_f ⟨default, T⟩).Dom)
    (h_f_spec : ∀ h, (TM0Seq.evalFromCfg M_f ⟨default, T⟩).get h =
      ⟨q_done, T'⟩) :
    let step_c := @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
    ∀ (h_c_dom : (Turing.eval step_c ⟨Sum.inl q_t, T⟩).Dom),
      (Turing.eval step_c ⟨Sum.inl q_t, T⟩).get h_c_dom =
        ⟨Sum.inr (Sum.inl q_done), T'⟩ := by
  intro step_c h_c_dom
  obtain ⟨c₂, h_step_f⟩ := h_step
  have h_step_c : step_c ⟨Sum.inl q_t, T⟩ =
      some ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩ := by
    show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _
      (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
    rw [condCompose_halt_true M_p M_f M_g q_t q_f T h_halt]
    simp [h_step_f]
  have h_eval_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_c)
  have h_eval_f_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_f)
  have hb_f_mem_c2 :
      ⟨q_done, T'⟩ ∈ Turing.eval (TM0.step M_f) c₂ := by
    rw [← h_eval_f_eq]
    exact h_f_spec h_f_dom ▸ Part.get_mem h_f_dom
  obtain ⟨b₂, hb₂_rel, hb₂_mem⟩ := Turing.tr_eval
    (condCompose_f_respects M_p M_f M_g q_t q_f)
    (a₁ := c₂) (a₂ := ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩)
    ⟨rfl, rfl⟩ hb_f_mem_c2
  have hb₂_mem' : b₂ ∈ Turing.eval step_c ⟨Sum.inl q_t, T⟩ := by
    rw [h_eval_eq]
    exact hb₂_mem
  have hb₂_eq : b₂ = ⟨Sum.inr (Sum.inl q_done), T'⟩ := by
    rcases hb₂_rel with ⟨hq, hT⟩
    cases b₂
    simp at hq hT
    simp [hq, hT]
  exact (Part.get_eq_of_mem hb₂_mem' h_c_dom).trans hb₂_eq

theorem condCompose_fixed_at_halt_false_of_step_local
    {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)
    (hne : q_t ≠ q_f)
    (q_done : Λ_g) (T T' : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_f, T⟩ = none)
    (h_step : ∃ c₂, TM0.step M_g ⟨default, T⟩ = some c₂)
    (h_g_dom : (TM0Seq.evalFromCfg M_g ⟨default, T⟩).Dom)
    (h_g_spec : ∀ h, (TM0Seq.evalFromCfg M_g ⟨default, T⟩).get h =
      ⟨q_done, T'⟩) :
    let step_c := @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
    ∀ (h_c_dom : (Turing.eval step_c ⟨Sum.inl q_f, T⟩).Dom),
      (Turing.eval step_c ⟨Sum.inl q_f, T⟩).get h_c_dom =
        ⟨Sum.inr (Sum.inr q_done), T'⟩ := by
  intro step_c h_c_dom
  obtain ⟨c₂, h_step_g⟩ := h_step
  have h_step_c : step_c ⟨Sum.inl q_f, T⟩ =
      some ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩ := by
    show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _
      (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
    rw [condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt]
    simp [h_step_g]
  have h_eval_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_c)
  have h_eval_g_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_g)
  have hb_g_mem_c2 :
      ⟨q_done, T'⟩ ∈ Turing.eval (TM0.step M_g) c₂ := by
    rw [← h_eval_g_eq]
    exact h_g_spec h_g_dom ▸ Part.get_mem h_g_dom
  obtain ⟨b₂, hb₂_rel, hb₂_mem⟩ := Turing.tr_eval
    (condCompose_g_respects M_p M_f M_g q_t q_f)
    (a₁ := c₂) (a₂ := ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩)
    ⟨rfl, rfl⟩ hb_g_mem_c2
  have hb₂_mem' : b₂ ∈ Turing.eval step_c ⟨Sum.inl q_f, T⟩ := by
    rw [h_eval_eq]
    exact hb₂_mem
  have hb₂_eq : b₂ = ⟨Sum.inr (Sum.inr q_done), T'⟩ := by
    rcases hb₂_rel with ⟨hq, hT⟩
    cases b₂
    simp at hq hT
    simp [hq, hT]
  exact (Part.get_eq_of_mem hb₂_mem' h_c_dom).trans hb₂_eq

/-- A machine that runs an operation on the field after the first
    `chainConsBottom`, bounded by the next `chainConsBottom`. -/
def TM0RealizesAfterFirstBeforeSecondConsBottom
    (f : List ChainΓ → List ChainΓ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine ChainΓ Λ),
    ∀ (left right suffix : List ChainΓ),
      (∀ g ∈ left, g ≠ default) →
      (∀ g ∈ left, g ≠ chainConsBottom) →
      (∀ g ∈ right, g ≠ default) →
      (∀ g ∈ right, g ≠ chainConsBottom) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f right, g ≠ default) →
      (∀ g ∈ f right, g ≠ chainConsBottom) →
      (TM0Seq.evalCfg M
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom),
        ((TM0Seq.evalCfg M
          (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get h).Tape =
          Tape.mk₁ (left ++ chainConsBottom :: f right ++
            chainConsBottom :: suffix)

inductive BinSuccAfterFirstConsBottomSt where
  | scan | succ (q : BinSuccSt)

noncomputable instance : DecidableEq BinSuccAfterFirstConsBottomSt :=
  Classical.typeDecidableEq _
noncomputable instance : Inhabited BinSuccAfterFirstConsBottomSt := ⟨.scan⟩

noncomputable instance : Fintype BinSuccAfterFirstConsBottomSt := by
  exact
  { elems := {.scan} ∪ Finset.univ.map
      ⟨BinSuccAfterFirstConsBottomSt.succ, fun a b h => by cases h; rfl⟩
    complete := by
      intro x
      cases x <;> simp [Finset.mem_map, Finset.mem_insert] }

noncomputable def binSuccAfterFirstConsBottomMachine :
    @TM0.Machine ChainΓ BinSuccAfterFirstConsBottomSt ⟨.scan⟩ :=
  fun q a =>
    match q with
    | .scan =>
      if a = chainConsBottom then some (.succ .carry, .move Dir.right)
      else if a = default then none
      else some (.scan, .move Dir.right)
    | .succ q =>
      match binSuccMachineSep chainConsBottom q a with
      | some (q', stmt) => some (.succ q', stmt)
      | none => none

theorem binSuccAfterFirstConsBottom_succ_lift {c d : TM0.Cfg ChainΓ BinSuccSt}
    (h : Reaches (TM0.step (binSuccMachineSep chainConsBottom)) c d) :
    Reaches (TM0.step binSuccAfterFirstConsBottomMachine)
      ⟨BinSuccAfterFirstConsBottomSt.succ c.q, c.Tape⟩
      ⟨BinSuccAfterFirstConsBottomSt.succ d.q, d.Tape⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      refine ih.tail ?_
      unfold TM0.step at hstep ⊢
      simp [binSuccAfterFirstConsBottomMachine] at hstep ⊢
      rcases hstep with ⟨q', stmt, hstep, hcfg⟩
      exact ⟨stmt, by rw [hstep]; cases hcfg; simp⟩

theorem binSuccAfterFirstConsBottom_step_done (T : Tape ChainΓ) :
    TM0.step binSuccAfterFirstConsBottomMachine
      ⟨BinSuccAfterFirstConsBottomSt.succ BinSuccSt.done, T⟩ = none := by
  simp [TM0.step, binSuccAfterFirstConsBottomMachine, binSuccMachineSep]

theorem binSuccAfterFirstConsBottom_scan_reaches
    (left revLeft right suffix : List ChainΓ)
    (hleft_nd : ∀ g ∈ left, g ≠ default)
    (hleft_nsep : ∀ g ∈ left, g ≠ chainConsBottom)
    (hrevLeft_nd : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccAfterFirstConsBottomMachine)
      ⟨.scan, ⟨(left ++ chainConsBottom :: right ++ chainConsBottom :: suffix).headI,
        ListBlank.mk revLeft,
        ListBlank.mk (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix).tail⟩⟩
      ⟨.succ .carry, ⟨(right ++ chainConsBottom :: suffix).headI,
        ListBlank.mk (chainConsBottom :: left.reverse ++ revLeft),
        ListBlank.mk (right ++ chainConsBottom :: suffix).tail⟩⟩ := by
  induction left generalizing revLeft with
  | nil =>
      apply Relation.ReflTransGen.single
      unfold TM0.step binSuccAfterFirstConsBottomMachine
      simp [Tape.move, ListBlank.cons_mk]
  | cons c rest ih =>
      have hc_nd : c ≠ default := hleft_nd c List.mem_cons_self
      have hc_nsep : c ≠ chainConsBottom := hleft_nsep c List.mem_cons_self
      have hrest_nd : ∀ g ∈ rest, g ≠ default :=
        fun g hg => hleft_nd g (List.mem_cons_of_mem _ hg)
      have hrest_nsep : ∀ g ∈ rest, g ≠ chainConsBottom :=
        fun g hg => hleft_nsep g (List.mem_cons_of_mem _ hg)
      have hstep : TM0.step binSuccAfterFirstConsBottomMachine
          ⟨BinSuccAfterFirstConsBottomSt.scan,
            ⟨((c :: rest) ++ chainConsBottom :: right ++ chainConsBottom :: suffix).headI,
              ListBlank.mk revLeft,
              ListBlank.mk
                (((c :: rest) ++ chainConsBottom :: right ++ chainConsBottom :: suffix).tail)⟩⟩ =
          some ⟨BinSuccAfterFirstConsBottomSt.scan,
            ⟨(rest ++ chainConsBottom :: right ++ chainConsBottom :: suffix).headI,
              ListBlank.mk (c :: revLeft),
              ListBlank.mk
                ((rest ++ chainConsBottom :: right ++ chainConsBottom :: suffix).tail)⟩⟩ := by
        unfold TM0.step binSuccAfterFirstConsBottomMachine
        simp [hc_nd, hc_nsep, Tape.move]
      refine Relation.ReflTransGen.head hstep ?_
      convert ih (c :: revLeft) hrest_nd hrest_nsep ?_ using 1
      · simp [List.reverse_cons, List.append_assoc]
      · intro g hg
        cases hg with
        | head => exact hc_nd
        | tail _ hg => exact hrevLeft_nd g hg

theorem binSuccAfterFirstConsBottom_full_reaches
    (left right suffix : List ChainΓ)
    (hleft_nd : ∀ g ∈ left, g ≠ default)
    (hleft_nsep : ∀ g ∈ left, g ≠ chainConsBottom)
    (hright_nd : ∀ g ∈ right, g ≠ default)
    (hright_nsep : ∀ g ∈ right, g ≠ chainConsBottom)
    (hsuffix_nd : ∀ g ∈ suffix, g ≠ default)
    (hbinSucc_nd : ∀ g ∈ binSucc right, g ≠ default) :
    Reaches (TM0.step binSuccAfterFirstConsBottomMachine)
      (TM0.init (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix))
      ⟨.succ .done,
        Tape.mk₁ (left ++ chainConsBottom :: binSucc right ++
          chainConsBottom :: suffix)⟩ := by
  have hscan := binSuccAfterFirstConsBottom_scan_reaches left [] right suffix
    hleft_nd hleft_nsep (by simp)
  have hsucc := binSucc_carry_aux_sep chainConsBottom
    (by decide) (by decide) chainConsBottom_ne_default
    right suffix (chainConsBottom :: left.reverse)
    hright_nd hright_nsep hsuffix_nd hbinSucc_nd
    (by
      intro g hg
      cases hg with
      | head => exact chainConsBottom_ne_default
      | tail _ hg => exact reverse_ne_default left hleft_nd g hg)
  have hsucc_lift := binSuccAfterFirstConsBottom_succ_lift hsucc
  have hscan' :
      Reaches (TM0.step binSuccAfterFirstConsBottomMachine)
        (TM0.init (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix))
        ⟨.succ .carry, ⟨(right ++ chainConsBottom :: suffix).headI,
          ListBlank.mk (chainConsBottom :: left.reverse),
          ListBlank.mk (right ++ chainConsBottom :: suffix).tail⟩⟩ := by
    simpa using hscan
  convert hscan'.trans hsucc_lift using 1
  simp [List.append_assoc]

theorem tm0_binSucc_afterFirstBeforeSecondConsBottom :
    TM0RealizesAfterFirstBeforeSecondConsBottom binSucc := by
  refine ⟨BinSuccAfterFirstConsBottomSt, inferInstance, inferInstance,
    binSuccAfterFirstConsBottomMachine, ?_⟩
  intro left right suffix hleft_nd hleft_nsep hright_nd hright_nsep hsuffix_nd
    hf_nd _hf_nsep
  have h_reaches := binSuccAfterFirstConsBottom_full_reaches left right suffix
    hleft_nd hleft_nsep hright_nd hright_nsep hsuffix_nd hf_nd
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr
      ⟨h_reaches, binSuccAfterFirstConsBottom_step_done _⟩⟩
  · intro h
    exact (Part.mem_unique (Part.get_mem h) (Turing.mem_eval.mpr
      ⟨h_reaches, binSuccAfterFirstConsBottom_step_done _⟩)).symm ▸ rfl

noncomputable def pairedDecrLeftIncrRightRaw (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  binPred left ++ [chainConsBottom] ++ binSucc right

theorem pairedDecrLeftIncrRightRaw_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pairedDecrLeftIncrRightRaw block, g ≠ default := by
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  have hleft_nd : ∀ g ∈ left, g ≠ default := by
    intro g hg
    exact hblock g (splitAtConsBottom_fst_subset block g (by simpa [hsplit] using hg))
  have hright_nd : ∀ g ∈ right, g ≠ default := by
    intro g hg
    exact hblock g (splitAtConsBottom_snd_subset block g (by simpa [hsplit] using hg))
  unfold pairedDecrLeftIncrRightRaw
  simp [hsplit]
  rintro g (hg | rfl | hg)
  · exact binPred_ne_default _ hleft_nd g hg
  · exact chainConsBottom_ne_default
  · exact binSucc_ne_default _ hright_nd g hg

theorem pairedDecrLeftIncrRightRaw_eq_pairedDecrLeftIncrRight_of_right_normalized
    (block : List ChainΓ) (hInv : pairedSepInv block)
    (n : ℕ) (hright : (splitAtConsBottom block).2 = chainBinaryRepr n) :
    pairedDecrLeftIncrRightRaw block = pairedDecrLeftIncrRight block := by
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  have hright' : right = chainBinaryRepr n := by
    simpa [hsplit] using hright
  rw [pairedDecrLeftIncrRight_eq_binPred_binSuccNormalize block hInv]
  unfold pairedDecrLeftIncrRightRaw Function.comp normalizeBlock
  simp [hsplit, hright', binSucc_correct]

theorem blockValueLeq_paired_prefix_append_secondSep
    (k : ℕ) (left right suffix : List ChainΓ) :
    blockValueLeq k
        (left ++ [chainConsBottom] ++ right ++ [chainConsBottom] ++ suffix) ↔
      blockValueLeq k (left ++ [chainConsBottom] ++ right) := by
  unfold blockValueLeq
  have hdecode :
      decodeBinaryBlock
          (left ++ [chainConsBottom] ++ right ++ [chainConsBottom] ++ suffix) =
        decodeBinaryBlock (left ++ [chainConsBottom] ++ right) := by
    convert decodeBinaryBlock_append_nonbit
      (left ++ [chainConsBottom] ++ right) suffix chainConsBottom
        (by decide) (by decide) using 2
    simp [List.append_assoc]
  rw [hdecode]

theorem tm0_pairedDecrLeftIncrRightRaw_beforeSecond :
    TM0RealizesPairedBlockBeforeConsBottom pairedDecrLeftIncrRightRaw := by
  obtain ⟨Λp, hΛpi, hΛpf, Mp, hMp⟩ := tm0_incBeforeSep_present_blockSep
  obtain ⟨Λs, hΛsi, hΛsf, Ms, hMs⟩ :=
    tm0_binSucc_afterFirstBeforeSecondConsBottom
  let hsum : Inhabited (Λp ⊕ Λs) := ⟨Sum.inl (@default _ hΛpi)⟩
  refine ⟨Λp ⊕ Λs, hsum, inferInstance,
    @TM0Seq.compose ChainΓ Λp hΛpi Λs hΛsi Mp Ms, ?_⟩
  intro left right suffix hleft_nd hleft_nsep hright_nd hright_nsep hsuffix_nd hf_nd
  have hpred_nd : ∀ g ∈ binPred left, g ≠ default :=
    binPred_ne_default left hleft_nd
  have hpred_nsep : ∀ g ∈ binPred left, g ≠ chainConsBottom :=
    binPred_no_consBottom left
  have hsucc_nd : ∀ g ∈ binSucc right, g ≠ default :=
    binSucc_ne_default right hright_nd
  have hsucc_nsep : ∀ g ∈ binSucc right, g ≠ chainConsBottom :=
    binSucc_no_consBottom right hright_nsep
  obtain ⟨hp_dom, hp_tape⟩ :=
    hMp left (right ++ [chainConsBottom] ++ suffix)
      hleft_nd hleft_nsep
      (by
        intro g hg
        simp [List.mem_append] at hg
        rcases hg with hg | rfl | hg
        · exact hright_nd g hg
        · exact chainConsBottom_ne_default
        · exact hsuffix_nd g hg)
      hpred_nd hpred_nsep
  have hp_dom' :
      (TM0Seq.evalCfg Mp
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom := by
    simpa [List.append_assoc] using hp_dom
  have hp_tape' :
      ((TM0Seq.evalCfg Mp
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get hp_dom').Tape =
        Tape.mk₁ (binPred left ++ chainConsBottom :: right ++ chainConsBottom :: suffix) := by
    have hget :
        (TM0Seq.evalCfg Mp
          (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get hp_dom' =
          (TM0Seq.evalCfg Mp
            (left ++ chainConsBottom :: (right ++ [chainConsBottom] ++ suffix))).get hp_dom := by
      apply Part.get_eq_get_of_eq
      simp [List.append_assoc]
    rw [hget, hp_tape hp_dom]
    simp [List.append_assoc]
  obtain ⟨hs_dom, hs_tape⟩ :=
    hMs (binPred left) right suffix
      hpred_nd hpred_nsep hright_nd hright_nsep hsuffix_nd hsucc_nd hsucc_nsep
  have hs_from_cfg :
      (TM0Seq.evalFromCfg Ms
        ⟨default, ((TM0Seq.evalCfg Mp
          (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get hp_dom').Tape⟩).Dom := by
    rw [hp_tape']
    show (TM0Seq.evalFromCfg Ms
      (TM0.init (binPred left ++ chainConsBottom :: right ++ chainConsBottom :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hs_dom
  have hcomp_dom :
      (TM0Seq.evalCfg
        (@TM0Seq.compose ChainΓ Λp hΛpi Λs hΛsi Mp Ms)
        (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff
      (@TM0Seq.compose ChainΓ Λp hΛpi Λs hΛsi Mp Ms)
      (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).mpr
        (@TM0Seq.compose_dom_of_parts ChainΓ _ Λp hΛpi Λs hΛsi
          Mp Ms
          (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)
          hp_dom' hs_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    @TM0Seq.compose_evalCfg_tape ChainΓ _ Λp hΛpi Λs hΛsi Mp Ms
      (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)
      (binPred left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)
      hp_dom' hp_tape' hs_dom h
  rw [hcomp_tape, hs_tape hs_dom]
  unfold pairedDecrLeftIncrRightRaw
  rw [splitAtConsBottom_general left right hleft_nsep]
  simp [List.append_assoc]

theorem tm0_pairedDecrLeftIncrRightRaw_beforeSecondCond :
    TM0RealizesPairedBlockBeforeConsBottomCond
      pairedDecrLeftIncrRightRaw pairedAddCond := by
  obtain ⟨Λr, hΛri, hΛrf, Mr, hMr⟩ :=
    tm0_pairedDecrLeftIncrRightRaw_beforeSecond
  obtain ⟨Λp, hΛpi, hΛpf, Mp, q_le, q_gt, hne, hp⟩ :=
    tm0_blockValueLeq_decidable_2 0
  haveI : DecidableEq Λp := Classical.decEq Λp
  let hΛrFi : Inhabited (Λr ⊕ FinalizeSt) := ⟨Sum.inl (@default _ hΛri)⟩
  let MrF : TM0.Machine ChainΓ (Λr ⊕ FinalizeSt) :=
    @TM0Seq.compose ChainΓ Λr hΛri FinalizeSt inferInstance Mr finalizeMachine
  let Mcond : TM0.Machine ChainΓ (Λp ⊕ FinalizeSt ⊕ (Λr ⊕ FinalizeSt)) :=
    @tm0CondCompose Λp FinalizeSt (Λr ⊕ FinalizeSt)
      hΛpi inferInstance hΛrFi inferInstance
      Mp finalizeMachine MrF q_le q_gt
  refine ⟨Λp ⊕ FinalizeSt ⊕ (Λr ⊕ FinalizeSt), inferInstance, inferInstance,
    Mcond, Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)), ?_⟩
  intro left right suffix hleft_nd hleft_nsep hright_nd hright_nsep hsuffix_nd hstep_nd
  set pairBlock := left ++ [chainConsBottom] ++ right with hpair_def
  set whole := left ++ chainConsBottom :: right ++ chainConsBottom :: suffix with hwhole_def
  have hwhole_nd : ∀ g ∈ whole, g ≠ default := by
    intro g hg
    simp [whole, List.mem_append] at hg
    rcases hg with hg | rfl | hg | rfl | hg
    · exact hleft_nd g hg
    · exact chainConsBottom_ne_default
    · exact hright_nd g hg
    · exact chainConsBottom_ne_default
    · exact hsuffix_nd g hg
  have hp_spec := hp whole [] hwhole_nd (by simp)
  have hp_dom_with_default := hp_spec.1
  have hp_dom : (TM0Seq.evalCfg Mp whole).Dom := by
    rw [← evalCfg_append_default]
    simpa using hp_dom_with_default
  have hp_out_with_default := hp_spec.2 hp_dom_with_default
  set cp := (TM0Seq.evalCfg Mp whole).get hp_dom
  have hcp_get :
      cp =
        (TM0Seq.evalCfg Mp (whole ++ [default])).get hp_dom_with_default := by
    apply Part.get_eq_get_of_eq
    exact (evalCfg_append_default Mp whole).symm
  have hcp_tape : cp.Tape = Tape.mk₁ whole := by
    rw [hcp_get, hp_out_with_default.1]
    exact tape_mk₁_append_default whole
  have hcp_mem : cp ∈ TM0Seq.evalCfg Mp whole := Part.get_mem hp_dom
  have hcp_eval := Turing.mem_eval.mp hcp_mem
  have hcp_halt : TM0.step Mp cp = none := hcp_eval.2
  have hcp_reaches : Reaches (TM0.step Mp) (TM0.init whole) cp := hcp_eval.1
  have hphase1 := condCompose_phase1_reaches Mp finalizeMachine MrF q_le q_gt
    cp whole hcp_reaches
  change Reaches (TM0.step Mcond) (TM0.init whole)
    { q := Sum.inl cp.q, Tape := cp.Tape } at hphase1
  have heval_rewrite :
      TM0Seq.evalCfg Mcond whole =
        Turing.eval (TM0.step Mcond) ⟨Sum.inl cp.q, cp.Tape⟩ := by
    exact Turing.reaches_eval hphase1
  have hwhole_eq_pair_suffix :
      whole = pairBlock ++ chainConsBottom :: suffix := by
    simp [whole, pairBlock, List.append_assoc]
  have hcond_bridge :
      blockValueLeq 0 whole ↔ blockValueLeq 0 pairBlock := by
    rw [hwhole_eq_pair_suffix]
    simpa [pairBlock, List.append_assoc] using
      blockValueLeq_paired_prefix_append_secondSep 0 left right suffix
  by_cases hcond : pairedAddCond pairBlock
  · have hp_false : ¬ blockValueLeq 0 whole := by
      intro hle
      exact hcond ((hcond_bridge.mp hle))
    have hq : cp.q = q_gt := by
      have hout := hp_out_with_default.2.2 hp_false
      rw [← hcp_get] at hout
      exact hout
    have hhalt_q : TM0.step Mp ⟨q_gt, cp.Tape⟩ = none := hq ▸ hcp_halt
    have hraw_nd : ∀ g ∈ pairedDecrLeftIncrRightRaw pairBlock, g ≠ default :=
      hstep_nd hcond
    obtain ⟨hMr_dom, hMr_tape⟩ :=
      hMr left right suffix hleft_nd hleft_nsep hright_nd hright_nsep hsuffix_nd
        (by simpa [pairBlock] using hraw_nd)
    have hMr_dom' : (TM0Seq.evalCfg Mr whole).Dom := by
      simpa [whole] using hMr_dom
    have hMr_tape' :
        ∀ h, ((TM0Seq.evalCfg Mr whole).get h).Tape =
          Tape.mk₁ (pairedDecrLeftIncrRightRaw pairBlock ++ chainConsBottom :: suffix) := by
      intro h
      have hget :
          (TM0Seq.evalCfg Mr whole).get h =
            (TM0Seq.evalCfg Mr
              (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get hMr_dom := by
        apply Part.get_eq_get_of_eq
        simp [whole]
      rw [hget, hMr_tape hMr_dom]
    have hfinal := compose_finalize_evalCfg Mr whole
      (pairedDecrLeftIncrRightRaw pairBlock ++ chainConsBottom :: suffix)
      hMr_dom' (hMr_tape' hMr_dom')
    have hbranch_dom :
        (TM0Seq.evalFromCfg MrF ⟨default, cp.Tape⟩).Dom := by
      rw [hcp_tape]
      change (TM0Seq.evalFromCfg MrF (TM0.init whole)).Dom
      rw [TM0Seq.evalFromCfg_init]
      exact hfinal.1
    have hbranch_spec :
        ∀ h, (TM0Seq.evalFromCfg MrF ⟨default, cp.Tape⟩).get h =
          ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (pairedDecrLeftIncrRightRaw pairBlock ++
              chainConsBottom :: suffix)⟩ := by
      intro h
      have heq :
          TM0Seq.evalFromCfg MrF ⟨default, cp.Tape⟩ =
            TM0Seq.evalCfg MrF whole := by
        rw [hcp_tape]
        exact TM0Seq.evalFromCfg_init (M := MrF) (l := whole)
      have hget :
          (TM0Seq.evalFromCfg MrF ⟨default, cp.Tape⟩).get h =
            (TM0Seq.evalCfg MrF whole).get hfinal.1 := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hfinal.2 hfinal.1
    have hbranch_step :
        ∃ c₂, TM0.step MrF ⟨default, cp.Tape⟩ = some c₂ := by
      rw [hcp_tape]
      change ∃ c₂, TM0.step MrF (TM0.init whole) = some c₂
      change ∃ c₂, TM0.step MrF ⟨default, Tape.mk₁ whole⟩ = some c₂
      rcases hfirst : TM0.step Mr ⟨default, Tape.mk₁ whole⟩ with _ | c₂
      · refine ⟨(⟨Sum.inr FinalizeSt.done, Tape.mk₁ whole⟩ :
            TM0.Cfg ChainΓ (Λr ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λr hΛri FinalizeSt inferInstance
          Mr finalizeMachine) ⟨Sum.inl default, Tape.mk₁ whole⟩ =
          some ⟨Sum.inr FinalizeSt.done, Tape.mk₁ whole⟩
        rw [TM0Seq.compose_step_on_halt Mr finalizeMachine default
          (Tape.mk₁ whole) hfirst]
        change Option.map
          (fun c₂ : TM0.Cfg ChainΓ FinalizeSt =>
            ({ q := Sum.inr c₂.q, Tape := c₂.Tape } :
              TM0.Cfg ChainΓ (Λr ⊕ FinalizeSt)))
          (TM0.step finalizeMachine ⟨FinalizeSt.start, Tape.mk₁ whole⟩) =
          some ⟨Sum.inr FinalizeSt.done, Tape.mk₁ whole⟩
        rw [finalize_step_start]
        rfl
      · refine ⟨(⟨Sum.inl c₂.q, c₂.Tape⟩ :
            TM0.Cfg ChainΓ (Λr ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λr hΛri FinalizeSt inferInstance
          Mr finalizeMachine) ⟨Sum.inl default, Tape.mk₁ whole⟩ =
          some ⟨Sum.inl c₂.q, c₂.Tape⟩
        simpa using TM0Seq.compose_step_inl Mr finalizeMachine
          (⟨default, Tape.mk₁ whole⟩ : TM0.Cfg ChainΓ Λr) c₂ hfirst
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MrF q_le q_gt))
        ⟨Sum.inl q_gt, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_false Mp finalizeMachine MrF q_le q_gt hne
        cp.Tape hhalt_q).mpr hbranch_dom
    have hdom : (TM0Seq.evalCfg Mcond whole).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_false_of_step_local
      Mp finalizeMachine MrF q_le q_gt hne (Sum.inr FinalizeSt.done) cp.Tape
      (Tape.mk₁ (pairedDecrLeftIncrRightRaw pairBlock ++ chainConsBottom :: suffix))
      hhalt_q hbranch_step hbranch_dom hbranch_spec
    have hcfg' : (TM0Seq.evalCfg Mcond whole).get h =
        ⟨Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)),
          Tape.mk₁ (pairedDecrLeftIncrRightRaw pairBlock ++ chainConsBottom :: suffix)⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond whole =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond whole).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    have hle_false : ¬ blockValueLeq 0 (left ++ chainConsBottom :: right) := by
      simpa [pairedAddCond, pairBlock] using hcond
    have hle_pair_false : ¬ blockValueLeq 0 pairBlock := by
      simpa [pairedAddCond] using hcond
    simp [hle_pair_false]
    constructor
    · simpa [hwhole_def] using congrArg TM0.Cfg.q hcfg'
    · simpa [hwhole_def, hpair_def] using congrArg TM0.Cfg.Tape hcfg'
  · have hp_true : blockValueLeq 0 whole := by
      exact hcond_bridge.mpr (by simpa [pairedAddCond] using hcond)
    have hq : cp.q = q_le := by
      have hout := hp_out_with_default.2.1 hp_true
      rw [← hcp_get] at hout
      exact hout
    have hhalt_q : TM0.step Mp ⟨q_le, cp.Tape⟩ = none := hq ▸ hcp_halt
    obtain ⟨hid_dom, hid_spec⟩ := finalize_evalFromCfg cp.Tape
    have hid_step : ∃ c₂, TM0.step finalizeMachine ⟨default, cp.Tape⟩ = some c₂ := by
      exact ⟨⟨FinalizeSt.done, cp.Tape⟩, finalize_step_start cp.Tape⟩
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MrF q_le q_gt))
        ⟨Sum.inl q_le, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_true Mp finalizeMachine MrF q_le q_gt
        cp.Tape hhalt_q).mpr hid_dom
    have hdom : (TM0Seq.evalCfg Mcond whole).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_true_of_step_local
      Mp finalizeMachine MrF q_le q_gt FinalizeSt.done cp.Tape cp.Tape
      hhalt_q hid_step hid_dom (fun h => hid_spec h)
    have hcfg' : (TM0Seq.evalCfg Mcond whole).get h =
        ⟨Sum.inr (Sum.inl FinalizeSt.done), cp.Tape⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond whole =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond whole).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    have hq_ne :
        Sum.inr (Sum.inl FinalizeSt.done) ≠
          (Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)) :
            Λp ⊕ FinalizeSt ⊕ (Λr ⊕ FinalizeSt)) := by
      simp
    have hle_pair : blockValueLeq 0 pairBlock := by
      simpa [pairedAddCond] using hcond
    have hle_true : blockValueLeq 0 (left ++ chainConsBottom :: right) := by
      simpa [pairBlock] using hle_pair
    simp [hle_pair]
    constructor
    · have hq_out : ((TM0Seq.evalCfg Mcond whole).get h).q ≠
          (Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)) :
            Λp ⊕ FinalizeSt ⊕ (Λr ⊕ FinalizeSt)) := by
        rw [hcfg']
        exact hq_ne
      simpa [hwhole_def] using hq_out
    · have htape_out : ((TM0Seq.evalCfg Mcond whole).get h).Tape =
          Tape.mk₁ whole := by
        rw [hcfg', hcp_tape]
      simpa [hwhole_def] using htape_out

theorem tm0RealizesPairedBlockBeforeConsBottom_while_pairedSepInv
    (step result : List ChainΓ → List ChainΓ) (cond : List ChainΓ → Prop)
    [DecidablePred cond]
    (hbody : TM0RealizesPairedBlockBeforeConsBottomCond step cond)
    (hinv_step : ∀ block, pairedSepInv block → (∀ g ∈ block, g ≠ default) →
      cond block → pairedSepInv (step block))
    (hstep_nd : ∀ block, (∀ g ∈ block, g ≠ default) → cond block →
      ∀ g ∈ step block, g ≠ default)
    (hresult_eq : ∀ block, (∀ g ∈ block, g ≠ default) → pairedSepInv block →
      ∃ n, result block = blockIterateWhile step cond n block ∧
        ¬cond (blockIterateWhile step cond n block)) :
    TM0RealizesPairedBlockBeforeConsBottom result := by
  obtain ⟨Λ, hΛi, hΛf, M, q_cont, hM⟩ := hbody
  haveI : DecidableEq Λ := Classical.decEq Λ
  refine ⟨Λ, hΛi, hΛf, tm0WhileLoop M q_cont, ?_⟩
  intro left right suffix hleft_nd hleft_nsep hright_nd hright_nsep hsuffix_nd hresult
  set block := left ++ [chainConsBottom] ++ right with hblock_def
  have hblock_nd : ∀ g ∈ block, g ≠ default := by
    intro g hg
    simp [block, List.mem_append] at hg
    rcases hg with hg | rfl | hg
    · exact hleft_nd g hg
    · exact chainConsBottom_ne_default
    · exact hright_nd g hg
  have hblockInv : pairedSepInv block := by
    constructor
    · unfold hasConsBottom
      simp [block]
    · rw [show splitAtConsBottom block = (left, right) by
        simpa [block] using splitAtConsBottom_general left right hleft_nsep]
      exact hright_nsep
  obtain ⟨n, hn_eq, hn_not_cond⟩ := hresult_eq block hblock_nd hblockInv
  suffices key : ∀ (m : ℕ) (blk : List ChainΓ),
      pairedSepInv blk →
      (∀ g ∈ blk, g ≠ default) →
      ¬cond (blockIterateWhile step cond m blk) →
      (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
        (blk ++ chainConsBottom :: suffix)).Dom ∧
      ∀ (hd : (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
        (blk ++ chainConsBottom :: suffix)).Dom),
        ((TM0Seq.evalCfg (tm0WhileLoop M q_cont)
          (blk ++ chainConsBottom :: suffix)).get hd).Tape =
          Tape.mk₁ (blockIterateWhile step cond m blk ++
            chainConsBottom :: suffix) by
    obtain ⟨h_dom, h_tape⟩ := key n block hblockInv hblock_nd hn_not_cond
    have hinput : block ++ chainConsBottom :: suffix =
        left ++ chainConsBottom :: right ++ chainConsBottom :: suffix := by
      simp [block, List.append_assoc]
    refine ⟨by simpa [hinput] using h_dom, ?_⟩
    intro hd
    have hget :
        (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
          (left ++ chainConsBottom :: right ++ chainConsBottom :: suffix)).get hd =
        (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
          (block ++ chainConsBottom :: suffix)).get h_dom := by
      apply Part.get_eq_get_of_eq
      simp [hinput]
    rw [hget, h_tape h_dom, hn_eq]
  intro m
  induction m with
  | zero =>
    intro blk hInv hblk hn_not
    simp only [blockIterateWhile] at hn_not ⊢
    rcases hsplit : splitAtConsBottom blk with ⟨l, r⟩
    have hblk_recon : blk = l ++ chainConsBottom :: r := by
      simpa [hsplit] using paired_splitAtConsBottom_reconstruct_of_mem blk hInv.1
    have hl_nd : ∀ g ∈ l, g ≠ default := by
      intro g hg
      exact hblk g (splitAtConsBottom_fst_subset blk g (by simpa [hsplit] using hg))
    have hr_nd : ∀ g ∈ r, g ≠ default := by
      intro g hg
      exact hblk g (splitAtConsBottom_snd_subset blk g (by simpa [hsplit] using hg))
    have hl_nsep : ∀ g ∈ l, g ≠ chainConsBottom := by
      simpa [hsplit] using splitAtConsBottom_fst_no_sep blk
    have hr_nsep : ∀ g ∈ r, g ≠ chainConsBottom := by
      simpa [pairedSepInv, hsplit] using hInv.2
    obtain ⟨h_body_dom, h_body_spec⟩ := hM l r suffix
      hl_nd hl_nsep hr_nd hr_nsep hsuffix_nd
      (fun hc => by
        simpa [hblk_recon] using hstep_nd blk hblk
          (by simpa [hblk_recon] using hc))
    have h_body_dom' :
        (TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).Dom := by
      simpa [hblk_recon, List.append_assoc] using h_body_dom
    have h_body_spec' := h_body_spec h_body_dom
    have hcond_lr : ¬ cond (l ++ chainConsBottom :: r) := by
      simpa [hblk_recon] using hn_not
    by_cases hc_lr : cond (l ++ chainConsBottom :: r)
    · exact False.elim (hcond_lr hc_lr)
    ·
      simp [hc_lr] at h_body_spec'
      obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
      have hget_body :
          (TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).get h_body_dom' =
          (TM0Seq.evalCfg M
            (l ++ chainConsBottom :: r ++ chainConsBottom :: suffix)).get h_body_dom := by
        apply Part.get_eq_get_of_eq
        simp [hblk_recon, List.append_assoc]
      have h_q_ne' :
          ((TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).get
            h_body_dom').q ≠ q_cont := by
        rw [hget_body]
        simpa [List.append_assoc] using h_q_ne
      obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _
        h_body_dom' h_q_ne'
      exact ⟨h_dom, fun hd => by
        rw [h_tape hd]
        simpa [hblk_recon, List.append_assoc] using h_tape_eq⟩
  | succ m ih =>
    intro blk hInv hblk hn_not
    by_cases hcond : cond blk
    · rw [blockIterateWhile_succ_true _ _ _ _ hcond] at hn_not ⊢
      have h_step_nd := hstep_nd blk hblk hcond
      have h_step_inv := hinv_step blk hInv hblk hcond
      rcases hsplit : splitAtConsBottom blk with ⟨l, r⟩
      have hblk_recon : blk = l ++ chainConsBottom :: r := by
        simpa [hsplit] using paired_splitAtConsBottom_reconstruct_of_mem blk hInv.1
      have hl_nd : ∀ g ∈ l, g ≠ default := by
        intro g hg
        exact hblk g (splitAtConsBottom_fst_subset blk g (by simpa [hsplit] using hg))
      have hr_nd : ∀ g ∈ r, g ≠ default := by
        intro g hg
        exact hblk g (splitAtConsBottom_snd_subset blk g (by simpa [hsplit] using hg))
      have hl_nsep : ∀ g ∈ l, g ≠ chainConsBottom := by
        simpa [hsplit] using splitAtConsBottom_fst_no_sep blk
      have hr_nsep : ∀ g ∈ r, g ≠ chainConsBottom := by
        simpa [pairedSepInv, hsplit] using hInv.2
      obtain ⟨h_body_dom, h_body_spec⟩ := hM l r suffix
        hl_nd hl_nsep hr_nd hr_nsep hsuffix_nd
        (fun _ => by simpa [hblk_recon] using h_step_nd)
      have h_body_dom' :
          (TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).Dom := by
        simpa [hblk_recon, List.append_assoc] using h_body_dom
      have h_body_spec' := h_body_spec h_body_dom
      have hcond_lr : cond (l ++ chainConsBottom :: r) := by
        simpa [hblk_recon] using hcond
      by_cases hc_lr : cond (l ++ chainConsBottom :: r)
      ·
        simp [hc_lr] at h_body_spec'
        obtain ⟨h_q_cont, h_tape_step⟩ := h_body_spec'
        have hget_body :
            (TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).get h_body_dom' =
            (TM0Seq.evalCfg M
              (l ++ chainConsBottom :: r ++ chainConsBottom :: suffix)).get h_body_dom := by
          apply Part.get_eq_get_of_eq
          simp [hblk_recon, List.append_assoc]
        have h_q_cont' :
            ((TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).get
              h_body_dom').q = q_cont := by
          rw [hget_body]
          simpa [List.append_assoc] using h_q_cont
        obtain ⟨h_W_step_dom, h_W_step_tape⟩ :=
          ih (step blk) h_step_inv h_step_nd hn_not
        obtain ⟨h_W_dom, h_W_tape⟩ := whileLoop_eval_cont M q_cont _ _
          h_body_dom' h_q_cont'
          (by simpa [hblk_recon, List.append_assoc] using h_tape_step)
          h_W_step_dom
        exact ⟨h_W_dom, fun hd => by
          rw [h_W_tape hd, h_W_step_tape h_W_step_dom]⟩
      · exact False.elim (hc_lr hcond_lr)
    · rw [blockIterateWhile_succ_false _ _ _ _ hcond] at hn_not ⊢
      rcases hsplit : splitAtConsBottom blk with ⟨l, r⟩
      have hblk_recon : blk = l ++ chainConsBottom :: r := by
        simpa [hsplit] using paired_splitAtConsBottom_reconstruct_of_mem blk hInv.1
      have hl_nd : ∀ g ∈ l, g ≠ default := by
        intro g hg
        exact hblk g (splitAtConsBottom_fst_subset blk g (by simpa [hsplit] using hg))
      have hr_nd : ∀ g ∈ r, g ≠ default := by
        intro g hg
        exact hblk g (splitAtConsBottom_snd_subset blk g (by simpa [hsplit] using hg))
      have hl_nsep : ∀ g ∈ l, g ≠ chainConsBottom := by
        simpa [hsplit] using splitAtConsBottom_fst_no_sep blk
      have hr_nsep : ∀ g ∈ r, g ≠ chainConsBottom := by
        simpa [pairedSepInv, hsplit] using hInv.2
      obtain ⟨h_body_dom, h_body_spec⟩ := hM l r suffix
        hl_nd hl_nsep hr_nd hr_nsep hsuffix_nd
        (fun hc => False.elim (hcond (by simpa [hblk_recon] using hc)))
      have h_body_dom' :
          (TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).Dom := by
        simpa [hblk_recon, List.append_assoc] using h_body_dom
      have h_body_spec' := h_body_spec h_body_dom
      have hcond_lr : ¬ cond (l ++ chainConsBottom :: r) := by
        simpa [hblk_recon] using hcond
      by_cases hc_lr : cond (l ++ chainConsBottom :: r)
      · exact False.elim (hcond_lr hc_lr)
      ·
        simp [hc_lr] at h_body_spec'
        obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
        have hget_body :
            (TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).get h_body_dom' =
            (TM0Seq.evalCfg M
              (l ++ chainConsBottom :: r ++ chainConsBottom :: suffix)).get h_body_dom := by
          apply Part.get_eq_get_of_eq
          simp [hblk_recon, List.append_assoc]
        have h_q_ne' :
            ((TM0Seq.evalCfg M (blk ++ chainConsBottom :: suffix)).get
              h_body_dom').q ≠ q_cont := by
          rw [hget_body]
          simpa [List.append_assoc] using h_q_ne
        obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _
          h_body_dom' h_q_ne'
        exact ⟨h_dom, fun hd => by
          rw [h_tape hd]
          simpa [hblk_recon, List.append_assoc] using h_tape_eq⟩


theorem binMulPairedStep_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) (_hcond : binMulPairedCond block) :
    ∀ g ∈ binMulPairedStep block, g ≠ default := by
  rcases hsplit : splitAtConsBottom block with ⟨acc, rest⟩
  rcases hrest : splitAtConsBottom rest with ⟨addend, fuel⟩
  have hacc : ∀ g ∈ acc, g ≠ default := by
    intro g hg
    exact hblock g (splitAtConsBottom_fst_subset block g (by simpa [hsplit] using hg))
  have hrest_block : ∀ g ∈ rest, g ≠ default := by
    intro g hg
    exact hblock g (splitAtConsBottom_snd_subset block g (by simpa [hsplit] using hg))
  have haddend : ∀ g ∈ addend, g ≠ default := by
    intro g hg
    exact hrest_block g (splitAtConsBottom_fst_subset rest g (by simpa [hrest] using hg))
  have hfuel : ∀ g ∈ fuel, g ≠ default := by
    intro g hg
    exact hrest_block g (splitAtConsBottom_snd_subset rest g (by simpa [hrest] using hg))
  have haddInput : ∀ g ∈ acc ++ chainConsBottom :: addend, g ≠ default := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hacc g hg
    · cases hg with
      | head => exact chainConsBottom_ne_default
      | tail _ hg => exact haddend g hg
  unfold binMulPairedStep
  simp [hsplit, hrest]
  rintro g (hg | rfl | hg | rfl | hg)
  · exact binAddPaired_ne_default _ haddInput g hg
  · exact chainConsBottom_ne_default
  · exact haddend g hg
  · exact chainConsBottom_ne_default
  · exact binPred_ne_default _ hfuel g hg

theorem binMulPairedStep_stateInv (block : List ChainΓ)
    (_hInv : binMulPairedStateInv block) :
    binMulPairedStateInv (binMulPairedStep block) := by
  unfold binMulPairedStateInv binMulPairedStep hasConsBottom
  rcases splitAtConsBottom block with ⟨acc, rest⟩
  rcases hrest : splitAtConsBottom rest with ⟨addend, fuel⟩
  simp [hrest, binAddPaired, List.append_assoc]
  rw [show splitAtConsBottom (addend ++ chainConsBottom :: binPred fuel) =
      (addend, binPred fuel) by
    simpa using splitAtConsBottom_general addend (binPred fuel)
      (by simpa [hrest] using splitAtConsBottom_fst_no_sep rest)]
  exact binPred_no_consBottom fuel

/-- The loop over an already-initialized multiplication state. -/
noncomputable def binMulPairedLoop (block : List ChainΓ) : List ChainΓ :=
  blockIterateWhile binMulPairedStep binMulPairedCond
    (decodeBinaryBlock (binMulPairedFuel block)) block

theorem binMulPairedLoop_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulPairedLoop block, g ≠ default := by
  unfold binMulPairedLoop
  induction' decodeBinaryBlock (binMulPairedFuel block) with n ih generalizing block
  · exact hblock
  · by_cases hcond : binMulPairedCond block
    · simp [blockIterateWhile, hcond]
      exact ih _ (binMulPairedStep_ne_default _ hblock hcond)
    · simp [blockIterateWhile, hcond]
      exact hblock

theorem binMulPairedLoop_stateInv (block : List ChainΓ)
    (hInv : binMulPairedStateInv block) :
    binMulPairedStateInv (binMulPairedLoop block) := by
  unfold binMulPairedLoop
  induction' decodeBinaryBlock (binMulPairedFuel block) with n ih generalizing block
  · exact hInv
  · by_cases hcond : binMulPairedCond block
    · simp [blockIterateWhile, hcond]
      exact ih _ (binMulPairedStep_stateInv block hInv)
    · simp [blockIterateWhile, hcond]
      exact hInv

@[simp]
theorem decodeBinaryBlock_binMulPairedInit_fuel (block : List ChainΓ) :
    decodeBinaryBlock (binMulPairedFuel (binMulPairedInit block)) =
      decodeBinaryBlock (splitAtConsBottom block).2 := by
  unfold binMulPairedFuel binMulPairedInit normalizePairedBlocks pairNormalizedBlocks
  rw [splitAtConsBottom_binary_sep]
  rw [splitAtConsBottom_binary_sep]
  rw [decodeBinaryBlock_chainBinaryRepr]

theorem binMulPairedWhile_eq_loop :
    binMulPairedWhile = binMulPairedLoop ∘ binMulPairedInit := by
  funext block
  unfold binMulPairedWhile binMulPairedLoop
  simp

theorem binMulPairedWhile_stateInv (block : List ChainΓ) :
    binMulPairedStateInv (binMulPairedWhile block) := by
  rw [binMulPairedWhile_eq_loop]
  exact binMulPairedLoop_stateInv _ (binMulPairedInit_stateInv block)

theorem binMulPairedWhile_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulPairedWhile block, g ≠ default := by
  rw [binMulPairedWhile_eq_loop]
  exact binMulPairedLoop_ne_default _ (binMulPairedInit_ne_default _ hblock)

theorem binMulPairedResult_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulPairedResult block, g ≠ default := by
  intro g hg
  exact hblock g (splitAtConsBottom_fst_subset _ g (by
    unfold binMulPairedResult at hg
    exact hg))

/-- **dropFromLastSep is block-realizable** when `sep ≠ default`. -/
theorem tm0_dropFromLastSep_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlock Γ (dropFromLastSep sep) :=
  tm0_dropFromLastSep_block_v2 sep hsep

/-- `extractPairedLeft = reverse ∘ dropFromLastSep chainConsBottom ∘ reverse`. -/
theorem extractPairedLeft_eq_rev_drop_rev :
    extractPairedLeft = List.reverse ∘ dropFromLastSep chainConsBottom ∘ @List.reverse ChainΓ := by
  funext block
  induction' block with c rest ih
  · rfl
  · by_cases hc : c = chainConsBottom <;> simp_all +decide [Function.comp]
    · have h_extract : extractPairedLeft (chainConsBottom :: rest) = [] := by
        unfold extractPairedLeft splitAtConsBottom; aesop
      induction' rest.reverse with c rest ih <;> simp_all +decide [dropFromLastSep]
    · rw [show extractPairedLeft (c :: rest) = c :: extractPairedLeft rest from ?_]
      · rw [show dropFromLastSep chainConsBottom (rest.reverse ++ [c]) = dropFromLastSep chainConsBottom rest.reverse ++ [c] from ?_]; aesop
        have h_app : ∀ (l : List ChainΓ) (c : ChainΓ), c ≠ chainConsBottom → dropFromLastSep chainConsBottom (l ++ [c]) = dropFromLastSep chainConsBottom l ++ [c] := by
          intros l c hc; induction' l with y l ih generalizing c <;> simp_all +decide [ dropFromLastSep ] ;
          split_ifs <;> simp_all +decide;
        exact h_app _ _ hc
      · unfold extractPairedLeft splitAtConsBottom; aesop

/-
**Extracting the left sub-block is block-realizable.**
    Decomposed as `reverse ∘ dropFromLastSep chainConsBottom ∘ reverse`.
-/
theorem tm0_extractPairedLeft_block :
    TM0RealizesBlock ChainΓ extractPairedLeft := by
  rw [extractPairedLeft_eq_rev_drop_rev];
  grind +suggestions

@[simp]
theorem binMulPairedFuel_normalized_state (acc addend fuel : ℕ) :
    binMulPairedFuel
      (chainBinaryRepr acc ++ [chainConsBottom] ++ chainBinaryRepr addend ++
        [chainConsBottom] ++ chainBinaryRepr fuel) =
    chainBinaryRepr fuel := by
  simp [binMulPairedFuel, List.append_assoc]

theorem binMulPairedStep_normalized_state (acc addend fuel : ℕ) :
    binMulPairedStep
      (chainBinaryRepr acc ++ [chainConsBottom] ++ chainBinaryRepr addend ++
        [chainConsBottom] ++ chainBinaryRepr fuel) =
    chainBinaryRepr (acc + addend) ++ [chainConsBottom] ++ chainBinaryRepr addend ++
      [chainConsBottom] ++ chainBinaryRepr (fuel - 1) := by
  simp [binMulPairedStep, binAddPaired, binPred, List.append_assoc]

@[simp]
theorem binMulPairedLoop_normalized_state (acc addend fuel : ℕ) :
    blockIterateWhile binMulPairedStep binMulPairedCond fuel
      (chainBinaryRepr acc ++ [chainConsBottom] ++ chainBinaryRepr addend ++
        [chainConsBottom] ++ chainBinaryRepr fuel) =
    chainBinaryRepr (acc + fuel * addend) ++ [chainConsBottom] ++
      chainBinaryRepr addend ++ [chainConsBottom] ++ chainBinaryRepr 0 := by
  induction' fuel with fuel ih generalizing acc
  · simp [blockIterateWhile]
  · rw [blockIterateWhile_succ_true]
    · rw [binMulPairedStep_normalized_state]
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (acc + addend)
    · unfold binMulPairedCond blockValueLeq
      rw [binMulPairedFuel_normalized_state]
      simp [decodeBinaryBlock_chainBinaryRepr]

@[simp]
theorem binMulPairedLoop_normalized_state_cons (acc addend fuel : ℕ) :
    blockIterateWhile binMulPairedStep binMulPairedCond fuel
      (chainBinaryRepr acc ++ chainConsBottom ::
        (chainBinaryRepr addend ++ chainConsBottom :: chainBinaryRepr fuel)) =
    chainBinaryRepr (acc + fuel * addend) ++ [chainConsBottom] ++
      chainBinaryRepr addend ++ [chainConsBottom] ++ chainBinaryRepr 0 := by
  simpa [List.append_assoc] using
    binMulPairedLoop_normalized_state acc addend fuel

theorem binMulPaired_eq_repeated_add :
    binMulPaired = binMulPairedResult ∘ binMulPairedWhile := by
  funext block
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  simp [binMulPaired, binMulPairedWhile, binMulPairedInit, normalizePairedBlocks,
    pairNormalizedBlocks, binMulPairedResult, Function.comp, hsplit,
    Nat.mul_comm, List.append_assoc]

/-- `decodeBinaryBlock (binPred block) = decodeBinaryBlock block - 1` -/
theorem decodeBinaryBlock_binPred (block : List ChainΓ) :
    decodeBinaryBlock (binPred block) = decodeBinaryBlock block - 1 := by
  simp [binPred, decodeBinaryBlock_chainBinaryRepr]
/-
The fuel field of `binMulPairedStep block` is `binPred` of the fuel field of `block`.
-/
theorem binMulPairedFuel_step (block : List ChainΓ) :
    binMulPairedFuel (binMulPairedStep block) = binPred (binMulPairedFuel block) := by
  unfold binMulPairedFuel binMulPairedStep;
  have h_split : ∀ (acc addend fuel : List ChainΓ), (∀ c ∈ acc, c ≠ chainConsBottom) → (∀ c ∈ addend, c ≠ chainConsBottom) → splitAtConsBottom (acc ++ [chainConsBottom] ++ addend ++ [chainConsBottom] ++ binPred fuel) = (acc, addend ++ [chainConsBottom] ++ binPred fuel) := by
    intros acc addend fuel hacc haddend
    have h_split : splitAtConsBottom (acc ++ [chainConsBottom] ++ addend ++ [chainConsBottom] ++ binPred fuel) = (acc, addend ++ [chainConsBottom] ++ binPred fuel) := by
      have h_split_acc : splitAtConsBottom (acc ++ [chainConsBottom] ++ addend ++ [chainConsBottom] ++ binPred fuel) = (acc, addend ++ [chainConsBottom] ++ binPred fuel) := by
        have h_split_acc : splitAtConsBottom (acc ++ [chainConsBottom] ++ addend ++ [chainConsBottom] ++ binPred fuel) = splitAtConsBottom (acc ++ [chainConsBottom] ++ (addend ++ [chainConsBottom] ++ binPred fuel)) := by
          simp +decide [ List.append_assoc ]
        convert splitAtConsBottom_general acc ( addend ++ [ chainConsBottom ] ++ binPred fuel ) hacc using 1
      exact h_split_acc;
    exact h_split;
  unfold binAddPaired; simp +decide [ h_split ] ;
  have := splitAtConsBottom_general ( ( splitAtConsBottom ( splitAtConsBottom block ).2 ).1 ) ( binPred ( splitAtConsBottom ( splitAtConsBottom block ).2 ).2 ) ( splitAtConsBottom_fst_no_sep _ ) ; aesop;
/-
After iterating `binMulPairedStep` with `blockIterateWhile` for `n` steps
    starting from `block`, the condition is false at the result,
    provided `n ≥ decodeBinaryBlock (binMulPairedFuel block)`.
-/
theorem binMulPairedCond_false_after_iterate (n : ℕ) (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hn : decodeBinaryBlock (binMulPairedFuel block) ≤ n) :
    ¬ binMulPairedCond
      (blockIterateWhile binMulPairedStep binMulPairedCond n block) := by
  induction' n with n ih generalizing block;
  · exact?;
  · by_cases h : binMulPairedCond block <;> simp +decide [ h, blockIterateWhile ];
    convert ih ( binMulPairedStep block ) ( binMulPairedStep_ne_default block hblock h ) _ using 1;
    · grind +qlia;
    · rw [ binMulPairedFuel_step ];
      rw [ decodeBinaryBlock_binPred ] ; omega

theorem binMulPairedWhile_eq_iterate (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∃ n, binMulPairedLoop block =
        blockIterateWhile binMulPairedStep binMulPairedCond n block ∧
      ¬ binMulPairedCond
        (blockIterateWhile binMulPairedStep binMulPairedCond n block) := by
  refine ⟨decodeBinaryBlock (binMulPairedFuel block), rfl, ?_⟩
  exact binMulPairedCond_false_after_iterate _ _ _hblock le_rfl

/-! #### Three-separator multiplication loop -/

/-- The loop over an already-initialized three-separator multiplication state. -/
noncomputable def binMulPairedLoop3 (block : List ChainΓ) : List ChainΓ :=
  blockIterateWhile binMulPairedStep3 binMulPairedCond3
    (decodeBinaryBlock (binMulPairedFuel3 block)) block

theorem binMulPairedFuel3_step (block : List ChainΓ)
    (hInv : binMulPairedStateInv3 block) :
    binMulPairedFuel3 (binMulPairedStep3 block) =
      binPred (binMulPairedFuel3 block) := by
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have haddend_no_sep₂ : ∀ g ∈ addend, g ≠ binMulStateSep₂ := by
    simpa [hsplit, hrest] using binMulPairedStateInv3_addend_no_sep₂ block hInv
  have hacc_no_sep₁ : ∀ g ∈ acc, g ≠ binMulStateSep₁ := by
    simpa [hsplit] using splitAtSep_fst_no_sep binMulStateSep₁ block
  have hkeep :
      binAddPairedKeepRightSep binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend) =
        binAddPairedSep binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend) ++
          binMulStateSep₁ :: addend := by
    exact binAddPairedKeepRightSep_eq_cons binMulStateSep₁ acc addend
      hacc_no_sep₁
  have hsplit_step :
      splitAtSep binMulStateSep₁
        (binAddPairedKeepRightSep binMulStateSep₁
            (acc ++ binMulStateSep₁ :: addend) ++
          binMulStateSep₂ :: binPred fuel) =
        (binAddPairedSep binMulStateSep₁
            (acc ++ binMulStateSep₁ :: addend),
          addend ++ binMulStateSep₂ :: binPred fuel) := by
    rw [hkeep]
    simpa [List.append_assoc] using splitAtSep_general_cons binMulStateSep₁
      (binAddPairedSep binMulStateSep₁
        (acc ++ binMulStateSep₁ :: addend))
      (addend ++ binMulStateSep₂ :: binPred fuel)
      (binAddPairedSep_no_mulSep₁ binMulStateSep₁
        (acc ++ binMulStateSep₁ :: addend))
  have hrest_step :
      splitAtSep binMulStateSep₂
        (addend ++ binMulStateSep₂ :: binPred fuel) =
        (addend, binPred fuel) := by
    exact splitAtSep_general_cons binMulStateSep₂ addend (binPred fuel)
      haddend_no_sep₂
  unfold binMulPairedFuel3 binMulPairedStep3
  simp only [hsplit, hrest]
  rw [show
      binAddPairedKeepRightSep binMulStateSep₁
          (acc ++ [binMulStateSep₁] ++ addend) ++
          [binMulStateSep₂] ++ binPred fuel =
        binAddPairedKeepRightSep binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend) ++
          binMulStateSep₂ :: binPred fuel by
    simp [List.append_assoc]]
  rw [hsplit_step, hrest_step]

theorem binMulPairedLoop3_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulPairedLoop3 block, g ≠ default := by
  unfold binMulPairedLoop3
  induction' decodeBinaryBlock (binMulPairedFuel3 block) with n ih generalizing block
  · exact hblock
  · by_cases hcond : binMulPairedCond3 block
    · simp [blockIterateWhile, hcond]
      exact ih _ (binMulPairedStep3_ne_default _ hblock hcond)
    · simp [blockIterateWhile, hcond]
      exact hblock

theorem binMulPairedLoop3_stateInv (block : List ChainΓ)
    (hInv : binMulPairedStateInv3 block) :
    binMulPairedStateInv3 (binMulPairedLoop3 block) := by
  unfold binMulPairedLoop3
  induction' decodeBinaryBlock (binMulPairedFuel3 block) with n ih generalizing block
  · exact hInv
  · by_cases hcond : binMulPairedCond3 block
    · simp [blockIterateWhile, hcond]
      exact ih _ (binMulPairedStep3_stateInv block hInv)
    · simp [blockIterateWhile, hcond]
      exact hInv

theorem binMulPairedCond3_false_after_iterate (n : ℕ) (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hInv : binMulPairedStateInv3 block)
    (hn : decodeBinaryBlock (binMulPairedFuel3 block) ≤ n) :
    ¬ binMulPairedCond3
      (blockIterateWhile binMulPairedStep3 binMulPairedCond3 n block) := by
  induction' n with n ih generalizing block
  · simp only [blockIterateWhile]
    unfold binMulPairedCond3 blockValueLeq at *
    exact not_not_intro (by omega)
  · by_cases hcond : binMulPairedCond3 block
    · simp [blockIterateWhile, hcond]
      have hnot := ih (binMulPairedStep3 block)
          (binMulPairedStep3_ne_default block hblock hcond)
          (binMulPairedStep3_stateInv block hInv)
          (by
            rw [binMulPairedFuel3_step block hInv, decodeBinaryBlock_binPred]
            omega)
      simpa [binMulPairedCond3] using hnot
    · simp [blockIterateWhile, hcond]

theorem binMulPairedLoop3_eq_iterate (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hInv : binMulPairedStateInv3 block) :
    ∃ n, binMulPairedLoop3 block =
        blockIterateWhile binMulPairedStep3 binMulPairedCond3 n block ∧
      ¬ binMulPairedCond3
        (blockIterateWhile binMulPairedStep3 binMulPairedCond3 n block) := by
  refine ⟨decodeBinaryBlock (binMulPairedFuel3 block), rfl, ?_⟩
  exact binMulPairedCond3_false_after_iterate _ _ hblock hInv le_rfl

theorem tm0_binMulPairedLoop3_blockInvSuffix
    (hstep : TM0RealizesBlockCondInvSuffix binMulPairedStep3 binMulPairedCond3
      binMulPairedStateInv3) :
    TM0RealizesBlockInvSuffix binMulPairedLoop3 binMulPairedStateInv3 := by
  exact tm0RealizesBlockInvSuffix_while
    binMulPairedStep3
    binMulPairedLoop3
    binMulPairedCond3
    binMulPairedStateInv3
    hstep
    (fun block hInv _hblock _hcond => binMulPairedStep3_stateInv block hInv)
    binMulPairedStep3_ne_default
    (fun block hblock hInv => binMulPairedLoop3_eq_iterate block hblock hInv)
    (fun block hblock _hInv => binMulPairedLoop3_ne_default block hblock)

@[simp]
theorem binMulPairedLoop3_normalized_state (acc addend fuel : ℕ) :
    blockIterateWhile binMulPairedStep3 binMulPairedCond3 fuel
      (chainBinaryRepr acc ++ [binMulStateSep₁] ++ chainBinaryRepr addend ++
        [binMulStateSep₂] ++ chainBinaryRepr fuel) =
    chainBinaryRepr (acc + fuel * addend) ++ [binMulStateSep₁] ++
      chainBinaryRepr addend ++ [binMulStateSep₂] ++ chainBinaryRepr 0 := by
  induction' fuel with fuel ih generalizing acc
  · simp [blockIterateWhile]
  · rw [blockIterateWhile_succ_true]
    · rw [binMulPairedStep3_normalized_state]
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (acc + addend)
    · unfold binMulPairedCond3 blockValueLeq
      rw [binMulPairedFuel3_normalized_state]
      simp [decodeBinaryBlock_chainBinaryRepr]

theorem tm0_binMulPairedResult3_block :
    TM0RealizesBlock ChainΓ binMulPairedResult3 := by
  rw [show binMulPairedResult3 =
      (List.takeWhile (fun x => !decide (x = binMulStateSep₁))) from ?_]
  · exact tm0_takeWhileNeSep binMulStateSep₁
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default)
  · funext block
    unfold binMulPairedResult3
    exact splitAtSep_fst_eq_takeWhile binMulStateSep₁ block

theorem tm0_binMulPairedResult_block :
    TM0RealizesBlock ChainΓ binMulPairedResult := by
  simpa [binMulPairedResult, extractPairedLeft] using tm0_extractPairedLeft_block

/-- Prepare a paired multiplication input with a fixed left operand. -/
noncomputable def pairWithConstLeft (c : ℕ) (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr c ++ [chainConsBottom] ++ block

theorem pairWithConstLeft_ne_default (c : ℕ) (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pairWithConstLeft c block, g ≠ default := by
  unfold pairWithConstLeft
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · exact chainBinaryRepr_ne_default _ g hg
    · rw [List.mem_singleton.mp hg]
      exact chainConsBottom_ne_default
  · exact hblock g hg

/-- Prepare a paired multiplication input with both operands equal to the
    normalized input block. This is the functional copy point for squaring. -/
noncomputable def duplicateNormalizedPaired (block : List ChainΓ) : List ChainΓ :=
  pairNormalizedBlocks block block

theorem duplicateNormalizedPaired_ne_default (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ duplicateNormalizedPaired block, g ≠ default := by
  exact pairNormalizedBlocks_ne_default block block _hblock _hblock

/-- Appending a non-default prefix preserves non-defaultness. -/
theorem prependList_ne_default {Γ : Type} [Inhabited Γ] (pref block : List Γ)
    (hpref : ∀ g ∈ pref, g ≠ default)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pref ++ block, g ≠ default :=
  prependList_ne_default' pref block hpref hblock

/-- Prepending a list is block-realizable (derived from the sep version). -/
theorem tm0_prependList_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (pref : List Γ) (hpref : ∀ g ∈ pref, g ≠ default) :
    TM0RealizesBlock Γ (fun block => pref ++ block) :=
  tm0RealizesBlock_of_sep_default (tm0_prependList_blockSep pref hpref hpref)

/-- Pairing with a constant left operand is realizable before any separator. -/
theorem tm0_pairWithConstLeft_blockSep (c : ℕ) {sep : ChainΓ}
    (hsep_ne_consBottom : sep ≠ chainConsBottom)
    (hsep_ne_bits : ∀ g ∈ chainBinaryRepr c, g ≠ sep) :
    TM0RealizesBlockSep ChainΓ sep (pairWithConstLeft c) := by
  unfold pairWithConstLeft
  exact tm0_prependList_blockSep (chainBinaryRepr c ++ [chainConsBottom])
    (by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact chainBinaryRepr_ne_default _ g hg
      · rw [List.mem_singleton.mp hg]
        exact chainConsBottom_ne_default)
    (by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hsep_ne_bits g hg
      · rw [List.mem_singleton.mp hg]
        exact hsep_ne_consBottom.symm)

/-- Pairing with a constant left operand is block-realizable. -/
theorem tm0_pairWithConstLeft_block (c : ℕ) :
    TM0RealizesBlock ChainΓ (pairWithConstLeft c) := by
  unfold pairWithConstLeft
  exact tm0_prependList_block (chainBinaryRepr c ++ [chainConsBottom])
    (by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact chainBinaryRepr_ne_default _ g hg
      · rw [List.mem_singleton.mp hg]
        exact chainConsBottom_ne_default)

theorem tm0_binMulPairedInit_block
    (hnorm : TM0RealizesBlock ChainΓ normalizePairedBlocks) :
    TM0RealizesBlock ChainΓ binMulPairedInit := by
  unfold binMulPairedInit
  exact tm0RealizesBlock_comp
    hnorm
    (tm0_prependList_block (chainBinaryRepr 0 ++ [chainConsBottom]) (by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact chainBinaryRepr_ne_default _ g hg
      · rw [List.mem_singleton.mp hg]
        exact chainConsBottom_ne_default))
    normalizePairedBlocks_ne_default

@[simp]
theorem splitAtConsBottom_chainBinaryRepr_cons (c : ℕ) (block : List ChainΓ) :
    splitAtConsBottom (chainBinaryRepr c ++ chainConsBottom :: block) =
      (chainBinaryRepr c, block) := by
  simp

@[simp]
theorem splitAtConsBottom_chainBinaryRepr_sep (c : ℕ) (block : List ChainΓ) :
    splitAtConsBottom (chainBinaryRepr c ++ [chainConsBottom] ++ block) =
      (chainBinaryRepr c, block) :=
  splitAtConsBottom_binary_sep c block

theorem binMulConst_eq_paired (c : ℕ) :
    binMulConst c = binMulPaired ∘ pairWithConstLeft c := by
  funext block
  simp only [Function.comp, binMulConst, binMulPaired, pairWithConstLeft]
  simp [decodeBinaryBlock_chainBinaryRepr]

theorem tm0_binMulPairedLoop_blockInv
    (hstep : TM0RealizesBlockCondInv binMulPairedStep binMulPairedCond
      binMulPairedStateInv) :
    TM0RealizesBlockInv binMulPairedLoop binMulPairedStateInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ :=
    tm0RealizesBlock_while_inv
      binMulPairedStep
      binMulPairedLoop
      binMulPairedCond
      binMulPairedStateInv
      hstep
      (fun block hInv _hblock _hcond => binMulPairedStep_stateInv block hInv)
      binMulPairedStep_ne_default
      (fun block hblock hInv => binMulPairedWhile_eq_iterate block hblock)
      (fun block hblock _hInv => binMulPairedLoop_ne_default block hblock)
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block hInv hblock hresult
  exact hM block hInv hblock hresult

theorem tm0_binMulPairedLoop_blockInvSuffix
    (hstep : TM0RealizesBlockCondInvSuffix binMulPairedStep binMulPairedCond
      binMulPairedStateInv) :
    TM0RealizesBlockInvSuffix binMulPairedLoop binMulPairedStateInv := by
  exact tm0RealizesBlockInvSuffix_while
    binMulPairedStep
    binMulPairedLoop
    binMulPairedCond
    binMulPairedStateInv
    hstep
    (fun block hInv _hblock _hcond => binMulPairedStep_stateInv block hInv)
    binMulPairedStep_ne_default
    (fun block hblock hInv => binMulPairedWhile_eq_iterate block hblock)
    (fun block hblock _hInv => binMulPairedLoop_ne_default block hblock)

/-- Downstream multiplication only needs the loop body on invariant states,
with the default-delimited suffix preserved.

This is the replacement for the old total malformed-state step theorem: the
initializer establishes `binMulPairedStateInv`, the suffix-preserving while
combinator maintains it, and result extraction runs after the loop. -/
theorem tm0_binMulPaired_block_of_stepInvSuffix
    (hnorm : TM0RealizesBlock ChainΓ normalizePairedBlocks)
    (hstep : TM0RealizesBlockCondInvSuffix binMulPairedStep binMulPairedCond
      binMulPairedStateInv) :
    TM0RealizesBlock ChainΓ binMulPaired := by
  rw [binMulPaired_eq_repeated_add, binMulPairedWhile_eq_loop]
  apply tm0RealizesBlock_comp
  · exact tm0RealizesBlock_comp_invSuffix
      (tm0_binMulPairedInit_block hnorm)
      (tm0_binMulPairedLoop_blockInvSuffix hstep)
      (fun block _hblock => binMulPairedInit_stateInv block)
      binMulPairedInit_ne_default
  · exact tm0_binMulPairedResult_block
  · exact fun block hblock =>
      binMulPairedLoop_ne_default _ (binMulPairedInit_ne_default _ hblock)

/-- General paired multiplication is block-realizable.

The implementation loops over a copied multiplier, repeatedly rebuilding a
paired-addition input from the accumulator and addend, applying `binAddPaired`,
and decrementing the multiplier copy. The concrete copy/loop machine is
isolated here so clients can reduce to multiplication rather than each carrying
their own arithmetic loop. -/
theorem tm0_binMulPaired_block
    (hnorm : TM0RealizesBlock ChainΓ normalizePairedBlocks)
    (hstep : TM0RealizesBlockCondInvSuffix binMulPairedStep binMulPairedCond
      binMulPairedStateInv) :
    TM0RealizesBlock ChainΓ binMulPaired := by
  exact tm0_binMulPaired_block_of_stepInvSuffix hnorm hstep

/-- `duplicateNormalizedPaired = copyBinaryWithSep ∘ normalizeBlock`. -/
theorem duplicateNormalizedPaired_eq_copyWithSep_comp :
    duplicateNormalizedPaired = copyBinaryWithSep ∘ normalizeBlock := by
  funext block
  simp only [Function.comp, copyBinaryWithSep, copyWithSep, normalizeBlock,
    duplicateNormalizedPaired, pairNormalizedBlocks]

/-- Normalized self-duplication is block-realizable.
This is the variable-copy primitive needed for squaring: it writes two copies
of the normalized input separated by `chainConsBottom`. -/
theorem tm0_duplicateNormalizedPaired_block :
    TM0RealizesBlock ChainΓ duplicateNormalizedPaired := by
  rw [duplicateNormalizedPaired_eq_copyWithSep_comp]
  exact tm0RealizesBlock_comp
    tm0_normalizeBlock
    tm0_copyBinaryWithSep_block
    (fun _ _ => normalizeBlock_ne_default _)

noncomputable def binMulConstInit (c : ℕ) (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr 0 ++ [chainConsBottom] ++ chainBinaryRepr c ++
    [chainConsBottom] ++ normalizeBlock block

theorem binMulConstInit_ne_default (c : ℕ) (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulConstInit c block, g ≠ default := by
  unfold binMulConstInit
  simp +zetaDelta
  rintro g (hg | rfl | hg | rfl | hg)
  · exact chainBinaryRepr_ne_default _ g hg
  · exact chainConsBottom_ne_default
  · exact chainBinaryRepr_ne_default _ g hg
  · exact chainConsBottom_ne_default
  · exact normalizeBlock_ne_default block g hg

theorem binMulConstInit_stateInv (c : ℕ) (block : List ChainΓ) :
    binMulPairedStateInv (binMulConstInit c block) := by
  unfold binMulPairedStateInv binMulConstInit hasConsBottom
  simp [splitAtConsBottom_binary_sep, normalizeBlock_no_consBottom, List.append_assoc]
  exact normalizeBlock_no_consBottom block

theorem tm0_binMulConstInit_block (c : ℕ) :
    TM0RealizesBlock ChainΓ (binMulConstInit c) := by
  unfold binMulConstInit
  exact tm0RealizesBlock_comp
    tm0_normalizeBlock
    (tm0_prependList_block
      (chainBinaryRepr 0 ++ [chainConsBottom] ++ chainBinaryRepr c ++ [chainConsBottom])
      (by
        intro g hg
        simp +zetaDelta at hg
        rcases hg with hg | rfl | hg | rfl
        · exact chainBinaryRepr_ne_default _ g hg
        · exact chainConsBottom_ne_default
        · exact chainBinaryRepr_ne_default _ g hg
        · exact chainConsBottom_ne_default))
    (fun _ _ => normalizeBlock_ne_default _)

theorem binMulConst_eq_direct_loop (c : ℕ) :
    binMulConst c =
      binMulPairedResult ∘ binMulPairedLoop ∘ binMulConstInit c := by
  funext block
  unfold Function.comp binMulConst binMulPairedResult binMulPairedLoop binMulConstInit normalizeBlock
  rw [binMulPairedFuel_normalized_state, decodeBinaryBlock_chainBinaryRepr,
    binMulPairedLoop_normalized_state]
  simp [Nat.mul_comm, List.append_assoc]

/-- **Multiplication by constant is block-realizable**, once paired
multiplication has the invariant/suffix loop body. -/
theorem tm0_binMulConst_block
    (hstep : TM0RealizesBlockCondInvSuffix binMulPairedStep binMulPairedCond
      binMulPairedStateInv)
    (c : ℕ) : TM0RealizesBlock ChainΓ (binMulConst c) := by
  rw [binMulConst_eq_direct_loop]
  apply tm0RealizesBlock_comp
  · exact tm0RealizesBlock_comp_invSuffix
      (tm0_binMulConstInit_block c)
      (tm0_binMulPairedLoop_blockInvSuffix hstep)
      (fun block _hblock => binMulConstInit_stateInv c block)
      (binMulConstInit_ne_default c)
  · exact tm0_binMulPairedResult_block
  · exact fun block hblock =>
      binMulPairedLoop_ne_default _ (binMulConstInit_ne_default c block hblock)

/-! ### Binary Squaring -/

/-- Square the binary block value: n → n². -/
noncomputable def binSquare (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr ((decodeBinaryBlock block) ^ 2)

theorem binSquare_correct (n : ℕ) :
    binSquare (chainBinaryRepr n) = chainBinaryRepr (n ^ 2) := by
  unfold binSquare; rw [decodeBinaryBlock_chainBinaryRepr]

theorem binSquare_ne_default (block : List ChainΓ) (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binSquare block, g ≠ default := by
  unfold binSquare; exact chainBinaryRepr_ne_default _

/-! #### Three-separator square route -/

noncomputable def binSquareInit3 (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr 0 ++ [binMulStateSep₁] ++ normalizeBlock block ++
    [binMulStateSep₂] ++ normalizeBlock block

theorem binSquareInit3_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binSquareInit3 block, g ≠ default := by
  unfold binSquareInit3
  simp
  rintro g (hg | rfl | hg | rfl | hg)
  · exact chainBinaryRepr_ne_default _ g hg
  · exact chainMulSep₁_ne_default
  · exact normalizeBlock_ne_default block g hg
  · exact chainMulSep₂_ne_default
  · exact normalizeBlock_ne_default block g hg

theorem binSquareInit3_stateInv (block : List ChainΓ) :
    binMulPairedStateInv3 (binSquareInit3 block) := by
  unfold binMulPairedStateInv3 binSquareInit3
  simp [chainMulSep₁_ne_chainMulSep₂, normalizeBlock_no_mulSep₁,
    normalizeBlock_no_mulSep₂, chainBinaryRepr_no_chainMulSep₂]
  exact ⟨
    (by simpa [binMulStateSep₂] using chainBinaryRepr_no_chainMulSep₂ 0),
    normalizeBlock_no_mulSep₁ block,
    normalizeBlock_no_mulSep₂ block⟩

theorem binSquareInit3_eq_copyWithSep_comp :
    binSquareInit3 =
      (fun block => chainBinaryRepr 0 ++ [binMulStateSep₁] ++ block) ∘
        copyWithSep binMulStateSep₂ ∘ normalizeBlock := by
  funext block
  simp [Function.comp, binSquareInit3, copyWithSep, List.append_assoc]

theorem tm0_binSquareInit3_block :
    TM0RealizesBlock ChainΓ binSquareInit3 := by
  rw [binSquareInit3_eq_copyWithSep_comp]
  apply tm0RealizesBlock_comp
  · exact tm0RealizesBlock_comp
      tm0_normalizeBlock
      (tm0_copyWithSep_block
        (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default))
      (fun _ _ => normalizeBlock_ne_default _)
  · exact tm0_prependList_block
      (chainBinaryRepr 0 ++ [binMulStateSep₁])
      (by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact chainBinaryRepr_ne_default _ g hg
        · rw [List.mem_singleton.mp hg]
          exact chainMulSep₁_ne_default)
  · intro block hblock
    exact copyWithSep_ne_default
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
      (normalizeBlock block) (normalizeBlock_ne_default block)

theorem binSquare_eq_direct_loop3 :
    binSquare = binMulPairedResult3 ∘ binMulPairedLoop3 ∘ binSquareInit3 := by
  funext block
  unfold Function.comp binSquare binMulPairedResult3 binMulPairedLoop3 binSquareInit3
    normalizeBlock
  rw [binMulPairedFuel3_normalized_state]
  rw [decodeBinaryBlock_chainBinaryRepr]
  rw [binMulPairedLoop3_normalized_state]
  simp [pow_two, Nat.mul_comm, List.append_assoc]

theorem tm0_binSquare_block
    (hstep : TM0RealizesBlockCondInvSuffix binMulPairedStep3 binMulPairedCond3
      binMulPairedStateInv3) :
    TM0RealizesBlock ChainΓ binSquare := by
  rw [binSquare_eq_direct_loop3]
  apply tm0RealizesBlock_comp
  · exact tm0RealizesBlock_comp_invSuffix
      tm0_binSquareInit3_block
      (tm0_binMulPairedLoop3_blockInvSuffix hstep)
      (fun block _hblock => binSquareInit3_stateInv block)
      binSquareInit3_ne_default
  · exact tm0_binMulPairedResult3_block
  · exact fun block hblock =>
      binMulPairedLoop3_ne_default _ (binSquareInit3_ne_default block hblock)

noncomputable def binSquareInit (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr 0 ++ [chainConsBottom] ++ duplicateNormalizedPaired block

theorem binSquareInit_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binSquareInit block, g ≠ default := by
  unfold binSquareInit
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · exact chainBinaryRepr_ne_default _ g hg
    · rw [List.mem_singleton.mp hg]
      exact chainConsBottom_ne_default
  · exact duplicateNormalizedPaired_ne_default block hblock g hg

theorem binSquareInit_stateInv (block : List ChainΓ) :
    binMulPairedStateInv (binSquareInit block) := by
  unfold binMulPairedStateInv binSquareInit duplicateNormalizedPaired pairNormalizedBlocks
    hasConsBottom
  simp [splitAtConsBottom_binary_sep, chainBinaryRepr_no_consBottom, List.append_assoc]
  exact chainBinaryRepr_no_consBottom _

theorem tm0_binSquareInit_block :
    TM0RealizesBlock ChainΓ binSquareInit := by
  unfold binSquareInit
  exact tm0RealizesBlock_comp
    tm0_duplicateNormalizedPaired_block
    (tm0_prependList_block (chainBinaryRepr 0 ++ [chainConsBottom]) (by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact chainBinaryRepr_ne_default _ g hg
      · rw [List.mem_singleton.mp hg]
        exact chainConsBottom_ne_default))
    duplicateNormalizedPaired_ne_default

theorem binSquare_eq_paired :
    binSquare = binMulPaired ∘ duplicateNormalizedPaired := by
  funext block
  simp only [Function.comp, binSquare, binMulPaired, duplicateNormalizedPaired, pairNormalizedBlocks]
  rw [splitAtConsBottom_chainBinaryRepr_sep]
  simp [pow_two, decodeBinaryBlock_chainBinaryRepr]

theorem binSquare_eq_direct_loop :
    binSquare = binMulPairedResult ∘ binMulPairedLoop ∘ binSquareInit := by
  rw [binSquare_eq_paired, binMulPaired_eq_repeated_add, binMulPairedWhile_eq_loop]
  funext block
  simp [Function.comp, binMulPairedInit, binSquareInit, normalizePairedBlocks,
    duplicateNormalizedPaired, pairNormalizedBlocks, normalizeBlock,
    splitAtConsBottom_chainBinaryRepr_sep, decodeBinaryBlock_chainBinaryRepr,
    List.append_assoc]

theorem tm0_binSquare_block_consBottom
    (hstep : TM0RealizesBlockCondInvSuffix binMulPairedStep binMulPairedCond
      binMulPairedStateInv) :
    TM0RealizesBlock ChainΓ binSquare := by
  rw [binSquare_eq_direct_loop]
  apply tm0RealizesBlock_comp
  · exact tm0RealizesBlock_comp_invSuffix
      tm0_binSquareInit_block
      (tm0_binMulPairedLoop_blockInvSuffix hstep)
      (fun block _hblock => binSquareInit_stateInv block)
      binSquareInit_ne_default
  · exact tm0_binMulPairedResult_block
  · exact fun block hblock =>
      binMulPairedLoop_ne_default _ (binSquareInit_ne_default block hblock)
