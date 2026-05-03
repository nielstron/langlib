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
import Langlib.Automata.Turing.DSL.CopyBinaryBlock

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

/-- `incLeftDecRight` is block-realizable.
    Decomposed as `decAfterSep ∘ incBeforeSep`:
    first decrement the left sub-block, then increment the right sub-block.
    Each component is block-realizable via adapted TM0 machines. -/
theorem tm0_incLeftDecRight_block :
    TM0RealizesBlock ChainΓ incLeftDecRight := by
  rw [incLeftDecRight_eq_comp]
  exact tm0RealizesBlock_comp
    tm0_incBeforeSep_block
    tm0_decAfterSep_block
    incBeforeSep_ne_default

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
    and increment the right sub-block. -/
noncomputable def pairedDecrLeftIncrRight (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  chainBinaryRepr (decodeBinaryBlock left - 1)
    ++ [chainConsBottom]
    ++ chainBinaryRepr (decodeBinaryBlock right + 1)

/-- `pairedDecrLeftIncrRight` preserves non-defaultness when the condition holds. -/
theorem pairedDecrLeftIncrRight_ne_default (block : List ChainΓ)
    (_h : ∀ g ∈ block, g ≠ default) (_hcond : ¬ blockValueLeq 0 block) :
    ∀ g ∈ pairedDecrLeftIncrRight block, g ≠ default := by
  unfold pairedDecrLeftIncrRight
  simp +zetaDelta
  rintro g (hg | rfl | hg)
  · exact chainBinaryRepr_ne_default _ g hg
  · exact chainConsBottom_ne_default
  · exact chainBinaryRepr_ne_default _ g hg

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

/-- The while loop result equals `blockIterateWhile` with appropriate fuel. -/
theorem binAddPairedWhile_eq_iterate (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∃ n, binAddPairedWhile block =
        blockIterateWhile pairedDecrLeftIncrRight pairedAddCond n block ∧
      ¬ pairedAddCond
        (blockIterateWhile pairedDecrLeftIncrRight pairedAddCond n block) := by
  refine' ⟨_, rfl, _⟩
  have h_left_zero :
      decodeBinaryBlock
        (splitAtConsBottom
          (blockIterateWhile pairedDecrLeftIncrRight pairedAddCond
            (decodeBinaryBlock (splitAtConsBottom block).1) block)).1 = 0 := by
    have h_left_zero : ∀ (k : ℕ), k ≤ decodeBinaryBlock (splitAtConsBottom block).1 →
        decodeBinaryBlock (splitAtConsBottom (pairedDecrLeftIncrRight^[k] block)).1 =
          decodeBinaryBlock (splitAtConsBottom block).1 - k := by
      intro k hk
      induction' k with k ih
      · norm_num
      · rw [Function.iterate_succ_apply']
        rw [Nat.sub_succ]
        rw [← ih (Nat.le_of_succ_le hk)]
        rw [pairedDecrLeftIncrRight]
        grind +suggestions
    rw [blockIterateWhile_eq_iterate_of_cond]
    · rw [h_left_zero _ le_rfl, Nat.sub_self]
    · intro k hk
      specialize h_left_zero k hk.le
      simp_all +decide [pairedAddCond]
      unfold blockValueLeq
      simp_all +decide
      rw [decodeBinaryBlock_eq_splitLeft]
      omega
  simp [pairedAddCond, blockValueLeq]
  rwa [decodeBinaryBlock_eq_splitLeft]

/-- Non-defaultness of the while loop result. -/
theorem binAddPairedWhile_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binAddPairedWhile block, g ≠ default := by
  obtain ⟨n, hn⟩ := binAddPairedWhile_eq_iterate block hblock
  have h_ind : ∀ (n : ℕ) (block : List ChainΓ), (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ blockIterateWhile pairedDecrLeftIncrRight pairedAddCond n block, g ≠ default := by
    intro n block hblock
    induction' n with n ih generalizing block
    · exact hblock
    · by_cases h : pairedAddCond block <;> simp +decide [h, blockIterateWhile]
      · exact ih _ (pairedDecrLeftIncrRight_ne_default _ hblock h)
      · exact hblock
  exact hn.1 ▸ h_ind n block hblock

/-- After k iterations of pairedDecrLeftIncrRight, the left and right decode
    values change as expected. -/
theorem pairedDecrLeftIncrRight_iterate_decode (block : List ChainΓ) (k : ℕ)
    (hk : k ≤ decodeBinaryBlock (splitAtConsBottom block).1) :
    let result := pairedDecrLeftIncrRight^[k] block
    decodeBinaryBlock (splitAtConsBottom result).1 =
      decodeBinaryBlock (splitAtConsBottom block).1 - k ∧
    decodeBinaryBlock (splitAtConsBottom result).2 =
      decodeBinaryBlock (splitAtConsBottom block).2 + k := by
  induction' k with k ih generalizing block <;>
    simp_all +decide [Function.iterate_succ_apply']
  specialize ih block hk.le
  unfold pairedDecrLeftIncrRight at *
  rw [splitAtConsBottom_binary_sep]
  simp +decide
  simp_all +decide [Nat.sub_sub, add_assoc]

/-- `binAddPaired = normalizeBlock ∘ extractPairedRight ∘ binAddPairedWhile`. -/
theorem binAddPaired_eq_while_decomp :
    binAddPaired = normalizeBlock ∘ extractPairedRight ∘ binAddPairedWhile := by
  unfold binAddPaired normalizeBlock extractPairedRight binAddPairedWhile
  ext block
  have h_iter : ∀ (k : ℕ), k ≤ decodeBinaryBlock (splitAtConsBottom block).1 →
      blockIterateWhile pairedDecrLeftIncrRight pairedAddCond k block =
        pairedDecrLeftIncrRight^[k] block := by
    intro k hk
    induction' k with k ih generalizing block <;>
      simp_all +decide [Function.iterate_succ_apply', blockIterateWhile]
    rw [if_neg]
    · rw [← Function.iterate_succ_apply' pairedDecrLeftIncrRight k block, ih]
      · rfl
      · have := pairedDecrLeftIncrRight_iterate_decode block 1 (by linarith)
        simp_all +decide
        exact Nat.le_sub_one_of_lt hk
    · contrapose! hk
      exact le_trans (decodeBinaryBlock_eq_splitLeft block ▸ hk) (Nat.zero_le _)
  simp +decide [h_iter _ le_rfl]
  rw [pairedDecrLeftIncrRight_iterate_decode _ _ le_rfl |>.2]
  rw [add_comm]

/-! ### Block-realizability of paired operations -/

/-- The decrement-left / increment-right step satisfies `TM0RealizesBlockCond`. -/
theorem tm0_pairedDecrLeftIncrRight_blockCond :
    TM0RealizesBlockCond pairedDecrLeftIncrRight pairedAddCond := by
  sorry

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

/-- **Paired addition is block-realizable.**

    Decomposed as `normalizeBlock ∘ extractPairedRight ∘ binAddPairedWhile`:
    1. The while loop iterates `pairedDecrLeftIncrRight` while the left
       sub-block is positive.
    2. `extractPairedRight` extracts the accumulated sum.
    3. `normalizeBlock` produces canonical binary representation.
-/
theorem tm0_binAddPaired_block :
    TM0RealizesBlock ChainΓ binAddPaired := by
  rw [binAddPaired_eq_while_decomp]
  apply tm0RealizesBlock_comp
  · apply tm0RealizesBlock_comp
    · exact tm0RealizesBlock_while
        pairedDecrLeftIncrRight
        binAddPairedWhile
        pairedAddCond
        tm0_pairedDecrLeftIncrRight_blockCond
        pairedDecrLeftIncrRight_ne_default
        binAddPairedWhile_eq_iterate
        binAddPairedWhile_ne_default
    · exact tm0_extractPairedRight_block
    · exact binAddPairedWhile_ne_default
  · exact tm0_normalizeBlock
  · exact extractPairedRight_binAddPairedWhile_ne_default

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

theorem tm0_normalizePairedBlocks_block :
    TM0RealizesBlock ChainΓ normalizePairedBlocks := by
  sorry

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

/-- The multiplication loop body is realized by rebuilding the paired-add
    input, running `tm0_binAddPaired_block`, restoring the retained addend, and
    decrementing the copied multiplier. -/
theorem tm0_binMulPairedStep_blockCond :
    TM0RealizesBlockCond binMulPairedStep binMulPairedCond := by
  have _hadd := tm0_binAddPaired_block
  sorry

theorem binMulPairedWhile_eq_iterate (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∃ n, binMulPairedLoop block =
        blockIterateWhile binMulPairedStep binMulPairedCond n block ∧
      ¬ binMulPairedCond
        (blockIterateWhile binMulPairedStep binMulPairedCond n block) := by
  refine ⟨decodeBinaryBlock (binMulPairedFuel block), rfl, ?_⟩
  sorry

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

theorem tm0_binMulPairedInit_block :
    TM0RealizesBlock ChainΓ binMulPairedInit := by
  unfold binMulPairedInit
  exact tm0RealizesBlock_comp
    tm0_normalizePairedBlocks_block
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

/-- General paired multiplication is block-realizable.

The implementation loops over a copied multiplier, repeatedly rebuilding a
paired-addition input from the accumulator and addend, applying `binAddPaired`,
and decrementing the multiplier copy. The concrete copy/loop machine is
isolated here so clients can reduce to multiplication rather than each carrying
their own arithmetic loop. -/
theorem tm0_binMulPaired_block :
    TM0RealizesBlock ChainΓ binMulPaired := by
  rw [binMulPaired_eq_repeated_add, binMulPairedWhile_eq_loop]
  apply tm0RealizesBlock_comp
  · apply tm0RealizesBlock_comp
    · exact tm0_binMulPairedInit_block
    · exact tm0RealizesBlock_while
        binMulPairedStep
        binMulPairedLoop
        binMulPairedCond
        tm0_binMulPairedStep_blockCond
        binMulPairedStep_ne_default
        binMulPairedWhile_eq_iterate
        binMulPairedLoop_ne_default
    · exact binMulPairedInit_ne_default
  · exact tm0_binMulPairedResult_block
  · exact fun block hblock =>
      binMulPairedLoop_ne_default _ (binMulPairedInit_ne_default _ hblock)

/-- `duplicateNormalizedPaired = copyBinaryWithSep ∘ normalizeBlock`. -/
theorem duplicateNormalizedPaired_eq_copyWithSep_comp :
    duplicateNormalizedPaired = copyBinaryWithSep ∘ normalizeBlock := by
  funext block
  simp only [Function.comp, copyBinaryWithSep, normalizeBlock,
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

/-- **Multiplication by constant is block-realizable.** -/
theorem tm0_binMulConst_block (c : ℕ) : TM0RealizesBlock ChainΓ (binMulConst c) := by
  rw [binMulConst_eq_paired]
  exact tm0RealizesBlock_comp
    (tm0_pairWithConstLeft_block c)
    tm0_binMulPaired_block
    (pairWithConstLeft_ne_default c)

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

theorem binSquare_eq_paired :
    binSquare = binMulPaired ∘ duplicateNormalizedPaired := by
  funext block
  simp only [Function.comp, binSquare, binMulPaired, duplicateNormalizedPaired, pairNormalizedBlocks]
  rw [splitAtConsBottom_chainBinaryRepr_sep]
  simp [pow_two, decodeBinaryBlock_chainBinaryRepr]

theorem tm0_binSquare_block : TM0RealizesBlock ChainΓ binSquare := by
  rw [binSquare_eq_paired]
  exact tm0RealizesBlock_comp
    tm0_duplicateNormalizedPaired_block
    tm0_binMulPaired_block
    duplicateNormalizedPaired_ne_default
