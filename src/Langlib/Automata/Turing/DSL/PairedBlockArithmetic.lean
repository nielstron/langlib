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

/-
Key iteration: after k steps on normalized input,
    left = chainBinaryRepr(a + k), right = binPredRaw^[k](chainBinaryRepr b).
-/
theorem incLeftDecRight_iterate (k a b : ℕ) :
    incLeftDecRight^[k] (chainBinaryRepr a ++ [chainConsBottom] ++ chainBinaryRepr b) =
      chainBinaryRepr (a + k) ++ [chainConsBottom] ++ binPredRaw^[k] (chainBinaryRepr b) := by
  induction' k with k ih;
  · rfl;
  · rw [ Function.iterate_succ_apply', ih ];
    unfold incLeftDecRight;
    rw [if_pos (by simp)]
    rw [ splitAtConsBottom_binary_sep ];
    rw [ ← add_assoc, Function.iterate_succ_apply' ];
    exact congr_arg₂ _ ( congr_arg₂ _ ( binSucc_correct _ ) rfl ) rfl

/-- `incLeftDecRight` is block-realizable.
    Decomposed as `decAfterSep ∘ incBeforeSep`:
    first increment the left sub-block, then decrement the right sub-block.
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
  exact ⟨decodeBinaryBlock_chainBinaryRepr _, decodeBinaryBlock_chainBinaryRepr _⟩

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
  sorry

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
input, add it into an accumulator, decrement the counter, and loop. -/

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
  let n := decodeBinaryBlock block
  chainBinaryRepr n ++ [chainConsBottom] ++ chainBinaryRepr n

theorem duplicateNormalizedPaired_ne_default (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ duplicateNormalizedPaired block, g ≠ default := by
  unfold duplicateNormalizedPaired
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · exact chainBinaryRepr_ne_default _ g hg
    · rw [List.mem_singleton.mp hg]
      exact chainConsBottom_ne_default
  · exact chainBinaryRepr_ne_default _ g hg

theorem tm0_id_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] :
    TM0RealizesBlock Γ id := by
  have h : id = List.reverse ∘ @List.reverse Γ := by
    funext block
    simp
  rw [h]
  exact tm0RealizesBlock_comp tm0_reverse_block tm0_reverse_block reverse_ne_default

theorem prependList_ne_default {Γ : Type} [Inhabited Γ] (pref block : List Γ)
    (hpref : ∀ g ∈ pref, g ≠ default)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pref ++ block, g ≠ default := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hpref g hg
  · exact hblock g hg

theorem tm0_prependList_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (pref : List Γ) (hpref : ∀ g ∈ pref, g ≠ default) :
    TM0RealizesBlock Γ (fun block => pref ++ block) := by
  induction' pref with c rest ih
  · simpa using (tm0_id_block (Γ := Γ))
  · have hc : c ≠ default := hpref c List.mem_cons_self
    have hrest : ∀ g ∈ rest, g ≠ default := fun g hg => hpref g (List.mem_cons_of_mem _ hg)
    have hcomp := tm0RealizesBlock_comp (ih hrest) (tm0_cons_block c hc)
      (fun block hblock => prependList_ne_default rest block hrest hblock)
    simpa [Function.comp, List.cons_append] using hcomp

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

@[simp]
theorem splitAtConsBottom_chainBinaryRepr_cons (c : ℕ) (block : List ChainΓ) :
    splitAtConsBottom (chainBinaryRepr c ++ chainConsBottom :: block) =
      (chainBinaryRepr c, block) := by
  simpa using splitAtConsBottom_binary_sep c block

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

The intended implementation loops over one operand, repeatedly rebuilding a
paired-addition input by copying the other operand, applying `binAddPaired`,
and decrementing the counter. The concrete copy/loop machine is isolated here
so clients can reduce to multiplication rather than each carrying their own
arithmetic loop. -/
theorem tm0_binMulPaired_block :
    TM0RealizesBlock ChainΓ binMulPaired := by
  sorry

/-- Normalized self-duplication is block-realizable.

This is the variable-copy primitive needed for squaring: it writes two copies
of the normalized input separated by `chainConsBottom`. -/
theorem tm0_duplicateNormalizedPaired_block :
    TM0RealizesBlock ChainΓ duplicateNormalizedPaired := by
  sorry

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
  simp only [Function.comp, binSquare, binMulPaired, duplicateNormalizedPaired]
  rw [splitAtConsBottom_chainBinaryRepr_sep]
  simp [pow_two, decodeBinaryBlock_chainBinaryRepr]

theorem tm0_binSquare_block : TM0RealizesBlock ChainΓ binSquare := by
  rw [binSquare_eq_paired]
  exact tm0RealizesBlock_comp
    tm0_duplicateNormalizedPaired_block
    tm0_binMulPaired_block
    duplicateNormalizedPaired_ne_default
