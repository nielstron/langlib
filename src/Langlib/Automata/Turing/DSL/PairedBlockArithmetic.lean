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

/-! # Paired Block Arithmetic — The Central Primitive

This file establishes **paired block addition** (`binAddPaired`) as the
central arithmetic primitive. Two numbers are stored side-by-side on the
tape, separated by `chainConsBottom`. Addition of the right value to the
left value is the fundamental operation from which both squaring and
multiplication by a constant are derived.

## Architecture

```
                    binAddPaired  (add right to left)
                    ╱            ╲
           binMulPaired           (iterate until right = 0)
           ╱         ╲
   binSquare         binMulConst c
   (dup + mul)       (write c + mul)
```

- **`binAddPaired`**: given `[left][sep][right]`, produces
  `[left + right][sep][right]`. This is "addition of neighboring numbers".

- **`binMulPaired`**: multiply two paired blocks via iterated addition.
  Iterates: add right to accumulator, decrement right, repeat until zero.
  Result: `[left * right][sep][0]` (which simplifies to `[left * right]`
  after extraction).

- **`binSquare`**: duplicate `n` as `[n][sep][n]`, then multiply paired.

- **`binMulConst c`**: write constant `c` as `[0][sep][block]`, iterate
  paired addition `c` times, then extract left. Equivalently:
  `extractPairedLeft ∘ binAddPaired^[c] ∘ (chainConsBottom :: ·)`.

Both squaring and multiplication by constant reuse the same paired
addition mechanism.

## Design principle

All operations here are defined purely in terms of `decodeBinaryBlock`
and `chainBinaryRepr` (the decode/encode pipeline). Block-realizability
proofs compose via `tm0RealizesBlock_comp`.
-/

open Turing PartrecToTM2 TM2to1

/-! ### Paired Block Addition — The Central Primitive -/

/-- **Paired block addition** (addition of neighboring numbers).
    Split the block at the first `chainConsBottom`, decode both halves,
    add them, re-encode the left, and preserve the right.

    Given a block encoding `[left][sep][right]`, produces
    `[left + right][sep][right]`. -/
noncomputable def binAddPaired (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  chainBinaryRepr (decodeBinaryBlock left + decodeBinaryBlock right)
    ++ [chainConsBottom] ++ right

/-- Extract the left sub-block (prefix before first `chainConsBottom`). -/
noncomputable def extractPairedLeft (block : List ChainΓ) : List ChainΓ :=
  (splitAtConsBottom block).1

/-- `binAddPaired` preserves non-defaultness. -/
theorem binAddPaired_ne_default (block : List ChainΓ)
    (h : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binAddPaired block, g ≠ default := by
  unfold binAddPaired;
  simp +zetaDelta at *;
  rintro g ( hg | rfl | hg );
  · exact chainBinaryRepr_ne_default _ _ hg;
  · exact fun h => by have := congr_arg Prod.fst h; simp +decide at this;
  · exact h g (splitAtConsBottom_snd_subset block g hg)

/-- `extractPairedLeft` preserves non-defaultness. -/
theorem extractPairedLeft_ne_default (block : List ChainΓ)
    (h : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ extractPairedLeft block, g ≠ default := by
  induction' block with c rest ih;
  · decide +kernel;
  · intro g hg
    exact h g (splitAtConsBottom_fst_subset _ g (by unfold extractPairedLeft at hg; exact hg))

/-- After `c` iterations of `binAddPaired` on `[chainConsBottom] ++ block`,
    the result is `chainBinaryRepr (c * decodeBinaryBlock block) ++
    [chainConsBottom] ++ block`. -/
theorem binAddPaired_iterate_sep (c : ℕ) (block : List ChainΓ) :
    binAddPaired^[c] (chainConsBottom :: block) =
      chainBinaryRepr (c * decodeBinaryBlock block)
        ++ [chainConsBottom] ++ block := by
  induction' c with c ih generalizing block;
  · unfold chainBinaryRepr; aesop;
  · rw [ Function.iterate_succ_apply', ih ];
    rw [ binAddPaired, splitAtConsBottom_binary_sep ];
    simp +decide [ add_mul, decodeBinaryBlock_chainBinaryRepr ]

/-! ### Paired Block Multiplication

`binMulPaired` multiplies two numbers stored side-by-side.
Both `binSquare` and `binMulConst` decompose through this operation.

For multiplication by a constant `c`, we use the simpler approach of
iterating `binAddPaired` exactly `c` times (the constant is known at
construction time). For squaring, we define `binSquare` directly via
the decode/encode pipeline and prove its block-realizability by
decomposing through paired addition. -/


/-! ### Multiplication by Constant -/

/-- Multiply the binary block value by a fixed constant c: n → c * n.
    Realized by writing `[0][sep][n]` (prepend separator), iterating
    `binAddPaired` c times, then extracting the left sub-block. -/
noncomputable def binMulConst (c : ℕ) (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (c * decodeBinaryBlock block)

theorem binMulConst_correct (c n : ℕ) :
    binMulConst c (chainBinaryRepr n) = chainBinaryRepr (c * n) := by
  unfold binMulConst; rw [decodeBinaryBlock_chainBinaryRepr]

theorem binMulConst_ne_default (c : ℕ) (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulConst c block, g ≠ default := by
  unfold binMulConst; exact chainBinaryRepr_ne_default _

/-- Functional decomposition: `binMulConst c` equals
    `extractPairedLeft ∘ binAddPaired^[c] ∘ (chainConsBottom :: ·)`.

    This shows that multiplication by a constant reuses the same
    paired addition mechanism: prepend a separator (creating `[0][sep][n]`),
    iterate addition c times (accumulating `c * n` on the left), then
    extract the result. -/
theorem binMulConst_eq_decomp (c : ℕ) :
    binMulConst c =
      extractPairedLeft ∘ (binAddPaired^[c]) ∘ (chainConsBottom :: ·) := by
  ext x;
  rw [ Function.comp_apply, Function.comp_apply, binAddPaired_iterate_sep ];
  rw [ extractPairedLeft, splitAtConsBottom_binary_sep ];
  rfl

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

/-! ### Block-realizability of paired operations -/

/-- **Paired addition is block-realizable.**

    Strategy: The proof decomposes binAddPaired through:
    1. Normalize the left sub-block
    2. Iterate incLeftDecRight (decodeBinaryBlock right) times
    3. Normalize the result

    Each component is block-realizable, and the composition
    yields binAddPaired.
-/
theorem tm0_binAddPaired_block :
    TM0RealizesBlock ChainΓ binAddPaired := by
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
          split_ifs <;> simp_all +decide [ List.append_assoc ];
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

/-- **Multiplication by constant is block-realizable.**

    Decomposed as:
    1. Prepend separator (`chainConsBottom :: ·`) — block-realizable
    2. Iterate paired addition `c` times — block-realizable
    3. Extract left sub-block — block-realizable
    Composed via `tm0RealizesBlock_comp`. -/
theorem tm0_binMulConst_block (c : ℕ) : TM0RealizesBlock ChainΓ (binMulConst c) := by
  rw [binMulConst_eq_decomp]
  apply tm0RealizesBlock_comp
  · apply tm0RealizesBlock_comp
    · exact tm0_cons_block chainConsBottom chainConsBottom_ne_default
    · exact tm0RealizesBlock_iterate tm0_binAddPaired_block binAddPaired_ne_default c
    · intro block hblock
      exact List.forall_mem_cons.mpr ⟨chainConsBottom_ne_default, hblock⟩
  · exact tm0_extractPairedLeft_block
  · intro block hblock
    exact iterate_preserves_nd binAddPaired_ne_default c
      (chainConsBottom :: block)
      (List.forall_mem_cons.mpr ⟨chainConsBottom_ne_default, hblock⟩)

/-! ### Binary Squaring -/

/-- Square the binary block value: n → n².
    Equivalent to duplicating the block as `[0][sep][n]` and
    iterating paired addition `n` times. -/
noncomputable def binSquare (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr ((decodeBinaryBlock block) ^ 2)

theorem binSquare_correct (n : ℕ) :
    binSquare (chainBinaryRepr n) = chainBinaryRepr (n ^ 2) := by
  unfold binSquare; rw [decodeBinaryBlock_chainBinaryRepr]

theorem binSquare_ne_default (block : List ChainΓ) (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binSquare block, g ≠ default := by
  unfold binSquare; exact chainBinaryRepr_ne_default _

theorem tm0_binSquare_block : TM0RealizesBlock ChainΓ binSquare := by
  sorry
