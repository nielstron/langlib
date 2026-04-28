import Langlib.Automata.Turing.DSL.PairedBlockArithmetic

/-! # Binary Squaring — Standalone Reference

This file re-exports the squaring decomposition from `PairedBlockArithmetic.lean`.

## Architecture

Squaring reuses the paired addition mechanism (addition of neighboring numbers):

1. **Paired addition** (`binAddPaired`): given `[left][sep][right]`, produces
   `[left + right][sep][right]`. This is the central primitive.

2. **Squaring** (`binSquare`): conceptually duplicates the input as `[0][sep][n]`
   and iterates paired addition `n` times. Defined as
   `chainBinaryRepr ((decodeBinaryBlock block) ^ 2)`.

3. **Multiplication by constant** (`binMulConst c`): same mechanism — write
   constant to tape, then iterate paired addition.

Both operations share the same underlying `binAddPaired` primitive.

### Proved results (in PairedBlockArithmetic)

- `binSquare_correct` — squaring is correct
- `binSquare_ne_default` — output is non-default
- `binMulConst_eq_decomp` — decomposition through paired addition
- `tm0_binMulConst_block` — multiplication by constant is block-realizable

### Remaining sorries

- `tm0_binSquare_block` — squaring block-realizability
  (requires a TM0 machine for the decrement-and-add loop)

- `tm0_binAddPaired_block` — paired addition block-realizability
  (central primitive, used by both squaring and multiplication)
-/
