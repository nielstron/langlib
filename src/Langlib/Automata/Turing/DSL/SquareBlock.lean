import Langlib.Automata.Turing.DSL.ChainEncodeDecomp

/-! # Binary Squaring — Standalone Reference

This file re-exports the copier + multiplier decomposition of binary
squaring from `ChainEncodeDecomp.lean`. The decomposition is:

1. **Copier** (`binDup`): duplicates the binary block as a paired
   encoding `(n, n)` separated by `pairSep`.

2. **Multiplier** (`binMulPaired`): takes a paired encoding `(a, b)`
   and produces `chainBinaryRepr (a * b)`.

3. **Composition**: `binSquare = binMulPaired ∘ binDup`
   (`binSquare_eq_comp`), so block-realizability of `binSquare` follows
   from `tm0RealizesBlock_comp` once both components are proved
   block-realizable.

### Proved results (in ChainEncodeDecomp)

- `pairSep_ne_default` — separator is non-default
- `chainBinaryRepr_ne_pairSep` — binary cells ≠ separator
- `binDup_ne_default` — copier output is non-default
- `binMulPaired_ne_default` — multiplier output is non-default
- `decodePairFirst_binPairBlock` — pair decoding first component
- `decodePairSecond_binPairBlock` — pair decoding second component
- `binSquare_eq_comp` — composition identity
- `tm0_binSquare_block` — squaring is block-realizable (via composition)

### Remaining sorries

- `tm0_binDup_block` — copier block-realizability
  (requires constructing a TM0 copier machine with marker-based
  cell-by-cell duplication)

- `tm0_binMulPaired_block` — multiplier block-realizability
  (requires constructing a TM0 multiplier using schoolbook repeated
  addition with binary decrement as loop control)
-/
