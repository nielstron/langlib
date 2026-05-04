import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep
import Langlib.Automata.Turing.DSL.BinaryArithmeticSep

/-! # Increment after separator, by decomposition

This file intentionally does not define a bespoke "scan to separator, then
successor" machine. The implementation path for `incAfterSep` is the
decomposition in `SplitAtSep`:

1. reverse the whole default-delimited block,
2. reverse the prefix before `chainConsBottom`,
3. run the separator-parameterized binary successor before `chainConsBottom`,
4. reverse the prefix before `chainConsBottom`,
5. reverse the whole block back.

The extensional bridge is `incAfterSep_eq_decomp_of_right_no_sep`.
-/

open Turing PartrecToTM2 TM2to1

/-- Successor before the paired-block separator is just the existing
separator-parameterized binary successor machine. -/
theorem tm0_incBeforeSep_blockSep :
    TM0RealizesBlockSep ChainΓ chainConsBottom binSucc :=
  tm0_binSucc_blockSep (sep := chainConsBottom) (by decide) (by decide)
