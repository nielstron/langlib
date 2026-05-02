import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep

/-! # Increment-After-Separator Machine

`decAfterSep` is block-realizable. The only consumer of this file is the
paired-side composition in `PairedBlockArithmetic`; the concrete machine proof
is postponed at this theorem boundary, matching `IncBeforeSepMachine`.
-/

open Turing PartrecToTM2 TM2to1

theorem tm0_decAfterSep_block : TM0RealizesBlock ChainΓ decAfterSep := by
  sorry
