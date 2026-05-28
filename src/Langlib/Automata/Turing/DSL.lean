module

public import Langlib.Automata.Turing.DSL.Enumeration
public import Langlib.Automata.Turing.DSL.SearchProcedure
public import Langlib.Automata.Turing.DSL.TM0FiniteSupport
public import Langlib.Automata.Turing.DSL.EmptyAlphabetTM
public import Langlib.Automata.Turing.DSL.TM0ChainInfrastructure
public import Langlib.Automata.Turing.DSL.PartrecCodeToTM0
public import Langlib.Automata.Turing.DSL.ListEncodeCode
public import Langlib.Automata.Turing.DSL.SearchProcToTM0
public import Langlib.Automata.Turing.DSL.CodeToTMDirect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-! # Composable TM Generators / Transformers — DSL Overview

This module collects the layers of the DSL for describing
TM-recognizable languages via composable search procedures.

## Architecture

### Layer 1–4: Enumeration, Search, TM0 Infrastructure, Partrec Chain

### Layer 5: Search compilation to TM0
**File**: `DSL/SearchProcToTM0.lean`

**`search_halts_tm0`**
It shows that any language expressible as `{ w | ∃ a : α, test a w = true }`
with `Primcodable α` and `Computable₂ test` is TM0-recognizable over the
Partrec chain's internal `Fintype` alphabet.

**`search_halts_tm0_fintype`** is the strengthened version that also provides
`Fintype` on states. It depends on `code_to_tm0_fintype`

### TM0 Support Infrastructure
**File**: `DSL/TM0ChainInfrastructure.lean`

- `tm0Reroot_supports` — PROVED: re-rooting preserves support
- `tm0RestrictReroot` — restrict + reroot combined
- `tm0RestrictReroot_eval_dom` — PROVED: halting equivalence for restrict+reroot

### Support Chain
**File**: `DSL/PartrecCodeToTM0.lean`

- `chainSuppTM2/TM1/TM0` — finite support sets for the chain
- `code_to_tm0_fintype`

-/
