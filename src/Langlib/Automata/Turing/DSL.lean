import Langlib.Automata.Turing.DSL.Enumeration
import Langlib.Automata.Turing.DSL.SearchProc
import Langlib.Automata.Turing.DSL.TM0Restrict
import Langlib.Automata.Turing.DSL.AlphabetSim
import Langlib.Automata.Turing.DSL.EmptyTM
import Langlib.Automata.Turing.DSL.ParrecToTM0
import Langlib.Automata.Turing.DSL.ParrecChain
import Langlib.Automata.Turing.DSL.Compile
import Langlib.Automata.Turing.DSL.InternalTM

/-! # Composable TM Generators / Transformers — DSL Overview

This module collects the layers of the DSL for describing
TM-recognizable languages via composable search procedures.

## Architecture

### Layer 1–4: Enumeration, Search, TM0 Infrastructure, Partrec Chain

### Layer 5: Compilation to TM0
**File**: `DSL/Compile.lean`

**`search_halts_tm0`**
It shows that any language expressible as `{ w | ∃ a : α, test a w = true }`
with `Primcodable α` and `Computable₂ test` is TM0-recognizable over the
Partrec chain's internal `Fintype` alphabet.

**`search_halts_tm0_fintype`** is the strengthened version that also provides
`Fintype` on states. It depends on `code_to_tm0_fintype`

### Layer 6: Internal TM-recognizability
**File**: `DSL/InternalTM.lean`


### TM0 Support Infrastructure
**File**: `DSL/ParrecToTM0.lean`

- `tm0Reroot_supports` — PROVED: re-rooting preserves support
- `tm0RestrictReroot` — restrict + reroot combined
- `tm0RestrictReroot_eval_dom` — PROVED: halting equivalence for restrict+reroot

### Support Chain
**File**: `DSL/ParrecChain.lean`

- `chainSuppTM2/TM1/TM0` — finite support sets for the chain
- `code_to_tm0_fintype`

-/
