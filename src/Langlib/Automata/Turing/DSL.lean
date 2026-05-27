import Langlib.Automata.Turing.DSL.Enumeration
import Langlib.Automata.Turing.DSL.SearchProcedure
import Langlib.Automata.Turing.DSL.TM0FiniteSupport
import Langlib.Automata.Turing.DSL.EmptyAlphabetTM
import Langlib.Automata.Turing.DSL.TM0ChainInfrastructure
import Langlib.Automata.Turing.DSL.PartrecCodeToTM0
import Langlib.Automata.Turing.DSL.ListEncodeCode
import Langlib.Automata.Turing.DSL.SearchProcToTM0
import Langlib.Automata.Turing.DSL.CodeToTMDirect

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
