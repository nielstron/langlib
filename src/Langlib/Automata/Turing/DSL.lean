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
All **fully proved** (0 sorry's) except `code_to_tm0_fintype`.

### Layer 5: Compilation to TM0 — **`search_halts_tm0` PROVED** (0 sorry)
**File**: `DSL/Compile.lean`

**`search_halts_tm0`** is fully proved (0 sorry, only standard axioms).
It shows that any language expressible as `{ w | ∃ a : α, test a w = true }`
with `Primcodable α` and `Computable₂ test` is TM0-recognizable over the
Partrec chain's internal `Fintype` alphabet.

**`search_halts_tm0_fintype`** is the strengthened version that also provides
`Fintype` on states. It depends on `code_to_tm0_fintype` (currently sorry'd).

### Layer 6: Internal TM-recognizability
**File**: `DSL/InternalTM.lean`

- `search_halts_internal` — fully proved, 0 sorry
- `is_TM_internal_to_TM` — requires alphabet simulation (sorry'd)

### TM0 Support Infrastructure
**File**: `DSL/ParrecToTM0.lean`

- `tm0Reroot_supports` — PROVED: re-rooting preserves support
- `tm0RestrictReroot` — restrict + reroot combined
- `tm0RestrictReroot_eval_dom` — PROVED: halting equivalence for restrict+reroot

### Support Chain
**File**: `DSL/ParrecChain.lean`

- `chainSuppTM2/TM1/TM0` — finite support sets for the chain
- `code_to_tm0_fintype` — sorry'd (see hurdles below)

## Sorry Summary

**Sorries in the Turing machine theory:**

| Sorry | File | Nature |
|---|---|---|
| `code_to_tm0_fintype` | ParrecChain.lean | **Inhabited instance mismatch** (see below) |
| `tm0_alphabet_simulation` | Compile.lean | TM0 alphabet conversion (standard TM theory) |
| `Computable enc` | InternalTM.lean | Computability of encoding |
| `Computable₂ (grammarTest g)` | GrammarSearch.lean | Grammar test function computability |

## Hurdles for `code_to_tm0_fintype`

The main obstacle is a **Lean `Inhabited` instance mismatch**:

1. `PartrecToTM2.tr_supports c k` produces `TM2.Supports` with a
   *code-dependent* `Inhabited` instance: `⟨trNormal c k⟩`.
2. `TM1to0.instInhabitedΛ'` defines `default = (some (M default), default)`,
   so the default for `ChainΛ_TM0` depends on the upstream `Inhabited`.
3. These instances are **not definitionally equal**, causing `exact` to fail.

This is NOT a mathematical obstacle — the support sets are the same.
But it requires careful instance management in Lean.

**Key proved results:**
- `search_halts_tm0`: **PROVED** (0 sorry, standard axioms only)
- `search_halts_internal`: **PROVED** (0 sorry)
- `is_TM_of_searchable`: **PROVED** (0 sorry)
- `code_to_tm0`: **PROVED** (0 sorry)
- `search_is_partrec`: **PROVED** (0 sorry)
- `tm0Reroot_supports`: **PROVED** (re-rooting preserves support)
- `tm0RestrictReroot_eval_dom`: **PROVED** (restrict+reroot halting)
-/
