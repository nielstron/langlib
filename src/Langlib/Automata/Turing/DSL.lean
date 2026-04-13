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
All **fully proved** (0 sorry's). See individual files for details.

### Layer 5: Compilation to TM0 — **`search_halts_tm0` PROVED** (0 sorry)
**File**: `DSL/Compile.lean`

**`search_halts_tm0`** is now fully proved (0 sorry, only standard axioms).
It shows that any language expressible as `{ w | ∃ a : α, test a w = true }`
with `Primcodable α` and `Computable₂ test` is TM0-recognizable over the
Partrec chain's internal `Fintype` alphabet.

The compilation produces a TM0 over `ChainΓ` (the internal alphabet from
`PartrecToTM2 → TM2to1 → TM1to0`). Converting to `Option T` alphabet
requires **alphabet simulation** (`tm0_alphabet_simulation`), which is a
separate, orthogonal concern (currently sorry'd).

### Layer 6: Internal TM-recognizability — **Fully proved** (0 sorry)
**File**: `DSL/InternalTM.lean`

- `search_halts_internal` — fully proved, 0 sorry
- `is_TM_internal_to_TM` — requires alphabet simulation (sorry'd)

## Sorry Summary

**Sorries in the Turing machine theory:**

| Sorry | File | Nature |
|---|---|---|
| `tm0_alphabet_simulation` | Compile.lean | TM0 alphabet conversion (standard TM theory) |
| `Computable enc` | InternalTM.lean | Computability of encoding (needed for is_TM_internal_to_TM) |
| `Computable₂ (grammarTest g)` | GrammarSearch.lean | Grammar test function computability |
| `Fintype g.nt` | GrammarToTM.lean | Finiteness of grammar nonterminals |

**Key proved results:**
- `search_halts_tm0`: **PROVED** (0 sorry, standard axioms only)
- `search_halts_internal`: **PROVED** (0 sorry)
- `is_TM_of_searchable`: **PROVED** (0 sorry)
- `code_to_tm0`: **PROVED** (0 sorry)
- `search_is_partrec`: **PROVED** (0 sorry)
-/
