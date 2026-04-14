import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.DSL.Compile
import Langlib.Automata.Turing.DSL.AlphabetSim

/-! # TM-recognizability with internal (arbitrary) alphabet

This file provides the connection between `is_TM_internal` (arbitrary
alphabet) and `is_TM` (Option (T ⊕ Γ) alphabet).

## Main results

- `is_TM_internal` — definition of TM-recognizability with arbitrary alphabet
- `is_TM_to_internal` — `is_TM → is_TM_internal` (trivial)
- `search_halts_internal` — the search pattern yields `is_TM_internal`

## Warning: `is_TM_internal` is vacuously true

**Important**: `is_TM_internal` as defined below is vacuously true for
*any* language, because the encoding `enc : List T → List Γ` is allowed
to be an arbitrary (non-computable) function. By choosing `enc` to map
words in `L` to a halting input and words outside `L` to a non-halting
input, any language satisfies `is_TM_internal`.

The theorems that produce `is_TM_internal` (such as `re_implies_tm_internal`
and `grammar_language_is_TM_internal_fintype`) are still meaningful because
their *proofs* construct specific, computable encodings via the compilation
chain. However, the conclusion `is_TM_internal L` does not capture this
computability information.

A meaningful strengthening would require the encoding to be `Computable`,
which would make `is_TM_internal → is_TM` provable via alphabet simulation.
This refactor is left for future work.

For the direction `RE ⊆ TM`, the encoding conversion (from the internal
alphabet to `Option (T ⊕ Γ)`) remains the key unsolved formalization
challenge. The mathematical content is fully captured by `search_halts_tm0`
and `code_to_tm0` in `Compile.lean`.
-/

open Turing

/-- A language `L` over alphabet `T` is **internally TM-recognizable** if there
exists a TM0 machine (possibly with a different tape alphabet) that halts on
`encode w` if and only if `w ∈ L`.

**Warning**: This notion is vacuously true for all languages, because
`enc` is allowed to be non-computable. See the module docstring for details.
The meaningful content is in the compilation chain that produces specific,
computable encodings. -/
def is_TM_internal {T : Type} (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ)
    (_ : Fintype Γ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ)
    (enc : List T → List Γ),
    ∀ w : List T, w ∈ L ↔ (TM0.eval M (enc w)).Dom

/-- `is_TM → is_TM_internal` (trivial).

With the generalized `is_TM`, we take the tape alphabet `Option (T ⊕ Γ)` and
encoding `w.map (fun x => some (Sum.inl x))` directly. -/
theorem is_TM_to_internal {T : Type} [Fintype T] (L : Language T) :
    is_TM L → is_TM_internal L := by
  intro ⟨Γ, hΓf, Λ, hΛ, hFin, M, hM⟩
  exact ⟨Option (T ⊕ Γ), Λ, inferInstance, hΛ, inferInstance, hFin, M,
    fun w => w.map (fun x => some (Sum.inl x)), hM⟩

/- The converse `is_TM_internal → is_TM` is NOT provable as stated, because
`is_TM_internal` allows non-computable encodings `enc`. With a non-computable
`enc`, the TM over `Option (T ⊕ Γ)` cannot compute `enc(w)` from the input
`w.map (fun x => some (Sum.inl x))`.

For the specific encodings produced by the compilation chain (which ARE
computable), the conversion is possible in principle via alphabet simulation,
but formalizing this requires carrying computability information through
the compilation chain. -/

/-- The search pattern yields internal TM-recognizability directly from
`Computable₂`

This is a wrapper around `search_halts_tm0` from `Compile.lean`. -/
theorem search_halts_internal {T : Type}
    {α : Type} [Primcodable α] [Primcodable T]
    (test : α → List T → Bool) (hc : Computable₂ test) :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ) (_ : Fintype Γ)
      (M : TM0.Machine Γ Λ) (enc : List T → List Γ),
      ∀ w : List T,
        (∃ a : α, test a w = true) ↔ (TM0.eval M (enc w)).Dom := by
  obtain ⟨Γ, hΓ, hΓf, Λ, hΛ, M, enc, hM⟩ := search_halts_tm0 test hc
  exact ⟨Γ, Λ, hΓ, hΛ, hΓf, M, enc, hM⟩
