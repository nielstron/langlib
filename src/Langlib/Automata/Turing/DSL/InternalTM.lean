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
- `is_TM_internal_to_TM` — `is_TM_internal → is_TM` (requires alphabet simulation)
-/

open Turing

/-- A language `L` over alphabet `T` is **internally TM-recognizable** if there
exists a TM0 machine (possibly with a different tape alphabet) that halts on
`encode w` if and only if `w ∈ L`.

This is weaker than `is_TM` because the tape alphabet is existentially
quantified rather than fixed to `Option (T ⊕ Γ)`. The two notions are equivalent
by the standard alphabet simulation theorem. -/
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

/-- `is_TM_internal → is_TM` requires alphabet simulation (the converse
direction).

With the generalized `is_TM` (allowing auxiliary tape symbols), this is
simpler than before: we use `tm0_alphabet_simulation` to get a TM over
`Option T`, then lift to `Option (T ⊕ Empty)` using alphabet simulation.

**Note**: The `Computable enc` obligation is still sorry'd; this is the same
fundamental difficulty as in the old definition. -/
theorem is_TM_internal_to_TM {T : Type} [DecidableEq T] [Fintype T]
    (L : Language T) :
    is_TM_internal L → is_TM L := by
  intro ⟨Γ₀, Λ, hΓ₀, hΛ, hΓ₀f, hΛf, M, enc, hM⟩
  haveI := hΓ₀; haveI := hΛ; haveI := hΓ₀f; haveI := hΛf
  -- Still requires alphabet simulation + encoding conversion (sorry'd as before)
  sorry

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
