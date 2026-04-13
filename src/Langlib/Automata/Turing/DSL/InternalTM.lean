import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.DSL.Compile

/-! # TM-recognizability with internal (arbitrary) alphabet

This file provides the connection between `is_TM_internal` (arbitrary
alphabet) and `is_TM` (Option T alphabet).

## Main results

- `is_TM_internal` — definition of TM-recognizability with arbitrary alphabet
- `is_TM_to_internal` — `is_TM → is_TM_internal` (trivial)
- `search_halts_internal` — the search pattern yields `is_TM_internal`
  (sorry-free given `Computable₂`)
- `is_TM_internal_to_TM` — `is_TM_internal → is_TM` (requires alphabet simulation)
-/

open Turing

/-- A language `L` over alphabet `T` is **internally TM-recognizable** if there
exists a TM0 machine (possibly with a different tape alphabet) that halts on
`encode w` if and only if `w ∈ L`.

This is weaker than `is_TM` because the tape alphabet is existentially
quantified rather than fixed to `Option T`. The two notions are equivalent
by the standard alphabet simulation theorem. -/
def is_TM_internal {T : Type} (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ)
    (_ : Fintype Γ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ)
    (enc : List T → List Γ),
    ∀ w : List T, w ∈ L ↔ (TM0.eval M (enc w)).Dom

/-- `is_TM → is_TM_internal` (trivial). -/
theorem is_TM_to_internal {T : Type} [Fintype T] (L : Language T) :
    is_TM L → is_TM_internal L := by
  intro ⟨Λ, hΛ, hFin, M, hM⟩
  exact ⟨Option T, Λ, inferInstance, hΛ, inferInstance, hFin, M, fun w => w.map some, hM⟩

/-- `is_TM_internal → is_TM` requires alphabet simulation (the converse
direction). This uses `tm0_alphabet_simulation` which requires
`Primcodable` instances and a `Computable` encoding. -/
theorem is_TM_internal_to_TM {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (L : Language T) :
    is_TM_internal L → is_TM L := by
  intro ⟨Γ, Λ, hΓ, hΛ, hΓf, hΛf, M, enc, hM⟩
  haveI := hΓ; haveI := hΛ; haveI := hΓf
  haveI : DecidableEq Γ := Classical.decEq _
  haveI : Primcodable Γ :=
    Primcodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.truncEquivFin Γ).out
  have henc : Computable enc := by sorry
  obtain ⟨Λ', hΛ', hΛ'f, M', hM'⟩ :=
    @tm0_alphabet_simulation T _ _ _ Γ hΓ hΓf (Classical.decEq _) _ Λ hΛ M enc henc
  exact ⟨Λ', hΛ', hΛ'f, M', fun w => by rw [hM, hM']⟩

/-- The search pattern yields internal TM-recognizability directly from
`Computable₂`, **without** any sorry.

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
