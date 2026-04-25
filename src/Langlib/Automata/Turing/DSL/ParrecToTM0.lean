import Mathlib
import Langlib.Automata.Turing.DSL.TM0Restrict

/-! # TM0 Re-rooting and Chain Infrastructure

This file provides infrastructure for the Partrec → TM0 compilation chain.

## Main results

### TM0 Re-rooting
- `ParrecToTM0.Rooted` — wrapper type with custom default
- `ParrecToTM0.tm0Reroot` — re-root a TM0 to start from an arbitrary state
- `ParrecToTM0.tm0Reroot_eval_dom` — re-rooting preserves halting (Dom)

### Chain Dom Preservation
- `ParrecToTM0.tm2to1_dom_general` — TM2 → TM1 preserves Dom for arbitrary initial configs
- `ParrecToTM0.tm1to0_dom_general` — TM1 → TM0 preserves Dom for arbitrary initial configs
-/

open Turing

namespace ParrecToTM0

/-! ### TM0 Re-rooting -/

/-- Wrapper type that allows re-rooting to a specified initial state. -/
@[ext]
structure Rooted (Λ : Type*) (q₀ : Λ) where
  val : Λ

instance {Λ : Type*} {q₀ : Λ} : Inhabited (Rooted Λ q₀) := ⟨⟨q₀⟩⟩

/-- Re-root a TM0 machine to start from state `q₀` instead of `default`. -/
def tm0Reroot {Γ : Type*} {Λ : Type*} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (q₀ : Λ) :
    @TM0.Machine Γ (Rooted Λ q₀) ⟨⟨q₀⟩⟩ :=
  fun ⟨q⟩ a => (M q a).map (fun (q', s) => (⟨q'⟩, s))

/-
The re-rooted TM0 respects the original via the unwrapping relation.
-/
theorem tm0Reroot_respects {Γ : Type*} {Λ : Type*} [Inhabited Λ] [Inhabited Γ]
    (M : TM0.Machine Γ Λ) (q₀ : Λ) :
    Respects
      (TM0.step M)
      (@TM0.step Γ (Rooted Λ q₀) ⟨⟨q₀⟩⟩ _ (tm0Reroot M q₀))
      (fun c₁ c₂ => c₁.q = c₂.q.val ∧ c₁.Tape = c₂.Tape) := by
  unfold TM0.step;
  unfold tm0Reroot;
  rintro ⟨ q, T ⟩ ⟨ ⟨ q' ⟩, T' ⟩ ⟨ hq, hT ⟩;
  rcases h : M q' T'.head with ( _ | ⟨ q'', s ⟩ ) <;> simp_all +decide [ Reaches₁ ];
  refine' ⟨ _, ⟨ rfl, rfl ⟩, Relation.TransGen.single ⟨ q'', s, h, rfl ⟩ ⟩

/-- Evaluation of the re-rooted TM0 starting from `q₀` preserves halting. -/
theorem tm0Reroot_eval_dom {Γ : Type*} {Λ : Type*} [Inhabited Λ] [Inhabited Γ]
    (M : TM0.Machine Γ Λ) (q₀ : Λ) (l : List Γ) :
    (eval (TM0.step M) ⟨q₀, Tape.mk₁ l⟩).Dom ↔
    (@TM0.eval Γ (Rooted Λ q₀) ⟨⟨q₀⟩⟩ _ (tm0Reroot M q₀) l).Dom := by
  simp only [TM0.eval]
  exact (tr_eval_dom (tm0Reroot_respects M q₀) ⟨rfl, rfl⟩).symm

/-! ### Chain Dom Preservation for Arbitrary Initial Configs -/

/-- TM2 → TM1 preserves Dom for arbitrary initial configs related by `TrCfg`. -/
theorem tm2to1_dom_general
    {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*}
    [DecidableEq K]
    (M : Λ → TM2.Stmt Γ Λ σ)
    (cfg₂ : TM2.Cfg Γ Λ σ)
    (cfg₁ : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ)
    (hrel : TM2to1.TrCfg cfg₂ cfg₁) :
    (eval (TM1.step (TM2to1.tr M)) cfg₁).Dom ↔
    (eval (TM2.step M) cfg₂).Dom :=
  tr_eval_dom (TM2to1.tr_respects M) hrel

/-- TM1 → TM0 preserves Dom for arbitrary initial configs. -/
theorem tm1to0_dom_general
    {Γ : Type*} {Λ : Type*} [Inhabited Λ] {σ : Type*} [Inhabited σ] [Inhabited Γ]
    (M : Λ → TM1.Stmt Γ Λ σ)
    (cfg₁ : TM1.Cfg Γ Λ σ) :
    (eval (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M cfg₁)).Dom ↔
    (eval (TM1.step M) cfg₁).Dom :=
  tr_eval_dom (TM1to0.tr_respects M) rfl

/-! ### Fintype States -/

/-- The TM1 → TM0 translation preserves support (re-exported for convenience). -/
theorem tm1to0_fintype_states
    {Γ : Type*} {Λ : Type*} [Inhabited Λ] {σ : Type*} [Inhabited σ] [Fintype σ]
    (M : Λ → TM1.Stmt Γ Λ σ) {S : Finset Λ}
    (hS : TM1.Supports M S) :
    TM0.Supports (TM1to0.tr M) ↑(TM1to0.trStmts M S) :=
  TM1to0.tr_supports M hS

/-! ### Re-rooting Support -/

/-- Embedding function for `Rooted`: wraps a value into a `Rooted`. -/
def rootedEmbFn {Λ : Type*} {q₀ : Λ} : Λ ↪ Rooted Λ q₀ :=
  ⟨fun q => ⟨q⟩, fun _ _ h => by cases h; rfl⟩

/-- If `TM0.Supports M S` and `q₀ ∈ S`, then `tm0Reroot M q₀` is supported
by the image of `S` under the `Rooted` embedding. -/
theorem tm0Reroot_supports {Γ : Type*} {Λ : Type*} [Inhabited Λ] [Inhabited Γ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S) (q₀ : Λ)
    (hq₀ : q₀ ∈ S) :
    @TM0.Supports Γ (Rooted Λ q₀) ⟨⟨q₀⟩⟩ (tm0Reroot M q₀)
      (↑(S.map (rootedEmbFn (q₀ := q₀))) : Set (Rooted Λ q₀)) := by
  refine ⟨?_, ?_⟩
  · -- default = ⟨q₀⟩ ∈ S.map rootedEmbFn
    show ⟨q₀⟩ ∈ S.map rootedEmbFn
    rw [Finset.mem_map]
    exact ⟨q₀, hq₀, rfl⟩
  · -- transitions preserve support
    intro q a q' s hstep hq
    show q' ∈ S.map rootedEmbFn
    have hq_mem : q ∈ S.map rootedEmbFn := hq
    rw [Finset.mem_map] at hq_mem ⊢
    obtain ⟨q_val, hq_val, rfl⟩ := hq_mem
    rcases q' with ⟨q'_val⟩
    simp only [tm0Reroot, Option.mem_def, Option.map_eq_some_iff] at hstep
    obtain ⟨⟨q'', s'⟩, hM, heq⟩ := hstep
    simp only [Prod.mk.injEq, Rooted.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [rootedEmbFn]
    exact ⟨q'', hS.2 hM hq_val, rfl⟩

/-- Restrict + reroot a TM0: combine re-rooting and restriction into one step.
Given `TM0.Supports M S` with `q₀ ∈ S`, produce a TM0 with `Fintype` states
that halts on `l` iff the original does when started from `q₀`. -/
noncomputable def tm0RestrictReroot {Γ : Type*} {Λ : Type*}
    [Inhabited Λ] [Inhabited Γ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S)
    (q₀ : Λ) (hq₀ : q₀ ∈ S) :
    let S' := S.map (rootedEmbFn (q₀ := q₀))
    let hS' := tm0Reroot_supports M S hS q₀ hq₀
    @TM0.Machine Γ { q : Rooted Λ q₀ // q ∈ S' } ⟨⟨⟨q₀⟩, by
      show ⟨q₀⟩ ∈ S.map rootedEmbFn
      rw [Finset.mem_map]; exact ⟨q₀, hq₀, rfl⟩⟩⟩ :=
  Turing.TM0.restrict (tm0Reroot M q₀) (S.map rootedEmbFn)
    (tm0Reroot_supports M S hS q₀ hq₀)

noncomputable def tm0RestrictReroot_fintype {Λ : Type*}
    (S : Finset Λ) (q₀ : Λ) :
    Fintype { q : Rooted Λ q₀ // q ∈ S.map (rootedEmbFn (q₀ := q₀)) } :=
  Finset.Subtype.fintype _

/-- The restrict+reroot machine halts iff the original does when started from `q₀`. -/
theorem tm0RestrictReroot_eval_dom {Γ : Type*} {Λ : Type*}
    [Inhabited Λ] [Inhabited Γ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S)
    (q₀ : Λ) (hq₀ : q₀ ∈ S) (l : List Γ) :
    (eval (TM0.step M) ⟨q₀, Tape.mk₁ l⟩).Dom ↔
    (@TM0.eval Γ { q : Rooted Λ q₀ // q ∈ S.map (rootedEmbFn (q₀ := q₀)) }
      ⟨⟨⟨q₀⟩, by show ⟨q₀⟩ ∈ S.map rootedEmbFn; rw [Finset.mem_map]; exact ⟨q₀, hq₀, rfl⟩⟩⟩
      inferInstance (tm0RestrictReroot M S hS q₀ hq₀) l).Dom := by
  rw [tm0Reroot_eval_dom M q₀ l]
  exact Turing.TM0.restrict_eval_dom_iff (tm0Reroot M q₀) _ (tm0Reroot_supports M S hS q₀ hq₀) l

end ParrecToTM0