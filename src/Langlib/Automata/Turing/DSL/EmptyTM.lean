import Mathlib
import Langlib.Automata.Turing.Definition

/-! # TM recognizability for languages over Empty

When `T = Empty`, every language over `T` is trivially TM-recognizable,
since `List Empty = {[]}` and any language is either `∅` or `{[]}`.
-/

open Turing

/-- Every list of Empty elements is the empty list. -/
theorem List.eq_nil_of_empty (l : List Empty) : l = [] := by
  cases l with
  | nil => rfl
  | cons a _ => exact a.elim

/-- A TM that always halts (transition function returns none). -/
noncomputable def alwaysHaltTM (Γ : Type) [Inhabited Γ] :
    @TM0.Machine Γ Unit ⟨()⟩ :=
  fun _ _ => none

/-
The always-halt TM halts on any input.
-/
theorem alwaysHaltTM_halts (Γ : Type) [Inhabited Γ] (l : List Γ) :
    (@TM0.eval Γ Unit ⟨()⟩ _ (alwaysHaltTM Γ) l).Dom := by
  constructor;
  swap;
  constructor;
  all_goals unfold TM0.step at *; simp_all +decide [ alwaysHaltTM ];
  convert Part.dom_iff_mem.mpr _;
  unfold WellFounded.fixF; aesop;

/-- A TM that loops forever (always moves right). -/
noncomputable def neverHaltTM (Γ : Type) [Inhabited Γ] :
    @TM0.Machine Γ Unit ⟨()⟩ :=
  fun _ _ => some ((), TM0.Stmt.move Dir.right)

/-
The never-halt TM diverges on any input.
-/
theorem neverHaltTM_diverges (Γ : Type) [Inhabited Γ] (l : List Γ) :
    ¬ (@TM0.eval Γ Unit ⟨()⟩ _ (neverHaltTM Γ) l).Dom := by
  simp [Turing.TM0.eval];
  rw [ Turing.eval ];
  unfold PFun.fix;
  simp +decide [ Part.assert ];
  intro x;
  exact absurd x ( by exact fun h => by exact h.recOn ( by tauto ) )

/-- Any language over the empty type is TM-recognizable. -/
theorem is_TM_of_empty (L : Language Empty) : is_TM L := by
  by_cases h : ([] : List Empty) ∈ L
  · -- L = {[]}: use the always-halt TM with Γ = Empty
    exact ⟨Empty, inferInstance, Unit, ⟨()⟩, inferInstance,
      alwaysHaltTM (Option Empty), Empty.elim, fun w => by
      rw [show w = [] from List.eq_nil_of_empty w]
      exact ⟨fun _ => alwaysHaltTM_halts _ _, fun _ => h⟩⟩
  · -- L = ∅: use the never-halt TM with Γ = Empty
    exact ⟨Empty, inferInstance, Unit, ⟨()⟩, inferInstance,
      neverHaltTM (Option Empty), Empty.elim, fun w => by
      rw [show w = [] from List.eq_nil_of_empty w]
      exact ⟨fun hmem => absurd hmem h,
        fun hdom => absurd hdom (neverHaltTM_diverges _ _)⟩⟩
