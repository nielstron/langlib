module

public import Langlib.Automata.Turing.Definition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
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

/-! # TM recognizability for languages over Empty

When `T = Empty`, every language over `T` is trivially TM-recognizable,
since `List Empty = {[]}` and any language is either `∅` or `{[]}`.

## Key results

- `alwaysHaltTM_halts`: the trivial halting TM halts on every input.
- `neverHaltTM_diverges`: the trivial moving TM never halts.
- `is_TM_of_empty`: every language over `Empty` is TM-recognizable.
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
  · -- L = {[]}: use the always-halt TM with no work symbols.
    exact ⟨Empty, inferInstance, Unit, ⟨()⟩, inferInstance,
      alwaysHaltTM (Option (Empty ⊕ Empty)), fun w => by
      rw [show w = [] from List.eq_nil_of_empty w]
      exact ⟨fun _ => alwaysHaltTM_halts _ _, fun _ => h⟩⟩
  · -- L = ∅: use the never-halt TM with no work symbols.
    exact ⟨Empty, inferInstance, Unit, ⟨()⟩, inferInstance,
      neverHaltTM (Option (Empty ⊕ Empty)), fun w => by
      rw [show w = [] from List.eq_nil_of_empty w]
      exact ⟨fun hmem => absurd hmem h,
        fun hdom => absurd hdom (neverHaltTM_diverges _ _)⟩⟩
