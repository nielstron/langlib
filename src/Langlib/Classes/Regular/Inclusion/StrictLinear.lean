module

public import Langlib.Classes.Linear.Definition
public import Langlib.Classes.Regular.Definition
public import Mathlib.Computability.DFA
import Langlib.Automata.FiniteState.Equivalence.Regular
public import Langlib.Classes.Linear.Examples.AnBn
import Langlib.Classes.Linear.Basics.Map
import Langlib.Classes.Regular.Examples.AnBn
import Langlib.Classes.Regular.Closure.Bijection
import Langlib.Classes.Regular.Inclusion.Linear
import Langlib.Utilities.Tactics
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
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ENatToNat
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
@[expose]
public section



/-! # RG ⊊ Linear

This file uses the example language `{aⁿbⁿ}` to show that regular languages
form a strict subclass of linear languages.

## Main results

- `exists_Linear_not_regular` — There exists a linear language over `Bool` that is not regular.
- `exists_Linear_not_regular_of_nontrivial` — There exists a linear nonregular language over
  any nontrivial alphabet.
- `RG_strict_subclass_Linear` — Right-regular languages form a strict subclass of linear languages.
- `RG_strict_subclass_Linear_of_card` — The same strict inclusion over every finite alphabet
  with at least 2 elements.
-/

open Language List Relation Classical

noncomputable section

variable {T : Type}

/-- There exists a linear language that is not regular. -/
theorem exists_Linear_not_regular : ∃ L : Language Bool, is_Linear L ∧ ¬ L.IsRegular :=
  ⟨anbn, anbn_is_Linear, anbn_not_isRegular⟩

public lemma map_anbn_is_Linear (f : Bool → T) (_hf : Function.Injective f) :
    is_Linear (Language.map f anbn) :=
  is_Linear_map anbn_is_Linear f

/-- There exists a linear nonregular language over any nontrivial alphabet. -/
theorem exists_Linear_not_regular_of_nontrivial {T : Type} [Nontrivial T] :
    ∃ L : Language T, is_Linear L ∧ ¬ L.IsRegular := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  exact ⟨Language.map f anbn, map_anbn_is_Linear f hf, map_anbn_not_isRegular hf⟩

/-- Right-regular languages form a strict subclass of linear languages over any nontrivial alphabet. -/
theorem RG_strict_subclass_Linear [Nontrivial T] :
    (RG : Set (Language T)) ⊂ (Linear : Set (Language T)) := by
  refine ⟨RG_subclass_Linear, ?_⟩
  intro hLinearsubsetRG
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> try rfl
    · simp [f] at hxy; exact False.elim (hab hxy)
    · simp [f] at hxy; exact False.elim (hab hxy.symm)
  have hLinear : Language.map f anbn ∈ (Linear : Set (Language T)) :=
    map_anbn_is_Linear f hf
  have hRG : Language.map f anbn ∈ (RG : Set (Language T)) := hLinearsubsetRG hLinear
  have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
  exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)

/-- Right-regular languages form a strict subclass of linear languages over every finite
alphabet with at least 2 elements. -/
public theorem RG_strict_subclass_Linear_of_card {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (RG : Set (Language T)) ⊂ (Linear : Set (Language T)) := by
  letI : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide) hT)
  exact RG_strict_subclass_Linear

end
