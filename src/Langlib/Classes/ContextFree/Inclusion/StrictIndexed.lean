module

public import Langlib.Classes.Indexed.Definition
public import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Closure.Bijection
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Inclusion.Indexed
import Langlib.Classes.Indexed.Closure.Injection
import Langlib.Classes.Indexed.Examples.AnBnCn
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
@[expose]
public section



/-! # Strict Inclusion: CF ⊊ Indexed

This file proves that the class of indexed languages strictly contains the class of
context-free languages, by exhibiting a witness: the language `{aⁿbⁿcⁿ | n ∈ ℕ}`
is indexed but not context-free.

The indexed grammar uses a stack-bottom marker to ensure that each nonterminal
consumes exactly as many flags as were pushed.

## Main declarations

- `CF_strict_subclass_Indexed` — `CF ⊂ Indexed`
-/

/-- CF ⊊ Indexed: context-free languages form a strict subclass of indexed languages. -/
theorem CF_subclass_Indexed_and_exists_strict :
    (∀ (T : Type) (L : Language T), is_CF L → is_Indexed L) ∧
    (∃ (T : Type) (L : Language T), is_Indexed L ∧ ¬ is_CF L) :=
  ⟨fun _ _ => is_Indexed_of_is_CF, ⟨Fin 3, lang_eq_eq, is_Indexed_lang_eq_eq, notCF_lang_eq_eq⟩⟩

/-- For any finite alphabet with at least `3` symbols, context-free languages form a strict
subclass of indexed languages. -/
theorem CF_strict_subclass_Indexed {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (CF : Set (Language T)) ⊂ (Indexed : Set (Language T)) := by
  let π : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let e : Fin 3 ↪ T := (Fin.castLEEmb hT).trans π.symm.toEmbedding
  refine ⟨CF_subclass_Indexed, ?_⟩
  intro hIndexedSubsetCF
  have hIndexed : is_Indexed (Language.map e lang_eq_eq) :=
    Indexed_of_map_injective_Indexed e.injective lang_eq_eq is_Indexed_lang_eq_eq
  have hCF : is_CF (Language.map e lang_eq_eq) :=
    hIndexedSubsetCF (a := Language.map e lang_eq_eq) hIndexed
  exact notCF_lang_eq_eq (CF_of_map_injective_CF_rev e.injective lang_eq_eq hCF)
