module

public import Langlib.Classes.Recursive.Definition
public import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Classes.Recursive.Closure.Complement
import Langlib.Classes.Recursive.Inclusion.RecursivelyEnumerable
import Langlib.Classes.RecursivelyEnumerable.Closure.Complement
import Langlib.Utilities.ClosurePredicates.Transport
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



/-! # Strict Inclusion: Recursive ⊊ RE

This file proves that recursive languages form a strict subclass of recursively
enumerable languages.

The proof is indirect.  If every RE language over the unary alphabet were recursive,
then RE would be closed under complement: move an RE language into `Recursive`, take
the recursive complement, and use `Recursive ⊆ RE`. This contradicts RE non-closure under
complement.

## Main declarations

- `Recursive_strict_subclass_RE_unit` — strict inclusion over `Unit`.
- `Recursive_strict_subclass_RE_of_nonempty` — strict inclusion over any nonempty finite
  alphabet.
- `Recursive_subclass_RE_and_exists_strict` — class-level inclusion plus a strict
  witness alphabet.
-/

open Language

/-- Recursive languages over the unary alphabet form a strict subclass of RE. -/
theorem Recursive_strict_subclass_RE_unit :
    (Recursive : Set (Language Unit)) ⊂ (RE : Set (Language Unit)) :=
  strict_subset_of_subset_different_property
    (P := is_Recursive) (Q := is_RE)
    (fun _ hL => Recursive_subset_RE hL)
    (X := ClosedUnderComplement)
    (fun hiff => ClosedUnderComplement_of_iff hiff)
    Recursive_closedUnderComplement
    RE_notClosedUnderComplement

/-- Recursive languages over any nonempty finite alphabet form a strict subclass of RE. -/
theorem Recursive_strict_subclass_RE_of_nonempty {T : Type} [DecidableEq T] [Fintype T]
    [Nonempty T] :
    (Recursive : Set (Language T)) ⊂ (RE : Set (Language T)) :=
  strict_subset_of_subset_different_property
    (P := is_Recursive) (Q := is_RE)
    (fun _ hL => Recursive_subset_RE hL)
    (X := ClosedUnderComplement)
    (fun hiff => ClosedUnderComplement_of_iff hiff)
    Recursive_closedUnderComplement
    RE_notClosedUnderComplement_of_nonempty

/-- Recursive languages are included in RE for every finite alphabet, and the inclusion
is strict for at least one alphabet. -/
theorem Recursive_subclass_RE_and_exists_strict :
    (∀ T : Type, [DecidableEq T] → [Fintype T] →
      (Recursive : Set (Language T)) ⊆ (RE : Set (Language T))) ∧
    (∃ T : Type, (Recursive : Set (Language T)) ⊂ (RE : Set (Language T))) :=
  ⟨fun _ _ _ => Recursive_subset_RE, ⟨Unit, Recursive_strict_subclass_RE_unit⟩⟩
