module

public import Langlib.Classes.RecursivelyEnumerable.Decidability.Helper
public import Langlib.Utilities.ComputabilityPredicates
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



/-! # Undecidability of Universality for RE Languages

This file proves that universality cannot be decided for recursively enumerable (RE)
languages. More precisely, the predicate "the partial function computed by code `c`
halts on every input" is not computable.

The proof mirrors that of emptiness undecidability, again via **Rice's theorem**
(`ComputablePred.rice`). The semantic property `C = {f | ∀ n, (f n).Dom}` is
non-trivial: the constant zero function `pure 0` is total (lies in `C`) while the
everywhere-undefined function `fun _ ↦ Part.none` is not (lies outside `C`).

## Main results

- `RE_universality_undecidable` — the predicate "code `c` halts on every input" is
  not computably decidable.
-/

open Nat.Partrec

/-- **Universality is undecidable for RE languages.**

There is no algorithm that, given a code `c` for a partial-recursive function,
decides whether `c` halts on every input (i.e., whether the domain of `c.eval`
is all of `ℕ`).

*Proof.* Apply Rice's theorem to the semantic property
`C = {f : ℕ →. ℕ | ∀ n, (f n).Dom}`. The constant zero function `pure 0` is
partial-recursive and lies in `C`, while the everywhere-undefined function
`fun _ ↦ Part.none` is partial-recursive and does not. Hence `C` is non-trivial
and therefore not computably decidable. -/
theorem RE_universality_undecidable :
    ¬ComputablePred (fun c : Code => ∀ n, (c.eval n).Dom) := by
  intro h
  have rice := ComputablePred.rice {f : ℕ →. ℕ | ∀ n, (f n).Dom}
  have h1 : ComputablePred (fun c : Code => c.eval ∈ {f : ℕ →. ℕ | ∀ n, (f n).Dom}) := by
    convert h using 1
  -- The everywhere-undefined function is NOT total
  have none_not_total :
      (fun (_ : ℕ) => (Part.none : Part ℕ)) ∉ {f : ℕ →. ℕ | ∀ n, (f n).Dom} :=
    fun h => h 0
  -- The constant zero function IS total
  -- Rice gives: pure 0 ∈ C  ⟹  (fun _ => Part.none) ∈ C, contradiction.
  exact none_not_total (rice h1 Nat.Partrec.zero Nat.Partrec.none (fun _ => trivial))

/-- Universality for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableUniversality_undecidable :
    ¬ComputableUniversality RE partrecCodeDomainLanguageOf := by
  intro h
  apply RE_universality_undecidable
  exact h.2.2.of_eq fun c => partrecCodeDomainLanguage_universal_iff c
