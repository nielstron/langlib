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



/-! # Undecidability of Emptiness for RE Languages

This file proves that emptiness cannot be decided for recursively enumerable (RE)
languages. More precisely, the predicate "the partial function computed by code `c`
has empty domain" is not computable.

The proof uses **Rice's theorem** (`ComputablePred.rice`): any computable semantic
property of programs must be trivial (satisfied by all partial-recursive functions
or by none). We exhibit two partial-recursive functions that separate the property —
the everywhere-undefined function `fun _ => Part.none` (empty domain) and the constant
zero function `pure 0` (total) — to derive a contradiction.

## Main results

- `RE_emptiness_undecidable` — the predicate "code `c` halts on no input" is not
  computably decidable.
-/

open Nat.Partrec

/-- **Emptiness is undecidable for RE languages.**

There is no algorithm that, given a code `c` for a partial-recursive function,
decides whether `c` halts on no input (i.e., whether the domain of `c.eval` is empty).

*Proof.* Apply Rice's theorem to the semantic property
`C = {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom}`. The everywhere-undefined function
`fun _ ↦ Part.none` is partial-recursive (`Nat.Partrec.none`) and lies in `C`, while
the constant zero function `pure 0` is partial-recursive (`Nat.Partrec.zero`) and does
not lie in `C`. Hence `C` is a non-trivial semantic property, so by Rice's theorem it
is not computably decidable. -/
theorem RE_emptiness_undecidable :
    ¬ComputablePred (fun c : Code => ∀ n, ¬(c.eval n).Dom) := by
  intro h
  -- Apply Rice's theorem to the set of functions with empty domain
  have rice := ComputablePred.rice {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom}
  -- Convert our hypothesis to the form expected by Rice
  have h1 : ComputablePred (fun c : Code => c.eval ∈ {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom}) := by
    convert h using 1
  -- The constant zero function is total, so it is NOT in the empty-domain set
  have pure_zero_not_empty :
      (pure 0 : ℕ →. ℕ) ∉ {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom} :=
    fun hf => hf 0 trivial
  -- The everywhere-undefined function IS in the empty-domain set
  have none_empty :
      (fun (_ : ℕ) => (Part.none : Part ℕ)) ∈ {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom} :=
    fun _ h => h
  -- Rice's theorem: if the property were decidable, every partrec function in the
  -- set would force every other partrec function into the set.
  -- In particular, `fun _ => Part.none ∈ C` would imply `pure 0 ∈ C`, contradiction.
  exact pure_zero_not_empty (rice h1 Nat.Partrec.none Nat.Partrec.zero none_empty)

/-- Emptiness for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableEmptiness_undecidable :
    ¬ComputableEmptiness partrecCodeDomainLanguageOf := by
  intro h
  apply RE_emptiness_undecidable
  unfold ComputableEmptiness at h
  exact h.of_eq fun c => partrecCodeDomainLanguage_empty_iff c
