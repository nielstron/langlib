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

@[expose] public section

/-! # Undecidability of Membership for RE Languages

This file proves that membership cannot be decided for recursively enumerable (RE)
languages in general. More precisely, there exists an RE predicate whose membership
is not computable.

The proof uses the classical halting-problem undecidability result from Mathlib:

- `ComputablePred.halting_problem_re` — the halting predicate is RE.
- `ComputablePred.halting_problem` — the halting predicate is not computable.

Together these immediately yield: **there exists an RE predicate that is not computable**,
which is the formal content of the statement "membership is undecidable for RE languages."

## Main results

- `RE_membership_undecidable` — there exists a recursively enumerable predicate that is
  not computably decidable.
- `RE_membership_undecidable'` — the halting predicate (for input `0`) is RE but not
  computably decidable.
-/

open Nat.Partrec

/-- The halting predicate (for input `0`) is RE but not computably decidable. -/
theorem RE_membership_undecidable' :
    REPred (fun c : Code => (c.eval 0).Dom) ∧
    ¬ComputablePred (fun c : Code => (c.eval 0).Dom) :=
  ⟨ComputablePred.halting_problem_re 0, ComputablePred.halting_problem 0⟩

/-- There exists a recursively enumerable predicate that is not computably decidable.

This is the formal statement of the classical result that "membership is undecidable
for RE languages": while RE languages/predicates are those for which membership can be
*confirmed* (semi-decided) by a Turing machine, there is no algorithm that can *decide*
membership (i.e., always halt with a yes/no answer) for every RE language. -/
theorem RE_membership_undecidable :
    ∃ (p : Code → Prop), REPred p ∧ ¬ComputablePred p :=
  ⟨_, RE_membership_undecidable'.1, RE_membership_undecidable'.2⟩

/-- Membership for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableMembership_undecidable :
    ¬ComputableMembership partrecCodeDomainLanguageOf := by
  intro h
  apply RE_membership_undecidable'.2
  have h_nil : ComputablePred
      (fun c : Code => ([] : List Unit) ∈ partrecCodeDomainLanguageOf c) := by
    unfold ComputableMembership at h
    rcases h with ⟨dec, hcomp⟩
    letI : DecidablePred
        (fun c : Code => ([] : List Unit) ∈ partrecCodeDomainLanguageOf c) :=
      fun c => dec (c, ([] : List Unit))
    exact ⟨inferInstance,
      hcomp.comp (Computable.pair Computable.id (Computable.const ([] : List Unit)))⟩
  exact h_nil.of_eq fun c => by
    change (c.eval 0).Dom ↔ (c.eval 0).Dom
    rfl
