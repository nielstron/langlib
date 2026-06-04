module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Grammars.ContextFree.MathlibCFG
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



/-! # Context-Free Closure Under String Homomorphism

This file proves that context-free languages are closed under string homomorphism
and epsilon-free string homomorphism.

## Main declarations

- `CF_closed_under_homomorphism` : CFLs are closed under string homomorphism.
- `CF_closed_under_epsfree_homomorphism` : CFLs are closed under ε-free string homomorphism.
-/


/-- Singleton word languages are context-free. -/
public lemma is_CF_singleton (w : List β) : is_CF ({w} : Language β) := by
  rw [is_CF_iff_isContextFree]
  exact isContextFree_singleton w

/-- The class of context-free languages is closed under string homomorphism.

Given a context-free language `L` over alphabet `α` and a string homomorphism `h : α → List β`,
the image `{h(w) | w ∈ L}` is also context-free.

**Proof sketch:** A string homomorphism is a special case of substitution where each symbol `a`
is replaced by the singleton language `{h(a)}`. Since every singleton language is context-free
and CFLs are closed under substitution (`CF_of_subst_CF`), the result follows. -/
public theorem CF_closed_under_homomorphism (L : Language α) (h : α → List β)
    (hL : is_CF L) : is_CF (L.homomorphicImage h) := by
  exact CF_of_subst_CF L (fun a => {h a}) hL (fun a => is_CF_singleton (h a))

/-- The class of context-free languages is closed under ε-free string homomorphism.

This is a direct corollary of `CF_closed_under_homomorphism`, since every ε-free
string homomorphism is in particular a string homomorphism. -/
theorem CF_closed_under_epsfree_homomorphism (L : Language α) (h : α → List β)
    (hL : is_CF L) (_heps : IsEpsFreeHomomorphism h) :
    is_CF (L.homomorphicImage h) := by
  exact CF_closed_under_homomorphism L h hL

/-- The class of context-free languages is closed under string homomorphism. -/
theorem CF_closedUnderHomomorphism : ClosedUnderHomomorphism is_CF :=
  fun L h hL => CF_closed_under_homomorphism L h hL

/-- The class of context-free languages is closed under ε-free string homomorphism. -/
theorem CF_closedUnderEpsFreeHomomorphism : ClosedUnderEpsFreeHomomorphism is_CF :=
  fun L h heps hL => CF_closed_under_epsfree_homomorphism L h hL heps
