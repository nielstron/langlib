module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Grammars.ContextFree.EquivMathlibCFG
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



/-! # Context-Free Closure Under Union

This file derives closure under union from closure under substitution.

## Main declarations

- `CF_of_CF_u_CF`
-/

variable {T : Type}

/-- The class of context-free languages is closed under union. -/
public theorem CF_of_CF_u_CF (L₁ : Language T) (L₂ : Language T) :
    is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ + L₂) := by
  classical
  rintro ⟨h₁, h₂⟩
  let f : Bool → Language T := fun b => if b then L₂ else L₁
  have hsubst : is_CF (({[false], [true]} : Language Bool).subst f) := by
    apply CF_of_subst_CF ({[false], [true]} : Language Bool) f
    · exact (is_CF_iff_isContextFree).mpr isContextFree_pair_bool
    · intro b
      cases b with
      | false => simpa [f]
      | true => simpa [f]
  simpa [f] using (Language.subst_singletons_eq_add (f := f) ▸ hsubst)

/-- The class of context-free languages is closed under union. -/
theorem CF_closedUnderUnion : ClosedUnderUnion (α := T) is_CF :=
  fun L₁ L₂ h₁ h₂ => CF_of_CF_u_CF L₁ L₂ ⟨h₁, h₂⟩
