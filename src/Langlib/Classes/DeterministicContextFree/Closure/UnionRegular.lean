module

public import Langlib.Classes.DeterministicContextFree.Definition
public import Mathlib.Computability.DFA
import Langlib.Classes.DeterministicContextFree.Closure.Complement
import Langlib.Classes.DeterministicContextFree.Closure.IntersectionRegular
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



/-! # Deterministic Context-Free Closure Under Union With Regular Languages

This is a derived closure fact, not full union closure for deterministic
context-free languages.  The proof uses De Morgan together with complement
closure and closure under intersection with regular languages.
-/

variable {T : Type} [Fintype T]

omit [Fintype T] in
private theorem language_union_eq_compl_inter_compl (L R : Language T) :
    L + R = (Lᶜ ⊓ Rᶜ)ᶜ := by
  ext w
  simp only [Language.add_def]
  change w ∈ L ⊔ R ↔ w ∈ (Lᶜ ⊓ Rᶜ)ᶜ
  rw [show (L ⊔ R : Set (List T)) = Set.union L R by rfl]
  change (w ∈ L ∨ w ∈ R) ↔ ¬ (w ∉ L ∧ w ∉ R)
  tauto

/-- Union of a DCF language with a regular language is DCF. -/
theorem DCF_union_regular (L R : Language T)
    (hL : is_DCF L) (hR : R.IsRegular) :
    is_DCF (L + R) := by
  rw [language_union_eq_compl_inter_compl]
  exact DCF_closedUnderComplement (Lᶜ ⊓ Rᶜ)
    (DCF_inter_regular Lᶜ Rᶜ (DCF_closedUnderComplement L hL) hR.compl)

/-- Union of a regular language with a DCF language is DCF. -/
theorem DCF_regular_union (R L : Language T)
    (hR : R.IsRegular) (hL : is_DCF L) :
    is_DCF (R + L) := by
  simpa [add_comm] using DCF_union_regular L R hL hR
