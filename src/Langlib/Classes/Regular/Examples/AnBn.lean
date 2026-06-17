module

public import Langlib.Examples.AnBn
public import Mathlib.Computability.MyhillNerode
import Langlib.Classes.Regular.Closure.Bijection
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



/-! # `a^n b^n` is not regular

This file proves that the language `{aⁿbⁿ | n ∈ ℕ}` (encoded with `false` = a,
`true` = b) is not regular, using the Myhill–Nerode theorem: it is shown to have
infinitely many distinct left quotients, hence is not regular.

## Main declarations

- `anbn_not_isRegular` — Proof that `anbn` is not regular.
- `map_anbn_not_isRegular` — Injective alphabet maps preserve the nonregularity of `anbn`.
-/

open Language List

/-- Left quotient of `anbn` by `replicate k false` contains `replicate k true`. -/
public lemma anbn_leftQuotient_replicate_false (k : ℕ) :
    List.replicate k true ∈ anbn.leftQuotient (List.replicate k false) := by
  show List.replicate k false ++ List.replicate k true ∈ anbn
  exact ⟨k, rfl⟩

/-- Left quotient of `anbn` by `replicate k false` does NOT contain `replicate j true`
    when `j ≠ k`. -/
public lemma anbn_leftQuotient_replicate_false_ne {k j : ℕ} (hjk : j ≠ k) :
    List.replicate j true ∉ anbn.leftQuotient (List.replicate k false) := by
  show ¬(List.replicate k false ++ List.replicate j true ∈ anbn)
  intro ⟨n, hn⟩
  have := congr_arg ( fun x : List Bool => x.count false ) hn ; norm_num at this;
  simp_all +decide [ List.count_replicate ]

/-- The left quotients of `anbn` indexed by `replicate k false` are pairwise distinct. -/
public lemma anbn_leftQuotient_injective :
    Function.Injective (fun k : ℕ => anbn.leftQuotient (List.replicate k false)) := by
  intro k₁ k₂ h
  by_contra hne
  have hmem := anbn_leftQuotient_replicate_false k₁
  have : anbn.leftQuotient (List.replicate k₁ false) = anbn.leftQuotient (List.replicate k₂ false) := h
  rw [this] at hmem
  exact anbn_leftQuotient_replicate_false_ne hne hmem

/-- The range of left quotients of `anbn` is infinite. -/
public lemma anbn_leftQuotient_range_infinite :
    ¬ (Set.range anbn.leftQuotient).Finite := by
  intro hfin
  have hsub : Set.range (fun k : ℕ => anbn.leftQuotient (List.replicate k false)) ⊆
      Set.range anbn.leftQuotient := by
    rintro _ ⟨k, rfl⟩
    exact ⟨List.replicate k false, rfl⟩
  exact Set.infinite_range_of_injective anbn_leftQuotient_injective (hfin.subset hsub)

/-- The language `{aⁿbⁿ}` is not regular. -/
public theorem anbn_not_isRegular : ¬ anbn.IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  exact anbn_leftQuotient_range_infinite

/-- Injective alphabet maps preserve the nonregularity of the `anbn` witness. -/
public theorem map_anbn_not_isRegular {T : Type*} {f : Bool → T} (hf : Function.Injective f) :
    ¬ (Language.map f anbn).IsRegular := by
  intro h
  exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf h)
