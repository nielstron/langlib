module

public import Langlib.Examples.A2nBnPos
public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.A2nBn
import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Closure.Homomorphism
import Langlib.Classes.ContextFree.Examples.A2nBn
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



/-! # The positive `{a^(2n)b^n}` language

This file defines `{a^(2n)b^n | n >= 1}` over `Bool`, with `false = a` and
`true = b`, and proves it is context-free.
-/

open Language

public lemma quotientLeftBlock_eq_singletons_core :
    quotientLeftBlock = ({[false, false]} : Language Bool) * quotientLeftBlockCore * {[true]} := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    rw [Language.mem_mul]
    refine ⟨[false, false] ++
        (List.replicate (2 * n) false ++ List.replicate n true),
      ?_, [true], Set.mem_singleton _, ?_⟩
    · rw [Language.mem_mul]
      refine ⟨[false, false], Set.mem_singleton _, _,
        ⟨n, rfl⟩, ?_⟩
      simp
    · rw [show 2 * (n + 1) = 2 + 2 * n by omega]
      rw [show List.replicate (2 + 2 * n) false =
          [false, false] ++ List.replicate (2 * n) false by
        simp [List.replicate_add]]
      rw [List.replicate_succ']
      simp [List.append_assoc]
  · intro hw
    rw [Language.mem_mul] at hw
    rcases hw with ⟨u, hu, v, hv, rfl⟩
    rw [Language.mem_mul] at hu
    rcases hu with ⟨p, hp, q, ⟨n, hq⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hp hv
    subst hp
    subst hv
    refine ⟨n, ?_⟩
    rw [hq]
    rw [show 2 * (n + 1) = 2 + 2 * n by omega]
    simp [List.replicate_add, List.append_assoc]

public lemma CF_quotientLeftBlock : is_CF quotientLeftBlock := by
  rw [quotientLeftBlock_eq_singletons_core]
  apply CF_of_CF_c_CF
  exact ⟨CF_of_CF_c_CF _ _ ⟨is_CF_singleton [false, false], CF_quotientLeftBlockCore⟩,
    is_CF_singleton [true]⟩
