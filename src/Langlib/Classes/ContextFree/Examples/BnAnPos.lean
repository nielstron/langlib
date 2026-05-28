module

public import Langlib.Examples.BnAnPos
public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.BnAn
public import Mathlib.Data.Matrix.Mul
import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Closure.Homomorphism
import Langlib.Classes.ContextFree.Examples.BnAn
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

/-! # The positive `{b^n a^n}` language

This file defines `{b^n a^n | n >= 1}` over `Bool`, with `false = a` and
`true = b`, and proves it is context-free.
-/

open Language

lemma quotientRightBlock_eq_singletons_core :
    quotientRightBlock = ({[true]} : Language Bool) * quotientRightBlockCore * {[false]} := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    rw [Language.mem_mul]
    refine ⟨[true] ++ (List.replicate n true ++ List.replicate n false),
      ?_, [false], Set.mem_singleton _, ?_⟩
    · rw [Language.mem_mul]
      refine ⟨[true], Set.mem_singleton _, _,
        ⟨n, rfl⟩, ?_⟩
      simp
    · rw [List.replicate_succ, List.replicate_succ']
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
    rw [List.replicate_succ, List.replicate_succ']
    simp [List.append_assoc]

lemma CF_quotientRightBlock : is_CF quotientRightBlock := by
  rw [quotientRightBlock_eq_singletons_core]
  apply CF_of_CF_c_CF
  exact ⟨CF_of_CF_c_CF _ _ ⟨is_CF_singleton [true], CF_quotientRightBlockCore⟩,
    is_CF_singleton [false]⟩
