module

public import Langlib.Examples.A2nBn
public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.AnBn
public import Langlib.Utilities.Homomorphism
import Langlib.Classes.ContextFree.Closure.Homomorphism
import Langlib.Classes.ContextFree.Examples.AnBn
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



/-! # The `{a^(2n)b^n}` language

This file defines `{a^(2n)b^n | n in N}` over `Bool`, with `false = a` and
`true = b`, and proves it is context-free.
-/

open Language

/-- Multiplying singleton-word languages along a word gives the flattened homomorphic image. -/
private lemma mem_prod_singleton_words_iff {α β : Type} (h : α → List β) :
    ∀ w : List α, ∀ u : List β,
      u ∈ (w.map fun x => ({h x} : Language β)).prod ↔ u = w.flatMap h
  | [], u => by
      change u ∈ ({[]} : Language β) ↔ u = []
      rfl
  | x :: xs, u => by
      constructor
      · intro hu
        rw [show (List.map (fun x => ({h x} : Language β)) (x :: xs)).prod =
            ({h x} : Language β) * (List.map (fun x => ({h x} : Language β)) xs).prod
          by rfl] at hu
        rw [Language.mul_def] at hu
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        have hu₂' := (mem_prod_singleton_words_iff h xs u₂).1 hu₂
        have hu₁' : u₁ = h x := by simpa using hu₁
        simp [hu₁', hu₂']
      · intro hu
        subst hu
        rw [show (List.map (fun x => ({h x} : Language β)) (x :: xs)).prod =
            ({h x} : Language β) * (List.map (fun x => ({h x} : Language β)) xs).prod
          by rfl]
        rw [Language.mul_def]
        refine ⟨h x, Set.mem_singleton _, xs.flatMap h, ?_, rfl⟩
        exact (mem_prod_singleton_words_iff h xs _).2 rfl

private lemma flatten_replicate_pair_false (n : ℕ) :
    (List.replicate n [false, false]).flatten = List.replicate (2 * n) false := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, ih]
      rw [show 2 * (n + 1) = 2 + 2 * n by omega]
      simp [List.replicate_add]

private lemma flatMap_left_hom_anbn (n : ℕ) :
    (List.replicate n false ++ List.replicate n true).flatMap
        (fun b => if b = true then [true] else [false, false]) =
      List.replicate (2 * n) false ++ List.replicate n true := by
  simp [List.flatMap_append, List.flatMap_replicate, flatten_replicate_pair_false]

public lemma quotientLeftBlockCore_eq_hom :
    quotientLeftBlockCore =
      anbn.homomorphicImage (fun b => if b = true then [true] else [false, false]) := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨List.replicate n false ++ List.replicate n true, ⟨n, rfl⟩, ?_⟩
    exact
      (mem_prod_singleton_words_iff
        (fun b => if b = true then [true] else [false, false]) _ _).2
        (flatMap_left_hom_anbn n).symm
  · rintro ⟨src, ⟨n, hsrc⟩, hwprod⟩
    refine ⟨n, ?_⟩
    have hw :=
      (mem_prod_singleton_words_iff
        (fun b => if b = true then [true] else [false, false]) src w).1 hwprod
    rw [hw, hsrc, flatMap_left_hom_anbn]

public lemma CF_quotientLeftBlockCore : is_CF quotientLeftBlockCore := by
  rw [quotientLeftBlockCore_eq_hom]
  exact CF_closed_under_homomorphism anbn
    (fun b => if b = true then [true] else [false, false]) anbn_is_CF
