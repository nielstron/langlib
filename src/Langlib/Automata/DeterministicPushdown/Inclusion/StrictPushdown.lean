module

public import Langlib.Automata.DeterministicPushdown.Definition
import Langlib.Automata.Pushdown.Equivalence.ContextFree
import Langlib.Classes.DeterministicContextFree.Inclusion.StrictContextFree
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

/-! # DPDAs are a strict subclass of PDAs

This file transfers the class-level strictness theorem `DCF ⊊ CF` to the
corresponding automaton classes.
-/

/-- DPDA final-state languages are a strict subclass of PDA languages over a
three-symbol alphabet. -/
theorem DPDA_strict_subclass_PDA :
    (DPDA.Class : Set (Language (Fin 3))) ⊂ PDA.Class := by
  rw [← CF_eq_PDA_Class]
  change (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3)))
  exact DCF_strict_subclass_CF
