module

public import Mathlib.Computability.Language
public import Mathlib.Computability.PostTuringMachine
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



/-! # Equivalence of Unrestricted Grammars and Turing Machines

This file defines the grammar construction for simulating TM0 machines, and states
the equivalence between unrestricted (Type-0) grammars and Turing machines.

The correctness proofs and the main equivalence theorem are in `TMtoGrammarHelpers.lean`.

## Main definitions

- `is_TM`: A language is TM-recognizable if there exists a finite-state
  Turing machine (using Mathlib's `Turing.TM0` model) that halts on input
  `w` iff `w ∈ L`.
-/
open Turing

/-! ### Definition of TM-Recognizability -/

/-- A language `L` over finite input alphabet `T` is **TM-recognizable** if
there exists a finite work alphabet `Γ` and a finite-state Turing machine
(in Mathlib's `Turing.TM0` model) over tape alphabet `Option (T ⊕ Γ)` that
halts on input `w` if and only if `w ∈ L`.

The tape alphabet is `Option (T ⊕ Γ)` where:
- `none` represents the blank symbol
- `some (Sum.inl t)` represents an input symbol `t : T`
- `some (Sum.inr γ)` represents a work symbol `γ : Γ`

The input word `w : List T` is written on the tape by the fixed inclusion
`T ↪ T ⊕ Γ`, producing `w.map (fun t => some (Sum.inl t))`.  The recognizer
may choose only the finite work alphabet and the machine, not an arbitrary
preprocessing map on input symbols. -/
@[expose]
public def is_TM {T : Type} [Fintype T] (L : Language T) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ)
    (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : Turing.TM0.Machine (Option (T ⊕ Γ)) Λ),
    ∀ w : List T,
      w ∈ L ↔ (Turing.TM0.eval M (w.map (fun t => some (Sum.inl t)))).Dom

@[expose]
public def TM {T : Type} [Fintype T] : Set (Language T) := setOf is_TM
