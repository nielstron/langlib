module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Automata.DeterministicPushdown.ClosureProperties.Complement
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



/-! # Deterministic Context-Free Closure Under Complement

This file is the deterministic context-free *class*-level view of complement closure.
The substantive work lives at the automaton level in
`Langlib.Automata.DeterministicPushdown.ClosureProperties.Complement`: the construction
`DPDA.complement` flips the accepting states, `DPDA.complement_isTotal` shows totality
is preserved, and `is_DCF_complement` totalizes an arbitrary final-state DPDA
(`DPDA.exists_equivalent_total`) before complementing it, so that no `DPDA.IsTotal`
hypothesis on the input is needed.

This file simply re-exports the headline `DCF_closedUnderComplement` under the
deterministic context-free class namespace.
-/

open PDA

variable {T : Type} [Fintype T]

/-- Deterministic context-free languages are closed under complement.

This is `is_DCF_closedUnderComplement`, proven at the automaton level by totalizing an
arbitrary DPDA and then complementing it. -/
public theorem DCF_closedUnderComplement :
    ClosedUnderComplement (α := T) is_DCF :=
  is_DCF_closedUnderComplement
