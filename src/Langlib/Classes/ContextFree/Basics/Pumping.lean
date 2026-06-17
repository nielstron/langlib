module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Utilities.ListUtils
import Langlib.Classes.ContextFree.Pumping.Pumping
import Langlib.Grammars.ContextFree.MathlibCFG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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



/-! # Elementary Pumping Lemmas

This file states the context-free pumping lemma for the project's `is_CF` predicate.
`CF_pumping` transports `Language.IsContextFree.pumping` (proved in
`Pumping/Pumping.lean` via Chomsky-normal-form parse trees) across
`is_CF_iff_isContextFree`.

## Main declarations

- `CF_pumping`
-/

open List

variable {T : Type}

/-- Pumping lemma for context-free languages.  -/
public lemma CF_pumping {T : Type} {L : Language T} (cf : is_CF L) :
  ∃ n : ℕ, ∀ w ∈ L, List.length w ≥ n → (
    ∃ u v x y z : List T,
      (w = u ++ v ++ x ++ y ++ z) ∧
      (v ++ y).length > 0         ∧
      (v ++ x ++ y).length ≤ n    ∧
      (∀ i : ℕ, u ++ v ^ i ++ x ++ y ^ i ++ z ∈ L)
  ) :=
by
  obtain ⟨n, hn⟩ := Language.IsContextFree.pumping ((is_CF_iff_isContextFree).mp cf)
  refine ⟨n, ?_⟩
  intro w hw hwlen
  obtain ⟨u, v, x, y, z, hsplit, hnonempty, hbound, hpump⟩ := hn w hw hwlen
  refine ⟨u, v, x, y, z, hsplit, hnonempty, hbound, ?_⟩
  intro i
  simpa [n_times, nTimes] using hpump i
