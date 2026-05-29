module

public import Langlib.Automata.DeterministicPushdown.Totalization.Saturation
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



/-! # Regular Epsilon Analysis for DPDA Totalization

The totalizer needs finite, stack-regular lookahead for two semantic questions:

* Does the forced epsilon phase from `(q, γ)` reach a stable configuration?
* If the input is already exhausted at `(q, γ)`, does the epsilon closure encounter
  an accepting state?

This file packages the finite analysis data.  The remaining existence theorem is
provided by the pushdown-system saturation construction: every finite DPDA has
such an analysis.
-/

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A finite regular analysis of the epsilon-only behavior of a DPDA. -/
public structure RegularEpsilonAnalysis (M : DPDA Q T S) where
  StopState : Q → Type
  stopDecidableEq : ∀ q, DecidableEq (StopState q)
  stopFintype : ∀ q, Fintype (StopState q)
  stopDFA : ∀ q, DFA S (StopState q)
  stop_correct :
    ∀ q γ, (stopDFA q).evalFrom (stopDFA q).start γ ∈ (stopDFA q).accept ↔
      ∃ c', M.EpsilonStopsAt (q, γ) c'
  AcceptState : Q → Type
  acceptDecidableEq : ∀ q, DecidableEq (AcceptState q)
  acceptFintype : ∀ q, Fintype (AcceptState q)
  acceptDFA : ∀ q, DFA S (AcceptState q)
  accept_correct :
    ∀ q γ, (acceptDFA q).evalFrom (acceptDFA q).start γ ∈ (acceptDFA q).accept ↔
      ∃ q' γ', M.EpsilonReaches (q, γ) (q', γ') ∧ q' ∈ M.final_states

attribute [instance] RegularEpsilonAnalysis.stopFintype
attribute [instance] RegularEpsilonAnalysis.stopDecidableEq
attribute [instance] RegularEpsilonAnalysis.acceptFintype
attribute [instance] RegularEpsilonAnalysis.acceptDecidableEq

/-- The semantic epsilon-analysis existence theorem needed by the finite totalizer. -/
@[expose]
public def HasRegularEpsilonAnalysis (M : DPDA Q T S) : Prop :=
  Nonempty M.RegularEpsilonAnalysis

noncomputable section

/-- The saturation construction supplies the finite regular epsilon analysis used
by the totalizer.  For each control state `q`, the DFA state is the current set of
P-automaton states reachable after reading the stack prefix. -/
@[expose]
public def regularEpsilonAnalysisOfSaturation (M : DPDA Q T S) :
    M.RegularEpsilonAnalysis where
  StopState := fun _ => Set (PAutState Q)
  stopDecidableEq := fun _ => by
    classical
    infer_instance
  stopFintype := fun _ => by
    classical
    infer_instance
  stopDFA := fun q => stopSaturationDFA M q
  stop_correct := by
    intro q γ
    exact stopSaturationDFA_correct M q γ
  AcceptState := fun _ => Set (PAutState Q)
  acceptDecidableEq := fun _ => by
    classical
    infer_instance
  acceptFintype := fun _ => by
    classical
    infer_instance
  acceptDFA := fun q => finalSaturationDFA M q
  accept_correct := by
    intro q γ
    exact finalSaturationDFA_correct M q γ

/-- Every finite DPDA has a regular epsilon analysis. -/
public theorem hasRegularEpsilonAnalysis (M : DPDA Q T S) :
    M.HasRegularEpsilonAnalysis :=
  ⟨regularEpsilonAnalysisOfSaturation M⟩

end

end DPDA
