module

public import Langlib.Automata.DeterministicPushdown.Definition
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



/-! # Total Deterministic Pushdown Automata

This file isolates the notion of a **total** DPDA.  A DPDA need not read all of its
input: it can reject by getting stuck or diverge in an infinite chain of ε-moves.  A
*total* DPDA always reaches an empty-input configuration on every input and its
reachable empty-input configurations agree on acceptance, so it decides every input.

This is the target normal form produced by the totalization construction in
`Langlib.Automata.DeterministicPushdown.Totalization` and the hypothesis under which
`DPDA.complement` recognizes the complement language
(`Langlib.Automata.DeterministicPushdown.ClosureProperties.Complement`).
-/

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A DPDA is **total** if it decides every input:
    1. **Totality**: for each word `w`, the DPDA can reach some configuration with
       empty input from the initial configuration.
    2. **Acceptance consistency**: all reachable empty-input configurations for a
       given word `w` agree on whether the state is accepting or not. -/
@[expose]
public def IsTotal (M : DPDA Q T S) : Prop :=
  (∀ w : List T, ∃ q γ, @PDA.Reaches Q T S _ _ _ M.toPDA
    ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩) ∧
  (∀ (w : List T) (q₁ q₂ : Q) (γ₁ γ₂ : List S),
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q₁, [], γ₁⟩ →
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q₂, [], γ₂⟩ →
    (q₁ ∈ M.final_states ↔ q₂ ∈ M.final_states))

end DPDA

variable {T : Type} [Fintype T]

/-- A language represented by a **total** DPDA: a DPDA that decides every input
    (`DPDA.IsTotal`) and accepts the language by final state.  This is the target normal
    form used by deterministic context-free complement closure. -/
@[expose]
public def is_DCF_total (L : Language T) : Prop :=
  ∃ (Q S : Type) (_ : Fintype Q) (_ : Fintype S) (M : DPDA Q T S),
    M.IsTotal ∧ M.acceptsByFinalState = L
