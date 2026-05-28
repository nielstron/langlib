module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.DeterministicContextFree.Totalization.Definition
import Langlib.Automata.DeterministicPushdown.ClosureProperties.Complement
import Langlib.Classes.DeterministicContextFree.Totalization.Presentation
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

/-! # Deterministic Context-Free Closure Under Complement

This file lifts the DPDA complement construction to the deterministic context-free
language level.  The totalization construction first replaces an arbitrary
final-state DPDA by an equivalent DPDA that decides every input, and the
automaton-level complement construction is then applied to that deciding DPDA.
-/

open PDA

variable {T : Type} [Fintype T]

/-- Complement closure for deterministic context-free languages with a deciding DPDA
presentation. -/
theorem is_DCF_decider_complement {L : Language T} (hL : is_DCF_decider L) :
    is_DCF_decider Lᶜ := by
  obtain ⟨Q, S, hQ, hS, M, hdec, hM⟩ := hL
  refine ⟨Q, S, hQ, hS, M.complement, ?_, ?_⟩
  · unfold DPDA.DecidesEveryInput at hdec ⊢
    constructor
    · intro w
      obtain ⟨q, γ, hreach⟩ := hdec.1 w
      exact ⟨q, γ, (DPDA.complement_toPDA_reaches M M.initial_state q w [M.start_symbol] γ).2 hreach⟩
    · intro w q₁ q₂ γ₁ γ₂ h₁ h₂
      rw [DPDA.complement_toPDA_reaches] at h₁
      rw [DPDA.complement_toPDA_reaches] at h₂
      simpa using not_congr (hdec.2 w q₁ q₂ γ₁ γ₂ h₁ h₂)
  · rw [DPDA.complement_acceptsByFinalState M hdec, hM]

/-- The deciding-DPDA presentation class is closed under complement. -/
theorem DCF_decider_closedUnderComplement :
    ClosedUnderComplement (α := T) is_DCF_decider :=
  fun _ => is_DCF_decider_complement

/-- If a language has a deciding-DPDA presentation, then its complement is a DCF. -/
theorem is_DCF_complement_of_is_DCF_decider {L : Language T} (hL : is_DCF_decider L) :
    is_DCF Lᶜ :=
  is_DCF_of_is_DCF_decider (is_DCF_decider_complement hL)

/-- Once arbitrary DPDAs are totalized, DCFs are closed under complement. -/
theorem DCF_closedUnderComplement_of_decider_presentations
    (htotal : EveryDCFHasDeciderPresentation T) :
    ClosedUnderComplement (α := T) is_DCF := by
  intro L hL
  exact is_DCF_complement_of_is_DCF_decider (htotal L hL)

/-- Deterministic context-free languages are closed under complement. -/
theorem DCF_closedUnderComplement :
    ClosedUnderComplement (α := T) is_DCF :=
  DCF_closedUnderComplement_of_decider_presentations
    everyDCFHasDeciderPresentation
