module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Automata.DeterministicPushdown.Basics.Total
public import Langlib.Automata.DeterministicPushdown.Totalization
public import Langlib.Utilities.ClosurePredicates
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



open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

namespace DPDA

/-- Construct the **complement DPDA** by replacing the set of accepting states
    with its complement. This is a syntactic operation that swaps which states
    are accepting. -/
@[expose]
public def complement (M : DPDA Q T S) : DPDA Q T S where
  initial_state := M.initial_state
  start_symbol := M.start_symbol
  final_states := M.final_statesᶜ
  transition := M.transition
  epsilon_transition := M.epsilon_transition
  no_mixed := M.no_mixed

@[simp]
theorem complement_final_states (M : DPDA Q T S) :
    M.complement.final_states = M.final_statesᶜ := rfl

@[simp]
theorem complement_transition (M : DPDA Q T S) :
    M.complement.transition = M.transition := rfl

@[simp]
theorem complement_epsilon_transition (M : DPDA Q T S) :
    M.complement.epsilon_transition = M.epsilon_transition := rfl

@[simp]
theorem complement_initial_state (M : DPDA Q T S) :
    M.complement.initial_state = M.initial_state := rfl

@[simp]
theorem complement_start_symbol (M : DPDA Q T S) :
    M.complement.start_symbol = M.start_symbol := rfl

@[simp]
theorem complement_complement (M : DPDA Q T S) :
    M.complement.complement.initial_state = M.initial_state
    ∧ M.complement.complement.start_symbol = M.start_symbol
    ∧ M.complement.complement.final_states = M.final_states
    ∧ M.complement.complement.transition = M.transition
    ∧ M.complement.complement.epsilon_transition = M.epsilon_transition := by
  simp [complement]

@[simp]
theorem complement_toPDA (M : DPDA Q T S) :
    M.complement.toPDA.initial_state = M.toPDA.initial_state := rfl

/-- The complement DPDA has the same transition functions as the original. -/
public theorem complement_toPDA_transition_fun (M : DPDA Q T S) :
    M.complement.toPDA.transition_fun = M.toPDA.transition_fun := rfl

/-- The complement DPDA has the same ε-transition functions as the original. -/
public theorem complement_toPDA_transition_fun' (M : DPDA Q T S) :
    M.complement.toPDA.transition_fun' = M.toPDA.transition_fun' := rfl

/-- The multi-step reachability relation is the same for a DPDA and its complement,
    because the step function depends only on the transitions, not the accepting states. -/
public theorem complement_toPDA_reaches (M : DPDA Q T S) (q q' : Q)
    (w : List T) (γ γ' : List S) :
    @PDA.Reaches _ _ _ _ _ _ M.complement.toPDA ⟨q, w, γ⟩ ⟨q', [], γ'⟩ ↔
    @PDA.Reaches _ _ _ _ _ _ M.toPDA ⟨q, w, γ⟩ ⟨q', [], γ'⟩ := by
  constructor
  · intro h
    exact PDA.reaches_of_same_transitions M.complement.toPDA M.toPDA
      (complement_toPDA_transition_fun M) (complement_toPDA_transition_fun' M)
      ⟨q, w, γ⟩ ⟨q', [], γ'⟩ h
  · intro h
    exact PDA.reaches_of_same_transitions M.toPDA M.complement.toPDA
      (complement_toPDA_transition_fun M).symm (complement_toPDA_transition_fun' M).symm
      ⟨q, w, γ⟩ ⟨q', [], γ'⟩ h

/-- Complementing a **total** DPDA yields a total DPDA: flipping the accepting states
    changes neither the transitions (so totality is preserved) nor whether two
    empty-input configurations agree (so acceptance consistency is preserved). -/
public theorem complement_isTotal (M : DPDA Q T S) (h : M.IsTotal) :
    M.complement.IsTotal := by
  obtain ⟨htotal, hconsistent⟩ := h
  refine ⟨fun w => ?_, fun w q₁ q₂ γ₁ γ₂ h₁ h₂ => ?_⟩
  · obtain ⟨q, γ, hreach⟩ := htotal w
    exact ⟨q, γ, (complement_toPDA_reaches M M.initial_state q w [M.start_symbol] γ).2 hreach⟩
  · rw [complement_toPDA_reaches] at h₁ h₂
    simpa using not_congr (hconsistent w q₁ q₂ γ₁ γ₂ h₁ h₂)

/-- For a **total** DPDA, the complemented DPDA accepts precisely the
    complement of the original language. -/
public theorem complement_acceptsByFinalState (M : DPDA Q T S) (h : M.IsTotal) :
    M.complement.acceptsByFinalState = (M.acceptsByFinalState)ᶜ := by
  obtain ⟨htotal, hconsistent⟩ := h
  unfold DPDA.acceptsByFinalState PDA.acceptsByFinalState
  ext w
  change (∃ q ∈ M.final_statesᶜ, ∃ γ : List S,
    @PDA.Reaches Q T S _ _ _ M.complement.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩) ↔
    ¬(∃ q ∈ M.final_states, ∃ γ : List S,
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩)
  constructor
  · rintro ⟨q, hq_not_final, γ, hreach⟩
    rw [complement_toPDA_reaches] at hreach
    rintro ⟨q', hq'_final, γ', hreach'⟩
    exact hq_not_final ((hconsistent w q q' γ γ' hreach hreach').mpr hq'_final)
  · intro h_not_accept
    obtain ⟨q, γ, hreach⟩ := htotal w
    refine ⟨q, ?_, γ, (complement_toPDA_reaches M M.initial_state q w [M.start_symbol] γ).mpr hreach⟩
    intro hq_final
    exact h_not_accept ⟨q, hq_final, γ, hreach⟩


end DPDA

variable {T : Type} [Fintype T]

/-- **Complement closure for total presentations.** If `L` is recognized by a total
    DPDA, so is `Lᶜ`: complement the total DPDA. -/
public theorem is_DCF_total_complement {L : Language T} (hL : is_DCF_total L) :
    is_DCF_total Lᶜ := by
  obtain ⟨Q, S, hQ, hS, M, htotal, hM⟩ := hL
  exact ⟨Q, S, hQ, hS, M.complement, DPDA.complement_isTotal M htotal, by
    rw [DPDA.complement_acceptsByFinalState M htotal, hM]⟩

/-- **Complement closure for deterministic context-free languages.** Every DCF `L`
    has `Lᶜ` deterministic context-free as well.  An arbitrary final-state DPDA for `L`
    need not decide every input, so the proof first totalizes it
    (`DPDA.exists_equivalent_total`) into an equivalent total DPDA and then complements
    that — no `DPDA.IsTotal` hypothesis on the input is required. -/
public theorem is_DCF_complement {L : Language T} (hL : is_DCF L) : is_DCF Lᶜ := by
  obtain ⟨Q, S, hQ, hS, M, hM⟩ := hL
  obtain ⟨Q', S', hQ', hS', M', htotal, heq⟩ := M.exists_equivalent_total
  refine ⟨Q', S', hQ', hS', M'.complement, ?_⟩
  rw [DPDA.complement_acceptsByFinalState M' htotal, heq, hM]

/-- Deterministic context-free languages are closed under complement. -/
public theorem is_DCF_closedUnderComplement :
    ClosedUnderComplement (α := T) is_DCF :=
  fun _ => is_DCF_complement
