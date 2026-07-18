module

public import Langlib.Automata.LinearBounded.BoundedCrossingProfiles
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

@[expose]
public section

/-!
# Cardinality of bounded crossing profiles

The finite-state construction for uniformly bounded crossing sequences uses profiles whose
length is at most a fixed bound.  This file records the exact number of profiles and delayed
scan states.  The formulas hold for every finite state and tape-symbol type, including empty
types and bound zero.
-/

namespace LBA.BoundedCrossing

universe u v

variable {Gamma : Type u} {State : Type v}

namespace Profile

/-- The exact profile count, indexed directly by the possible profile lengths. -/
theorem card_fin [Fintype State] (bound : Nat) :
    Fintype.card (Profile State bound) =
      ∑ length : Fin (bound + 1), Fintype.card State ^ length.val := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro length _
  exact card_vector length.val

/-- The exact profile count as a finite geometric sum over all lengths at most `bound`. -/
theorem card [Fintype State] (bound : Nat) :
    Fintype.card (Profile State bound) =
      ∑ length ∈ Finset.range (bound + 1), Fintype.card State ^ length := by
  rw [card_fin, Fin.sum_univ_eq_sum_range]

@[simp] theorem card_zero [Fintype State] :
    Fintype.card (Profile State 0) = 1 := by
  calc
    Fintype.card (Profile State 0) =
        ∑ length ∈ Finset.range (0 + 1), Fintype.card State ^ length := card 0
    _ = 1 := by simp

end Profile

/-- `ScanState` consists of one `before` state, one `first` state per tape symbol, and a pending
state carrying a tape symbol, a crossing profile, and a terminal-event bit. -/
private def scanStateEquiv (Gamma : Type u) (State : Type v) (bound : Nat) :
    ScanState Gamma State bound ≃
      Unit ⊕ (Gamma ⊕ (Gamma × Profile State bound × Bool)) where
  toFun
    | .before => .inl ()
    | .first symbol => .inr (.inl symbol)
    | .pending symbol profile seenTerminal =>
        .inr (.inr (symbol, profile, seenTerminal))
  invFun
    | .inl () => .before
    | .inr (.inl symbol) => .first symbol
    | .inr (.inr (symbol, profile, seenTerminal)) =>
        .pending symbol profile seenTerminal
  left_inv state := by cases state <;> rfl
  right_inv state := by
    rcases state with _ | symbol | ⟨symbol, profile, seenTerminal⟩ <;> rfl

/-- Exact count of delayed scan states in terms of the profile count. -/
theorem card_scanState [Fintype Gamma] [Fintype State] (bound : Nat) :
    Fintype.card (ScanState Gamma State bound) =
      1 + Fintype.card Gamma +
        (2 : Nat) * Fintype.card Gamma * Fintype.card (Profile State bound) := by
  rw [Fintype.card_congr (scanStateEquiv Gamma State bound)]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod,
    Fintype.card_bool]
  ring

/-- Exact count of delayed scan states, with the bounded-profile count expanded. -/
theorem card_scanState_expanded [Fintype Gamma] [Fintype State] (bound : Nat) :
    Fintype.card (ScanState Gamma State bound) =
      1 + Fintype.card Gamma +
        (2 : Nat) * Fintype.card Gamma *
          (∑ length ∈ Finset.range (bound + 1), Fintype.card State ^ length) := by
  rw [card_scanState, Profile.card]

@[simp] theorem card_scanState_zero [Fintype Gamma] [Fintype State] :
    Fintype.card (ScanState Gamma State 0) =
      1 + (3 : Nat) * Fintype.card Gamma := by
  rw [card_scanState, Profile.card_zero]
  ring

end LBA.BoundedCrossing

end
