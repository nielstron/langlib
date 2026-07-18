module

public import Langlib.Automata.LinearBounded.SuccinctDiamondScheduleCapacity
public import Langlib.Automata.LinearBounded.TemporalEnumerationBarrier
import Mathlib.Tactic

@[expose]
public section

/-!
# A temporal barrier to enumerating every succinct-diamond schedule

The static capacity theorem for the succinct diamond family says that its valid target-reaching
schedules cannot all be stored injectively in one fixed-linear row.  Here we combine that fact
with the deterministic first-halt orbit theorem.  At the same explicit width, a deterministic
finite-state computation whose **complete state** injects into such a row cannot emit every valid
schedule, one schedule per pre-halt state, before first halting.

The state encoding premise deliberately covers finite control, head position, and all other
retained data; none may be hidden outside the row.  Emissions may be skipped or repeated.  The
result only excludes literal one-item-per-state enumeration.  A state may still summarize many
schedules, and no language-class or deterministic-space lower bound is claimed.
-/

namespace SuccinctDiamondTemporalEnumeration

open SavitchRecomputationBarrier
open SuccinctDiamondScheduleCapacity
open TemporalEnumerationBarrier

/-- At the explicit capacity-obstruction width, a deterministic first-halting orbit whose whole
state injects into a fixed-linear row cannot emit every valid target-reaching bounded-replay
schedule before it halts.

No nonemptiness or positive-factor assumption is imposed.  In the degenerate zero-width cases,
the row state space is still the singleton empty function, whereas the diamond has two schedules.
-/
public theorem no_firstSatisfying_emits_all_targetSchedules_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ)
    {State : Type*} [Fintype State]
    (encodeState : State →
      Fin (factor * obstructionWidth A factor) → A)
    (hencode : Function.Injective encodeState)
    (step : State → State) (initial : State) (halting : State → Prop)
    (emit : State →
      Option (TargetBoundedReplaySchedule (2 ^ obstructionWidth A factor)))
    (steps : ℕ) :
    ¬ (halting (orbit step initial steps) ∧
      (∀ k < steps, ¬ halting (orbit step initial k)) ∧
      ∀ schedule : TargetBoundedReplaySchedule (2 ^ obstructionWidth A factor),
        ∃ k < steps, emit (orbit step initial k) = some schedule) := by
  classical
  rintro ⟨hhalt, hfirst, hcoverage⟩
  let Item := TargetBoundedReplaySchedule (2 ^ obstructionWidth A factor)
  letI : Fintype Item := Fintype.ofFinite Item
  have hitems_lt_states : Fintype.card Item < Fintype.card State :=
    card_items_lt_card_of_firstSatisfying_emission
      step initial halting emit hhalt hfirst hcoverage
  have hstates_le_rows :
      Fintype.card State ≤
        Fintype.card (Fin (factor * obstructionWidth A factor) → A) :=
    Fintype.card_le_of_injective encodeState hencode
  have hrows_lt_items :
      Fintype.card (Fin (factor * obstructionWidth A factor) → A) <
        Fintype.card Item := by
    have hcapacity := rowCapacity_lt_completePathSchedules A factor
    have hitems : Fintype.card Item = 2 ^ (2 ^ obstructionWidth A factor) := by
      simpa only [Item, Nat.card_eq_fintype_card] using
        card_targetBoundedReplaySchedules (obstructionWidth A factor)
    simpa only [Fintype.card_fun, Fintype.card_fin, hitems] using hcapacity
  exact (Nat.not_lt_of_ge hstates_le_rows)
    (hrows_lt_items.trans hitems_lt_states)

/-- Designated first-target form of the same obstruction.  The target need not be terminal or a
fixed point; it only has to occur for the first time at `steps`. -/
public theorem no_firstHit_emits_all_targetSchedules_fixedLinear
    (A : Type*) [Fintype A] (factor : ℕ)
    {State : Type*} [Fintype State]
    (encodeState : State →
      Fin (factor * obstructionWidth A factor) → A)
    (hencode : Function.Injective encodeState)
    (step : State → State) (initial target : State)
    (emit : State →
      Option (TargetBoundedReplaySchedule (2 ^ obstructionWidth A factor)))
    (steps : ℕ) :
    ¬ (orbit step initial steps = target ∧
      (∀ k < steps, orbit step initial k ≠ target) ∧
      ∀ schedule : TargetBoundedReplaySchedule (2 ^ obstructionWidth A factor),
        ∃ k < steps, emit (orbit step initial k) = some schedule) := by
  simpa only using
    no_firstSatisfying_emits_all_targetSchedules_fixedLinear
      A factor encodeState hencode step initial (fun state ↦ state = target) emit steps

end SuccinctDiamondTemporalEnumeration

end
