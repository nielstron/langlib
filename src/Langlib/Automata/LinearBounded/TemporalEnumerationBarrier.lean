module

public import Langlib.Automata.LinearBounded.SavitchRecomputationBarrier
import Mathlib.Tactic

@[expose]
public section

/-!
# Temporal enumeration before a deterministic first halt

Suppose a deterministic finite-state orbit first reaches a designated halting state (or halting
set) after `steps` transitions.  If each state emits at most one item and every item is emitted
strictly before that first halt, then there are at most `steps` distinct items.  The first-hit
orbit contains `steps + 1` distinct states, so the item type has cardinality strictly below the
state type.

The optional-valued map `emit : State → Option Item` makes the one-item-per-state premise
explicit while allowing states that emit nothing.  Different states may emit the same item, and
the halt-time emission is ignored (so it may duplicate an item already emitted earlier).  No
nonemptiness or lower cardinality assumptions are imposed.  In particular, an empty item type and
zero halt time are included; an empty state type simply cannot supply the required `source` state.

This is a barrier to a **literal temporal enumeration** in which every distinct item must occur
as the single optional output of a pre-halt state.  It does not cover representations in which
one state names a collection of items, and it is not a deterministic-space lower bound.
-/

namespace TemporalEnumerationBarrier

open SavitchRecomputationBarrier

/-! ## Counting optional emissions -/

/-- A time strictly before `steps` at which the orbit emits an item. -/
private abbrev EmittingTime {State Item : Type*}
    (step : State → State) (source : State) (emit : State → Option Item)
    (steps : ℕ) :=
  { time : Fin steps //
    (emit (orbit step source time.val)).isSome = true }

/-- Recover the item emitted at an emitting time. -/
private def EmittingTime.item {State Item : Type*}
    {step : State → State} {source : State} {emit : State → Option Item}
    {steps : ℕ}
    (time : EmittingTime step source emit steps) : Item :=
  (emit (orbit step source time.val)).get time.property

private theorem EmittingTime.item_eq_of_emit_eq_some
    {State Item : Type*}
    {step : State → State} {source : State} {emit : State → Option Item}
    {steps : ℕ} (time : Fin steps) (item : Item)
    (hemit : emit (orbit step source time.val) = some item) :
    EmittingTime.item
      (⟨time, by simp [hemit]⟩ : EmittingTime step source emit steps) = item := by
  simp [EmittingTime.item, hemit]

/-- If every item occurs as an optional output at some time strictly before `steps`, there are at
most `steps` distinct items.

This counting fact does not require the state type to be finite or the orbit to avoid repeats.
It includes `steps = 0`: in that case the coverage premise forces the finite item type to be
empty. -/
public theorem card_items_le_steps_of_emitted_before
    {State Item : Type*} [Fintype Item]
    (step : State → State) (source : State) (emit : State → Option Item)
    (steps : ℕ)
    (hcoverage : ∀ item : Item, ∃ k < steps,
      emit (orbit step source k) = some item) :
    Fintype.card Item ≤ steps := by
  have hsurjective : Function.Surjective
      (@EmittingTime.item State Item step source emit steps) := by
    intro item
    obtain ⟨k, hk, hemit⟩ := hcoverage item
    let time : Fin steps := ⟨k, hk⟩
    refine ⟨⟨time, ?_⟩, ?_⟩
    · simp [time, hemit]
    · exact EmittingTime.item_eq_of_emit_eq_some time item hemit
  calc
    Fintype.card Item ≤ Fintype.card (EmittingTime step source emit steps) :=
      Fintype.card_le_of_surjective _ hsurjective
    _ ≤ Fintype.card (Fin steps) := Fintype.card_subtype_le _
    _ = steps := Fintype.card_fin steps

/-! ## Combining enumeration with a deterministic first halt -/

/-- If `steps` is the first time a deterministic finite-state orbit satisfies `halting`, and
every item is emitted strictly earlier, then one additional state beyond the number of items is
available.  This is the additive form of the strict cardinality barrier.

The predicate formulation permits an arbitrary set of halting states; its members need not be
terminal or fixed points. -/
public theorem card_items_add_one_le_card_of_firstSatisfying_emission
    {State Item : Type*} [Fintype State] [Fintype Item]
    (step : State → State) (source : State) (halting : State → Prop)
    (emit : State → Option Item) {steps : ℕ}
    (hhalt : halting (orbit step source steps))
    (hfirst : ∀ k < steps, ¬ halting (orbit step source k))
    (hcoverage : ∀ item : Item, ∃ k < steps,
      emit (orbit step source k) = some item) :
    Fintype.card Item + 1 ≤ Fintype.card State := by
  exact (Nat.add_le_add_right
    (card_items_le_steps_of_emitted_before
      step source emit steps hcoverage) 1).trans
    (Nat.succ_le_iff.mpr
      (firstSatisfying_steps_lt_card
        step source halting hhalt hfirst))

/-- Under the same first-halting and coverage premises, the item type is strictly smaller than
the finite deterministic state type. -/
public theorem card_items_lt_card_of_firstSatisfying_emission
    {State Item : Type*} [Fintype State] [Fintype Item]
    (step : State → State) (source : State) (halting : State → Prop)
    (emit : State → Option Item) {steps : ℕ}
    (hhalt : halting (orbit step source steps))
    (hfirst : ∀ k < steps, ¬ halting (orbit step source k))
    (hcoverage : ∀ item : Item, ∃ k < steps,
      emit (orbit step source k) = some item) :
    Fintype.card Item < Fintype.card State := by
  exact Nat.lt_of_succ_le
    (card_items_add_one_le_card_of_firstSatisfying_emission
      step source halting emit hhalt hfirst hcoverage)

/-- Designated-target specialization of the additive temporal-enumeration barrier.  The target
need not be terminal or a fixed point; only its first occurrence on this orbit matters. -/
public theorem card_items_add_one_le_card_of_firstHit_emission
    {State Item : Type*} [Fintype State] [Fintype Item]
    (step : State → State) (source target : State)
    (emit : State → Option Item) {steps : ℕ}
    (hhit : orbit step source steps = target)
    (hfirst : ∀ k < steps, orbit step source k ≠ target)
    (hcoverage : ∀ item : Item, ∃ k < steps,
      emit (orbit step source k) = some item) :
    Fintype.card Item + 1 ≤ Fintype.card State := by
  exact card_items_add_one_le_card_of_firstSatisfying_emission
    step source (fun state ↦ state = target) emit hhit hfirst hcoverage

/-- If every item is emitted before the first visit to a designated target, then the item type
is strictly smaller than the finite state type. -/
public theorem card_items_lt_card_of_firstHit_emission
    {State Item : Type*} [Fintype State] [Fintype Item]
    (step : State → State) (source target : State)
    (emit : State → Option Item) {steps : ℕ}
    (hhit : orbit step source steps = target)
    (hfirst : ∀ k < steps, orbit step source k ≠ target)
    (hcoverage : ∀ item : Item, ∃ k < steps,
      emit (orbit step source k) = some item) :
    Fintype.card Item < Fintype.card State := by
  exact Nat.lt_of_succ_le
    (card_items_add_one_le_card_of_firstHit_emission
      step source target emit hhit hfirst hcoverage)

end TemporalEnumerationBarrier

end
