module

public import Langlib.Automata.LinearBounded.BoundedNondeterminism
public import Langlib.Automata.LinearBounded.DiamondPaths
import Mathlib.Tactic

@[expose]
public section

/-!
# Capacity of literal same-width branch schedules

A row of width `width` over a finite alphabet `A` has exactly `|A| ^ width` possible values.
Consequently, an injective encoding of every length-`k` Boolean branch vector into one such row
requires `2 ^ k ≤ |A| ^ width`.  This file records that elementary obstruction, its
contrapositive, and versions for the bounded schedules and diamond paths already used by the LBA
development.

The results concern **literal enumeration or encoding of all schedules as distinct rows**.  They
are not lower bounds for deterministic LBA simulation: a simulator may recompute choices, reuse
space, encode only selected schedules, or avoid materializing a whole branch vector.
-/

namespace ScheduleCapacity

/-! ## Finite row capacity -/

/-- An injection of a finite source type into width-`width` rows requires at least as many rows
as source values.  This statement includes width zero and empty alphabets. -/
public theorem card_le_rowCapacity_of_injective
    {S A : Type*} [Fintype S] [Fintype A] {width : ℕ}
    (encode : S → Fin width → A) (hinjective : Function.Injective encode) :
    Fintype.card S ≤ Fintype.card A ^ width := by
  rw [← Fintype.card_pi_const A width]
  exact Fintype.card_le_of_injective encode hinjective

/-- Encoding all choice vectors indexed by an arbitrary finite type into one row forces the
corresponding cardinal inequality. -/
public theorem choiceVectors_le_rowCapacity_of_injective
    {I Choice A : Type*} [Fintype I] [Fintype Choice] [Fintype A] {width : ℕ}
    (encode : (I → Choice) → Fin width → A)
    (hinjective : Function.Injective encode) :
    Fintype.card Choice ^ Fintype.card I ≤ Fintype.card A ^ width := by
  classical
  simpa only [Fintype.card_fun] using
    card_le_rowCapacity_of_injective encode hinjective

/-- The finite-index form of the choice-vector capacity bound. -/
public theorem finChoiceVectors_le_rowCapacity_of_injective
    {Choice A : Type*} [Fintype Choice] [Fintype A] {k width : ℕ}
    (encode : (Fin k → Choice) → Fin width → A)
    (hinjective : Function.Injective encode) :
    Fintype.card Choice ^ k ≤ Fintype.card A ^ width := by
  simpa only [Fintype.card_fin] using
    choiceVectors_le_rowCapacity_of_injective encode hinjective

/-- In particular, an injective row encoding of all `k`-bit branch vectors requires capacity at
least `2 ^ k`. -/
public theorem bitVectors_le_rowCapacity_of_injective
    {A : Type*} [Fintype A] {k width : ℕ}
    (encode : (Fin k → Bool) → Fin width → A)
    (hinjective : Function.Injective encode) :
    2 ^ k ≤ Fintype.card A ^ width := by
  simpa only [Fintype.card_bool] using
    finChoiceVectors_le_rowCapacity_of_injective encode hinjective

/-- If the row capacity is strictly below `2 ^ k`, no map from all `k`-bit vectors to rows can
be injective. -/
public theorem not_injective_bitVectors_of_capacity_lt
    {A : Type*} [Fintype A] {k width : ℕ}
    (hcapacity : Fintype.card A ^ width < 2 ^ k)
    (encode : (Fin k → Bool) → Fin width → A) :
    ¬ Function.Injective encode := by
  intro hinjective
  exact (Nat.not_lt_of_ge
    (bitVectors_le_rowCapacity_of_injective encode hinjective)) hcapacity

/-- A positive number of branch bits cannot be injectively stored in a row of width zero,
independently of the target alphabet. -/
public theorem not_injective_bitVectors_zero_width
    {A : Type*} [Fintype A] {k : ℕ} (hk : 0 < k)
    (encode : (Fin k → Bool) → Fin 0 → A) :
    ¬ Function.Injective encode := by
  apply not_injective_bitVectors_of_capacity_lt (encode := encode)
  simpa only [pow_zero] using Nat.one_lt_two_pow (Nat.ne_of_gt hk)

/-- Over an alphabet with at most two symbols, fewer than `k` cells cannot injectively store all
`k`-bit vectors.  The exact-capacity theorem above is the useful version for larger alphabets. -/
public theorem not_injective_bitVectors_of_card_le_two_of_width_lt
    {A : Type*} [Fintype A] {k width : ℕ}
    (hcard : Fintype.card A ≤ 2) (hwidth : width < k)
    (encode : (Fin k → Bool) → Fin width → A) :
    ¬ Function.Injective encode := by
  apply not_injective_bitVectors_of_capacity_lt (encode := encode)
  exact (Nat.pow_le_pow_left hcard width).trans_lt
    (Nat.pow_lt_pow_right (by omega) hwidth)

/-! ## Existing bounded schedules -/

/-- Regard an exact length-`k` vector as a bounded schedule whose budget is `k`. -/
@[expose]
public def fullSchedule {Choice : Type*} {k : ℕ} (choices : Fin k → Choice) :
    FiniteChoiceGraph.Schedule Choice k :=
  FiniteChoiceGraph.Schedule.ofList (List.ofFn choices) (by simp)

/-- Converting a full schedule back to a list recovers its vector. -/
public theorem fullSchedule_toList {Choice : Type*} {k : ℕ}
    (choices : Fin k → Choice) :
    (fullSchedule choices).toList = List.ofFn choices := by
  exact FiniteChoiceGraph.Schedule.toList_ofList _ _

/-- Exact-length vectors embed into the existing type of schedules of length at most `k`. -/
public theorem fullSchedule_injective {Choice : Type*} {k : ℕ} :
    Function.Injective (fullSchedule :
      (Fin k → Choice) → FiniteChoiceGraph.Schedule Choice k) := by
  intro left right heq
  apply List.ofFn_injective
  rw [← fullSchedule_toList left, ← fullSchedule_toList right, heq]

/-- Any injective row representation of every bounded schedule must in particular hold all
exact-length schedules. -/
public theorem schedules_le_rowCapacity_of_injective
    {Choice A : Type*} [Fintype Choice] [Fintype A] {k width : ℕ}
    (encode : FiniteChoiceGraph.Schedule Choice k → Fin width → A)
    (hinjective : Function.Injective encode) :
    Fintype.card Choice ^ k ≤ Fintype.card A ^ width := by
  apply finChoiceVectors_le_rowCapacity_of_injective
    (encode := encode ∘ fullSchedule)
  exact hinjective.comp fullSchedule_injective

/-- If exact length-`k` schedules already exceed the row capacity, an encoding of the larger
bounded-schedule type cannot be injective. -/
public theorem not_injective_schedules_of_capacity_lt
    {Choice A : Type*} [Fintype Choice] [Fintype A] {k width : ℕ}
    (hcapacity : Fintype.card A ^ width < Fintype.card Choice ^ k)
    (encode : FiniteChoiceGraph.Schedule Choice k → Fin width → A) :
    ¬ Function.Injective encode := by
  intro hinjective
  exact (Nat.not_lt_of_ge
    (schedules_le_rowCapacity_of_injective encode hinjective)) hcapacity

/-! ## Diamond-path corollaries -/

/-- An injective encoding of every path through a `k`-diamond chain into a single row requires
room for its `2 ^ k` explicitly distinct bit-selected paths. -/
public theorem diamondPaths_le_rowCapacity_of_injective
    {A : Type*} [Fintype A] {k width : ℕ}
    (encode : DiamondPaths.STPath k → Fin width → A)
    (hinjective : Function.Injective encode) :
    2 ^ k ≤ Fintype.card A ^ width := by
  apply bitVectors_le_rowCapacity_of_injective
    (encode := encode ∘ DiamondPaths.pathOfBits)
  exact hinjective.comp (DiamondPaths.pathOfBits_injective k)

/-- Below the cardinal threshold, no single row can injectively enumerate all path data in the
diamond chain.  This is an enumeration barrier, not a deterministic-LBA lower bound. -/
public theorem not_injective_diamondPaths_of_capacity_lt
    {A : Type*} [Fintype A] {k width : ℕ}
    (hcapacity : Fintype.card A ^ width < 2 ^ k)
    (encode : DiamondPaths.STPath k → Fin width → A) :
    ¬ Function.Injective encode := by
  intro hinjective
  exact (Nat.not_lt_of_ge
    (diamondPaths_le_rowCapacity_of_injective encode hinjective)) hcapacity

end ScheduleCapacity

end
