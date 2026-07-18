module

public import Langlib.Automata.LinearBounded.HeadTurnCrossing

@[expose]
public section

/-!
# Sweeping traces on a marker-free bounded tape

This file defines the semantic sweeping restriction for concrete LBA traces.  On a tape with
`n + 1` physical cells, a trace is sweeping when every change between consecutive genuine head
movement directions occurs at cell `0` or cell `n`.

The definition uses `LBA.HeadTurns.physicalDirection`.  Consequently explicit `stay` moves and
outward moves clamped at an endpoint do not create a movement direction, do not overwrite the
previous genuine direction, and do not themselves count as turns.  The source configuration of
the first genuine step in the new direction is the configuration required to be at an endpoint.

All definitions and trace lemmas work over arbitrary symbol and state types.  In particular, no
finiteness, nonemptiness, or positive-width assumption is used.  On a one-cell tape (`n = 0`),
every step is physically stationary and every trace is sweeping.
-/

namespace LBA

namespace Sweeping

open LBA.HeadTurns

universe u v

variable {Gamma : Type u} {State : Type v} {n : Nat}

/-- The head is at one of the two physical endpoints of its bounded tape.

For a tape indexed by `Fin (n + 1)`, these endpoints are cells `0` and `n`.  When `n = 0`, the
unique cell is both endpoints. -/
def AtEndpoint (cfg : DLBA.Cfg Gamma State n) : Prop :=
  cfg.tape.head.val = 0 ∨ cfg.tape.head.val = n

public instance instDecidableAtEndpoint (cfg : DLBA.Cfg Gamma State n) :
    Decidable (AtEndpoint cfg) := by
  unfold AtEndpoint
  infer_instance

@[simp]
theorem atEndpoint_width_zero (cfg : DLBA.Cfg Gamma State 0) :
    AtEndpoint cfg := by
  left
  omega

/-- Whether a new genuine movement direction is compatible with the preceding genuine
direction.  The first genuine direction is always allowed; retaining the same direction is
always allowed; changing direction requires the source configuration to be at an endpoint. -/
def DirectionAllowed (previous : Option Direction)
    (source : DLBA.Cfg Gamma State n) (current : Direction) : Prop :=
  match previous with
  | none => True
  | some prior => prior = current ∨ AtEndpoint source

@[simp]
theorem directionAllowed_none (source : DLBA.Cfg Gamma State n) (current : Direction) :
    DirectionAllowed none source current := by
  simp [DirectionAllowed]

@[simp]
theorem directionAllowed_some (source : DLBA.Cfg Gamma State n)
    (prior current : Direction) :
    DirectionAllowed (some prior) source current ↔
      prior = current ∨ AtEndpoint source := by
  rfl

@[simp]
theorem directionAllowed_same (source : DLBA.Cfg Gamma State n) (direction : Direction) :
    DirectionAllowed (some direction) source direction := by
  simp [DirectionAllowed]

theorem directionAllowed_of_atEndpoint
    {source : DLBA.Cfg Gamma State n} (hsource : AtEndpoint source)
    (previous : Option Direction) (current : Direction) :
    DirectionAllowed previous source current := by
  cases previous with
  | none => trivial
  | some prior => exact Or.inr hsource

/-- Update the remembered genuine direction across one configuration pair.

Physically stationary pairs retain the old value.  A genuine movement replaces it with that
movement's direction. -/
def advanceDirection (previous : Option Direction)
    (source target : DLBA.Cfg Gamma State n) : Option Direction :=
  match physicalDirection source target with
  | none => previous
  | some current => some current

theorem advanceDirection_of_physicalDirection_eq_none
    (previous : Option Direction) (source target : DLBA.Cfg Gamma State n)
    (hdirection : physicalDirection source target = none) :
    advanceDirection previous source target = previous := by
  simp [advanceDirection, hdirection]

theorem advanceDirection_of_physicalDirection_eq_some
    (previous : Option Direction) (source target : DLBA.Cfg Gamma State n)
    (current : Direction)
    (hdirection : physicalDirection source target = some current) :
    advanceDirection previous source target = some current := by
  simp [advanceDirection, hdirection]

/-- The local sweeping obligation for one configuration pair.

A physically stationary pair is always allowed.  For a genuine movement, this is exactly
`DirectionAllowed` relative to the most recent genuine direction. -/
def TurnAllowed (previous : Option Direction)
    (source target : DLBA.Cfg Gamma State n) : Prop :=
  match physicalDirection source target with
  | none => True
  | some current => DirectionAllowed previous source current

theorem turnAllowed_of_physicalDirection_eq_none
    (previous : Option Direction) (source target : DLBA.Cfg Gamma State n)
    (hdirection : physicalDirection source target = none) :
    TurnAllowed previous source target := by
  simp [TurnAllowed, hdirection]

theorem turnAllowed_of_physicalDirection_eq_some
    (previous : Option Direction) (source target : DLBA.Cfg Gamma State n)
    (current : Direction)
    (hdirection : physicalDirection source target = some current) :
    TurnAllowed previous source target ↔
      DirectionAllowed previous source current := by
  simp [TurnAllowed, hdirection]

theorem turnAllowed_of_atEndpoint
    {source : DLBA.Cfg Gamma State n} (hsource : AtEndpoint source)
    (previous : Option Direction) (target : DLBA.Cfg Gamma State n) :
    TurnAllowed previous source target := by
  unfold TurnAllowed
  cases hdirection : physicalDirection source target with
  | none => trivial
  | some current =>
      exact directionAllowed_of_atEndpoint hsource previous current

/-- Every configuration pair on a one-cell tape is physically stationary. -/
@[simp]
theorem physicalDirection_width_zero
    (source target : DLBA.Cfg Gamma State 0) :
    physicalDirection source target = none := by
  simp [physicalDirection]

end Sweeping

namespace StepTrace

open LBA.HeadTurns
open LBA.Sweeping

universe u v

variable {Gamma : Type u} {State : Type v} {n : Nat}
variable {M : LBA.Machine Gamma State}
variable {source middle target : DLBA.Cfg Gamma State n}

/-- The most recent genuine movement direction after traversing a trace, starting with
`previous` before the trace.  Stationary and clamped steps leave the remembered direction
unchanged. -/
def lastDirectionFrom : {source target : DLBA.Cfg Gamma State n} →
    LBA.StepTrace M source target → Option Direction → Option Direction
  | _, _, .refl _, previous => previous
  | source, _, .head (next := next) _ rest, previous =>
      lastDirectionFrom rest (advanceDirection previous source next)

/-- A trace is sweeping relative to the most recent genuine direction before it began.

At each genuine movement, changing the remembered direction is permitted only when the source
configuration is at a physical endpoint.  Physically stationary steps preserve the remembered
direction and impose no obligation. -/
def SweepingFrom : {source target : DLBA.Cfg Gamma State n} →
    LBA.StepTrace M source target → Option Direction → Prop
  | _, _, .refl _, _ => True
  | source, _, .head (next := next) _ rest, previous =>
      TurnAllowed previous source next ∧
        SweepingFrom rest (advanceDirection previous source next)

/-- A sweeping trace, with no genuine movement direction preceding its first step. -/
def Sweeping (trace : LBA.StepTrace M source target) : Prop :=
  trace.SweepingFrom none

@[simp]
theorem lastDirectionFrom_refl
    (cfg : DLBA.Cfg Gamma State n) (previous : Option Direction) :
    lastDirectionFrom (.refl cfg : LBA.StepTrace M cfg cfg) previous = previous := rfl

@[simp]
theorem lastDirectionFrom_head
    {next : DLBA.Cfg Gamma State n} (step : LBA.Step M source next)
    (rest : LBA.StepTrace M next target) (previous : Option Direction) :
    lastDirectionFrom (.head step rest) previous =
      rest.lastDirectionFrom (advanceDirection previous source next) := rfl

@[simp]
theorem sweepingFrom_refl
    (cfg : DLBA.Cfg Gamma State n) (previous : Option Direction) :
    SweepingFrom (.refl cfg : LBA.StepTrace M cfg cfg) previous := trivial

@[simp]
theorem sweepingFrom_head
    {next : DLBA.Cfg Gamma State n} (step : LBA.Step M source next)
    (rest : LBA.StepTrace M next target) (previous : Option Direction) :
    SweepingFrom (.head step rest) previous ↔
      TurnAllowed previous source next ∧
        rest.SweepingFrom (advanceDirection previous source next) := by
  rfl

@[simp]
theorem sweeping_refl (cfg : DLBA.Cfg Gamma State n) :
    Sweeping (.refl cfg : LBA.StepTrace M cfg cfg) := trivial

/-- A physically stationary first step is completely ignored by the sweeping predicate: it
adds no turn obligation and preserves the preceding genuine direction. -/
theorem sweepingFrom_head_of_physicalDirection_eq_none
    {next : DLBA.Cfg Gamma State n} (step : LBA.Step M source next)
    (rest : LBA.StepTrace M next target) (previous : Option Direction)
    (hdirection : physicalDirection source next = none) :
    SweepingFrom (.head step rest) previous ↔
      rest.SweepingFrom previous := by
  simp [SweepingFrom, TurnAllowed, advanceDirection, hdirection]

/-- For a genuine first movement, the local obligation is `DirectionAllowed`, and the
remembered direction for the remaining trace becomes that movement's direction. -/
theorem sweepingFrom_head_of_physicalDirection_eq_some
    {next : DLBA.Cfg Gamma State n} (step : LBA.Step M source next)
    (rest : LBA.StepTrace M next target) (previous : Option Direction)
    (current : Direction)
    (hdirection : physicalDirection source next = some current) :
    SweepingFrom (.head step rest) previous ↔
      DirectionAllowed previous source current ∧
        rest.SweepingFrom (some current) := by
  simp [SweepingFrom, TurnAllowed, advanceDirection, hdirection]

/-- Starting a trace without a preceding direction is no more restrictive than starting it with
an already remembered direction. -/
theorem sweeping_of_sweepingFrom
    (trace : LBA.StepTrace M source target) (previous : Option Direction)
    (htrace : trace.SweepingFrom previous) :
    trace.Sweeping := by
  induction trace generalizing previous with
  | refl => trivial
  | @head source next target step rest ih =>
      cases hdirection : physicalDirection source next with
      | none =>
          have hrest : rest.SweepingFrom previous :=
            (sweepingFrom_head_of_physicalDirection_eq_none
              step rest previous hdirection).mp htrace
          have hsweeping : rest.Sweeping := ih previous hrest
          simpa [Sweeping,
            sweepingFrom_head_of_physicalDirection_eq_none
              step rest none hdirection] using hsweeping
      | some current =>
          have hrest : rest.SweepingFrom (some current) :=
            ((sweepingFrom_head_of_physicalDirection_eq_some
              step rest previous current hdirection).mp htrace).2
          exact (sweepingFrom_head_of_physicalDirection_eq_some
            step rest none current hdirection).mpr ⟨by simp, hrest⟩

/-- Remembered directions compose in chronological order across trace concatenation. -/
@[simp]
theorem lastDirectionFrom_append
    (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target)
    (previous : Option Direction) :
    (first.append second).lastDirectionFrom previous =
      second.lastDirectionFrom (first.lastDirectionFrom previous) := by
  induction first generalizing previous with
  | refl => rfl
  | @head source next middle step rest ih =>
      simp only [append, lastDirectionFrom_head]
      exact ih second (advanceDirection previous source next)

/-- Exact composition law for sweeping relative to a preceding direction. -/
theorem sweepingFrom_append
    (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target)
    (previous : Option Direction) :
    (first.append second).SweepingFrom previous ↔
      first.SweepingFrom previous ∧
        second.SweepingFrom (first.lastDirectionFrom previous) := by
  induction first generalizing previous with
  | refl =>
      change second.SweepingFrom previous ↔ True ∧ second.SweepingFrom previous
      simp
  | @head source next middle step rest ih =>
      simp only [append, sweepingFrom_head, lastDirectionFrom_head]
      rw [ih second]
      tauto

/-- Exact composition law for traces with no preceding direction. -/
theorem sweeping_append
    (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target) :
    (first.append second).Sweeping ↔
      first.Sweeping ∧
        second.SweepingFrom (first.lastDirectionFrom none) := by
  exact sweepingFrom_append first second none

/-- Every prefix of a sweeping trace is sweeping. -/
theorem sweeping_prefix
    (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target)
    (htrace : (first.append second).Sweeping) :
    first.Sweeping :=
  (sweeping_append first second).mp htrace |>.1

/-- The suffix of a sweeping trace is sweeping relative to the last genuine direction of its
prefix. -/
theorem sweepingFrom_suffix
    (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target)
    (htrace : (first.append second).Sweeping) :
    second.SweepingFrom (first.lastDirectionFrom none) :=
  (sweeping_append first second).mp htrace |>.2

/-- On a one-cell tape there is no physical head movement, so the remembered direction never
changes. -/
@[simp]
theorem lastDirectionFrom_width_zero
    {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State 0}
    (trace : LBA.StepTrace M source target) (previous : Option Direction) :
    trace.lastDirectionFrom previous = previous := by
  induction trace generalizing previous with
  | refl => rfl
  | @head source next target step rest ih =>
      rw [lastDirectionFrom_head,
        advanceDirection_of_physicalDirection_eq_none previous source next
          (physicalDirection_width_zero source next)]
      exact ih previous

/-- Every trace on a one-cell tape is sweeping, relative to any preceding direction. -/
@[simp]
theorem sweepingFrom_width_zero
    {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State 0}
    (trace : LBA.StepTrace M source target) (previous : Option Direction) :
    trace.SweepingFrom previous := by
  induction trace generalizing previous with
  | refl => trivial
  | @head source next target step rest ih =>
      apply (sweepingFrom_head_of_physicalDirection_eq_none
        step rest previous (physicalDirection_width_zero source next)).mpr
      exact ih previous

@[simp]
theorem sweeping_width_zero
    {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State 0}
    (trace : LBA.StepTrace M source target) :
    trace.Sweeping :=
  sweepingFrom_width_zero trace none

end StepTrace

namespace Machine

universe u v w

variable {Input : Type u} {Gamma : Type v} {State : Type w}

/-- Every finite trace from every positive-width marker-free input encoded by `embed` is
sweeping.

The vector presentation ranges over exactly the nonempty words: `input : Fin (n + 1) → Input`
represents a word of length `n + 1`, placed on the full tape with the head at cell `0`.  The
quantification is over every target and every concrete trace, not merely over a selected
accepting trace. -/
def SweepingViaEmbed (M : LBA.Machine Gamma State) (embed : Input → Gamma) : Prop :=
  ∀ {n : Nat} (input : Fin (n + 1) → Input)
    {target : DLBA.Cfg Gamma State n},
    ∀ trace : LBA.StepTrace M
      ⟨M.initial, ⟨fun index => embed (input index), 0⟩⟩ target,
      trace.Sweeping

end Machine

end LBA
