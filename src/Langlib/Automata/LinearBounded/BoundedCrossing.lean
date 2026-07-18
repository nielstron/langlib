module

public import Langlib.Automata.LinearBounded.SimpleTraceCrossingBound
public import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

@[expose]
public section

/-!
# Uniformly bounded crossing witnesses

This module packages the weak, existential bounded-crossing promise for an LBA.  An input is
accepted with crossing bound `c` when it has one accepting concrete trace that crosses every
physical tape boundary at most `c` times.  Other accepting and rejecting traces are unrestricted.

Quantitative loop erasure from `SimpleTraceCrossingBound` turns such a witness into a simple
one without increasing any boundary count.  If the tape has `n + 1` cells, the shortened trace
therefore has length `L` satisfying

`L + 1 ≤ (|state| * |alphabet|) * (n * c + 1)`.

For canonical endmarker inputs of length `m`, the tape has `m + 2` cells.  A single uniform
crossing bound consequently yields accepting witnesses of linear length.  This is a resource
lemma, not a determinization: under the weak measure, linear accepting time by itself does not
force a nondeterministic one-tape language to be regular.
-/

namespace LBA.BoundedCrossing

universe u v

variable {Gamma : Type u} {State : Type v} {n : Nat}
variable {M : LBA.Machine Gamma State}
variable {source : DLBA.Cfg Gamma State n}

/-- Acceptance witnessed by one concrete trace whose crossing count at every physical boundary
is at most `bound`. -/
def AcceptsWithBound (M : LBA.Machine Gamma State)
    (source : DLBA.Cfg Gamma State n) (bound : Nat) : Prop :=
  ∃ target : DLBA.Cfg Gamma State n,
    ∃ trace : LBA.StepTrace M source target,
      M.accept target.state = true ∧
        ∀ b : Fin n, trace.crossingCount b ≤ bound

/-- Exact trace-level negation of bounded acceptance: every accepting trace must exceed the
proposed cap at some physical boundary.

This includes `n = 0`.  In that case there is no boundary, so the right-hand side says that
there can be no accepting trace, exactly as the vacuous boundary bound in `AcceptsWithBound`
requires. -/
theorem not_acceptsWithBound_iff_every_acceptingTrace_exceeds
    (M : LBA.Machine Gamma State) (source : DLBA.Cfg Gamma State n) (bound : Nat) :
    ¬ AcceptsWithBound M source bound ↔
      ∀ (target : DLBA.Cfg Gamma State n)
        (trace : LBA.StepTrace M source target),
        M.accept target.state = true →
          ∃ boundary : Fin n, bound < trace.crossingCount boundary := by
  constructor
  · intro hnotBounded target trace hfinal
    by_contra hnotExceeds
    apply hnotBounded
    refine ⟨target, trace, hfinal, ?_⟩
    intro boundary
    exact Nat.le_of_not_gt fun hexceeds ↦
      hnotExceeds ⟨boundary, hexceeds⟩
  · intro hexceeds hbounded
    obtain ⟨target, trace, hfinal, hcross⟩ := hbounded
    obtain ⟨boundary, hboundary⟩ := hexceeds target trace hfinal
    exact (Nat.not_lt_of_ge (hcross boundary)) hboundary

/-- Increasing the crossing cap preserves a bounded accepting witness. -/
theorem AcceptsWithBound.mono {smaller larger : Nat}
    (haccept : AcceptsWithBound M source smaller) (hbound : smaller ≤ larger) :
    AcceptsWithBound M source larger := by
  obtain ⟨target, trace, hfinal, hcross⟩ := haccept
  exact ⟨target, trace, hfinal, fun b ↦ (hcross b).trans hbound⟩

/-- A bounded-crossing accepting witness is an ordinary accepting run. -/
theorem accepts_of_acceptsWithBound {bound : Nat}
    (haccept : AcceptsWithBound M source bound) :
    LBA.Accepts M source := by
  obtain ⟨target, trace, hfinal, hcross⟩ := haccept
  exact ⟨target, trace.reaches, hfinal⟩

/-- Every accepting finite run has some finite per-boundary bound.

The trace length itself is a uniform bound over its finitely many boundaries, including the
vacuous one-cell case. -/
theorem accepts_iff_exists_acceptsWithBound :
    LBA.Accepts M source ↔ ∃ bound, AcceptsWithBound M source bound := by
  constructor
  · rintro ⟨target, hreach, hfinal⟩
    obtain ⟨trace⟩ := LBA.StepTrace.nonempty_iff_reaches.mpr hreach
    exact ⟨trace.length, target, trace, hfinal,
      fun b ↦ LBA.StepTrace.crossingCount_le_length b trace⟩
  · rintro ⟨bound, haccept⟩
    exact accepts_of_acceptsWithBound haccept

/-- A bounded-crossing accepting witness can be chosen simple, with an explicit length bound.

This theorem is uniform over arbitrary finite tape-symbol and state types and makes no
inhabitedness or cardinality-lower-bound assumption. -/
theorem exists_simple_acceptingTrace_of_acceptsWithBound
    [Fintype Gamma] [Fintype State] {bound : Nat}
    (haccept : AcceptsWithBound M source bound) :
    ∃ target : DLBA.Cfg Gamma State n,
      ∃ trace : LBA.StepTrace M source target,
        M.accept target.state = true ∧
          trace.Simple ∧
          (∀ b : Fin n, trace.crossingCount b ≤ bound) ∧
          trace.length + 1 ≤
            (Fintype.card State * Fintype.card Gamma) * (n * bound + 1) := by
  obtain ⟨target, trace, hfinal, hcross⟩ := haccept
  obtain ⟨shortened, hsimple, hlength, hshortCross, hbound⟩ :=
    LBA.StepTrace.exists_simple_length_add_one_le_card_mul_boundaryCap_add_one
      trace bound hcross
  exact ⟨target, shortened, hfinal, hsimple,
    fun b ↦ (hshortCross b).trans (hcross b), hbound⟩

variable {Terminal Work : Type*}

/-- One constant bounds a selected accepting trace on every accepted canonical endmarker input.

The quantifier order is the weak/existential one: for each accepted word there merely has to
exist one bounded-crossing accepting computation. -/
def HasUniformAcceptingBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (bound : Nat) : Prop :=
  ∀ input : List Terminal,
    LBA.Accepts M (LBA.initCfgEnd M input) →
      AcceptsWithBound M (LBA.initCfgEnd M input) bound

/-- Semantic promise that every accepted endmarker input has an accepting concrete trace of at
most `stepsPerCell` steps per physical tape cell. -/
def HasLinearAcceptingStepBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (stepsPerCell : Nat) : Prop :=
  ∀ input : List Terminal,
    LBA.Accepts M (LBA.initCfgEnd M input) →
      ∃ target : DLBA.Cfg (LBA.EndAlpha Terminal Work) State (input.length + 1),
        ∃ trace : LBA.StepTrace M (LBA.initCfgEnd M input) target,
          M.accept target.state = true ∧
            trace.length ≤ (input.length + 2) * stepsPerCell

/-- A uniform crossing cap gives a uniform linear bound on the length of a selected accepting
trace.

For an input of length `m`, there are `m + 1` boundaries and `m + 2` physical cells.  The
constant is the number of local `(state, tape symbol)` views times `bound + 1`. -/
theorem hasLinearAcceptingStepBound_of_hasUniformAcceptingBound
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    {bound : Nat} (hbound : HasUniformAcceptingBound M bound) :
    HasLinearAcceptingStepBound M
      (Fintype.card State * Fintype.card (LBA.EndAlpha Terminal Work) *
        max bound 1) := by
  intro input haccept
  obtain ⟨target, trace, hfinal, hsimple, hcross, hlength⟩ :=
    exists_simple_acceptingTrace_of_acceptsWithBound
      (hbound input haccept)
  refine ⟨target, trace, hfinal, ?_⟩
  let localViews :=
    Fintype.card State * Fintype.card (LBA.EndAlpha Terminal Work)
  let cap := max bound 1
  have hwidth :
      (input.length + 1) * bound + 1 ≤
        (input.length + 2) * cap := by
    calc
      (input.length + 1) * bound + 1 ≤
          (input.length + 1) * cap + cap := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left _ (Nat.le_max_left bound 1))
          (Nat.le_max_right bound 1)
      _ = (input.length + 2) * cap := by ring
  calc
    trace.length ≤ trace.length + 1 := Nat.le_succ _
    _ ≤ localViews * ((input.length + 1) * bound + 1) := by
      simpa [localViews] using hlength
    _ ≤ localViews * ((input.length + 2) * cap) :=
      Nat.mul_le_mul_left localViews hwidth
    _ = (input.length + 2) *
          (Fintype.card State * Fintype.card (LBA.EndAlpha Terminal Work) *
            max bound 1) := by
      simp only [localViews, cap]
      ac_rfl

end LBA.BoundedCrossing

end
