module

public import Langlib.Automata.LinearBounded.BoundedCrossing
public import Langlib.Automata.LinearBounded.BoundedNondeterminism
import Mathlib.Tactic

@[expose]
public section

/-!
# From bounded crossings to linearly many genuine branch events

A concrete LBA trace determines a branch schedule for the finite-choice graph: record a choice
exactly at configurations having two distinct successors.  The schedule contains no more entries
than the trace has steps.  Combining that observation with quantitative loop erasure proves that
a uniform accepting crossing bound implies the semantic linear-choice promise already used by
`BoundedNondeterminism`.

This is an exact resource bridge, not by itself a concrete DLBA construction.  The existing
bounded-nondeterminism development proves finite exhaustive-search semantics and same-width
storage capacity for the schedules, but deliberately does not yet implement the low-level sweep
machine that enumerates and replays them.
-/

open Relation

namespace FiniteChoiceGraph

variable {V Choice : Type*} (G : FiniteChoiceGraph V Choice)

/-- Prepending one nonbranching edge preserves the branch schedule. -/
theorem BranchTrace.head_deterministic
    {choices : List Choice} {source next target : V}
    (hstep : G.DeterministicStep source next)
    (trace : G.BranchTrace choices next target) :
    G.BranchTrace choices source target := by
  cases trace with
  | finish path =>
      exact .finish (ReflTransGen.head hstep path)
  | branch path isBranch take rest =>
      exact .branch (ReflTransGen.head hstep path) isBranch take rest

end FiniteChoiceGraph

namespace LBA.BoundedNondeterminism

universe u v

variable {Gamma : Type u} {State : Type v} {n : Nat}

/-- A concrete computation induces a schedule containing exactly its genuine branch events,
and hence no more choices than machine steps. -/
theorem exists_branchTrace_length_le_of_stepTrace
    (M : LBA.Machine Gamma State)
    {source target : DLBA.Cfg Gamma State n}
    (trace : LBA.StepTrace M source target) :
    ∃ choices,
      (cfgGraph M).BranchTrace choices source target ∧
        choices.length ≤ trace.length := by
  induction trace with
  | refl cfg =>
      exact ⟨[], .finish .refl, Nat.zero_le 0⟩
  | @head source next target hstep rest ih =>
      obtain ⟨choices, branchTrace, hlength⟩ := ih
      have hedge : (cfgGraph M).Edge source next :=
        (cfgGraph_edge_iff M source next).2 hstep
      by_cases hbranch : (cfgGraph M).Branching source
      · obtain ⟨choice, hchoice⟩ := hedge
        refine ⟨choice :: choices,
          .branch .refl hbranch hchoice branchTrace, ?_⟩
        simp only [List.length_cons, LBA.StepTrace.length]
        omega
      · refine ⟨choices,
          branchTrace.head_deterministic (G := cfgGraph M)
            ⟨hedge, hbranch⟩, ?_⟩
        simp only [LBA.StepTrace.length]
        omega

variable [Fintype Gamma] [Fintype State]
variable [DecidableEq Gamma] [DecidableEq State]

/-- A concrete accepting trace whose length is within `budget` witnesses bounded-choice
acceptance with the same budget. -/
theorem acceptsWithChoiceEvents_of_stepTrace
    (M : LBA.Machine Gamma State)
    {source target : DLBA.Cfg Gamma State n} {budget : Nat}
    (trace : LBA.StepTrace M source target)
    (hfinal : M.accept target.state = true)
    (hlength : trace.length ≤ budget) :
    AcceptsWithChoiceEvents M source budget := by
  obtain ⟨choices, branchTrace, hchoices⟩ :=
    exists_branchTrace_length_le_of_stepTrace M trace
  have hbudget : choices.length ≤ budget := hchoices.trans hlength
  let schedule : FiniteChoiceGraph.Schedule (BranchChoice Gamma State) budget :=
    FiniteChoiceGraph.Schedule.ofList choices hbudget
  refine ⟨schedule, target, ?_, hfinal⟩
  have replay := (cfgGraph M).replayTrace_of_branchTrace branchTrace
  simpa [schedule] using replay

/-- A per-boundary cap on one concrete accepting computation gives an explicit bounded-choice
witness.  Loop erasure is internal, so the original computation may repeat configurations. -/
theorem acceptsWithChoiceEvents_of_boundaryCap_stepTrace
    (M : LBA.Machine Gamma State)
    {source target : DLBA.Cfg Gamma State n}
    (trace : LBA.StepTrace M source target)
    (hfinal : M.accept target.state = true)
    (crossingsPerBoundary : Nat)
    (hcross : ∀ b : Fin n,
      trace.crossingCount b ≤ crossingsPerBoundary) :
    AcceptsWithChoiceEvents M source
      ((Fintype.card State * Fintype.card Gamma) *
        (n * crossingsPerBoundary + 1)) := by
  obtain ⟨shortened, hsimple, hleOriginal, hcrossShort, hlength⟩ :=
    LBA.StepTrace.exists_simple_length_add_one_le_card_mul_boundaryCap_add_one
      trace crossingsPerBoundary hcross
  apply acceptsWithChoiceEvents_of_stepTrace M shortened hfinal
  omega

variable {Terminal Work : Type*}
variable [Fintype Terminal] [Fintype Work]
variable [DecidableEq Terminal] [DecidableEq Work]

/-- A uniform accepting crossing cap implies the existing linear genuine-branch-event promise.

For a positive cap the constant is exactly `|state| * |tape alphabet| * cap`.  The `max` also
covers cap zero and the empty word's genuine two-cell endmarker tape. -/
theorem hasLinearAcceptingChoiceBound_of_hasUniformAcceptingBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (crossingsPerBoundary : Nat)
    (hcross : LBA.BoundedCrossing.HasUniformAcceptingBound
      M crossingsPerBoundary) :
    HasLinearAcceptingChoiceBound M
      ((Fintype.card State * Fintype.card (LBA.EndAlpha Terminal Work)) *
        max crossingsPerBoundary 1) := by
  intro input haccept
  obtain ⟨target, trace, hfinal, hcap⟩ := hcross input haccept
  let cap := max crossingsPerBoundary 1
  have hcap' : ∀ b : Fin (input.length + 1),
      trace.crossingCount b ≤ cap :=
    fun b ↦ (hcap b).trans (Nat.le_max_left _ _)
  obtain ⟨shortened, hsimple, hleOriginal, hcrossShort, hlength⟩ :=
    LBA.StepTrace.exists_simple_length_add_one_le_card_mul_boundaryCap_add_one
      trace cap hcap'
  apply acceptsWithChoiceEvents_of_stepTrace M shortened hfinal
  have hdropOne : shortened.length ≤
      (Fintype.card State * Fintype.card (LBA.EndAlpha Terminal Work)) *
        ((input.length + 1) * cap + 1) := by
    omega
  calc
    shortened.length ≤
        (Fintype.card State * Fintype.card (LBA.EndAlpha Terminal Work)) *
          ((input.length + 1) * cap + 1) := hdropOne
    _ ≤ (Fintype.card State * Fintype.card (LBA.EndAlpha Terminal Work)) *
          ((input.length + 2) * cap) := by
      apply Nat.mul_le_mul_left
      have hcapPositive : 1 ≤ cap := Nat.le_max_right _ _
      rw [show (input.length + 2) * cap =
        (input.length + 1) * cap + cap by ring]
      exact Nat.add_le_add_left hcapPositive _
    _ = (input.length + 2) *
        ((Fintype.card State * Fintype.card (LBA.EndAlpha Terminal Work)) *
          max crossingsPerBoundary 1) := by
      simp only [cap]
      ring

end LBA.BoundedNondeterminism

end
