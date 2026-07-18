module

public import Langlib.Automata.LinearBounded.BoundedNondeterminism
public import Langlib.Automata.LinearBounded.ThreeMatchingReachability

@[expose]
public section

/-!
# Two matching layers permit at most one genuine branch event

An exact union of two directed matchings can branch only at a vertex with no predecessor.
Consequently every path, from every source, encounters at most one genuine branch event: after
taking an edge out of a branch, every later vertex has an incoming edge.

This file connects that relational fact to the bounded-nondeterminism search API.  It proves that
budget `1` is complete for reachability and LBA acceptance whenever the whole configuration step
relation has a width-uniform exact two-matching partition.  This file supplies the finite-search
specification; `MachineTwoMatchings/Determinize.lean` gives the completed low-level
`DLBA.Machine` compiler and the resulting language-class inclusion.
-/

open Classical Relation

namespace FiniteChoiceGraph

variable {V Choice : Type*} (G : FiniteChoiceGraph V Choice)

/-- Increasing the schedule budget preserves bounded-choice acceptance. -/
public theorem acceptsWithChoices_mono
    [Fintype V] [DecidableEq V]
    (accept : V → Bool) (source : V) {small large : ℕ}
    (hbudget : small ≤ large)
    (haccept : G.AcceptsWithChoices accept source small) :
    G.AcceptsWithChoices accept source large := by
  obtain ⟨schedule, target, trace, hfinal⟩ := haccept
  have hlengthSmall : schedule.toList.length ≤ small := by
    rw [schedule.length_toList]
    exact Nat.le_of_lt_succ schedule.1.isLt
  let enlarged : Schedule Choice large :=
    Schedule.ofList schedule.toList (hlengthSmall.trans hbudget)
  refine ⟨enlarged, target, ?_, hfinal⟩
  simpa [enlarged] using trace

/-- If the source of a branch trace already has an incoming edge, the trace contains no branch
choices.  A later branch junction would itself have an incoming edge, contradicting the
two-matching obstruction. -/
public theorem BranchTrace.choices_eq_nil_of_incoming
    {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, G.Edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {predecessor source target : V} (hincoming : G.Edge predecessor source)
    {choices : List Choice} (trace : G.BranchTrace choices source target) :
    choices = [] := by
  cases trace with
  | finish _ => rfl
  | @branch _ junction _ _ _ _ detPath isBranch _ _ =>
      have hjunctionIncoming : ∃ previous, G.Edge previous junction := by
        rcases ReflTransGen.cases_tail detPath with heq | ⟨previous, _, hlast⟩
        · subst junction
          exact ⟨predecessor, hincoming⟩
        · exact ⟨previous, hlast.1⟩
      obtain ⟨previous, hprevious⟩ := hjunctionIncoming
      exact False.elim
        (ThreeMatchingReachability.no_predecessor_of_branches
          cover biUnique short isBranch previous hprevious)

/-- Every branch trace in an exact union of two directed matchings records at most one genuine
branch event. -/
public theorem BranchTrace.length_le_one_of_twoMatchings
    {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, G.Edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {choices : List Choice} {source target : V}
    (trace : G.BranchTrace choices source target) :
    choices.length ≤ 1 := by
  cases trace with
  | finish _ => simp
  | @branch _ junction next _ choice choices _ _ take rest =>
      have hincoming : G.Edge junction next := ⟨choice, take⟩
      have hnil : choices = [] :=
        rest.choices_eq_nil_of_incoming G cover biUnique short hincoming
      simp [hnil]

variable [Fintype V] [DecidableEq V]

/-- In an exact union of two directed matchings, ordinary accepting reachability always has a
bounded replay schedule of budget one. -/
public theorem acceptsWithChoices_one_of_reaches
    {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, G.Edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    (accept : V → Bool) {source target : V}
    (hreach : ReflTransGen G.Edge source target)
    (hfinal : accept target = true) :
    G.AcceptsWithChoices accept source 1 := by
  obtain ⟨choices, trace⟩ := G.exists_branchTrace_of_reaches hreach
  have hlength : choices.length ≤ 1 :=
    trace.length_le_one_of_twoMatchings G cover biUnique short
  let schedule : Schedule Choice 1 := Schedule.ofList choices hlength
  refine ⟨schedule, target, ?_, hfinal⟩
  simpa [schedule] using G.replayTrace_of_branchTrace trace

/-- Budget-one exhaustive search is exact for every acceptance predicate on an exact union of
two directed matchings. -/
public theorem acceptsWithChoicesSearch_one_eq_true_iff
    [Fintype Choice]
    {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, G.Edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    (accept : V → Bool) (source : V) :
    G.acceptsWithChoicesSearch accept source 1 = true ↔
      ∃ target, ReflTransGen G.Edge source target ∧ accept target = true := by
  rw [G.acceptsWithChoicesSearch_eq_true_iff]
  constructor
  · exact G.acceptsWithChoices_imp accept
  · rintro ⟨target, hreach, hfinal⟩
    exact G.acceptsWithChoices_one_of_reaches
      cover biUnique short accept hreach hfinal

end FiniteChoiceGraph

namespace LBA

variable {Γ Λ : Type*}

/-- A width-uniform exact two-color partition of the complete raw configuration relation into
directed matchings. -/
public def Machine.HasTwoMatchingStepPartition (M : Machine Γ Λ) : Prop :=
  ∃ layer : (n : ℕ) → Fin 2 →
      DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop,
    (∀ n source target,
      Step M source target ↔ ∃! color, layer n color source target) ∧
      (∀ n color source target,
        layer n color source target → Step M source target) ∧
      (∀ n color, Relator.BiUnique (layer n color)) ∧
      ∀ n color,
        LinearTwoDiforestReachability.PathLengthAtMostOne (layer n color)

namespace BoundedNondeterminism

variable [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- For an LBA whose complete step relation is an exact union of two directed matchings,
acceptance is witnessed by a schedule containing at most one genuine branch event. -/
public theorem acceptsWithChoiceEvents_one_iff
    (M : Machine Γ Λ) (hlayers : M.HasTwoMatchingStepPartition)
    {n : ℕ} (source : DLBA.Cfg Γ Λ n) :
    AcceptsWithChoiceEvents M source 1 ↔ Accepts M source := by
  rcases hlayers with ⟨layer, cover, _sub, biUnique, short⟩
  constructor
  · exact accepts_of_acceptsWithChoiceEvents M
  · rintro ⟨target, hreach, hfinal⟩
    have graphCover : ∀ old new,
        (cfgGraph M).Edge old new ↔ ∃! color, layer n color old new := by
      intro old new
      exact (cfgGraph_edge_iff M old new).trans (cover n old new)
    have graphReach : ReflTransGen (cfgGraph M).Edge source target :=
      hreach.mono fun old new hstep => (cfgGraph_edge_iff M old new).2 hstep
    exact (cfgGraph M).acceptsWithChoices_one_of_reaches
      graphCover (biUnique n) (short n)
      (fun cfg => M.accept cfg.state) graphReach hfinal

/-- The corresponding executable finite specification needs to enumerate only schedules of
budget one, independently of the tape width. -/
public theorem acceptsWithChoiceEventsSearch_one_eq_true_iff
    (M : Machine Γ Λ) (hlayers : M.HasTwoMatchingStepPartition)
    {n : ℕ} (source : DLBA.Cfg Γ Λ n) :
    acceptsWithChoiceEventsSearch M source 1 = true ↔ Accepts M source := by
  rw [acceptsWithChoiceEventsSearch_eq_true_iff]
  exact acceptsWithChoiceEvents_one_iff M hlayers source

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Two exact matching layers imply the existing linear-choice promise with constant one. -/
public theorem hasLinearAcceptingChoiceBound_one_of_twoMatchings
    (M : Machine (EndAlpha T Γ) Λ)
    (hlayers : M.HasTwoMatchingStepPartition) :
    HasLinearAcceptingChoiceBound M 1 := by
  intro input haccept
  have hone : AcceptsWithChoiceEvents M (initCfgEnd M input) 1 :=
    (acceptsWithChoiceEvents_one_iff M hlayers _).2 haccept
  apply (cfgGraph M).acceptsWithChoices_mono
    (fun cfg => M.accept cfg.state) (initCfgEnd M input) (haccept := hone)
  simp

end BoundedNondeterminism

end LBA

end
