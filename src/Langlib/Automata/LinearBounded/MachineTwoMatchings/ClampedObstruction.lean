module

public import Langlib.Automata.LinearBounded.Cofunctional.ClampedObstruction
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Clamped moves inside exact two-matching presentations

An exact union of two directed matchings has a sharp local incidence restriction.  If a vertex
has two distinct predecessors, those incoming edges must consume the two different colors.
Because neither color permits two composable edges, the vertex has no successor.  Dually, a
vertex with two distinct successors has no predecessor.

Every enabled directional LBA transition creates such a two-predecessor vertex somewhere in the
complete raw width-two configuration graph: put the symbol written by the transition in both
cells and compare the clamped boundary departure with the neighbouring departure.  Hence that
particular collision target must be a sink in every exact-two-matching presentation.

This is deliberately an existential boundary obstruction.  An arbitrary interior target of a
directional transition can have only one positional predecessor and may continue using the other
color.  Thus these lemmas do not imply that exact-two-matching languages are constant.
-/

namespace LBA

open Relation

variable {Γ Λ : Type*}

/-- In an exact union of two directed matchings, a vertex with two distinct predecessors is a
sink. -/
public theorem Machine.sink_of_two_distinct_predecessors_of_hasTwoMatchingStepPartition
    (M : Machine Γ Λ) (hlayers : M.HasTwoMatchingStepPartition) {n : ℕ}
    {left right target : DLBA.Cfg Γ Λ n}
    (hne : left ≠ right) (hleft : Step M left target) (hright : Step M right target) :
    ∀ next, ¬ Step M target next := by
  rcases hlayers with ⟨layer, cover, _subedge, biUnique, short⟩
  obtain ⟨leftColor, hleftColor, _⟩ := (cover n left target).mp hleft
  obtain ⟨rightColor, hrightColor, _⟩ := (cover n right target).mp hright
  have hcolors : leftColor ≠ rightColor := by
    intro heq
    subst rightColor
    exact hne ((biUnique n leftColor).1 hleftColor hrightColor)
  intro next hnext
  obtain ⟨nextColor, hnextColor, _⟩ := (cover n target next).mp hnext
  have hnextCases : nextColor = leftColor ∨ nextColor = rightColor := by
    omega
  rcases hnextCases with hsame | hsame
  · subst nextColor
    exact short n leftColor hleftColor hnextColor
  · subst nextColor
    exact short n rightColor hrightColor hnextColor

/-- Dually, a vertex with two distinct successors has no predecessor. -/
public theorem Machine.source_of_two_distinct_successors_of_hasTwoMatchingStepPartition
    (M : Machine Γ Λ) (hlayers : M.HasTwoMatchingStepPartition) {n : ℕ}
    {source left right : DLBA.Cfg Γ Λ n}
    (hne : left ≠ right) (hleft : Step M source left) (hright : Step M source right) :
    ∀ previous, ¬ Step M previous source := by
  rcases hlayers with ⟨layer, cover, _subedge, biUnique, short⟩
  obtain ⟨leftColor, hleftColor, _⟩ := (cover n source left).mp hleft
  obtain ⟨rightColor, hrightColor, _⟩ := (cover n source right).mp hright
  have hcolors : leftColor ≠ rightColor := by
    intro heq
    subst rightColor
    exact hne ((biUnique n leftColor).2 hleftColor hrightColor)
  intro previous hprevious
  obtain ⟨previousColor, hpreviousColor, _⟩ :=
    (cover n previous source).mp hprevious
  have hpreviousCases : previousColor = leftColor ∨ previousColor = rightColor := by
    omega
  rcases hpreviousCases with hsame | hsame
  · subst previousColor
    exact short n leftColor hpreviousColor hleftColor
  · subst previousColor
    exact short n rightColor hpreviousColor hrightColor

/-- Every enabled left move creates an explicit clamped two-predecessor collision whose target
is therefore a sink under an exact two-matching partition. -/
public theorem Machine.exists_left_clamping_collision_sink_of_hasTwoMatchingStepPartition
    (M : Machine Γ Λ) (hlayers : M.HasTwoMatchingStepPartition)
    {source target : Λ} {read written : Γ}
    (henabled : (target, written, DLBA.Dir.left) ∈ M.transition source read) :
    ∃ (boundary neighbor destination : DLBA.Cfg Γ Λ 1),
      boundary ≠ neighbor ∧
        Step M boundary destination ∧ Step M neighbor destination ∧
        ∀ next, ¬ Step M destination next := by
  obtain ⟨boundary, neighbor, destination, hne, hboundary, hneighbor⟩ :=
    M.exists_distinct_predecessors_of_mem_transition_left henabled
  exact ⟨boundary, neighbor, destination, hne, hboundary, hneighbor,
    M.sink_of_two_distinct_predecessors_of_hasTwoMatchingStepPartition
      hlayers hne hboundary hneighbor⟩

/-- Every enabled right move creates the mirrored clamped collision sink. -/
public theorem Machine.exists_right_clamping_collision_sink_of_hasTwoMatchingStepPartition
    (M : Machine Γ Λ) (hlayers : M.HasTwoMatchingStepPartition)
    {source target : Λ} {read written : Γ}
    (henabled : (target, written, DLBA.Dir.right) ∈ M.transition source read) :
    ∃ (neighbor boundary destination : DLBA.Cfg Γ Λ 1),
      neighbor ≠ boundary ∧
        Step M neighbor destination ∧ Step M boundary destination ∧
        ∀ next, ¬ Step M destination next := by
  obtain ⟨neighbor, boundary, destination, hne, hneighbor, hboundary⟩ :=
    M.exists_distinct_predecessors_of_mem_transition_right henabled
  exact ⟨neighbor, boundary, destination, hne, hneighbor, hboundary,
    M.sink_of_two_distinct_predecessors_of_hasTwoMatchingStepPartition
      hlayers hne hneighbor hboundary⟩

end LBA

