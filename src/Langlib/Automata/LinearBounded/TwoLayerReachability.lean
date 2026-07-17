module

public import Mathlib.Logic.Relation
public import Mathlib.Logic.Relator
public import Mathlib.Logic.ExistsUnique
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

@[expose]
public section

/-!
# Reachability through two partial-function layers

This file records the exact one-step recurrences for reachability when a directed relation is
partitioned into two partial functions.  `TwoPartialFunctionPartition edge layer` says that the
two `Fin 2` layers cover precisely the edges, assign a unique layer to every edge, and have at
most one successor of each color at every source.

For a final-vertex predicate `final`, `CanReach edge final source` means that some final vertex is
reachable from `source`, allowing a zero-step path.  Its complement requires both colored
successors to fail:

* reachability is `final source`, or success through layer zero, or success through layer one;
* nonreachability is `¬ final source` and failure through every layer-zero and layer-one edge.

These are propositional equivalences, not a deterministic evaluation algorithm.  Right
uniqueness makes each colored successor a partial function, but it does not choose which color
can eventually reach a final vertex.  No acyclicity, well-founded recursion, decidability, or
space bound is asserted.
-/

namespace TwoLayerReachability

open Relation

variable {V : Type*}

/-- An exact partition of `edge` into two partial functions.

`edge_iff_exists_layer` gives coverage and excludes spurious layer edges, `layer_disjoint` makes
the color of every edge unique, and `rightUnique` says that a fixed source and color have at most
one target. -/
public structure TwoPartialFunctionPartition
    (edge : V → V → Prop) (layer : Fin 2 → V → V → Prop) : Prop where
  edge_iff_exists_layer : ∀ source target,
    edge source target ↔ ∃ color, layer color source target
  layer_disjoint : ∀ {source target} {leftColor rightColor : Fin 2},
    layer leftColor source target →
      layer rightColor source target → leftColor = rightColor
  rightUnique : ∀ color, Relator.RightUnique (layer color)

namespace TwoPartialFunctionPartition

variable {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}

/-- Build the packaged partition from the unique-color interface used by the LBA degree
serializers and finite-relation decomposition theorems. -/
public theorem of_existsUnique
    (edge_iff_existsUnique : ∀ source target,
      edge source target ↔ ∃! color, layer color source target)
    (layer_sub_edge : ∀ color source target,
      layer color source target → edge source target)
    (rightUnique : ∀ color, Relator.RightUnique (layer color)) :
    TwoPartialFunctionPartition edge layer := by
  refine ⟨?_, ?_, rightUnique⟩
  · intro source target
    constructor
    · intro hedge
      exact ((edge_iff_existsUnique source target).mp hedge).exists
    · rintro ⟨color, hcolor⟩
      exact layer_sub_edge color source target hcolor
  · intro source target leftColor rightColor hleft hright
    have hedge := layer_sub_edge leftColor source target hleft
    obtain ⟨chosen, _hchosen, unique⟩ :=
      (edge_iff_existsUnique source target).mp hedge
    exact (unique leftColor hleft).trans (unique rightColor hright).symm

/-- Forget the cofunctional half of an exact two-partial-bijection partition.  This is the
direct adapter from the two-biunique normal form used by the LBA serializers to the recurrence
interface in this module. -/
public theorem of_existsUnique_biUnique
    (edge_iff_existsUnique : ∀ source target,
      edge source target ↔ ∃! color, layer color source target)
    (layer_sub_edge : ∀ color source target,
      layer color source target → edge source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color)) :
    TwoPartialFunctionPartition edge layer :=
  of_existsUnique edge_iff_existsUnique layer_sub_edge fun color ↦ (biUnique color).2

/-- Every colored edge is an edge of the underlying relation. -/
public theorem layer_sub_edge
    (partition : TwoPartialFunctionPartition edge layer)
    {color : Fin 2} {source target : V}
    (hlayer : layer color source target) :
    edge source target :=
  (partition.edge_iff_exists_layer source target).mpr ⟨color, hlayer⟩

/-- The partition can equivalently be presented using unique existence of an edge color. -/
public theorem edge_iff_existsUnique_layer
    (partition : TwoPartialFunctionPartition edge layer)
    (source target : V) :
    edge source target ↔ ∃! color, layer color source target := by
  constructor
  · intro hedge
    obtain ⟨color, hcolor⟩ :=
      (partition.edge_iff_exists_layer source target).mp hedge
    refine ⟨color, hcolor, ?_⟩
    intro other hother
    exact partition.layer_disjoint hother hcolor
  · rintro ⟨color, hcolor, _⟩
    exact partition.layer_sub_edge hcolor

/-- A source has at most one successor in each fixed layer. -/
public theorem target_eq_of_same_layer
    (partition : TwoPartialFunctionPartition edge layer)
    {color : Fin 2} {source left right : V}
    (hleft : layer color source left) (hright : layer color source right) :
    left = right :=
  partition.rightUnique color hleft hright

/-- Since there are exactly two colors, an underlying edge is in layer zero or layer one. -/
public theorem edge_iff_layer_zero_or_one
    (partition : TwoPartialFunctionPartition edge layer)
    (source target : V) :
    edge source target ↔ layer 0 source target ∨ layer 1 source target := by
  constructor
  · intro hedge
    obtain ⟨color, hcolor⟩ :=
      (partition.edge_iff_exists_layer source target).mp hedge
    fin_cases color
    · exact Or.inl hcolor
    · exact Or.inr hcolor
  · rintro (hzero | hone)
    · exact partition.layer_sub_edge hzero
    · exact partition.layer_sub_edge hone

/-- Two partial-function layers give every vertex at most two underlying successors. -/
public theorem outdegreeAtMostTwo
    (partition : TwoPartialFunctionPartition edge layer) (source : V) :
    Set.encard {target | edge source target} ≤ 2 := by
  have hset :
      {target | edge source target} =
        {target | layer 0 source target} ∪ {target | layer 1 source target} := by
    ext target
    exact partition.edge_iff_layer_zero_or_one source target
  rw [hset]
  calc
    Set.encard ({target | layer 0 source target} ∪
        {target | layer 1 source target}) ≤
        Set.encard {target | layer 0 source target} +
          Set.encard {target | layer 1 source target} :=
      Set.encard_union_le _ _
    _ ≤ 1 + 1 := by
      apply add_le_add
      · apply Set.encard_le_one_iff.mpr
        intro left right hleft hright
        exact partition.rightUnique 0 hleft hright
      · apply Set.encard_le_one_iff.mpr
        intro left right hleft hright
        exact partition.rightUnique 1 hleft hright
    _ = 2 := rfl

/-- If the two layers are also cofunctional, every vertex has at most two underlying
predecessors. -/
public theorem indegreeAtMostTwo
    (partition : TwoPartialFunctionPartition edge layer)
    (leftUnique : ∀ color, Relator.LeftUnique (layer color)) (target : V) :
    Set.encard {source | edge source target} ≤ 2 := by
  have hset :
      {source | edge source target} =
        {source | layer 0 source target} ∪ {source | layer 1 source target} := by
    ext source
    exact partition.edge_iff_layer_zero_or_one source target
  rw [hset]
  calc
    Set.encard ({source | layer 0 source target} ∪
        {source | layer 1 source target}) ≤
        Set.encard {source | layer 0 source target} +
          Set.encard {source | layer 1 source target} :=
      Set.encard_union_le _ _
    _ ≤ 1 + 1 := by
      apply add_le_add
      · apply Set.encard_le_one_iff.mpr
        intro left right hleft hright
        exact leftUnique 0 hleft hright
      · apply Set.encard_le_one_iff.mpr
        intro left right hleft hright
        exact leftUnique 1 hleft hright
    _ = 2 := rfl

/-- An exact two-partial-bijection presentation entails both directed degree-two bounds. -/
public theorem directedDegreeAtMostTwo_of_biUnique
    (partition : TwoPartialFunctionPartition edge layer)
    (biUnique : ∀ color, Relator.BiUnique (layer color)) :
    (∀ source, Set.encard {target | edge source target} ≤ 2) ∧
      ∀ target, Set.encard {source | edge source target} ≤ 2 :=
  ⟨partition.outdegreeAtMostTwo,
    partition.indegreeAtMostTwo (fun color ↦ (biUnique color).1)⟩

end TwoPartialFunctionPartition

/-- Some vertex satisfying `final` is reachable by zero or more `edge` steps. -/
@[expose]
public def CanReach (edge : V → V → Prop) (final : V → Prop) (source : V) : Prop :=
  ∃ target, ReflTransGen edge source target ∧ final target

/-- Reachability is the one-step existential fixed-point recurrence. -/
public theorem canReach_iff
    (edge : V → V → Prop) (final : V → Prop) (source : V) :
    CanReach edge final source ↔
      final source ∨
        ∃ target, edge source target ∧ CanReach edge final target := by
  constructor
  · rintro ⟨target, path, hfinal⟩
    rcases path.cases_head with rfl | ⟨next, hstep, rest⟩
    · exact Or.inl hfinal
    · exact Or.inr ⟨next, hstep, target, rest, hfinal⟩
  · rintro (hfinal | ⟨next, hstep, target, rest, hfinal⟩)
    · exact ⟨source, .refl, hfinal⟩
    · exact ⟨target, rest.head hstep, hfinal⟩

/-- Nonreachability is the corresponding one-step universal invariant. -/
public theorem not_canReach_iff
    (edge : V → V → Prop) (final : V → Prop) (source : V) :
    ¬ CanReach edge final source ↔
      ¬ final source ∧
        ∀ target, edge source target → ¬ CanReach edge final target := by
  rw [canReach_iff]
  constructor
  · intro hreach
    refine ⟨fun hfinal ↦ hreach (Or.inl hfinal), ?_⟩
    intro target hstep htarget
    exact hreach (Or.inr ⟨target, hstep, htarget⟩)
  · rintro ⟨hfinal, htargets⟩ (hhere | ⟨target, hstep, htarget⟩)
    · exact hfinal hhere
    · exact htargets target hstep htarget

/-- With two partial-function layers, reachability branches only over the two layer colors.

The existential target in either colored clause is unique when it exists, by
`TwoPartialFunctionPartition.target_eq_of_same_layer`. -/
public theorem canReach_iff_twoLayers
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (partition : TwoPartialFunctionPartition edge layer)
    (final : V → Prop) (source : V) :
    CanReach edge final source ↔
      final source ∨
        (∃ target, layer 0 source target ∧ CanReach edge final target) ∨
        ∃ target, layer 1 source target ∧ CanReach edge final target := by
  rw [canReach_iff]
  constructor
  · rintro (hfinal | ⟨target, hstep, htarget⟩)
    · exact Or.inl hfinal
    · rcases (partition.edge_iff_layer_zero_or_one source target).mp hstep with
        hzero | hone
      · exact Or.inr (Or.inl ⟨target, hzero, htarget⟩)
      · exact Or.inr (Or.inr ⟨target, hone, htarget⟩)
  · rintro (hfinal | ⟨target, hzero, htarget⟩ | ⟨target, hone, htarget⟩)
    · exact Or.inl hfinal
    · exact Or.inr ⟨target, partition.layer_sub_edge hzero, htarget⟩
    · exact Or.inr ⟨target, partition.layer_sub_edge hone, htarget⟩

/-- With two partial-function layers, nonreachability requires failure through both colors.

This theorem does not turn the two universal clauses into a same-space deterministic procedure;
it only states the exact logical recurrence such a procedure would have to evaluate. -/
public theorem not_canReach_iff_twoLayers
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (partition : TwoPartialFunctionPartition edge layer)
    (final : V → Prop) (source : V) :
    ¬ CanReach edge final source ↔
      ¬ final source ∧
        (∀ target, layer 0 source target → ¬ CanReach edge final target) ∧
        ∀ target, layer 1 source target → ¬ CanReach edge final target := by
  constructor
  · intro hreach
    obtain ⟨hfinal, htargets⟩ := (not_canReach_iff edge final source).mp hreach
    refine ⟨hfinal, ?_, ?_⟩
    · intro target hzero
      exact htargets target (partition.layer_sub_edge hzero)
    · intro target hone
      exact htargets target (partition.layer_sub_edge hone)
  · rintro ⟨hfinal, hzero, hone⟩
    apply (not_canReach_iff edge final source).mpr
    refine ⟨hfinal, ?_⟩
    intro target hstep
    rcases (partition.edge_iff_layer_zero_or_one source target).mp hstep with
      htargetZero | htargetOne
    · exact hzero target htargetZero
    · exact hone target htargetOne

end TwoLayerReachability
