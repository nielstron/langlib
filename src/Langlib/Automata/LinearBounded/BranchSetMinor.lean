module

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Relation

@[expose]
public section

/-!
# Branch-set models of relation minors

This file records the elementary branch-set certificate used by graph-minor arguments without
depending on a simple-graph minor library.  A vertex of the small relation is represented by a
nonempty, connected, pairwise-disjoint set of vertices of the large relation, and every small
edge has an edge between the corresponding branch sets.

The large relation may be directed.  `BranchSetMinorModel` deliberately takes its symmetric
closure before asking for connectivity and represented edges, so it describes a minor of the
underlying undirected relation.
-/

namespace Relation

/-- Add the reverse of every edge to a relation. -/
@[expose]
public def SymmetricClosure {V : Type u} (edge : V → V → Prop) : V → V → Prop :=
  fun source target => edge source target ∨ edge target source

/-- Restrict both endpoints of a relation to a set. -/
@[expose]
public def Restricted {V : Type u} (vertices : Set V) (edge : V → V → Prop) :
    V → V → Prop :=
  fun source target => source ∈ vertices ∧ edge source target ∧ target ∈ vertices

/-- A branch-set certificate that `smallEdge` is a minor of the underlying undirected relation
of `largeEdge`.

No simplicity assumptions are imposed on either relation.  When both are adjacency relations of
simple graphs, these are exactly the usual branch-set data for a graph minor. -/
public structure BranchSetMinorModel {Small : Type u} {Large : Type v}
    (smallEdge : Small → Small → Prop) (largeEdge : Large → Large → Prop) where
  /-- The connected branch set representing each small vertex. -/
  branchSet : Small → Set Large
  /-- Every branch set has a representative. -/
  nonempty : ∀ vertex, (branchSet vertex).Nonempty
  /-- Distinct small vertices have disjoint branch sets. -/
  disjoint : ∀ {left right}, left ≠ right → Disjoint (branchSet left) (branchSet right)
  /-- Every two representatives of one branch set are connected inside that branch set. -/
  connected : ∀ vertex {source target}, source ∈ branchSet vertex →
    target ∈ branchSet vertex →
      ReflTransGen
        (Restricted (branchSet vertex) (SymmetricClosure largeEdge)) source target
  /-- Every small edge is represented by an edge between the corresponding branch sets. -/
  map_edge : ∀ {source target}, smallEdge source target →
    ∃ sourceRep ∈ branchSet source, ∃ targetRep ∈ branchSet target,
      SymmetricClosure largeEdge sourceRep targetRep

end Relation

end
