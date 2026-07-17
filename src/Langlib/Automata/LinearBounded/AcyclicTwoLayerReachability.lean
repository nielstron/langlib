module

public import Langlib.Automata.LinearBounded.LayeredReachability
public import Langlib.Automata.LinearBounded.PartialBijectionDecomposition

@[expose]
public section

/-!
# Acyclic two-layer normal form for degree-two reachability

Strict clock layering turns finite directed reachability into reachability in a DAG without
increasing either directed degree.  Every relation with at most two successors and at most two
predecessors is, in turn, exactly partitioned into two partial bijections.  This module packages
those two facts into one theorem.

The input relation must already have both directed degrees at most two.  Moreover, strict
layering preserves reachability by allowing the target to occur at *some* clock layer.  The
result is therefore a multi-target reduction to the clock copies of the original target, not a
single-distinguished-target reduction.  Adding padding would recover one prescribed final layer
but could raise each directed degree by one.

The two-layer partition is structural: no decidable adjacency relation, effective coloring, or
uniform algorithm for choosing the layers is asserted.
-/

namespace AcyclicTwoLayerReachability

open Relation

/-- A finite degree-two reachability instance has an equivalent strict-clock presentation that
is acyclic, remains degree two, and is exactly partitioned into two bi-unique layers.

The target condition ranges over all valid clock copies of `target`.  Thus this theorem does not
by itself give a reduction to reachability of one distinguished target vertex. -/
public theorem exists_twoBiUnique_strictLayering
    {V : Type*} [Fintype V]
    (edge : V → V → Prop)
    (hdegree : LayeredReachability.DirectedDegreeAtMost 2 edge)
    (source target : V) :
    ∃ layer : Fin 2 →
        LayeredReachability.Vertex V → LayeredReachability.Vertex V → Prop,
      (ReflTransGen edge source target ↔
        ∃ clock,
          ∃ hclock : clock ≤ Fintype.card V,
            ReflTransGen (LayeredReachability.StrictEdge edge)
              (LayeredReachability.bottom source)
              (LayeredReachability.atLayer target clock hclock)) ∧
      (∀ vertex, ¬ TransGen (LayeredReachability.StrictEdge edge) vertex vertex) ∧
      LayeredReachability.DirectedDegreeAtMost 2
        (LayeredReachability.StrictEdge edge) ∧
      (∀ old new, LayeredReachability.StrictEdge edge old new ↔
        ∃! color, layer color old new) ∧
      (∀ color old new, layer color old new →
        LayeredReachability.StrictEdge edge old new) ∧
      ∀ color, Relator.BiUnique (layer color) := by
  have hclockDegree :
      LayeredReachability.DirectedDegreeAtMost 2
        (LayeredReachability.StrictEdge edge) :=
    LayeredReachability.strictEdge_directedDegreeAtMost hdegree
  obtain ⟨layer, hexact, hsub, hbiUnique⟩ :=
    PartialBijectionDecomposition.exists_two_biUnique_partition
      (LayeredReachability.StrictEdge edge) hclockDegree.1 hclockDegree.2
  exact ⟨layer,
    LayeredReachability.reaches_iff_exists_strictLayer_reaches edge source target,
    LayeredReachability.strict_no_transGen_self edge,
    hclockDegree, hexact, hsub, hbiUnique⟩

end AcyclicTwoLayerReachability

end
