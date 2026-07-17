module

public import Langlib.Automata.LinearBounded.ExplicitDegreeTwoReachability
public import Langlib.Automata.LinearBounded.ShortLayerSubdivision

@[expose]
public section

/-!
# Arbitrary finite reachability through two short linear layers

This module composes the explicit single-target clock serializer with the generic three-edge
short-layer subdivision.  The first construction gives an acyclic finite relation with an exact
two-bi-unique coloring.  The second replaces each colored edge by the color pattern
`c, opposite(c), c`, making every monochromatic directed path have length at most two while
preserving one designated source and target.

The structural numbering inherited from `ExplicitDegreeTwoReachability` is noncomputable.  The
result is therefore a finite mathematical reduction, not a claimed effective or logspace
encoding procedure.
-/

namespace ShortLayerSubdivisionReachability

open Relation

/-- Vertices after subdividing the clock-serialized finite graph. -/
public abbrev Vertex (V : Type*) [Fintype V] :=
  ShortLayerSubdivision.Vertex
    (ExplicitDegreeTwoReachability.ClockSerializedVertex V)

/-- The final subdivided relation. -/
public noncomputable def Edge {V : Type*} [Fintype V]
    (edge : V → V → Prop) : Vertex V → Vertex V → Prop :=
  ShortLayerSubdivision.Edge
    (ExplicitDegreeTwoReachability.clockSerializedEdge edge)

/-- The final two supplied layers. -/
public noncomputable def Layer {V : Type*} [Fintype V]
    (edge : V → V → Prop) (color : Fin 2) :
    Vertex V → Vertex V → Prop :=
  ShortLayerSubdivision.Layer
    (ExplicitDegreeTwoReachability.clockSerializedLayer edge) color

/-- The one designated source in the final graph. -/
public noncomputable def source {V : Type*} [Fintype V] (vertex : V) : Vertex V :=
  ShortLayerSubdivision.core
    (ExplicitDegreeTwoReachability.clockSerializedSource vertex)

/-- The one designated target in the final graph. -/
public noncomputable def target {V : Type*} [Fintype V] (vertex : V) : Vertex V :=
  ShortLayerSubdivision.core
    (ExplicitDegreeTwoReachability.clockSerializedTarget vertex)

/-- The strict rank on the clock serializer before the final short-layer subdivision. -/
public noncomputable def clockSerializedRank (V : Type*) [Fintype V] :
    ExplicitDegreeTwoReachability.ClockSerializedVertex V → ℕ :=
  ExplicitDegreeTwoReachability.liftedRank
    (fun index ↦
      ((ExplicitDegreeTwoReachability.clockNumbering V).symm index).2.val)

/-- The strict rank on the final subdivided graph. -/
public noncomputable def Rank (V : Type*) [Fintype V] : Vertex V → ℕ :=
  ShortLayerSubdivision.Rank (clockSerializedRank V)

/-- The final graph still has an explicit finite vertex type. -/
public theorem card_vertex (V : Type*) [Fintype V] :
    Fintype.card (Vertex V) =
      Nat.add
        (Fintype.card (ExplicitDegreeTwoReachability.ClockSerializedVertex V))
        (Nat.mul 2
          (Nat.mul
            (Fintype.card (ExplicitDegreeTwoReachability.ClockSerializedVertex V))
            (Fintype.card (ExplicitDegreeTwoReachability.ClockSerializedVertex V)))) :=
  ShortLayerSubdivision.card_vertex _

private theorem clockSerializedRank_lt {V : Type*} [Fintype V]
    {edge : V → V → Prop}
    {old new : ExplicitDegreeTwoReachability.ClockSerializedVertex V}
    (h : ExplicitDegreeTwoReachability.clockSerializedEdge edge old new) :
    clockSerializedRank V old < clockSerializedRank V new := by
  apply ExplicitDegreeTwoReachability.liftedRank_lt_of_edge
    (fun index ↦
      ((ExplicitDegreeTwoReachability.clockNumbering V).symm index).2.val)
    (fun hstep ↦ LayeredReachability.edge_layer_lt hstep)
  exact h

/-- Arbitrary finite directed reachability reduces to one designated source and target in an
acyclic degree-two relation that is exactly covered by two bi-unique layers, each with directed
path length at most two.

The output additionally exposes the strict natural-valued rank witnessing acyclicity. -/
public theorem finiteReachability_singleTarget_twoLinearTwoDiforests
    {V : Type*} [Fintype V]
    (edge : V → V → Prop) (start finish : V) :
    (ReflTransGen edge start finish ↔
      ReflTransGen (Edge edge) (source start) (target finish)) ∧
      (∀ old new, Edge edge old new ↔
        ∃! color, Layer edge color old new) ∧
      (∀ color old new, Layer edge color old new → Edge edge old new) ∧
      (∀ color, Relator.BiUnique (Layer edge color)) ∧
      (∀ color,
        ShortLayerSubdivision.PathLengthAtMostTwo (Layer edge color)) ∧
      LayeredReachability.DirectedDegreeAtMost 2 (Edge edge) ∧
      (∀ ⦃old new⦄, Edge edge old new → Rank V old < Rank V new) ∧
      (∀ vertex, ¬ TransGen (Edge edge) vertex vertex) := by
  have hproperties :=
    ShortLayerSubdivision.subdivision_properties_of_existsUnique
      (ExplicitDegreeTwoReachability.clockSerialized_edge_iff_existsUnique_layer edge)
      (ExplicitDegreeTwoReachability.clockSerialized_layer_sub_edge edge)
      (ExplicitDegreeTwoReachability.clockSerialized_layer_biUnique edge)
      (@clockSerializedRank_lt V _ edge)
      (ExplicitDegreeTwoReachability.clockSerializedSource start)
      (ExplicitDegreeTwoReachability.clockSerializedTarget finish)
  rcases hproperties with
    ⟨hshortReach, hexact, hsub, hbiUnique, hshort, hdegree, hrank, hacyclic⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hreach :=
      (ExplicitDegreeTwoReachability.reaches_iff_clockSerialized edge start finish).trans
        hshortReach
    simpa only [Edge, source, target] using hreach
  · simpa only [Edge, Layer] using hexact
  · simpa only [Edge, Layer] using hsub
  · simpa only [Layer] using hbiUnique
  · simpa only [Layer] using hshort
  · simpa only [Edge] using hdegree
  · simpa only [Edge, Rank] using hrank
  · simpa only [Edge] using hacyclic

end ShortLayerSubdivisionReachability

end
