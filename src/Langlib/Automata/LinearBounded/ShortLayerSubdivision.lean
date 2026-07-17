module

public import Langlib.Automata.LinearBounded.LayeredReachability
public import Langlib.Automata.LinearBounded.TwoLayerReachability
import Mathlib.Tactic

@[expose]
public section

/-!
# Short two-layer subdivision

Suppose a relation is exactly partitioned into two bi-unique layers.  Replace every edge
`u → v` of color `c` by the three-edge path

`core u -c→ enter(u,v) -opposite(c)→ exit(u,v) -c→ core v`.

The construction allocates both auxiliary vertices for every ordered pair, independently of
whether the pair is an edge.  This keeps the vertex type finite without requiring decidable
adjacency.  Each new layer remains bi-unique.  Its only possible composable pair has the form
`exit → core → enter`, so no same-color path contains three edges.

Core-to-core reachability is preserved exactly.  If the original relation has a strict
natural-valued rank, multiplying core ranks by three and placing the two auxiliaries in the
intermediate positions gives a strict rank for the subdivision as well.
-/

namespace ShortLayerSubdivision

open Relation

/-- A core vertex or one of the two auxiliary vertices allocated to an ordered pair. -/
public inductive Vertex (V : Type*)
  | core (vertex : V)
  | enter (source target : V)
  | exit (source target : V)
  deriving Fintype

private def vertexEquiv (V : Type*) :
    Vertex V ≃ V ⊕ ((V × V) ⊕ (V × V)) where
  toFun
    | .core vertex => Sum.inl vertex
    | .enter source target => Sum.inr (Sum.inl (source, target))
    | .exit source target => Sum.inr (Sum.inr (source, target))
  invFun
    | Sum.inl vertex => .core vertex
    | Sum.inr (Sum.inl pair) => .enter pair.1 pair.2
    | Sum.inr (Sum.inr pair) => .exit pair.1 pair.2
  left_inv vertex := by cases vertex <;> rfl
  right_inv vertex := by
    rcases vertex with vertex | pair
    · rfl
    · rcases pair with pair | pair <;> rcases pair with ⟨source, target⟩ <;> rfl

/-- Allocating two auxiliary vertices for every ordered pair gives `|V| + 2 * |V|²` vertices. -/
public theorem card_vertex (V : Type*) [Fintype V] :
    Fintype.card (Vertex V) =
      Nat.add (Fintype.card V)
        (Nat.mul 2 (Nat.mul (Fintype.card V) (Fintype.card V))) := by
  rw [Fintype.card_congr (vertexEquiv V)]
  simp
  ring

/-- The other one of two colors. -/
@[expose]
public def opposite (color : Fin 2) : Fin 2 :=
  ⟨1 - color.val, by omega⟩

@[simp]
public theorem opposite_opposite (color : Fin 2) :
    opposite (opposite color) = color := by
  apply Fin.ext
  simp only [opposite]
  omega

public theorem opposite_ne (color : Fin 2) : opposite color ≠ color := by
  intro h
  have hval := congrArg Fin.val h
  simp only [opposite] at hval
  omega

public theorem opposite_injective : Function.Injective opposite := by
  intro left right h
  have := congrArg opposite h
  simpa only [opposite_opposite] using this

/-- The three-edge subdivision of a relation. -/
public inductive Edge {V : Type*} (edge : V → V → Prop) :
    Vertex V → Vertex V → Prop
  | first {source target} (h : edge source target) :
      Edge edge (.core source) (.enter source target)
  | middle {source target} (h : edge source target) :
      Edge edge (.enter source target) (.exit source target)
  | last {source target} (h : edge source target) :
      Edge edge (.exit source target) (.core target)

/-- Color `c` uses the old color `c` on the outside subdivision edges and the opposite old
color on the middle edge. -/
public inductive Layer {V : Type*} (oldLayer : Fin 2 → V → V → Prop)
    (color : Fin 2) : Vertex V → Vertex V → Prop
  | first {source target} (h : oldLayer color source target) :
      Layer oldLayer color (.core source) (.enter source target)
  | middle {source target} (h : oldLayer (opposite color) source target) :
      Layer oldLayer color (.enter source target) (.exit source target)
  | last {source target} (h : oldLayer color source target) :
      Layer oldLayer color (.exit source target) (.core target)

/-- Forget auxiliary positions while projecting exactly one of the three subdivision edges to
the represented original edge. -/
@[expose]
public def project {V : Type*} : Vertex V → V
  | .core vertex => vertex
  | .enter source _ => source
  | .exit _ target => target

/-- The canonical copy of an original vertex. -/
@[expose]
public def core {V : Type*} (vertex : V) : Vertex V := .core vertex

/-- Lift a natural-valued rank through the two intermediate subdivision positions. -/
@[expose]
public def Rank {V : Type*} (rank : V → ℕ) : Vertex V → ℕ
  | .core vertex => Nat.mul 3 (rank vertex)
  | .enter source _ => Nat.add (Nat.mul 3 (rank source)) 1
  | .exit source _ => Nat.add (Nat.mul 3 (rank source)) 2

/-! ## Exact layers and partial bijections -/

/-- Every new colored edge is a genuine subdivision edge.  The input partition's subrelation
field is essential here: unique color on old edges alone would not exclude colored nonedges. -/
public theorem layer_sub_edge {V : Type*}
    {edge : V → V → Prop} {oldLayer : Fin 2 → V → V → Prop}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition edge oldLayer)
    {color : Fin 2} {old new : Vertex V}
    (h : Layer oldLayer color old new) : Edge edge old new := by
  cases h with
  | first h => exact Edge.first (partition.layer_sub_edge h)
  | middle h => exact Edge.middle (partition.layer_sub_edge h)
  | last h => exact Edge.last (partition.layer_sub_edge h)

/-- Each subdivided color is functional when the corresponding old colors are functional. -/
public theorem layer_rightUnique {V : Type*}
    {oldLayer : Fin 2 → V → V → Prop}
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 2) : Relator.RightUnique (Layer oldLayer color) := by
  intro source left right hleft hright
  cases hleft with
  | first hleft =>
      cases hright with
      | first hright =>
          have htarget := (hbiUnique color).2 hleft hright
          cases htarget
          rfl
  | middle hleft =>
      cases hright with
      | middle _ => rfl
  | last hleft =>
      cases hright with
      | last _ => rfl

/-- Each subdivided color is cofunctional when the corresponding old colors are cofunctional. -/
public theorem layer_leftUnique {V : Type*}
    {oldLayer : Fin 2 → V → V → Prop}
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 2) : Relator.LeftUnique (Layer oldLayer color) := by
  intro left right target hleft hright
  cases hleft with
  | first hleft =>
      cases hright with
      | first _ => rfl
  | middle hleft =>
      cases hright with
      | middle _ => rfl
  | last hleft =>
      cases hright with
      | last hright =>
          have hsource := (hbiUnique color).1 hleft hright
          cases hsource
          rfl

/-- Both functional directions are preserved by the short subdivision. -/
public theorem layer_biUnique {V : Type*}
    {oldLayer : Fin 2 → V → V → Prop}
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (color : Fin 2) : Relator.BiUnique (Layer oldLayer color) :=
  ⟨layer_leftUnique hbiUnique color, layer_rightUnique hbiUnique color⟩

/-- The two new layers form an exact two-partial-function partition of the subdivided edge
relation. -/
public theorem twoPartialFunctionPartition {V : Type*}
    {edge : V → V → Prop} {oldLayer : Fin 2 → V → V → Prop}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition edge oldLayer)
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color)) :
    TwoLayerReachability.TwoPartialFunctionPartition
      (Edge edge) (Layer oldLayer) := by
  refine ⟨?_, ?_, layer_rightUnique hbiUnique⟩
  · intro old new
    constructor
    · intro h
      cases h with
      | first h =>
          obtain ⟨color, hcolor⟩ :=
            (partition.edge_iff_exists_layer _ _).mp h
          exact ⟨color, Layer.first hcolor⟩
      | middle h =>
          obtain ⟨color, hcolor⟩ :=
            (partition.edge_iff_exists_layer _ _).mp h
          refine ⟨opposite color, Layer.middle ?_⟩
          simpa only [opposite_opposite] using hcolor
      | last h =>
          obtain ⟨color, hcolor⟩ :=
            (partition.edge_iff_exists_layer _ _).mp h
          exact ⟨color, Layer.last hcolor⟩
    · rintro ⟨color, hcolor⟩
      exact layer_sub_edge partition hcolor
  · intro old new leftColor rightColor hleft hright
    cases hleft with
    | first hleft =>
        cases hright with
        | first hright => exact partition.layer_disjoint hleft hright
    | middle hleft =>
        cases hright with
        | middle hright =>
            exact opposite_injective (partition.layer_disjoint hleft hright)
    | last hleft =>
        cases hright with
        | last hright => exact partition.layer_disjoint hleft hright

/-- Every subdivision edge has one and only one new color. -/
public theorem edge_iff_existsUnique_layer {V : Type*}
    {edge : V → V → Prop} {oldLayer : Fin 2 → V → V → Prop}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition edge oldLayer)
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (old new : Vertex V) :
    Edge edge old new ↔ ∃! color, Layer oldLayer color old new :=
  (twoPartialFunctionPartition partition hbiUnique).edge_iff_existsUnique_layer old new

/-! ## Short monochromatic components and directed degree -/

/-- A relation contains no directed path of three composable edges. -/
public def PathLengthAtMostTwo {W : Type*} (relation : W → W → Prop) : Prop :=
  ∀ ⦃a b c d⦄, relation a b → relation b c → relation c d → False

/-- No new color contains three composable edges.  Outside-to-middle and middle-to-outside
compositions would assign both old colors to one old edge.  The only possible monochromatic pair
is `exit → core → enter`, and it cannot be extended by a third edge of that color. -/
public theorem layer_pathLengthAtMostTwo {V : Type*}
    {edge : V → V → Prop} {oldLayer : Fin 2 → V → V → Prop}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition edge oldLayer)
    (color : Fin 2) : PathLengthAtMostTwo (Layer oldLayer color) := by
  intro a b c d hab hbc hcd
  cases hab with
  | first hab =>
      cases hbc with
      | middle hbc =>
          exact opposite_ne color (partition.layer_disjoint hbc hab)
  | middle hab =>
      cases hbc with
      | last hbc =>
          exact opposite_ne color (partition.layer_disjoint hab hbc)
  | last hab =>
      cases hbc with
      | first hbc =>
          cases hcd with
          | middle hcd =>
              exact opposite_ne color (partition.layer_disjoint hcd hbc)

/-- Two exact bi-unique layers bound both directed degrees of the subdivision by two. -/
public theorem directedDegreeAtMostTwo {V : Type*}
    {edge : V → V → Prop} {oldLayer : Fin 2 → V → V → Prop}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition edge oldLayer)
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color)) :
    LayeredReachability.DirectedDegreeAtMost 2 (Edge edge) := by
  have hdegree :=
    (twoPartialFunctionPartition partition hbiUnique).directedDegreeAtMostTwo_of_biUnique
      (layer_biUnique hbiUnique)
  simpa only [LayeredReachability.DirectedDegreeAtMost,
    LayeredReachability.OutdegreeAtMost, LayeredReachability.IndegreeAtMost] using hdegree

/-! ## Exact preservation of core reachability -/

/-- One original edge expands to its three-edge subdivision path. -/
public theorem reaches_core_of_edge {V : Type*}
    {edge : V → V → Prop} {source target : V}
    (h : edge source target) :
    ReflTransGen (Edge edge) (core source) (core target) := by
  exact ((ReflTransGen.single (Edge.first h)).trans
    (ReflTransGen.single (Edge.middle h))).trans
      (ReflTransGen.single (Edge.last h))

/-- Every original path lifts to a path between the corresponding core vertices. -/
public theorem reaches_core_of_reaches {V : Type*}
    {edge : V → V → Prop} {source target : V}
    (h : ReflTransGen edge source target) :
    ReflTransGen (Edge edge) (core source) (core target) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans (reaches_core_of_edge hstep)

/-- A subdivision edge either stutters under projection or projects to its represented original
edge. -/
public theorem project_edge {V : Type*}
    {edge : V → V → Prop} {old new : Vertex V}
    (h : Edge edge old new) :
    project old = project new ∨ edge (project old) (project new) := by
  cases h with
  | first _ => exact Or.inl rfl
  | middle h => exact Or.inr h
  | last _ => exact Or.inl rfl

/-- Projecting a subdivided path deletes the two stuttering edge kinds and retains every
represented original edge. -/
public theorem reaches_project_of_reaches {V : Type*}
    {edge : V → V → Prop} {old new : Vertex V}
    (h : ReflTransGen (Edge edge) old new) :
    ReflTransGen edge (project old) (project new) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases project_edge hstep with heq | hedge
      · simpa only [heq] using ih
      · exact ih.tail hedge

/-- Original reachability is equivalent to reachability between the designated core copies. -/
public theorem reaches_iff {V : Type*}
    (edge : V → V → Prop) (source target : V) :
    ReflTransGen edge source target ↔
      ReflTransGen (Edge edge) (core source) (core target) := by
  constructor
  · exact reaches_core_of_reaches
  · intro h
    simpa only [core, project] using reaches_project_of_reaches h

/-! ## Strict ranks and acyclicity -/

/-- A supplied strict natural-valued rank remains strict after subdivision. -/
public theorem rank_lt_of_edge {V : Type*}
    {edge : V → V → Prop} {rank : V → ℕ}
    (hstrict : ∀ ⦃source target⦄, edge source target → rank source < rank target)
    {old new : Vertex V} (h : Edge edge old new) :
    Rank rank old < Rank rank new := by
  cases h with
  | first _ => simp [Rank]
  | middle _ => simp [Rank]
  | last h =>
      have hbase := hstrict h
      simp [Rank]
      omega

/-- The lifted rank strictly increases along every nonempty subdivided path. -/
public theorem rank_lt_of_transGen {V : Type*}
    {edge : V → V → Prop} {rank : V → ℕ}
    (hstrict : ∀ ⦃source target⦄, edge source target → rank source < rank target)
    {old new : Vertex V} (h : TransGen (Edge edge) old new) :
    Rank rank old < Rank rank new := by
  induction h with
  | single hstep => exact rank_lt_of_edge hstrict hstep
  | tail hpath hstep ih => exact ih.trans (rank_lt_of_edge hstrict hstep)

/-- A relation carrying a strict natural-valued rank remains acyclic after subdivision. -/
public theorem acyclic_of_rank {V : Type*}
    {edge : V → V → Prop} {rank : V → ℕ}
    (hstrict : ∀ ⦃source target⦄, edge source target → rank source < rank target) :
    ∀ vertex : Vertex V, ¬ TransGen (Edge edge) vertex vertex := by
  intro vertex hcycle
  exact (Nat.lt_irrefl (Rank rank vertex)) (rank_lt_of_transGen hstrict hcycle)

/-! ## Packaged construction -/

/-- The complete short-layer subdivision theorem from a packaged exact two-color partition. -/
public theorem subdivision_properties {V : Type*}
    {edge : V → V → Prop} {oldLayer : Fin 2 → V → V → Prop}
    {rank : V → ℕ}
    (partition : TwoLayerReachability.TwoPartialFunctionPartition edge oldLayer)
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (hstrict : ∀ ⦃old new⦄, edge old new → rank old < rank new)
    (source target : V) :
    (ReflTransGen edge source target ↔
      ReflTransGen (Edge edge) (core source) (core target)) ∧
      (∀ old new, Edge edge old new ↔
        ∃! color, Layer oldLayer color old new) ∧
      (∀ color old new, Layer oldLayer color old new → Edge edge old new) ∧
      (∀ color, Relator.BiUnique (Layer oldLayer color)) ∧
      (∀ color, PathLengthAtMostTwo (Layer oldLayer color)) ∧
      LayeredReachability.DirectedDegreeAtMost 2 (Edge edge) ∧
      (∀ ⦃old new⦄, Edge edge old new → Rank rank old < Rank rank new) ∧
      (∀ vertex, ¬ TransGen (Edge edge) vertex vertex) := by
  exact ⟨reaches_iff edge source target,
    edge_iff_existsUnique_layer partition hbiUnique,
    fun color _ _ h ↦ layer_sub_edge partition h,
    layer_biUnique hbiUnique,
    layer_pathLengthAtMostTwo partition,
    directedDegreeAtMostTwo partition hbiUnique,
    (fun ⦃old new⦄ h ↦ rank_lt_of_edge hstrict h),
    acyclic_of_rank hstrict⟩

/-- The same packaged theorem in the explicit unique-cover/subrelation interface used by the
finite serializers.  Both assumptions are retained: unique cover on genuine edges does not by
itself rule out colored nonedges. -/
public theorem subdivision_properties_of_existsUnique {V : Type*}
    {edge : V → V → Prop} {oldLayer : Fin 2 → V → V → Prop}
    {rank : V → ℕ}
    (edge_iff_existsUnique : ∀ old new,
      edge old new ↔ ∃! color, oldLayer color old new)
    (oldLayer_sub_edge : ∀ color old new,
      oldLayer color old new → edge old new)
    (hbiUnique : ∀ color, Relator.BiUnique (oldLayer color))
    (hstrict : ∀ ⦃old new⦄, edge old new → rank old < rank new)
    (source target : V) :
    (ReflTransGen edge source target ↔
      ReflTransGen (Edge edge) (core source) (core target)) ∧
      (∀ old new, Edge edge old new ↔
        ∃! color, Layer oldLayer color old new) ∧
      (∀ color old new, Layer oldLayer color old new → Edge edge old new) ∧
      (∀ color, Relator.BiUnique (Layer oldLayer color)) ∧
      (∀ color, PathLengthAtMostTwo (Layer oldLayer color)) ∧
      LayeredReachability.DirectedDegreeAtMost 2 (Edge edge) ∧
      (∀ ⦃old new⦄, Edge edge old new → Rank rank old < Rank rank new) ∧
      (∀ vertex, ¬ TransGen (Edge edge) vertex vertex) := by
  let partition : TwoLayerReachability.TwoPartialFunctionPartition edge oldLayer :=
    TwoLayerReachability.TwoPartialFunctionPartition.of_existsUnique_biUnique
      edge_iff_existsUnique oldLayer_sub_edge hbiUnique
  exact subdivision_properties partition hbiUnique hstrict source target

end ShortLayerSubdivision

end
