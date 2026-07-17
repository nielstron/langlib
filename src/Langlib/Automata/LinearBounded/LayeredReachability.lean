module

public import Langlib.Automata.LinearBounded.FiniteReachabilityCounting
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

@[expose]
public section

/-!
# Layering finite directed reachability

Any finite directed reachability instance can be made acyclic by adjoining a clock layer.
For a graph on `V`, the layered graph has vertices

`V × Fin (Fintype.card V + 1)`.

Every edge advances the clock by exactly one and either follows an original edge or keeps the
underlying vertex unchanged.  The equality alternative is the padding step needed to turn a
path of at most `Fintype.card V` genuine edges into a path ending at the top layer.

The layered relation is acyclic because its clock strictly increases.  Nevertheless, reaching
`target` from `source` in the original graph is equivalent to reaching `(target, |V|)` from
`(source, 0)` in the layered graph.  Thus acyclicity or a rigid layer structure alone does not
make finite directed reachability substantially easier.
-/

namespace LayeredReachability

open Relation
open FiniteReachabilityCounting

variable {V : Type*} [Fintype V]

/-- A vertex together with a clock ranging from zero through `Fintype.card V`. -/
public abbrev Vertex (V : Type*) [Fintype V] :=
  V × Fin (Fintype.card V + 1)

/-- Place an underlying vertex at a specified valid clock layer. -/
@[expose]
public def atLayer (vertex : V) (layer : ℕ) (hlayer : layer ≤ Fintype.card V) :
    Vertex V :=
  (vertex, ⟨layer, by omega⟩)

/-- Place an underlying vertex at clock layer zero. -/
@[expose]
public def bottom (vertex : V) : Vertex V :=
  atLayer vertex 0 (Nat.zero_le _)

/-- Place an underlying vertex at the final clock layer `Fintype.card V`. -/
@[expose]
public def top (vertex : V) : Vertex V :=
  atLayer vertex (Fintype.card V) (Nat.le_refl _)

/-- The layered version of an edge relation.  A layered edge advances the clock by one and
either follows an original edge or pads the path by keeping its underlying vertex fixed. -/
@[expose]
public def Edge (edge : V → V → Prop) : Vertex V → Vertex V → Prop :=
  fun old new =>
    new.2.val = old.2.val + 1 ∧
      (old.1 = new.1 ∨ edge old.1 new.1)

/-- Strict layering, without padding edges.  This variant cannot increase either directed
degree: every successor or predecessor projects injectively to one in the original graph.  Its
target condition is therefore "the target occurs at some layer", rather than requiring the
target to occur at the final layer. -/
@[expose]
public def StrictEdge (edge : V → V → Prop) : Vertex V → Vertex V → Prop :=
  fun old new =>
    new.2.val = old.2.val + 1 ∧ edge old.1 new.1

/-- Forget the orientation of a layered edge. -/
@[expose]
public def UndirectedEdge (edge : V → V → Prop) : Vertex V → Vertex V → Prop :=
  fun old new => Edge edge old new ∨ Edge edge new old

/-- A uniform bound on the number of distinct immediate successors. -/
public def OutdegreeAtMost {W : Type*} (bound : ℕ∞) (edge : W → W → Prop) : Prop :=
  ∀ old, Set.encard {new | edge old new} ≤ bound

/-- A uniform bound on the number of distinct immediate predecessors. -/
public def IndegreeAtMost {W : Type*} (bound : ℕ∞) (edge : W → W → Prop) : Prop :=
  ∀ new, Set.encard {old | edge old new} ≤ bound

/-- Simultaneous uniform bounds on both directed degrees. -/
public def DirectedDegreeAtMost {W : Type*} (bound : ℕ∞) (edge : W → W → Prop) : Prop :=
  OutdegreeAtMost bound edge ∧ IndegreeAtMost bound edge

/-- Every layered edge strictly increases its clock coordinate. -/
public theorem edge_layer_lt {edge : V → V → Prop} {old new : Vertex V}
    (h : Edge edge old new) :
    old.2.val < new.2.val := by
  rcases h with ⟨hlayer, _⟩
  omega

/-- Every nonempty layered path strictly increases its clock coordinate. -/
public theorem transGen_layer_lt {edge : V → V → Prop} {old new : Vertex V}
    (h : TransGen (Edge edge) old new) :
    old.2.val < new.2.val := by
  induction h with
  | single hstep =>
      exact edge_layer_lt hstep
  | tail hpath hstep ih =>
      exact ih.trans (edge_layer_lt hstep)

/-- The transitive closure of the layered relation is irreflexive: the layered graph has no
nontrivial directed cycle. -/
public theorem no_transGen_self (edge : V → V → Prop) (vertex : Vertex V) :
    ¬ TransGen (Edge edge) vertex vertex := by
  intro hcycle
  exact (Nat.lt_irrefl vertex.2.val) (transGen_layer_lt hcycle)

/-- Every strict layered edge increases its clock coordinate. -/
public theorem strictEdge_layer_lt {edge : V → V → Prop} {old new : Vertex V}
    (h : StrictEdge edge old new) :
    old.2.val < new.2.val := by
  rcases h with ⟨hlayer, _⟩
  omega

/-- Every nonempty path in the strict layered graph increases its clock coordinate. -/
public theorem strictTransGen_layer_lt {edge : V → V → Prop} {old new : Vertex V}
    (h : TransGen (StrictEdge edge) old new) :
    old.2.val < new.2.val := by
  induction h with
  | single hstep =>
      exact strictEdge_layer_lt hstep
  | tail hpath hstep ih =>
      exact ih.trans (strictEdge_layer_lt hstep)

/-- The strict layered graph is acyclic. -/
public theorem strict_no_transGen_self (edge : V → V → Prop) (vertex : Vertex V) :
    ¬ TransGen (StrictEdge edge) vertex vertex := by
  intro hcycle
  exact (Nat.lt_irrefl vertex.2.val) (strictTransGen_layer_lt hcycle)

/-- Strict layering cannot increase the number of distinct immediate successors. -/
public theorem strictEdge_outdegree_le (edge : V → V → Prop) (old : Vertex V) :
    Set.encard {new | StrictEdge edge old new} ≤
      Set.encard {vertex | edge old.1 vertex} := by
  apply Set.encard_le_encard_of_injOn (f := fun new : Vertex V => new.1)
  · intro new hnew
    exact hnew.2
  · intro left hleft right hright hprojection
    apply Prod.ext
    · exact hprojection
    · apply Fin.ext
      exact hleft.1.trans hright.1.symm

/-- Strict layering cannot increase the number of distinct immediate predecessors. -/
public theorem strictEdge_indegree_le (edge : V → V → Prop) (new : Vertex V) :
    Set.encard {old | StrictEdge edge old new} ≤
      Set.encard {vertex | edge vertex new.1} := by
  apply Set.encard_le_encard_of_injOn (f := fun old : Vertex V => old.1)
  · intro old hold
    exact hold.2
  · intro left hleft right hright hprojection
    apply Prod.ext
    · exact hprojection
    · apply Fin.ext
      have hleftLayer := hleft.1
      have hrightLayer := hright.1
      omega

/-- Strict layering preserves every uniform outdegree bound, not just the degree-two case. -/
public theorem strictEdge_outdegreeAtMost {bound : ℕ∞} {edge : V → V → Prop}
    (hbound : OutdegreeAtMost bound edge) :
    OutdegreeAtMost bound (StrictEdge edge) := by
  intro old
  exact (strictEdge_outdegree_le edge old).trans (hbound old.1)

/-- Strict layering preserves every uniform indegree bound. -/
public theorem strictEdge_indegreeAtMost {bound : ℕ∞} {edge : V → V → Prop}
    (hbound : IndegreeAtMost bound edge) :
    IndegreeAtMost bound (StrictEdge edge) := by
  intro new
  exact (strictEdge_indegree_le edge new).trans (hbound new.1)

/-- Strict layering simultaneously preserves arbitrary bounds on both directed degrees. -/
public theorem strictEdge_directedDegreeAtMost {bound : ℕ∞} {edge : V → V → Prop}
    (hbound : DirectedDegreeAtMost bound edge) :
    DirectedDegreeAtMost bound (StrictEdge edge) :=
  ⟨strictEdge_outdegreeAtMost hbound.1, strictEdge_indegreeAtMost hbound.2⟩

/-- A layered reachable path whose endpoints have the same clock layer must be the reflexive
zero-step path. -/
public theorem eq_of_reaches_of_layer_eq {edge : V → V → Prop} {old new : Vertex V}
    (hreach : ReflTransGen (Edge edge) old new)
    (hlayer : old.2.val = new.2.val) :
    old = new := by
  rcases (reflTransGen_iff_eq_or_transGen.mp hreach) with heq | hpath
  · exact heq.symm
  · have hlt := transGen_layer_lt hpath
    omega

/-- An exactly fuel-indexed padded path lifts to a path through the corresponding clock
layers. -/
public theorem reaches_atLayer_of_paddedPath (edge : V → V → Prop)
    {source target : V} {steps : ℕ} (hsteps : steps ≤ Fintype.card V)
    (hpath : PaddedPath edge source steps target) :
    ReflTransGen (Edge edge)
      (bottom source) (atLayer target steps hsteps) := by
  induction hpath with
  | zero =>
      exact .refl
  | @succ steps old new hpath hmove ih =>
      have hsteps' : steps ≤ Fintype.card V := by omega
      have hreach := ih hsteps'
      apply hreach.tail
      exact ⟨rfl, hmove⟩

/-- Projecting a layered path from the bottom recovers an exactly indexed padded path in the
underlying graph. -/
public theorem paddedPath_of_reaches_bottom (edge : V → V → Prop)
    {source : V} {target : Vertex V}
    (hreach : ReflTransGen (Edge edge) (bottom source) target) :
    PaddedPath edge source target.2.val target.1 := by
  induction hreach with
  | refl =>
      exact .zero
  | tail hreach hstep ih =>
      rw [hstep.1]
      exact .succ ih hstep.2

/-- Delete every padding step from a padded path and lift the remaining genuine edges through
strict clock layers. -/
public theorem exists_strictReaches_of_paddedPath (edge : V → V → Prop)
    {source target : V} {steps : ℕ} (hsteps : steps ≤ Fintype.card V)
    (hpath : PaddedPath edge source steps target) :
    ∃ used, ∃ hused : used ≤ steps,
      ReflTransGen (StrictEdge edge)
        (bottom source) (atLayer target used (hused.trans hsteps)) := by
  induction hpath with
  | zero =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      exact .refl
  | @succ k old new hpath hmove ih =>
      have hk : k ≤ Fintype.card V := by omega
      rcases ih hk with ⟨used, hused, hreach⟩
      rcases hmove with rfl | hedge
      · refine ⟨used, hused.trans (Nat.le_succ k), ?_⟩
        simpa only [bottom, atLayer] using hreach
      · have husedSucc : used + 1 ≤ k + 1 := Nat.add_le_add_right hused 1
        have husedCard : used + 1 ≤ Fintype.card V :=
          husedSucc.trans hsteps
        refine ⟨used + 1, husedSucc, ?_⟩
        have hstep :
            StrictEdge edge
              (atLayer old used (hused.trans hk))
              (atLayer new (used + 1) husedCard) := by
          exact ⟨by simp [atLayer], hedge⟩
        have := hreach.tail hstep
        simpa only [bottom, atLayer] using this

/-- Original reachability is equivalent to strict-layer reachability of the target at some
clock layer.  Unlike final-layer padding, this simultaneous acyclicization preserves both
directed degree bounds. -/
public theorem reaches_iff_exists_strictLayer_reaches (edge : V → V → Prop)
    (source target : V) :
    ReflTransGen edge source target ↔
      ∃ layer, ∃ hlayer : layer ≤ Fintype.card V,
        ReflTransGen (StrictEdge edge)
          (bottom source) (atLayer target layer hlayer) := by
  classical
  letI : DecidableRel edge := Classical.decRel edge
  constructor
  · intro hreach
    have hmem :
        target ∈ reached edge source (Fintype.card V) :=
      (mem_reached_card_iff (edge := edge) (source := source)).2 hreach
    have hpath :
        PaddedPath edge source (Fintype.card V) target :=
      (mem_reached_iff_paddedPath (edge := edge) (source := source)).1 hmem
    exact exists_strictReaches_of_paddedPath edge (Nat.le_refl _) hpath
  · rintro ⟨layer, hlayer, hreach⟩
    have hprojected :=
      hreach.lift (fun vertex : Vertex V => vertex.1)
        (fun _ _ hstep => hstep.2)
    simpa only [bottom, atLayer] using hprojected

/-- An undirected layered edge can increase the layer by at most one. -/
public theorem undirectedEdge_layer_le {edge : V → V → Prop}
    {old new : Vertex V} (h : UndirectedEdge edge old new) :
    new.2.val ≤ old.2.val + 1 := by
  rcases h with hforward | hbackward
  · rcases hforward with ⟨hlayer, _⟩
    omega
  · rcases hbackward with ⟨hlayer, _⟩
    omega

/-- After `steps` moves in the underlying undirected layered graph, the layer can have
increased by at most `steps`.  `PaddedPath` also permits stuttering, which satisfies the same
bound. -/
public theorem paddedUndirectedPath_layer_le {edge : V → V → Prop}
    {start finish : Vertex V} {steps : ℕ}
    (hpath : PaddedPath (UndirectedEdge edge) start steps finish) :
    finish.2.val ≤ start.2.val + steps := by
  induction hpath with
  | zero =>
      simp
  | @succ k old new hpath hmove ih =>
      rcases hmove with rfl | hstep
      · omega
      · have hstepLe := undirectedEdge_layer_le hstep
        omega

/-- No walk in the underlying undirected layered graph can travel from the bottom to the top
in fewer than `|V|` moves. -/
public theorem no_undirectedPaddedPath_bottom_top_of_lt_card
    {edge : V → V → Prop} {source target : V} {steps : ℕ}
    (hsteps : steps < Fintype.card V) :
    ¬ PaddedPath (UndirectedEdge edge) (bottom source) steps (top target) := by
  intro hpath
  have hlayer := paddedUndirectedPath_layer_le hpath
  simp [top, bottom, atLayer] at hlayer
  omega

/-- A padded undirected layered path attaining the maximum possible layer increase has no
stutters or backward moves: every one of its steps is a forward layered edge. -/
public theorem paddedUndirectedPath_of_maximal_layer {edge : V → V → Prop}
    {start finish : Vertex V} {steps : ℕ}
    (hpath : PaddedPath (UndirectedEdge edge) start steps finish)
    (hmax : finish.2.val = start.2.val + steps) :
    PaddedPath (Edge edge) start steps finish := by
  revert hmax
  induction hpath with
  | zero =>
      intro _hmax
      exact .zero
  | @succ k old new hpath hmove ih =>
      intro hmax
      have hprefixLe :=
        paddedUndirectedPath_layer_le (edge := edge) hpath
      have hstepLe : new.2.val ≤ old.2.val + 1 := by
        rcases hmove with rfl | hstep
        · omega
        · exact undirectedEdge_layer_le hstep
      have holdLayer : old.2.val = start.2.val + k := by
        omega
      have hprefix : PaddedPath (Edge edge) start k old :=
        ih holdLayer
      apply PaddedPath.succ hprefix
      rcases hmove with heq | hstep
      · subst new
        exfalso
        omega
      · rcases hstep with hforward | hbackward
        · exact Or.inr hforward
        · exfalso
          have := hbackward.1
          omega

/-- Lift an exactly indexed padded path to an exactly indexed path in the directed layered
graph.  Every source stutter becomes a genuine clock-advancing padding edge. -/
public theorem layeredPaddedPath_of_paddedPath (edge : V → V → Prop)
    {source target : V} {steps : ℕ} (hsteps : steps ≤ Fintype.card V)
    (hpath : PaddedPath edge source steps target) :
    PaddedPath (Edge edge)
      (bottom source) steps (atLayer target steps hsteps) := by
  induction hpath with
  | zero =>
      exact .zero
  | @succ k old new hpath hmove ih =>
      have hk : k ≤ Fintype.card V := by omega
      have hprefix := ih hk
      apply PaddedPath.succ hprefix
      exact Or.inr ⟨by simp [atLayer], hmove⟩

/-- Project an exactly indexed layered path from the bottom to an exactly indexed padded path
in the original graph. -/
public theorem paddedPath_of_layeredPaddedPath_bottom (edge : V → V → Prop)
    {source : V} {target : Vertex V} {steps : ℕ}
    (hpath : PaddedPath (Edge edge) (bottom source) steps target) :
    PaddedPath edge source steps target.1 := by
  induction hpath with
  | zero =>
      exact .zero
  | @succ k old new hpath hmove ih =>
      apply PaddedPath.succ ih
      rcases hmove with rfl | hstep
      · exact Or.inl rfl
      · exact hstep.2

/-- Every directed layered padded path is also a path after forgetting edge orientations. -/
public theorem paddedUndirectedPath_of_layeredPaddedPath {edge : V → V → Prop}
    {start finish : Vertex V} {steps : ℕ}
    (hpath : PaddedPath (Edge edge) start steps finish) :
    PaddedPath (UndirectedEdge edge) start steps finish := by
  induction hpath with
  | zero =>
      exact .zero
  | succ hprefix hmove ih =>
      apply PaddedPath.succ ih
      exact hmove.imp id Or.inl

/-- Finite directed reachability is equivalent to bottom-to-top reachability in the acyclic
layered graph. -/
public theorem reaches_iff_layered_reaches (edge : V → V → Prop)
    (source target : V) :
    ReflTransGen edge source target ↔
      ReflTransGen (Edge edge) (bottom source) (top target) := by
  classical
  letI : DecidableRel edge := Classical.decRel edge
  constructor
  · intro hreach
    have hmem :
        target ∈ reached edge source (Fintype.card V) :=
      (mem_reached_card_iff (edge := edge) (source := source)).2 hreach
    have hpath :
        PaddedPath edge source (Fintype.card V) target :=
      (mem_reached_iff_paddedPath (edge := edge) (source := source)).1 hmem
    simpa [top] using
      reaches_atLayer_of_paddedPath edge (Nat.le_refl _) hpath
  · intro hreach
    have hpath :
        PaddedPath edge source (Fintype.card V) target := by
      simpa [top] using paddedPath_of_reaches_bottom edge hreach
    have hmem :
        target ∈ reached edge source (Fintype.card V) :=
      (mem_reached_iff_paddedPath (edge := edge) (source := source)).2 hpath
    exact (mem_reached_card_iff (edge := edge) (source := source)).1 hmem

/-- Directed reachability is equivalent to a length-`|V|` walk between the bottom source and
top target after forgetting every layered edge's orientation.

The endpoints are exactly `|V|` layers apart.  Since one undirected move can raise the layer by
at most one, any such walk must raise it on every move and is therefore a directed layered path.
Equivalently, in the underlying undirected layered graph the endpoint distance is exactly
`|V|` precisely when the original target is reachable. -/
public theorem reaches_iff_undirectedPaddedPath_card (edge : V → V → Prop)
    (source target : V) :
    ReflTransGen edge source target ↔
      PaddedPath (UndirectedEdge edge) (bottom source)
        (Fintype.card V) (top target) := by
  classical
  letI : DecidableRel edge := Classical.decRel edge
  constructor
  · intro hreach
    have hmem :
        target ∈ reached edge source (Fintype.card V) :=
      (mem_reached_card_iff (edge := edge) (source := source)).2 hreach
    have hpath :
        PaddedPath edge source (Fintype.card V) target :=
      (mem_reached_iff_paddedPath (edge := edge) (source := source)).1 hmem
    have hlayered :
        PaddedPath (Edge edge) (bottom source)
          (Fintype.card V) (top target) := by
      simpa only [top] using
        layeredPaddedPath_of_paddedPath edge (Nat.le_refl _) hpath
    exact paddedUndirectedPath_of_layeredPaddedPath hlayered
  · intro hundirected
    have hmax :
        (top target).2.val =
          (bottom source).2.val + Fintype.card V := by
      simp [top, bottom, atLayer]
    have hlayered :
        PaddedPath (Edge edge) (bottom source)
          (Fintype.card V) (top target) :=
      paddedUndirectedPath_of_maximal_layer hundirected hmax
    have hpath :
        PaddedPath edge source (Fintype.card V) target := by
      simpa only [top] using
        paddedPath_of_layeredPaddedPath_bottom edge hlayered
    have hmem :
        target ∈ reached edge source (Fintype.card V) :=
      (mem_reached_iff_paddedPath (edge := edge) (source := source)).2 hpath
    exact (mem_reached_card_iff (edge := edge) (source := source)).1 hmem

end LayeredReachability

end
