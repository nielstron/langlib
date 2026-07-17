module

public import Langlib.Automata.LinearBounded.LayeredReachability
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Relator
import Mathlib.Tactic

@[expose]
public section

/-!
# Reachability through two linear 2-diforests

This file formalizes a fixed-slot version of the degree-splitting reduction in Theorem 3.1 of
Bhadra and Tewari, *Reachability in Graphs Having Linear 2-Arboricity Two Is NL-Hard*.

For a relation on `Fin n`, every original vertex receives `2 * n` incidence slots.  The first
`n` slots name possible outgoing edges and the last `n` slots name possible incoming edges.
Every slot has three phases.  The internal edges make all phases and slots of one original
vertex into a directed cycle, while an original edge `u → v` is represented by an edge from
the outgoing-`v` slot of `u` to the incoming-`u` slot of `v`.

The first supplied layer consists of the represented original edges and all phase-one to
phase-two edges.  It is a directed matching.  The second supplied layer consists of disjoint
paths

`(slot, 2) → (next slot, 0) → (next slot, 1)`.

Thus both layers are partial bijections, and their components have length at most one and two,
respectively.  Core-to-core reachability is preserved exactly.  Unlike the acyclic serializer,
this construction intentionally contains a positive directed cycle over every original vertex.

The fixed slots make the construction total even for isolated vertices and avoid choosing an
ordering of the actual incident edges.  They also make every edge predicate a direct formula on
numbered vertices.  The construction has exactly `6 * n ^ 2` vertices.
-/

namespace LinearTwoDiforestReachability

open Relation Set

/-- A serialized vertex: an original vertex, one of its `2 * n` fixed incidence slots, and one
of three phases. -/
@[ext]
public structure Vertex (n : ℕ) where
  vertex : Fin n
  slot : Fin (n + n)
  phase : Fin 3
  deriving DecidableEq, Fintype

private def vertexEquiv (n : ℕ) :
    Vertex n ≃ Fin n × Fin (n + n) × Fin 3 where
  toFun vertex := (vertex.vertex, vertex.slot, vertex.phase)
  invFun vertex := ⟨vertex.1, vertex.2.1, vertex.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fixed-slot construction has exactly `6 * n ^ 2` vertices. -/
public theorem card_vertex (n : ℕ) :
    Fintype.card (Vertex n) = Nat.mul 6 (Nat.mul n n) := by
  rw [Fintype.card_congr (vertexEquiv n)]
  simp
  ring

/-- The first half of the slots names possible outgoing targets. -/
@[expose]
public def outSlot {n : ℕ} (target : Fin n) : Fin (n + n) :=
  ⟨target.val, by omega⟩

/-- The second half of the slots names possible incoming sources. -/
@[expose]
public def inSlot {n : ℕ} (source : Fin n) : Fin (n + n) :=
  ⟨n + source.val, by omega⟩

/-- Rotate the fixed incidence slots by one position. -/
@[expose]
public def nextSlot (n : ℕ) : Equiv.Perm (Fin (n + n)) :=
  finRotate (n + n)

private theorem outSlot_injective {n : ℕ} : Function.Injective (@outSlot n) := by
  intro left right h
  apply Fin.ext
  have hval := congrArg (fun slot : Fin (n + n) ↦ slot.val) h
  simpa only [outSlot] using hval

private theorem inSlot_injective {n : ℕ} : Function.Injective (@inSlot n) := by
  intro left right h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [inSlot] at this
  omega

private theorem outSlot_ne_inSlot {n : ℕ} (left right : Fin n) :
    outSlot left ≠ inSlot right := by
  intro h
  have := congrArg Fin.val h
  simp only [outSlot, inSlot] at this
  omega

/-- The layer containing represented original edges and phase-one to phase-two edges. -/
@[expose]
public def FirstLayer {n : ℕ} (edge : Fin n → Fin n → Prop) :
    Vertex n → Vertex n → Prop :=
  fun old new ↦
    (old.phase = 0 ∧ new.phase = 0 ∧
      old.slot = outSlot new.vertex ∧
      new.slot = inSlot old.vertex ∧
      edge old.vertex new.vertex) ∨
    (old.vertex = new.vertex ∧ old.slot = new.slot ∧
      old.phase = 1 ∧ new.phase = 2)

/-- The layer containing phase-zero to phase-one edges and phase-two slot rotations. -/
@[expose]
public def SecondLayer {n : ℕ} : Vertex n → Vertex n → Prop :=
  fun old new ↦
    (old.vertex = new.vertex ∧ old.slot = new.slot ∧
      old.phase = 0 ∧ new.phase = 1) ∨
    (old.vertex = new.vertex ∧ nextSlot n old.slot = new.slot ∧
      old.phase = 2 ∧ new.phase = 0)

/-- The complete serialized edge relation. -/
@[expose]
public def Edge {n : ℕ} (edge : Fin n → Fin n → Prop) :
    Vertex n → Vertex n → Prop :=
  fun old new ↦ FirstLayer edge old new ∨ SecondLayer old new

/-- The syntactic color of a serialized edge. -/
@[expose]
public def edgeColor {n : ℕ} (old new : Vertex n) : Fin 2 :=
  if (old.phase = 0 ∧ new.phase = 0) ∨
      (old.phase = 1 ∧ new.phase = 2) then 0 else 1

/-- One supplied layer of the serialized relation. -/
@[expose]
public def Layer {n : ℕ} (edge : Fin n → Fin n → Prop)
    (color : Fin 2) (old new : Vertex n) : Prop :=
  Edge edge old new ∧ edgeColor old new = color

private theorem edgeColor_eq_zero_of_first {n : ℕ}
    {edge : Fin n → Fin n → Prop} {old new : Vertex n}
    (h : FirstLayer edge old new) :
    edgeColor old new = 0 := by
  rcases h with h | h
  · simp [edgeColor, h.1, h.2.1]
  · simp [edgeColor, h.2.2.1, h.2.2.2]

private theorem edgeColor_eq_one_of_second {n : ℕ}
    {old new : Vertex n} (h : SecondLayer old new) :
    edgeColor old new = 1 := by
  rcases h with h | h
  · simp [edgeColor, h.2.2.1, h.2.2.2]
  · simp [edgeColor, h.2.2.1, h.2.2.2]

/-- Every serialized edge has exactly one supplied color. -/
public theorem edge_iff_existsUnique_layer {n : ℕ}
    (edge : Fin n → Fin n → Prop) (old new : Vertex n) :
    Edge edge old new ↔ ∃! color, Layer edge color old new := by
  constructor
  · intro hedge
    refine ⟨edgeColor old new, ⟨hedge, rfl⟩, ?_⟩
    intro color hcolor
    exact hcolor.2.symm
  · rintro ⟨_, hcolor, _⟩
    exact hcolor.1

/-- A supplied layer contains only genuine serialized edges. -/
public theorem layer_sub_edge {n : ℕ}
    (edge : Fin n → Fin n → Prop) (color : Fin 2)
    {old new : Vertex n} (h : Layer edge color old new) :
    Edge edge old new :=
  h.1

public theorem layer_zero_iff_first {n : ℕ}
    (edge : Fin n → Fin n → Prop) (old new : Vertex n) :
    Layer edge 0 old new ↔ FirstLayer edge old new := by
  constructor
  · rintro ⟨hfirst | hsecond, hcolor⟩
    · exact hfirst
    · rw [edgeColor_eq_one_of_second hsecond] at hcolor
      omega
  · intro hfirst
    exact ⟨Or.inl hfirst, edgeColor_eq_zero_of_first hfirst⟩

public theorem layer_one_iff_second {n : ℕ}
    (edge : Fin n → Fin n → Prop) (old new : Vertex n) :
    Layer edge 1 old new ↔ SecondLayer old new := by
  constructor
  · rintro ⟨hfirst | hsecond, hcolor⟩
    · rw [edgeColor_eq_zero_of_first hfirst] at hcolor
      omega
    · exact hsecond
  · intro hsecond
    exact ⟨Or.inr hsecond, edgeColor_eq_one_of_second hsecond⟩

private theorem layer_zero_eq_first {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    Layer edge 0 = FirstLayer edge := by
  funext old new
  exact propext (layer_zero_iff_first edge old new)

private theorem layer_one_eq_second {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    Layer edge 1 = SecondLayer := by
  funext old new
  exact propext (layer_one_iff_second edge old new)

private theorem firstLayer_rightUnique {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    Relator.RightUnique (FirstLayer edge) := by
  intro source left right hleft hright
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · apply Vertex.ext
    · apply outSlot_injective
      exact hleft.2.2.1.symm.trans hright.2.2.1
    · rw [hleft.2.2.2.1, hright.2.2.2.1]
    · rw [hleft.2.1, hright.2.1]
  · have : source.phase = 0 := hleft.1
    have : source.phase = 1 := hright.2.2.1
    omega
  · have : source.phase = 1 := hleft.2.2.1
    have : source.phase = 0 := hright.1
    omega
  · apply Vertex.ext
    · exact hleft.1.symm.trans hright.1
    · exact hleft.2.1.symm.trans hright.2.1
    · rw [hleft.2.2.2, hright.2.2.2]

private theorem firstLayer_leftUnique {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    Relator.LeftUnique (FirstLayer edge) := by
  intro left right target hleft hright
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · apply Vertex.ext
    · apply inSlot_injective
      exact hleft.2.2.2.1.symm.trans hright.2.2.2.1
    · rw [hleft.2.2.1, hright.2.2.1]
    · rw [hleft.1, hright.1]
  · have : target.phase = 0 := hleft.2.1
    have : target.phase = 2 := hright.2.2.2
    omega
  · have : target.phase = 2 := hleft.2.2.2
    have : target.phase = 0 := hright.2.1
    omega
  · apply Vertex.ext
    · exact hleft.1.trans hright.1.symm
    · exact hleft.2.1.trans hright.2.1.symm
    · rw [hleft.2.2.1, hright.2.2.1]

private theorem secondLayer_rightUnique {n : ℕ} :
    Relator.RightUnique (@SecondLayer n) := by
  intro source left right hleft hright
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · apply Vertex.ext
    · exact hleft.1.symm.trans hright.1
    · exact hleft.2.1.symm.trans hright.2.1
    · rw [hleft.2.2.2, hright.2.2.2]
  · have : source.phase = 0 := hleft.2.2.1
    have : source.phase = 2 := hright.2.2.1
    omega
  · have : source.phase = 2 := hleft.2.2.1
    have : source.phase = 0 := hright.2.2.1
    omega
  · apply Vertex.ext
    · exact hleft.1.symm.trans hright.1
    · exact hleft.2.1.symm.trans hright.2.1
    · rw [hleft.2.2.2, hright.2.2.2]

private theorem secondLayer_leftUnique {n : ℕ} :
    Relator.LeftUnique (@SecondLayer n) := by
  intro left right target hleft hright
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · apply Vertex.ext
    · exact hleft.1.trans hright.1.symm
    · exact hleft.2.1.trans hright.2.1.symm
    · rw [hleft.2.2.1, hright.2.2.1]
  · have : target.phase = 1 := hleft.2.2.2
    have : target.phase = 0 := hright.2.2.2
    omega
  · have : target.phase = 0 := hleft.2.2.2
    have : target.phase = 1 := hright.2.2.2
    omega
  · apply Vertex.ext
    · exact hleft.1.trans hright.1.symm
    · exact (nextSlot n).injective (hleft.2.1.trans hright.2.1.symm)
    · rw [hleft.2.2.1, hright.2.2.1]

/-- Every supplied layer is both functional and cofunctional. -/
public theorem layer_biUnique {n : ℕ}
    (edge : Fin n → Fin n → Prop) (color : Fin 2) :
    Relator.BiUnique (Layer edge color) := by
  have hcolor : color = 0 ∨ color = 1 := by omega
  rcases hcolor with rfl | rfl
  · rw [layer_zero_eq_first]
    exact ⟨firstLayer_leftUnique edge, firstLayer_rightUnique edge⟩
  · rw [layer_one_eq_second]
    exact ⟨secondLayer_leftUnique, secondLayer_rightUnique⟩

/-- A relation has no directed path containing two composable edges. -/
public def PathLengthAtMostOne {V : Type*} (relation : V → V → Prop) : Prop :=
  ∀ {a b c : V}, relation a b → relation b c → False

/-- A relation has no directed path containing three composable edges. -/
public def PathLengthAtMostTwo {V : Type*} (relation : V → V → Prop) : Prop :=
  ∀ {a b c d : V}, relation a b → relation b c → relation c d → False

/-- The first layer is a directed matching, so its path components have length at most one. -/
public theorem firstLayer_pathLengthAtMostOne {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    PathLengthAtMostOne (FirstLayer edge) := by
  intro a b c hab hbc
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · exact outSlot_ne_inSlot c.vertex a.vertex
      (hbc.2.2.1.symm.trans hab.2.2.2.1)
  all_goals omega

/-- Color zero is exactly the first matching layer, hence has path length at most one. -/
public theorem layer_zero_pathLengthAtMostOne {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    PathLengthAtMostOne (Layer edge 0) := by
  rw [layer_zero_eq_first]
  exact firstLayer_pathLengthAtMostOne edge

/-- The second layer consists of directed paths of length at most two. -/
public theorem secondLayer_pathLengthAtMostTwo {n : ℕ} :
    PathLengthAtMostTwo (@SecondLayer n) := by
  intro a b c d hab hbc hcd
  rcases hab with hab | hab <;>
    rcases hbc with hbc | hbc <;>
      rcases hcd with hcd | hcd <;> omega

/-- Color-indexed path-length bound: color zero has length at most one and color one has length
at most two. -/
public theorem layer_pathLengthAtMostTwo {n : ℕ}
    (edge : Fin n → Fin n → Prop) (color : Fin 2) :
    PathLengthAtMostTwo (Layer edge color) := by
  have hcolor : color = 0 ∨ color = 1 := by omega
  rcases hcolor with rfl | rfl
  · intro a b c d hab hbc _
    exact layer_zero_pathLengthAtMostOne edge hab hbc
  · rw [layer_one_eq_second]
    intro a b c d hab hbc hcd
    exact secondLayer_pathLengthAtMostTwo hab hbc hcd

/-! ## Directed-degree bounds -/

/-- The two functional supplied layers bound every successor fiber by two. -/
public theorem outdegreeAtMostTwo {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    LayeredReachability.OutdegreeAtMost 2 (Edge edge) := by
  intro old
  calc
    Set.encard {new | Edge edge old new} ≤
        Set.encard (Set.univ : Set (Fin 2)) := by
      apply Set.encard_le_encard_of_injOn (f := fun new ↦ edgeColor old new)
      · intro new _
        exact Set.mem_univ _
      · intro left hleft right hright hcolor
        exact (layer_biUnique edge (edgeColor old left)).2
          ⟨hleft, rfl⟩ ⟨hright, hcolor.symm⟩
    _ = 2 := by
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      norm_num

/-- The two cofunctional supplied layers bound every predecessor fiber by two. -/
public theorem indegreeAtMostTwo {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    LayeredReachability.IndegreeAtMost 2 (Edge edge) := by
  intro new
  calc
    Set.encard {old | Edge edge old new} ≤
        Set.encard (Set.univ : Set (Fin 2)) := by
      apply Set.encard_le_encard_of_injOn (f := fun old ↦ edgeColor old new)
      · intro old _
        exact Set.mem_univ _
      · intro left hleft right hright hcolor
        exact (layer_biUnique edge (edgeColor left new)).1
          ⟨hleft, rfl⟩ ⟨hright, hcolor.symm⟩
    _ = 2 := by
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      norm_num

/-- Both directed degrees of the serialized relation are at most two. -/
public theorem directedDegreeAtMostTwo {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    LayeredReachability.DirectedDegreeAtMost 2 (Edge edge) :=
  ⟨outdegreeAtMostTwo edge, indegreeAtMostTwo edge⟩

/-! ## Exact preservation of reachability -/

/-- A canonical representative of an original vertex. -/
@[expose]
public def canonical {n : ℕ} (vertex : Fin n) : Vertex n :=
  ⟨vertex, outSlot vertex, 0⟩

/-- Forget the fixed incidence slot and phase. -/
@[expose]
public def project {n : ℕ} (vertex : Vertex n) : Fin n :=
  vertex.vertex

private theorem edge_phase_zero_one {n : ℕ}
    (edge : Fin n → Fin n → Prop) (vertex : Fin n)
    (slot : Fin (n + n)) :
    Edge edge ⟨vertex, slot, 0⟩ ⟨vertex, slot, 1⟩ := by
  exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)

private theorem edge_phase_one_two {n : ℕ}
    (edge : Fin n → Fin n → Prop) (vertex : Fin n)
    (slot : Fin (n + n)) :
    Edge edge ⟨vertex, slot, 1⟩ ⟨vertex, slot, 2⟩ := by
  exact Or.inl (Or.inr ⟨rfl, rfl, rfl, rfl⟩)

private theorem edge_rotate {n : ℕ}
    (edge : Fin n → Fin n → Prop) (vertex : Fin n)
    (slot : Fin (n + n)) :
    Edge edge ⟨vertex, slot, 2⟩ ⟨vertex, nextSlot n slot, 0⟩ := by
  exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)

/-- One complete three-phase traversal advances the incidence slot once. -/
public theorem reaches_nextSlot {n : ℕ}
    (edge : Fin n → Fin n → Prop) (vertex : Fin n)
    (slot : Fin (n + n)) :
    ReflTransGen (Edge edge) ⟨vertex, slot, 0⟩
      ⟨vertex, nextSlot n slot, 0⟩ := by
  exact ((ReflTransGen.single (edge_phase_zero_one edge vertex slot)).trans
    (ReflTransGen.single (edge_phase_one_two edge vertex slot))).trans
      (ReflTransGen.single (edge_rotate edge vertex slot))

private theorem reaches_iterate_nextSlot {n : ℕ}
    (edge : Fin n → Fin n → Prop) (vertex : Fin n)
    (slot : Fin (n + n)) (steps : ℕ) :
    ReflTransGen (Edge edge) ⟨vertex, slot, 0⟩
      ⟨vertex, (nextSlot n)^[steps] slot, 0⟩ := by
  induction steps with
  | zero => exact .refl
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (reaches_nextSlot edge vertex _)

/-- All phase-zero slots belonging to one original vertex are mutually reachable. -/
public theorem reaches_phaseZero {n : ℕ}
    (edge : Fin n → Fin n → Prop) (vertex : Fin n)
    (source target : Fin (n + n)) :
    ReflTransGen (Edge edge) ⟨vertex, source, 0⟩ ⟨vertex, target, 0⟩ := by
  letI : NeZero (n + n) := ⟨by have := source.isLt; omega⟩
  let difference : Fin (n + n) := target - source
  have htarget : (nextSlot n)^[difference.val] source = target := by
    change (finRotate (n + n))^[difference.val] source = target
    rw [← finCycle_eq_finRotate_iterate]
    simp [difference]
  simpa only [htarget] using
    reaches_iterate_nextSlot edge vertex source difference.val

/-- A represented original edge joins its named outgoing and incoming phase-zero ports. -/
private theorem edge_external {n : ℕ} {edge : Fin n → Fin n → Prop}
    {source target : Fin n} (h : edge source target) :
    Edge edge ⟨source, outSlot target, 0⟩ ⟨target, inSlot source, 0⟩ := by
  exact Or.inl (Or.inl ⟨rfl, rfl, rfl, rfl, h⟩)

/-- One original edge expands to a path between canonical representatives. -/
public theorem reaches_canonical_of_edge {n : ℕ}
    {edge : Fin n → Fin n → Prop} {source target : Fin n}
    (h : edge source target) :
    ReflTransGen (Edge edge) (canonical source) (canonical target) := by
  exact (reaches_phaseZero edge source (outSlot source) (outSlot target)).trans
    ((ReflTransGen.single (edge_external h)).trans
      (reaches_phaseZero edge target (inSlot source) (outSlot target)))

/-- Every original path lifts to a path between canonical representatives. -/
public theorem reaches_canonical_of_reaches {n : ℕ}
    {edge : Fin n → Fin n → Prop} {source target : Fin n}
    (h : ReflTransGen edge source target) :
    ReflTransGen (Edge edge) (canonical source) (canonical target) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans (reaches_canonical_of_edge hstep)

/-- Every serialized edge either stutters under projection or performs one original edge. -/
public theorem project_edge {n : ℕ}
    {edge : Fin n → Fin n → Prop} {old new : Vertex n}
    (h : Edge edge old new) :
    project old = project new ∨ edge (project old) (project new) := by
  rcases h with (h | h) | (h | h)
  · exact Or.inr h.2.2.2.2
  · exact Or.inl h.1
  · exact Or.inl h.1
  · exact Or.inl h.1

/-- Projecting a serialized path deletes internal cycle steps and retains represented original
edges. -/
public theorem reaches_project_of_reaches {n : ℕ}
    {edge : Fin n → Fin n → Prop} {old new : Vertex n}
    (h : ReflTransGen (Edge edge) old new) :
    ReflTransGen edge (project old) (project new) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases project_edge hstep with heq | hedge
      · simpa only [heq] using ih
      · exact ih.tail hedge

/-- Exact reachability equivalence between arbitrary original endpoints and their canonical
representatives. -/
public theorem reaches_iff {n : ℕ}
    (edge : Fin n → Fin n → Prop) (source target : Fin n) :
    ReflTransGen edge source target ↔
      ReflTransGen (Edge edge) (canonical source) (canonical target) := by
  constructor
  · exact reaches_canonical_of_reaches
  · intro h
    simpa only [project, canonical] using reaches_project_of_reaches h

/-! ## The forced directed cycles -/

/-- Every original vertex has a genuinely nonempty directed cycle through each phase-zero slot.
This is why the short-component reduction is not an acyclic reduction. -/
public theorem positiveCycle {n : ℕ}
    (edge : Fin n → Fin n → Prop) (vertex : Fin n)
    (slot : Fin (n + n)) :
    TransGen (Edge edge) ⟨vertex, slot, 0⟩ ⟨vertex, slot, 0⟩ := by
  apply TransGen.head' (edge_phase_zero_one edge vertex slot)
  exact (ReflTransGen.single (edge_phase_one_two edge vertex slot)).trans
    ((ReflTransGen.single (edge_rotate edge vertex slot)).trans
      (reaches_phaseZero edge vertex (nextSlot n slot) slot))

/-- Every nonempty input vertex type yields a cyclic serialized relation. -/
public theorem not_acyclic_of_neZero (n : ℕ) [NeZero n]
    (edge : Fin n → Fin n → Prop) :
    ¬ (∀ vertex : Vertex n, ¬ TransGen (Edge edge) vertex vertex) := by
  intro hacyclic
  let vertex : Fin n := 0
  let slot : Fin (n + n) := outSlot vertex
  exact hacyclic ⟨vertex, slot, 0⟩ (positiveCycle edge vertex slot)

/-! ## Packaged reduction theorem -/

/-- Finite directed reachability reduces exactly to reachability in a graph of directed degree
at most two whose edge relation is covered uniquely by two linear 2-diforests.  The first
layer is in fact a matching.  The quadratic-size fixed-slot construction is necessarily cyclic
whenever the input vertex set is nonempty. -/
public theorem finiteReachability_twoLinearTwoDiforests {n : ℕ}
    (edge : Fin n → Fin n → Prop) (source target : Fin n) :
    Fintype.card (Vertex n) = Nat.mul 6 (Nat.mul n n) ∧
      (ReflTransGen edge source target ↔
        ReflTransGen (Edge edge) (canonical source) (canonical target)) ∧
      LayeredReachability.DirectedDegreeAtMost 2 (Edge edge) ∧
      (∀ old new, Edge edge old new ↔ ∃! color, Layer edge color old new) ∧
      (∀ color old new, Layer edge color old new → Edge edge old new) ∧
      (∀ color, Relator.BiUnique (Layer edge color)) ∧
      PathLengthAtMostOne (Layer edge 0) ∧
      (∀ color, PathLengthAtMostTwo (Layer edge color)) ∧
      (0 < n → ∃ vertex, TransGen (Edge edge) vertex vertex) := by
  refine ⟨card_vertex n, reaches_iff edge source target,
    directedDegreeAtMostTwo edge, ?_, ?_, layer_biUnique edge,
    layer_zero_pathLengthAtMostOne edge, layer_pathLengthAtMostTwo edge, ?_⟩
  · exact edge_iff_existsUnique_layer edge
  · intro color old new h
    exact layer_sub_edge edge color h
  · intro _
    let slot : Fin (n + n) := outSlot source
    exact ⟨⟨source, slot, 0⟩, positiveCycle edge source slot⟩

end LinearTwoDiforestReachability

end
