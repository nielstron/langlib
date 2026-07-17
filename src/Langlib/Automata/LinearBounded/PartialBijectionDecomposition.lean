module

public import Langlib.Automata.LinearBounded.BoundedDegree
public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relator
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Tactic

@[expose]
public section

/-!
# Decomposing degree-two relations into partial bijections

Every relation with at most two successors and at most two predecessors is the union of four
relations that are both functional and cofunctional.  No finiteness assumption is made on the
ambient vertex type: only the individual predecessor and successor fibers are bounded.

The construction independently assigns a two-valued port to every outgoing and incoming fiber,
then colors an edge by its pair of ports.  The result is structural rather than algorithmic: the
ports are chosen classically.
-/

open Set

namespace PartialBijectionDecomposition

variable {V : Type*}

/-- A set of cardinality at most two admits a two-valued coloring that is injective on the set.
The ambient type itself need not be finite. -/
private theorem exists_finTwo_injOn (s : Set V) (hcard : s.encard ≤ 2) :
    ∃ color : V → Fin 2, Set.InjOn color s := by
  have hs : s.Finite := Set.finite_of_encard_le_coe hcard
  have hle : s.encard ≤ (Set.univ : Set (Fin 2)).encard := by
    simpa using hcard
  obtain ⟨color, _, hinjective⟩ := hs.exists_injOn_of_encard_le hle
  exact ⟨color, hinjective⟩

/-- Any directed relation with predecessor and successor fibers of extended cardinality at most
two is partitioned into four bi-unique relations.

The unique-existence clause says that every edge receives exactly one color.  Thus this is
strictly stronger than merely expressing the original relation as a union of four layers. -/
public theorem exists_four_biUnique_partition
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2) :
    ∃ layer : Fin 2 × Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target, layer color source target → edge source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  classical
  choose outPort houtPort using fun source =>
    exists_finTwo_injOn {target | edge source target} (hout source)
  choose inPort hinPort using fun target =>
    exists_finTwo_injOn {source | edge source target} (hin target)
  let layer : Fin 2 × Fin 2 → V → V → Prop :=
    fun color source target =>
      edge source target ∧
        outPort source target = color.1 ∧
        inPort target source = color.2
  refine ⟨layer, ?_, ?_, ?_⟩
  · intro source target
    constructor
    · intro hedge
      refine ⟨(outPort source target, inPort target source),
        ⟨hedge, rfl, rfl⟩, ?_⟩
      intro color hcolor
      apply Prod.ext
      · exact hcolor.2.1.symm
      · exact hcolor.2.2.symm
    · rintro ⟨color, hcolor, _⟩
      exact hcolor.1
  · intro color source target hcolor
    exact hcolor.1
  · intro color
    constructor
    · intro left right target hleft hright
      apply hinPort target hleft.1 hright.1
      exact hleft.2.2.trans hright.2.2.symm
    · intro source left right hleft hright
      apply houtPort source hleft.1 hright.1
      exact hleft.2.1.trans hright.2.1.symm

/-- Any directed relation with predecessor and successor fibers of extended cardinality at most
two is exactly the union of four bi-unique relations.

`layer (outPort, inPort)` contains the edges carrying that outgoing port at their source and that
incoming port at their target.  `Relator.BiUnique` says simultaneously that a layer has at most
one outgoing edge at every source and at most one incoming edge at every target. -/
public theorem exists_four_biUnique_decomposition
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2) :
    ∃ layer : Fin 2 × Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃ color, layer color source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  obtain ⟨layer, hpartition, hsub, hbiUnique⟩ :=
    exists_four_biUnique_partition edge hout hin
  refine ⟨layer, ?_, hbiUnique⟩
  · intro source target
    constructor
    · intro hedge
      exact ((hpartition source target).mp hedge).exists
    · rintro ⟨color, hcolor⟩
      exact hsub color source target hcolor

/-- Function equality form of `exists_four_biUnique_decomposition`. -/
public theorem exists_four_biUnique_decomposition_eq
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2) :
    ∃ layer : Fin 2 × Fin 2 → V → V → Prop,
      edge = (fun source target => ∃ color, layer color source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  obtain ⟨layer, hcover, hunique⟩ :=
    exists_four_biUnique_decomposition edge hout hin
  exact ⟨layer, funext fun source => funext fun target => propext (hcover source target), hunique⟩

/-! ## The finite two-layer frontier

For a finite relation, the optimal bound is two rather than four.  The incidence graph is
bipartite and has maximum degree two, so each of its path and even-cycle components admits an
alternating edge coloring.  The next definitions and degree theorem isolate the first formal
step of that argument: the conflict graph on relation edges itself has maximum degree two.
-/

section Finite

variable [Fintype V] [DecidableEq V]

/-- An edge of a finite directed relation, retaining both endpoints. -/
public abbrev FiniteEdge (edge : V → V → Prop) :=
  { endpoints : V × V // edge endpoints.1 endpoints.2 }

/-- Two distinct relation edges conflict when they share a source or share a target.  A color
class is bi-unique exactly when it contains no conflicting pair. -/
public def EdgeConflict {edge : V → V → Prop}
    (left right : FiniteEdge edge) : Prop :=
  left ≠ right ∧
    (left.1.1 = right.1.1 ∨ left.1.2 = right.1.2)

omit [Fintype V] [DecidableEq V] in
public theorem EdgeConflict.symm {edge : V → V → Prop} {left right : FiniteEdge edge}
    (h : EdgeConflict left right) : EdgeConflict right left := by
  rcases h with ⟨hne, hsource | htarget⟩
  · exact ⟨hne.symm, Or.inl hsource.symm⟩
  · exact ⟨hne.symm, Or.inr htarget.symm⟩

public instance instDecidableEdgeConflict {edge : V → V → Prop} :
    DecidableRel (EdgeConflict (edge := edge)) := by
  intro left right
  unfold EdgeConflict
  infer_instance

/-- The conflict graph of a finite relation.  Its vertices are relation edges, and adjacency
means that two distinct edges cannot occur in the same partial-bijection layer. -/
public def edgeConflictGraph (edge : V → V → Prop) :
    SimpleGraph (FiniteEdge edge) where
  Adj := EdgeConflict
  symm := by
    rintro left right ⟨hne, hsource | htarget⟩
    · exact ⟨hne.symm, Or.inl hsource.symm⟩
    · exact ⟨hne.symm, Or.inr htarget.symm⟩
  loopless := ⟨fun edge hconflict => hconflict.1 rfl⟩

public instance instDecidableEdgeConflictGraphAdj (edge : V → V → Prop) :
    DecidableRel (edgeConflictGraph edge).Adj :=
  instDecidableEdgeConflict

private theorem finTwo_eq_of_ne_same {a b pivot : Fin 2}
    (ha : a ≠ pivot) (hb : b ≠ pivot) : a = b := by
  apply Fin.ext
  have haVal : a.val ≠ pivot.val := by
    intro h
    exact ha (Fin.ext h)
  have hbVal : b.val ≠ pivot.val := by
    intro h
    exact hb (Fin.ext h)
  omega

/-- A nonempty cyclic sequence of two-valued labels that changes at every step has even
length.  The formulation separates the ordinary successor steps from the final wraparound. -/
private theorem even_of_finTwo_cyclic_alternation
    {n : ℕ} (hn : 0 < n) (label : Fin n → Fin 2)
    (hnext : ∀ (i : ℕ) (hi : i + 1 < n),
      label ⟨i, Nat.lt_of_succ_lt hi⟩ ≠ label ⟨i + 1, hi⟩)
    (hwrap : label ⟨n - 1, Nat.sub_lt hn (by omega)⟩ ≠ label ⟨0, hn⟩) :
    Even n := by
  obtain ⟨k, heven | hodd⟩ := Nat.even_or_odd' n
  · exact ⟨k, by omega⟩
  · subst n
    exfalso
    have hevenIndex : ∀ (j : ℕ) (hj : 2 * j < 2 * k + 1),
        label ⟨2 * j, hj⟩ = label ⟨0, by omega⟩ := by
      intro j
      induction j with
      | zero =>
          intro hj
          rfl
      | succ j ih =>
          intro hj
          have hj0 : 2 * j < 2 * k + 1 := by omega
          have hfirst := hnext (2 * j) (by omega)
          have hsecond := hnext (2 * j + 1) (by omega)
          have hpair :
              label ⟨2 * (j + 1), hj⟩ = label ⟨2 * j, hj0⟩ := by
            apply finTwo_eq_of_ne_same
            · simpa [Nat.mul_succ] using hsecond.symm
            · exact hfirst
          exact hpair.trans (ih hj0)
    apply hwrap
    simpa using hevenIndex k (by omega)

/-- If every simple cycle of a graph has even length, then the graph is two-colorable.

Choose a spanning forest and color it by distance parity.  Every edge outside the forest closes
the unique forest path between its endpoints into a simple cycle.  That cycle is even, so the
forest path is odd and its endpoints receive different colors. -/
private theorem colorable_two_of_isCycle_even {W : Type*} (G : SimpleGraph W)
    (hcycle : ∀ {base : W} {walk : G.Walk base base}, walk.IsCycle → Even walk.length) :
    G.Colorable 2 := by
  classical
  obtain ⟨F, hFG, hFacyclic, hreachable⟩ := G.exists_isAcyclic_reachable_eq_le
  let forestColorFin : F.Coloring (Fin 2) := hFacyclic.coloringTwo
  let forestColor : F.Coloring Bool :=
    F.recolorOfEquiv finTwoEquiv forestColorFin
  let graphColor : G.Coloring Bool := SimpleGraph.Coloring.mk forestColor (by
    intro left right hadj
    by_contra hsame
    have hreachG : G.Reachable left right := hadj.reachable
    have hreachF : F.Reachable left right := by
      rw [hreachable]
      exact hreachG
    obtain ⟨path, hpath⟩ := hreachF.exists_isPath
    have hpathEven : Even path.length :=
      (forestColor.even_length_iff_congr path).2 (by simp [hsame])
    have hedgeNotMem : s(left, right) ∉ path.edges := by
      intro hedgeMem
      exact (forestColor.valid (path.adj_of_mem_edges hedgeMem)) hsame
    let reversePath : G.Path right left :=
      ⟨path.reverse.mapLe hFG, hpath.reverse.mapLe hFG⟩
    have hnewCycle :=
      reversePath.cons_isCycle hadj (by simpa [reversePath] using hedgeNotMem)
    have hnewCycleEven := hcycle hnewCycle
    have hsuccEven : Even (path.length + 1) := by
      simpa [reversePath] using hnewCycleEven
    obtain ⟨pathHalf, hpathLength⟩ := hpathEven
    obtain ⟨cycleHalf, hcycleLength⟩ := hsuccEven
    omega)
  exact ⟨G.recolorOfEquiv finTwoEquiv.symm graphColor⟩

omit [Fintype V] [DecidableEq V] in
/-- Two edges distinct from a common base edge cannot both be the other edge at the base
source when outgoing fibers have cardinality at most two. -/
public theorem eq_of_conflict_of_source_eq
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (base left right : FiniteEdge edge)
    (hleft : EdgeConflict base left) (hright : EdgeConflict base right)
    (hleftSource : base.1.1 = left.1.1)
    (hrightSource : base.1.1 = right.1.1) :
    left = right := by
  classical
  obtain ⟨outPort, houtPort⟩ :=
    exists_finTwo_injOn {target | edge base.1.1 target} (hout base.1.1)
  have hleftTarget : left.1.2 ≠ base.1.2 := by
    intro htarget
    apply hleft.1
    apply Subtype.ext
    apply Prod.ext
    · exact hleftSource
    · exact htarget.symm
  have hrightTarget : right.1.2 ≠ base.1.2 := by
    intro htarget
    apply hright.1
    apply Subtype.ext
    apply Prod.ext
    · exact hrightSource
    · exact htarget.symm
  have hbaseEdge : edge base.1.1 base.1.2 := base.2
  have hleftEdge : edge base.1.1 left.1.2 := by
    simpa [hleftSource] using left.2
  have hrightEdge : edge base.1.1 right.1.2 := by
    simpa [hrightSource] using right.2
  have hleftPort : outPort left.1.2 ≠ outPort base.1.2 := by
    intro hport
    exact hleftTarget (houtPort hleftEdge hbaseEdge hport)
  have hrightPort : outPort right.1.2 ≠ outPort base.1.2 := by
    intro hport
    exact hrightTarget (houtPort hrightEdge hbaseEdge hport)
  have htarget : left.1.2 = right.1.2 :=
    houtPort hleftEdge hrightEdge (finTwo_eq_of_ne_same hleftPort hrightPort)
  apply Subtype.ext
  apply Prod.ext
  · exact hleftSource.symm.trans hrightSource
  · exact htarget

omit [Fintype V] [DecidableEq V] in
/-- The incoming-fiber dual of `eq_of_conflict_of_source_eq`. -/
public theorem eq_of_conflict_of_target_eq
    (edge : V → V → Prop)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2)
    (base left right : FiniteEdge edge)
    (hleft : EdgeConflict base left) (hright : EdgeConflict base right)
    (hleftTarget : base.1.2 = left.1.2)
    (hrightTarget : base.1.2 = right.1.2) :
    left = right := by
  classical
  obtain ⟨inPort, hinPort⟩ :=
    exists_finTwo_injOn {source | edge source base.1.2} (hin base.1.2)
  have hleftSource : left.1.1 ≠ base.1.1 := by
    intro hsource
    apply hleft.1
    apply Subtype.ext
    apply Prod.ext
    · exact hsource.symm
    · exact hleftTarget
  have hrightSource : right.1.1 ≠ base.1.1 := by
    intro hsource
    apply hright.1
    apply Subtype.ext
    apply Prod.ext
    · exact hsource.symm
    · exact hrightTarget
  have hbaseEdge : edge base.1.1 base.1.2 := base.2
  have hleftEdge : edge left.1.1 base.1.2 := by
    simpa [hleftTarget] using left.2
  have hrightEdge : edge right.1.1 base.1.2 := by
    simpa [hrightTarget] using right.2
  have hleftPort : inPort left.1.1 ≠ inPort base.1.1 := by
    intro hport
    exact hleftSource (hinPort hleftEdge hbaseEdge hport)
  have hrightPort : inPort right.1.1 ≠ inPort base.1.1 := by
    intro hport
    exact hrightSource (hinPort hrightEdge hbaseEdge hport)
  have hsource : left.1.1 = right.1.1 :=
    hinPort hleftEdge hrightEdge (finTwo_eq_of_ne_same hleftPort hrightPort)
  apply Subtype.ext
  apply Prod.ext
  · exact hsource
  · exact hleftTarget.symm.trans hrightTarget

/-- The endpoint kind of a conflict: zero for a shared source and one for a shared target.  Since
distinct relation edges cannot share both endpoints, this is unambiguous on conflicts. -/
public def edgeConflictKind {edge : V → V → Prop}
    (left right : FiniteEdge edge) : Fin 2 :=
  if left.1.1 = right.1.1 then 0 else 1

omit [Fintype V] in
/-- Along three distinct consecutive edges of the conflict graph, the shared endpoint kind must
alternate.  Otherwise all three relation edges would meet at one source or at one target. -/
public theorem edgeConflictKind_ne_of_distinct
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2)
    (left middle right : FiniteEdge edge)
    (hleft : EdgeConflict left middle)
    (hright : EdgeConflict middle right)
    (hne : left ≠ right) :
    edgeConflictKind left middle ≠ edgeConflictKind middle right := by
  intro hkinds
  by_cases hleftSource : left.1.1 = middle.1.1
  · have hrightSource : middle.1.1 = right.1.1 := by
      by_contra h
      simp [edgeConflictKind, hleftSource] at hkinds
      exact h hkinds
    exact hne (eq_of_conflict_of_source_eq edge hout middle left right
      hleft.symm hright hleftSource.symm hrightSource)
  · have hrightSource : ¬middle.1.1 = right.1.1 := by
      intro h
      simp [edgeConflictKind, h] at hkinds
      exact hleftSource (hkinds.trans h.symm)
    have hleftTarget : middle.1.2 = left.1.2 :=
      (hleft.2.resolve_left hleftSource).symm
    have hrightTarget : middle.1.2 = right.1.2 :=
      hright.2.resolve_left hrightSource
    exact hne (eq_of_conflict_of_target_eq edge hin middle left right
      hleft.symm hright hleftTarget hrightTarget)

omit [Fintype V] in
/-- Every simple cycle in the conflict graph of a finite degree-two relation has even length.
The conflict kind alternates around the cycle because its two neighbors at each cycle vertex are
distinct. -/
public theorem edgeConflictGraph_isCycle_even
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2)
    {base : FiniteEdge edge}
    {walk : (edgeConflictGraph edge).Walk base base}
    (hcycle : walk.IsCycle) :
    Even walk.length := by
  have hn : 0 < walk.length := by
    have := hcycle.three_le_length
    omega
  let label : Fin walk.length → Fin 2 := fun i =>
    edgeConflictKind (walk.getVert i.val) (walk.getVert (i.val + 1))
  apply even_of_finTwo_cyclic_alternation hn label
  · intro i hi
    apply edgeConflictKind_ne_of_distinct edge hout hin
    · exact walk.adj_getVert_succ (by omega)
    · exact walk.adj_getVert_succ hi
    · simpa [Nat.add_assoc] using
        hcycle.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega)
  · have hlast :
        EdgeConflict (walk.getVert (walk.length - 1)) (walk.getVert walk.length) := by
      simpa [edgeConflictGraph, Nat.sub_add_cancel (by omega : 1 ≤ walk.length)] using
        walk.adj_getVert_succ (i := walk.length - 1) (by omega)
    have hfirst : EdgeConflict (walk.getVert walk.length) (walk.getVert 1) := by
      simpa [edgeConflictGraph] using walk.adj_getVert_succ (i := 0) hn
    have houter : walk.getVert (walk.length - 1) ≠ walk.getVert 1 :=
      hcycle.snd_ne_penultimate.symm
    simpa [label, Nat.sub_add_cancel (by omega : 1 ≤ walk.length)] using
      edgeConflictKind_ne_of_distinct edge hout hin
        (walk.getVert (walk.length - 1)) (walk.getVert walk.length) (walk.getVert 1)
        hlast hfirst houter

/-- The conflict graph of a finite relation with at most two incoming and two outgoing edges at
each vertex is two-colorable.  Equivalently, its relation edges admit two colors such that edges
sharing a source or a target always receive different colors. -/
public theorem edgeConflictGraph_colorable_two
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2) :
    (edgeConflictGraph edge).Colorable 2 :=
  colorable_two_of_isCycle_even (edgeConflictGraph edge) fun hcycle =>
    edgeConflictGraph_isCycle_even edge hout hin hcycle

/-- At a fixed edge of a finite degree-two relation, there are at most two conflicting edges:
at most one sharing its source and at most one sharing its target.

The proof gives an explicit injection of the conflict fiber into `Fin 2`; the two values record
which endpoint is shared.  This is the local degree bound needed for the alternating-component
proof of the optimal two-layer decomposition. -/
public theorem card_edgeConflict_le_two
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2)
    (base : FiniteEdge edge) :
    Nat.card {other : FiniteEdge edge // EdgeConflict base other} ≤ 2 := by
  classical
  choose outPort houtPort using fun source =>
    exists_finTwo_injOn {target | edge source target} (hout source)
  choose inPort hinPort using fun target =>
    exists_finTwo_injOn {source | edge source target} (hin target)
  let side : {other : FiniteEdge edge // EdgeConflict base other} → Fin 2 :=
    fun other => if base.1.1 = other.1.1.1 then 0 else 1
  simpa using Nat.card_le_card_of_injective side (by
    intro left right hside
    apply Subtype.ext
    rcases left with ⟨left, hleft⟩
    rcases right with ⟨right, hright⟩
    by_cases hleftSource : base.1.1 = left.1.1
    · have hrightSource : base.1.1 = right.1.1 := by
        by_contra h
        simp [side, hleftSource] at hside
        exact h (hleftSource.trans hside)
      have hleftTarget : left.1.2 ≠ base.1.2 := by
        intro htarget
        apply hleft.1
        apply Subtype.ext
        apply Prod.ext
        · exact hleftSource
        · exact htarget.symm
      have hrightTarget : right.1.2 ≠ base.1.2 := by
        intro htarget
        apply hright.1
        apply Subtype.ext
        apply Prod.ext
        · exact hrightSource
        · exact htarget.symm
      have hbaseEdge : edge base.1.1 base.1.2 := base.2
      have hleftEdge : edge base.1.1 left.1.2 := by
        simpa [hleftSource] using left.2
      have hrightEdge : edge base.1.1 right.1.2 := by
        simpa [hrightSource] using right.2
      have hleftPort :
          outPort base.1.1 left.1.2 ≠ outPort base.1.1 base.1.2 := by
        intro hport
        exact hleftTarget (houtPort base.1.1 hleftEdge hbaseEdge hport)
      have hrightPort :
          outPort base.1.1 right.1.2 ≠ outPort base.1.1 base.1.2 := by
        intro hport
        exact hrightTarget (houtPort base.1.1 hrightEdge hbaseEdge hport)
      have htarget : left.1.2 = right.1.2 :=
        houtPort base.1.1 hleftEdge hrightEdge
          (finTwo_eq_of_ne_same hleftPort hrightPort)
      apply Subtype.ext
      apply Prod.ext
      · exact hleftSource.symm.trans hrightSource
      · exact htarget
    · have hrightSource : ¬base.1.1 = right.1.1 := by
        intro h
        simp [side, h] at hside
        exact hleftSource (h.trans hside)
      have hleftTarget : base.1.2 = left.1.2 :=
        hleft.2.resolve_left hleftSource
      have hrightTarget : base.1.2 = right.1.2 :=
        hright.2.resolve_left hrightSource
      have hbaseEdge : edge base.1.1 base.1.2 := base.2
      have hleftEdge : edge left.1.1 base.1.2 := by
        simpa [hleftTarget] using left.2
      have hrightEdge : edge right.1.1 base.1.2 := by
        simpa [hrightTarget] using right.2
      have hleftPort :
          inPort base.1.2 left.1.1 ≠ inPort base.1.2 base.1.1 := by
        intro hport
        exact hleftSource (hinPort base.1.2 hbaseEdge hleftEdge hport.symm)
      have hrightPort :
          inPort base.1.2 right.1.1 ≠ inPort base.1.2 base.1.1 := by
        intro hport
        exact hrightSource (hinPort base.1.2 hbaseEdge hrightEdge hport.symm)
      have hsource : left.1.1 = right.1.1 :=
        hinPort base.1.2 hleftEdge hrightEdge
          (finTwo_eq_of_ne_same hleftPort hrightPort)
      apply Subtype.ext
      apply Prod.ext
      · exact hsource
      · exact hleftTarget.symm.trans hrightTarget)

/-- The conflict graph of a finite relation with at most two incoming and two outgoing edges at
each vertex has graph-theoretic degree at most two. -/
public theorem edgeConflictGraph_degree_le_two
    (edge : V → V → Prop) [DecidableRel edge]
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2)
    (base : FiniteEdge edge) :
    (edgeConflictGraph edge).degree base ≤ 2 := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  change Fintype.card {other : FiniteEdge edge // EdgeConflict base other} ≤ 2
  simpa only [Nat.card_eq_fintype_card] using
    card_edgeConflict_le_two edge hout hin base

omit [Fintype V] in
/-- A proper coloring of the edge-conflict graph partitions the original relation into
bi-unique color layers.  This theorem is independent of the number of colors and isolates the
precise graph-coloring content of partial-bijection decompositions. -/
public theorem exists_biUnique_partition_of_conflictColoring
    {Color : Type*} (edge : V → V → Prop)
    (coloring : (edgeConflictGraph edge).Coloring Color) :
    ∃ layer : Color → V → V → Prop,
      (∀ source target, edge source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target, layer color source target → edge source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  classical
  let layer : Color → V → V → Prop := fun color source target =>
    ∃ hedge : edge source target,
      coloring (⟨(source, target), hedge⟩ : FiniteEdge edge) = color
  refine ⟨layer, ?_, ?_, ?_⟩
  · intro source target
    constructor
    · intro hedge
      let e : FiniteEdge edge := ⟨(source, target), hedge⟩
      refine ⟨coloring e, ⟨hedge, rfl⟩, ?_⟩
      intro color hcolor
      obtain ⟨hedge', hcolor'⟩ := hcolor
      have heq : (⟨(source, target), hedge'⟩ : FiniteEdge edge) = e :=
        Subtype.ext rfl
      simpa [heq] using hcolor'.symm
    · rintro ⟨color, ⟨hedge, _⟩, _⟩
      exact hedge
  · intro color source target hcolor
    exact hcolor.choose
  · intro color
    constructor
    · intro left right target hleft hright
      obtain ⟨hleftEdge, hleftColor⟩ := hleft
      obtain ⟨hrightEdge, hrightColor⟩ := hright
      by_contra hne
      let leftEdge : FiniteEdge edge := ⟨(left, target), hleftEdge⟩
      let rightEdge : FiniteEdge edge := ⟨(right, target), hrightEdge⟩
      have hedgeNe : leftEdge ≠ rightEdge := by
        intro hedgeEq
        apply hne
        exact congrArg (fun e : FiniteEdge edge => e.1.1) hedgeEq
      have hadj : (edgeConflictGraph edge).Adj leftEdge rightEdge :=
        ⟨hedgeNe, Or.inr rfl⟩
      exact (coloring.valid hadj) (hleftColor.trans hrightColor.symm)
    · intro source left right hleft hright
      obtain ⟨hleftEdge, hleftColor⟩ := hleft
      obtain ⟨hrightEdge, hrightColor⟩ := hright
      by_contra hne
      let leftEdge : FiniteEdge edge := ⟨(source, left), hleftEdge⟩
      let rightEdge : FiniteEdge edge := ⟨(source, right), hrightEdge⟩
      have hedgeNe : leftEdge ≠ rightEdge := by
        intro hedgeEq
        apply hne
        exact congrArg (fun e : FiniteEdge edge => e.1.2) hedgeEq
      have hadj : (edgeConflictGraph edge).Adj leftEdge rightEdge :=
        ⟨hedgeNe, Or.inl rfl⟩
      exact (coloring.valid hadj) (hleftColor.trans hrightColor.symm)

omit [Fintype V] in
/-- If the edge-conflict graph is two-colorable, the relation has a two-layer bi-unique
partition. -/
public theorem exists_two_biUnique_partition_of_conflictColorable
    (edge : V → V → Prop)
    (hcolorable : (edgeConflictGraph edge).Colorable 2) :
    ∃ layer : Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target, layer color source target → edge source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  exact exists_biUnique_partition_of_conflictColoring edge hcolorable.some

/-- Every finite directed relation with at most two successors and at most two predecessors at
each vertex is partitioned into two bi-unique relations.

The two layers are optimal in general: a vertex with two distinct outgoing edges forces those
edges into different layers. -/
public theorem exists_two_biUnique_partition
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2) :
    ∃ layer : Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target, layer color source target → edge source target) ∧
        ∀ color, Relator.BiUnique (layer color) :=
  exists_two_biUnique_partition_of_conflictColorable edge
    (edgeConflictGraph_colorable_two edge hout hin)

end Finite

end PartialBijectionDecomposition

namespace LBA

variable {Γ Λ : Type*}

/-- At every fixed tape width, a degree-two LBA configuration relation is exactly the union of
four partial bijections.  The four layers may depend on the width; the number of layers does not.
-/
public theorem Machine.exists_four_biUnique_step_decomposition
    (M : Machine Γ Λ) (hdegree : M.ConfigurationDegreeAtMostTwo) (n : ℕ) :
    ∃ layer : Fin 2 × Fin 2 →
        DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop,
      (∀ source target,
        Step M source target ↔ ∃ color, layer color source target) ∧
        ∀ color, Relator.BiUnique (layer color) :=
  PartialBijectionDecomposition.exists_four_biUnique_decomposition
    (Step M) (hdegree.1 n) (hdegree.2 n)

/-- At every fixed tape width, the four partial-bijection layers can be chosen so that every
machine edge belongs to exactly one of them. -/
public theorem Machine.exists_four_biUnique_step_partition
    (M : Machine Γ Λ) (hdegree : M.ConfigurationDegreeAtMostTwo) (n : ℕ) :
    ∃ layer : Fin 2 × Fin 2 →
        DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop,
      (∀ source target,
        Step M source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target,
          layer color source target → Step M source target) ∧
        ∀ color, Relator.BiUnique (layer color) :=
  PartialBijectionDecomposition.exists_four_biUnique_partition
    (Step M) (hdegree.1 n) (hdegree.2 n)

/-- At every fixed tape width, a degree-two LBA configuration relation is partitioned into two
partial bijections.

The layers are chosen classically and may depend on the tape width.  This theorem therefore does
not provide a uniform transition-table decomposition or a determinization construction. -/
public theorem Machine.exists_two_biUnique_step_partition
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hdegree : M.ConfigurationDegreeAtMostTwo) (n : ℕ) :
    ∃ layer : Fin 2 →
        DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop,
      (∀ source target,
        Step M source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target,
          layer color source target → Step M source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  classical
  exact PartialBijectionDecomposition.exists_two_biUnique_partition
    (Step M) (hdegree.1 n) (hdegree.2 n)

end LBA

end
