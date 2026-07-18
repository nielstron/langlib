module

public import Langlib.Automata.LinearBounded.DiamondPaths
public import Langlib.Automata.LinearBounded.ThreeMatchingReachability
import Mathlib.Tactic

@[expose]
public section

/-!
# Linearly many relevant branches in exact three-matching DAGs

Splitting every vertex of the `k`-diamond chain into an input and output copy turns its two
partial-bijection edge colors into three directed matchings.  The resulting graph is acyclic,
has exactly `6 * k + 2` vertices, and has `k` distinct genuine branch vertices.  Every one of
those branches is reachable from the designated source and can still reach the designated
target.

Thus the constant-one branch-event argument for exact unions of two directed matchings cannot
extend to three matchings: relevant branch points can grow linearly with the graph.  This is not
a deterministic-space lower bound.  In particular, it does not rule out recomputation or a
target-dependent algorithm which avoids storing all branch choices simultaneously.
-/

namespace ThreeMatchingDiamondBranches

open Relation

/-! ## The split diamond graph and its three layers -/

/-- Input and output copies of vertices in a `k`-diamond chain. -/
public abbrev Vertex (k : ℕ) :=
  ThreeMatchingReachability.Vertex (DiamondPaths.Vertex k)

/-- The split diamond edge relation. -/
@[expose]
public def Edge (k : ℕ) : Vertex k → Vertex k → Prop :=
  ThreeMatchingReachability.Edge (DiamondPaths.Edge k)

/-- Reindex the two Boolean diamond layers by `Fin 2`. -/
@[expose]
public def OldLayer (k : ℕ) (color : Fin 2) :
    DiamondPaths.Vertex k → DiamondPaths.Vertex k → Prop :=
  DiamondPaths.edgeLayer k (finTwoEquiv color)

/-- The three directed matching layers of the split graph. -/
@[expose]
public def Layer (k : ℕ) (color : Fin 3) : Vertex k → Vertex k → Prop :=
  ThreeMatchingReachability.Layer (OldLayer k) color

/-- The designated input-copy source. -/
@[expose]
public def source (k : ℕ) : Vertex k :=
  .input (DiamondPaths.source k)

/-- The designated output-copy target. -/
@[expose]
public def target (k : ℕ) : Vertex k :=
  .output (DiamondPaths.target k)

/-- The output copy of junction `i`, for a junction which has a following diamond. -/
@[expose]
public def branchJunction {k : ℕ} (i : Fin k) : Vertex k :=
  .output (DiamondPaths.junction i.castSucc)

/-- The input copy of one of the two children of junction `i`. -/
@[expose]
public def branchChild {k : ℕ} (i : Fin k) (bit : Bool) : Vertex k :=
  .input (DiamondPaths.branch i bit)

/-- Reindexing by `Fin 2` preserves the exact two-color cover. -/
public theorem oldEdge_iff_existsUnique_oldLayer
    (k : ℕ) (old new : DiamondPaths.Vertex k) :
    DiamondPaths.Edge k old new ↔ ∃! color, OldLayer k color old new := by
  constructor
  · intro hedge
    obtain ⟨color, hcolor, hunique⟩ :=
      (DiamondPaths.edgeLayer_exact k old new).mp hedge
    refine ⟨finTwoEquiv.symm color, ?_, ?_⟩
    · simpa [OldLayer] using hcolor
    · intro other hother
      apply finTwoEquiv.injective
      simpa using hunique _ (by simpa [OldLayer] using hother)
  · rintro ⟨color, hcolor, _⟩
    exact hcolor.1

/-- Every reindexed old layer contains only diamond edges. -/
public theorem oldLayer_sub_edge
    (k : ℕ) (color : Fin 2) (old new : DiamondPaths.Vertex k)
    (hlayer : OldLayer k color old new) :
    DiamondPaths.Edge k old new :=
  hlayer.1

/-- Every reindexed old layer is a partial bijection. -/
public theorem oldLayer_biUnique (k : ℕ) (color : Fin 2) :
    Relator.BiUnique (OldLayer k color) :=
  DiamondPaths.edgeLayer_biUnique k (finTwoEquiv color)

/-- Every split edge has exactly one of the three supplied colors. -/
public theorem edge_iff_existsUnique_layer (k : ℕ) (old new : Vertex k) :
    Edge k old new ↔ ∃! color, Layer k color old new :=
  ThreeMatchingReachability.edge_iff_existsUnique_layer
    (oldEdge_iff_existsUnique_oldLayer k) (oldLayer_sub_edge k) old new

/-- A split layer contains no spurious edges. -/
public theorem layer_sub_edge
    (k : ℕ) (color : Fin 3) (old new : Vertex k)
    (hlayer : Layer k color old new) : Edge k old new :=
  ThreeMatchingReachability.layer_sub_edge (oldLayer_sub_edge k) hlayer

/-- Each split layer is both functional and cofunctional. -/
public theorem layer_biUnique (k : ℕ) (color : Fin 3) :
    Relator.BiUnique (Layer k color) :=
  ThreeMatchingReachability.layer_biUnique (oldLayer_biUnique k) color

/-- No two edges in one split layer are composable. -/
public theorem layer_pathLengthAtMostOne (k : ℕ) (color : Fin 3) :
    LinearTwoDiforestReachability.PathLengthAtMostOne (Layer k color) :=
  ThreeMatchingReachability.layer_pathLengthAtMostOne (OldLayer k) color

/-! ## Acyclicity, size, and designated reachability -/

/-- Every split-diamond edge strictly raises the lifted diamond rank. -/
public theorem liftedRank_lt_of_edge {k : ℕ} {old new : Vertex k}
    (h : Edge k old new) :
    ThreeMatchingReachability.liftedRank (DiamondPaths.rank (k := k)) old <
      ThreeMatchingReachability.liftedRank (DiamondPaths.rank (k := k)) new := by
  apply ThreeMatchingReachability.liftedRank_lt_of_edge
    (edge := DiamondPaths.Edge k)
    (DiamondPaths.rank (k := k))
  · intro first last hstep
    have hrank := DiamondPaths.rank_eq_succ_of_edge hstep
    omega
  · exact h

/-- The split diamond graph is acyclic. -/
public theorem acyclic (k : ℕ) (vertex : Vertex k) :
    ¬ TransGen (Edge k) vertex vertex := by
  apply ThreeMatchingReachability.acyclic_of_rank
    (edge := DiamondPaths.Edge k)
    (DiamondPaths.rank (k := k))
  intro old new hstep
  have hrank := DiamondPaths.rank_eq_succ_of_edge hstep
  omega

/-- The split `k`-diamond graph has exactly `6 * k + 2` vertices. -/
public theorem card_vertex (k : ℕ) :
    Fintype.card (Vertex k) = Nat.mul 6 k + 2 := by
  rw [ThreeMatchingReachability.card_vertex, DiamondPaths.card_vertex]
  simp [Nat.succ_mul]
  omega

/-- The diamond source reaches every junction. -/
public theorem source_reaches_junction {k : ℕ} (i : Fin (k + 1)) :
    ReflTransGen (DiamondPaths.Edge k)
      (DiamondPaths.source k) (DiamondPaths.junction i) := by
  induction i using Fin.induction with
  | zero => exact .refl
  | succ i ih =>
      have henter : DiamondPaths.Edge k
          (DiamondPaths.junction i.castSucc) (DiamondPaths.branch i false) := by
        simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]
      have hleave : DiamondPaths.Edge k
          (DiamondPaths.branch i false) (DiamondPaths.junction i.succ) := by
        simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]
      exact (ih.tail henter).tail hleave

/-- Every junction reaches the last junction. -/
public theorem junction_reaches_target {k : ℕ} (i : Fin (k + 1)) :
    ReflTransGen (DiamondPaths.Edge k)
      (DiamondPaths.junction i) (DiamondPaths.target k) := by
  induction i using Fin.reverseInduction with
  | last => exact .refl
  | cast i ih =>
      have henter : DiamondPaths.Edge k
          (DiamondPaths.junction i.castSucc) (DiamondPaths.branch i false) := by
        simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]
      have hleave : DiamondPaths.Edge k
          (DiamondPaths.branch i false) (DiamondPaths.junction i.succ) := by
        simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]
      exact (ReflTransGen.single henter).trans
        ((ReflTransGen.single hleave).trans ih)

private theorem junction_reaches_add
    {k : ℕ} (first : Fin (k + 1)) :
    ∀ (distance : ℕ) (hbound : first.val + distance < k + 1),
      ReflTransGen (DiamondPaths.Edge k)
        (DiamondPaths.junction first)
        (DiamondPaths.junction ⟨first.val + distance, hbound⟩)
  | 0, hbound => by
      have heq : (⟨first.val + 0, hbound⟩ : Fin (k + 1)) = first := by
        apply Fin.ext
        simp
      rw [heq]
  | distance + 1, hbound => by
      have hprevious : first.val + distance < k + 1 := by omega
      have hdiamond : first.val + distance < k := by omega
      let previous : Fin (k + 1) := ⟨first.val + distance, hprevious⟩
      let diamond : Fin k := ⟨first.val + distance, hdiamond⟩
      have hreach := junction_reaches_add first distance hprevious
      have henter : DiamondPaths.Edge k
          (DiamondPaths.junction previous)
          (DiamondPaths.branch diamond false) := by
        simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch,
          previous, diamond]
      have hleave : DiamondPaths.Edge k
          (DiamondPaths.branch diamond false)
          (DiamondPaths.junction ⟨first.val + (distance + 1), hbound⟩) := by
        simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch,
          diamond]
        omega
      exact (hreach.tail henter).tail hleave

/-- Earlier junctions reach later junctions in their index order. -/
public theorem junction_reaches_junction_of_le
    {k : ℕ} (first last : Fin (k + 1)) (hle : first.val ≤ last.val) :
    ReflTransGen (DiamondPaths.Edge k)
      (DiamondPaths.junction first) (DiamondPaths.junction last) := by
  let distance := last.val - first.val
  have hsum : first.val + distance = last.val := by
    exact Nat.add_sub_of_le hle
  have hbound : first.val + distance < k + 1 := by
    rw [hsum]
    exact last.isLt
  have hreach := junction_reaches_add first distance hbound
  have heq : (⟨first.val + distance, hbound⟩ : Fin (k + 1)) = last := by
    apply Fin.ext
    exact hsum
  rwa [heq] at hreach

/-- An old path lifts between output copies without adding an initial internal edge. -/
public theorem output_reaches_output_of_reaches
    {k : ℕ} {old new : DiamondPaths.Vertex k}
    (hreach : ReflTransGen (DiamondPaths.Edge k) old new) :
    ReflTransGen (Edge k) (.output old) (.output new) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.trans (ThreeMatchingReachability.reaches_output_of_edge hstep)

/-- The designated split source reaches the designated split target, including at `k = 0`. -/
public theorem source_reaches_target (k : ℕ) :
    ReflTransGen (Edge k) (source k) (target k) := by
  apply ThreeMatchingReachability.reaches_output_of_reaches
  simpa only [DiamondPaths.target] using
    source_reaches_junction (Fin.last k)

/-! ## The linearly many relevant branches -/

private theorem diamond_successor_eq_of_branch
    {k : ℕ} {i : Fin k} {bit : Bool} {left right : DiamondPaths.Vertex k}
    (hleft : DiamondPaths.Edge k (DiamondPaths.branch i bit) left)
    (hright : DiamondPaths.Edge k (DiamondPaths.branch i bit) right) :
    left = right := by
  rcases left with left | ⟨leftIndex, leftBit⟩ <;>
    rcases right with right | ⟨rightIndex, rightBit⟩ <;>
    simp only [DiamondPaths.Edge, DiamondPaths.branch] at hleft hright
  · exact congrArg Sum.inl (hleft.trans hright.symm)

/-- In the unsplit diamond chain, genuine branches are exactly the nonfinal junctions. -/
private theorem diamond_branches_iff_exists_junction
    {k : ℕ} {vertex : DiamondPaths.Vertex k} :
    ThreeMatchingReachability.Branches (DiamondPaths.Edge k) vertex ↔
      ∃ i : Fin k, vertex = DiamondPaths.junction i.castSucc := by
  constructor
  · rintro ⟨left, right, hleft, hright, hne⟩
    rcases vertex with junctionIndex | ⟨branchIndex, branchBit⟩
    · rcases left with leftJunction | ⟨leftIndex, leftBit⟩
      · simp [DiamondPaths.Edge] at hleft
      · have hindex : junctionIndex = leftIndex.castSucc := by
          simpa [DiamondPaths.Edge] using hleft
        exact ⟨leftIndex, congrArg Sum.inl hindex⟩
    · exact False.elim
        (hne (diamond_successor_eq_of_branch hleft hright))
  · rintro ⟨i, rfl⟩
    refine ⟨DiamondPaths.branch i false, DiamondPaths.branch i true, ?_, ?_, ?_⟩
    · simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]
    · simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]
    · intro heq
      simp [DiamondPaths.branch] at heq

private theorem split_successor_eq_of_input
    {k : ℕ} {vertex : DiamondPaths.Vertex k} {left right : Vertex k}
    (hleft : Edge k (.input vertex) left)
    (hright : Edge k (.input vertex) right) : left = right := by
  rcases left with left | left <;> rcases right with right | right <;>
    simp only [Edge, ThreeMatchingReachability.Edge] at hleft hright
  · exact congrArg ThreeMatchingReachability.Vertex.output
      (hleft.symm.trans hright)

/-- The split graph's genuine branches are exactly the `k` named junction-output copies. -/
public theorem branches_iff_exists_branchJunction
    {k : ℕ} {vertex : Vertex k} :
    ThreeMatchingReachability.Branches (Edge k) vertex ↔
      ∃ i : Fin k, vertex = branchJunction i := by
  constructor
  · rintro ⟨left, right, hleft, hright, hne⟩
    rcases vertex with old | old
    · exact False.elim (hne (split_successor_eq_of_input hleft hright))
    · rcases left with left | left
      · rcases right with right | right
        · have holdLeft : DiamondPaths.Edge k old left := hleft
          have holdRight : DiamondPaths.Edge k old right := hright
          have holdNe : left ≠ right := by
            intro heq
            exact hne (congrArg ThreeMatchingReachability.Vertex.input heq)
          obtain ⟨i, hi⟩ :=
            diamond_branches_iff_exists_junction.mp
              ⟨left, right, holdLeft, holdRight, holdNe⟩
          exact ⟨i, congrArg ThreeMatchingReachability.Vertex.output hi⟩
        · simp [Edge, ThreeMatchingReachability.Edge] at hright
      · simp [Edge, ThreeMatchingReachability.Edge] at hleft
  · rintro ⟨i, rfl⟩
    refine ⟨branchChild i false, branchChild i true, ?_, ?_, ?_⟩
    · apply ThreeMatchingReachability.edge_external
      simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]
    · apply ThreeMatchingReachability.edge_external
      simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]
    · intro heq
      change ThreeMatchingReachability.Vertex.input (DiamondPaths.branch i false) =
        ThreeMatchingReachability.Vertex.input (DiamondPaths.branch i true) at heq
      injection heq with hbranch
      simp [DiamondPaths.branch] at hbranch

/-- Each named junction output has both Boolean branch children as split successors. -/
public theorem edge_branchChild {k : ℕ} (i : Fin k) (bit : Bool) :
    Edge k (branchJunction i) (branchChild i bit) := by
  apply ThreeMatchingReachability.edge_external
  simp [DiamondPaths.Edge, DiamondPaths.junction, DiamondPaths.branch]

/-- The two children of one split branch junction are distinct. -/
public theorem branchChild_false_ne_true {k : ℕ} (i : Fin k) :
    branchChild i false ≠ branchChild i true := by
  intro heq
  change ThreeMatchingReachability.Vertex.input (DiamondPaths.branch i false) =
    ThreeMatchingReachability.Vertex.input (DiamondPaths.branch i true) at heq
  injection heq with hbranch
  simp [DiamondPaths.branch] at hbranch

/-- Every named junction output is a genuine branch. -/
public theorem branches_branchJunction {k : ℕ} (i : Fin k) :
    ThreeMatchingReachability.Branches (Edge k) (branchJunction i) :=
  ⟨branchChild i false, branchChild i true,
    edge_branchChild i false, edge_branchChild i true,
    branchChild_false_ne_true i⟩

/-- Every named branch junction is reachable from the designated source. -/
public theorem source_reaches_branchJunction {k : ℕ} (i : Fin k) :
    ReflTransGen (Edge k) (source k) (branchJunction i) := by
  exact ThreeMatchingReachability.reaches_output_of_reaches
    (source_reaches_junction i.castSucc)

/-- Every named branch junction can still reach the designated target. -/
public theorem branchJunction_reaches_target {k : ℕ} (i : Fin k) :
    ReflTransGen (Edge k) (branchJunction i) (target k) := by
  exact output_reaches_output_of_reaches
    (junction_reaches_target i.castSucc)

/-- The named relevant branches occur in diamond-index order. -/
public theorem branchJunction_reaches_branchJunction_of_le
    {k : ℕ} (first last : Fin k) (hle : first.val ≤ last.val) :
    ReflTransGen (Edge k) (branchJunction first) (branchJunction last) := by
  exact output_reaches_output_of_reaches
    (junction_reaches_junction_of_le first.castSucc last.castSucc hle)

/-- Distinct diamond indices give distinct branch junctions. -/
public theorem branchJunction_injective (k : ℕ) :
    Function.Injective (@branchJunction k) := by
  intro left right heq
  have hproject := congrArg ThreeMatchingReachability.project heq
  simp only [branchJunction, ThreeMatchingReachability.project,
    DiamondPaths.junction, Sum.inl.injEq] at hproject
  exact Fin.castSucc_injective _ hproject

/-- There are `k` injectively named genuine branches lying between the designated source and
target. -/
public theorem exists_k_relevant_branches (k : ℕ) :
    ∃ branches : Fin k → Vertex k,
      Function.Injective branches ∧
        (∀ i, ReflTransGen (Edge k) (source k) (branches i) ∧
          ThreeMatchingReachability.Branches (Edge k) (branches i) ∧
          ReflTransGen (Edge k) (branches i) (target k)) ∧
        ∀ i j, i.val ≤ j.val →
          ReflTransGen (Edge k) (branches i) (branches j) :=
  ⟨branchJunction, branchJunction_injective k, fun i ↦
    ⟨source_reaches_branchJunction i, branches_branchJunction i,
      branchJunction_reaches_target i⟩,
    fun i j hle ↦ branchJunction_reaches_branchJunction_of_le i j hle⟩

/-- The split diamond graph has exactly `k` genuine branch vertices. -/
public theorem ncard_branchVertices (k : ℕ) :
    Set.ncard {vertex : Vertex k |
      ThreeMatchingReachability.Branches (Edge k) vertex} = k := by
  have hset :
      {vertex : Vertex k |
        ThreeMatchingReachability.Branches (Edge k) vertex} =
        Set.range (@branchJunction k) := by
    ext vertex
    rw [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro hbranch
      obtain ⟨i, hi⟩ := branches_iff_exists_branchJunction.mp hbranch
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact branches_iff_exists_branchJunction.mpr ⟨i, rfl⟩
  rw [hset, Set.ncard_range_of_injective (branchJunction_injective k)]
  simp

/-- Packaged obstruction: for every `k`, the same designated finite DAG is an exact union of
three directed matchings and contains `k` distinct source-to-target-relevant branch vertices. -/
public theorem exactThreeMatching_relevantBranch_obstruction (k : ℕ) :
    Fintype.card (Vertex k) = Nat.mul 6 k + 2 ∧
      Set.ncard {vertex : Vertex k |
        ThreeMatchingReachability.Branches (Edge k) vertex} = k ∧
      (∀ vertex, ¬ TransGen (Edge k) vertex vertex) ∧
      (∀ old new, Edge k old new ↔ ∃! color, Layer k color old new) ∧
      (∀ color old new, Layer k color old new → Edge k old new) ∧
      (∀ color, Relator.BiUnique (Layer k color)) ∧
      (∀ color,
        LinearTwoDiforestReachability.PathLengthAtMostOne (Layer k color)) ∧
      ReflTransGen (Edge k) (source k) (target k) ∧
      ∃ branches : Fin k → Vertex k,
        Function.Injective branches ∧
          (∀ i, ReflTransGen (Edge k) (source k) (branches i) ∧
            ThreeMatchingReachability.Branches (Edge k) (branches i) ∧
            ReflTransGen (Edge k) (branches i) (target k)) ∧
          ∀ i j, i.val ≤ j.val →
            ReflTransGen (Edge k) (branches i) (branches j) :=
  ⟨card_vertex k, ncard_branchVertices k, acyclic k, edge_iff_existsUnique_layer k,
    layer_sub_edge k, layer_biUnique k, layer_pathLengthAtMostOne k,
    source_reaches_target k, exists_k_relevant_branches k⟩

end ThreeMatchingDiamondBranches

end
