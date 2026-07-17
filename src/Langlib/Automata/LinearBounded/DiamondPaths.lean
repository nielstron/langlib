module

public import Mathlib.Data.Set.Card
import Mathlib.Tactic

@[expose]
public section

/-!
# Degree-two acyclic graphs can have exponentially many paths

This file records a small graph-theoretic obstruction relevant to deterministic simulation of
linear-bounded automata.  A chain of `k` diamonds has only `3 * k + 1` vertices, is acyclic, and
has both directed indegree and directed outdegree at most two.  Nevertheless, every bit vector
of length `k` determines a distinct path from the first junction to the last junction.

Paths are represented as data rather than merely by a reachability proposition.  This matters:
proof irrelevance would identify all proofs of the same propositional reachability statement,
whereas the middle vertex chosen in each diamond is genuine path information.
-/

namespace DiamondPaths

open Relation

/-- The vertices of a chain of `k` diamonds.

The left summand contains the `k + 1` junctions.  The right summand contains the two middle
vertices of each of the `k` diamonds. -/
public abbrev Vertex (k : ℕ) :=
  Fin (k + 1) ⊕ (Fin k × Bool)

/-- The junction at level `i`. -/
@[expose]
public def junction {k : ℕ} (i : Fin (k + 1)) : Vertex k :=
  Sum.inl i

/-- The middle vertex selected by `bit` in diamond `i`. -/
@[expose]
public def branch {k : ℕ} (i : Fin k) (bit : Bool) : Vertex k :=
  Sum.inr (i, bit)

/-- The source of the diamond chain. -/
@[expose]
public def source (k : ℕ) : Vertex k :=
  junction 0

/-- The target of the diamond chain. -/
@[expose]
public def target (k : ℕ) : Vertex k :=
  junction (Fin.last k)

/-- Directed edges in the chain of diamonds.

Each diamond has one edge from its left junction to each middle vertex and one edge from each
middle vertex to its right junction. -/
@[expose]
public def Edge (k : ℕ) : Vertex k → Vertex k → Prop
  | Sum.inl left, Sum.inr (i, _) => left = i.castSucc
  | Sum.inr (i, _), Sum.inl right => right = i.succ
  | _, _ => False

/-- The chain of `k` diamonds has exactly `3 * k + 1` vertices. -/
public theorem card_vertex (k : ℕ) :
    Fintype.card (Vertex k) = k + k + k + 1 := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool]
  omega

/-- A topological rank on the vertices.  Every edge increases this rank by exactly one. -/
@[expose]
public def rank {k : ℕ} : Vertex k → ℕ
  | Sum.inl i => i.val + i.val
  | Sum.inr (i, _) => i.val + i.val + 1

/-- Every diamond-chain edge increases the topological rank by one. -/
public theorem rank_eq_succ_of_edge {k : ℕ} {old new : Vertex k}
    (hedge : Edge k old new) :
    rank new = rank old + 1 := by
  rcases old with left | ⟨i, bit⟩ <;>
    rcases new with right | ⟨j, branchBit⟩ <;>
    simp only [Edge] at hedge
  · subst left
    simp only [rank, Fin.val_castSucc]
  · subst right
    simp only [rank, Fin.val_succ]
    omega

/-- Every nonempty directed path strictly increases topological rank. -/
public theorem rank_lt_of_transGen {k : ℕ} {old new : Vertex k}
    (hpath : TransGen (Edge k) old new) :
    rank old < rank new := by
  induction hpath with
  | single hedge =>
      rw [rank_eq_succ_of_edge hedge]
      exact Nat.lt_succ_self _
  | tail hpath hedge ih =>
      rw [rank_eq_succ_of_edge hedge]
      exact ih.trans (Nat.lt_succ_self _)

/-- The chain of diamonds is acyclic. -/
public theorem acyclic (k : ℕ) (vertex : Vertex k) :
    ¬ TransGen (Edge k) vertex vertex := by
  intro hcycle
  exact (Nat.lt_irrefl (rank vertex)) (rank_lt_of_transGen hcycle)

/-- Read the Boolean tag of a branch vertex.  The value at a junction is arbitrary; among
successors or predecessors of any fixed vertex there is at most one junction. -/
@[expose]
public def degreeTag {k : ℕ} : Vertex k → Bool
  | Sum.inl _ => false
  | Sum.inr (_, bit) => bit

private theorem target_eq_of_edges_of_tag_eq {k : ℕ} {old left right : Vertex k}
    (hleft : Edge k old left) (hright : Edge k old right)
    (htag : degreeTag left = degreeTag right) :
    left = right := by
  rcases old with oldJunction | ⟨oldBranch, oldBit⟩ <;>
    rcases left with leftJunction | ⟨leftBranch, leftBit⟩ <;>
    rcases right with rightJunction | ⟨rightBranch, rightBit⟩ <;>
    simp only [Edge, degreeTag] at hleft hright htag
  · apply congrArg Sum.inr
    apply Prod.ext
    · exact Fin.castSucc_inj.mp (hleft.symm.trans hright)
    · exact htag
  · rw [hleft, hright]

private theorem source_eq_of_edges_of_tag_eq {k : ℕ} {left right new : Vertex k}
    (hleft : Edge k left new) (hright : Edge k right new)
    (htag : degreeTag left = degreeTag right) :
    left = right := by
  rcases new with newJunction | ⟨newBranch, newBit⟩ <;>
    rcases left with leftJunction | ⟨leftBranch, leftBit⟩ <;>
    rcases right with rightJunction | ⟨rightBranch, rightBit⟩ <;>
    simp only [Edge, degreeTag] at hleft hright htag
  · apply congrArg Sum.inr
    apply Prod.ext
    · exact Fin.succ_inj.mp (hleft.symm.trans hright)
    · exact htag
  · rw [hleft, hright]

/-- A directed relation has outdegree at most two when every successor set has cardinality at
most two. -/
public def OutdegreeAtMostTwo {V : Type*} (edge : V → V → Prop) : Prop :=
  ∀ old, Set.encard {new | edge old new} ≤ 2

/-- A directed relation has indegree at most two when every predecessor set has cardinality at
most two. -/
public def IndegreeAtMostTwo {V : Type*} (edge : V → V → Prop) : Prop :=
  ∀ new, Set.encard {old | edge old new} ≤ 2

/-- Every vertex of the diamond chain has at most two distinct immediate successors. -/
public theorem outdegreeAtMostTwo (k : ℕ) :
    OutdegreeAtMostTwo (Edge k) := by
  intro old
  calc
    Set.encard {new | Edge k old new} ≤ Set.encard (Set.univ : Set Bool) := by
      apply Set.encard_le_encard_of_injOn (f := degreeTag)
      · intro new _
        exact Set.mem_univ _
      · intro left hleft right hright htag
        exact target_eq_of_edges_of_tag_eq hleft hright htag
    _ = 2 := by
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]
      norm_num

/-- Every vertex of the diamond chain has at most two distinct immediate predecessors. -/
public theorem indegreeAtMostTwo (k : ℕ) :
    IndegreeAtMostTwo (Edge k) := by
  intro new
  calc
    Set.encard {old | Edge k old new} ≤ Set.encard (Set.univ : Set Bool) := by
      apply Set.encard_le_encard_of_injOn (f := degreeTag)
      · intro old _
        exact Set.mem_univ _
      · intro left hleft right hright htag
        exact source_eq_of_edges_of_tag_eq hleft hright htag
    _ = 2 := by
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]
      norm_num

/-- An explicit source-to-target path through a chain of diamonds.

The fields record all `2 * k + 1` visited vertices in alternating form, together with each of
the `2 * k` edge witnesses. -/
public structure STPath (k : ℕ) where
  junctionAt : Fin (k + 1) → Vertex k
  branchAt : Fin k → Vertex k
  source_eq : junctionAt 0 = source k
  target_eq : junctionAt (Fin.last k) = target k
  enter : ∀ i : Fin k, Edge k (junctionAt i.castSucc) (branchAt i)
  leave : ∀ i : Fin k, Edge k (branchAt i) (junctionAt i.succ)

/-- Follow the upper or lower branch in diamond `i` according to `bits i`. -/
@[expose]
public def pathOfBits {k : ℕ} (bits : Fin k → Bool) : STPath k where
  junctionAt := junction
  branchAt := fun i => branch i (bits i)
  source_eq := rfl
  target_eq := rfl
  enter := fun i => by simp [Edge, junction, branch]
  leave := fun i => by simp [Edge, junction, branch]

/-- Every junction field in an explicit source-to-target path is the junction at the
corresponding level.  The proof uses the preceding edge to propagate this fact from the fixed
source. -/
public theorem STPath.junctionAt_eq {k : ℕ} (path : STPath k)
    (i : Fin (k + 1)) :
    path.junctionAt i = junction i := by
  induction i using Fin.induction with
  | zero =>
      exact path.source_eq
  | succ i ih =>
      have henter := path.enter i
      rw [ih] at henter
      rcases hbranch : path.branchAt i with branchJunction | ⟨j, bit⟩
      · rw [hbranch] at henter
        simp [Edge, junction] at henter
      · rw [hbranch] at henter
        have hindex : i = j := by
          simpa [Edge, junction] using henter
        subst j
        have hleave := path.leave i
        rw [hbranch] at hleave
        rcases hnext : path.junctionAt i.succ with nextJunction | nextBranch
        · rw [hnext] at hleave
          apply congrArg Sum.inl
          simpa [Edge] using hleave
        · rw [hnext] at hleave
          simp [Edge] at hleave

/-- Every branch field in an explicit path is the selected middle vertex in its own diamond. -/
public theorem STPath.branchAt_eq_branch_degreeTag {k : ℕ} (path : STPath k)
    (i : Fin k) :
    path.branchAt i = branch i (degreeTag (path.branchAt i)) := by
  have henter := path.enter i
  rw [path.junctionAt_eq i.castSucc] at henter
  rcases hbranch : path.branchAt i with branchJunction | ⟨j, bit⟩
  · rw [hbranch] at henter
    simp [Edge, junction] at henter
  · rw [hbranch] at henter
    have hindex : i = j := by
      simpa [Edge, junction] using henter
    subst j
    simp [branch, degreeTag]

/-- Recover the branch bit chosen by an explicit path at every diamond. -/
@[expose]
public def bitsOfPath {k : ℕ} (path : STPath k) : Fin k → Bool :=
  fun i => degreeTag (path.branchAt i)

/-- Two explicit paths are equal once their data fields agree; the remaining fields are
propositions and hence proof-irrelevant. -/
public theorem STPath.ext_fields {k : ℕ} {left right : STPath k}
    (hjunction : left.junctionAt = right.junctionAt)
    (hbranch : left.branchAt = right.branchAt) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Encoding the bits recovered from a path gives the original path. -/
public theorem pathOfBits_bitsOfPath {k : ℕ} (path : STPath k) :
    pathOfBits (bitsOfPath path) = path := by
  apply STPath.ext_fields
  · funext i
    exact (path.junctionAt_eq i).symm
  · funext i
    exact (path.branchAt_eq_branch_degreeTag i).symm

/-- Every explicit source-to-target path through the diamond chain is selected by one bit
vector. -/
public theorem pathOfBits_surjective (k : ℕ) :
    Function.Surjective (@pathOfBits k) := by
  intro path
  exact ⟨bitsOfPath path, pathOfBits_bitsOfPath path⟩

/-- Distinct bit vectors determine distinct source-to-target paths. -/
public theorem pathOfBits_injective (k : ℕ) :
    Function.Injective (@pathOfBits k) := by
  intro left right hpaths
  funext i
  have hbranch :=
    congrArg (fun path : STPath k => degreeTag (path.branchAt i)) hpaths
  simpa only [pathOfBits, branch, degreeTag] using hbranch

/-- Bit vectors and explicit source-to-target paths through the chain are in bijection. -/
public theorem pathOfBits_bijective (k : ℕ) :
    Function.Bijective (@pathOfBits k) :=
  ⟨pathOfBits_injective k, pathOfBits_surjective k⟩

/-- The canonical equivalence between length-`k` branch vectors and source-to-target paths. -/
@[expose]
public noncomputable def bitVectorsEquivPaths (k : ℕ) :
    (Fin k → Bool) ≃ STPath k :=
  Equiv.ofBijective pathOfBits (pathOfBits_bijective k)

/-- There are exactly `2 ^ k` bit vectors available to choose paths. -/
public theorem card_bitVectors (k : ℕ) :
    Fintype.card (Fin k → Bool) = Nat.pow 2 k := by
  simp

/-- There are exactly `2 ^ k` explicit source-to-target paths through a `k`-diamond chain. -/
public theorem card_stPaths (k : ℕ) :
    Nat.card (STPath k) = Nat.pow 2 k := by
  rw [Nat.card_congr (bitVectorsEquivPaths k).symm]
  simp

/-- The bit-vector-indexed family of distinct source-to-target paths. -/
public theorem exponentiallyManyDistinctPaths (k : ℕ) :
    ∃ paths : (Fin k → Bool) → STPath k, Function.Injective paths :=
  ⟨pathOfBits, pathOfBits_injective k⟩

/-- The complete diamond-chain obstruction in one statement: linearly many vertices,
acyclicity, degree at most two in both directions, exactly `2 ^ k` source-to-target paths, and
their explicit injective bit-vector enumeration. -/
public theorem diamondChain_obstruction (k : ℕ) :
    Fintype.card (Vertex k) = k + k + k + 1 ∧
      (∀ vertex : Vertex k, ¬ TransGen (Edge k) vertex vertex) ∧
      OutdegreeAtMostTwo (Edge k) ∧
      IndegreeAtMostTwo (Edge k) ∧
      Fintype.card (Fin k → Bool) = Nat.pow 2 k ∧
      Nat.card (STPath k) = Nat.pow 2 k ∧
      ∃ paths : (Fin k → Bool) → STPath k, Function.Injective paths :=
  ⟨card_vertex k, acyclic k, outdegreeAtMostTwo k, indegreeAtMostTwo k,
    card_bitVectors k, card_stPaths k, exponentiallyManyDistinctPaths k⟩

end DiamondPaths
