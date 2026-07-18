module

public import Langlib.Automata.LinearBounded.FiniteDAGPathDecomposition
import Mathlib.Tactic

@[expose]
public section

/-!
# Minimum edge-path partitions of finite DAGs

An edge-path partition is encoded by a partial successor on edge occurrences.  Successors must
join at a common vertex, no edge may have two predecessors, and the successor relation must be
acyclic.  Thus every edge occurrence belongs to exactly one of the finite directed chains induced
by the successor links; isolated edges are one-edge paths.

At a vertex, at most `min(indegree, outdegree)` incoming edges can be continued.  Summing this
local bound gives a lower bound on the number of paths in every partition.  For an acyclic input
relation, the canonical local pairing from `FiniteDAGPathDecomposition` attains the bound, so the
minimum number of paths has both of the expected closed forms.
-/

open Finset Relation

namespace FiniteDAGPathDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (edge : V → V → Prop) [DecidableRel edge]

/-- A partition of all edge occurrences into finite directed paths, represented by their
partial successor links.  Coverage is built into the representation: every `Edge edge` is an
occurrence in exactly one successor-chain component. -/
public structure EdgePathPartition where
  /-- The next edge occurrence on the same path, if any. -/
  next : Edge edge → Option (Edge edge)
  /-- Consecutive edge occurrences meet at their common endpoint. -/
  adjacent : ∀ {e f}, next e = some f → e.1.2 = f.1.1
  /-- An edge occurrence has at most one predecessor. -/
  rightUnique : ∀ {e₁ e₂ f}, next e₁ = some f → next e₂ = some f → e₁ = e₂
  /-- Successor links contain no cycle, so their components are paths rather than cycles. -/
  acyclic : ∀ e, ¬ Relation.TransGen (fun e f => next e = some f) e e

namespace EdgePathPartition

variable (P : EdgePathPartition edge)

/-- The directed successor-link relation encoded by a path partition. -/
public def Successor (e f : Edge edge) : Prop := P.next e = some f

/-- Zero or more successor links within one path component. -/
public def Reaches (e f : Edge edge) : Prop :=
  Relation.ReflTransGen (EdgePathPartition.Successor edge P) e f

/-- A predecessor-free edge occurrence, hence the first edge of its path component. -/
public def IsStart (e : Edge edge) : Prop :=
  ¬ ∃ predecessor, EdgePathPartition.Successor edge P predecessor e

/-- Edge occurrences that are continued by a successor link. -/
public noncomputable def linkedSources : Finset (Edge edge) :=
  Finset.univ.filter fun e => (P.next e).isSome

/-- The successor of an edge occurrence known to be linked. -/
public noncomputable def linkedTarget
    (e : {e : Edge edge // e ∈ P.linkedSources}) : Edge edge :=
  (P.next e.1).get (by
    simpa only [linkedSources, Finset.mem_filter, Finset.mem_univ, true_and] using e.2)

omit [DecidableEq V] in
public theorem next_linkedTarget
    (e : {e : Edge edge // e ∈ P.linkedSources}) :
    P.next e.1 = some (EdgePathPartition.linkedTarget edge P e) := by
  classical
  exact (Option.some_get (by
    simpa only [linkedSources, Finset.mem_filter, Finset.mem_univ, true_and] using e.2)).symm

omit [DecidableEq V] in
private theorem linkedTarget_injective :
    Function.Injective (EdgePathPartition.linkedTarget edge P) := by
  classical
  intro e₁ e₂ htarget
  apply Subtype.ext
  apply P.rightUnique
  · exact (EdgePathPartition.next_linkedTarget edge P e₁).trans
      (congrArg some htarget)
  · exact EdgePathPartition.next_linkedTarget edge P e₂

/-- Edge occurrences that have a predecessor in the partition. -/
public noncomputable def continuedTargets : Finset (Edge edge) :=
  P.linkedSources.attach.image (EdgePathPartition.linkedTarget edge P)

/-- Initial edge occurrences, one for each path in the partition. -/
public noncomputable def startEdges : Finset (Edge edge) :=
  P.continuedTargetsᶜ

/-- The number of paths, counted by their unique initial edge occurrences. -/
public noncomputable def pathCount : ℕ := P.startEdges.card

public theorem mem_continuedTargets_iff (f : Edge edge) :
    f ∈ P.continuedTargets ↔ ∃ e, P.next e = some f := by
  classical
  constructor
  · intro hf
    rw [continuedTargets, Finset.mem_image] at hf
    obtain ⟨e, _, rfl⟩ := hf
    exact ⟨e.1, EdgePathPartition.next_linkedTarget edge P e⟩
  · rintro ⟨e, he⟩
    have helinked : e ∈ P.linkedSources := by
      simp [linkedSources, he]
    rw [continuedTargets, Finset.mem_image]
    refine ⟨⟨e, helinked⟩, Finset.mem_attach _ _, ?_⟩
    exact Option.some.inj
      ((EdgePathPartition.next_linkedTarget edge P ⟨e, helinked⟩).symm.trans he)

public theorem mem_startEdges_iff (f : Edge edge) :
    f ∈ P.startEdges ↔ ¬ ∃ e, P.next e = some f := by
  classical
  simp [startEdges, EdgePathPartition.mem_continuedTargets_iff edge P]

/-- The semantic predecessor-free predicate agrees exactly with the finite set used to count
path starts. -/
public theorem mem_startEdges_iff_isStart (f : Edge edge) :
    f ∈ P.startEdges ↔ EdgePathPartition.IsStart edge P f := by
  simpa [IsStart, Successor] using EdgePathPartition.mem_startEdges_iff edge P f

omit [DecidableEq V] [DecidableRel edge] in
private theorem successorTransGen_wellFounded :
    WellFounded
      (Relation.TransGen (EdgePathPartition.Successor edge P)) := by
  letI : Std.Irrefl
      (Relation.TransGen (EdgePathPartition.Successor edge P)) :=
    ⟨by
      intro e
      exact P.acyclic e⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

omit [DecidableEq V] [DecidableRel edge] in
/-- Every edge occurrence has a predecessor-free ancestor connected to it by successor links. -/
public theorem exists_start_reaches (e : Edge edge) :
    ∃ start, EdgePathPartition.IsStart edge P start ∧
      EdgePathPartition.Reaches edge P start e := by
  classical
  refine (EdgePathPartition.successorTransGen_wellFounded edge P).induction
    (C := fun current =>
      ∃ start, EdgePathPartition.IsStart edge P start ∧
        EdgePathPartition.Reaches edge P start current)
    e ?_
  intro current ih
  by_cases hstart : EdgePathPartition.IsStart edge P current
  · exact ⟨current, hstart, Relation.ReflTransGen.refl⟩
  · have hpredecessor : ∃ predecessor,
        EdgePathPartition.Successor edge P predecessor current := by
      exact Classical.not_not.mp hstart
    obtain ⟨predecessor, hlink⟩ := hpredecessor
    obtain ⟨start, hstart, hreach⟩ :=
      ih predecessor (Relation.TransGen.single hlink)
    exact ⟨start, hstart, hreach.tail hlink⟩

omit [Fintype V] [DecidableEq V] [DecidableRel edge] in
private theorem successor_swap_rightUnique :
    Relator.RightUnique
      (Function.swap (EdgePathPartition.Successor edge P)) := by
  intro target left right hleft hright
  exact P.rightUnique hleft hright

private theorem reflTransGen_terminal_unique_of_rightUnique
    {A : Type*} {relation : A → A → Prop}
    (hunique : Relator.RightUnique relation)
    {source left right : A}
    (hleft : Relation.ReflTransGen relation source left)
    (hright : Relation.ReflTransGen relation source right)
    (hleftTerminal : ∀ after, ¬ relation left after)
    (hrightTerminal : ∀ after, ¬ relation right after) :
    left = right := by
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun source hpath =>
      ∀ {right}, Relation.ReflTransGen relation source right →
        (∀ after, ¬ relation left after) →
        (∀ after, ¬ relation right after) → left = right)
    hleft ?_ ?_ hright hleftTerminal hrightTerminal
  · intro right hright hleftTerminal _
    rcases hright.cases_head with heq | ⟨middle, hfirst, _⟩
    · exact heq
    · exact (hleftTerminal middle hfirst).elim
  · intro source middle hfirst hrest ih right hright
      hleftTerminal hrightTerminal
    have htail : Relation.ReflTransGen relation middle right := by
      rcases hright.cases_head with heq | ⟨candidate, hcandidate, htail⟩
      · subst right
        exact (hrightTerminal middle hfirst).elim
      · have hmiddle : middle = candidate := hunique hfirst hcandidate
        simpa [hmiddle] using htail
    exact ih htail hleftTerminal hrightTerminal

omit [Fintype V] [DecidableEq V] [DecidableRel edge] in
/-- Two predecessor-free edges whose successor chains reach the same occurrence are equal. -/
public theorem start_unique_of_reaches {left right target : Edge edge}
    (hleftStart : EdgePathPartition.IsStart edge P left)
    (hrightStart : EdgePathPartition.IsStart edge P right)
    (hleft : EdgePathPartition.Reaches edge P left target)
    (hright : EdgePathPartition.Reaches edge P right target) :
    left = right := by
  apply reflTransGen_terminal_unique_of_rightUnique
    (EdgePathPartition.successor_swap_rightUnique edge P)
    hleft.swap hright.swap
  · intro predecessor hlink
    exact hleftStart ⟨predecessor, hlink⟩
  · intro predecessor hlink
    exact hrightStart ⟨predecessor, hlink⟩

omit [DecidableEq V] [DecidableRel edge] in
/-- Adequacy of the successor-link representation: every edge occurrence lies on a successor
chain from exactly one start edge. -/
public theorem existsUnique_start_reaches (e : Edge edge) :
    ∃! start, EdgePathPartition.IsStart edge P start ∧
      EdgePathPartition.Reaches edge P start e := by
  obtain ⟨start, hstart, hreach⟩ :=
    EdgePathPartition.exists_start_reaches edge P e
  refine ⟨start, ⟨hstart, hreach⟩, ?_⟩
  intro candidate hcandidate
  exact EdgePathPartition.start_unique_of_reaches edge P
    hcandidate.1 hstart hcandidate.2 hreach

private theorem card_continuedTargets :
    P.continuedTargets.card = P.linkedSources.card := by
  classical
  rw [continuedTargets,
    Finset.card_image_of_injective _
      (EdgePathPartition.linkedTarget_injective edge P),
    Finset.card_attach]

/-- For every edge-path partition, paths equal edge occurrences minus successor links. -/
public theorem pathCount_eq_card_edges_sub_card_linkedSources :
    P.pathCount = Fintype.card (Edge edge) - P.linkedSources.card := by
  classical
  rw [pathCount, startEdges, Finset.card_compl,
    EdgePathPartition.card_continuedTargets edge P]

/-- Incoming edge occurrences at `v` that this partition continues. -/
public noncomputable def locallyLinked (v : V) : Finset (Incoming edge v) :=
  Finset.univ.filter fun e => (P.next e.1).isSome

/-- The global continuation count is the sum of its target-vertex fibers. -/
public theorem card_linkedSources_eq_sum_card_locallyLinked :
    P.linkedSources.card =
      ∑ v, (EdgePathPartition.locallyLinked edge P v).card := by
  classical
  calc
    P.linkedSources.card =
        (Finset.univ.sigma (EdgePathPartition.locallyLinked edge P)).card := by
      apply Finset.card_equiv (incomingBundleEquiv edge).symm
      intro e
      simp only [linkedSources, locallyLinked, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_sigma]
      rfl
    _ = ∑ v, (EdgePathPartition.locallyLinked edge P v).card := by
      rw [Finset.card_sigma]

/-- The outgoing edge reached by a locally linked incoming edge occurrence. -/
public noncomputable def locallyLinkedTarget {v : V}
    (e : {e : Incoming edge v //
      e ∈ EdgePathPartition.locallyLinked edge P v}) : Outgoing edge v :=
  let f := (P.next e.1.1).get (by
    simpa only [locallyLinked, Finset.mem_filter, Finset.mem_univ, true_and] using e.2)
  ⟨f, by
    have hnext : P.next e.1.1 = some f :=
      (Option.some_get (by
        simpa only [locallyLinked, Finset.mem_filter, Finset.mem_univ, true_and]
          using e.2)).symm
    exact (P.adjacent hnext).symm.trans e.1.2⟩

public theorem next_locallyLinkedTarget {v : V}
    (e : {e : Incoming edge v //
      e ∈ EdgePathPartition.locallyLinked edge P v}) :
    P.next e.1.1 =
      some (EdgePathPartition.locallyLinkedTarget edge P e).1 := by
  classical
  exact (Option.some_get (by
    simpa only [locallyLinked, Finset.mem_filter, Finset.mem_univ, true_and] using e.2)).symm

private theorem locallyLinkedTarget_injective {v : V} :
    Function.Injective
      (EdgePathPartition.locallyLinkedTarget edge P (v := v)) := by
  classical
  intro e₁ e₂ htarget
  apply Subtype.ext
  apply Subtype.ext
  apply P.rightUnique
  · exact (EdgePathPartition.next_locallyLinkedTarget edge P e₁).trans
      (congrArg (fun f : Outgoing edge v => some f.1) htarget)
  · exact EdgePathPartition.next_locallyLinkedTarget edge P e₂

private theorem card_locallyLinked_le_indegree (v : V) :
    (EdgePathPartition.locallyLinked edge P v).card ≤
      indegree (edge := edge) v := by
  calc
    (EdgePathPartition.locallyLinked edge P v).card ≤
        (Finset.univ : Finset (Incoming edge v)).card :=
      Finset.card_le_card (by simp)
    _ = indegree (edge := edge) v := by simp [indegree]

private theorem card_locallyLinked_le_outdegree (v : V) :
    (EdgePathPartition.locallyLinked edge P v).card ≤
      outdegree (edge := edge) v := by
  classical
  simpa only [outdegree, Fintype.card_coe] using
    (Fintype.card_le_of_injective
      (EdgePathPartition.locallyLinkedTarget edge P)
      (EdgePathPartition.locallyLinkedTarget_injective edge P))

/-- At a vertex, a path partition can continue at most the smaller of the two edge fibers. -/
public theorem card_locallyLinked_le_min (v : V) :
    (EdgePathPartition.locallyLinked edge P v).card ≤
      min (indegree (edge := edge) v) (outdegree (edge := edge) v) :=
  Nat.le_min.mpr ⟨EdgePathPartition.card_locallyLinked_le_indegree edge P v,
    EdgePathPartition.card_locallyLinked_le_outdegree edge P v⟩

/-- Every edge-path partition uses at most the sum of the local minimum degrees as successor
links. -/
public theorem card_linkedSources_le_sum_min :
    P.linkedSources.card ≤
      ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) := by
  rw [EdgePathPartition.card_linkedSources_eq_sum_card_locallyLinked edge P]
  apply Finset.sum_le_sum
  intro v _
  exact EdgePathPartition.card_locallyLinked_le_min edge P v

/-- General lower bound on the number of paths in an edge-path partition. -/
public theorem card_edges_sub_sum_min_le_pathCount :
    Fintype.card (Edge edge) -
        ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) ≤
      P.pathCount := by
  calc
    Fintype.card (Edge edge) -
          ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) ≤
        Fintype.card (Edge edge) - P.linkedSources.card :=
      Nat.sub_le_sub_left
        (EdgePathPartition.card_linkedSources_le_sum_min edge P) _
    _ = P.pathCount :=
      (EdgePathPartition.pathCount_eq_card_edges_sub_card_linkedSources edge P).symm

/-- The same lower bound in positive outdegree-imbalance form. -/
public theorem sum_outdegree_sub_indegree_le_pathCount :
    ∑ v, (outdegree (edge := edge) v - indegree (edge := edge) v) ≤
      P.pathCount := by
  rw [← card_edges_sub_sum_min_eq_sum_outdegree_sub_indegree edge]
  exact EdgePathPartition.card_edges_sub_sum_min_le_pathCount edge P

end EdgePathPartition

/-- The canonical local pairing is an edge-path partition whenever the vertex relation is
acyclic. -/
public noncomputable def canonicalPathPartition
    (hacyclic : ∀ v, ¬ Relation.TransGen edge v v) : EdgePathPartition edge where
  next := FiniteDAGPathDecomposition.next edge
  adjacent := next_eq_some_implies_adjacent edge
  rightUnique := next_rightUnique edge
  acyclic := next_link_acyclic edge hacyclic

/-- The canonical pairing attains the edge-minus-local-continuations bound. -/
public theorem canonicalPathPartition_pathCount_eq_card_edges_sub_sum_min
    (hacyclic : ∀ v, ¬ Relation.TransGen edge v v) :
    (canonicalPathPartition edge hacyclic).pathCount =
      Fintype.card (Edge edge) -
        ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) := by
  rw [EdgePathPartition.pathCount_eq_card_edges_sub_card_linkedSources]
  congr 1
  simpa [EdgePathPartition.linkedSources, canonicalPathPartition,
    FiniteDAGPathDecomposition.linkedSources] using card_linkedSources edge

/-- A numerical path count is realized by some edge-path partition. -/
public def RealizesPathCount (n : ℕ) : Prop :=
  ∃ P : EdgePathPartition edge, P.pathCount = n

public theorem exists_realized_pathCount : ∃ n, RealizesPathCount edge n := by
  classical
  let P : EdgePathPartition edge := {
    next := fun _ => none
    adjacent := by simp
    rightUnique := by simp
    acyclic := by
      intro e hcycle
      have noTrans : ∀ {a b : Edge edge},
          Relation.TransGen (fun _ _ : Edge edge => False) a b → False := by
        intro a b h
        induction h with
        | single h => exact h
        | tail _ h _ => exact h
      apply noTrans
      exact hcycle.lift id (by simp)
  }
  exact ⟨P.pathCount, P, rfl⟩

/-- The least number of paths among all edge-path partitions. -/
public noncomputable def minimumPathCount : ℕ := by
  classical
  exact Nat.find (exists_realized_pathCount edge)

public theorem minimumPathCount_realized :
    RealizesPathCount edge (minimumPathCount edge) := by
  classical
  unfold minimumPathCount
  exact Nat.find_spec (exists_realized_pathCount edge)

public theorem minimumPathCount_le (P : EdgePathPartition edge) :
    minimumPathCount edge ≤ P.pathCount := by
  classical
  unfold minimumPathCount
  exact Nat.find_min' (exists_realized_pathCount edge) ⟨P, rfl⟩

/-- For a finite DAG, the exact minimum is edges minus the sum of local minimum degrees. -/
public theorem minimumPathCount_eq_card_edges_sub_sum_min
    (hacyclic : ∀ v, ¬ Relation.TransGen edge v v) :
    minimumPathCount edge =
      Fintype.card (Edge edge) -
        ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) := by
  apply Nat.le_antisymm
  · calc
      minimumPathCount edge ≤ (canonicalPathPartition edge hacyclic).pathCount :=
        minimumPathCount_le edge _
      _ = Fintype.card (Edge edge) -
          ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) :=
        canonicalPathPartition_pathCount_eq_card_edges_sub_sum_min edge hacyclic
  · obtain ⟨P, hP⟩ := minimumPathCount_realized edge
    rw [← hP]
    exact P.card_edges_sub_sum_min_le_pathCount

/-- Equivalent closed form: the exact minimum is the sum of positive outdegree imbalances. -/
public theorem minimumPathCount_eq_sum_outdegree_sub_indegree
    (hacyclic : ∀ v, ¬ Relation.TransGen edge v v) :
    minimumPathCount edge =
      ∑ v, (outdegree (edge := edge) v - indegree (edge := edge) v) := by
  rw [minimumPathCount_eq_card_edges_sub_sum_min edge hacyclic,
    card_edges_sub_sum_min_eq_sum_outdegree_sub_indegree edge]

/-- The existing canonical local pairing attains the abstract minimum path count. -/
public theorem canonicalPathPartition_pathCount_eq_minimumPathCount
    (hacyclic : ∀ v, ¬ Relation.TransGen edge v v) :
    (canonicalPathPartition edge hacyclic).pathCount = minimumPathCount edge := by
  rw [canonicalPathPartition_pathCount_eq_card_edges_sub_sum_min edge hacyclic,
    minimumPathCount_eq_card_edges_sub_sum_min edge hacyclic]

end FiniteDAGPathDecomposition

end
