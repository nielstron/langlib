module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

@[expose]
public section

/-!
# Edge-path decompositions of finite directed acyclic graphs

This file packages the elementary local-pairing construction used in edge-path decompositions
of a finite DAG.  At every vertex, enumerate the incoming and outgoing edges and link the edges
with the same index for as long as both enumerations continue.

The resulting relation on edges is functional and cofunctional.  This file proves adjacency,
cofunctionality, inherited acyclicity, and the exact number of chain starts.  It deliberately
does not define a separate type of finite path covers or state a minimization theorem about all
such covers.
-/

open Finset Relation

namespace FiniteDAGPathDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge of a directed relation, retaining both endpoints. -/
public abbrev Edge (edge : V → V → Prop) :=
  { endpoints : V × V // edge endpoints.1 endpoints.2 }

public abbrev Incoming (edge : V → V → Prop) (v : V) :=
  { e : Edge edge // e.1.2 = v }

public abbrev Outgoing (edge : V → V → Prop) (v : V) :=
  { e : Edge edge // e.1.1 = v }

variable (edge : V → V → Prop) [DecidableRel edge]

public def indegree (v : V) : ℕ := Fintype.card (Incoming edge v)

public def outdegree (v : V) : ℕ := Fintype.card (Outgoing edge v)

public noncomputable def incomingIndex (v : V) :
    Incoming edge v ≃ Fin (indegree (edge := edge) v) :=
  Fintype.equivFin _

public noncomputable def outgoingIndex (v : V) :
    Outgoing edge v ≃ Fin (outdegree (edge := edge) v) :=
  Fintype.equivFin _

/-- Pair the `i`th incoming edge at a vertex with its `i`th outgoing edge, whenever both
exist. -/
public noncomputable def localNext (v : V) (e : Incoming edge v) :
    Option (Outgoing edge v) :=
  let i := incomingIndex edge v e
  if h : i.val < outdegree (edge := edge) v then
    some ((outgoingIndex edge v).symm ⟨i.val, h⟩)
  else
    none

/-- Every edge is canonically an incoming edge at its target. -/
public def asIncoming (e : Edge edge) : Incoming edge e.1.2 :=
  ⟨e, rfl⟩

/-- Forget the vertex index from an outgoing edge. -/
public def fromOutgoing {v : V} (e : Outgoing edge v) : Edge edge := e.1

/-- The local pairings, assembled into a partial successor function on all edges. -/
public noncomputable def next (e : Edge edge) : Option (Edge edge) :=
  (localNext edge e.1.2 (asIncoming edge e)).map (fromOutgoing edge)

public theorem next_eq_some_implies_adjacent {e f : Edge edge}
    (h : next edge e = some f) :
    e.1.2 = f.1.1 := by
  classical
  unfold next at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨f', hlocal, rfl⟩ := h
  exact f'.2.symm

private theorem localNext_rightUnique (v : V) {e₁ e₂ : Incoming edge v}
    {f : Outgoing edge v}
    (h₁ : localNext edge v e₁ = some f)
    (h₂ : localNext edge v e₂ = some f) :
    e₁ = e₂ := by
  classical
  unfold localNext at h₁ h₂
  dsimp only at h₁ h₂
  by_cases hi₁ : (incomingIndex edge v e₁).val < outdegree (edge := edge) v
  · simp only [dif_pos hi₁, Option.some.injEq] at h₁
    by_cases hi₂ : (incomingIndex edge v e₂).val < outdegree (edge := edge) v
    · simp only [dif_pos hi₂, Option.some.injEq] at h₂
      have hout :
          (outgoingIndex edge v).symm ⟨(incomingIndex edge v e₁).val, hi₁⟩ =
            (outgoingIndex edge v).symm ⟨(incomingIndex edge v e₂).val, hi₂⟩ := by
        exact h₁.trans h₂.symm
      have hfin : incomingIndex edge v e₁ = incomingIndex edge v e₂ := by
        have hind := congrArg (outgoingIndex edge v) hout
        have hind' :
            (⟨(incomingIndex edge v e₁).val, hi₁⟩ :
                Fin (outdegree (edge := edge) v)) =
              (⟨(incomingIndex edge v e₂).val, hi₂⟩ :
                Fin (outdegree (edge := edge) v)) := by
          simpa using hind
        have hval :
            (incomingIndex edge v e₁).val = (incomingIndex edge v e₂).val :=
          congrArg (fun z : Fin (outdegree (edge := edge) v) => z.val) hind'
        exact Fin.ext hval
      exact (incomingIndex edge v).injective hfin
    · rw [dif_neg hi₂] at h₂
      simp at h₂
  · rw [dif_neg hi₁] at h₁
    simp at h₁

public theorem next_rightUnique {e₁ e₂ f : Edge edge}
    (h₁ : next edge e₁ = some f)
    (h₂ : next edge e₂ = some f) :
    e₁ = e₂ := by
  classical
  have hv₁ := next_eq_some_implies_adjacent edge h₁
  have hv₂ := next_eq_some_implies_adjacent edge h₂
  have hv : e₁.1.2 = e₂.1.2 := hv₁.trans hv₂.symm
  -- Put both incoming edges in the same dependent fiber and use local injectivity.
  rcases e₁ with ⟨⟨s₁, t₁⟩, he₁⟩
  rcases e₂ with ⟨⟨s₂, t₂⟩, he₂⟩
  change t₁ = t₂ at hv
  subst t₂
  unfold next at h₁ h₂
  simp only [Option.map_eq_some_iff] at h₁ h₂
  obtain ⟨f₁, hf₁, hforget₁⟩ := h₁
  obtain ⟨f₂, hf₂, hforget₂⟩ := h₂
  have hff : f₁ = f₂ := by
    apply Subtype.ext
    exact hforget₁.trans hforget₂.symm
  subst f₂
  have hin :
      asIncoming edge ⟨(s₁, t₁), he₁⟩ =
        asIncoming edge ⟨(s₂, t₁), he₂⟩ :=
    localNext_rightUnique edge _ hf₁ hf₂
  exact congrArg Subtype.val hin

/-- Every edge can equivalently be indexed as an incoming edge at its target. -/
public def incomingBundleEquiv :
    (Σ v, Incoming edge v) ≃ Edge edge where
  toFun e := e.2.1
  invFun e := ⟨e.1.2, asIncoming edge e⟩
  left_inv e := by
    rcases e with ⟨v, ⟨e, he⟩⟩
    subst v
    rfl
  right_inv _ := rfl

/-- Every edge can equivalently be indexed as an outgoing edge at its source. -/
public def outgoingBundleEquiv :
    (Σ v, Outgoing edge v) ≃ Edge edge where
  toFun e := e.2.1
  invFun e := ⟨e.1.1, ⟨e, rfl⟩⟩
  left_inv e := by
    rcases e with ⟨v, ⟨e, he⟩⟩
    subst v
    rfl
  right_inv _ := rfl

public theorem sum_indegree_eq_card_edges :
    ∑ v, indegree (edge := edge) v = Fintype.card (Edge edge) := by
  change (∑ v, Fintype.card (Incoming edge v)) = Fintype.card (Edge edge)
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (incomingBundleEquiv edge)

public theorem sum_outdegree_eq_card_edges :
    ∑ v, outdegree (edge := edge) v = Fintype.card (Edge edge) := by
  change (∑ v, Fintype.card (Outgoing edge v)) = Fintype.card (Edge edge)
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (outgoingBundleEquiv edge)

private theorem card_fin_filter_lt (n m : ℕ) :
    (Finset.univ.filter (fun i : Fin n => i.val < m)).card = min n m := by
  by_cases h : m < n
  · have hm :
        (Finset.univ.filter (fun i : Fin n => i.val < m)) =
          Finset.Iio (⟨m, h⟩ : Fin n) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      rfl
    rw [hm, Fin.card_Iio]
    change m = min n m
    exact (Nat.min_eq_right (Nat.le_of_lt h)).symm
  · have hnm : n ≤ m := Nat.le_of_not_gt h
    have hm :
        (Finset.univ.filter (fun i : Fin n => i.val < m)) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [i.isLt.trans_le hnm]
    rw [hm, Finset.card_univ]
    simpa using (Nat.min_eq_left hnm).symm

/-- Incoming edges at `v` that are linked to a successor by the local construction. -/
public noncomputable def locallyLinked (v : V) : Finset (Incoming edge v) :=
  Finset.univ.filter fun e => (localNext edge v e).isSome

private theorem localNext_isSome_iff (v : V) (e : Incoming edge v) :
    (localNext edge v e).isSome ↔
      (incomingIndex edge v e).val < outdegree (edge := edge) v := by
  classical
  unfold localNext
  dsimp only
  by_cases h : (incomingIndex edge v e).val < outdegree (edge := edge) v
  · simp [h]
  · simp [h]

/-- Exactly `min(indegree, outdegree)` incoming edges are continued at each vertex. -/
public theorem card_locallyLinked (v : V) :
    (locallyLinked edge v).card =
      min (indegree (edge := edge) v) (outdegree (edge := edge) v) := by
  classical
  calc
    (locallyLinked edge v).card =
        (Finset.univ.filter (fun i : Fin (indegree (edge := edge) v) =>
          i.val < outdegree (edge := edge) v)).card := by
      apply Finset.card_equiv (incomingIndex edge v)
      intro e
      simp only [locallyLinked, Finset.mem_filter, Finset.mem_univ, true_and]
      exact localNext_isSome_iff edge v e
    _ = min (indegree (edge := edge) v) (outdegree (edge := edge) v) :=
      card_fin_filter_lt _ _

/-- Edges that the canonical pairing continues with a successor. -/
public noncomputable def linkedSources : Finset (Edge edge) :=
  Finset.univ.filter fun e => (next edge e).isSome

private theorem next_isSome_iff_localNext_isSome (e : Edge edge) :
    (next edge e).isSome ↔
      (localNext edge e.1.2 (asIncoming edge e)).isSome := by
  classical
  simp [next]

/-- The canonical pairing uses exactly the sum of the local minimum degrees. -/
public theorem card_linkedSources :
    (linkedSources edge).card =
      ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) := by
  classical
  calc
    (linkedSources edge).card =
        (Finset.univ.sigma (locallyLinked edge)).card := by
      apply Finset.card_equiv (incomingBundleEquiv edge).symm
      intro e
      simp only [linkedSources, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sigma]
      rw [next_isSome_iff_localNext_isSome]
      simp [locallyLinked, incomingBundleEquiv]
    _ = ∑ v, (locallyLinked edge v).card := by
      rw [Finset.card_sigma]
    _ = ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) := by
      apply Finset.sum_congr rfl
      intro v _
      exact card_locallyLinked edge v

/-- The successor selected for an edge known to be linked. -/
public noncomputable def linkedTarget
    (e : {e : Edge edge // e ∈ linkedSources edge}) : Edge edge :=
  (next edge e.1).get (by
    simpa only [linkedSources, Finset.mem_filter, Finset.mem_univ, true_and] using e.2)

public theorem next_linkedTarget
    (e : {e : Edge edge // e ∈ linkedSources edge}) :
    next edge e.1 = some (linkedTarget edge e) := by
  classical
  exact (Option.some_get (by
    simpa only [linkedSources, Finset.mem_filter, Finset.mem_univ, true_and] using e.2)).symm

private theorem linkedTarget_injective :
    Function.Injective (linkedTarget edge) := by
  classical
  intro e₁ e₂ htarget
  apply Subtype.ext
  apply next_rightUnique edge
  · exact (next_linkedTarget edge e₁).trans (congrArg some htarget)
  · exact next_linkedTarget edge e₂

/-- Edges that have a predecessor in the canonical pairing. -/
public noncomputable def continuedTargets : Finset (Edge edge) :=
  (linkedSources edge).attach.image (linkedTarget edge)

/-- Initial edges of the chains induced by the canonical pairing. -/
public noncomputable def startEdges : Finset (Edge edge) :=
  (continuedTargets edge)ᶜ

public theorem mem_continuedTargets_iff (f : Edge edge) :
    f ∈ continuedTargets edge ↔ ∃ e, next edge e = some f := by
  classical
  constructor
  · intro hf
    rw [continuedTargets, Finset.mem_image] at hf
    obtain ⟨e, _, rfl⟩ := hf
    exact ⟨e.1, next_linkedTarget edge e⟩
  · rintro ⟨e, he⟩
    have helinked : e ∈ linkedSources edge := by
      simp [linkedSources, he]
    rw [continuedTargets, Finset.mem_image]
    refine ⟨⟨e, helinked⟩, Finset.mem_attach _ _, ?_⟩
    have hnext := next_linkedTarget edge ⟨e, helinked⟩
    exact Option.some.inj (hnext.symm.trans he)

public theorem mem_startEdges_iff (f : Edge edge) :
    f ∈ startEdges edge ↔ ¬ ∃ e, next edge e = some f := by
  classical
  simp [startEdges, mem_continuedTargets_iff]

private theorem card_continuedTargets :
    (continuedTargets edge).card = (linkedSources edge).card := by
  classical
  rw [continuedTargets, Finset.card_image_of_injective _ (linkedTarget_injective edge),
    Finset.card_attach]

/-- The number of chain starts is the number of edges minus the number of local continuations. -/
public theorem card_startEdges_eq_card_edges_sub_sum_min :
    (startEdges edge).card =
      Fintype.card (Edge edge) -
        ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) := by
  classical
  rw [startEdges, Finset.card_compl, card_continuedTargets, card_linkedSources]

/-- A cycle of linked edges would project to a directed cycle in the original graph. -/
public theorem next_link_acyclic
    (hacyclic : ∀ v, ¬ Relation.TransGen edge v v) (e : Edge edge) :
    ¬ Relation.TransGen (fun e f => next edge e = some f) e e := by
  intro hcycle
  have hvertexCycle : Relation.TransGen edge e.1.1 e.1.1 :=
    hcycle.lift (fun e : Edge edge => e.1.1) (by
      intro source target hnext
      have hadj := next_eq_some_implies_adjacent edge hnext
      simpa [hadj] using source.2)
  exact hacyclic e.1.1 hvertexCycle

/-- The edge-minus-continuation expression is the sum of all positive outdegree imbalances. -/
public theorem card_edges_sub_sum_min_eq_sum_outdegree_sub_indegree :
    Fintype.card (Edge edge) -
        ∑ v, min (indegree (edge := edge) v) (outdegree (edge := edge) v) =
      ∑ v, (outdegree (edge := edge) v - indegree (edge := edge) v) := by
  rw [← sum_outdegree_eq_card_edges edge]
  rw [← Finset.sum_tsub_distrib Finset.univ (by
    intro v _
    exact min_le_right _ _)]
  change
    Finset.sum Finset.univ (fun v =>
      outdegree (edge := edge) v -
        min (indegree (edge := edge) v) (outdegree (edge := edge) v)) =
      Finset.sum Finset.univ (fun v =>
        outdegree (edge := edge) v - indegree (edge := edge) v)
  apply Finset.sum_congr rfl
  intro v _
  omega

/-- Closed form for the number of initial edges in the canonical pairing. -/
public theorem card_startEdges_eq_sum_outdegree_sub_indegree :
    (startEdges edge).card =
      ∑ v, (outdegree (edge := edge) v - indegree (edge := edge) v) := by
  rw [card_startEdges_eq_card_edges_sub_sum_min,
    card_edges_sub_sum_min_eq_sum_outdegree_sub_indegree]

end FiniteDAGPathDecomposition

end
