module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation
import Mathlib.Tactic

@[expose]
public section

/-!
# Natural ranks for finite acyclic relations

Every acyclic relation on a finite type admits a strict natural-valued rank.  A canonical
choice is the number of vertices that can reach the given vertex, including the vertex itself.
Along an edge the ancestor set grows strictly: every old ancestor remains an ancestor, while the
new target is not an ancestor of the old source because that would close a directed cycle.

The converse is immediate, so finite acyclicity is equivalent to the existence of a strict
natural rank.  This generic result is shared by the finite-reachability and machine-level
normal-form constructions.
-/

namespace FiniteAcyclicRank

open Classical Relation

variable {V : Type*} [Fintype V]

/-- Vertices that can reach `target`, including `target` itself. -/
public noncomputable def ancestors (edge : V → V → Prop) (target : V) : Finset V :=
  Finset.univ.filter fun source => ReflTransGen edge source target

/-- The ancestor-count rank of a vertex. -/
public noncomputable def rank (edge : V → V → Prop) (target : V) : ℕ :=
  (ancestors edge target).card

/-- Ancestor rank never exceeds the size of the finite vertex space. -/
public theorem rank_le_card (edge : V → V → Prop) (target : V) :
    rank edge target ≤ Fintype.card V := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

@[simp]
public theorem mem_ancestors_iff {edge : V → V → Prop} {source target : V} :
    source ∈ ancestors edge target ↔ ReflTransGen edge source target := by
  simp [ancestors]

omit [Fintype V] in
/-- In an acyclic relation, an edge cannot be followed by a path back to its source. -/
public theorem not_reaches_back_of_edge
    {edge : V → V → Prop}
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex)
    {source target : V} (hstep : edge source target) :
    ¬ ReflTransGen edge target source := by
  intro hback
  rcases reflTransGen_iff_eq_or_transGen.mp hback with heq | hpath
  · subst target
    exact hacyclic source (TransGen.single hstep)
  · exact hacyclic target (hpath.tail hstep)

/-- Ancestor count strictly increases along every edge of a finite acyclic relation. -/
public theorem rank_lt_of_edge
    {edge : V → V → Prop}
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex)
    {source target : V} (hstep : edge source target) :
    rank edge source < rank edge target := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro vertex hvertex
    rw [mem_ancestors_iff] at hvertex ⊢
    exact hvertex.tail hstep
  · intro heq
    have htarget : target ∈ ancestors edge target := by
      exact mem_ancestors_iff.mpr .refl
    have hnot : target ∉ ancestors edge source := by
      rw [mem_ancestors_iff]
      exact not_reaches_back_of_edge hacyclic hstep
    exact hnot (by simpa [heq] using htarget)

/-- Every finite acyclic relation has a strict natural-valued rank. -/
public theorem exists_strictRank
    {edge : V → V → Prop}
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex) :
    ∃ rank : V → ℕ,
      ∀ ⦃source target⦄, edge source target → rank source < rank target := by
  exact ⟨rank edge, fun {_ _} hstep => rank_lt_of_edge hacyclic hstep⟩

/-- Every vertex of a finite acyclic relation reaches a sink. -/
public theorem exists_reachable_sink
    {edge : V → V → Prop}
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex)
    (source : V) :
    ∃ target, ReflTransGen edge source target ∧ ∀ next, ¬ edge target next := by
  let measure : V → ℕ := fun vertex => Fintype.card V - rank edge vertex
  suffices h : ∀ fuel vertex, measure vertex = fuel →
      ∃ target, ReflTransGen edge vertex target ∧ ∀ next, ¬ edge target next by
    exact h (measure source) source rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro vertex hmeasure
      by_cases hout : ∃ next, edge vertex next
      · obtain ⟨next, hstep⟩ := hout
        have hrank : rank edge vertex < rank edge next :=
          rank_lt_of_edge hacyclic hstep
        have hnextMeasure : measure next < fuel := by
          rw [← hmeasure]
          dsimp only [measure]
          have hbound := rank_le_card edge next
          omega
        obtain ⟨target, hreach, hsink⟩ :=
          ih (measure next) hnextMeasure next rfl
        exact ⟨target, ReflTransGen.head hstep hreach, hsink⟩
      · exact ⟨vertex, .refl, fun next hstep => hout ⟨next, hstep⟩⟩

omit [Fintype V] in
/-- A strict natural-valued rank rules out every nonempty directed cycle. -/
public theorem acyclic_of_strictRank
    {edge : V → V → Prop} {rank : V → ℕ}
    (hstrict : ∀ ⦃source target⦄, edge source target → rank source < rank target) :
    ∀ vertex, ¬ TransGen edge vertex vertex := by
  have hpath : ∀ {source target}, TransGen edge source target →
      rank source < rank target := by
    intro source target path
    induction path with
    | single hstep => exact hstrict hstep
    | tail _ hstep ih => exact ih.trans (hstrict hstep)
  intro vertex hcycle
  exact (Nat.lt_irrefl _) (hpath hcycle)

/-- On a finite type, acyclicity is equivalent to admitting a strict natural-valued rank. -/
public theorem acyclic_iff_exists_strictRank {edge : V → V → Prop} :
    (∀ vertex, ¬ TransGen edge vertex vertex) ↔
      ∃ rank : V → ℕ,
        ∀ ⦃source target⦄, edge source target → rank source < rank target := by
  constructor
  · exact exists_strictRank
  · rintro ⟨rank, hstrict⟩
    exact acyclic_of_strictRank hstrict

end FiniteAcyclicRank

end
