module

public import Mathlib.Data.Set.Disjoint
public import Mathlib.Logic.Relation

@[expose]
public section

/-!
# Branch-set models of relation minors

This file records the elementary branch-set certificate used by graph-minor arguments without
depending on a simple-graph minor library.  A vertex of the small relation is represented by a
nonempty, connected, pairwise-disjoint set of vertices of the large relation, and every small
edge has an edge between the corresponding branch sets.

The large relation may be directed.  `BranchSetMinorModel` deliberately takes its symmetric
closure before asking for connectivity and represented edges, so it describes a minor of the
underlying undirected relation.
-/

namespace Relation

/-- Add the reverse of every edge to a relation. -/
@[expose]
public def SymmetricClosure {V : Type u} (edge : V → V → Prop) : V → V → Prop :=
  fun source target => edge source target ∨ edge target source

/-- Restrict both endpoints of a relation to a set. -/
@[expose]
public def Restricted {V : Type u} (vertices : Set V) (edge : V → V → Prop) :
    V → V → Prop :=
  fun source target => source ∈ vertices ∧ edge source target ∧ target ∈ vertices

/-- A branch-set certificate that `smallEdge` is a minor of the underlying undirected relation
of `largeEdge`.

No simplicity assumptions are imposed on either relation.  When both are adjacency relations of
simple graphs, these are exactly the usual branch-set data for a graph minor. -/
public structure BranchSetMinorModel {Small : Type u} {Large : Type v}
    (smallEdge : Small → Small → Prop) (largeEdge : Large → Large → Prop) where
  /-- The connected branch set representing each small vertex. -/
  branchSet : Small → Set Large
  /-- Every branch set has a representative. -/
  nonempty : ∀ vertex, (branchSet vertex).Nonempty
  /-- Distinct small vertices have disjoint branch sets. -/
  disjoint : ∀ {left right}, left ≠ right → Disjoint (branchSet left) (branchSet right)
  /-- Every two representatives of one branch set are connected inside that branch set. -/
  connected : ∀ vertex {source target}, source ∈ branchSet vertex →
    target ∈ branchSet vertex →
      ReflTransGen
        (Restricted (branchSet vertex) (SymmetricClosure largeEdge)) source target
  /-- Every small edge is represented by an edge between the corresponding branch sets. -/
  map_edge : ∀ {source target}, smallEdge source target →
    ∃ sourceRep ∈ branchSet source, ∃ targetRep ∈ branchSet target,
      SymmetricClosure largeEdge sourceRep targetRep

/-! ## Transport and composition -/

/-- Enlarging the large relation preserves every branch-set certificate. -/
public def BranchSetMinorModel.monoLarge {Small : Type u} {Large : Type v}
    {smallEdge : Small → Small → Prop} {largeEdge largerEdge : Large → Large → Prop}
    (model : BranchSetMinorModel smallEdge largeEdge)
    (hmono : ∀ {source target}, largeEdge source target → largerEdge source target) :
    BranchSetMinorModel smallEdge largerEdge where
  branchSet := model.branchSet
  nonempty := model.nonempty
  disjoint := model.disjoint
  connected vertex {source target} hsource htarget :=
    (model.connected vertex hsource htarget).mono fun _ _ hstep ↦
      ⟨hstep.1, hstep.2.1.elim
        (fun hedge ↦ Or.inl (hmono hedge))
        (fun hedge ↦ Or.inr (hmono hedge)), hstep.2.2⟩
  map_edge {source target} hedge := by
    rcases model.map_edge hedge with
      ⟨sourceRep, hsource, targetRep, htarget, hlarge⟩
    exact ⟨sourceRep, hsource, targetRep, htarget,
      hlarge.elim (fun h ↦ Or.inl (hmono h)) (fun h ↦ Or.inr (hmono h))⟩

/-- An injective edge-preserving map of the large vertices transports a branch-set
certificate.  Edge reflection is unnecessary: extra edges in the target do not invalidate a
minor model. -/
public def BranchSetMinorModel.mapLargeEmbedding
    {Small : Type u} {Large : Type v} {Larger : Type w}
    {smallEdge : Small → Small → Prop} {largeEdge : Large → Large → Prop}
    {largerEdge : Larger → Larger → Prop}
    (model : BranchSetMinorModel smallEdge largeEdge)
    (embed : Large → Larger) (hinjective : Function.Injective embed)
    (mapEdge : ∀ {source target}, largeEdge source target →
      largerEdge (embed source) (embed target)) :
    BranchSetMinorModel smallEdge largerEdge where
  branchSet vertex := embed '' model.branchSet vertex
  nonempty vertex := by
    rcases model.nonempty vertex with ⟨representative, hrepresentative⟩
    exact ⟨embed representative, representative, hrepresentative, rfl⟩
  disjoint {left right} hne := by
    rw [Set.disjoint_left]
    rintro _ ⟨leftRep, hleftRep, rfl⟩ ⟨rightRep, hrightRep, heq⟩
    have hreps : leftRep = rightRep := hinjective heq.symm
    subst rightRep
    exact (Set.disjoint_left.mp (model.disjoint hne)) hleftRep hrightRep
  connected vertex {source target} hsource htarget := by
    rcases hsource with ⟨sourceRep, hsourceRep, rfl⟩
    rcases htarget with ⟨targetRep, htargetRep, rfl⟩
    exact Relation.ReflTransGen.lift embed (fun _ _ hstep ↦
      ⟨⟨_, hstep.1, rfl⟩,
        hstep.2.1.elim (fun h ↦ Or.inl (mapEdge h)) (fun h ↦ Or.inr (mapEdge h)),
        ⟨_, hstep.2.2, rfl⟩⟩)
      (model.connected vertex hsourceRep htargetRep)
  map_edge {source target} hedge := by
    rcases model.map_edge hedge with
      ⟨sourceRep, hsourceRep, targetRep, htargetRep, hlarge⟩
    exact ⟨embed sourceRep, ⟨sourceRep, hsourceRep, rfl⟩,
      embed targetRep, ⟨targetRep, htargetRep, rfl⟩,
      hlarge.elim (fun h ↦ Or.inl (mapEdge h)) (fun h ↦ Or.inr (mapEdge h))⟩

/-- The union of the inner branch sets indexed by one outer branch set. -/
@[expose]
public def BranchSetMinorModel.composedBranchSet
    {Small : Type u} {Middle : Type v} {Large : Type w}
    {smallEdge : Small → Small → Prop} {middleEdge : Middle → Middle → Prop}
    {largeEdge : Large → Large → Prop}
    (outer : BranchSetMinorModel smallEdge middleEdge)
    (inner : BranchSetMinorModel (SymmetricClosure middleEdge) largeEdge)
    (vertex : Small) : Set Large :=
  {large | ∃ middle ∈ outer.branchSet vertex, large ∈ inner.branchSet middle}

/-- Branch-set certificates compose.  The inner certificate is stated for the symmetric
closure of the middle relation because both connectivity and represented outer edges forget
that relation's orientation. -/
public def BranchSetMinorModel.trans
    {Small : Type u} {Middle : Type v} {Large : Type w}
    {smallEdge : Small → Small → Prop} {middleEdge : Middle → Middle → Prop}
    {largeEdge : Large → Large → Prop}
    (outer : BranchSetMinorModel smallEdge middleEdge)
    (inner : BranchSetMinorModel (SymmetricClosure middleEdge) largeEdge) :
    BranchSetMinorModel smallEdge largeEdge where
  branchSet := outer.composedBranchSet inner
  nonempty vertex := by
    rcases outer.nonempty vertex with ⟨middle, hmiddle⟩
    rcases inner.nonempty middle with ⟨large, hlarge⟩
    exact ⟨large, middle, hmiddle, hlarge⟩
  disjoint {left right} hne := by
    rw [Set.disjoint_left]
    rintro large ⟨leftMiddle, hleftMiddle, hleftLarge⟩
      ⟨rightMiddle, hrightMiddle, hrightLarge⟩
    have hmiddle : leftMiddle = rightMiddle := by
      by_contra hmiddle
      exact (Set.disjoint_left.mp (inner.disjoint hmiddle))
        hleftLarge hrightLarge
    subst rightMiddle
    exact (Set.disjoint_left.mp (outer.disjoint hne))
      hleftMiddle hrightMiddle
  connected vertex {source target} hsource htarget := by
    rcases hsource with ⟨sourceMiddle, hsourceMiddle, hsource⟩
    rcases htarget with ⟨targetMiddle, htargetMiddle, htarget⟩
    let composed := outer.composedBranchSet inner vertex
    have liftInner {middle : Middle} (hmiddle : middle ∈ outer.branchSet vertex)
        {left right : Large} (hleft : left ∈ inner.branchSet middle)
        (hright : right ∈ inner.branchSet middle) :
        ReflTransGen (Restricted composed (SymmetricClosure largeEdge)) left right := by
      exact Relation.ReflTransGen.lift id (fun _ _ hstep ↦
        ⟨⟨middle, hmiddle, hstep.1⟩, hstep.2.1,
          ⟨middle, hmiddle, hstep.2.2⟩⟩)
        (inner.connected middle hleft hright)
    have crossInner {leftMiddle rightMiddle : Middle}
        (hleftMiddle : leftMiddle ∈ outer.branchSet vertex)
        (hrightMiddle : rightMiddle ∈ outer.branchSet vertex)
        (hmiddleEdge : SymmetricClosure middleEdge leftMiddle rightMiddle)
        {left right : Large} (hleft : left ∈ inner.branchSet leftMiddle)
        (hright : right ∈ inner.branchSet rightMiddle) :
        ReflTransGen (Restricted composed (SymmetricClosure largeEdge)) left right := by
      rcases inner.map_edge hmiddleEdge with
        ⟨leftRep, hleftRep, rightRep, hrightRep, hedge⟩
      exact ((liftInner hleftMiddle hleft hleftRep).tail
        ⟨⟨leftMiddle, hleftMiddle, hleftRep⟩, hedge,
          ⟨rightMiddle, hrightMiddle, hrightRep⟩⟩).trans
        (liftInner hrightMiddle hrightRep hright)
    have liftOuter : ∀ {leftMiddle rightMiddle : Middle},
        leftMiddle ∈ outer.branchSet vertex →
        rightMiddle ∈ outer.branchSet vertex →
        ReflTransGen
          (Restricted (outer.branchSet vertex) (SymmetricClosure middleEdge))
          leftMiddle rightMiddle →
        ∀ {left right : Large}, left ∈ inner.branchSet leftMiddle →
          right ∈ inner.branchSet rightMiddle →
          ReflTransGen (Restricted composed (SymmetricClosure largeEdge)) left right := by
      intro leftMiddle rightMiddle hleftMiddle hrightMiddle hpath
      induction hpath with
      | refl =>
          intro left right hleft hright
          exact liftInner hleftMiddle hleft hright
      | @tail middle last hpath hstep ih =>
          intro left right hleft hright
          rcases inner.nonempty middle with ⟨middleRep, hmiddleRep⟩
          have hmiddle : middle ∈ outer.branchSet vertex := hstep.1
          exact (ih hmiddle hleft hmiddleRep).trans
            (crossInner hmiddle hrightMiddle hstep.2.1 hmiddleRep hright)
    exact liftOuter hsourceMiddle htargetMiddle
      (outer.connected vertex hsourceMiddle htargetMiddle) hsource htarget
  map_edge {source target} hedge := by
    rcases outer.map_edge hedge with
      ⟨sourceMiddle, hsourceMiddle, targetMiddle, htargetMiddle, hmiddle⟩
    rcases inner.map_edge hmiddle with
      ⟨sourceRep, hsourceRep, targetRep, htargetRep, hlarge⟩
    exact ⟨sourceRep, ⟨sourceMiddle, hsourceMiddle, hsourceRep⟩,
      targetRep, ⟨targetMiddle, htargetMiddle, htargetRep⟩, hlarge⟩

end Relation

end
