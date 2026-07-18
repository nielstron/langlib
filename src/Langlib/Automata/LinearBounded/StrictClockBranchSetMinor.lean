module

public import Langlib.Automata.LinearBounded.BranchSetMinor
public import Langlib.Automata.LinearBounded.StrictClockLayering
import Mathlib.Tactic

@[expose]
public section

/-!
# Underlying minors survive a two-level strict clock

Let `edge` be an arbitrary directed relation with a self-loop at every vertex.  Its exact
two-level strict time-unrolling has vertices `V × Fin 2` and edges only from level zero to
level one, following `edge`.  The two clock copies of each vertex form a connected branch set:
the required internal edge is precisely the lifted self-loop.  Every source edge is then
represented between the corresponding branch sets.  Consequently the underlying undirected
source relation is a branch-set
minor of this acyclic directed unrolling.

No finiteness, decidability, or cardinality hypothesis is used for that result.  The finite
section at the end identifies the two-level relation with the first two layers of
`LayeredReachability.StrictEdge`, and hence with the semantic `StrictClockLayering.ClockedStep`
used for LBAs.  This is only a relational branch-set certificate: it does not construct, or
make any claim about, the concrete one-tape clock/serializer compiler.
-/

namespace Relation.TwoLevelStrict

/-- Two clock copies of every vertex. -/
public abbrev Vertex (V : Type u) := V × Fin 2

/-- Exact two-level strict time-unrolling of a directed relation. -/
@[expose]
public def Edge {V : Type u} (edge : V → V → Prop) : Vertex V → Vertex V → Prop :=
  fun old new => new.2.val = old.2.val + 1 ∧ edge old.1 new.1

/-- Every two-level strict edge increases the clock coordinate. -/
public theorem edge_layer_lt {V : Type u} {edge : V → V → Prop}
    {old new : Vertex V} (hstep : Edge edge old new) :
    old.2.val < new.2.val := by
  rcases hstep with ⟨hlayer, _⟩
  omega

/-- Every nonempty path in the two-level unrolling increases its clock coordinate. -/
public theorem transGen_layer_lt {V : Type u} {edge : V → V → Prop}
    {old new : Vertex V} (hpath : TransGen (Edge edge) old new) :
    old.2.val < new.2.val := by
  induction hpath with
  | single hstep => exact edge_layer_lt hstep
  | tail _ hstep ih => exact ih.trans (edge_layer_lt hstep)

/-- The exact two-level strict unrolling is acyclic, independently of the source relation. -/
public theorem edge_acyclic {V : Type u} (edge : V → V → Prop) :
    ∀ vertex : Vertex V, ¬ TransGen (Edge edge) vertex vertex := by
  intro vertex hcycle
  exact (Nat.lt_irrefl vertex.2.val) (transGen_layer_lt hcycle)

/-- The two time copies representing one source vertex. -/
@[expose]
public def branchSet {V : Type u} (vertex : V) : Set (Vertex V) :=
  Set.range fun layer : Fin 2 => (vertex, layer)

/-- A reflexive directed relation is an underlying undirected branch-set minor of its exact
two-level strict time-unrolling.  `SymmetricClosure edge` makes the small relation's forgotten
orientation explicit; the branch-set model also forgets the orientation of the large relation.
-/
public def branchSetMinorModel {V : Type u} (edge : V → V → Prop)
    (selfLoop : ∀ vertex, edge vertex vertex) :
    BranchSetMinorModel (SymmetricClosure edge) (Edge edge) where
  branchSet := branchSet
  nonempty vertex := ⟨(vertex, 0), ⟨0, rfl⟩⟩
  disjoint {left right} hne := by
    rw [Set.disjoint_left]
    rintro _ ⟨leftLayer, rfl⟩ ⟨rightLayer, heq⟩
    exact hne (congrArg Prod.fst heq).symm
  connected vertex {source target} hsource htarget := by
    rcases hsource with ⟨sourceLayer, rfl⟩
    rcases htarget with ⟨targetLayer, rfl⟩
    fin_cases sourceLayer <;> fin_cases targetLayer
    · exact .refl
    · apply ReflTransGen.single
      refine ⟨⟨0, rfl⟩, Or.inl ?_, ⟨1, rfl⟩⟩
      exact ⟨rfl, selfLoop vertex⟩
    · apply ReflTransGen.single
      refine ⟨⟨1, rfl⟩, Or.inr ?_, ⟨0, rfl⟩⟩
      exact ⟨rfl, selfLoop vertex⟩
    · exact .refl
  map_edge {source target} hsourceTarget := by
    rcases hsourceTarget with hforward | hbackward
    · refine ⟨(source, 0), ⟨0, rfl⟩, (target, 1), ⟨1, rfl⟩, Or.inl ?_⟩
      exact ⟨rfl, hforward⟩
    · refine ⟨(source, 1), ⟨1, rfl⟩, (target, 0), ⟨0, rfl⟩, Or.inr ?_⟩
      exact ⟨rfl, hbackward⟩

/-! ## Exact inclusion into the existing finite strict clock -/

section FiniteBridge

variable {V : Type u} [Fintype V]

/-- Include the two time copies into layers zero and one of the full finite clock.  The vertex
component itself witnesses that the finite type is nonempty, so layer one is always available
where this function must be evaluated. -/
@[expose]
public def intoLayered (clocked : Vertex V) : LayeredReachability.Vertex V :=
  (clocked.1, ⟨clocked.2.val, by
    have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨clocked.1⟩
    have hlayer := clocked.2.isLt
    omega⟩)

/-- The inclusion of the first two layers is injective. -/
public theorem intoLayered_injective : Function.Injective (intoLayered (V := V)) := by
  rintro ⟨leftVertex, leftLayer⟩ ⟨rightVertex, rightLayer⟩ heq
  apply Prod.ext
  · exact congrArg (fun cfg : LayeredReachability.Vertex V => cfg.1) heq
  · apply Fin.ext
    exact congrArg (fun cfg : LayeredReachability.Vertex V => cfg.2.val) heq

/-- The exact two-level edge relation is the relation induced by the full strict clock on the
first two layers. -/
public theorem edge_iff_strictEdge (edge : V → V → Prop) (old new : Vertex V) :
    Edge edge old new ↔
      LayeredReachability.StrictEdge edge (intoLayered old) (intoLayered new) := by
  rfl

end FiniteBridge

/-! ## LBA semantic-clock specialization -/

section LBABridge

variable {Γ Λ : Type*} [Fintype Γ] [Fintype Λ]

/-- On fixed-width LBA configurations, the generic inclusion lands in the semantic clocked
configuration type. -/
public abbrev intoClockedCfg {n : ℕ} :=
  intoLayered (V := DLBA.Cfg Γ Λ n)

/-- The generic two-level unrolling of the LBA step relation agrees exactly with the first two
layers of `StrictClockLayering.ClockedStep`.  This is a semantic relation theorem, not an
operational compiler theorem. -/
public theorem edge_iff_clockedStep (M : LBA.Machine Γ Λ) {n : ℕ}
    (old new : Vertex (DLBA.Cfg Γ Λ n)) :
    Edge (LBA.Step M) old new ↔
      LBA.StrictClockLayering.ClockedStep M
        (intoClockedCfg old) (intoClockedCfg new) := by
  rfl

end LBABridge

end Relation.TwoLevelStrict

end
