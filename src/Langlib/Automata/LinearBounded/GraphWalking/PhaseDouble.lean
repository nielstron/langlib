module

public import Langlib.Automata.LinearBounded.PermutationReachability
import Mathlib.Tactic

@[expose]
public section

/-!
# Alternating double covers of reversible walks

A permutation orbit need not be bipartite: an odd cycle cannot itself be
partitioned into two directed matchings by alternating its edges.  The usual
finite-control repair is to add one bit and flip it at every step.  This file
records that repair for an arbitrary relation, without any finiteness
assumption on its vertex type.

The construction is intended for the local Euler walk.  It changes neither
projected reachability nor the set of projected accepting vertices, but gives
the explicit two-valued phase required by the alternating-matching criterion.
-/

namespace GraphWalking

open Relation

universe u

namespace PhaseDouble

/-- Add a control bit which flips across every source edge. -/
@[expose]
public def Edge {V : Type u} (edge : V → V → Prop) :
    (V × Bool) → (V × Bool) → Prop :=
  fun source target => edge source.1 target.1 ∧ target.2 = !source.2

/-- Forget the alternating control bit. -/
@[expose]
public def project {V : Type u} : V × Bool → V := Prod.fst

/-- The finite phase exposed to the two-matching criterion. -/
@[expose]
public def phase {V : Type u} (vertex : V × Bool) : Fin 2 :=
  if vertex.2 then 1 else 0

/-- Every doubled edge projects to its source edge. -/
public theorem edge_project {V : Type u} {edge : V → V → Prop}
    {source target : V × Bool} (hstep : Edge edge source target) :
    edge (project source) (project target) :=
  hstep.1

/-- Every doubled edge crosses the explicit two-valued phase. -/
public theorem phase_ne_of_edge {V : Type u} {edge : V → V → Prop}
    {source target : V × Bool} (hstep : Edge edge source target) :
    phase source ≠ phase target := by
  rcases source with ⟨source, sourceBit⟩
  rcases target with ⟨target, targetBit⟩
  rcases hstep with ⟨_, rfl⟩
  cases sourceBit <;> simp [phase]

/-- Right uniqueness is preserved by the alternating double cover. -/
public theorem rightUnique {V : Type u} {edge : V → V → Prop}
    (hunique : Relator.RightUnique edge) :
    Relator.RightUnique (Edge edge) := by
  rintro ⟨source, sourceBit⟩ ⟨left, leftBit⟩ ⟨right, rightBit⟩
    ⟨hleft, hleftBit⟩ ⟨hright, hrightBit⟩
  have hvertex : left = right := hunique hleft hright
  subst right
  have hbit : leftBit = rightBit := hleftBit.trans hrightBit.symm
  cases hbit
  rfl

/-- Left uniqueness is preserved by the alternating double cover. -/
public theorem leftUnique {V : Type u} {edge : V → V → Prop}
    (hunique : Relator.LeftUnique edge) :
    Relator.LeftUnique (Edge edge) := by
  rintro ⟨left, leftBit⟩ ⟨right, rightBit⟩ ⟨target, targetBit⟩
    ⟨hleft, hleftBit⟩ ⟨hright, hrightBit⟩
  have hvertex : left = right := hunique hleft hright
  subst right
  have hnot : (!leftBit) = (!rightBit) := hleftBit.symm.trans hrightBit
  have hbit : leftBit = rightBit := by
    cases leftBit <;> cases rightBit <;> simp_all
  cases hbit
  rfl

/-- A partial bijection remains a partial bijection after phase doubling. -/
public theorem biUnique {V : Type u} {edge : V → V → Prop}
    (hunique : Relator.BiUnique edge) :
    Relator.BiUnique (Edge edge) :=
  ⟨leftUnique hunique.1, rightUnique hunique.2⟩

/-- A doubled run projects to a run of the original relation. -/
public theorem reaches_project {V : Type u} {edge : V → V → Prop}
    {source target : V × Bool}
    (hreach : ReflTransGen (Edge edge) source target) :
    ReflTransGen edge (project source) (project target) :=
  hreach.lift project (fun _ _ hstep => edge_project hstep)

/-- Every source run lifts from either initial phase. -/
public theorem exists_reaches_lift {V : Type u} {edge : V → V → Prop}
    {source target : V} (initialPhase : Bool)
    (hreach : ReflTransGen edge source target) :
    ∃ finalPhase,
      ReflTransGen (Edge edge)
        (source, initialPhase) (target, finalPhase) := by
  induction hreach with
  | refl =>
      exact ⟨initialPhase, .refl⟩
  | @tail middle target hreach hstep ih =>
      obtain ⟨middlePhase, hlift⟩ := ih
      exact ⟨!middlePhase, hlift.tail ⟨hstep, rfl⟩⟩

/-- Projected reachability is exactly reachability to one of the two phases. -/
public theorem exists_reaches_iff {V : Type u} (edge : V → V → Prop)
    (source target : V) (initialPhase : Bool) :
    (∃ finalPhase,
      ReflTransGen (Edge edge)
        (source, initialPhase) (target, finalPhase)) ↔
      ReflTransGen edge source target := by
  constructor
  · rintro ⟨finalPhase, hreach⟩
    exact reaches_project hreach
  · exact exists_reaches_lift initialPhase

/-- Acceptance by a projected endpoint is unchanged by phase doubling. -/
public theorem exists_reaches_accepting_iff
    {V : Type u} (edge : V → V → Prop) (accepting : V → Prop)
    (source : V) (initialPhase : Bool) :
    (∃ target finalPhase,
      ReflTransGen (Edge edge)
        (source, initialPhase) (target, finalPhase) ∧ accepting target) ↔
      ∃ target, ReflTransGen edge source target ∧ accepting target := by
  constructor
  · rintro ⟨target, finalPhase, hreach, haccept⟩
    exact ⟨target, reaches_project hreach, haccept⟩
  · rintro ⟨target, hreach, haccept⟩
    obtain ⟨finalPhase, hlift⟩ := exists_reaches_lift initialPhase hreach
    exact ⟨target, finalPhase, hlift, haccept⟩

/-! ## Permutation specialization -/

/-- The alternating double cover of a total permutation. -/
@[expose]
public def permutation {V : Type u} (permutation : Equiv.Perm V) :
    Equiv.Perm (V × Bool) where
  toFun vertex := (permutation vertex.1, !vertex.2)
  invFun vertex := (permutation⁻¹ vertex.1, !vertex.2)
  left_inv := by
    rintro ⟨vertex, bit⟩
    simp
  right_inv := by
    rintro ⟨vertex, bit⟩
    simp

/-- One step of the doubled permutation is exactly the doubled source edge. -/
public theorem powerEdge_permutation_iff {V : Type u}
    (permutation : Equiv.Perm V) (source target : V × Bool) :
    PermutationReachability.PowerEdge (PhaseDouble.permutation permutation)
        source target ↔
      Edge (PermutationReachability.PowerEdge permutation) source target := by
  rcases source with ⟨source, sourceBit⟩
  rcases target with ⟨target, targetBit⟩
  change
    (permutation source, !sourceBit) = (target, targetBit) ↔
      permutation source = target ∧ targetBit = !sourceBit
  constructor
  · intro hstep
    exact ⟨congrArg Prod.fst hstep, (congrArg Prod.snd hstep).symm⟩
  · rintro ⟨hvertex, hbit⟩
    exact Prod.ext hvertex hbit.symm

/-- The doubled permutation is still a partial bijection, now with an explicit
alternating phase on every edge. -/
public theorem permutation_biUnique {V : Type u}
    (permutation : Equiv.Perm V) :
    Relator.BiUnique
      (PermutationReachability.PowerEdge
        (PhaseDouble.permutation permutation)) := by
  rw [show PermutationReachability.PowerEdge
      (PhaseDouble.permutation permutation) =
        Edge (PermutationReachability.PowerEdge permutation) by
    funext source target
    apply propext
    exact powerEdge_permutation_iff permutation source target]
  apply biUnique
  constructor
  · intro left right target hleft hright
    exact permutation.injective (hleft.trans hright.symm)
  · intro source left right hleft hright
    exact hleft.symm.trans hright

end PhaseDouble

end GraphWalking

end
