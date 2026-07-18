module

public import Langlib.Automata.LinearBounded.FunctionalGraphReversibleTraversal

@[expose]
public section

/-!
# Weak reachability from a root in a cofunctional graph

For a left-unique (cofunctional) directed relation, a vertex with no predecessor is a genuine
root of its entire weak component: every vertex weakly connected to the root is reachable from
it by a directed path.  This is the edge-reversed dual of the terminal-sink theorem
`FunctionalGraphReversibleTraversal.weakReaches_sink_iff_reaches`.

No finiteness or acyclicity assumption is needed.  A directed cycle may occur elsewhere, but
left-uniqueness prevents an edge from entering that cycle from the root's weak component.
-/

namespace FunctionalGraphReversibleTraversal

open Relation

universe u

/-- Along one edge of a cofunctional relation, reachability from a predecessor-free root is
invariant between the edge's endpoints. -/
private theorem root_reaches_iff_of_edge
    {V : Type u} {edge : V → V → Prop}
    (cofunctional : Relator.LeftUnique edge) {root source target : V}
    (root_initial : ∀ predecessor, ¬ edge predecessor root)
    (hstep : edge source target) :
    ReflTransGen edge root source ↔ ReflTransGen edge root target := by
  constructor
  · intro hreach
    exact hreach.tail hstep
  · intro hreach
    rcases hreach.cases_tail with heq | ⟨predecessor, hprefix, hlast⟩
    · subst target
      exact False.elim (root_initial source hstep)
    · have hsource : source = predecessor := cofunctional hstep hlast
      simpa [hsource] using hprefix

/-- Reachability from a predecessor-free root is invariant across one weak edge of a
cofunctional graph. -/
private theorem root_reaches_iff_of_weakStep
    {V : Type u} {edge : V → V → Prop}
    (cofunctional : Relator.LeftUnique edge) {root source target : V}
    (root_initial : ∀ predecessor, ¬ edge predecessor root)
    (hstep : WeakStep edge source target) :
    ReflTransGen edge root source ↔ ReflTransGen edge root target := by
  rcases hstep with hforward | hbackward
  · exact root_reaches_iff_of_edge cofunctional root_initial hforward
  · exact (root_reaches_iff_of_edge cofunctional root_initial hbackward).symm

/-- In a cofunctional graph, weak reachability from a predecessor-free root is exactly forward
directed reachability from that root.

This holds over an arbitrary vertex type and does not require finiteness or acyclicity. -/
public theorem weakReaches_root_iff_reaches
    {V : Type u} {edge : V → V → Prop}
    (cofunctional : Relator.LeftUnique edge) {root target : V}
    (root_initial : ∀ predecessor, ¬ edge predecessor root) :
    ReflTransGen (WeakStep edge) root target ↔
      ReflTransGen edge root target := by
  constructor
  · intro hweak
    induction hweak with
    | refl => exact .refl
    | tail _ hstep ih =>
        exact (root_reaches_iff_of_weakStep
          cofunctional root_initial hstep).mp ih
  · intro hreach
    exact hreach.lift id (fun _ _ hstep => Or.inl hstep)

namespace PortSystem

variable {V : Type u} {edge : V → V → Prop} (ports : PortSystem edge)

local instance cofunctionalRootPortFintype : Fintype ports.Port :=
  ports.portFintype
local instance cofunctionalRootPortDecidableEq : DecidableEq ports.Port :=
  ports.portDecidableEq

private theorem exists_phase_of_visits_rooted
    {actions : List Action} {source target : ports.Port}
    (hvisit : ports.Visits actions source target) :
    ∃ phase, ReflTransGen (PhaseStep actions) 0 phase ∧
      ports.portAt actions source phase = target := by
  obtain ⟨pre, suf, hactions, hexecute⟩ := hvisit
  let phase : Phase actions :=
    ⟨pre.length, by simp [hactions]⟩
  refine ⟨phase, zero_reaches_phase actions phase, ?_⟩
  simpa [portAt, phase, hactions] using hexecute

/-- The exhaustive reversible port schedule visits a vertex exactly when that vertex lies in
the weak component of the source.  This graph-theoretic statement needs no orientation
hypothesis on the relation. -/
public theorem accepts_iff_weakReaches {source target : V} :
    ports.Accepts source target ↔
      ReflTransGen (WeakStep edge) source target := by
  constructor
  · rintro ⟨phase, _, htarget⟩
    have haction := ports.actionReaches_execute
      ((ports.exhaustiveSchedule (ports.anchor source)).take phase.val)
      (ports.anchor source)
    have hweak := ports.weakReaches_endpoint_of_actionReaches haction
    rw [ports.endpoint_anchor source] at hweak
    change ports.endpoint
      (ports.execute
        ((ports.exhaustiveSchedule (ports.anchor source)).take phase.val)
        (ports.anchor source)) = target at htarget
    simpa [htarget] using hweak
  · intro hweak
    have haction : ReflTransGen ports.ActionEdge
        (ports.anchor source) (ports.anchor target) :=
      ports.actionReaches_anchor_of_weakReaches hweak
    have hvisit := ports.exhaustiveSchedule_visits_of_actionReaches haction
    obtain ⟨phase, hphase, hport⟩ :=
      ports.exists_phase_of_visits_rooted hvisit
    refine ⟨phase, hphase, ?_⟩
    rw [hport, ports.endpoint_anchor]

/-- The finite reversible port schedule exactly decides forward reachability from a
predecessor-free root of a cofunctional graph.  Unlike the functional-sink theorem, the queried
target need not be terminal. -/
public theorem accepts_iff_reaches_of_cofunctional_root
    (cofunctional : Relator.LeftUnique edge) {root target : V}
    (root_initial : ∀ predecessor, ¬ edge predecessor root) :
    ports.Accepts root target ↔ ReflTransGen edge root target := by
  rw [ports.accepts_iff_weakReaches,
    weakReaches_root_iff_reaches cofunctional root_initial]

end PortSystem

end FunctionalGraphReversibleTraversal

end
