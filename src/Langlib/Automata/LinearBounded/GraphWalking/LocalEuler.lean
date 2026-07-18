module

public import Langlib.Automata.LinearBounded.GraphWalking.LocalPort
public import Langlib.Automata.LinearBounded.GraphWalking.FixedStubContour
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact local Euler backtracking for deterministic graph walks

This module combines the uniform finite-control ports with the fixed-stub
contour theorem.  For every finite memory graph, the single permutation
`swap ∘ rotate` visits a terminal configuration exactly when the original
deterministic walk reaches it.  The rotation order is independent of the
number of memory vertices.

This is the local semantic core of the Kunc--Okhotin/Sipser backtracking
construction.  An incoming port deliberately remembers its candidate source
state while logically sitting at the target configuration.  Testing that port
moves once in the opposite direction and inspects the predecessor label.  A
tape-level compiler should retain this out-of-sync phase; synchronizing first
and then erasing the saved source instruction would introduce precisely the
backward merge that the construction avoids.
-/

namespace GraphWalking

open Classical Relation
open FunctionalGraphReversibleTraversal

universe uLabel uDirection uVertex uState

namespace LocalPort

variable {Label : Type uLabel} {Direction : Type uDirection}
  {Vertex : Type uVertex} {State : Type uState}
  (machine : Machine Label Direction State)
  (graph : MemoryGraph Label Direction Vertex)
  (arrival : machine.ArrivalDiscipline)

/-- The parent port in the backward basin of `accept`.  The root uses its
anchor as a virtual parent; every other basin vertex uses its outgoing slot. -/
@[expose]
public def basinParentPort [DecidableEq State] [DecidableEq Vertex]
    (accept vertex : Configuration State Vertex) :
    Option (Port State Vertex) :=
  if vertex = accept then some (anchor vertex)
  else some (vertex, .outgoing)

@[simp]
public theorem basinParentPort_accept [DecidableEq State] [DecidableEq Vertex]
    (accept : Configuration State Vertex) :
    basinParentPort accept accept = some (anchor accept) := by
  simp [basinParentPort]

public theorem basinParentPort_of_ne [DecidableEq State] [DecidableEq Vertex]
    {accept vertex : Configuration State Vertex} (hne : vertex ≠ accept) :
    basinParentPort accept vertex = some (vertex, .outgoing) := by
  simp [basinParentPort, hne]

/-- Any directed edge into a terminal basin carries basin membership forward. -/
private theorem basin_forward_closed
    {accept source target : Configuration State Vertex}
    (accept_terminal : ∀ next, ¬ machine.Step graph accept next)
    (hsource : ReflTransGen (machine.Step graph) source accept)
    (hstep : machine.Step graph source target) :
    ReflTransGen (machine.Step graph) target accept := by
  have hweakTargetSource :
      ReflTransGen (WeakStep (machine.Step graph)) target source :=
    .single (Or.inr hstep)
  have hweakSourceAccept :
      ReflTransGen (WeakStep (machine.Step graph)) source accept :=
    hsource.lift id (fun _ _ edge => Or.inl edge)
  exact (weakReaches_sink_iff_reaches (machine.step_rightUnique graph) accept_terminal).mp
    (hweakTargetSource.trans hweakSourceAccept)

variable [Fintype State] [DecidableEq State] [DecidableEq Direction]
  [Fintype Vertex] [DecidableEq Vertex]

/-- The local uniform ports form a fixed-stub ranked tree on the backward
basin of any terminal configuration. -/
noncomputable def rankedBasin
    (accept : Configuration State Vertex)
    (accept_terminal : ∀ next, ¬ machine.Step graph accept next) :
    (ofMachine machine graph arrival).FixedStubRankedTree where
  member := fun vertex => ReflTransGen (machine.Step graph) vertex accept
  rank := basinRank (machine.Step graph) accept
  parentPort := basinParentPort accept
  parent_endpoint := by
    intro vertex port hport
    by_cases hroot : vertex = accept
    · subst vertex
      simp only [basinParentPort_accept, Option.some.injEq] at hport
      subst port
      rfl
    · rw [basinParentPort_of_ne hroot] at hport
      cases Option.some.inj hport
      rfl
  classify := by
    intro vertex port hmember hendpoint
    rcases port with ⟨portVertex, slot⟩
    simp only [ofMachine, endpoint] at hendpoint
    subst portVertex
    cases slot with
    | anchor =>
        exact Or.inl rfl
    | outgoing =>
        by_cases hroot : vertex = accept
        · subst vertex
          cases hnext : machine.next graph accept with
          | none =>
              exact Or.inl (by simp [ofMachine, swap, swapFun, hnext])
          | some target =>
              exact (accept_terminal target hnext).elim
        · exact Or.inr (Or.inl
            ⟨(vertex, .outgoing), basinParentPort_of_ne hroot, rfl⟩)
    | incoming sourceState =>
        cases hincoming : incomingSource machine graph arrival vertex sourceState with
        | none =>
            exact Or.inl (by simp [ofMachine, swap, swapFun, hincoming])
        | some source =>
            have hstep : machine.Step graph source vertex :=
              step_of_incomingSource_eq_some machine graph arrival hincoming
            have hchildMember : ReflTransGen (machine.Step graph) source accept :=
              hmember.head hstep
            have hrank :
                basinRank (machine.Step graph) accept source <
                  basinRank (machine.Step graph) accept vertex :=
              basinRank_lt_of_edge (machine.step_rightUnique graph) accept_terminal
                hchildMember hstep
            have hsourceNe : source ≠ accept := by
              intro heq
              subst source
              exact accept_terminal vertex hstep
            have hsourceState : source.1 = sourceState :=
              fst_eq_of_incomingSource_eq_some
                machine graph arrival hincoming
            exact Or.inr (Or.inr
              ⟨source, (source, .outgoing), hchildMember, hrank,
                basinParentPort_of_ne hsourceNe, by
                  change swap machine graph arrival (source, .outgoing) =
                    (vertex, .incoming sourceState)
                  change machine.next graph source = some vertex at hstep
                  simp [swap, swapFun, hstep, hsourceState]⟩)
  edge_parent := by
    intro source target hmember hstep
    have hsourceNe : source ≠ accept := by
      intro heq
      subst source
      exact accept_terminal target hstep
    refine ⟨(source, .outgoing), basinParentPort_of_ne hsourceNe, ?_⟩
    change endpoint (swap machine graph arrival (source, .outgoing)) = target
    change machine.next graph source = some target at hstep
    simp [endpoint, swap, swapFun, hstep]
  forward_closed := by
    intro source target hsource hstep
    exact basin_forward_closed machine graph accept_terminal hsource hstep

/-- **Local finite-control Euler theorem.**  The single uniform local Euler
permutation reaches a terminal configuration exactly when the source
deterministic graph walk does. -/
public theorem eulerAccepts_iff_reaches
    {source accept : Configuration State Vertex}
    (accept_terminal : ∀ next, ¬ machine.Step graph accept next) :
    (ofMachine machine graph arrival).EulerAccepts source accept ↔
      ReflTransGen (machine.Step graph) source accept := by
  constructor
  · intro haccept
    have hweak :=
      (ofMachine machine graph arrival).weakReaches_of_eulerAccepts haccept
    exact (weakReaches_sink_iff_reaches
      (machine.step_rightUnique graph) accept_terminal).mp hweak
  · intro hreach
    exact PortSystem.FixedStubRankedTree.eulerReaches_accept_of_reaches
      (ports := ofMachine machine graph arrival)
      (rankedBasin machine graph arrival accept accept_terminal)
      hreach hreach

/-- Accepting-set form.  If every accepting configuration is terminal, the
local Euler orbit visits an accepting endpoint exactly when the source walk
reaches an accepting configuration. -/
public theorem exists_eulerReaches_accepting_iff_exists_reaches
    (accepting : Configuration State Vertex → Prop)
    (accept_terminal : ∀ accept, accepting accept →
      ∀ next, ¬ machine.Step graph accept next)
    (source : Configuration State Vertex) :
    (∃ finish,
      ReflTransGen (ofMachine machine graph arrival).EulerEdge
        ((ofMachine machine graph arrival).anchor source) finish ∧
      accepting ((ofMachine machine graph arrival).endpoint finish)) ↔
      ∃ accept, accepting accept ∧
        ReflTransGen (machine.Step graph) source accept := by
  constructor
  · rintro ⟨finish, hfinish, haccept⟩
    let accept := (ofMachine machine graph arrival).endpoint finish
    have heuler : (ofMachine machine graph arrival).EulerAccepts source accept :=
      ⟨finish, hfinish, rfl⟩
    exact ⟨accept, haccept,
      (eulerAccepts_iff_reaches machine graph arrival
        (accept_terminal accept haccept)).mp heuler⟩
  · rintro ⟨accept, haccept, hreach⟩
    obtain ⟨finish, hfinish, hendpoint⟩ :=
      (eulerAccepts_iff_reaches machine graph arrival
        (accept_terminal accept haccept)).mpr hreach
    exact ⟨finish, hfinish, hendpoint ▸ haccept⟩

/-- Controller-acceptance specialization of the accepting-set theorem. -/
public theorem exists_eulerReaches_machineAccepting_iff
    (hterminal : machine.TerminalAcceptance)
    (source : Configuration State Vertex) :
    (∃ finish,
      ReflTransGen (ofMachine machine graph arrival).EulerEdge
        ((ofMachine machine graph arrival).anchor source) finish ∧
      machine.Accepting graph
        ((ofMachine machine graph arrival).endpoint finish)) ↔
      ∃ accept, machine.Accepting graph accept ∧
        ReflTransGen (machine.Step graph) source accept := by
  apply exists_eulerReaches_accepting_iff_exists_reaches
    machine graph arrival (machine.Accepting graph)
  intro accept haccept
  exact machine.no_step_of_accepting graph hterminal haccept

end LocalPort

end GraphWalking

end
