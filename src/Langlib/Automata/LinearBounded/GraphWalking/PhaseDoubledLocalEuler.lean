module

public import Langlib.Automata.LinearBounded.GraphWalking.PhaseDouble
public import Langlib.Automata.LinearBounded.GraphWalking.LocalEuler
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.AlternatingMatchingCriterion
import Mathlib.Tactic

@[expose]
public section

/-!
# Two matching layers for the phase-doubled local Euler walk

The local Euler operation is a permutation, but an odd Euler orbit cannot be
edge-colored alternately with two colors.  Doubling every port by one bit and
flipping that bit at each Euler step removes this obstruction.

For a bi-unique source relation the matching partition is completely local:
color a doubled edge by the phase of its source.  Bi-uniqueness makes each
color class a partial bijection, while the phase flip prevents two edges of
one color from being composable.  This direct construction works over an
arbitrary vertex type.  A separate theorem records that it also satisfies the
more general `AlternatingMatchingCriterion` interface.

Specializing to `LocalPort.ofMachine` preserves both terminal reachability
and accepting-set reachability of the represented deterministic graph walk.
-/

namespace GraphWalking

open Relation
open FunctionalGraphReversibleTraversal

universe u uLabel uDirection uVertex uState

namespace PhaseDouble

/-- The explicit matching layer of a phase-doubled relation: an edge belongs
to the color carried by its source phase. -/
@[expose]
public def MatchingLayer {V : Type u} (edge : V → V → Prop)
    (color : Fin 2) : (V × Bool) → (V × Bool) → Prop :=
  fun source target ↦ Edge edge source target ∧ color = phase source

/-- The source-phase layers cover every doubled edge exactly once. -/
public theorem matchingLayer_partition {V : Type u} (edge : V → V → Prop)
    (source target : V × Bool) :
    Edge edge source target ↔
      ∃! color, MatchingLayer edge color source target := by
  constructor
  · intro hstep
    refine ⟨phase source, ⟨hstep, rfl⟩, ?_⟩
    intro color hcolor
    exact hcolor.2
  · rintro ⟨color, hcolor, _⟩
    exact hcolor.1

/-- Every explicit layer is a subrelation of the doubled edge relation. -/
public theorem matchingLayer_sub {V : Type u} (edge : V → V → Prop)
    (color : Fin 2) {source target : V × Bool}
    (hstep : MatchingLayer edge color source target) :
    Edge edge source target :=
  hstep.1

/-- A source-phase layer of a doubled partial bijection remains a partial
bijection. -/
public theorem matchingLayer_biUnique {V : Type u} {edge : V → V → Prop}
    (hbiUnique : Relator.BiUnique edge) (color : Fin 2) :
    Relator.BiUnique (MatchingLayer edge color) := by
  have hdoubled : Relator.BiUnique (Edge edge) := biUnique hbiUnique
  constructor
  · intro left right target hleft hright
    exact hdoubled.1 hleft.1 hright.1
  · intro source left right hleft hright
    exact hdoubled.2 hleft.1 hright.1

/-- The source-phase color changes after every doubled edge, so one layer
contains no two composable edges. -/
public theorem matchingLayer_pathLengthAtMostOne
    {V : Type u} (edge : V → V → Prop) (color : Fin 2) :
    LinearTwoDiforestReachability.PathLengthAtMostOne
      (MatchingLayer edge color) := by
  intro first middle last hfirst hlast
  exact phase_ne_of_edge hfirst.1 (hfirst.2.symm.trans hlast.2)

/-- Explicit exact two-directed-matching decomposition of the doubled form
of any partial bijection.  No finiteness or decidable-equality assumption on
the vertex type is needed. -/
public theorem explicit_twoMatching_partition_of_biUnique
    {V : Type u} (edge : V → V → Prop)
    (hbiUnique : Relator.BiUnique edge) :
    (∀ source target, Edge edge source target ↔
      ∃! color, MatchingLayer edge color source target) ∧
    (∀ color source target,
      MatchingLayer edge color source target → Edge edge source target) ∧
    (∀ color, Relator.BiUnique (MatchingLayer edge color)) ∧
    ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne
      (MatchingLayer edge color) := by
  exact ⟨matchingLayer_partition edge,
    fun color source target hstep ↦ matchingLayer_sub edge color hstep,
    matchingLayer_biUnique hbiUnique,
    matchingLayer_pathLengthAtMostOne edge⟩

/-! ## Connection to the general alternating criterion -/

/-- A phase-doubled partial bijection has indegree at most two (indeed, at
most one), as required by the general alternating criterion. -/
public theorem indegreeAtMostTwo_of_biUnique
    {V : Type u} {edge : V → V → Prop}
    (hbiUnique : Relator.BiUnique edge) (target : V × Bool) :
    Set.encard {source | Edge edge source target} ≤ 2 := by
  have hone : Set.encard {source | Edge edge source target} ≤ 1 := by
    apply Set.encard_le_one_iff.mpr
    intro left right hleft hright
    exact (biUnique hbiUnique).1 hleft hright
  exact hone.trans (by norm_num)

/-- Two distinct predecessors of a phase-doubled partial bijection are
impossible, so the double-predecessor sink condition holds vacuously. -/
public theorem doublePredecessorSink_of_biUnique
    {V : Type u} {edge : V → V → Prop}
    (hbiUnique : Relator.BiUnique edge) :
    AlternatingMatchingCriterion.DoublePredecessorSink (Edge edge) := by
  intro left right target hleft hright hne next hnext
  exact hne ((biUnique hbiUnique).1 hleft hright)

/-- The general alternating-matching theorem applies to every phase-doubled
partial bijection.  The direct `MatchingLayer` theorem above is stronger: it
identifies the layers explicitly and does not require decidable equality. -/
public theorem exists_twoMatching_partition_via_alternatingCriterion
    {V : Type u} [DecidableEq V] (edge : V → V → Prop)
    (hbiUnique : Relator.BiUnique edge) :
    ∃ layer : Fin 2 → (V × Bool) → (V × Bool) → Prop,
      (∀ source target, Edge edge source target ↔
        ∃! color, layer color source target) ∧
      (∀ color source target,
        layer color source target → Edge edge source target) ∧
      (∀ color, Relator.BiUnique (layer color)) ∧
      ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne
        (layer color) := by
  apply AlternatingMatchingCriterion.exists_two_directedMatching_partition_of_alternating
    (Edge edge) (biUnique hbiUnique).2
      (indegreeAtMostTwo_of_biUnique hbiUnique)
      (doublePredecessorSink_of_biUnique hbiUnique)
      phase
  intro source target hstep
  exact phase_ne_of_edge hstep

end PhaseDouble

end GraphWalking

namespace FunctionalGraphReversibleTraversal

open GraphWalking Relation

namespace PortSystem

variable {V : Type u} {edge : V → V → Prop} (ports : PortSystem edge)

/-- The local Euler permutation with one alternating control bit. -/
@[expose]
noncomputable def phaseDoubledEuler : Equiv.Perm (ports.Port × Bool) :=
  PhaseDouble.permutation ports.euler

/-- The phase-doubled local Euler relation. -/
@[expose]
public def PhaseDoubledEulerEdge :
    (ports.Port × Bool) → (ports.Port × Bool) → Prop :=
  PhaseDouble.Edge ports.EulerEdge

/-- The explicit matching layers of the phase-doubled Euler relation. -/
@[expose]
public def phaseDoubledEulerLayer (color : Fin 2) :
    (ports.Port × Bool) → (ports.Port × Bool) → Prop :=
  PhaseDouble.MatchingLayer ports.EulerEdge color

/-- The relation definition agrees exactly with one step of the doubled
Euler permutation. -/
public theorem powerEdge_phaseDoubledEuler_iff
    (source target : ports.Port × Bool) :
    PermutationReachability.PowerEdge ports.phaseDoubledEuler source target ↔
      ports.PhaseDoubledEulerEdge source target := by
  exact PhaseDouble.powerEdge_permutation_iff ports.euler source target

/-- The doubled local Euler edge is itself bi-unique. -/
public theorem phaseDoubledEulerEdge_biUnique :
    Relator.BiUnique ports.PhaseDoubledEulerEdge :=
  PhaseDouble.biUnique ports.eulerEdge_biUnique

/-- The explicit source-phase layers are an exact partition of the doubled
local Euler relation into two directed matchings. -/
public theorem phaseDoubledEuler_explicitTwoMatchingPartition :
    (∀ source target, ports.PhaseDoubledEulerEdge source target ↔
      ∃! color, ports.phaseDoubledEulerLayer color source target) ∧
    (∀ color source target,
      ports.phaseDoubledEulerLayer color source target →
        ports.PhaseDoubledEulerEdge source target) ∧
    (∀ color, Relator.BiUnique (ports.phaseDoubledEulerLayer color)) ∧
    ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne
      (ports.phaseDoubledEulerLayer color) := by
  exact PhaseDouble.explicit_twoMatching_partition_of_biUnique
    ports.EulerEdge ports.eulerEdge_biUnique

/-- The phase-doubled Euler relation also meets the hypotheses and conclusion
of the repository's general alternating-matching criterion. -/
public theorem phaseDoubledEuler_alternatingCriterion :
    ∃ layer : Fin 2 → (ports.Port × Bool) → (ports.Port × Bool) → Prop,
      (∀ source target, ports.PhaseDoubledEulerEdge source target ↔
        ∃! color, layer color source target) ∧
      (∀ color source target,
        layer color source target → ports.PhaseDoubledEulerEdge source target) ∧
      (∀ color, Relator.BiUnique (layer color)) ∧
      ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne
        (layer color) := by
  letI : DecidableEq ports.Port := ports.portDecidableEq
  exact PhaseDouble.exists_twoMatching_partition_via_alternatingCriterion
    ports.EulerEdge ports.eulerEdge_biUnique

/-- Projecting away the phase bit preserves and reflects reachability between
specified Euler ports. -/
public theorem exists_phaseDoubledEulerReaches_iff
    (source target : ports.Port) (initialPhase : Bool) :
    (∃ finalPhase,
      ReflTransGen ports.PhaseDoubledEulerEdge
        (source, initialPhase) (target, finalPhase)) ↔
      ReflTransGen ports.EulerEdge source target := by
  exact PhaseDouble.exists_reaches_iff
    ports.EulerEdge source target initialPhase

/-- Projecting away the phase bit preserves reachability of every endpoint
predicate. -/
public theorem exists_phaseDoubledEulerReaches_accepting_iff
    (accepting : V → Prop) (source : V) (initialPhase : Bool) :
    (∃ finish finalPhase,
      ReflTransGen ports.PhaseDoubledEulerEdge
        (ports.anchor source, initialPhase) (finish, finalPhase) ∧
      accepting (ports.endpoint finish)) ↔
    ∃ finish,
      ReflTransGen ports.EulerEdge (ports.anchor source) finish ∧
      accepting (ports.endpoint finish) := by
  exact PhaseDouble.exists_reaches_accepting_iff
    ports.EulerEdge (fun finish ↦ accepting (ports.endpoint finish))
      (ports.anchor source) initialPhase

/-- A phase-doubled Euler run reaches a port incident with the designated
accepting vertex. -/
@[expose]
public def PhaseDoubledEulerAccepts
    (source accept : V) (initialPhase : Bool) : Prop :=
  ∃ finish finalPhase,
    ReflTransGen ports.PhaseDoubledEulerEdge
      (ports.anchor source, initialPhase) (finish, finalPhase) ∧
    ports.endpoint finish = accept

/-- Phase doubling leaves the local Euler acceptance relation unchanged. -/
public theorem phaseDoubledEulerAccepts_iff_eulerAccepts
    (source accept : V) (initialPhase : Bool) :
    ports.PhaseDoubledEulerAccepts source accept initialPhase ↔
      ports.EulerAccepts source accept := by
  exact ports.exists_phaseDoubledEulerReaches_accepting_iff
    (fun vertex ↦ vertex = accept) source initialPhase

end PortSystem

end FunctionalGraphReversibleTraversal

namespace GraphWalking

open Relation

namespace LocalPort

variable {Label : Type uLabel} {Direction : Type uDirection}
  {Vertex : Type uVertex} {State : Type uState}
  (machine : Machine Label Direction State)
  (graph : MemoryGraph Label Direction Vertex)
  (arrival : machine.ArrivalDiscipline)

variable [Fintype State] [DecidableEq State] [DecidableEq Direction]
  [Fintype Vertex] [DecidableEq Vertex]

/-- Phase doubling turns the local Euler walk into an exact union of two
explicit directed matchings while preserving terminal reachability. -/
public theorem phaseDoubledEulerAccepts_iff_reaches
    {source accept : Configuration State Vertex} (initialPhase : Bool)
    (accept_terminal : ∀ next, ¬ machine.Step graph accept next) :
    (ofMachine machine graph arrival).PhaseDoubledEulerAccepts
        source accept initialPhase ↔
      ReflTransGen (machine.Step graph) source accept := by
  rw [(ofMachine machine graph arrival).phaseDoubledEulerAccepts_iff_eulerAccepts]
  exact eulerAccepts_iff_reaches machine graph arrival accept_terminal

/-- Accepting-set form of exact phase-doubled local Euler reachability. -/
public theorem exists_phaseDoubledEulerReaches_accepting_iff_exists_reaches
    (accepting : Configuration State Vertex → Prop)
    (accept_terminal : ∀ accept, accepting accept →
      ∀ next, ¬ machine.Step graph accept next)
    (source : Configuration State Vertex) (initialPhase : Bool) :
    (∃ finish finalPhase,
      ReflTransGen (ofMachine machine graph arrival).PhaseDoubledEulerEdge
        ((ofMachine machine graph arrival).anchor source, initialPhase)
        (finish, finalPhase) ∧
      accepting ((ofMachine machine graph arrival).endpoint finish)) ↔
      ∃ accept, accepting accept ∧
        ReflTransGen (machine.Step graph) source accept := by
  calc
    _ ↔ ∃ finish,
        ReflTransGen (ofMachine machine graph arrival).EulerEdge
          ((ofMachine machine graph arrival).anchor source) finish ∧
        accepting ((ofMachine machine graph arrival).endpoint finish) :=
      (ofMachine machine graph arrival).exists_phaseDoubledEulerReaches_accepting_iff
        accepting source initialPhase
    _ ↔ _ := exists_eulerReaches_accepting_iff_exists_reaches
      machine graph arrival accepting accept_terminal source

/-- Controller-acceptance specialization of the phase-doubled theorem. -/
public theorem exists_phaseDoubledEulerReaches_machineAccepting_iff
    (hterminal : machine.TerminalAcceptance)
    (source : Configuration State Vertex) (initialPhase : Bool) :
    (∃ finish finalPhase,
      ReflTransGen (ofMachine machine graph arrival).PhaseDoubledEulerEdge
        ((ofMachine machine graph arrival).anchor source, initialPhase)
        (finish, finalPhase) ∧
      machine.Accepting graph
        ((ofMachine machine graph arrival).endpoint finish)) ↔
      ∃ accept, machine.Accepting graph accept ∧
        ReflTransGen (machine.Step graph) source accept := by
  apply exists_phaseDoubledEulerReaches_accepting_iff_exists_reaches
    machine graph arrival (machine.Accepting graph)
  intro accept haccept
  exact machine.no_step_of_accepting graph hterminal haccept

end LocalPort

end GraphWalking

end
