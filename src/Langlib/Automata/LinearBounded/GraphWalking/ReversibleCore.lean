module

public import Langlib.Automata.LinearBounded.GraphWalking.LocalEuler
import Mathlib.Tactic

@[expose]
public section

/-!
# Reversible local core for an arbitrary deterministic graph walker

The first finite-control transformation remembers the direction of arrival.
The second replaces the resulting functional configuration graph by the
uniform local Euler contour.  Together they give exact reachability and
acceptance equivalences for every finite locally reversible memory graph.

The result is deliberately phrased at the port-operation boundary.  It does
not identify one port permutation step with one raw LBA step: an incoming-port
test has an out-of-sync phase at the neighbouring memory vertex, which the
tape compiler must expose and protect against clamping.
-/

namespace GraphWalking

open Relation
open FunctionalGraphReversibleTraversal

universe uLabel uDirection uVertex uState

variable {Label : Type uLabel} {Direction : Type uDirection}
  {Vertex : Type uVertex} {State : Type uState}

/-- **Arbitrary deterministic-walk form.**  After remembering the arrival
direction in finite control, the single local Euler permutation reaches a
port representing `target` exactly when the original walk reaches `target`.

Only `State`, `Direction`, and the particular input memory graph are finite.
The rotation order is on `LocalPort.Slot (State × Direction)`, never on the
configuration universe. -/
public theorem directionLift_localEuler_iff_reaches
    [Fintype State] [DecidableEq State]
    [Fintype Direction] [DecidableEq Direction]
    [Fintype Vertex] [DecidableEq Vertex]
    (machine : Machine Label Direction State)
    (graph : MemoryGraph Label Direction Vertex)
    (initialDirection : Direction)
    {source target : Configuration State Vertex}
    (target_terminal : ∀ next, ¬ machine.Step graph target next) :
    let lifted := machine.directionLift
    let arrival := machine.directionLiftArrival
    let ports := LocalPort.ofMachine lifted graph arrival
    (∃ finish,
      ReflTransGen ports.EulerEdge
        (ports.anchor ((source.1, initialDirection), source.2)) finish ∧
      forgetDirection (ports.endpoint finish) = target) ↔
      ReflTransGen (machine.Step graph) source target := by
  dsimp only
  let lifted := machine.directionLift
  let arrival := machine.directionLiftArrival
  let ports := LocalPort.ofMachine lifted graph arrival
  have hterminal : ∀ accept,
      forgetDirection accept = target →
      ∀ next, ¬ lifted.Step graph accept next := by
    intro accept hforget next hstep
    have hprojected := machine.step_forgetDirection graph hstep
    rw [hforget] at hprojected
    exact target_terminal _ hprojected
  have heuler := LocalPort.exists_eulerReaches_accepting_iff_exists_reaches
    lifted graph arrival (fun accept => forgetDirection accept = target)
    hterminal ((source.1, initialDirection), source.2)
  constructor
  · intro hrun
    obtain ⟨accept, hforget, hreach⟩ := heuler.mp hrun
    exact (machine.exists_directionLift_reaches_iff
      graph initialDirection).mp ⟨accept, hreach, hforget⟩
  · intro hreach
    obtain ⟨accept, hlifted, hforget⟩ :=
      (machine.exists_directionLift_reaches_iff
        graph initialDirection).mpr hreach
    exact heuler.mpr ⟨accept, hforget, hlifted⟩

/-- Accepting-set form for an arbitrary deterministic walker.  A reachable
Euler endpoint projects to an accepting source configuration exactly when the
source computation reaches some accepting configuration. -/
public theorem directionLift_localEuler_accepting_iff
    [Fintype State] [DecidableEq State]
    [Fintype Direction] [DecidableEq Direction]
    [Fintype Vertex] [DecidableEq Vertex]
    (machine : Machine Label Direction State)
    (graph : MemoryGraph Label Direction Vertex)
    (initialDirection : Direction)
    (hterminal : machine.TerminalAcceptance)
    (source : Configuration State Vertex) :
    let lifted := machine.directionLift
    let arrival := machine.directionLiftArrival
    let ports := LocalPort.ofMachine lifted graph arrival
    (∃ finish,
      ReflTransGen ports.EulerEdge
        (ports.anchor ((source.1, initialDirection), source.2)) finish ∧
      machine.Accepting graph (forgetDirection (ports.endpoint finish))) ↔
      ∃ accept, machine.Accepting graph accept ∧
        ReflTransGen (machine.Step graph) source accept := by
  dsimp only
  let lifted := machine.directionLift
  let arrival := machine.directionLiftArrival
  let ports := LocalPort.ofMachine lifted graph arrival
  have hliftedTerminal : ∀ accept,
      machine.Accepting graph (forgetDirection accept) →
      ∀ next, ¬ lifted.Step graph accept next := by
    intro accept haccept next hstep
    have hprojected := machine.step_forgetDirection graph hstep
    exact machine.no_step_of_accepting graph hterminal haccept _ hprojected
  have heuler := LocalPort.exists_eulerReaches_accepting_iff_exists_reaches
    lifted graph arrival
    (fun accept => machine.Accepting graph (forgetDirection accept))
    hliftedTerminal ((source.1, initialDirection), source.2)
  constructor
  · intro hrun
    obtain ⟨liftedAccept, haccept, hliftedReach⟩ := heuler.mp hrun
    exact ⟨forgetDirection liftedAccept, haccept,
      machine.reaches_forgetDirection graph hliftedReach⟩
  · rintro ⟨accept, haccept, hreach⟩
    obtain ⟨liftedAccept, hliftedReach, hforget⟩ :=
      machine.exists_directionLift_reaches graph initialDirection hreach
    exact heuler.mpr ⟨liftedAccept, hforget ▸ haccept, hliftedReach⟩

/-! ## Exact remaining tape-level obligation

The next compiler lemma must refine one `ports.euler` operation into raw LBA
microsteps while keeping the incoming probe out of sync:

* on a valid incoming slot, move oppositely once and finish at the predecessor
  in its outgoing slot;
* on an invalid incoming slot, move oppositely, discover the failed finite
  transition test, and move forward again to restore the original target port;
* if either physical move clamps, enter a nonaccepting terminal collision
  state rather than pretending that the partial memory move succeeded.

The refinement must prove macro simulation and reflection, raw functionality,
in-degree at most two, terminality of every double-predecessor collision, and
a phase parity that flips on every microstep.  Those are precisely the inputs
to the repository's alternating-matching criterion.

Raw clamped head movement cannot itself instantiate `MemoryGraph`: a boundary
landing has two distinct predecessors, whereas `MemoryGraph.move_leftUnique`
proves every named partial move left-unique.  Thus quotienting the incoming
probe into a synchronized four-step shuttle is not a valid shortcut; the
boundary-safe refinement above is essential.
-/

end GraphWalking

end
