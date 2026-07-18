module

public import Langlib.Automata.LinearBounded.GraphWalking.EndmarkerNonclamping
public import Langlib.Automata.LinearBounded.GraphWalking.PhaseDoubledLocalEuler
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical bounded-tape runs and the phase-doubled local Euler walk

This file closes the semantic bridge between three existing constructions:

* the terminalized endmarker simulator
  `EndmarkerNonclamping.deterministicSimMachine`;
* its partial, locally reversible bounded-tape graph-walking controller; and
* the phase-doubled local Euler traversal of the direction-determinate lift.

The key run theorem is genuinely two-sided.  A controller run always projects
to a deterministic bounded-tape run.  Conversely, on the canonical endmarked
input, the endpoint-marker invariant makes every reachable simulator step
nonclamping, so every deterministic step is a controller step.  This gives
exact whole-run and acceptance equivalences, not merely step soundness.

The final theorem also reconnects the construction to the repository's
marker-free `(machine, acceptEmpty)` language presentation.  It uses only the
already established
`toLBA'` and `simMachine` language equivalences; it does not assert a new
language-class inclusion or a raw-LBA implementation of the Euler ports.
-/

namespace GraphWalking

open Relation
open FunctionalGraphReversibleTraversal

universe uInput uWork uState

namespace BoundedEulerBridge

/-! ## Generic deterministic reachability and terminal acceptance -/

/-- Iterating a deterministic bounded-tape step produces a path in its
one-step graph. -/
public theorem reflTransGen_step_of_iterateStep_eq_some
    {A : Type uInput} {State : Type uState} {n : Nat}
    (machine : DLBA.Machine A State) (source target : DLBA.Cfg A State n)
    {steps : Nat} (hiterate : DLBA.iterateStep machine source steps = some target) :
    ReflTransGen (fun left right => DLBA.step machine left = some right)
      source target := by
  induction steps generalizing target with
  | zero =>
      simp only [DLBA.iterateStep_zero, Option.some.injEq] at hiterate
      subst target
      exact .refl
  | succ steps ih =>
      rw [DLBA.iterateStep_succ] at hiterate
      cases hmiddle : DLBA.iterateStep machine source steps with
      | none => simp [hmiddle] at hiterate
      | some middle =>
          have hlast : DLBA.step machine middle = some target := by
            simpa [hmiddle] using hiterate
          exact (ih middle hmiddle).tail hlast

/-- Every path in a deterministic bounded-tape step graph is realized by a
finite iterate. -/
public theorem exists_iterateStep_eq_some_of_reflTransGen_step
    {A : Type uInput} {State : Type uState} {n : Nat}
    (machine : DLBA.Machine A State) {source target : DLBA.Cfg A State n}
    (hreaches : ReflTransGen
      (fun left right => DLBA.step machine left = some right) source target) :
    ∃ steps, DLBA.iterateStep machine source steps = some target := by
  induction hreaches with
  | refl => exact ⟨0, rfl⟩
  | @tail middle target _ hlast ih =>
      obtain ⟨steps, hmiddle⟩ := ih
      refine ⟨steps + 1, ?_⟩
      rw [DLBA.iterateStep_succ, hmiddle]
      exact hlast

/-- For a machine whose accepting states are terminal, DLBA acceptance is
exactly reachability of an accepting configuration. -/
public theorem dlbaAccepts_iff_exists_reaches_accepting_of_terminal
    {A : Type uInput} {State : Type uState} {n : Nat}
    (machine : DLBA.Machine A State)
    (hterminal : ∀ state observed, machine.accept state = true →
      machine.transition state observed = none)
    (source : DLBA.Cfg A State n) :
    DLBA.Accepts machine source ↔
      ∃ target, ReflTransGen
          (fun left right => DLBA.step machine left = some right)
          source target ∧
        machine.accept target.state = true := by
  constructor
  · rintro ⟨steps, _hhalt, target, htarget, haccept⟩
    exact ⟨target,
      reflTransGen_step_of_iterateStep_eq_some machine source target htarget,
      haccept⟩
  · rintro ⟨target, hreaches, haccept⟩
    obtain ⟨steps, htarget⟩ :=
      exists_iterateStep_eq_some_of_reflTransGen_step machine hreaches
    have htransition :
        machine.transition target.state target.tape.read = none :=
      hterminal target.state target.tape.read haccept
    have hhalt : DLBA.step machine target = none := by
      unfold DLBA.step
      simp only [htransition]
    refine ⟨steps, ?_, target, htarget, haccept⟩
    rw [DLBA.iterateStep_succ, htarget]
    exact hhalt

/-! ## The canonical simulator and its graph-walking presentations -/

/-- The locally reversible controller selected from the canonical
deterministic endmarker simulator. -/
@[expose]
public noncomputable def controller
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) :
    Machine (LBA.EndAlpha T Gamma)
      (BoundedTapeMemory.Direction (LBA.EndAlpha T Gamma))
      (LBA.SimState (Option State)) :=
  BoundedTapeController.machine
    (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty)

/-- The direction-determinate state expansion used by local incoming-port
reconstruction. -/
@[expose]
public noncomputable def liftedController
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) :=
  (controller machine acceptEmpty).directionLift

/-- A fixed initial value for the remembered incoming operation.  It has no
semantic effect: the direction lift overwrites it after the first step. -/
@[expose]
public def initialDirection (T : Type uInput) (Gamma : Type uWork) :
    BoundedTapeMemory.Direction (LBA.EndAlpha T Gamma) :=
  .stationary LBA.leftMark LBA.leftMark

/-- The canonical simulator configuration on a bracketed word. -/
@[expose]
public noncomputable def simulatorStart
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T) :
    DLBA.Cfg (LBA.EndAlpha T Gamma) (LBA.SimState (Option State))
      (word.length + 1) :=
  ⟨(EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty).initial,
    LBA.loadEnd word⟩

/-- The same canonical configuration in graph-walking product form. -/
@[expose]
public noncomputable def controllerStart
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T) :
    Configuration (LBA.SimState (Option State))
      (DLBA.BoundedTape (LBA.EndAlpha T Gamma) (word.length + 1)) :=
  ((EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty).initial,
    LBA.loadEnd word)

/-- Initial configuration of the direction-determinate controller. -/
@[expose]
public noncomputable def liftedControllerStart
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T) :
    Configuration
      (DirectionLiftState (LBA.SimState (Option State))
        (BoundedTapeMemory.Direction (LBA.EndAlpha T Gamma)))
      (DLBA.BoundedTape (LBA.EndAlpha T Gamma) (word.length + 1)) :=
  (((EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty).initial,
      initialDirection T Gamma),
    LBA.loadEnd word)

/-- Exact whole-run correspondence on a canonical input.  The target is
arbitrary; only the source of each simulated forward step needs the
canonical-reachability invariant. -/
public theorem controller_reaches_iff_simulator_reaches
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq T] [DecidableEq Gamma]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T)
    {target : DLBA.Cfg (LBA.EndAlpha T Gamma) (LBA.SimState (Option State))
      (word.length + 1)} :
    ReflTransGen
        ((controller machine acceptEmpty).Step
          (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1)))
        (controllerStart machine acceptEmpty word)
        (target.state, target.tape) ↔
      ReflTransGen
        (fun left right =>
          DLBA.step
            (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty)
            left = some right)
        (simulatorStart machine acceptEmpty word) target := by
  let simulator :=
    EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty
  let graph := BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1)
  constructor
  · intro hcontroller
    exact BoundedTapeController.reaches_sound simulator hcontroller
  · intro hsimulator
    induction hsimulator with
    | refl => exact .refl
    | @tail middle target hprefix hlast ih =>
        apply ih.tail
        exact (EndmarkerNonclamping.controller_step_iff_dlba_step_of_reachable
          machine acceptEmpty word hprefix).2 hlast

/-- Acceptance of the canonical deterministic simulator is exactly
accepting reachability in its bounded-tape graph-walking controller. -/
public theorem simulatorAccepts_iff_controller_reaches_accepting
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq T] [DecidableEq Gamma]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T) :
    DLBA.Accepts
        (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty)
        (simulatorStart machine acceptEmpty word) ↔
      ∃ accept,
        (controller machine acceptEmpty).Accepting
          (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1))
          accept ∧
        ReflTransGen
          ((controller machine acceptEmpty).Step
            (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1)))
          (controllerStart machine acceptEmpty word) accept := by
  let simulator :=
    EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty
  rw [dlbaAccepts_iff_exists_reaches_accepting_of_terminal simulator
    (EndmarkerNonclamping.deterministicSimMachine_terminalAcceptance
      machine acceptEmpty)]
  constructor
  · rintro ⟨target, hreaches, haccept⟩
    refine ⟨(target.state, target.tape), ?_,
      (controller_reaches_iff_simulator_reaches
        machine acceptEmpty word).2 hreaches⟩
    exact haccept
  · rintro ⟨⟨targetState, targetTape⟩, haccept, hreaches⟩
    let target : DLBA.Cfg (LBA.EndAlpha T Gamma)
        (LBA.SimState (Option State)) (word.length + 1) :=
      ⟨targetState, targetTape⟩
    refine ⟨target,
      (controller_reaches_iff_simulator_reaches
        machine acceptEmpty word).1 hreaches, ?_⟩
    exact haccept

/-- Terminal acceptance is preserved by the direction-determinate state
lift. -/
public theorem liftedController_terminalAcceptance
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq T] [DecidableEq Gamma]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) :
    (liftedController machine acceptEmpty).TerminalAcceptance := by
  intro state observed haccept
  have hbase :=
    EndmarkerNonclamping.controller_deterministicSimMachine_terminalAcceptance
      machine acceptEmpty state.1 observed haccept
  change ((controller machine acceptEmpty).transition state.1 observed).map
      (fun output => (output, output.2)) = none
  change (controller machine acceptEmpty).transition state.1 observed = none at hbase
  rw [hbase]
  rfl

/-- Direction lifting preserves and reflects accepting reachability from the
chosen canonical start. -/
public theorem simulatorAccepts_iff_liftedController_reaches_accepting
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [DecidableEq T] [DecidableEq Gamma]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T) :
    DLBA.Accepts
        (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty)
        (simulatorStart machine acceptEmpty word) ↔
      ∃ accept,
        (liftedController machine acceptEmpty).Accepting
          (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1))
          accept ∧
        ReflTransGen
          ((liftedController machine acceptEmpty).Step
            (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1)))
          (liftedControllerStart machine acceptEmpty word) accept := by
  rw [simulatorAccepts_iff_controller_reaches_accepting
    machine acceptEmpty word]
  let base := controller machine acceptEmpty
  let graph := BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1)
  constructor
  · rintro ⟨accept, haccept, hreaches⟩
    obtain ⟨liftedAccept, hlifted, hforget⟩ :=
      base.exists_directionLift_reaches graph (initialDirection T Gamma) hreaches
    refine ⟨liftedAccept, ?_, hlifted⟩
    change base.Accepting graph (forgetDirection liftedAccept)
    rw [hforget]
    exact haccept
  · rintro ⟨accept, haccept, hreaches⟩
    refine ⟨forgetDirection accept, ?_,
      base.reaches_forgetDirection graph hreaches⟩
    exact haccept

/-! ## Phase-doubled local Euler acceptance -/

/-- The finite local port system of the direction-determinate canonical
controller on one bounded input tape. -/
@[expose]
public noncomputable def localPorts
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype State]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq State]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T) :=
  LocalPort.ofMachine
    (liftedController machine acceptEmpty)
    (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1))
    (controller machine acceptEmpty).directionLiftArrival

/-- Exact acceptance equivalence between the canonical deterministic
simulator and the phase-doubled local Euler orbit.  The initial phase is
arbitrary. -/
public theorem simulatorAccepts_iff_phaseDoubledLocalEuler
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype State]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq State]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T) (initialPhase : Bool) :
    DLBA.Accepts
        (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty)
        (simulatorStart machine acceptEmpty word) ↔
      ∃ finish finalPhase,
        ReflTransGen
          (localPorts machine acceptEmpty word).PhaseDoubledEulerEdge
          ((localPorts machine acceptEmpty word).anchor
              (liftedControllerStart machine acceptEmpty word), initialPhase)
          (finish, finalPhase) ∧
        (liftedController machine acceptEmpty).Accepting
          (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1))
          ((localPorts machine acceptEmpty word).endpoint finish) := by
  rw [simulatorAccepts_iff_liftedController_reaches_accepting
    machine acceptEmpty word]
  exact (LocalPort.exists_phaseDoubledEulerReaches_machineAccepting_iff
    (liftedController machine acceptEmpty)
    (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1))
    (controller machine acceptEmpty).directionLiftArrival
    (liftedController_terminalAcceptance machine acceptEmpty)
    (liftedControllerStart machine acceptEmpty word) initialPhase).symm

/-- The same Euler criterion stated directly for membership in the language
presented by the marker-free machine together with its explicit empty-word
bit.  This is a composition of the existing `toLBA'` and endmarker-simulator
equivalences with the theorem above. -/
public theorem sourceLanguage_iff_phaseDoubledLocalEuler
    {T : Type uInput} {Gamma : Type uWork} {State : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype State]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq State]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T) (initialPhase : Bool) :
    DLBA.LanguageRecognized machine (fun input => some (Sum.inl input))
        acceptEmpty word ↔
      ∃ finish finalPhase,
        ReflTransGen
          (localPorts machine acceptEmpty word).PhaseDoubledEulerEdge
          ((localPorts machine acceptEmpty word).anchor
              (liftedControllerStart machine acceptEmpty word), initialPhase)
          (finish, finalPhase) ∧
        (liftedController machine acceptEmpty).Accepting
          (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1))
          ((localPorts machine acceptEmpty word).endpoint finish) := by
  have hmarkerFree :
      DLBA.LanguageRecognized machine (fun input => some (Sum.inl input))
          acceptEmpty =
        LBA.LanguageRecognized (DLBA.toLBA' machine)
          (fun input => some (Sum.inl input)) acceptEmpty := by
    have hvia :
        DLBA.LanguageViaEmbed machine (fun input => some (Sum.inl input)) =
          LBA.LanguageViaEmbed (DLBA.toLBA' machine)
            (fun input => some (Sum.inl input)) :=
      dlba_language_eq_lba_language machine
        (fun input => some (Sum.inl input))
    funext input
    apply propext
    simp only [DLBA.LanguageRecognized, LBA.LanguageRecognized, hvia]
  rw [hmarkerFree]
  rw [← LBA.language_simMachine_eq]
  change LBA.Accepts
      (LBA.simMachine (DLBA.toLBA' machine) acceptEmpty)
      ⟨(LBA.simMachine (DLBA.toLBA' machine) acceptEmpty).initial,
        LBA.loadEnd word⟩ ↔ _
  rw [← EndmarkerNonclamping.deterministicSimMachine_accepts_iff
    machine acceptEmpty]
  exact simulatorAccepts_iff_phaseDoubledLocalEuler
    machine acceptEmpty word initialPhase

end BoundedEulerBridge

end GraphWalking

end
