module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.CanonicalSimulation
public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.Structural
public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.MarkedMachineSimulation
import Mathlib.Tactic

@[expose]
public section

/-!
# Whole-run reflection for the marked Euler probe

The raw protocol has variable macro lengths, so ordinary reflexive-transitive
reachability does not by itself identify the first canonical endpoint.  This
file isolates the exact invariant needed for reflection: a positive raw path
whose endpoint is canonical and whose proper positive prefixes are not.

The generic segmentation theorem below is independent of the concrete
protocol lengths.  For a right-unique raw relation, designated first returns
compose to reflect every canonical-to-canonical raw run into a run of the
represented macro relation.
-/

namespace GraphWalking

open Relation
open FunctionalGraphReversibleTraversal

universe uRaw uCanonical

namespace MarkedEulerProbe

/-! ## Exact-length paths -/

/-- A path with an explicit number of relation edges.  The head-oriented
presentation makes it convenient to split a deterministic path after a
known positive macro prefix. -/
public inductive ExactSteps {Raw : Type uRaw}
    (relation : Raw -> Raw -> Prop) : Nat -> Raw -> Raw -> Prop
  | zero (source : Raw) : ExactSteps relation 0 source source
  | succ {steps : Nat} {source middle target : Raw}
      (head : relation source middle)
      (tail : ExactSteps relation steps middle target) :
      ExactSteps relation (steps + 1) source target

namespace ExactSteps

variable {Raw : Type uRaw} {relation : Raw -> Raw -> Prop}

@[simp]
public theorem zero_iff {source target : Raw} :
    ExactSteps relation 0 source target <-> source = target := by
  constructor
  · intro path
    cases path
    rfl
  · rintro rfl
    exact .zero source

/-- Forgetting the exact length gives ordinary reflexive-transitive
reachability. -/
public theorem to_reflTransGen {steps : Nat} {source target : Raw}
    (path : ExactSteps relation steps source target) :
    ReflTransGen relation source target := by
  induction path with
  | zero => exact .refl
  | succ head _ ih => exact ih.head head

/-- Every finite reflexive-transitive path has some exact length. -/
public theorem exists_of_reflTransGen {source target : Raw}
    (path : ReflTransGen relation source target) :
    exists steps, ExactSteps relation steps source target := by
  induction path using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .zero target⟩
  | @head source middle head tail ih =>
      obtain ⟨steps, exactTail⟩ := ih
      exact ⟨steps + 1, .succ head exactTail⟩

/-- Concatenate exact paths. -/
public theorem append {leftSteps rightSteps : Nat}
    {source middle target : Raw}
    (left : ExactSteps relation leftSteps source middle)
    (right : ExactSteps relation rightSteps middle target) :
    ExactSteps relation (rightSteps + leftSteps) source target := by
  induction left with
  | zero => simpa using right
  | @succ steps source next middle head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ExactSteps.succ head (ih right))

/-- Split an exact path after any bounded prefix length. -/
public theorem split {steps cut : Nat} {source target : Raw}
    (path : ExactSteps relation steps source target)
    (hcut : cut <= steps) :
    exists middle,
      ExactSteps relation cut source middle ∧
      ExactSteps relation (steps - cut) middle target := by
  induction cut generalizing steps source with
  | zero => exact ⟨source, .zero source, by simpa using path⟩
  | succ cut ih =>
      cases path with
      | zero => omega
      | @succ tailSteps source next target head tail =>
          have hle : cut <= tailSteps := by omega
          obtain ⟨middle, left, right⟩ := ih tail hle
          refine ⟨middle, ?_, ?_⟩
          · simpa [Nat.add_comm] using ExactSteps.succ head left
          · simpa [Nat.add_comm] using right

/-- Right uniqueness of one edge lifts to paths having the same exact
length. -/
public theorem target_eq_of_rightUnique
    (hright : Relator.RightUnique relation)
    {steps : Nat} {source leftTarget rightTarget : Raw}
    (left : ExactSteps relation steps source leftTarget)
    (right : ExactSteps relation steps source rightTarget) :
    leftTarget = rightTarget := by
  induction left generalizing rightTarget with
  | zero =>
      exact zero_iff.mp right
  | @succ steps source leftMiddle leftTarget leftHead leftTail ih =>
      cases right with
      | @succ _ _ rightMiddle rightTarget rightHead rightTail =>
          have hmiddle : leftMiddle = rightMiddle :=
            hright leftHead rightHead
          subst rightMiddle
          exact ih rightTail

/-- In a right-unique relation, a shorter exact path is the unique prefix of
a longer one. -/
public theorem suffix_of_rightUnique
    (hright : Relator.RightUnique relation)
    {prefixSteps totalSteps : Nat} {source prefixTarget target : Raw}
    (initial : ExactSteps relation prefixSteps source prefixTarget)
    (total : ExactSteps relation totalSteps source target)
    (hle : prefixSteps <= totalSteps) :
    ExactSteps relation (totalSteps - prefixSteps) prefixTarget target := by
  obtain ⟨middle, totalPrefix, suffix⟩ := split total hle
  have heq : prefixTarget = middle :=
    target_eq_of_rightUnique hright initial totalPrefix
  simpa [heq] using suffix

end ExactSteps

/-! ## First canonical returns and generic segmentation -/

/-- A positive path to a canonical target that encounters no canonical state
at a proper positive prefix.  The source may itself be canonical. -/
@[expose]
public def FirstCanonicalReturn {Raw : Type uRaw}
    (relation : Raw -> Raw -> Prop) (Canonical : Raw -> Prop)
    (source target : Raw) : Prop :=
  Canonical target ∧
    exists steps,
      0 < steps ∧
      ExactSteps relation steps source target ∧
      forall cut middle,
        0 < cut -> cut < steps ->
        ExactSteps relation cut source middle ->
        ¬ Canonical middle

public theorem FirstCanonicalReturn.transGen
    {Raw : Type uRaw} {relation : Raw -> Raw -> Prop}
    {Canonical : Raw -> Prop} {source target : Raw}
    (hreturn : FirstCanonicalReturn relation Canonical source target) :
    TransGen relation source target := by
  obtain ⟨_, steps, hpositive, path, _⟩ := hreturn
  cases steps with
  | zero => omega
  | succ steps =>
      cases path with
      | @succ _ _ middle target head tail =>
          exact TransGen.head' head tail.to_reflTransGen

/-- A single edge into a canonical state is a first canonical return. -/
public theorem FirstCanonicalReturn.of_step
    {Raw : Type uRaw} {relation : Raw -> Raw -> Prop}
    {Canonical : Raw -> Prop} {source target : Raw}
    (htarget : Canonical target) (hstep : relation source target) :
    FirstCanonicalReturn relation Canonical source target := by
  refine ⟨htarget, 1, by omega, ?_, ?_⟩
  · exact .succ hstep (.zero target)
  · intro cut middle hpositive hproper _
    omega

/-- Prepending one edge whose landing is noncanonical preserves the
first-return property.  This packages the protocol chains from their final
edge backwards, without depending on a fixed macro length. -/
public theorem FirstCanonicalReturn.prepend
    {Raw : Type uRaw} {relation : Raw -> Raw -> Prop}
    {Canonical : Raw -> Prop}
    (hright : Relator.RightUnique relation)
    {source middle target : Raw}
    (hstep : relation source middle)
    (hmiddle : ¬ Canonical middle)
    (hreturn : FirstCanonicalReturn relation Canonical middle target) :
    FirstCanonicalReturn relation Canonical source target := by
  obtain ⟨htarget, steps, hpositive, path, hinterior⟩ := hreturn
  refine ⟨htarget, steps + 1, by omega, .succ hstep path, ?_⟩
  intro cut point hcutPositive hcutProper cutPath
  cases cut with
  | zero => omega
  | succ remaining =>
      cases cutPath with
      | @succ _ _ reached point firstStep rest =>
          have hreached : reached = middle := hright firstStep hstep
          subst reached
          by_cases hzero : remaining = 0
          · subst remaining
            have hpoint : middle = point := ExactSteps.zero_iff.mp rest
            simpa [← hpoint] using hmiddle
          · exact hinterior remaining point (Nat.pos_of_ne_zero hzero)
              (by omega) rest

/-- A designated first canonical return is a prefix of every positive path
from the same source to any canonical endpoint. -/
public theorem FirstCanonicalReturn.suffix_of_exactSteps
    {Raw : Type uRaw} {relation : Raw -> Raw -> Prop}
    {Canonical : Raw -> Prop}
    (hright : Relator.RightUnique relation)
    {source first target : Raw}
    (hreturn : FirstCanonicalReturn relation Canonical source first)
    {totalSteps : Nat} (hpositive : 0 < totalSteps)
    (total : ExactSteps relation totalSteps source target)
    (htarget : Canonical target) :
    exists firstSteps,
      0 < firstSteps ∧ firstSteps <= totalSteps ∧
      ExactSteps relation (totalSteps - firstSteps) first target := by
  obtain ⟨_, firstSteps, hfirstPositive, firstPath, hinterior⟩ := hreturn
  have hle : firstSteps <= totalSteps := by
    by_contra hnot
    have hlt : totalSteps < firstSteps := by omega
    have hnotCanonical := hinterior totalSteps target hpositive hlt total
    exact hnotCanonical htarget
  exact ⟨firstSteps, hfirstPositive, hle,
    ExactSteps.suffix_of_rightUnique hright firstPath total hle⟩

/-- Exact-length segmentation to an arbitrary raw canonical endpoint.

Besides projecting the run, this theorem proves that the endpoint is in the
image of `encode`.  This is the form needed for raw acceptance: the raw accept
predicate exposes a canonical control core, but does not itself state that
the restored tape is an encoded plain tape. -/
public theorem exactSteps_exists_encoded_project_of_firstCanonicalReturns
    {Raw : Type uRaw} {CanonicalState : Type uCanonical}
    (relation : Raw -> Raw -> Prop)
    (Canonical : Raw -> Prop)
    (encode : CanonicalState -> Raw)
    (project : CanonicalState -> CanonicalState -> Prop)
    (Good : CanonicalState -> Prop)
    (hright : Relator.RightUnique relation)
    (hfirst : forall source, Good source ->
      exists target,
        Good target ∧ project source target ∧
        FirstCanonicalReturn relation Canonical
          (encode source) (encode target))
    {steps : Nat} {source : CanonicalState} {rawTarget : Raw}
    (hgood : Good source)
    (rawReach : ExactSteps relation steps (encode source) rawTarget)
    (htarget : Canonical rawTarget) :
    exists target,
      rawTarget = encode target ∧ ReflTransGen project source target := by
  induction steps using Nat.strong_induction_on generalizing source with
  | h steps ih =>
      by_cases hzero : steps = 0
      · subst steps
        exact ⟨source, (ExactSteps.zero_iff.mp rawReach).symm,
          ReflTransGen.refl⟩
      · have hpositive : 0 < steps := Nat.pos_of_ne_zero hzero
        obtain ⟨next, hnextGood, hproject, hreturn⟩ := hfirst source hgood
        obtain ⟨firstSteps, hfirstPositive, hle, suffix⟩ :=
          hreturn.suffix_of_exactSteps hright hpositive rawReach htarget
        have hsmaller : steps - firstSteps < steps := by omega
        obtain ⟨target, htargetEncode, htail⟩ :=
          ih (steps - firstSteps) hsmaller hnextGood suffix
        exact ⟨target, htargetEncode,
          (ReflTransGen.single hproject).trans htail⟩

/-- Reflexive-transitive segmentation to an arbitrary raw canonical
endpoint. -/
public theorem reflTransGen_exists_encoded_project_of_firstCanonicalReturns
    {Raw : Type uRaw} {CanonicalState : Type uCanonical}
    (relation : Raw -> Raw -> Prop)
    (Canonical : Raw -> Prop)
    (encode : CanonicalState -> Raw)
    (project : CanonicalState -> CanonicalState -> Prop)
    (Good : CanonicalState -> Prop)
    (hright : Relator.RightUnique relation)
    (hfirst : forall source, Good source ->
      exists target,
        Good target ∧ project source target ∧
        FirstCanonicalReturn relation Canonical
          (encode source) (encode target))
    {source : CanonicalState} {rawTarget : Raw}
    (hgood : Good source)
    (rawReach : ReflTransGen relation (encode source) rawTarget)
    (htarget : Canonical rawTarget) :
    exists target,
      rawTarget = encode target ∧ ReflTransGen project source target := by
  obtain ⟨steps, exactRawReach⟩ :=
    ExactSteps.exists_of_reflTransGen rawReach
  exact exactSteps_exists_encoded_project_of_firstCanonicalReturns
    relation Canonical encode project Good hright hfirst hgood
    exactRawReach htarget

/-- Exact-length whole-run segmentation through designated first canonical
returns.

`encode` may retain implementation data such as a phase bit, while `project`
forgets it.  Each first raw return supplies one represented macro edge.  The
conclusion therefore lives entirely in the undoubled projected system. -/
public theorem exactSteps_project_of_firstCanonicalReturns
    {Raw : Type uRaw} {CanonicalState : Type uCanonical}
    (relation : Raw -> Raw -> Prop)
    (Canonical : Raw -> Prop)
    (encode : CanonicalState -> Raw)
    (project : CanonicalState -> CanonicalState -> Prop)
    (Good : CanonicalState -> Prop)
    (hright : Relator.RightUnique relation)
    (hcanonical : forall state, Canonical (encode state))
    (hencode : Function.Injective encode)
    (hfirst : forall source, Good source ->
      exists target,
        Good target ∧ project source target ∧
        FirstCanonicalReturn relation Canonical
          (encode source) (encode target))
    {steps : Nat} {source target : CanonicalState}
    (hgood : Good source)
    (rawReach : ExactSteps relation steps (encode source) (encode target)) :
    ReflTransGen project source target := by
  induction steps using Nat.strong_induction_on generalizing source with
  | h steps ih =>
      by_cases hzero : steps = 0
      · subst steps
        have heq : encode source = encode target :=
          ExactSteps.zero_iff.mp rawReach
        exact (hencode heq) ▸ ReflTransGen.refl
      · have hpositive : 0 < steps := Nat.pos_of_ne_zero hzero
        obtain ⟨next, hnextGood, hproject, hreturn⟩ := hfirst source hgood
        obtain ⟨firstSteps, hfirstPositive, hle, suffix⟩ :=
          hreturn.suffix_of_exactSteps hright hpositive rawReach
            (hcanonical target)
        have hsmaller : steps - firstSteps < steps := by
          omega
        exact (ReflTransGen.single hproject).trans
          (ih (steps - firstSteps) hsmaller hnextGood suffix)

/-- Whole-run segmentation through designated first canonical returns. -/
public theorem reflTransGen_project_of_firstCanonicalReturns
    {Raw : Type uRaw} {CanonicalState : Type uCanonical}
    (relation : Raw -> Raw -> Prop)
    (Canonical : Raw -> Prop)
    (encode : CanonicalState -> Raw)
    (project : CanonicalState -> CanonicalState -> Prop)
    (Good : CanonicalState -> Prop)
    (hright : Relator.RightUnique relation)
    (hcanonical : forall state, Canonical (encode state))
    (hencode : Function.Injective encode)
    (hfirst : forall source, Good source ->
      exists target,
        Good target ∧ project source target ∧
        FirstCanonicalReturn relation Canonical
          (encode source) (encode target))
    {source target : CanonicalState}
    (hgood : Good source)
    (rawReach : ReflTransGen relation (encode source) (encode target)) :
    ReflTransGen project source target := by
  obtain ⟨steps, exactRawReach⟩ :=
    ExactSteps.exists_of_reflTransGen rawReach
  exact exactSteps_project_of_firstCanonicalReturns
    relation Canonical encode project Good hright hcanonical hencode hfirst
    hgood exactRawReach

/-! ## Concrete canonical states and protocol stages -/

universe uTerminal uWork uState

/-- Raw configurations that are exactly encodings of a phase and an
undoubled local port.  Merely having a `canonical` control constructor is not
enough: all tape cells must also be ordinary encoded data. -/
@[expose]
public def IsEncodedCanonical
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n) : Prop :=
  exists phase port, configuration = encodePortCfg phase port

/-- The accepting control shape of the raw machine.  Unlike
`IsEncodedCanonical`, this predicate deliberately says nothing about the tape;
whole-run segmentation will prove that a reachable such endpoint is encoded. -/
@[expose]
public def HasCanonicalCore
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n) : Prop :=
  exists endpoint slot,
    configuration.state.core = .canonical endpoint slot

public theorem isEncodedCanonical_encodePortCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)) :
    IsEncodedCanonical (encodePortCfg phase port) :=
  ⟨phase, port, rfl⟩

public theorem hasCanonicalCore_encodePortCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)) :
    HasCanonicalCore (encodePortCfg phase port) :=
  ⟨port.1.1, port.2, rfl⟩

/-- Canonical encoding is injective jointly in the phase and represented
port. -/
public theorem encodePortCfg_pair_injective
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat} :
    Function.Injective
      (fun state : Bool × LocalPort.Port (LiftState T Gamma Q)
          (DLBA.BoundedTape (PlainCode T Gamma) n) =>
        encodePortCfg state.1 state.2) := by
  intro left right heq
  have hdecoded := congrArg decodePortCfg heq
  simpa using hdecoded

/-- Remaining control-stage depth before the protocol can next enter a
canonical core.  A raw step from a noncanonical core strictly decreases this
number. -/
@[expose]
public def protocolRank
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} :
    CoreState T Gamma Q -> Nat
  | .canonical _ _ => 0
  | .dispatch _ _ => 6
  | .outgoingAtNeighbour _ => 5
  | .outgoingAtDeparture _ => 4
  | .outgoingRestoreNeighbour _ => 3
  | .outgoingValidateAtDeparture _ => 2
  | .incomingInspect _ => 4
  | .incomingValidAtTarget _ => 2
  | .incomingValidFinish _ => 1
  | .incomingInvalidAtTarget _ _ => 3
  | .incomingInvalidAtSource _ _ => 2
  | .incomingReturnAtTarget _ => 1
  | .stationaryOutgoingPending _ => 1
  | .stationaryIncomingPending _ => 1

@[simp]
public theorem protocolRank_eq_zero_iff
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    (core : CoreState T Gamma Q) :
    protocolRank core = 0 <->
      exists endpoint slot, core = .canonical endpoint slot := by
  cases core <;> simp [protocolRank]

public theorem protocolRank_eq_zero_iff_hasCanonicalCore
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n) :
    protocolRank configuration.state.core = 0 <->
      HasCanonicalCore configuration := by
  exact protocolRank_eq_zero_iff configuration.state.core

public theorem not_hasCanonicalCore_of_protocolRank_ne_zero
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n)
    (hrank : protocolRank configuration.state.core ≠ 0) :
    ¬ HasCanonicalCore configuration := by
  intro hcanonical
  exact hrank ((protocolRank_eq_zero_iff_hasCanonicalCore configuration).2
    hcanonical)

/-- The core-only predicate exported with the explicit staged witnesses is
exactly strong enough to exclude a canonical return. -/
public theorem NoncanonicalCore.not_hasCanonicalCore
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    {configuration : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hnoncanonical : NoncanonicalCore configuration) :
    ¬ HasCanonicalCore configuration := by
  rcases configuration with ⟨⟨phase, core⟩, tape⟩
  cases core <;>
    simp [NoncanonicalCore, HasCanonicalCore] at hnoncanonical ⊢

/-- Constructor-level stage classification: after leaving a canonical core,
every individual raw step strictly decreases the protocol rank until the next
canonical core is reached. -/
public theorem protocolRank_lt_of_rawTransitionCase
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {phase : Bool} {core : CoreState T Gamma Q}
    {read written : Alphabet T Gamma Q} {next : State T Gamma Q}
    {direction : DLBA.Dir}
    (hcase : RawTransitionCase machine phase core read
      (next, written, direction))
    (hnoncanonical : protocolRank core ≠ 0) :
    protocolRank next.core < protocolRank core := by
  cases hcase <;> simp [protocolRank, nextState] at hnoncanonical ⊢

public theorem protocolRank_lt_of_step_of_ne_zero
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {source target : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) source target)
    (hnoncanonical : protocolRank source.state.core ≠ 0) :
    protocolRank target.state.core < protocolRank source.state.core := by
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  rcases source with ⟨⟨phase, core⟩, tape⟩
  have hcase :=
    (mem_transition_iff_rawTransitionCase machine phase core tape.read
      (next, written, direction)).mp hmem
  exact protocolRank_lt_of_rawTransitionCase machine hcase hnoncanonical

/-- A convenient constructor for first returns when an explicit exact macro
path and its noncanonical proper-prefix invariant are available. -/
public theorem firstCanonicalReturn_of_exactSteps
    {Raw : Type uRaw} {relation : Raw -> Raw -> Prop}
    {Canonical : Raw -> Prop} {source target : Raw} {steps : Nat}
    (htarget : Canonical target) (hpositive : 0 < steps)
    (path : ExactSteps relation steps source target)
    (hinterior : forall cut middle,
      0 < cut -> cut < steps ->
      ExactSteps relation cut source middle -> ¬ Canonical middle) :
    FirstCanonicalReturn relation Canonical source target :=
  ⟨htarget, steps, hpositive, path, hinterior⟩

/-! ## First-return packages for the explicit dispatch paths -/

public theorem firstCanonicalReturn_dispatch_stationary_outgoing
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint target : LiftState T Gamma Q)
    (old written : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (htransition : (walker machine).transition endpoint tape.read =
      some (target, .stationary old written)) :
    FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      (encodePortCfg phase
        (((target, tape.write written), .incoming endpoint))) := by
  obtain ⟨middle, hfirst, hsecond, hmiddle⟩ :=
    exists_steps_dispatch_stationary_outgoing machine phase endpoint target
      old written tape htransition
  exact (FirstCanonicalReturn.of_step
      (hasCanonicalCore_encodePortCfg phase
        (((target, tape.write written), .incoming endpoint))) hsecond).prepend
    (rawMachine_step_rightUnique machine) hfirst hmiddle.not_hasCanonicalCore

public theorem firstCanonicalReturn_dispatch_stationary_incoming
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .stationary old written)
    (hread : tape.read = written)
    (henabled : (Edge.ofIncoming endpoint source).Enabled machine) :
    FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape tape))
      (encodePortCfg phase (((source, tape.write old), .outgoing))) := by
  obtain ⟨middle, hfirst, hsecond, hmiddle⟩ :=
    exists_steps_dispatch_stationary_incoming machine phase endpoint source
      old written tape hdirection hread henabled
  exact (FirstCanonicalReturn.of_step
      (hasCanonicalCore_encodePortCfg phase
        (((source, tape.write old), .outgoing))) hsecond).prepend
    (rawMachine_step_rightUnique machine) hfirst hmiddle.not_hasCanonicalCore

public theorem firstCanonicalReturn_dispatch_departure_outgoing
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint target : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape)
    (htransition : (walker machine).transition endpoint tape.read =
      some (target, .departure old written travel))
    (hallows : tape.read.boundary.allows travel = true) :
    FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      (encodePortCfg phase
        (((target, (tape.write written).moveHead travel.toDir),
          .incoming endpoint))) := by
  obtain ⟨first, second, third, fourth, fifth,
      hfirst, hsecond, hthird, hfourth, hfifth, hsixth,
      hfirstCore, hsecondCore, hthirdCore, hfourthCore, hfifthCore⟩ :=
    exists_steps_dispatch_departure_outgoing machine phase endpoint target
      old written travel tape hwell htransition hallows
  exact (((((FirstCanonicalReturn.of_step
      (hasCanonicalCore_encodePortCfg phase
        (((target, (tape.write written).moveHead travel.toDir),
          .incoming endpoint))) hsixth).prepend
      (rawMachine_step_rightUnique machine) hfifth
        hfifthCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hfourth
        hfourthCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hthird
        hthirdCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hsecond
        hsecondCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hfirst
        hfirstCore.not_hasCanonicalCore

public theorem firstCanonicalReturn_dispatch_departure_incoming_valid
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (targetTape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded targetTape)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hallows : targetTape.read.boundary.allows travel.reverse = true)
    (hvalid : incomingCandidateCode travel targetTape = written ∧
      (Edge.ofIncoming endpoint source).Enabled machine ∧
      (incomingCandidateCode travel targetTape).boundary.allows travel = true)
    (holdAllows : old.boundary.allows travel = true) :
    FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape targetTape))
      (encodePortCfg phase
        (((source, (targetTape.moveHead travel.reverse.toDir).write old),
          .outgoing))) := by
  obtain ⟨first, second, third, hfirst, hsecond, hthird, hfourth,
      hfirstCore, hsecondCore, hthirdCore⟩ :=
    exists_steps_dispatch_departure_incoming_valid machine phase endpoint source
      old written travel targetTape hwell hdirection hallows hvalid holdAllows
  exact (((FirstCanonicalReturn.of_step
      (hasCanonicalCore_encodePortCfg phase
        (((source, (targetTape.moveHead travel.reverse.toDir).write old),
          .outgoing))) hfourth).prepend
      (rawMachine_step_rightUnique machine) hthird
        hthirdCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hsecond
        hsecondCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hfirst
        hfirstCore.not_hasCanonicalCore

public theorem firstCanonicalReturn_dispatch_departure_incoming_invalid
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (targetTape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded targetTape)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hallows : targetTape.read.boundary.allows travel.reverse = true)
    (hinvalid : ¬(incomingCandidateCode travel targetTape = written ∧
      (Edge.ofIncoming endpoint source).Enabled machine ∧
      (incomingCandidateCode travel targetTape).boundary.allows travel = true)) :
    FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape targetTape))
      (encodePortCfg (!phase) (((endpoint, targetTape), .incoming source))) := by
  obtain ⟨first, second, third, fourth,
      hfirst, hsecond, hthird, hfourth, hfifth,
      hfirstCore, hsecondCore, hthirdCore, hfourthCore⟩ :=
    exists_steps_dispatch_departure_incoming_invalid machine phase endpoint source
      old written travel targetTape hwell hdirection hallows hinvalid
  exact ((((FirstCanonicalReturn.of_step
      (hasCanonicalCore_encodePortCfg (!phase)
        (((endpoint, targetTape), .incoming source))) hfifth).prepend
      (rawMachine_step_rightUnique machine) hfourth
        hfourthCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hthird
        hthirdCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hsecond
        hsecondCore.not_hasCanonicalCore).prepend
      (rawMachine_step_rightUnique machine) hfirst
        hfirstCore.not_hasCanonicalCore

/-! ## Canonical-source invariant -/

/-- Boundary correctness carried by a phase-tagged canonical port. -/
@[expose]
public def GoodPortState
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (state : Bool × LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)) : Prop :=
  WellBoundaryCoded state.2.1.2

/-- One undoubled Euler step preserves the canonical-source invariant. -/
public theorem goodPortState_euler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase finalPhase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hgood : GoodPortState (phase, port)) :
    GoodPortState (finalPhase, (ports machine n).euler port) := by
  change WellBoundaryCoded (((ports machine n).euler port).1.2)
  simpa only [ports, markedPorts] using
    wellBoundaryCoded_euler machine port hgood

/-! ## Semantic assembly of one first return -/

public theorem exists_phase_firstCanonicalReturn_dispatch_outgoing_swap
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint : LiftState T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) :
    exists finalPhase,
      FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
        (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
        (encodePortCfg finalPhase
          ((ports machine n).swap (((endpoint, tape), .outgoing)))) := by
  cases htransition :
      (walker machine).transition endpoint (tape.contents tape.head) with
  | none =>
      have hstep := step_dispatch_outgoing_none machine phase endpoint tape htransition
      refine ⟨!phase, ?_⟩
      simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
        Machine.next, htransition] using
        (FirstCanonicalReturn.of_step
          (hasCanonicalCore_encodePortCfg (!phase)
            (((endpoint, tape), .outgoing))) hstep)
  | some output =>
      rcases output with ⟨target, direction⟩
      cases direction with
      | stationary old written =>
          have hreturn := firstCanonicalReturn_dispatch_stationary_outgoing
            machine phase endpoint target old written tape htransition
          refine ⟨phase, ?_⟩
          have hold : old = tape.read := by
            simpa using edge_old_eq_of_walker_transition machine htransition
          simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
            Machine.next, htransition, BoundedTapeMemory.graph,
            BoundedTapeMemory.move, DLBA.BoundedTape.read, hold] using hreturn
      | departure old written travel =>
          have hold : old = tape.read := by
            simpa using edge_old_eq_of_walker_transition machine htransition
          subst old
          let edge : Edge T Gamma Q :=
            { source := endpoint, target := target,
              direction := .departure tape.read written travel }
          have henabled : edge.Enabled machine := by
            simp [Edge.Enabled, Edge.old, edge, htransition]
          have hallows : tape.read.boundary.allows travel = true := by
            simpa [edge, Edge.old] using
              edge.old_boundary_allows_of_enabled_departure machine henabled
                tape.read written travel (by rfl)
          obtain ⟨targetHead, hnext⟩ :=
            (allows_iff_exists_nextHead tape hwell travel).mp hallows
          have hmove :
              BoundedTapeMemory.move
                  (.departure tape.read written travel) tape =
                some ((tape.write written).moveHead travel.toDir) := by
            simpa only [BoundedTapeMemory.graph_move] using
              BoundedTapeMemory.move_departure_eq_write_moveHead
                tape written travel hnext
          change BoundedTapeMemory.move
              (.departure (tape.contents tape.head) written travel) tape =
            some ((tape.write written).moveHead travel.toDir) at hmove
          have hnextCfg :
              (walker machine).next
                  (BoundedTapeMemory.graph (PlainCode T Gamma) n)
                  (endpoint, tape) =
                some (target, (tape.write written).moveHead travel.toDir) := by
            simp [Machine.next, htransition, hmove]
          have hreturn := firstCanonicalReturn_dispatch_departure_outgoing
            machine phase endpoint target tape.read written travel tape hwell
              htransition hallows
          refine ⟨phase, ?_⟩
          simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
            hnextCfg] using hreturn
      | arrival old written travel =>
          exact (walker_transition_ne_arrival machine endpoint target tape.read
            old written travel htransition).elim

public theorem exists_phase_firstCanonicalReturn_dispatch_incoming_swap
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) :
    exists finalPhase,
      FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
        (protocolCfg phase (.dispatch endpoint (.incoming source))
          (encodeTape tape))
        (encodePortCfg finalPhase
          ((ports machine n).swap (((endpoint, tape), .incoming source)))) := by
  let edge : Edge T Gamma Q := Edge.ofIncoming endpoint source
  cases hdirection : edge.direction with
  | stationary old written =>
      have hsource := incomingSource_stationary_eq machine endpoint source
        old written tape (by simpa [edge] using hdirection)
      by_cases hvalid : tape.read = written ∧ edge.Enabled machine
      · rw [if_pos (by simpa [edge] using hvalid)] at hsource
        have hreturn := firstCanonicalReturn_dispatch_stationary_incoming
          machine phase endpoint source old written tape
            (by simpa [edge] using hdirection) hvalid.1
            (by simpa [edge] using hvalid.2)
        refine ⟨phase, ?_⟩
        simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
          hsource] using hreturn
      · rw [if_neg (by simpa [edge] using hvalid)] at hsource
        have hstep := step_dispatch_stationary_incoming_fixed machine phase
          endpoint source old written tape (by simpa [edge] using hdirection)
          (by simpa [edge] using hvalid)
        refine ⟨!phase, ?_⟩
        simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
          hsource] using
          (FirstCanonicalReturn.of_step
            (hasCanonicalCore_encodePortCfg (!phase)
              (((endpoint, tape), .incoming source))) hstep)
  | departure old written travel =>
      cases hallows : tape.read.boundary.allows travel.reverse with
      | false =>
          have hsource := incomingSource_departure_blocked_eq_none machine
            endpoint source old written travel tape hwell
              (by simpa [edge] using hdirection) hallows
          have hstep := step_dispatch_incoming_departure_blocked machine phase
            endpoint source old written travel tape
              (by simpa [edge] using hdirection) hallows
          refine ⟨!phase, ?_⟩
          simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
            hsource] using
            (FirstCanonicalReturn.of_step
              (hasCanonicalCore_encodePortCfg (!phase)
                (((endpoint, tape), .incoming source))) hstep)
      | true =>
          have hsource := incomingSource_departure_allowed_eq machine
            endpoint source old written travel tape hwell
              (by simpa [edge] using hdirection) hallows
          have hcandidateAllows :
              (incomingCandidateCode travel tape).boundary.allows travel = true := by
            have hreverse := neighbour_allows_reverse travel.reverse tape hwell hallows
            simpa [incomingCandidateCode, outgoingNeighbourCode] using hreverse
          by_cases hvalid :
              incomingCandidateCode travel tape = written ∧ edge.Enabled machine
          · rw [if_pos (by simpa [edge] using hvalid)] at hsource
            have holdAllows : old.boundary.allows travel = true := by
              have hold := edge.old_boundary_allows_of_enabled_departure
                machine hvalid.2 old written travel hdirection
              simpa [edge, Edge.old, hdirection] using hold
            have hreturn :=
              firstCanonicalReturn_dispatch_departure_incoming_valid
                machine phase endpoint source old written travel tape hwell
                (by simpa [edge] using hdirection) hallows
                ⟨hvalid.1, by simpa [edge] using hvalid.2, hcandidateAllows⟩
                holdAllows
            refine ⟨phase, ?_⟩
            simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
              hsource] using hreturn
          · rw [if_neg (by simpa [edge] using hvalid)] at hsource
            have hinvalid : ¬(incomingCandidateCode travel tape = written ∧
                (Edge.ofIncoming endpoint source).Enabled machine ∧
                (incomingCandidateCode travel tape).boundary.allows travel = true) := by
              intro hall
              apply hvalid
              exact ⟨hall.1, by simpa [edge] using hall.2.1⟩
            have hreturn :=
              firstCanonicalReturn_dispatch_departure_incoming_invalid
                machine phase endpoint source old written travel tape hwell
                (by simpa [edge] using hdirection) hallows hinvalid
            refine ⟨!phase, ?_⟩
            simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
              hsource] using hreturn
  | arrival old written travel =>
      have hsource := incomingSource_arrival_eq_none machine endpoint source
        old written travel tape (by simpa [edge] using hdirection)
      have hstep := step_dispatch_incoming_arrival machine phase endpoint source
        old written travel tape (by simpa [edge] using hdirection)
      refine ⟨!phase, ?_⟩
      simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
        hsource] using
        (FirstCanonicalReturn.of_step
          (hasCanonicalCore_encodePortCfg (!phase)
            (((endpoint, tape), .incoming source))) hstep)

/-- Every dispatch branch returns for the first time at its exact semantic
swap port. -/
public theorem exists_phase_firstCanonicalReturn_dispatch_swap
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint : LiftState T Gamma Q) (slot : Slot T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) :
    exists finalPhase,
      FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
        (protocolCfg phase (.dispatch endpoint slot) (encodeTape tape))
        (encodePortCfg finalPhase
          ((ports machine n).swap (((endpoint, tape), slot)))) := by
  cases slot with
  | anchor =>
      have hstep := step_dispatch_anchor machine phase endpoint tape
      refine ⟨!phase, ?_⟩
      simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun] using
        (FirstCanonicalReturn.of_step
          (hasCanonicalCore_encodePortCfg (!phase)
            (((endpoint, tape), .anchor))) hstep)
  | outgoing =>
      exact exists_phase_firstCanonicalReturn_dispatch_outgoing_swap
        machine phase endpoint tape hwell
  | incoming source =>
      exact exists_phase_firstCanonicalReturn_dispatch_incoming_swap
        machine phase endpoint source tape hwell

/-- A complete raw macro returns for the first time at one undoubled Euler
successor. -/
public theorem exists_phase_firstCanonicalReturn_euler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded port.1.2) :
    exists finalPhase,
      FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
        (encodePortCfg phase port)
        (encodePortCfg finalPhase ((ports machine n).euler port)) := by
  rcases port with ⟨⟨endpoint, tape⟩, slot⟩
  have hrotate := step_rotate_to_dispatch machine phase endpoint slot tape
  obtain ⟨finalPhase, hdispatch⟩ :=
    exists_phase_firstCanonicalReturn_dispatch_swap machine (!phase) endpoint
      (rotateSlot slot) tape hwell
  have hdispatchCore : NoncanonicalCore
      (protocolCfg (!phase) (.dispatch endpoint (rotateSlot slot))
        (encodeTape tape)) := by
    simp
  refine ⟨finalPhase, ?_⟩
  simpa [PortSystem.euler, ports, LocalPort.ofMachine, LocalPort.rotate,
    rotateSlot] using
      hdispatch.prepend (rawMachine_step_rightUnique machine) hrotate
        hdispatchCore.not_hasCanonicalCore

/-- The concrete first-return package consumed by whole-run segmentation. -/
public theorem euler_firstCanonicalReturns
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    forall state : Bool × LocalPort.Port (LiftState T Gamma Q)
        (DLBA.BoundedTape (PlainCode T Gamma) n),
      GoodPortState state ->
      exists target,
        GoodPortState target ∧
        (ports machine n).EulerEdge state.2 target.2 ∧
        FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
          (encodePortCfg state.1 state.2)
          (encodePortCfg target.1 target.2) := by
  rintro ⟨phase, port⟩ hgood
  obtain ⟨finalPhase, hreturn⟩ :=
    exists_phase_firstCanonicalReturn_euler machine phase port hgood
  refine ⟨(finalPhase, (ports machine n).euler port), ?_, ?_, hreturn⟩
  · exact goodPortState_euler machine phase finalPhase port hgood
  · change (ports machine n).euler port = (ports machine n).euler port
    rfl

/-! ## Concrete whole-run reflection interface -/

/-- Once the one-macro first-return fact has been established, every raw run
from a good encoded port to a canonical control state ends at an encoded port
reachable in the *undoubled* Euler system.  In particular, this theorem also
rules out malformed canonical accepting endpoints. -/
public theorem rawReaches_canonical_reflects_euler_of_firstReturns
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (hfirst : forall state : Bool × LocalPort.Port (LiftState T Gamma Q)
        (DLBA.BoundedTape (PlainCode T Gamma) n),
      GoodPortState state ->
      exists target,
        GoodPortState target ∧
        (ports machine n).EulerEdge state.2 target.2 ∧
        FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
          (encodePortCfg state.1 state.2)
          (encodePortCfg target.1 target.2))
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hgood : WellBoundaryCoded port.1.2)
    {rawTarget : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hreach : LBA.Reaches (rawMachine machine)
      (encodePortCfg phase port) rawTarget)
    (hcanonical : HasCanonicalCore rawTarget) :
    exists finalPhase finish,
      rawTarget = encodePortCfg finalPhase finish ∧
      ReflTransGen (ports machine n).EulerEdge port finish := by
  let encodeState := fun state : Bool × LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n) =>
    encodePortCfg state.1 state.2
  let projectedEdge := fun left right : Bool × LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n) =>
    (ports machine n).EulerEdge left.2 right.2
  have hgoodState : GoodPortState (phase, port) := hgood
  have hreachState : ReflTransGen (LBA.Step (rawMachine machine))
      (encodeState (phase, port)) rawTarget := by
    simpa only [encodeState] using hreach
  obtain ⟨target, htarget, hprojected⟩ :=
    reflTransGen_exists_encoded_project_of_firstCanonicalReturns
      (LBA.Step (rawMachine machine)) HasCanonicalCore encodeState projectedEdge
      GoodPortState (rawMachine_step_rightUnique machine) hfirst hgoodState
      hreachState hcanonical
  refine ⟨target.1, target.2, htarget, ?_⟩
  exact ReflTransGen.lift Prod.snd (fun _ _ hstep => hstep) hprojected

/-- Raw acceptance can hold only at a canonical control core. -/
public theorem hasCanonicalCore_of_rawMachine_accept
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (configuration : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n)
    (haccept : (rawMachine machine).accept configuration.state = true) :
    HasCanonicalCore configuration := by
  rcases configuration with ⟨⟨phase, core⟩, tape⟩
  cases core <;> simp [rawMachine, HasCanonicalCore] at haccept ⊢

@[simp]
public theorem rawMachine_accept_encodePortCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)) :
    (rawMachine machine).accept (encodePortCfg phase port).state =
      machine.accept port.1.1.1 := by
  rfl

/-- Acceptance reflection in its phase-erased form.  Every accepting raw run
from a good canonical source yields an accepting port in the undoubled Euler
orbit. -/
public theorem rawAccepts_reflects_euler_of_firstReturns
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (hfirst : forall state : Bool × LocalPort.Port (LiftState T Gamma Q)
        (DLBA.BoundedTape (PlainCode T Gamma) n),
      GoodPortState state ->
      exists target,
        GoodPortState target ∧
        (ports machine n).EulerEdge state.2 target.2 ∧
        FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
          (encodePortCfg state.1 state.2)
          (encodePortCfg target.1 target.2))
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hgood : WellBoundaryCoded port.1.2)
    (haccept : LBA.Accepts (rawMachine machine) (encodePortCfg phase port)) :
    exists finish,
      ReflTransGen (ports machine n).EulerEdge port finish ∧
      machine.accept finish.1.1.1 = true := by
  obtain ⟨rawTarget, hreach, htargetAccept⟩ := haccept
  have hcanonical :=
    hasCanonicalCore_of_rawMachine_accept machine rawTarget htargetAccept
  obtain ⟨finalPhase, finish, htarget, heuler⟩ :=
    rawReaches_canonical_reflects_euler_of_firstReturns
      machine hfirst phase port hgood hreach hcanonical
  subst rawTarget
  exact ⟨finish, heuler, by simpa using htargetAccept⟩

/-- Every undoubled Euler run lifts to a raw run.  The existential final phase
absorbs the mixed parity of the concrete protocol branches. -/
public theorem exists_phase_rawReaches_of_eulerReaches
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool)
    {source finish : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)}
    (hwell : WellBoundaryCoded source.1.2)
    (heuler : ReflTransGen (ports machine n).EulerEdge source finish) :
    exists finalPhase,
      WellBoundaryCoded finish.1.2 ∧
      LBA.Reaches (rawMachine machine)
        (encodePortCfg phase source) (encodePortCfg finalPhase finish) := by
  induction heuler generalizing phase with
  | refl => exact ⟨phase, hwell, ReflTransGen.refl⟩
  | @tail middle finish hprefix hstep ih =>
      obtain ⟨middlePhase, hmiddleWell, hrawPrefix⟩ := ih phase
      change (ports machine n).euler middle = finish at hstep
      obtain ⟨finalPhase, hrawStep⟩ :=
        exists_phase_reaches_euler machine middlePhase middle hmiddleWell
      have hfinishWell : WellBoundaryCoded finish.1.2 := by
        rw [← hstep]
        exact goodPortState_euler machine middlePhase finalPhase middle hmiddleWell
      rw [hstep] at hrawStep
      exact ⟨finalPhase, hfinishWell, hrawPrefix.trans hrawStep⟩

/-- Completeness of raw acceptance with respect to accepting undoubled Euler
ports. -/
public theorem rawAccepts_of_exists_eulerAccepting
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded port.1.2)
    (haccept : exists finish,
      ReflTransGen (ports machine n).EulerEdge port finish ∧
      machine.accept finish.1.1.1 = true) :
    LBA.Accepts (rawMachine machine) (encodePortCfg phase port) := by
  obtain ⟨finish, heuler, hfinishAccept⟩ := haccept
  obtain ⟨finalPhase, _, hraw⟩ :=
    exists_phase_rawReaches_of_eulerReaches machine phase hwell heuler
  exact ⟨encodePortCfg finalPhase finish, hraw, by simpa using hfinishAccept⟩

/-- Conditional final characterization, awaiting only the concrete
first-return package for one macro.  Both directions otherwise use the actual
raw machine and the undoubled Euler relation. -/
public theorem rawAccepts_iff_exists_eulerAccepting_of_firstReturns
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (hfirst : forall state : Bool × LocalPort.Port (LiftState T Gamma Q)
        (DLBA.BoundedTape (PlainCode T Gamma) n),
      GoodPortState state ->
      exists target,
        GoodPortState target ∧
        (ports machine n).EulerEdge state.2 target.2 ∧
        FirstCanonicalReturn (LBA.Step (rawMachine machine)) HasCanonicalCore
          (encodePortCfg state.1 state.2)
          (encodePortCfg target.1 target.2))
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded port.1.2) :
    LBA.Accepts (rawMachine machine) (encodePortCfg phase port) <->
      exists finish,
        ReflTransGen (ports machine n).EulerEdge port finish ∧
        machine.accept finish.1.1.1 = true := by
  constructor
  · exact rawAccepts_reflects_euler_of_firstReturns
      machine hfirst phase port hwell
  · exact rawAccepts_of_exists_eulerAccepting machine phase port hwell

/-! ## Unconditional reflection and acceptance -/

/-- Every raw reach from a well-coded port to any canonical-core endpoint is
an undoubled Euler reach, and the endpoint tape is necessarily an encoded
plain tape. -/
public theorem rawReaches_canonical_reflects_euler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded port.1.2)
    {rawTarget : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hreach : LBA.Reaches (rawMachine machine)
      (encodePortCfg phase port) rawTarget)
    (hcanonical : HasCanonicalCore rawTarget) :
    exists finalPhase finish,
      rawTarget = encodePortCfg finalPhase finish ∧
      ReflTransGen (ports machine n).EulerEdge port finish := by
  exact rawReaches_canonical_reflects_euler_of_firstReturns
    machine (euler_firstCanonicalReturns machine) phase port hwell
      hreach hcanonical

/-- Canonical-to-canonical raw reach reflects to the exact represented
undoubled ports; both implementation phase bits are erased. -/
public theorem rawReaches_encodePortCfg_reflects_euler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (sourcePhase targetPhase : Bool)
    (source target : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded source.1.2)
    (hreach : LBA.Reaches (rawMachine machine)
      (encodePortCfg sourcePhase source) (encodePortCfg targetPhase target)) :
    ReflTransGen (ports machine n).EulerEdge source target := by
  obtain ⟨finalPhase, finish, hencoded, heuler⟩ :=
    rawReaches_canonical_reflects_euler machine sourcePhase source hwell
      hreach (hasCanonicalCore_encodePortCfg targetPhase target)
  have hpairs : (targetPhase, target) = (finalPhase, finish) :=
    encodePortCfg_pair_injective hencoded
  cases hpairs
  exact heuler

/-- Phase-erased canonical reachability is exactly undoubled Euler
reachability. -/
public theorem exists_phase_rawReaches_iff_eulerReaches
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (sourcePhase : Bool)
    (source target : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded source.1.2) :
    (exists targetPhase,
      LBA.Reaches (rawMachine machine)
        (encodePortCfg sourcePhase source) (encodePortCfg targetPhase target)) <->
      ReflTransGen (ports machine n).EulerEdge source target := by
  constructor
  · rintro ⟨targetPhase, hraw⟩
    exact rawReaches_encodePortCfg_reflects_euler machine sourcePhase
      targetPhase source target hwell hraw
  · intro heuler
    obtain ⟨targetPhase, _, hraw⟩ :=
      exists_phase_rawReaches_of_eulerReaches machine sourcePhase hwell heuler
    exact ⟨targetPhase, hraw⟩

/-- Raw acceptance is exactly reachability of an accepting port in the
undoubled Euler orbit. -/
public theorem rawAccepts_iff_exists_eulerAccepting
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded port.1.2) :
    LBA.Accepts (rawMachine machine) (encodePortCfg phase port) <->
      exists finish,
        ReflTransGen (ports machine n).EulerEdge port finish ∧
        machine.accept finish.1.1.1 = true := by
  exact rawAccepts_iff_exists_eulerAccepting_of_firstReturns
    machine (euler_firstCanonicalReturns machine) phase port hwell

/-- Initial-input form, including the empty word.  The existing exact
initialization equality is quantified over all lists, so no nonempty premise
is introduced here. -/
public theorem rawMachine_accepts_initCfgEnd_iff_exists_eulerAccepting
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) (word : List T) :
    LBA.Accepts (rawMachine machine)
        (LBA.initCfgEnd (rawMachine machine) word) <->
      exists finish,
        ReflTransGen (ports machine (word.length + 1)).EulerEdge
          (initialPort machine word) finish ∧
        machine.accept finish.1.1.1 = true := by
  rw [initCfgEnd_rawMachine_eq_encodePortCfg machine word]
  exact rawAccepts_iff_exists_eulerAccepting machine false
    (initialPort machine word) (plainLoadEnd_wellBoundaryCoded word)

/-- Explicit epsilon specialization of the initial-input characterization. -/
public theorem rawMachine_accepts_initCfgEnd_nil_iff_exists_eulerAccepting
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    LBA.Accepts (rawMachine machine)
        (LBA.initCfgEnd (rawMachine machine) ([] : List T)) <->
      exists finish,
        ReflTransGen (ports machine 1).EulerEdge
          (initialPort machine []) finish ∧
        machine.accept finish.1.1.1 = true := by
  simpa using
    (rawMachine_accepts_initCfgEnd_iff_exists_eulerAccepting machine ([] : List T))

end MarkedEulerProbe

end GraphWalking

end
