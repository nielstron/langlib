module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedCanonical
import Mathlib.Tactic

@[expose]
public section

/-!
# Reflection for the combined boundary shuttle

The positive simulation theorem for the combined shuttle deliberately excludes outward clamped
directional moves.  Reflection needs no such premise: a clamped first microstep is terminal, and
therefore cannot fabricate a return to a normal state.  This file records the stronger invariant
behind that observation.  Every configuration reachable from a plain/normal configuration is a
canonical protocol configuration representing a source configuration reachable in the original
machine.

No functionality, injectivity, finiteness, or tape-width hypothesis is used.  In particular, the
result applies uniformly to nondeterministic machines and to the one-cell bounded tape.
-/

namespace LBA

open Relation

variable {Γ Λ : Type*}

/-- If the first directional shuttle landing can read plain data, the head really moved.  At an
outward boundary (including either direction on a one-cell tape), it instead reads the departure
tag that was just written. -/
public theorem movesInside_of_combinedAfterDirectionalDeparture_read_plain
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hdirectional : move.direction ≠ .stay) (symbol : Γ)
    (hread : (combinedAfterDirectionalDeparture move tape).read = .plain symbol) :
    movesInside tape move.direction := by
  classical
  rcases tape with ⟨contents, head⟩
  cases hdirection : move.direction with
  | stay => exact False.elim (hdirectional hdirection)
  | left =>
      simp only [movesInside]
      by_contra hnot
      have hzero : ¬ 0 < head.val := hnot
      simp only [combinedAfterDirectionalDeparture, combinedShuttleTape,
        DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.read,
        hdirection, hzero, dite_false] at hread
      simp at hread
  | right =>
      simp only [movesInside]
      by_contra hnot
      simp only [combinedAfterDirectionalDeparture, combinedShuttleTape,
        DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.read,
        hdirection, hnot, dite_false] at hread
      simp at hread

/-- Canonical protocol configurations represent the source configuration obtained after zero or
one source steps.  For directional and stationary protocols we regard the semantic source step as
happening on the first microedge; the remaining microedges preserve the represented successor.

The first directional phase does not require `movesInside`: a clamped first edge is reachable and
represents the clamped source successor, but it has no outgoing compiled edge. -/
public inductive CombinedShuttleRepresents (M : Machine Γ Λ) {n : ℕ} :
    DLBA.Cfg Γ Λ n →
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n → Prop
  | normal (cfg : DLBA.Cfg Γ Λ n) :
      CombinedShuttleRepresents M cfg (combinedShuttleCfg cfg)
  | directionalAtNeighbour (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
      (henabled : M.ShuttleDirectionalEnabled move) (hread : tape.read = move.old) :
      CombinedShuttleRepresents M
        ⟨move.target, (tape.write move.written).moveHead move.direction⟩
        ⟨.directionalAtNeighbour move, combinedAfterDirectionalDeparture move tape⟩
  | directionalAtDeparture (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
      (henabled : M.ShuttleDirectionalEnabled move) (hread : tape.read = move.old)
      (hinside : movesInside tape move.direction) :
      CombinedShuttleRepresents M
        ⟨move.target, (tape.write move.written).moveHead move.direction⟩
        ⟨.directionalAtDeparture move (combinedDirectionalNeighbourSymbol move tape),
          combinedAfterDirectionalNeighbour move tape⟩
  | directionalRestoreNeighbour (move : ShuttleMove Γ Λ)
      (tape : DLBA.BoundedTape Γ n)
      (henabled : M.ShuttleDirectionalEnabled move) (hread : tape.read = move.old)
      (hinside : movesInside tape move.direction) :
      CombinedShuttleRepresents M
        ⟨move.target, (tape.write move.written).moveHead move.direction⟩
        ⟨.directionalRestoreNeighbour move (combinedDirectionalNeighbourSymbol move tape),
          combinedAfterDirectionalRestoreDeparture move tape⟩
  | stationaryPending (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
      (henabled : M.ShuttleStationaryEnabled move) (hread : tape.read = move.old) :
      CombinedShuttleRepresents M
        ⟨move.target, tape.write move.written⟩
        ⟨.stationaryPending move, combinedAfterStationarySave move tape⟩

/-- One compiled edge from a canonical reachable protocol shape either performs one source edge
(the first edge of a protocol) or preserves the already represented source successor. -/
public theorem Machine.combinedShuttleRepresents_step
    (M : Machine Γ Λ) {n : ℕ}
    {represented : DLBA.Cfg Γ Λ n}
    {source target :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    (hrep : CombinedShuttleRepresents M represented source)
    (hstep : Step M.combinedBoundaryShuttle source target) :
    ∃ represented' : DLBA.Cfg Γ Λ n,
      (represented' = represented ∨ Step M represented represented') ∧
      CombinedShuttleRepresents M represented' target := by
  cases hrep with
  | normal =>
      rcases represented with ⟨state, tape⟩
      rcases hstep with ⟨next, written, direction, henabled, rfl⟩
      change
        (∃ move : ShuttleMove Γ Λ,
          M.ShuttleDirectionalEnabled move ∧ move.source = state ∧
            move.old = tape.read ∧
            (next, written, direction) =
              (.directionalAtNeighbour move, .directionalDeparture move,
                move.direction)) ∨
        (∃ move : ShuttleMove Γ Λ,
          M.ShuttleStationaryEnabled move ∧ move.source = state ∧
            move.old = tape.read ∧
            (next, written, direction) =
              (.stationaryPending move, .stationarySaved move, .stay)) at henabled
      rcases henabled with
          ⟨move, hmove, hsource, hold, hout⟩ |
          ⟨move, hmove, hsource, hold, hout⟩
      · simp only [Prod.mk.injEq] at hout
        rcases hout with ⟨rfl, rfl, rfl⟩
        let successor : DLBA.Cfg Γ Λ n :=
          ⟨move.target, (tape.write move.written).moveHead move.direction⟩
        refine ⟨successor, Or.inr ?_, ?_⟩
        · exact ⟨move.target, move.written, move.direction,
            by simpa only [Machine.ShuttleEnabled, hsource, hold] using hmove.1, rfl⟩
        · exact CombinedShuttleRepresents.directionalAtNeighbour
            move tape hmove hold.symm
      · simp only [Prod.mk.injEq] at hout
        rcases hout with ⟨rfl, rfl, rfl⟩
        let successor : DLBA.Cfg Γ Λ n := ⟨move.target, tape.write move.written⟩
        have hstay : move.direction = .stay := hmove.2
        refine ⟨successor, Or.inr ?_, ?_⟩
        · refine ⟨move.target, move.written, move.direction,
            by simpa only [Machine.ShuttleEnabled, hsource, hold] using hmove.1, ?_⟩
          simp only [successor, hstay, combined_moveHead_stay]
        · simpa only [combinedAfterStationarySave, combined_moveHead_stay] using
            (CombinedShuttleRepresents.stationaryPending move tape hmove hold.symm)
  | directionalAtNeighbour move tape henabled hsourceRead =>
      rcases hstep with ⟨next, written, direction, hraw, rfl⟩
      cases hlanding : (combinedAfterDirectionalDeparture move tape).read with
      | plain neighbour =>
          rw [hlanding] at hraw
          change M.ShuttleDirectionalEnabled move ∧
            (next, written, direction) =
              (.directionalAtDeparture move neighbour,
                .directionalNeighbour move neighbour,
                reverseDirection move.direction) at hraw
          obtain ⟨_, hout⟩ := hraw
          simp only [Prod.mk.injEq] at hout
          rcases hout with ⟨rfl, rfl, rfl⟩
          have hinside : movesInside tape move.direction :=
            movesInside_of_combinedAfterDirectionalDeparture_read_plain
              move tape henabled.2 neighbour hlanding
          have hcanonical := combinedAfterDirectionalDeparture_read move tape hinside
          have hneighbour : neighbour = combinedDirectionalNeighbourSymbol move tape := by
            exact CombinedShuttleAlphabet.plain.inj (hlanding.symm.trans hcanonical)
          subst neighbour
          refine ⟨⟨move.target,
              (tape.write move.written).moveHead move.direction⟩, Or.inl rfl, ?_⟩
          exact CombinedShuttleRepresents.directionalAtDeparture
            move tape henabled hsourceRead hinside
      | directionalDeparture observed =>
          rw [hlanding] at hraw
          simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at hraw
      | directionalNeighbour observed neighbour =>
          rw [hlanding] at hraw
          simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at hraw
      | stationarySaved observed =>
          rw [hlanding] at hraw
          simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at hraw
  | directionalAtDeparture move tape henabled hsourceRead hinside =>
      rcases hstep with ⟨next, written, direction, hraw, rfl⟩
      rw [combinedAfterDirectionalNeighbour_read move tape hinside] at hraw
      change move = move ∧ M.ShuttleDirectionalEnabled move ∧
        (next, written, direction) =
          (.directionalRestoreNeighbour move
              (combinedDirectionalNeighbourSymbol move tape),
            .plain move.written, move.direction) at hraw
      obtain ⟨_, _, hout⟩ := hraw
      simp only [Prod.mk.injEq] at hout
      rcases hout with ⟨rfl, rfl, rfl⟩
      refine ⟨⟨move.target,
          (tape.write move.written).moveHead move.direction⟩, Or.inl rfl, ?_⟩
      exact CombinedShuttleRepresents.directionalRestoreNeighbour
        move tape henabled hsourceRead hinside
  | directionalRestoreNeighbour move tape henabled hsourceRead hinside =>
      rcases hstep with ⟨next, written, direction, hraw, rfl⟩
      rw [combinedAfterDirectionalRestoreDeparture_read move tape hinside] at hraw
      change move = move ∧
        combinedDirectionalNeighbourSymbol move tape =
          combinedDirectionalNeighbourSymbol move tape ∧
        M.ShuttleDirectionalEnabled move ∧
        (next, written, direction) =
          (.normal move.target,
            .plain (combinedDirectionalNeighbourSymbol move tape), .stay) at hraw
      obtain ⟨_, _, _, hout⟩ := hraw
      simp only [Prod.mk.injEq] at hout
      rcases hout with ⟨rfl, rfl, rfl⟩
      refine ⟨⟨move.target,
          (tape.write move.written).moveHead move.direction⟩, Or.inl rfl, ?_⟩
      have hfinish := combinedAfterDirectionalFinish_eq move tape hinside
      have htargetTape :
          ((combinedAfterDirectionalRestoreDeparture move tape).write
              (.plain (combinedDirectionalNeighbourSymbol move tape))).moveHead .stay =
            combinedShuttleTape
              ((tape.write move.written).moveHead move.direction) := by
        rw [combined_moveHead_stay]
        exact hfinish
      rw [htargetTape]
      exact CombinedShuttleRepresents.normal (M := M)
        (⟨move.target,
          (tape.write move.written).moveHead move.direction⟩ : DLBA.Cfg Γ Λ n)
  | stationaryPending move tape henabled hsourceRead =>
      rcases hstep with ⟨next, written, direction, hraw, rfl⟩
      rw [combinedAfterStationarySave_read move tape] at hraw
      change move = move ∧ M.ShuttleStationaryEnabled move ∧
        (next, written, direction) =
          (.normal move.target, .plain move.written, .stay) at hraw
      obtain ⟨_, _, hout⟩ := hraw
      simp only [Prod.mk.injEq] at hout
      rcases hout with ⟨rfl, rfl, rfl⟩
      refine ⟨⟨move.target, tape.write move.written⟩, Or.inl rfl, ?_⟩
      have hfinish := combinedAfterStationaryFinish_eq move tape
      have htargetTape :
          ((combinedAfterStationarySave move tape).write
              (.plain move.written)).moveHead .stay =
            combinedShuttleTape (tape.write move.written) := by
        rw [combined_moveHead_stay]
        exact hfinish
      rw [htargetTape]
      exact CombinedShuttleRepresents.normal (M := M)
        (⟨move.target, tape.write move.written⟩ : DLBA.Cfg Γ Λ n)

/-- Every raw run starting at a plain/normal embedding remains in one of the canonical protocol
shapes and represents a configuration reachable in the source machine.  A clamped directional
start is included as a terminal `directionalAtNeighbour` shape. -/
public theorem Machine.exists_reachable_of_reaches_combinedBoundaryShuttle
    (M : Machine Γ Λ) {n : ℕ}
    {source : DLBA.Cfg Γ Λ n}
    {target :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    (hreach : Reaches M.combinedBoundaryShuttle (combinedShuttleCfg source) target) :
    ∃ represented : DLBA.Cfg Γ Λ n,
      Reaches M source represented ∧ CombinedShuttleRepresents M represented target := by
  induction hreach with
  | refl =>
      exact ⟨source, ReflTransGen.refl, CombinedShuttleRepresents.normal source⟩
  | tail hprefix hstep ih =>
      obtain ⟨represented, hsourceReach, hrep⟩ := ih
      obtain ⟨represented', hsemantic, hrep'⟩ :=
        M.combinedShuttleRepresents_step hrep hstep
      refine ⟨represented', ?_, hrep'⟩
      rcases hsemantic with rfl | hsourceStep
      · exact hsourceReach
      · exact hsourceReach.tail hsourceStep

/-- A represented normal configuration is necessarily the exact plain embedding of what it
represents.  The intermediate constructors are excluded solely by their disjoint control-state
constructors. -/
public theorem CombinedShuttleRepresents.eq_combinedShuttleCfg_of_normal
    {M : Machine Γ Λ} {n : ℕ}
    {represented : DLBA.Cfg Γ Λ n}
    {target :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    (hrep : CombinedShuttleRepresents M represented target) (state : Λ)
    (hstate : target.state = .normal state) :
    target = combinedShuttleCfg represented := by
  cases hrep <;> simp_all [combinedShuttleCfg]

/-- The plain/normal configuration embedding is injective, for arbitrary alphabets and tape
widths. -/
public theorem combinedShuttleCfg_injective {n : ℕ} :
    Function.Injective
      (combinedShuttleCfg (Γ := Γ) (Λ := Λ) (n := n)) := by
  rintro ⟨leftState, ⟨leftContents, leftHead⟩⟩
    ⟨rightState, ⟨rightContents, rightHead⟩⟩ heq
  have hstate := congrArg
    (DLBA.Cfg.state :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n →
        CombinedShuttleState Γ Λ) heq
  have htape := congrArg
    (DLBA.Cfg.tape :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n →
        DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n) heq
  have hcontents := congrArg DLBA.BoundedTape.contents htape
  have hhead := congrArg DLBA.BoundedTape.head htape
  have hsourceState : leftState = rightState :=
    CombinedShuttleState.normal.inj hstate
  have hsourceContents : leftContents = rightContents := by
    funext index
    exact CombinedShuttleAlphabet.plain.inj (congrFun hcontents index)
  change leftHead = rightHead at hhead
  subst rightState
  subst rightContents
  subst rightHead
  rfl

/-- Run reflection at an arbitrary normal endpoint.  Starting from a canonical configuration,
no malformed tagged tape can return to a normal control state: the whole endpoint is the plain
embedding of a reachable source configuration. -/
public theorem Machine.exists_reaches_of_reaches_combinedBoundaryShuttle_of_normal
    (M : Machine Γ Λ) {n : ℕ}
    {source : DLBA.Cfg Γ Λ n}
    {target :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    (hreach : Reaches M.combinedBoundaryShuttle (combinedShuttleCfg source) target)
    (state : Λ) (hstate : target.state = .normal state) :
    ∃ represented : DLBA.Cfg Γ Λ n,
      Reaches M source represented ∧ target = combinedShuttleCfg represented := by
  obtain ⟨represented, hsourceReach, hrep⟩ :=
    M.exists_reachable_of_reaches_combinedBoundaryShuttle hreach
  exact ⟨represented, hsourceReach,
    hrep.eq_combinedShuttleCfg_of_normal state hstate⟩

/-- Exact reflection between two plain/normal endpoints.  This is the converse of the positive
simulation direction whenever the source run is nonclamping; reflection itself needs no
nonclamping or determinism premise. -/
public theorem Machine.reaches_of_reaches_combinedBoundaryShuttle
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hreach : Reaches M.combinedBoundaryShuttle
      (combinedShuttleCfg source) (combinedShuttleCfg target)) :
    Reaches M source target := by
  obtain ⟨represented, hsourceReach, htarget⟩ :=
    M.exists_reaches_of_reaches_combinedBoundaryShuttle_of_normal hreach
      target.state rfl
  have heq : target = represented :=
    combinedShuttleCfg_injective htarget
  simpa only [heq] using hsourceReach

/-- Acceptance reflection for the combined compiler.  Since only normal states accept, the
normal-endpoint reflection theorem applies automatically. -/
public theorem Machine.accepts_of_accepts_combinedBoundaryShuttle
    (M : Machine Γ Λ) {n : ℕ} (source : DLBA.Cfg Γ Λ n)
    (haccept : Accepts M.combinedBoundaryShuttle (combinedShuttleCfg source)) :
    Accepts M source := by
  obtain ⟨target, hreach, hfinal⟩ := haccept
  cases htargetState : target.state with
  | normal state =>
      obtain ⟨represented, hsourceReach, htarget⟩ :=
        M.exists_reaches_of_reaches_combinedBoundaryShuttle_of_normal
          hreach state htargetState
      refine ⟨represented, hsourceReach, ?_⟩
      rw [htarget] at hfinal
      exact hfinal
  | directionalAtNeighbour move =>
      rw [htargetState] at hfinal
      exact False.elim (Bool.false_ne_true hfinal)
  | directionalAtDeparture move neighbour =>
      rw [htargetState] at hfinal
      exact False.elim (Bool.false_ne_true hfinal)
  | directionalRestoreNeighbour move neighbour =>
      rw [htargetState] at hfinal
      exact False.elim (Bool.false_ne_true hfinal)
  | stationaryPending move =>
      rw [htargetState] at hfinal
      exact False.elim (Bool.false_ne_true hfinal)

end LBA
