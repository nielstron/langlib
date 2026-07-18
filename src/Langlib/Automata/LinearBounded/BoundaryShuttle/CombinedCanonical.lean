module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedStructural
public import Langlib.Automata.LinearBounded.BoundaryShuttle.Canonical
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical simulation by the combined shuttle

Every enabled stay instruction has an exact two-edge simulation on every bounded tape, including
one-cell tapes (`n = 0`).  Every enabled left/right instruction whose head genuinely moves has an
exact four-edge simulation.  The interior premise is essential: an outward boundary move is
supposed to become a terminal tagged collision, not a simulated clamped source step.
-/

namespace LBA

open Relation

variable {Γ Λ : Type*}

private theorem combined_boundedTape_ext {A : Type*} {n : ℕ}
    {left right : DLBA.BoundedTape A n}
    (hcontents : left.contents = right.contents)
    (hhead : left.head = right.head) : left = right := by
  cases left
  cases right
  simp_all

/-! ## Directional protocol -/

@[expose]
public def combinedAfterDirectionalDeparture {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n :=
  ((combinedShuttleTape (Λ := Λ) tape).write
    (.directionalDeparture move)).moveHead move.direction

@[expose]
public def combinedDirectionalNeighbourSymbol {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) : Γ :=
  (tape.moveHead move.direction).read

@[expose]
public def combinedAfterDirectionalNeighbour {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n :=
  ((combinedAfterDirectionalDeparture move tape).write
      (.directionalNeighbour move (combinedDirectionalNeighbourSymbol move tape))).moveHead
    (reverseDirection move.direction)

@[expose]
public def combinedAfterDirectionalRestoreDeparture {n : ℕ}
    (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n :=
  ((combinedAfterDirectionalNeighbour move tape).write
      (.plain move.written)).moveHead move.direction

@[expose]
public def combinedAfterDirectionalFinish {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n :=
  (combinedAfterDirectionalRestoreDeparture move tape).write
    (.plain (combinedDirectionalNeighbourSymbol move tape))

public theorem combinedAfterDirectionalDeparture_read
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hinside : movesInside tape move.direction) :
    (combinedAfterDirectionalDeparture move tape).read =
      .plain (combinedDirectionalNeighbourSymbol move tape) := by
  classical
  change Function.update (CombinedShuttleAlphabet.plain ∘ tape.contents) tape.head
      (.directionalDeparture move) (tape.moveHead move.direction).head =
    .plain (tape.contents (tape.moveHead move.direction).head)
  rw [Function.update_of_ne (movesInside_head_ne tape move.direction hinside)]
  rfl

public theorem combinedAfterDirectionalNeighbour_read
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hinside : movesInside tape move.direction) :
    (combinedAfterDirectionalNeighbour move tape).read =
      .directionalDeparture move := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (moveHead_reverseDirection_moveHead tape move.direction hinside)
  change Function.update
      (Function.update (CombinedShuttleAlphabet.plain ∘ tape.contents) tape.head
        (.directionalDeparture move))
      (tape.moveHead move.direction).head
      (.directionalNeighbour move (combinedDirectionalNeighbourSymbol move tape))
      ((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).head = .directionalDeparture move
  rw [hback]
  rw [Function.update_of_ne (movesInside_head_ne tape move.direction hinside).symm]
  simp

public theorem combinedAfterDirectionalRestoreDeparture_read
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hinside : movesInside tape move.direction) :
    (combinedAfterDirectionalRestoreDeparture move tape).read =
      .directionalNeighbour move (combinedDirectionalNeighbourSymbol move tape) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (moveHead_reverseDirection_moveHead tape move.direction hinside)
  have hforward :
      (((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).moveHead move.direction).head =
          (tape.moveHead move.direction).head := by
    rw [moveHead_reverseDirection_moveHead tape move.direction hinside]
  change Function.update
      (Function.update
        (Function.update (CombinedShuttleAlphabet.plain ∘ tape.contents) tape.head
          (.directionalDeparture move))
        (tape.moveHead move.direction).head
        (.directionalNeighbour move (combinedDirectionalNeighbourSymbol move tape)))
      ((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).head
      (.plain move.written)
      (((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).moveHead move.direction).head =
          .directionalNeighbour move (combinedDirectionalNeighbourSymbol move tape)
  rw [hback, hforward]
  rw [Function.update_of_ne (movesInside_head_ne tape move.direction hinside)]
  simp

/-- Exact tape restoration after the directional four-edge protocol. -/
public theorem combinedAfterDirectionalFinish_eq
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hinside : movesInside tape move.direction) :
    combinedAfterDirectionalFinish move tape =
      combinedShuttleTape (Λ := Λ)
        ((tape.write move.written).moveHead move.direction) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (moveHead_reverseDirection_moveHead tape move.direction hinside)
  have hforward :
      (((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).moveHead move.direction).head =
          (tape.moveHead move.direction).head := by
    rw [moveHead_reverseDirection_moveHead tape move.direction hinside]
  apply combined_boundedTape_ext
  · change Function.update
        (Function.update
          (Function.update
            (Function.update (CombinedShuttleAlphabet.plain ∘ tape.contents) tape.head
              (.directionalDeparture move))
            (tape.moveHead move.direction).head
            (.directionalNeighbour move (combinedDirectionalNeighbourSymbol move tape)))
          ((tape.moveHead move.direction).moveHead
            (reverseDirection move.direction)).head
          (.plain move.written))
        (((tape.moveHead move.direction).moveHead
          (reverseDirection move.direction)).moveHead move.direction).head
        (.plain (combinedDirectionalNeighbourSymbol move tape)) =
      CombinedShuttleAlphabet.plain ∘
        Function.update tape.contents tape.head move.written
    rw [hback, hforward]
    have hne := movesInside_head_ne tape move.direction hinside
    rw [Function.update_comm hne.symm]
    rw [Function.update_idem]
    rw [Function.update_comm hne]
    rw [Function.update_idem]
    rw [Function.comp_update]
    change Function.update
      (Function.update (CombinedShuttleAlphabet.plain ∘ tape.contents) tape.head
        (.plain move.written))
      (tape.moveHead move.direction).head
      (.plain ((tape.moveHead move.direction).read)) = _
    apply Function.update_eq_self_iff.mpr
    rw [Function.update_of_ne hne]
    rfl
  · exact hforward

/-- An enabled non-clamped directional instruction expands through the three advertised
canonical intermediate configurations and four raw edges. -/
public theorem Machine.combinedBoundaryShuttle_exact_four_steps_of_directional_move
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = move.old)
    (hinside : movesInside tape move.direction) :
    ∃ first second third :
        DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n,
      first = ⟨.directionalAtNeighbour move,
        combinedAfterDirectionalDeparture move tape⟩ ∧
      second = ⟨.directionalAtDeparture move
          (combinedDirectionalNeighbourSymbol move tape),
        combinedAfterDirectionalNeighbour move tape⟩ ∧
      third = ⟨.directionalRestoreNeighbour move
          (combinedDirectionalNeighbourSymbol move tape),
        combinedAfterDirectionalRestoreDeparture move tape⟩ ∧
      Step M.combinedBoundaryShuttle
        (combinedShuttleCfg (Λ := Λ) ⟨move.source, tape⟩) first ∧
      Step M.combinedBoundaryShuttle first second ∧
      Step M.combinedBoundaryShuttle second third ∧
      Step M.combinedBoundaryShuttle third
        (combinedShuttleCfg (Λ := Λ)
          ⟨move.target, (tape.write move.written).moveHead move.direction⟩) := by
  let first : DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
    ⟨.directionalAtNeighbour move, combinedAfterDirectionalDeparture move tape⟩
  let second : DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
    ⟨.directionalAtDeparture move (combinedDirectionalNeighbourSymbol move tape),
      combinedAfterDirectionalNeighbour move tape⟩
  let third : DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
    ⟨.directionalRestoreNeighbour move (combinedDirectionalNeighbourSymbol move tape),
      combinedAfterDirectionalRestoreDeparture move tape⟩
  refine ⟨first, second, third, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · apply M.step_combinedShuttle_directionalStart move
      (combinedShuttleTape (Λ := Λ) tape) henabled
    change CombinedShuttleAlphabet.plain tape.read = .plain move.old
    rw [hread]
  · apply M.step_combinedShuttle_directionalTagNeighbour move
      (combinedDirectionalNeighbourSymbol move tape)
      (combinedAfterDirectionalDeparture move tape) henabled
    exact combinedAfterDirectionalDeparture_read move tape hinside
  · apply M.step_combinedShuttle_directionalRestoreDeparture move
      (combinedDirectionalNeighbourSymbol move tape)
      (combinedAfterDirectionalNeighbour move tape) henabled
    exact combinedAfterDirectionalNeighbour_read move tape hinside
  · have hfinish := M.step_combinedShuttle_directionalFinish move
      (combinedDirectionalNeighbourSymbol move tape)
      (combinedAfterDirectionalRestoreDeparture move tape) henabled
      (combinedAfterDirectionalRestoreDeparture_read move tape hinside)
    simpa only [third, combinedShuttleCfg, combinedAfterDirectionalFinish] using
      (combinedAfterDirectionalFinish_eq move tape hinside ▸ hfinish)

public theorem Machine.reaches_combinedBoundaryShuttle_of_directional_move
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = move.old)
    (hinside : movesInside tape move.direction) :
    Reaches M.combinedBoundaryShuttle
      (combinedShuttleCfg (Λ := Λ) ⟨move.source, tape⟩)
      (combinedShuttleCfg (Λ := Λ)
        ⟨move.target, (tape.write move.written).moveHead move.direction⟩) := by
  obtain ⟨first, second, third, _, _, _, h₁, h₂, h₃, h₄⟩ :=
    M.combinedBoundaryShuttle_exact_four_steps_of_directional_move
      move tape henabled hread hinside
  exact (ReflTransGen.single h₁).tail h₂ |>.tail h₃ |>.tail h₄

/-! ## Stationary protocol -/

@[expose]
public def combinedAfterStationarySave {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n :=
  (combinedShuttleTape (Λ := Λ) tape).write (.stationarySaved move)

@[expose]
public def combinedAfterStationaryFinish {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n :=
  (combinedAfterStationarySave move tape).write (.plain move.written)

public theorem combinedAfterStationarySave_read
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n) :
    (combinedAfterStationarySave move tape).read = .stationarySaved move := by
  classical
  simp [combinedAfterStationarySave, DLBA.BoundedTape.read, DLBA.BoundedTape.write]

public theorem combinedAfterStationaryFinish_eq
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n) :
    combinedAfterStationaryFinish move tape =
      combinedShuttleTape (Λ := Λ) (tape.write move.written) := by
  classical
  rcases tape with ⟨contents, head⟩
  simp only [combinedAfterStationaryFinish, combinedAfterStationarySave,
    combinedShuttleTape, DLBA.BoundedTape.write]
  congr 1
  rw [Function.update_idem]
  rw [Function.comp_update]

/-- Exact two-edge simulation of an enabled stay instruction, with no tape-width or head-position
premise. -/
public theorem Machine.combinedBoundaryShuttle_exact_two_steps_of_stationary_move
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n)
    (henabled : M.ShuttleStationaryEnabled move)
    (hread : tape.read = move.old) :
    ∃ middle :
        DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n,
      middle = ⟨.stationaryPending move, combinedAfterStationarySave move tape⟩ ∧
      Step M.combinedBoundaryShuttle
        (combinedShuttleCfg (Λ := Λ) ⟨move.source, tape⟩) middle ∧
      Step M.combinedBoundaryShuttle middle
        (combinedShuttleCfg (Λ := Λ)
          ⟨move.target, tape.write move.written⟩) := by
  let middle : DLBA.Cfg
      (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
    ⟨.stationaryPending move, combinedAfterStationarySave move tape⟩
  refine ⟨middle, rfl, ?_, ?_⟩
  · apply M.step_combinedShuttle_stationarySave move
      (combinedShuttleTape (Λ := Λ) tape) henabled
    change CombinedShuttleAlphabet.plain tape.read = .plain move.old
    rw [hread]
  · have hfinish := M.step_combinedShuttle_stationaryFinish move
      (combinedAfterStationarySave move tape) henabled
      (combinedAfterStationarySave_read move tape)
    simpa only [middle, combinedShuttleCfg, combinedAfterStationaryFinish] using
      (combinedAfterStationaryFinish_eq move tape ▸ hfinish)

public theorem Machine.reaches_combinedBoundaryShuttle_of_stationary_move
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n)
    (henabled : M.ShuttleStationaryEnabled move)
    (hread : tape.read = move.old) :
    Reaches M.combinedBoundaryShuttle
      (combinedShuttleCfg (Λ := Λ) ⟨move.source, tape⟩)
      (combinedShuttleCfg (Λ := Λ) ⟨move.target, tape.write move.written⟩) := by
  obtain ⟨middle, _, hfirst, hsecond⟩ :=
    M.combinedBoundaryShuttle_exact_two_steps_of_stationary_move
      move tape henabled hread
  exact (ReflTransGen.single hfirst).tail hsecond

/-- Unified positive simulation theorem.  Every enabled stay instruction is covered, and every
enabled directional instruction is covered when its physical head motion is non-clamped. -/
public theorem Machine.reaches_combinedBoundaryShuttle_of_move
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n)
    (henabled : M.ShuttleEnabled move)
    (hread : tape.read = move.old)
    (hphysical : move.direction = .stay ∨ movesInside tape move.direction) :
    Reaches M.combinedBoundaryShuttle
      (combinedShuttleCfg (Λ := Λ) ⟨move.source, tape⟩)
      (combinedShuttleCfg (Λ := Λ)
        ⟨move.target, (tape.write move.written).moveHead move.direction⟩) := by
  rcases hphysical with hstay | hinside
  · have hreach := M.reaches_combinedBoundaryShuttle_of_stationary_move
      move tape ⟨henabled, hstay⟩ hread
    simpa [hstay] using hreach
  · exact M.reaches_combinedBoundaryShuttle_of_directional_move
      move tape ⟨henabled, movesInside_directional hinside⟩ hread hinside

end LBA
