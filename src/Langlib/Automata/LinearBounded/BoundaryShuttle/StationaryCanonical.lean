module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.StationaryStructural
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact canonical two-step semantics of the stationary shuttle

An enabled stay instruction on a plain embedded tape always performs exactly the two advertised
microsteps.  The intermediate tape contains its private instruction tag at the head; the second
step erases that tag and yields precisely the plain embedding of the source write.  No interior-
head premise is needed because both steps use `stay`.
-/

namespace LBA

open Relation

variable {Γ Λ : Type*}

/-- Canonical tape after saving a stationary instruction. -/
@[expose]
public def stationaryShuttleAfterSave {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n :=
  (stationaryShuttleTape (Λ := Λ) tape).write (.saved move)

/-- Canonical tape after finishing a stationary instruction. -/
@[expose]
public def stationaryShuttleAfterFinish {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n :=
  (stationaryShuttleAfterSave move tape).write (.plain move.written)

/-- The saved-instruction phase reads exactly the private tag just written. -/
public theorem stationaryShuttleAfterSave_read
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n) :
    (stationaryShuttleAfterSave move tape).read = .saved move := by
  classical
  simp [stationaryShuttleAfterSave, DLBA.BoundedTape.read,
    DLBA.BoundedTape.write]

/-- Erasing the saved tag yields exactly the plain embedding of the source write. -/
public theorem stationaryShuttleAfterFinish_eq
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n) :
    stationaryShuttleAfterFinish move tape =
      stationaryShuttleTape (Λ := Λ) (tape.write move.written) := by
  classical
  rcases tape with ⟨contents, head⟩
  simp only [stationaryShuttleAfterFinish, stationaryShuttleAfterSave,
    stationaryShuttleTape, DLBA.BoundedTape.write]
  congr 1
  rw [Function.update_idem]
  rw [Function.comp_update]

/-- An enabled stay instruction expands to exactly two raw stationary-shuttle edges, with the
unique advertised canonical midpoint. -/
public theorem Machine.stationaryShuttle_exact_two_steps_of_move
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n)
    (henabled : M.ShuttleStationaryEnabled move)
    (hread : tape.read = move.old) :
    ∃ middle :
        DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n,
      middle = ⟨.pending move, stationaryShuttleAfterSave move tape⟩ ∧
      Step M.stationaryShuttle
        (stationaryShuttleCfg (Λ := Λ) ⟨move.source, tape⟩) middle ∧
      Step M.stationaryShuttle middle
        (stationaryShuttleCfg (Λ := Λ)
          ⟨move.target, tape.write move.written⟩) := by
  let middle :
      DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n :=
    ⟨.pending move, stationaryShuttleAfterSave move tape⟩
  refine ⟨middle, rfl, ?_, ?_⟩
  · apply M.step_stationaryShuttle_save move
      (stationaryShuttleTape (Λ := Λ) tape) henabled
    change StationaryShuttleAlphabet.plain tape.read = .plain move.old
    rw [hread]
  · have hfinish := M.step_stationaryShuttle_finish move
      (stationaryShuttleAfterSave move tape) henabled
      (stationaryShuttleAfterSave_read move tape)
    simpa only [middle, stationaryShuttleCfg, stationaryShuttleAfterFinish] using
      (stationaryShuttleAfterFinish_eq move tape ▸ hfinish)

/-- Reachability corollary of the exact two-step canonical simulation. -/
public theorem Machine.reaches_stationaryShuttle_of_move
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n)
    (henabled : M.ShuttleStationaryEnabled move)
    (hread : tape.read = move.old) :
    Reaches M.stationaryShuttle
      (stationaryShuttleCfg (Λ := Λ) ⟨move.source, tape⟩)
      (stationaryShuttleCfg (Λ := Λ)
        ⟨move.target, tape.write move.written⟩) := by
  obtain ⟨middle, _, hfirst, hsecond⟩ :=
    M.stationaryShuttle_exact_two_steps_of_move move tape henabled hread
  exact (ReflTransGen.single hfirst).tail hsecond

/-- Configuration-facing exact simulation.  The extra witness identifies which source edge is
the enabled stay edge when `M` is nondeterministic. -/
public theorem Machine.stationaryShuttle_exact_two_steps_of_stationary_step
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hstationary : ∃ next written,
      (next, written, .stay) ∈ M.transition source.state source.tape.read ∧
      target = ⟨next, source.tape.write written⟩) :
    ∃ middle :
        DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n,
      Step M.stationaryShuttle (stationaryShuttleCfg source) middle ∧
      Step M.stationaryShuttle middle (stationaryShuttleCfg target) := by
  obtain ⟨next, written, henabled, rfl⟩ := hstationary
  let move : ShuttleMove Γ Λ :=
    { source := source.state
      old := source.tape.read
      target := next
      written := written
      direction := .stay }
  obtain ⟨middle, _, hfirst, hsecond⟩ :=
    M.stationaryShuttle_exact_two_steps_of_move move source.tape
      ⟨henabled, rfl⟩ rfl
  exact ⟨middle, hfirst, hsecond⟩

end LBA
