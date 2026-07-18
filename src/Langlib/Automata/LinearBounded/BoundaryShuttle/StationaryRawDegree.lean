module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.StationaryCanonical
public import Langlib.Automata.LinearBounded.Cofunctional
import Mathlib.Tactic

@[expose]
public section

/-!
# Raw predecessor bounds for the stationary shuttle

Stationary writes have only one inverse head position.  A pending landing also retains the full
move in its state and tag, so its predecessor is unique without any source hypothesis.  A normal
landing exposes the final written symbol; `StationaryTargetWrittenInjective` then recovers the
full move and makes that predecessor unique as well.  Consequently the complete raw step graph
has indegree at most one—not merely two—and a purported double merge is impossible.
-/

namespace LBA

open Classical

variable {Γ Λ : Type*}

private theorem stationary_write_write_read {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (written : A) :
    (tape.write written).write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

/-- The one-cell tape used to witness necessity of target-and-written injectivity. -/
private def stationarySingletonTape {A : Type*} (symbol : A) :
    DLBA.BoundedTape A 0 :=
  ⟨fun _ ↦ symbol, ⟨0, by omega⟩⟩

@[simp]
private theorem stationarySingletonTape_read {A : Type*} (symbol : A) :
    (stationarySingletonTape symbol).read = symbol := rfl

@[simp]
private theorem stationarySingletonTape_write {A : Type*} (old written : A) :
    (stationarySingletonTape old).write written =
      stationarySingletonTape written := by
  classical
  simp only [stationarySingletonTape, DLBA.BoundedTape.write]
  congr 1
  funext index
  have hindex : index = (⟨0, by omega⟩ : Fin 1) := by
    apply Fin.ext
    omega
  subst index
  simp

/-- Every pending configuration has a unique raw predecessor. -/
public theorem Machine.predecessor_stationaryShuttle_pending_eq
    (M : Machine Γ Λ) {n : ℕ}
    {left right :
      DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ}
    {tape : DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n}
    (hleft : Step M.stationaryShuttle left ⟨.pending move, tape⟩)
    (hright : Step M.stationaryShuttle right ⟨.pending move, tape⟩) :
    left = right := by
  rw [M.step_stationaryShuttle_iff] at hleft hright
  rcases hleft with
      ⟨leftMove, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩
  all_goals try simp at hleftTarget
  rcases hright with
      ⟨rightMove, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩
  all_goals try simp at hrightTarget
  rcases hleftTarget with ⟨hleftMove, hleftTape⟩
  rcases hrightTarget with ⟨hrightMove, hrightTape⟩
  subst leftMove
  subst rightMove
  have hleftRestore : leftTape = tape.write (.plain move.old) := by
    rw [hleftTape]
    rw [← hleftRead]
    exact (stationary_write_write_read leftTape (.saved move)).symm
  have hrightRestore : rightTape = tape.write (.plain move.old) := by
    rw [hrightTape]
    rw [← hrightRead]
    exact (stationary_write_write_read rightTape (.saved move)).symm
  rw [hleftSource, hrightSource, hleftRestore, hrightRestore]

/-- Under `(target, written)` injectivity, every normal configuration has a unique raw
predecessor. -/
public theorem Machine.predecessor_stationaryShuttle_normal_eq
    (M : Machine Γ Λ) (htarget : M.StationaryTargetWrittenInjective)
    {n : ℕ}
    {left right :
      DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n}
    {target : Λ}
    {tape : DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n}
    (hleft : Step M.stationaryShuttle left ⟨.normal target, tape⟩)
    (hright : Step M.stationaryShuttle right ⟨.normal target, tape⟩) :
    left = right := by
  rw [M.step_stationaryShuttle_iff] at hleft hright
  rcases hleft with
      ⟨leftMove, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩
  all_goals try simp at hleftTarget
  rcases hright with
      ⟨rightMove, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩
  all_goals try simp at hrightTarget
  rcases hleftTarget with ⟨hleftTargetState, hleftTargetTape⟩
  rcases hrightTarget with ⟨hrightTargetState, hrightTargetTape⟩
  have hleftVisible : tape.read = .plain leftMove.written := by
    rw [hleftTargetTape]
    simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
  have hrightVisible : tape.read = .plain rightMove.written := by
    rw [hrightTargetTape]
    simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
  have hwritten : leftMove.written = rightMove.written := by
    rw [hleftVisible] at hrightVisible
    exact StationaryShuttleAlphabet.plain.inj hrightVisible
  have hmove : leftMove = rightMove :=
    htarget leftMove rightMove hleftEnabled hrightEnabled
      (hleftTargetState.symm.trans hrightTargetState) hwritten
  subst rightMove
  have hleftRestore : leftTape = tape.write (.saved leftMove) := by
    rw [hleftTargetTape]
    rw [← hleftRead]
    exact (stationary_write_write_read leftTape (.plain leftMove.written)).symm
  have hrightRestore : rightTape = tape.write (.saved leftMove) := by
    rw [hrightTargetTape]
    rw [← hrightRead]
    exact (stationary_write_write_read rightTape (.plain leftMove.written)).symm
  rw [hleftSource, hrightSource, hleftRestore, hrightRestore]

/-- The complete raw stationary-shuttle step relation is cofunctional under the exact target-
and-written-symbol injectivity premise. -/
public theorem Machine.stationaryShuttle_cofunctional
    (M : Machine Γ Λ) (htarget : M.StationaryTargetWrittenInjective) :
    M.stationaryShuttle.Cofunctional := by
  intro n left right target hleft hright
  rcases target with ⟨state, tape⟩
  cases state with
  | normal state =>
      exact M.predecessor_stationaryShuttle_normal_eq htarget hleft hright
  | pending move =>
      exact M.predecessor_stationaryShuttle_pending_eq hleft hright

/-- The `(target, written)` premise is not merely sufficient: raw cofunctionality of the
standalone stationary compiler forces it.  The counterexample to injectivity already lives on a
one-cell tape. -/
public theorem Machine.stationaryTargetWrittenInjective_of_stationaryShuttle_cofunctional
    (M : Machine Γ Λ) (hcofunctional : M.stationaryShuttle.Cofunctional) :
    M.StationaryTargetWrittenInjective := by
  intro leftMove rightMove hleftEnabled hrightEnabled htarget hwritten
  let leftTape : DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) 0 :=
    stationarySingletonTape (.saved leftMove)
  let rightTape : DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) 0 :=
    stationarySingletonTape (.saved rightMove)
  have hleft : Step M.stationaryShuttle
      ⟨.pending leftMove, leftTape⟩
      ⟨.normal leftMove.target,
        stationarySingletonTape (.plain leftMove.written)⟩ := by
    simpa [leftTape] using
      M.step_stationaryShuttle_finish leftMove leftTape hleftEnabled
        (by simp [leftTape, stationarySingletonTape])
  have hright : Step M.stationaryShuttle
      ⟨.pending rightMove, rightTape⟩
      ⟨.normal leftMove.target,
        stationarySingletonTape (.plain leftMove.written)⟩ := by
    have hright' := M.step_stationaryShuttle_finish rightMove rightTape
      hrightEnabled (by simp [rightTape, stationarySingletonTape])
    simpa [rightTape, ← htarget, ← hwritten] using hright'
  have hcfg :
      (⟨.pending leftMove, leftTape⟩ :
        DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) 0) =
      ⟨.pending rightMove, rightTape⟩ :=
    hcofunctional hleft hright
  have hstate := congrArg DLBA.Cfg.state hcfg
  exact StationaryShuttleState.pending.inj hstate

/-- Exact characterization of the stationary compiler's raw backward determinism. -/
public theorem Machine.stationaryShuttle_cofunctional_iff
    (M : Machine Γ Λ) :
    M.stationaryShuttle.Cofunctional ↔ M.StationaryTargetWrittenInjective :=
  ⟨M.stationaryTargetWrittenInjective_of_stationaryShuttle_cofunctional,
    M.stationaryShuttle_cofunctional⟩

/-- Every raw stationary-shuttle configuration has at most one predecessor. -/
public theorem Machine.stationaryShuttle_configurationIndegreeAtMostOne
    (M : Machine Γ Λ) (htarget : M.StationaryTargetWrittenInjective) :
    ∀ (n : ℕ)
      (target :
        DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n),
      Set.encard {source | Step M.stationaryShuttle source target} ≤ 1 := by
  intro n target
  apply Set.encard_le_one_iff.mpr
  intro left right hleft hright
  exact M.stationaryShuttle_cofunctional htarget hleft hright

/-- In particular, every raw stationary-shuttle configuration has indegree at most two. -/
public theorem Machine.stationaryShuttle_configurationIndegreeAtMostTwo
    (M : Machine Γ Λ) (htarget : M.StationaryTargetWrittenInjective) :
    M.stationaryShuttle.ConfigurationIndegreeAtMostTwo := by
  intro n target
  exact (M.stationaryShuttle_configurationIndegreeAtMostOne htarget n target).trans (by
    norm_num)

/-- Functionality gives the raw outdegree bound one. -/
public theorem Machine.stationaryShuttle_configurationOutdegreeAtMostOne
    (M : Machine Γ Λ) (hfunctional : M.StationaryFunctional) :
    ∀ (n : ℕ)
      (source :
        DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n),
      Set.encard {target | Step M.stationaryShuttle source target} ≤ 1 := by
  intro n source
  apply Set.encard_le_one_iff.mpr
  intro left right hleft hright
  rcases hleft with ⟨leftTarget, leftWritten, leftDirection, hleftEnabled, rfl⟩
  rcases hright with ⟨rightTarget, rightWritten, rightDirection, hrightEnabled, rfl⟩
  have hmove := M.stationaryShuttle_functional hfunctional
    source.state source.tape.read hleftEnabled hrightEnabled
  simp only [Prod.mk.injEq] at hmove
  rcases hmove with ⟨rfl, rfl, rfl⟩
  rfl

/-- A purported raw double merge is impossible, hence vacuously a sink. -/
public theorem Machine.sink_of_two_distinct_predecessors_stationaryShuttle
    (M : Machine Γ Λ) (htarget : M.StationaryTargetWrittenInjective)
    {n : ℕ}
    {left right target :
      DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n}
    (hne : left ≠ right)
    (hleft : Step M.stationaryShuttle left target)
    (hright : Step M.stationaryShuttle right target) :
    ∀ next, ¬ Step M.stationaryShuttle target next := by
  exact False.elim (hne (M.stationaryShuttle_cofunctional htarget hleft hright))

end LBA
