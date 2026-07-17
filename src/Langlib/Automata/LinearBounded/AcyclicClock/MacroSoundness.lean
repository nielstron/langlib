module

public import Langlib.Automata.LinearBounded.AcyclicClock.MacroSimulation
public import Langlib.Automata.LinearBounded.AcyclicClock.EffectiveClock
public import Langlib.Automata.LinearBounded.AcyclicClock.SoundnessLift

@[expose]
public section

/-!
# Soundness of operational Ready-to-Ready paths

Outside `ready`, the concrete protocol is deterministic.  We stop its transition relation as soon
as a Ready checkpoint is reached, compare two such stopped paths by right-uniqueness, and use the
strict Ready-to-Ready clock rank to identify the first returned checkpoint with the one constructed
by macro completeness.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

set_option maxHeartbeats 1000000 in
private theorem transition_right_unique_of_not_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (state : State Λ) (symbol : TapeAlpha T Γ Λ)
    (hstate : ¬state.IsReady)
    {left right : State Λ × TapeAlpha T Γ Λ × DLBA.Dir}
    (hleft : left ∈ transition M state symbol)
    (hright : right ∈ transition M state symbol) :
    left = right := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rcases symbol with (inner | boundary)
  · rcases inner with (_ | tagged)
    · cases state <;> simp_all [transition]
    · rcases tagged with (input | cell)
      · cases state <;> simp_all [transition]
      · by_cases hready : state.IsReady
        · exact (hstate hready).elim
        · cases state <;> simp_all [State.IsReady, transition] <;>
            repeat' first
              | split at hleft
              | split at hright <;>
            simp_all
  · cases boundary <;> cases state <;> simp_all [transition]

/-- Every non-Ready source configuration has at most one target-machine successor. -/
public theorem nonready_step_right_unique
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source left right :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hsource : ¬source.state.IsReady)
    (hleft : LBA.Step (machine M) source left)
    (hright : LBA.Step (machine M) source right) :
    left = right := by
  rcases hleft with ⟨leftState, leftWritten, leftDirection, hleftMem, rfl⟩
  rcases hright with
    ⟨rightState, rightWritten, rightDirection, hrightMem, rfl⟩
  have htriple :
      (leftState, leftWritten, leftDirection) =
        (rightState, rightWritten, rightDirection) :=
    transition_right_unique_of_not_ready M source.state source.tape.read
      hsource hleftMem hrightMem
  cases htriple
  rfl

/-- The target step relation stopped at Ready sources. -/
public def BeforeReadyStep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (source target :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) : Prop :=
  LBA.Step (machine M) source target ∧ ¬source.state.IsReady

public theorem beforeReadyStep_rightUnique
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} :
    Relator.RightUnique
      (BeforeReadyStep M :
        DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n →
          DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n → Prop) := by
  intro source left right hleft hright
  exact nonready_step_right_unique M hleft.2 hleft.1 hright.1

/-- Split a path starting outside Ready at its first Ready visit. -/
public theorem reaches_split_first_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source target :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hsource : ¬source.state.IsReady)
    (htarget : target.state.IsReady)
    (hpath : LBA.Reaches (machine M) source target) :
    ∃ first,
      ReflTransGen (BeforeReadyStep M) source first ∧
        first.state.IsReady ∧
        LBA.Reaches (machine M) first target := by
  induction hpath using ReflTransGen.head_induction_on with
  | refl =>
      exact (hsource htarget).elim
  | @head source middle hstep hrest ih =>
      by_cases hmiddle : middle.state.IsReady
      · exact ⟨middle, .single ⟨hstep, hsource⟩, hmiddle, hrest⟩
      · obtain ⟨first, hprefix, hfirst, hsuffix⟩ := ih hmiddle
        exact
          ⟨first, ReflTransGen.head ⟨hstep, hsource⟩ hprefix,
            hfirst, hsuffix⟩

/-- A stopped path cannot leave a Ready source. -/
public theorem beforeReady_reaches_eq_of_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source target :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hsource : source.state.IsReady)
    (hpath : ReflTransGen (BeforeReadyStep M) source target) :
    source = target := by
  rcases ReflTransGen.cases_head hpath with heq | ⟨middle, hstep, hrest⟩
  · exact heq
  · exact (hstep.2 hsource).elim

/-- Right-uniqueness makes the first Ready endpoint of a stopped protocol run unique. -/
public theorem beforeReady_ready_endpoint_unique
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source left right :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hleftReady : left.state.IsReady)
    (hrightReady : right.state.IsReady)
    (hleft : ReflTransGen (BeforeReadyStep M) source left)
    (hright : ReflTransGen (BeforeReadyStep M) source right) :
    left = right := by
  rcases ReflTransGen.total_of_right_unique
      (beforeReadyStep_rightUnique M) hleft hright with
    hleftRight | hrightLeft
  · exact beforeReady_reaches_eq_of_ready M hleftReady hleftRight
  · exact (beforeReady_reaches_eq_of_ready M hrightReady hrightLeft).symm

/-- Invert the sole nondeterministic step at a represented Ready checkpoint. -/
public theorem step_checkpoint_inv
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hstep :
      LBA.Step (machine M) (checkpointCfg cfg digits trails) target) :
    ∃ (nextState : Λ) (written : SourceAlpha T Γ) (direction : DLBA.Dir),
      (nextState, written, direction) ∈
          M.transition cfg.state cfg.tape.read ∧
        target =
          afterReadyCfg cfg digits trails nextState written direction := by
  rcases hstep with ⟨nextState, written, direction, hmem, rfl⟩
  change
    (nextState, written, direction) ∈
      transition M (.ready cfg.state)
        (workSymbol (checkpointCell cfg.tape digits trails cfg.tape.head)) at hmem
  rw [transition_ready_work, if_pos] at hmem
  · rcases hmem with ⟨move, hmove, hchoice⟩
    rcases move with ⟨moveState, moveWritten, moveDirection⟩
    simp only [sourceChoice] at hchoice
    rcases hchoice with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, _, hmove, rfl⟩
  · simp [checkpointCell, readyCell]

/-- A nonempty return from a checkpoint to Ready forces the current fixed-width clock row to have
a successor.  Otherwise the current rank would already be the full clock capacity minus one,
contradicting strict Ready-to-Ready growth and the universal capacity bound. -/
public theorem incrementClockRow_noOverflow_of_ready_transGen
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (htarget : target.state.IsReady)
    (hpath :
      TransGen (LBA.Step (machine M))
        (checkpointCfg cfg digits trails) target) :
    (incrementClockRow M (List.ofFn digits)).2 = false := by
  let E := clockCodec (T := T) (Γ := Γ) (Λ := Λ)
  letI : Nonempty Λ := ⟨M.initial⟩
  have hgrowth :=
    ready_transGen_clockValue_lt M (by trivial) htarget hpath
  have hbound := clockValue_lt_capacity M target.tape
  have hbound' :
      clockValue M target.tape < E.radix ^ (n + 1) := by
    simpa [LBA.StrictClockLayering.clockCapacity, E,
      clockCodec_radix] using hbound
  have hgrowth' :
      E.value (List.ofFn digits) < clockValue M target.tape := by
    simpa [checkpointCfg, E] using hgrowth
  cases hflag : (incrementClockRow M (List.ofFn digits)).2 with
  | false => rfl
  | true =>
      have hoverflow :
          (E.increment (List.ofFn digits)).2 = true := by
        simpa [incrementClockRow, E] using hflag
      have hfull :=
        (E.increment_overflow_iff_value (List.ofFn digits)).1 hoverflow
      have hlength : (List.ofFn digits).length = n + 1 := by simp
      rw [hlength] at hfull
      omega

/-- The checkpoint reconstructed from the nonoverflowing increment has clock rank exactly one
larger than the original checkpoint, independently of both checkpoints' scratch trails. -/
public theorem clockValue_checkpoint_of_increment
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (cfg cfg' : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits digits' : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails trails' : ReadyTrails n)
    (hno : (incrementClockRow M (List.ofFn digits)).2 = false)
    (hdigits :
      List.ofFn digits' = (incrementClockRow M (List.ofFn digits)).1) :
    clockValue M (checkpointCfg cfg' digits' trails').tape =
      clockValue M (checkpointCfg cfg digits trails).tape + 1 := by
  let E := clockCodec (T := T) (Γ := Γ) (Λ := Λ)
  letI : Nonempty Λ := ⟨M.initial⟩
  have hno' : (E.increment (List.ofFn digits)).2 = false := by
    simpa [incrementClockRow, E] using hno
  have hvalue :=
    E.value_increment_of_not_overflow (List.ofFn digits) hno'
  simp only [checkpointCfg, clockValue_checkpointTape]
  rw [hdigits]
  simpa [incrementClockRow, E] using hvalue

private theorem beforeReady_reaches_machine
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source target :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpath : ReflTransGen (BeforeReadyStep M) source target) :
    LBA.Reaches (machine M) source target :=
  ReflTransGen.mono (fun _ _ hstep => hstep.1) hpath

/-- The first Ready checkpoint reached after taking a step out of a represented checkpoint is
exactly the incremented representation of the source successor selected by that first step. -/
public theorem first_ready_after_checkpoint
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    {after first :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hstep :
      LBA.Step (machine M) (checkpointCfg cfg digits trails) after)
    (hprefix : ReflTransGen (BeforeReadyStep M) after first)
    (hfirstReady : first.state.IsReady) :
    ∃ (sourceTarget : DLBA.Cfg (SourceAlpha T Γ) Λ n)
      (targetDigits : Fin (n + 1) → ClockDigit T Γ Λ)
      (targetTrails : ReadyTrails n),
      LBA.Step M cfg sourceTarget ∧
        List.ofFn targetDigits =
          (incrementClockRow M (List.ofFn digits)).1 ∧
        first =
          checkpointCfg sourceTarget targetDigits targetTrails := by
  obtain ⟨nextState, written, direction, hmove, hafter⟩ :=
    step_checkpoint_inv M cfg digits trails hstep
  subst after
  let sourceTarget : DLBA.Cfg (SourceAlpha T Γ) Λ n :=
    ⟨nextState, (cfg.tape.write written).moveHead direction⟩
  have hsourceStep : LBA.Step M cfg sourceTarget := by
    exact ⟨nextState, written, direction, hmove, rfl⟩
  have hactualReach :
      LBA.Reaches (machine M)
        (afterReadyCfg cfg digits trails nextState written direction) first :=
    beforeReady_reaches_machine M hprefix
  have hactualTrans :
      TransGen (LBA.Step (machine M))
        (checkpointCfg cfg digits trails) first :=
    TransGen.head' hstep hactualReach
  have hno :=
    incrementClockRow_noOverflow_of_ready_transGen M cfg digits trails
      hfirstReady hactualTrans
  obtain ⟨targetDigits, targetTrails, hdigits, hconstructed⟩ :=
    reaches_incremented_checkpoint_afterReady M cfg digits trails
      nextState written direction hno
  let predicted :=
    checkpointCfg sourceTarget targetDigits targetTrails
  have hafterNotReady :
      ¬(afterReadyCfg cfg digits trails nextState written direction).state.IsReady := by
    simp [afterReadyCfg, State.IsReady]
  have hpredictedReady : predicted.state.IsReady := by
    simp [predicted, checkpointCfg, State.IsReady]
  obtain ⟨constructedFirst, hconstructedPrefix, hconstructedReady,
      hconstructedSuffix⟩ :=
    reaches_split_first_ready M hafterNotReady hpredictedReady hconstructed
  have hconstructedFirst : constructedFirst = predicted := by
    rcases reflTransGen_iff_eq_or_transGen.mp hconstructedSuffix with
      heq | hstrict
    · exact heq.symm
    · have holdConstructed :
          TransGen (LBA.Step (machine M))
            (checkpointCfg cfg digits trails) constructedFirst :=
        TransGen.head' hstep
          (beforeReady_reaches_machine M hconstructedPrefix)
      have hgrowthOld :=
        ready_transGen_clockValue_lt M (by trivial)
          hconstructedReady holdConstructed
      have hgrowthNew :=
        ready_transGen_clockValue_lt M hconstructedReady
          hpredictedReady hstrict
      have hone :
          clockValue M predicted.tape =
            clockValue M (checkpointCfg cfg digits trails).tape + 1 := by
        exact clockValue_checkpoint_of_increment M cfg sourceTarget
          digits targetDigits trails targetTrails hno hdigits
      omega
  rw [hconstructedFirst] at hconstructedPrefix
  have hfirst : first = predicted :=
    beforeReady_ready_endpoint_unique M hfirstReady hpredictedReady
      hprefix hconstructedPrefix
  exact ⟨sourceTarget, targetDigits, targetTrails,
    hsourceStep, hdigits, hfirst⟩

/-- The first target step out of a represented Ready checkpoint enters the non-Ready `.mark`
phase. -/
public theorem step_checkpoint_target_not_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hstep :
      LBA.Step (machine M) (checkpointCfg cfg digits trails) target) :
    ¬target.state.IsReady := by
  obtain ⟨nextState, written, direction, _, htarget⟩ :=
    step_checkpoint_inv M cfg digits trails hstep
  rw [htarget]
  simp [afterReadyCfg, State.IsReady]

private theorem reflect_checkpoint_paths_of_measure
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    ∀ fuel : ℕ,
      ∀ {n : ℕ}
        (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
        (digits : Fin (n + 1) → ClockDigit T Γ Λ)
        (trails : ReadyTrails n)
        (target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n),
        LBA.StrictClockLayering.clockCapacity
              (Γ := SourceAlpha T Γ) (Λ := Λ) n -
            clockValue M (checkpointCfg source digits trails).tape =
          fuel →
        LBA.Reaches (machine M)
            (checkpointCfg source digits trails) target →
          target.state.IsReady →
            ∃ (sourceTarget : DLBA.Cfg (SourceAlpha T Γ) Λ n)
              (targetDigits : Fin (n + 1) → ClockDigit T Γ Λ)
              (targetTrails : ReadyTrails n),
              LBA.Reaches M source sourceTarget ∧
                target =
                  checkpointCfg sourceTarget targetDigits targetTrails := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro n source digits trails target hmeasure hpath htargetReady
      rcases ReflTransGen.cases_head hpath with
        heq | ⟨after, hstep, htail⟩
      · subst target
        exact ⟨source, digits, trails, .refl, rfl⟩
      · have hafterNotReady :=
          step_checkpoint_target_not_ready M source digits trails hstep
        obtain ⟨first, hfirstPrefix, hfirstReady, hfirstSuffix⟩ :=
          reaches_split_first_ready M hafterNotReady htargetReady htail
        obtain ⟨sourceNext, digitsNext, trailsNext, hsourceStep,
            _, hfirst⟩ :=
          first_ready_after_checkpoint M source digits trails
            hstep hfirstPrefix hfirstReady
        have hreturnTrans :
            TransGen (LBA.Step (machine M))
              (checkpointCfg source digits trails) first :=
          TransGen.head' hstep
            (beforeReady_reaches_machine M hfirstPrefix)
        have hgrowth :=
          ready_transGen_clockValue_lt M (by trivial)
            hfirstReady hreturnTrans
        rw [hfirst] at hgrowth
        rw [hfirst] at hfirstSuffix
        have hnextBound :=
          clockValue_lt_capacity M
            (checkpointCfg sourceNext digitsNext trailsNext).tape
        simp only [checkpointCfg] at hgrowth hnextBound hmeasure
        let nextFuel :=
          LBA.StrictClockLayering.clockCapacity
                (Γ := SourceAlpha T Γ) (Λ := Λ) n -
              clockValue M
                (checkpointCfg sourceNext digitsNext trailsNext).tape
        have hnextFuel : nextFuel < fuel := by
          dsimp [nextFuel]
          omega
        obtain ⟨sourceTarget, targetDigits, targetTrails,
            hsourceSuffix, htarget⟩ :=
          ih nextFuel hnextFuel sourceNext digitsNext trailsNext target
            (by rfl) hfirstSuffix htargetReady
        exact
          ⟨sourceTarget, targetDigits, targetTrails,
            (ReflTransGen.single hsourceStep).trans hsourceSuffix,
            htarget⟩

/-- Every Ready checkpoint reachable from a represented checkpoint represents a genuinely
source-reachable configuration. -/
public theorem machine_reflectsCheckpointPaths
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    ReflectsCheckpointPaths M := by
  intro n source digits trails target hpath htargetReady
  exact
    reflect_checkpoint_paths_of_measure M
      (LBA.StrictClockLayering.clockCapacity
          (Γ := SourceAlpha T Γ) (Λ := Λ) n -
        clockValue M (checkpointCfg source digits trails).tape)
      source digits trails target rfl hpath htargetReady

/-- The operational acyclic-clock compiler recognizes exactly the source machine's language. -/
public theorem languageEnd_machine_eq
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    LBA.LanguageEnd (machine M) = LBA.LanguageEnd M := by
  letI : Nonempty Λ := ⟨M.initial⟩
  exact languageEnd_machine_eq_of_simulation M
    (machine_simulatesClockedSteps M)
    (machine_reflectsCheckpointPaths M)

end LBA.AcyclicClock

end
