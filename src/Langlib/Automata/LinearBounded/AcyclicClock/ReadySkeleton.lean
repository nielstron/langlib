module

public import Langlib.Automata.LinearBounded.AcyclicClock.MacroSoundness

@[expose]
public section

/-!
# The exact operational Ready-checkpoint skeleton

The concrete compiler performs many target-machine transitions for one source-machine step.  Its
observable skeleton is obtained by starting at a `ready` checkpoint, taking a source-choice
transition (the only protocol phase that can branch), and stopping at the first subsequent
`ready` configuration.

`FirstReadyMacroStep` records precisely that stopped run.  The main characterization below says
that, modulo the two intentionally irrelevant `ReadyTrails` tracks, this skeleton is exactly the
strict time-unrolling of the source machine: one genuine source step and one nonoverflowing clock
increment.  In particular, the statement does not claim that an arbitrary assignment of outgoing
trails is reachable.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- One complete operational macro, stopped at its first Ready endpoint.  The first transition is
separated because a represented Ready checkpoint is exactly where the source machine makes its
nondeterministic choice.  Every later transition in the prefix has a non-Ready source. -/
public def FirstReadyMacroStep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (source target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) : Prop :=
  ∃ after,
    LBA.Step (machine M) source after ∧
      ReflTransGen (BeforeReadyStep M) after target ∧
      target.state.IsReady

/-- The semantic strict source-clock edge represented by one operational macro. -/
public def StrictSourceClockStep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (sourceDigits : Fin (n + 1) → ClockDigit T Γ Λ)
    (target : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (targetDigits : Fin (n + 1) → ClockDigit T Γ Λ) : Prop :=
  LBA.Step M source target ∧
    (incrementClockRow M (List.ofFn sourceDigits)).2 = false ∧
    List.ofFn targetDigits =
      (incrementClockRow M (List.ofFn sourceDigits)).1

namespace FirstReadyMacroStep

/-- Forgetting the stopping predicate gives a nonempty target-machine path. -/
public theorem transGen
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hmacro : FirstReadyMacroStep M source target) :
    TransGen (LBA.Step (machine M)) source target := by
  rcases hmacro with ⟨after, hstep, hprefix, _⟩
  exact TransGen.head' hstep
    (ReflTransGen.mono (fun _ _ hbefore => hbefore.1) hprefix)

/-- A stopped macro ends in Ready by definition. -/
public theorem target_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hmacro : FirstReadyMacroStep M source target) :
    target.state.IsReady :=
  hmacro.choose_spec.2.2

end FirstReadyMacroStep

/-- Inversion of an arbitrary stopped first-Ready run.  It recovers the genuine source step, the
nonoverflowing increment, and an exact operational checkpoint endpoint with some recorded
outgoing Ready trails. -/
public theorem firstReadyMacroStep_checkpoint_inv
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hmacro :
      FirstReadyMacroStep M (checkpointCfg source digits trails) target) :
    ∃ (sourceTarget : DLBA.Cfg (SourceAlpha T Γ) Λ n)
      (targetDigits : Fin (n + 1) → ClockDigit T Γ Λ)
      (targetTrails : ReadyTrails n),
      LBA.Step M source sourceTarget ∧
        (incrementClockRow M (List.ofFn digits)).2 = false ∧
        List.ofFn targetDigits =
          (incrementClockRow M (List.ofFn digits)).1 ∧
        target = checkpointCfg sourceTarget targetDigits targetTrails := by
  rcases hmacro with ⟨after, hstep, hprefix, htargetReady⟩
  have hpath :
      TransGen (LBA.Step (machine M))
        (checkpointCfg source digits trails) target :=
    TransGen.head' hstep
      (ReflTransGen.mono (fun _ _ hbefore => hbefore.1) hprefix)
  have hno :=
    incrementClockRow_noOverflow_of_ready_transGen M source digits trails
      htargetReady hpath
  obtain ⟨sourceTarget, targetDigits, targetTrails,
      hsourceStep, hdigits, htarget⟩ :=
    first_ready_after_checkpoint M source digits trails
      hstep hprefix htargetReady
  exact ⟨sourceTarget, targetDigits, targetTrails,
    hsourceStep, hno, hdigits, htarget⟩

/-- Every stopped first-Ready macro advances the physical clock rank by exactly one.  The result
is independent of both the incoming and outgoing Ready trails. -/
public theorem FirstReadyMacroStep.clockValue_eq_add_one
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hmacro :
      FirstReadyMacroStep M (checkpointCfg source digits trails) target) :
    clockValue M target.tape =
      clockValue M (checkpointCfg source digits trails).tape + 1 := by
  obtain ⟨sourceTarget, targetDigits, targetTrails,
      _, hno, hdigits, htarget⟩ :=
    firstReadyMacroStep_checkpoint_inv M source digits trails hmacro
  rw [htarget]
  exact clockValue_checkpoint_of_increment M source sourceTarget
    digits targetDigits trails targetTrails hno hdigits

/-- Macro completeness strengthened to stop at the first Ready return.  For each source step and
nonoverflowing row, it constructs the exact returned checkpoint (including its actual outgoing
trail witness), not merely a path that may pass through earlier Ready states. -/
public theorem firstReadyMacroStep_checkpoint_of_source_step
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source sourceTarget : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (hsourceStep : LBA.Step M source sourceTarget)
    (hno : (incrementClockRow M (List.ofFn digits)).2 = false) :
    ∃ (targetDigits : Fin (n + 1) → ClockDigit T Γ Λ)
      (targetTrails : ReadyTrails n),
      List.ofFn targetDigits =
          (incrementClockRow M (List.ofFn digits)).1 ∧
        FirstReadyMacroStep M
          (checkpointCfg source digits trails)
          (checkpointCfg sourceTarget targetDigits targetTrails) := by
  obtain ⟨targetDigits, targetTrails, hdigits, hreach⟩ :=
    reaches_incremented_checkpoint_of_step M digits trails hsourceStep hno
  have hclock :
      clockValue M (checkpointCfg sourceTarget targetDigits targetTrails).tape =
        clockValue M (checkpointCfg source digits trails).tape + 1 :=
    clockValue_checkpoint_of_increment M source sourceTarget
      digits targetDigits trails targetTrails hno hdigits
  have hne :
      checkpointCfg source digits trails ≠
        checkpointCfg sourceTarget targetDigits targetTrails := by
    intro heq
    have hvalueEq := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n =>
        clockValue M cfg.tape) heq
    have hvalueLt :
        clockValue M (checkpointCfg source digits trails).tape <
          clockValue M
            (checkpointCfg sourceTarget targetDigits targetTrails).tape := by
      omega
    exact (Nat.ne_of_lt hvalueLt) hvalueEq
  rcases ReflTransGen.cases_head hreach with
    heq | ⟨after, hstep, htail⟩
  · exact (hne heq).elim
  · have hafterNotReady :=
      step_checkpoint_target_not_ready M source digits trails hstep
    have htargetReady :
        (checkpointCfg sourceTarget targetDigits targetTrails).state.IsReady := by
      simp [checkpointCfg, State.IsReady]
    obtain ⟨first, hprefix, hfirstReady, hsuffix⟩ :=
      reaches_split_first_ready M hafterNotReady htargetReady htail
    have hfirstEq :
        first = checkpointCfg sourceTarget targetDigits targetTrails := by
      rcases reflTransGen_iff_eq_or_transGen.mp hsuffix with
        heq | hstrict
      · exact heq.symm
      · have hstartFirst :
            TransGen (LBA.Step (machine M))
              (checkpointCfg source digits trails) first :=
          TransGen.head' hstep
            (ReflTransGen.mono (fun _ _ hbefore => hbefore.1) hprefix)
        have hgrowthStart :=
          ready_transGen_clockValue_lt M (by trivial)
            hfirstReady hstartFirst
        have hgrowthSuffix :=
          ready_transGen_clockValue_lt M hfirstReady
            htargetReady hstrict
        omega
    rw [hfirstEq] at hprefix
    exact ⟨targetDigits, targetTrails, hdigits,
      ⟨after, hstep, hprefix, htargetReady⟩⟩

/-- Existence of a first Ready return is equivalent to existence of a genuine source successor
and availability of the next fixed-width clock value. -/
public theorem firstReadyMacroStep_checkpoint_exists_iff
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    (∃ target,
        FirstReadyMacroStep M
          (checkpointCfg source digits trails) target) ↔
      (∃ sourceTarget, LBA.Step M source sourceTarget) ∧
        (incrementClockRow M (List.ofFn digits)).2 = false := by
  constructor
  · rintro ⟨target, hmacro⟩
    obtain ⟨sourceTarget, targetDigits, targetTrails,
        hstep, hno, _, _⟩ :=
      firstReadyMacroStep_checkpoint_inv M source digits trails hmacro
    exact ⟨⟨sourceTarget, hstep⟩, hno⟩
  · rintro ⟨⟨sourceTarget, hstep⟩, hno⟩
    obtain ⟨targetDigits, targetTrails, _, hmacro⟩ :=
      firstReadyMacroStep_checkpoint_of_source_step M digits trails
        hstep hno
    exact ⟨checkpointCfg sourceTarget targetDigits targetTrails, hmacro⟩

/-- **Exact Ready-skeleton theorem.**  After quotienting the irrelevant outgoing Ready trails via
`RepresentsCheckpoint`, the concrete first-Ready macro relation is precisely one strict
source-clock edge. -/
public theorem firstReadyMacroStep_represents_iff_strictSourceClockStep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (sourceDigits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (target : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (targetDigits : Fin (n + 1) → ClockDigit T Γ Λ) :
    (∃ operationalTarget,
        FirstReadyMacroStep M
            (checkpointCfg source sourceDigits trails) operationalTarget ∧
          RepresentsCheckpoint target targetDigits operationalTarget) ↔
      StrictSourceClockStep M source sourceDigits target targetDigits := by
  constructor
  · rintro ⟨operationalTarget, hmacro, hrep⟩
    obtain ⟨actualTarget, actualDigits, actualTrails,
        hstep, hno, hdigits, htarget⟩ :=
      firstReadyMacroStep_checkpoint_inv M source sourceDigits trails hmacro
    have hactualRep :
        RepresentsCheckpoint actualTarget actualDigits operationalTarget :=
      ⟨actualTrails, htarget⟩
    obtain ⟨htargetEq, hdigitsEq⟩ :=
      representsCheckpoint_source_clock_unique hrep hactualRep
    subst actualTarget
    subst actualDigits
    exact ⟨hstep, hno, hdigits⟩
  · rintro ⟨hstep, hno, hdigits⟩
    obtain ⟨actualDigits, actualTrails, hactualDigits, hmacro⟩ :=
      firstReadyMacroStep_checkpoint_of_source_step M sourceDigits trails
        hstep hno
    have hdigitsEq : actualDigits = targetDigits :=
      List.ofFn_injective (hactualDigits.trans hdigits.symm)
    subst actualDigits
    exact
      ⟨checkpointCfg target targetDigits actualTrails, hmacro,
        representsCheckpoint_checkpointCfg target targetDigits actualTrails⟩

end LBA.AcyclicClock

end
