module

public import Langlib.Automata.LinearBounded.AcyclicClock.Initialization
public import Langlib.Automata.LinearBounded.AcyclicClock.PhaseAcyclic
public import Langlib.Automata.LinearBounded.AcyclicClock.SemanticCheckpoint

@[expose]
public section

/-!
# Lifting one operational macro to complete semantic clock paths

This file isolates the relational induction needed after the concrete compiler proves one
source-step macro.  If every semantic strict-clock edge can be simulated between operational
checkpoints (with arbitrary incoming and existential outgoing Ready trails), then every semantic
clock path can be simulated.  As a first consequence, source acceptance implies acceptance from
the canonical compiled checkpoint.

The converse language direction still requires a macro soundness theorem.
-/

open Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

section Completeness

variable [Nonempty Λ]

/-- Operational completeness specification for one semantic strict-clock edge. -/
public def SimulatesClockedSteps
    (M : LBA.Machine (SourceAlpha T Γ) Λ) : Prop :=
  ∀ {n : ℕ}
    {old new :
      LBA.StrictClockLayering.ClockedCfg
        (SourceAlpha T Γ) Λ n},
    LBA.StrictClockLayering.ClockedStep M old new →
      ∀ trails : ReadyTrails n,
        ∃ nextTrails : ReadyTrails n,
          LBA.Reaches (machine M)
            (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ)
              n old trails)
            (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ)
              n new nextTrails)

/-- A one-edge operational simulation lifts to every reflexive-transitive semantic clock path. -/
public theorem reaches_semanticCheckpoint_of_clockedReaches
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hmacro : SimulatesClockedSteps M)
    {n : ℕ}
    {old new :
      LBA.StrictClockLayering.ClockedCfg
        (SourceAlpha T Γ) Λ n}
    (hpath :
      ReflTransGen
        (LBA.StrictClockLayering.ClockedStep M) old new)
    (trails : ReadyTrails n) :
    ∃ nextTrails : ReadyTrails n,
      LBA.Reaches (machine M)
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ)
          n old trails)
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ)
          n new nextTrails) := by
  induction hpath with
  | refl =>
      exact ⟨trails, ReflTransGen.refl⟩
  | @tail middle new hprefix hstep ih =>
      obtain ⟨middleTrails, hmiddle⟩ := ih
      obtain ⟨nextTrails, hnext⟩ := hmacro hstep middleTrails
      exact ⟨nextTrails, hmiddle.trans hnext⟩

/-- Macro completeness already gives the source-to-compiler acceptance direction from the
canonical zero-clock checkpoint. -/
public theorem accepts_machine_canonical_of_accepts
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hmacro : SimulatesClockedSteps M)
    {n : ℕ} (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (haccept : LBA.Accepts M source) :
    LBA.Accepts (machine M) (canonicalCfg M source) := by
  obtain ⟨target, htargetAccept, layer, hlayer, hclocked⟩ :=
    (LBA.StrictClockLayering.accepts_iff_exists_clocked_accept M source).1
      haccept
  obtain ⟨trails, hoperational⟩ :=
    reaches_semanticCheckpoint_of_clockedReaches M hmacro hclocked
      (ReadyTrails.clear n)
  let clockedTarget :=
    LBA.StrictClockLayering.atLayer target layer hlayer
  refine ⟨semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ)
      n clockedTarget trails, ?_, ?_⟩
  · rw [← semanticCheckpointCfg_bottom_clear M source]
    exact hoperational
  · change M.accept target.state = true
    exact htargetAccept

/-- With macro completeness, the compiled machine accepts every canonical input accepted by the
source machine. -/
public theorem accepts_machine_init_of_accepts
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hmacro : SimulatesClockedSteps M)
    (input : List T)
    (haccept : LBA.Accepts M (LBA.initCfgEnd M input)) :
    LBA.Accepts (machine M) (LBA.initCfgEnd (machine M) input) := by
  obtain ⟨target, hreach, htargetAccept⟩ :=
    accepts_machine_canonical_of_accepts M hmacro
      (LBA.initCfgEnd M input) haccept
  exact ⟨target,
    (reaches_canonicalCfg_init M input).trans hreach,
    htargetAccept⟩

/-- Macro completeness gives the forward language inclusion of the operational compiler. -/
public theorem languageEnd_subset_machine
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hmacro : SimulatesClockedSteps M) :
    ∀ input, LBA.LanguageEnd M input →
      LBA.LanguageEnd (machine M) input := by
  intro input hinput
  exact accepts_machine_init_of_accepts M hmacro input hinput

end Completeness

/-! ## Conditional soundness interface -/

/-- Soundness specification for arbitrary paths whose endpoints are Ready checkpoints.  Every
Ready endpoint reached from a represented source configuration must represent some genuinely
source-reachable configuration. -/
public def ReflectsCheckpointPaths
    (M : LBA.Machine (SourceAlpha T Γ) Λ) : Prop :=
  ∀ {n : ℕ}
    (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n),
    LBA.Reaches (machine M)
        (checkpointCfg source digits trails) target →
      target.state.IsReady →
        ∃ (sourceTarget : DLBA.Cfg (SourceAlpha T Γ) Λ n)
          (targetDigits : Fin (n + 1) → ClockDigit T Γ Λ)
          (targetTrails : ReadyTrails n),
          LBA.Reaches M source sourceTarget ∧
            target =
              checkpointCfg sourceTarget targetDigits targetTrails

/-- Checkpoint-path reflection gives the compiler-to-source acceptance direction from a canonical
compiled checkpoint. -/
public theorem accepts_of_accepts_machine_canonical
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hreflect : ReflectsCheckpointPaths M)
    {n : ℕ} (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (haccept : LBA.Accepts (machine M) (canonicalCfg M source)) :
    LBA.Accepts M source := by
  obtain ⟨target, hreach, htargetAccept⟩ := haccept
  have hready : target.state.IsReady := by
    obtain ⟨state, hstate, _⟩ :=
      (machine_accept_eq_true_iff M target.state).1 htargetAccept
    rw [hstate]
    trivial
  rw [canonicalCfg_eq_checkpointCfg_clear_zero M source] at hreach
  obtain ⟨sourceTarget, targetDigits, targetTrails,
      hsourceReach, htarget⟩ :=
    hreflect source (fun _ => clockZero M) (ReadyTrails.clear n)
      target hreach hready
  subst target
  exact ⟨sourceTarget, hsourceReach, htargetAccept⟩

end LBA.AcyclicClock

end
