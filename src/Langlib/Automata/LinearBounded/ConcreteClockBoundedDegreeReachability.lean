module

public import Langlib.Automata.LinearBounded.BoundedDegreeReachability
public import Langlib.Automata.LinearBounded.AcyclicClock.MacroSimulation
public import Langlib.Automata.LinearBounded.AcyclicClock.MacroSoundness

@[expose]
public section

/-!
# Exact reachability through the concrete clock-and-degree pipeline

The operational acyclic-clock compiler preserves arbitrary fixed-width source reachability
between a canonical zero-clock source and some represented checkpoint for the prescribed source
target.  Checkpoint reflection and uniqueness prove the converse.  Composing this exact statement
with the canonical reachability equivalence for the simultaneous degree serializer gives an
all-pairs theorem for the complete concrete pipeline, beyond its language-equivalence theorem.

The target clock row and harmless Ready trails are existential because different source paths can
have different lengths and the operational macro determines its outgoing trails.  No positive-
width premise is needed.
-/

open Classical

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]
variable [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]

/-- Every fixed-width source run reaches a bounded-degree lift of a represented checkpoint for
the prescribed source target.  The witness row is a canonical semantic clock row; the outgoing
Ready trails are those produced by the concrete operational macro. -/
public theorem reaches_boundedDegreeCheckpoint_of_reaches
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {source target : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (hreach : LBA.Reaches M source target) :
    ∃ (digits : Fin (n + 1) → ClockDigit T Γ Λ)
      (trails : ReadyTrails n),
      LBA.Reaches (machine M).boundedDegree
        (LBA.boundedDegreeLiftCfg (canonicalCfg M source))
        (LBA.boundedDegreeLiftCfg
          (checkpointCfg target digits trails)) := by
  letI : Nonempty Λ := ⟨M.initial⟩
  obtain ⟨layer, hlayer, hclocked⟩ :=
    (LBA.StrictClockLayering.reaches_iff_exists_clocked_reaches
      M source target).1 hreach
  obtain ⟨trails, hoperational⟩ :=
    reaches_semanticCheckpoint_of_clockedReaches M
      (machine_simulatesClockedSteps M) hclocked (ReadyTrails.clear n)
  let clockedTarget :=
    LBA.StrictClockLayering.atLayer target layer hlayer
  refine ⟨semanticDigits (T := T) (Γ := Γ) (Λ := Λ)
      n clockedTarget.2, trails, ?_⟩
  apply (machine M).reaches_boundedDegreeLift_of_reaches
  rw [semanticCheckpointCfg_bottom_clear M source] at hoperational
  simpa [clockedTarget, semanticCheckpointCfg,
    LBA.StrictClockLayering.atLayer] using hoperational

/-- Reaching any bounded-degree lift of a represented checkpoint for `target` reflects to a
genuine source run ending at that exact source configuration.  Neither the supplied clock row nor
the harmless Ready trails need to be canonical. -/
public theorem reaches_of_reaches_boundedDegreeCheckpoint
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {source target : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (hreach :
      LBA.Reaches (machine M).boundedDegree
        (LBA.boundedDegreeLiftCfg (canonicalCfg M source))
        (LBA.boundedDegreeLiftCfg
          (checkpointCfg target digits trails))) :
    LBA.Reaches M source target := by
  have hoperational :
      LBA.Reaches (machine M) (canonicalCfg M source)
        (checkpointCfg target digits trails) :=
    ((machine M).reaches_boundedDegreeLift_iff).1 hreach
  rw [canonicalCfg_eq_checkpointCfg_clear_zero M source] at hoperational
  obtain ⟨sourceTarget, targetDigits, targetTrails,
      hsourceReach, htarget⟩ :=
    machine_reflectsCheckpointPaths M source
      (fun _ => clockZero M) (ReadyTrails.clear n)
      (checkpointCfg target digits trails) hoperational (by
        simp [checkpointCfg, State.IsReady])
  have hgiven :
      RepresentsCheckpoint target digits
        (checkpointCfg target digits trails) :=
    representsCheckpoint_checkpointCfg target digits trails
  have hreflected :
      RepresentsCheckpoint sourceTarget targetDigits
        (checkpointCfg target digits trails) :=
    ⟨targetTrails, htarget⟩
  have htargetSource : target = sourceTarget :=
    (representsCheckpoint_source_clock_unique hgiven hreflected).1
  simpa only [← htargetSource] using hsourceReach

/-- **Exact all-pairs reachability theorem for the complete concrete pipeline.**  A source
configuration reaches a prescribed source target iff the actual clocked and degree-serialized
machine reaches some canonical serializer lift of a checkpoint representing that target.

The statement is uniform over all tape indices `n`, including `n = 0`, and imposes no lower bound
on either alphabet cardinality. -/
public theorem reaches_iff_exists_concreteClockBoundedDegreeCheckpoint
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source target : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    LBA.Reaches M source target ↔
      ∃ (digits : Fin (n + 1) → ClockDigit T Γ Λ)
        (trails : ReadyTrails n),
        LBA.Reaches (machine M).boundedDegree
          (LBA.boundedDegreeLiftCfg (canonicalCfg M source))
          (LBA.boundedDegreeLiftCfg
            (checkpointCfg target digits trails)) := by
  constructor
  · exact reaches_boundedDegreeCheckpoint_of_reaches M
  · rintro ⟨digits, trails, hreach⟩
    exact reaches_of_reaches_boundedDegreeCheckpoint M digits trails hreach

end LBA.AcyclicClock

end
