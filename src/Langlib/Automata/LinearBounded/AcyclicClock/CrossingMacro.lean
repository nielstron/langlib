module

public import Langlib.Automata.LinearBounded.AcyclicClock.MacroCompleteness
public import Langlib.Automata.LinearBounded.AcyclicClock.SemanticCheckpoint
public import Langlib.Automata.LinearBounded.StepTraceCrossing

@[expose]
public section

/-!
# Boundary crossings in one operational clock macro

The completeness proof for the concrete acyclic clock factors a simulated source step through a
canonical right-boundary configuration.  This file retains that factorization as a concrete
`StepTrace`.  Consequently, when the source head starts at cell zero, one complete nonoverflowing
macro crosses every physical tape boundary at least once.

The statement is uniform in the tape width.  At width one (`n = 0`) there is no boundary, so the
crossing conclusion is vacuous; no positivity hypothesis or alphabet-cardinality assumption is
needed.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- A complete nonoverflowing operational macro, starting with the simulated head at cell zero,
has a concrete trace that crosses every tape boundary.  The output clock row is exactly the row
returned by `incrementClockRow`, just as in `reaches_incremented_checkpoint_of_step`.

The trace is deliberately assembled through `rightBoundaryCfg`: its prefix starts at physical
cell zero and ends at physical cell `n`, which forces a crossing of every `b : Fin n` independently
of the behavior of the remaining carry/return suffix. -/
public theorem exists_incremented_checkpoint_stepTrace_crosses_every_boundary
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {cfg cfg' : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (hstep : LBA.Step M cfg cfg')
    (hno : (incrementClockRow M (List.ofFn digits)).2 = false)
    (hhead : cfg.tape.head.val = 0) :
    ∃ (digits' : Fin (n + 1) → ClockDigit T Γ Λ)
      (trails' : ReadyTrails n)
      (trace : LBA.StepTrace (machine M)
        (checkpointCfg cfg digits trails)
        (checkpointCfg cfg' digits' trails')),
      List.ofFn digits' = (incrementClockRow M (List.ofFn digits)).1 ∧
      ∀ b : Fin n, 1 ≤ LBA.StepTrace.crossingCount b trace := by
  rcases exists_first_next_of_not_overflow M digits hno with
    ⟨stop, next, hbefore, hnext⟩
  let digits' := incrementedDigitsAt M digits stop next
  let trails' := completedTrails cfg'.tape stop
  let boundary := rightBoundaryCfg cfg' digits
  let toBoundary :
      LBA.StepTrace (machine M) (checkpointCfg cfg digits trails) boundary :=
    LBA.StepTrace.ofReaches
      (reaches_rightBoundary_checkpoint_of_step M digits trails hstep)
  have hsuffixReach :
      LBA.Reaches (machine M) boundary (checkpointCfg cfg' digits' trails') := by
    dsimp only [boundary]
    exact (reaches_carry_of_rightBoundary M cfg'.state cfg'.tape digits).trans
      (by
        simpa only [digits', trails'] using
          reaches_checkpoint_of_first_next M cfg'.state cfg'.tape digits stop next
            hbefore hnext)
  let suffix :
      LBA.StepTrace (machine M) boundary (checkpointCfg cfg' digits' trails') :=
    LBA.StepTrace.ofReaches hsuffixReach
  let trace := LBA.StepTrace.append toBoundary suffix
  refine ⟨digits', trails', trace, ?_, ?_⟩
  · have hinc := increment_of_first_next M digits stop next hbefore hnext
    exact (congrArg Prod.fst hinc).symm
  · intro b
    have hprefix : 1 ≤ LBA.StepTrace.crossingCount b toBoundary := by
      apply LBA.StepTrace.one_le_crossingCount_of_left_right b toBoundary
      · simp only [LBA.StepTrace.HeadAtOrLeft, checkpointCfg, checkpointTape]
        omega
      · simp only [LBA.StepTrace.HeadRight, boundary, rightBoundaryCfg,
          rightBoundaryTape]
        exact b.isLt
    simp only [trace, LBA.StepTrace.crossingCount_append]
    omega

/-- Semantic specialization of the concrete crossing macro.  Every strict clock edge whose
source simulated head is at cell zero has an operational trace between the exact semantic
checkpoints, with arbitrary incoming trails, existential outgoing trails, and at least one
crossing of each physical tape boundary. -/
public theorem exists_semanticCheckpoint_stepTrace_crosses_every_boundary
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    [Nonempty Λ]
    {n : ℕ}
    {old new :
      LBA.StrictClockLayering.ClockedCfg (SourceAlpha T Γ) Λ n}
    (hstep : LBA.StrictClockLayering.ClockedStep M old new)
    (trails : ReadyTrails n)
    (hhead : old.1.tape.head.val = 0) :
    ∃ (trails' : ReadyTrails n)
      (trace : LBA.StepTrace (machine M)
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ) n old trails)
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ) n new trails')),
      ∀ b : Fin n, 1 ≤ LBA.StepTrace.crossingCount b trace := by
  let oldDigits :=
    semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n old.2
  let newDigits :=
    semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n new.2
  have hincRaw :=
    increment_semanticDigits_of_clockedStep
      (T := T) (Γ := Γ) (Λ := Λ) M hstep
  have hinc :
      incrementClockRow M (List.ofFn oldDigits) =
        (List.ofFn newDigits, false) := by
    simpa [incrementClockRow, oldDigits, newDigits] using hincRaw
  have hno : (incrementClockRow M (List.ofFn oldDigits)).2 = false := by
    rw [hinc]
  obtain ⟨digits', trails', trace, hrow, hcross⟩ :=
    exists_incremented_checkpoint_stepTrace_crosses_every_boundary
      M oldDigits trails hstep.2 hno hhead
  have hrow' : List.ofFn digits' = List.ofFn newDigits :=
    hrow.trans (congrArg Prod.fst hinc)
  have hdigits : digits' = newDigits := List.ofFn_inj.mp hrow'
  subst digits'
  simpa only [semanticCheckpointCfg, oldDigits, newDigits] using
    (⟨trails', trace, hcross⟩ :
      ∃ (trails' : ReadyTrails n)
        (trace : LBA.StepTrace (machine M)
          (checkpointCfg old.1 oldDigits trails)
          (checkpointCfg new.1 newDigits trails')),
        ∀ b : Fin n, 1 ≤ LBA.StepTrace.crossingCount b trace)

end LBA.AcyclicClock

end
