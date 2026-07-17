module

public import Langlib.Automata.LinearBounded.AcyclicClock.MacroCompleteness
public import Langlib.Automata.LinearBounded.AcyclicClock.SimulationLift

@[expose]
public section

/-!
# Semantic strict-clock simulation by the operational macro

`MacroCompleteness` proves one operational macro for an arbitrary nonoverflowing digit row.
`SemanticCheckpoint` proves that every semantic strict-clock edge is exactly such an increment.
This file is the small adapter between those two interfaces.
-/

open Classical

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ] [Nonempty Λ]

/-- The concrete compiler simulates every semantic strict-clock edge between operational Ready
checkpoints, with arbitrary incoming and existential outgoing harmless trails. -/
public theorem machine_simulatesClockedSteps
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    SimulatesClockedSteps M := by
  intro n old new hstep trails
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
  have hno :
      (incrementClockRow M (List.ofFn oldDigits)).2 = false := by
    rw [hinc]
  obtain ⟨digits', nextTrails, hrow, hreach⟩ :=
    reaches_incremented_checkpoint_of_step M oldDigits trails hstep.2 hno
  have hrow' : List.ofFn digits' = List.ofFn newDigits := by
    exact hrow.trans (congrArg Prod.fst hinc)
  have hdigits : digits' = newDigits :=
    List.ofFn_inj.mp hrow'
  subst digits'
  refine ⟨nextTrails, ?_⟩
  simpa [semanticCheckpointCfg, oldDigits, newDigits] using hreach

/-- Consequently the operational compiler accepts every canonical source configuration accepted
by the source LBA. -/
public theorem accepts_machine_canonical_of_accepts_concrete
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (haccept : LBA.Accepts M source) :
    LBA.Accepts (machine M) (canonicalCfg M source) :=
  accepts_machine_canonical_of_accepts M (machine_simulatesClockedSteps M)
    source haccept

/-- Forward language inclusion for the concrete operational compiler. -/
public theorem languageEnd_subset_machine_concrete
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    ∀ input, LBA.LanguageEnd M input →
      LBA.LanguageEnd (machine M) input :=
  languageEnd_subset_machine M (machine_simulatesClockedSteps M)

end LBA.AcyclicClock

end
