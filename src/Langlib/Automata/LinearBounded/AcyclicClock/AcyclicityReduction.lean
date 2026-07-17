module

public import Langlib.Automata.LinearBounded.AcyclicBoundedDegree
public import Langlib.Automata.LinearBounded.AcyclicClock.CycleCriterion
public import Langlib.Automata.LinearBounded.AcyclicClock.EffectiveClock

@[expose]
public section

/-!
# Global acyclicity of the guarded clock compiler

The global proof splits cleanly into two independently checkable claims:

1. every target step whose endpoints are both outside `ready` strictly raises
   `phasePotential`; and
2. every nonempty path from one `ready` configuration to another strictly raises the complete
   physical `clockValue`.

The generic checkpoint criterion then rules out every cycle, including cycles through malformed
configurations.  The first two theorems package this implication for reuse.  `EffectiveClock`
discharges the Ready-to-Ready claim for the concrete transition table, yielding the final
unconditional `machine_configurationAcyclic` theorem below.
-/

open Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- The phase-local and Ready-to-Ready clock-growth claims imply global configuration acyclicity
of the concrete compiled machine. -/
public theorem machine_configurationAcyclic_of_ranks
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hphase :
      ∀ {n : ℕ}
        {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n},
        LBA.Step (machine M) old new →
          ¬ old.state.IsReady → ¬ new.state.IsReady →
            phasePotential old < phasePotential new)
    (hclock :
      ∀ {n : ℕ}
        {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n},
        old.state.IsReady → new.state.IsReady →
          TransGen (LBA.Step (machine M)) old new →
            clockValue M old.tape < clockValue M new.tape) :
    (machine M).ConfigurationAcyclic := by
  intro n cfg
  exact
    CycleCriterion.acyclic_of_checkpointRanks
      (LBA.Step (machine M))
      (fun target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n =>
        target.state.IsReady)
      phasePotential
      (fun hstep hold hnew => hphase hstep hold hnew)
      (fun target => clockValue M target.tape)
      (fun hold hnew hpath => hclock hold hnew hpath)
      cfg

/-- Once phase-local growth has been established separately, the sole remaining global obligation
is strict complete-clock growth on every nonempty Ready-to-Ready path. -/
public theorem machine_configurationAcyclic_of_ready_clock_growth
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hclock :
      ∀ {n : ℕ}
        {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n},
        old.state.IsReady → new.state.IsReady →
          TransGen (LBA.Step (machine M)) old new →
            clockValue M old.tape < clockValue M new.tape) :
    (machine M).ConfigurationAcyclic :=
  machine_configurationAcyclic_of_ranks M
    (fun hstep hold hnew =>
      nonready_step_phasePotential_lt M hstep hold hnew)
    hclock

/-- The concrete guarded clock compiler is globally configuration-acyclic at every tape width,
including on arbitrary malformed target configurations. -/
public theorem machine_configurationAcyclic
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    (machine M).ConfigurationAcyclic :=
  machine_configurationAcyclic_of_ready_clock_growth M
    (fun hold hnew hpath =>
      ready_transGen_clockValue_lt M hold hnew hpath)

end LBA.AcyclicClock

end
