module

public import Langlib.Automata.LinearBounded.ConcreteClockBoundedDegreeHypercubeMinor
public import Langlib.Automata.LinearBounded.IdentityClockCrossing
import Mathlib.Tactic

@[expose]
public section

/-!
# Exponential crossings in the fixed concrete locality machine

`ConcreteClockBoundedDegreeHypercubeMinor` exhibits one fixed clocked-and-serialized machine
whose width-`n` raw configuration graph contains the `(n+1)`-cube as an underlying-undirected
branch-set minor.  This file proves a directed trace statement about that *same definitionally
identical machine*.

The endmarked locality source has a self-loop at every raw configuration.  Repeating one such
self-loop through all exact semantic clock layers gives one actual operational trace crossing
every physical tape boundary at least once per successive layer advance.  Lifting that trace
through both degree serializers loses no crossings.  Since the source has two states and six
tape symbols, its width-`n` configuration space has exactly
`2 * 6 ^ (n + 1) * (n + 1)` elements.

This proves existence of one long trace in a nondeterministic machine.  It does not say that all
runs, accepting runs, or paths witnessing any language decision must have this crossing count.
At `n = 0` the trace still exists, while the assertion indexed by `Fin 0` is vacuous.
-/

namespace LBA.LocalityHypercube.ConcreteClock

open Classical

local instance : Nonempty Phase := ⟨.right⟩

/-! ## A canonical self-looping source configuration -/

/-- A canonical source tape with its head at physical cell zero.  Its contents are immaterial
for the inserted self-loop; choosing the left endmarker gives one explicit row at every width. -/
public def crossingSourceTape (n : ℕ) :
    DLBA.BoundedTape (LBA.AcyclicClock.SourceAlpha Unit Bool) n :=
  ⟨fun _ ↦ LBA.leftMark, ⟨0, Nat.zero_lt_succ n⟩⟩

/-- The source configuration whose self-loop is iterated through the complete concrete clock. -/
public def crossingSourceCfg (n : ℕ) :
    DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool) Phase n :=
  ⟨.right, crossingSourceTape n⟩

@[simp]
public theorem crossingSourceCfg_head (n : ℕ) :
    (crossingSourceCfg n).tape.head.val = 0 := rfl

/-- The chosen source configuration has the globally inserted identity transition. -/
public theorem crossingSourceCfg_step_self (n : ℕ) :
    LBA.Step endmarkedReflexiveMachine
      (crossingSourceCfg n) (crossingSourceCfg n) :=
  step_endmarkedReflexiveMachine_self _

/-! ## Crossing traces before and after degree serialization -/

/-- Before degree serialization, the complete concrete clock has a bottom-to-top trace with
`|Cfg|` successive layer advances, crossing every physical boundary at least once per advance. -/
public theorem exists_concreteClock_stepTrace_crosses_card (n : ℕ) :
    ∃ (trails : LBA.AcyclicClock.ReadyTrails n)
      (trace : LBA.StepTrace
        (LBA.AcyclicClock.machine endmarkedReflexiveMachine)
        (LBA.AcyclicClock.canonicalCfg endmarkedReflexiveMachine
          (crossingSourceCfg n))
        (LBA.AcyclicClock.semanticCheckpointCfg
          (T := Unit) (Γ := Bool) (Λ := Phase) n
          (LBA.StrictClockLayering.atLayer (crossingSourceCfg n)
            (Fintype.card
              (DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool) Phase n))
            (Nat.le_refl _)) trails)),
      ∀ b : Fin n,
        Fintype.card
            (DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool) Phase n) ≤
          LBA.StepTrace.crossingCount b trace := by
  have h :=
    LBA.AcyclicClock.exists_selfLoop_fullClock_stepTrace_crosses
      endmarkedReflexiveMachine (crossingSourceCfg n)
      (crossingSourceCfg_step_self n) (crossingSourceCfg_head n)
      (LBA.AcyclicClock.ReadyTrails.clear n)
  rw [LBA.AcyclicClock.semanticCheckpointCfg_bottom_clear
    endmarkedReflexiveMachine (crossingSourceCfg n)] at h
  exact h

/-- Lift the complete crossing trace through both actual degree serializers.  The machine in
this statement is definitionally the `boundedDegreeMachine` carrying the cube-minor certificate,
and no source crossing is lost. -/
public theorem exists_boundedDegreeMachine_stepTrace_crosses_card (n : ℕ) :
    ∃ (trails : LBA.AcyclicClock.ReadyTrails n)
      (trace : LBA.StepTrace boundedDegreeMachine
        (LBA.boundedDegreeLiftCfg
          (LBA.AcyclicClock.canonicalCfg endmarkedReflexiveMachine
            (crossingSourceCfg n)))
        (LBA.boundedDegreeLiftCfg
          (LBA.AcyclicClock.semanticCheckpointCfg
            (T := Unit) (Γ := Bool) (Λ := Phase) n
            (LBA.StrictClockLayering.atLayer (crossingSourceCfg n)
              (Fintype.card
                (DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool) Phase n))
              (Nat.le_refl _)) trails))),
      ∀ b : Fin n,
        Fintype.card
            (DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool) Phase n) ≤
          LBA.StepTrace.crossingCount b trace := by
  obtain ⟨trails, sourceTrace, hsource⟩ :=
    exists_concreteClock_stepTrace_crosses_card n
  let trace :=
    (LBA.AcyclicClock.machine endmarkedReflexiveMachine).boundedDegreeLiftTrace
      sourceTrace
  refine ⟨trails, trace, ?_⟩
  intro b
  exact (hsource b).trans
    (LBA.Machine.crossingCount_le_boundedDegreeLiftTrace
      (LBA.AcyclicClock.machine endmarkedReflexiveMachine) b sourceTrace)

/-! ## Closed-form exponential bounds for the exact same machine -/

/-- Exact size of the endmarked locality source's width-`n` configuration space. -/
public theorem card_crossingSourceCfgSpace (n : ℕ) :
    Fintype.card
        (DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool) Phase n) =
      2 * 6 ^ (n + 1) * (n + 1) := by
  have hphase : Fintype.card Phase = 2 := by
    let phaseEquivBool : Phase ≃ Bool :=
      { toFun := fun
          | .right => false
          | .left => true
        invFun := fun
          | false => .right
          | true => .left
        left_inv := by intro phase; cases phase <;> rfl
        right_inv := by intro bit; cases bit <;> rfl }
    calc
      Fintype.card Phase = Fintype.card Bool :=
        Fintype.card_congr phaseEquivBool
      _ = 2 := by decide
  rw [DLBA.card_cfg,
    LBA.AcyclicClock.IdentityCrossing.card_sourceAlpha_unit_bool, hphase]

/-- Exact source-configuration-count lower bound for the crossing trace in the fixed final
locality machine. -/
public theorem exists_boundedDegreeMachine_stepTrace_crosses_exact (n : ℕ) :
    ∃ (trails : LBA.AcyclicClock.ReadyTrails n)
      (trace : LBA.StepTrace boundedDegreeMachine
        (LBA.boundedDegreeLiftCfg
          (LBA.AcyclicClock.canonicalCfg endmarkedReflexiveMachine
            (crossingSourceCfg n)))
        (LBA.boundedDegreeLiftCfg
          (LBA.AcyclicClock.semanticCheckpointCfg
            (T := Unit) (Γ := Bool) (Λ := Phase) n
            (LBA.StrictClockLayering.atLayer (crossingSourceCfg n)
              (Fintype.card
                (DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool) Phase n))
              (Nat.le_refl _)) trails))),
      ∀ b : Fin n,
        2 * 6 ^ (n + 1) * (n + 1) ≤
          LBA.StepTrace.crossingCount b trace := by
  simpa only [card_crossingSourceCfgSpace] using
    exists_boundedDegreeMachine_stepTrace_crosses_card n

/-- In particular, the very same fixed machine whose raw graph contains the `(n+1)`-cube has
one width-`n` directed trace crossing every physical boundary at least `2 ^ (n + 1)` times. -/
public theorem exists_boundedDegreeMachine_stepTrace_crosses_twoPow (n : ℕ) :
    ∃ (trails : LBA.AcyclicClock.ReadyTrails n)
      (trace : LBA.StepTrace boundedDegreeMachine
        (LBA.boundedDegreeLiftCfg
          (LBA.AcyclicClock.canonicalCfg endmarkedReflexiveMachine
            (crossingSourceCfg n)))
        (LBA.boundedDegreeLiftCfg
          (LBA.AcyclicClock.semanticCheckpointCfg
            (T := Unit) (Γ := Bool) (Λ := Phase) n
            (LBA.StrictClockLayering.atLayer (crossingSourceCfg n)
              (Fintype.card
                (DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool) Phase n))
              (Nat.le_refl _)) trails))),
      ∀ b : Fin n,
        2 ^ (n + 1) ≤ LBA.StepTrace.crossingCount b trace := by
  obtain ⟨trails, trace, hcross⟩ :=
    exists_boundedDegreeMachine_stepTrace_crosses_exact n
  refine ⟨trails, trace, ?_⟩
  intro b
  apply le_trans ?_ (hcross b)
  calc
    2 ^ (n + 1) ≤ 6 ^ (n + 1) :=
      Nat.pow_le_pow_left (by omega) (n + 1)
    _ ≤ 2 * 6 ^ (n + 1) * (n + 1) := by
      calc
        6 ^ (n + 1) = 6 ^ (n + 1) * 1 := by omega
        _ ≤ 6 ^ (n + 1) * (2 * (n + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = 2 * 6 ^ (n + 1) * (n + 1) := by ring

end LBA.LocalityHypercube.ConcreteClock

end
