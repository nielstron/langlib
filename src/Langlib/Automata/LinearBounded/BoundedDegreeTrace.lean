module

public import Langlib.Automata.LinearBounded.BoundedDegreeReachability
public import Langlib.Automata.LinearBounded.StepTraceCrossing

@[expose]
public section

/-!
# Concrete traces through the bounded-degree serializer

The simultaneous outgoing- and incoming-degree serializer preserves more than propositional
reachability.  Every concrete source trace has a canonical, noncomputably chosen concrete trace
between the corresponding base-ready configurations of the serialized machine.  The choice is
made separately for each source step and the resulting finite serializer runs are concatenated.

The canonical configuration embedding leaves the tape, and hence its head position, unchanged.
Consequently the lifted trace crosses every tape boundary at least as often as the source trace.
This statement is uniform in the tape width; at index `n = 0`, the boundary-indexed theorem is
vacuous because `Fin 0` is empty.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- The canonical bounded-degree configuration embedding preserves the complete bounded tape. -/
@[simp]
public theorem boundedDegreeLiftCfg_tape
    [Fintype Γ] [Fintype Λ] {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    (boundedDegreeLiftCfg cfg).tape = cfg.tape := rfl

/-- The canonical bounded-degree configuration embedding preserves the tape-head position. -/
@[simp]
public theorem boundedDegreeLiftCfg_head
    [Fintype Γ] [Fintype Λ] {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    (boundedDegreeLiftCfg cfg).tape.head = cfg.tape.head := rfl

/-- A single source step is simulated by a finite bounded-degree serializer run between
canonical configurations. -/
public theorem Machine.reaches_boundedDegreeLift_of_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hstep : Step M source target) :
    Reaches M.boundedDegree
      (boundedDegreeLiftCfg source) (boundedDegreeLiftCfg target) := by
  apply M.reaches_boundedDegreeLift_of_reaches
  exact Relation.ReflTransGen.single hstep

/-- Lift a concrete source trace through both degree-serialization stages.

Each source step is replaced by the concrete trace noncomputably selected from its serializer
reachability proof.  The definition is canonical relative to Lean's global classical choice.
-/
@[expose]
public noncomputable def Machine.boundedDegreeLiftTrace
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (trace : StepTrace M source target) :
  StepTrace M.boundedDegree
      (boundedDegreeLiftCfg source) (boundedDegreeLiftCfg target) :=
  StepTrace.liftByReach boundedDegreeLiftCfg
    (fun {_ _} hstep => M.reaches_boundedDegreeLift_of_step hstep) trace

/-- Forgetting the chosen lifted trace yields the corresponding bounded-degree reachability
fact automatically. -/
public theorem Machine.boundedDegreeLiftTrace_reaches
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (trace : StepTrace M source target) :
    Reaches M.boundedDegree
      (boundedDegreeLiftCfg source) (boundedDegreeLiftCfg target) :=
  (M.boundedDegreeLiftTrace trace).reaches

/-- Degree serialization cannot erase a tape-boundary crossing from a concrete source trace.

No nonemptiness or cardinality hypothesis is imposed on either alphabet.  For `n = 0` there is
no `b : Fin n`, so the fully quantified statement remains valid without a special case. -/
public theorem Machine.crossingCount_le_boundedDegreeLiftTrace
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (b : Fin n) (trace : StepTrace M source target) :
    StepTrace.crossingCount b trace ≤
      StepTrace.crossingCount b (M.boundedDegreeLiftTrace trace) := by
  exact StepTrace.crossingCount_le_liftByReach
    boundedDegreeLiftCfg
    (fun {_ _} hstep => M.reaches_boundedDegreeLift_of_step hstep)
    boundedDegreeLiftCfg_head b trace

end LBA

end
