module

public import Langlib.Automata.LinearBounded.BoundedDegree

@[expose]
public section

/-!
# Exact reachability through the bounded-degree serializer

The simultaneous degree serializer preserves and reflects reachability between canonical
configurations, not merely acceptance from an initial configuration.  Its canonical embedding
is the composition of the ready-state embedding for outgoing serialization and the base-state
embedding for incoming serialization.  Its projection composes the two corresponding global
projections.

The theorem is uniform in the tape width, including the one-cell bounded tape at index `0`.
-/

namespace LBA

open Classical

variable {Γ Λ : Type*}

/-- Embed an original configuration into the canonical base-ready phase of the simultaneous
outgoing- and incoming-edge serializer. -/
public def boundedDegreeLiftCfg
    [Fintype Γ] [Fintype Λ] {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg Γ (IncomingState Γ (BinaryBranchState Γ Λ)) n :=
  incomingLiftCfg (binaryLiftCfg cfg)

/-- Forget both serialization protocols in an arbitrary bounded-degree configuration. -/
public def boundedDegreeProjectCfg
    [Fintype Γ] [Fintype Λ] {n : ℕ}
    (cfg : DLBA.Cfg Γ (IncomingState Γ (BinaryBranchState Γ Λ)) n) :
    DLBA.Cfg Γ Λ n :=
  binaryProjectCfg (incomingProjectCfg cfg)

@[simp]
public theorem boundedDegreeProjectCfg_lift
    [Fintype Γ] [Fintype Λ] {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    boundedDegreeProjectCfg (boundedDegreeLiftCfg cfg) = cfg := rfl

/-- The canonical bounded-degree embedding never identifies original configurations. -/
public theorem boundedDegreeLiftCfg_injective
    [Fintype Γ] [Fintype Λ] {n : ℕ} :
    Function.Injective (boundedDegreeLiftCfg :
      DLBA.Cfg Γ Λ n →
        DLBA.Cfg Γ (IncomingState Γ (BinaryBranchState Γ Λ)) n) := by
  intro source target heq
  have := congrArg boundedDegreeProjectCfg heq
  simpa using this

@[simp]
public theorem boundedDegreeLiftCfg_inj
    [Fintype Γ] [Fintype Λ] {n : ℕ}
    {source target : DLBA.Cfg Γ Λ n} :
    boundedDegreeLiftCfg source = boundedDegreeLiftCfg target ↔
      source = target :=
  boundedDegreeLiftCfg_injective.eq_iff

/-- Every original run lifts through both degree-serialization stages. -/
public theorem Machine.reaches_boundedDegreeLift_of_reaches
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg Γ Λ n}
    (hreach : Reaches M source target) :
    Reaches M.boundedDegree
      (boundedDegreeLiftCfg source) (boundedDegreeLiftCfg target) := by
  exact M.binaryBranch.reaches_incomingLift_of_reaches
    (M.reaches_binaryLift_of_reaches hreach)

/-- Projecting a run of the simultaneous serializer yields a run of the original machine.
This is global and therefore also applies when either endpoint is an intermediate or malformed
serializer configuration. -/
public theorem Machine.reaches_boundedDegreeProjectCfg
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {source target :
      DLBA.Cfg Γ (IncomingState Γ (BinaryBranchState Γ Λ)) n}
    (hreach : Reaches M.boundedDegree source target) :
    Reaches M (boundedDegreeProjectCfg source)
      (boundedDegreeProjectCfg target) := by
  exact M.reaches_binaryProjectCfg
    (M.binaryBranch.reaches_incomingProjectCfg hreach)

/-- Exact all-pairs reachability preservation and reflection between canonical configurations
of a machine and its simultaneous bounded-degree serialization. -/
public theorem Machine.reaches_boundedDegreeLift_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg Γ Λ n} :
    Reaches M.boundedDegree
        (boundedDegreeLiftCfg source) (boundedDegreeLiftCfg target) ↔
      Reaches M source target := by
  constructor
  · intro hreach
    simpa using M.reaches_boundedDegreeProjectCfg hreach
  · exact M.reaches_boundedDegreeLift_of_reaches

end LBA

end
