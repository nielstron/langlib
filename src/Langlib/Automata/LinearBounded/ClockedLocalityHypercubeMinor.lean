module

public import Langlib.Automata.LinearBounded.LocalityHypercubeMinor
public import Langlib.Automata.LinearBounded.StrictClockBranchSetMinor
import Mathlib.Tactic

@[expose]
public section

/-!
# Hypercube minors survive semantic strict clocking

The fixed locality machine already realizes every Boolean-cube edge.  Here we add one identity
`stay` instruction at every state/symbol pair, making its complete raw configuration relation
reflexive at every width.  The generic two-level branch-set construction can then contract the
two clock copies of each source configuration, and branch-set composition preserves the cube
minor.  Finally the exact first-two-layer embedding transports that certificate into the full
semantic strict clock.

Thus one fixed binary, two-state source machine has semantic strictly clocked configuration
graphs which are acyclic and contain Boolean-cube minors of every positive dimension.  This is
still not a theorem about the concrete one-tape clock compiler: its protocol corridors and
serializer contractions are separate obligations.
-/

namespace LBA.LocalityHypercube

/-- Add an explicit identity instruction to every local transition set of the fixed locality
machine.  Its state and tape alphabets remain `Phase` and `Bool`. -/
public def reflexiveMachine : LBA.Machine Bool Phase where
  transition state symbol :=
    Set.insert (state, symbol, .stay) (machine.transition state symbol)
  accept := machine.accept
  initial := machine.initial

/-- Every step of the original locality machine remains a step after adding identity
instructions. -/
public theorem step_reflexiveMachine_of_step {n : ℕ}
    {source target : DLBA.Cfg Bool Phase n}
    (hstep : LBA.Step machine source target) :
    LBA.Step reflexiveMachine source target := by
  rcases hstep with ⟨state, symbol, direction, htransition, rfl⟩
  exact ⟨state, symbol, direction, by
    exact Set.mem_insert_iff.mpr (Or.inr htransition), rfl⟩

/-- The augmented raw configuration relation is reflexive at every tape parameter, including
`n = 0` (a one-cell bounded tape). -/
public theorem step_reflexiveMachine_self {n : ℕ}
    (cfg : DLBA.Cfg Bool Phase n) :
    LBA.Step reflexiveMachine cfg cfg := by
  refine ⟨cfg.state, cfg.tape.read, .stay, ?_, ?_⟩
  · exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

/-- Adding the identity instructions preserves the original fixed-content branch sets and
their Boolean-cube minor. -/
public def reflexiveHypercubeBranchSetMinor (n : ℕ) :
    Relation.BranchSetMinorModel
      (CubeEdge (d := n + 1))
      (LBA.Step (n := n) reflexiveMachine) :=
  (hypercubeBranchSetMinor n).monoLarge step_reflexiveMachine_of_step

/-- Every positive-dimensional cube is a minor of the exact two-level strict unrolling of the
reflexive locality machine.  That two-level relation is acyclic. -/
public def twoLevelClockHypercubeBranchSetMinor (n : ℕ) :
    Relation.BranchSetMinorModel
      (CubeEdge (d := n + 1))
      (Relation.TwoLevelStrict.Edge
        (LBA.Step (n := n) reflexiveMachine)) :=
  (reflexiveHypercubeBranchSetMinor n).trans
    (Relation.TwoLevelStrict.branchSetMinorModel
      (LBA.Step (n := n) reflexiveMachine) step_reflexiveMachine_self)

/-- The preceding certificate transported to the first two layers of the full semantic strict
clock. -/
public def strictClockHypercubeBranchSetMinor (n : ℕ) :
    Relation.BranchSetMinorModel
      (CubeEdge (d := n + 1))
      (LBA.StrictClockLayering.ClockedStep (n := n) reflexiveMachine) :=
  (twoLevelClockHypercubeBranchSetMinor n).mapLargeEmbedding
    (Relation.TwoLevelStrict.intoLayered
      (V := DLBA.Cfg Bool Phase n))
    Relation.TwoLevelStrict.intoLayered_injective
    (fun {source target} hstep ↦
      (Relation.TwoLevelStrict.edge_iff_clockedStep
        reflexiveMachine source target).mp hstep)

/-- The complete full semantic strict-clock graph used above is acyclic, not merely the
represented cube subgraph. -/
public theorem strictClock_reflexiveMachine_acyclic (n : ℕ) :
    ∀ cfg : LBA.StrictClockLayering.ClockedCfg Bool Phase n,
      ¬ Relation.TransGen
        (LBA.StrictClockLayering.ClockedStep reflexiveMachine) cfg cfg :=
  LBA.StrictClockLayering.clockedStep_acyclic reflexiveMachine n

end LBA.LocalityHypercube

end
