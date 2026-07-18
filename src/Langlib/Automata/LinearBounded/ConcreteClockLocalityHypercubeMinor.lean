module

public import Langlib.Automata.LinearBounded.ClockedLocalityHypercubeMinor
public import Langlib.Automata.LinearBounded.ConcreteClockBranchSetMinor
public import Langlib.Automata.LinearBounded.AcyclicClock.AcyclicityReduction
import Mathlib.Tactic

@[expose]
public section

/-!
# Hypercube minors inside the concrete acyclic-clock machine

The generic concrete corridor theorem expects a source machine over the canonical endmarker
alphabet.  This file supplies the missing alphabet bridge for the fixed locality-hypercube
machine.  Boolean cells are embedded as ordinary work symbols of `EndAlpha Unit Bool`; all other
endmarker-alphabet symbols receive an identity move.  On embedded Boolean configurations the
machine contains every transition of the reflexive locality machine, while its complete
configuration relation is reflexive.

Transporting the existing cube certificate through that embedding and composing it with
`concreteClockBranchSetMinorModel` puts every positive-dimensional Boolean cube inside the raw
configuration graph of one fixed concrete `AcyclicClock.machine`.  That raw graph is globally
acyclic.  This closes the clock-protocol contraction only; no degree-serializer image or
reachability lower bound is claimed.
-/

namespace LBA.LocalityHypercube.ConcreteClock

open Relation

/-- Embed one Boolean cell as an ordinary work symbol of the canonical endmarker alphabet. -/
@[expose]
public def embedBit (bit : Bool) : LBA.AcyclicClock.SourceAlpha Unit Bool :=
  .inl (some (.inr bit))

/-- The work-symbol embedding is injective. -/
public theorem embedBit_injective : Function.Injective embedBit := by
  intro left right heq
  simp [embedBit] at heq
  exact heq

/-- Embed a complete bounded Boolean tape without changing its physical head. -/
@[expose]
public def embedTape {n : ℕ} (tape : DLBA.BoundedTape Bool n) :
    DLBA.BoundedTape (LBA.AcyclicClock.SourceAlpha Unit Bool) n :=
  ⟨embedBit ∘ tape.contents, tape.head⟩

@[simp]
public theorem embedTape_read {n : ℕ} (tape : DLBA.BoundedTape Bool n) :
    (embedTape tape).read = embedBit tape.read := rfl

/-- Embedding commutes with a bounded-tape write. -/
public theorem embedTape_write {n : ℕ} (tape : DLBA.BoundedTape Bool n) (bit : Bool) :
    embedTape (tape.write bit) = (embedTape tape).write (embedBit bit) := by
  rcases tape with ⟨contents, head⟩
  apply congrArg (fun newContents ↦
    DLBA.BoundedTape.mk newContents head)
  funext index
  by_cases hindex : index = head
  · subst index
    simp [embedTape, DLBA.BoundedTape.write, Function.comp_apply]
  · simp [embedTape, DLBA.BoundedTape.write, Function.comp_apply, hindex]

/-- Embedding commutes with clamped head movement, including both boundary cases. -/
public theorem embedTape_moveHead {n : ℕ} (tape : DLBA.BoundedTape Bool n)
    (direction : DLBA.Dir) :
    embedTape (tape.moveHead direction) = (embedTape tape).moveHead direction := by
  cases direction <;> simp [embedTape, DLBA.BoundedTape.moveHead]

/-- Embed a complete locality-machine configuration. -/
@[expose]
public def embedCfg {n : ℕ} (cfg : DLBA.Cfg Bool LBA.LocalityHypercube.Phase n) :
    DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool)
      LBA.LocalityHypercube.Phase n :=
  ⟨cfg.state, embedTape cfg.tape⟩

/-- Configuration embedding is injective, including at tape parameter zero. -/
public theorem embedCfg_injective {n : ℕ} : Function.Injective (@embedCfg n) := by
  rintro ⟨leftState, ⟨leftContents, leftHead⟩⟩
    ⟨rightState, ⟨rightContents, rightHead⟩⟩ heq
  have hstate : leftState = rightState :=
    congrArg DLBA.Cfg.state heq
  have hhead : leftHead = rightHead :=
    congrArg (fun cfg ↦ cfg.tape.head) heq
  have hcontents : leftContents = rightContents := by
    funext index
    apply embedBit_injective
    exact congrFun (congrArg (fun cfg ↦ cfg.tape.contents) heq) index
  subst rightState
  subst rightHead
  subst rightContents
  rfl

/-- Source moves lifted from the Boolean locality machine at an embedded work symbol. -/
@[expose]
public def liftedMoves (state : LBA.LocalityHypercube.Phase)
    (symbol : LBA.AcyclicClock.SourceAlpha Unit Bool) :
    Set (LBA.LocalityHypercube.Phase ×
      LBA.AcyclicClock.SourceAlpha Unit Bool × DLBA.Dir) :=
  {move | ∃ oldBit nextState newBit direction,
    symbol = embedBit oldBit ∧
      (nextState, newBit, direction) ∈
        LBA.LocalityHypercube.reflexiveMachine.transition state oldBit ∧
      move = (nextState, embedBit newBit, direction)}

/-- Endmarker-alphabet version of the reflexive locality machine.  The explicit inserted stay
move makes every raw configuration self-loop, including configurations containing malformed or
endmarker symbols. -/
public def endmarkedReflexiveMachine :
    LBA.Machine (LBA.AcyclicClock.SourceAlpha Unit Bool)
      LBA.LocalityHypercube.Phase where
  transition state symbol :=
    Set.insert (state, symbol, .stay) (liftedMoves state symbol)
  accept := fun _ ↦ false
  initial := .right

/-- Every raw fixed-width configuration of the endmarked source machine has a self-loop. -/
public theorem step_endmarkedReflexiveMachine_self {n : ℕ}
    (cfg : DLBA.Cfg (LBA.AcyclicClock.SourceAlpha Unit Bool)
      LBA.LocalityHypercube.Phase n) :
    LBA.Step endmarkedReflexiveMachine cfg cfg := by
  refine ⟨cfg.state, cfg.tape.read, .stay, ?_, ?_⟩
  · exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

/-- Every transition of the reflexive Boolean locality machine is preserved by the complete
configuration embedding. -/
public theorem step_endmarkedReflexiveMachine_of_step {n : ℕ}
    {source destination : DLBA.Cfg Bool LBA.LocalityHypercube.Phase n}
    (hstep : LBA.Step LBA.LocalityHypercube.reflexiveMachine source destination) :
    LBA.Step endmarkedReflexiveMachine (embedCfg source) (embedCfg destination) := by
  rcases hstep with ⟨nextState, written, direction, htransition, rfl⟩
  refine ⟨nextState, embedBit written, direction, ?_, ?_⟩
  · apply Set.mem_insert_iff.mpr
    right
    exact ⟨source.tape.read, nextState, written, direction, rfl,
      htransition, rfl⟩
  · change
      embedCfg ⟨nextState, (source.tape.write written).moveHead direction⟩ =
        ⟨nextState,
          ((embedCfg source).tape.write (embedBit written)).moveHead direction⟩
    apply congrArg (fun tape ↦ DLBA.Cfg.mk nextState tape)
    rw [embedTape_moveHead, embedTape_write]
    simp [embedCfg]

/-! ## The concrete compiled cube certificate -/

/-- Transport the existing hypercube certificate into the canonical endmarker source alphabet. -/
public def endmarkedHypercubeBranchSetMinor (n : ℕ) :
    BranchSetMinorModel
      (LBA.LocalityHypercube.CubeEdge (d := n + 1))
      (LBA.Step (n := n) endmarkedReflexiveMachine) :=
  (LBA.LocalityHypercube.reflexiveHypercubeBranchSetMinor n).mapLargeEmbedding
    embedCfg embedCfg_injective step_endmarkedReflexiveMachine_of_step

/-- Every positive-dimensional Boolean cube is a branch-set minor of the raw configuration graph
of the actual one-tape acyclic-clock machine obtained from one fixed endmarked locality machine. -/
public def concreteClockHypercubeBranchSetMinor (n : ℕ) :
    BranchSetMinorModel
      (LBA.LocalityHypercube.CubeEdge (d := n + 1))
      (LBA.Step (n := n)
        (LBA.AcyclicClock.machine endmarkedReflexiveMachine)) :=
  (endmarkedHypercubeBranchSetMinor n).trans
    (LBA.AcyclicClock.concreteClockBranchSetMinorModel
      endmarkedReflexiveMachine step_endmarkedReflexiveMachine_self)

/-- The complete raw compiled configuration graph used above is globally acyclic at every tape
parameter, including arbitrary malformed protocol configurations. -/
public theorem concreteClock_endmarkedReflexiveMachine_acyclic (n : ℕ) :
    ∀ cfg : DLBA.Cfg
      (LBA.AcyclicClock.TapeAlpha Unit Bool LBA.LocalityHypercube.Phase)
      (LBA.AcyclicClock.State LBA.LocalityHypercube.Phase) n,
      ¬ TransGen
        (LBA.Step (LBA.AcyclicClock.machine endmarkedReflexiveMachine)) cfg cfg :=
  LBA.AcyclicClock.machine_configurationAcyclic endmarkedReflexiveMachine n

end LBA.LocalityHypercube.ConcreteClock

end
