module

public import Langlib.Automata.LinearBounded.DeterministicSweeping.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Correctness of the deterministic sweeping compiler

This file proves that the machine from `DeterministicSweeping.Definition` initializes its
same-width encoded tape, simulates every source step by one positive-length endpoint-to-endpoint
macro, and preserves deterministic acceptance.  The construction concerns a deterministic
source machine only; it makes no claim about determinizing an arbitrary LBA.
-/

namespace DLBA.DeterministicSweeping

open Relation

universe u v w x y

variable {I : Type u} {Gamma : Type v} {Q : Type w}
  {Delta : Type x} {P : Type y}

public def leftIndex (n : Nat) : Fin (n + 1) :=
  ⟨0, Nat.zero_lt_succ n⟩

/-- Canonical converted cell representing one source configuration. -/
public def encodedCell {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (index : Fin (n + 1)) : Cell Gamma Q :=
  { left := decide (index.val = 0)
    right := decide (index.val = n)
    symbol := cfg.tape.contents index
    tag := if index = cfg.tape.head then .head cfg.state else .plain }

/-- Pointwise target-alphabet encoding of a source configuration. -/
public def encodedContents {n : Nat} (cfg : DLBA.Cfg Gamma Q n) :
    Fin (n + 1) → Alphabet I Gamma Q :=
  fun index => workSymbol (encodedCell cfg index)

/-- A converted source tape, with the simulator's physical head independently placed at
`physical`. -/
public def encodedTapeAt {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (physical : Fin (n + 1)) :
    DLBA.BoundedTape (Alphabet I Gamma Q) n :=
  ⟨fun index => workSymbol (encodedCell cfg index), physical⟩

/-- A simulator configuration over canonical encoded contents, at an arbitrary phase and
physical head position. -/
public def encodedCfgAt {n : Nat} (phase : Phase Q) (cfg : DLBA.Cfg Gamma Q n)
    (physical : Fin (n + 1)) :
    DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n :=
  ⟨phase, encodedTapeAt cfg physical⟩

/-- Canonical round boundary: the physical head is at the left endpoint and the next pass is
rightward. -/
public def roundCfg {n : Nat} (cfg : DLBA.Cfg Gamma Q n) :
    DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n :=
  encodedCfgAt .scanRight cfg (leftIndex n)

/-- Canonical query configuration reached when the rightward scan finds the simulated head. -/
public def queryCfg {n : Nat} (cfg : DLBA.Cfg Gamma Q n) :
    DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n :=
  encodedCfgAt (.query cfg.state) cfg cfg.tape.head

@[simp] theorem encodedCell_left {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (index : Fin (n + 1)) :
    (encodedCell cfg index).left = decide (index.val = 0) := rfl

@[simp] theorem encodedCell_right {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (index : Fin (n + 1)) :
    (encodedCell cfg index).right = decide (index.val = n) := rfl

@[simp] theorem encodedCell_symbol {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (index : Fin (n + 1)) :
    (encodedCell cfg index).symbol = cfg.tape.contents index := rfl

@[simp] theorem encodedCell_tag_head {n : Nat} (cfg : DLBA.Cfg Gamma Q n) :
    (encodedCell cfg cfg.tape.head).tag = .head cfg.state := by
  simp [encodedCell]

theorem encodedCell_tag_plain {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    {index : Fin (n + 1)} (hne : index ≠ cfg.tape.head) :
    (encodedCell cfg index).tag = .plain := by
  simp [encodedCell, hne]

@[simp] theorem encodedTapeAt_contents {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (physical index : Fin (n + 1)) :
    (encodedTapeAt (I := I) cfg physical).contents index =
      workSymbol (encodedCell cfg index) := rfl

@[simp] theorem encodedTapeAt_head {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (physical : Fin (n + 1)) :
    (encodedTapeAt (I := I) cfg physical).head = physical := rfl

public abbrev SimulatorStep (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat} :=
  fun left right : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n =>
    DLBA.step (machine M embed) left = some right

private theorem exists_pos_iterateStep_of_transGen
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    {source target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    (hreach : TransGen (SimulatorStep M embed) source target) :
    ∃ steps, 0 < steps ∧
      DLBA.iterateStep (machine M embed) source steps = some target := by
  induction hreach with
  | single hstep =>
      exact ⟨1, by omega, by simp [DLBA.iterateStep_succ, hstep]⟩
  | @tail middle target hreach hstep ih =>
      obtain ⟨steps, hpositive, hmiddle⟩ := ih
      refine ⟨steps + 1, by omega, ?_⟩
      rw [DLBA.iterateStep_succ, hmiddle]
      exact hstep

private theorem iterateStep_trans
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    {source middle target : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n}
    {first second : Nat}
    (hfirst : DLBA.iterateStep (machine M embed) source first = some middle)
    (hsecond : DLBA.iterateStep (machine M embed) middle second = some target) :
    DLBA.iterateStep (machine M embed) source (first + second) = some target := by
  rw [DLBA.iterateStep_add, hfirst]
  exact hsecond

private theorem step_scanRight_before_head
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (index : Fin (n + 1))
    (hbefore : index.val < cfg.tape.head.val) :
    SimulatorStep M embed
      (encodedCfgAt .scanRight cfg index)
      (encodedCfgAt .scanRight cfg ⟨index.val + 1, by omega⟩) := by
  have hne : index ≠ cfg.tape.head := by
    intro heq
    subst index
    omega
  have hlt : index.val < n := by
    have := cfg.tape.head.isLt
    omega
  have hnotRight : index.val ≠ n := by
    have := cfg.tape.head.isLt
    omega
  unfold SimulatorStep DLBA.step machine transition continueRight
  simp [encodedCfgAt, encodedTapeAt, encodedCell, hne, hnotRight, hlt,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_scanRight_at_head
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) :
    SimulatorStep M embed
      (encodedCfgAt .scanRight cfg cfg.tape.head)
      (queryCfg cfg) := by
  unfold SimulatorStep DLBA.step machine transition queryCfg
  simp [encodedCfgAt, encodedTapeAt, encodedCell,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem transGen_scanRight_to_query
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) :
    ∀ index : Fin (n + 1), index.val ≤ cfg.tape.head.val →
      TransGen (SimulatorStep M embed)
        (encodedCfgAt .scanRight cfg index) (queryCfg cfg) := by
  suffices H : ∀ distance, ∀ index : Fin (n + 1),
      index.val ≤ cfg.tape.head.val →
      cfg.tape.head.val - index.val = distance →
      TransGen (SimulatorStep M embed)
        (encodedCfgAt .scanRight cfg index) (queryCfg cfg) from
    fun index hle => H (cfg.tape.head.val - index.val) index hle rfl
  intro distance
  induction distance with
  | zero =>
      intro index hle hdistance
      have hval : index.val = cfg.tape.head.val := by omega
      have hindex : index = cfg.tape.head := Fin.ext hval
      subst index
      exact .single (step_scanRight_at_head M embed cfg)
  | succ distance ih =>
      intro index hle hdistance
      have hbefore : index.val < cfg.tape.head.val := by omega
      let next : Fin (n + 1) := ⟨index.val + 1, by
        have := cfg.tape.head.isLt
        omega⟩
      have hnextLe : next.val ≤ cfg.tape.head.val := by
        simp only [next]
        omega
      have hnextDistance : cfg.tape.head.val - next.val = distance := by
        simp only [next]
        omega
      exact TransGen.head
        (step_scanRight_before_head M embed cfg index hbefore)
        (ih next hnextLe hnextDistance)

/-- Every canonical round reaches its unique source-transition query by a nonempty rightward
scan. -/
public theorem roundCfg_transGen_queryCfg
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) :
    TransGen (SimulatorStep M embed) (roundCfg cfg) (queryCfg cfg) := by
  apply transGen_scanRight_to_query M embed cfg (leftIndex n)
  simp [leftIndex]

/-- Iteration form of `roundCfg_transGen_queryCfg`, retaining positivity of the scan length. -/
public theorem exists_pos_iterateStep_roundCfg_queryCfg
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) :
    ∃ steps, 0 < steps ∧
      DLBA.iterateStep (machine M embed) (roundCfg cfg) steps = some (queryCfg cfg) :=
  exists_pos_iterateStep_of_transGen M embed
    (roundCfg_transGen_queryCfg M embed cfg)

private theorem encodedContents_write_stay
    {n : Nat} (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma) :
    Function.update (encodedContents (I := I) cfg) cfg.tape.head
        (workSymbol ((encodedCell cfg cfg.tape.head).writeTagged symbol (.head next))) =
      encodedContents
        (I := I) (⟨next, (cfg.tape.write symbol).moveHead .stay⟩ : DLBA.Cfg Gamma Q n) := by
  funext index
  by_cases hindex : index = cfg.tape.head
  · subst index
    simp [encodedContents, encodedCell, Cell.writeTagged,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  · simp [encodedContents, encodedCell, Cell.writeTagged, hindex,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_query_stay_at_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .stay))
    (hright : cfg.tape.head.val = n) :
    SimulatorStep M embed (queryCfg cfg)
      (encodedCfgAt .scanLeft
        (⟨next, (cfg.tape.write symbol).moveHead .stay⟩ : DLBA.Cfg Gamma Q n)
        ((cfg.tape.write symbol).moveHead .left).head) := by
  have ht : M.transition cfg.state (cfg.tape.contents cfg.tape.head) =
      some (next, symbol, .stay) := by
    simpa [DLBA.BoundedTape.read] using htransition
  unfold SimulatorStep DLBA.step machine transition queryCfg encodedCfgAt encodedTapeAt
  simp [ht, encodedCell, hright, continueRight, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead]
  funext index
  by_cases hindex : index = cfg.tape.head
  · subst index
    simp [hright]
    constructor
    · intro hn
      apply Fin.ext
      omega
    · intro hhead
      have hzero : cfg.tape.head.val = 0 := by
        simpa using congrArg Fin.val hhead
      omega
  · simp [hindex]

private theorem step_query_stay_before_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .stay))
    (hbefore : cfg.tape.head.val < n) :
    SimulatorStep M embed (queryCfg cfg)
      (encodedCfgAt .scanRight
        (⟨next, (cfg.tape.write symbol).moveHead .stay⟩ : DLBA.Cfg Gamma Q n)
        ((cfg.tape.write symbol).moveHead .right).head) := by
  have ht : M.transition cfg.state (cfg.tape.contents cfg.tape.head) =
      some (next, symbol, .stay) := by
    simpa [DLBA.BoundedTape.read] using htransition
  unfold SimulatorStep DLBA.step machine transition queryCfg encodedCfgAt encodedTapeAt
  have hnotRight : cfg.tape.head.val ≠ n := by omega
  simp [ht, encodedCell, hnotRight, hbefore, continueRight, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead]
  funext index
  by_cases hindex : index = cfg.tape.head
  · subst index
    simp [hnotRight]
  · simp [hindex]

/-- The simulator configuration between clearing an old head marker and installing the marker
one cell to its right. -/
private def rightPendingCfg {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (next : Q) (symbol : Gamma) :
    DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n :=
  ⟨.putRight next,
    ⟨Function.update (encodedContents cfg) cfg.tape.head
        (workSymbol ((encodedCell cfg cfg.tape.head).writeTagged symbol .plain)),
      ((cfg.tape.write symbol).moveHead .right).head⟩⟩

private theorem encodedContents_write_right
    {n : Nat} (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hbefore : cfg.tape.head.val < n) :
    Function.update
        (rightPendingCfg (I := I) cfg next symbol).tape.contents
        ((cfg.tape.write symbol).moveHead .right).head
        (workSymbol
          ((encodedCell cfg ((cfg.tape.write symbol).moveHead .right).head).withTag
            (.head next))) =
      encodedContents
        (I := I) (⟨next, (cfg.tape.write symbol).moveHead .right⟩ : DLBA.Cfg Gamma Q n) := by
  let newHead : Fin (n + 1) := ((cfg.tape.write symbol).moveHead .right).head
  have hnewVal : newHead.val = cfg.tape.head.val + 1 := by
    simp [newHead, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hbefore]
  have hnewNe : newHead ≠ cfg.tape.head := by
    intro h
    have := congrArg Fin.val h
    omega
  have holdNe : cfg.tape.head ≠ newHead := Ne.symm hnewNe
  change Function.update
      (Function.update (encodedContents (I := I) cfg) cfg.tape.head
        (workSymbol ((encodedCell cfg cfg.tape.head).writeTagged symbol .plain)))
      newHead
      (workSymbol ((encodedCell cfg newHead).withTag (.head next))) =
    encodedContents
      (I := I) (⟨next, (cfg.tape.write symbol).moveHead .right⟩ : DLBA.Cfg Gamma Q n)
  funext index
  by_cases hnew : index = newHead
  · subst index
    simp [encodedContents, encodedCell, Cell.writeTagged, Cell.withTag,
      Function.update_apply, newHead, hbefore,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    intro heq
    have hval : cfg.tape.head.val + 1 = cfg.tape.head.val := by
      simpa using congrArg Fin.val heq
    omega
  · by_cases hold : index = cfg.tape.head
    · subst index
      simp [encodedContents, encodedCell, Cell.writeTagged, Cell.withTag,
        Function.update_apply, newHead, hbefore,
        DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      split
      · next heq =>
        have hval : cfg.tape.head.val = cfg.tape.head.val + 1 := by
          simpa using congrArg Fin.val heq
        omega
      · rfl
    · simp [encodedContents, encodedCell, Cell.writeTagged, Cell.withTag,
        Function.update_apply, newHead, hold, hbefore,
        DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      split
      · next heq =>
        exfalso
        apply hnew
        apply Fin.ext
        have hval := congrArg Fin.val heq
        simp at hval
        omega
      · rfl

private theorem encodedContents_write_right_clamped
    {n : Nat} (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hright : cfg.tape.head.val = n) :
    Function.update (encodedContents (I := I) cfg) cfg.tape.head
        (workSymbol ((encodedCell cfg cfg.tape.head).writeTagged symbol (.head next))) =
      encodedContents
        (I := I) (⟨next, (cfg.tape.write symbol).moveHead .right⟩ : DLBA.Cfg Gamma Q n) := by
  funext index
  by_cases hindex : index = cfg.tape.head
  · subst index
    simp [encodedContents, encodedCell, Cell.writeTagged, hright,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  · simp [encodedContents, encodedCell, Cell.writeTagged, hindex, hright,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_query_right_before_boundary
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .right))
    (hbefore : cfg.tape.head.val < n) :
    SimulatorStep M embed (queryCfg cfg) (rightPendingCfg cfg next symbol) := by
  have ht : M.transition cfg.state (cfg.tape.contents cfg.tape.head) =
      some (next, symbol, .right) := by
    simpa [DLBA.BoundedTape.read] using htransition
  have hnotRight : cfg.tape.head.val ≠ n := by omega
  unfold SimulatorStep DLBA.step machine transition queryCfg encodedCfgAt encodedTapeAt
    rightPendingCfg
  simp [ht, encodedCell, hnotRight, hbefore, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead]
  unfold encodedContents workSymbol encodedCell
  congr 1
  funext index
  simp

private theorem step_query_right_at_boundary
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .right))
    (hright : cfg.tape.head.val = n) :
    SimulatorStep M embed (queryCfg cfg)
      (encodedCfgAt .scanLeft
        (⟨next, (cfg.tape.write symbol).moveHead .right⟩ : DLBA.Cfg Gamma Q n)
        ((cfg.tape.write symbol).moveHead .left).head) := by
  have ht : M.transition cfg.state (cfg.tape.contents cfg.tape.head) =
      some (next, symbol, .right) := by
    simpa [DLBA.BoundedTape.read] using htransition
  unfold SimulatorStep DLBA.step machine transition queryCfg encodedCfgAt encodedTapeAt
  simp [ht, encodedCell, hright, continueRight, DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead]
  funext index
  by_cases hindex : index = cfg.tape.head
  · subst index
    simp [hright]
    constructor
    · intro hn
      apply Fin.ext
      omega
    · intro hhead
      have hzero : cfg.tape.head.val = 0 := by
        simpa using congrArg Fin.val hhead
      omega
  · simp [hindex]

private theorem rightPending_finish_tape
    {n : Nat} (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hbefore : cfg.tape.head.val < n) (direction : DLBA.Dir) :
    ((rightPendingCfg (I := I) cfg next symbol).tape.write
        (workSymbol
          ((encodedCell cfg ((cfg.tape.write symbol).moveHead .right).head).withTag
            (.head next)))).moveHead direction =
      encodedTapeAt
        (I := I) (⟨next, (cfg.tape.write symbol).moveHead .right⟩ : DLBA.Cfg Gamma Q n)
        (((cfg.tape.write symbol).moveHead .right).moveHead direction).head := by
  have hcontents := encodedContents_write_right (I := I) cfg next symbol hbefore
  cases direction <;>
    simp [rightPendingCfg, encodedTapeAt, DLBA.BoundedTape.write,
      DLBA.BoundedTape.moveHead] at hcontents ⊢
  all_goals simpa [encodedContents] using hcontents

private theorem step_putRight_at_boundary
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hbefore : cfg.tape.head.val < n)
    (hnewRight : ((cfg.tape.write symbol).moveHead .right).head.val = n) :
    SimulatorStep M embed (rightPendingCfg cfg next symbol)
      (encodedCfgAt .scanLeft
        (⟨next, (cfg.tape.write symbol).moveHead .right⟩ : DLBA.Cfg Gamma Q n)
        (((cfg.tape.write symbol).moveHead .right).moveHead .left).head) := by
  let newHead : Fin (n + 1) := ((cfg.tape.write symbol).moveHead .right).head
  have hnewNe : newHead ≠ cfg.tape.head := by
    intro h
    have hval := congrArg Fin.val h
    simp [newHead, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hbefore] at hval
  have hactualNe : ((cfg.tape.write symbol).moveHead .right).head ≠ cfg.tape.head := by
    simpa only [newHead] using hnewNe
  have hread : (rightPendingCfg (I := I) cfg next symbol).tape.read =
      workSymbol (encodedCell cfg newHead) := by
    unfold DLBA.BoundedTape.read rightPendingCfg
    simp [encodedContents, hactualNe, newHead]
  have htargetTransition :
      (machine M embed).transition (.putRight next)
          (workSymbol (encodedCell cfg newHead)) =
        some (.scanLeft,
          workSymbol ((encodedCell cfg newHead).withTag (.head next)), .left) := by
    simp [machine, transition, continueRight, encodedCell, newHead, hnewRight]
  unfold SimulatorStep DLBA.step
  rw [hread]
  rw [show (rightPendingCfg (I := I) cfg next symbol).state = .putRight next from rfl]
  rw [htargetTransition]
  simp only
  unfold encodedCfgAt
  dsimp only [newHead]
  exact congrArg
    (fun tape : DLBA.BoundedTape (Alphabet I Gamma Q) n =>
      some (DLBA.Cfg.mk Phase.scanLeft tape))
    (rightPending_finish_tape (I := I) cfg next symbol hbefore .left)

private theorem step_putRight_before_boundary
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hbefore : cfg.tape.head.val < n)
    (hnewBefore : ((cfg.tape.write symbol).moveHead .right).head.val < n) :
    SimulatorStep M embed (rightPendingCfg cfg next symbol)
      (encodedCfgAt .scanRight
        (⟨next, (cfg.tape.write symbol).moveHead .right⟩ : DLBA.Cfg Gamma Q n)
        (((cfg.tape.write symbol).moveHead .right).moveHead .right).head) := by
  let newHead : Fin (n + 1) := ((cfg.tape.write symbol).moveHead .right).head
  have hnewNe : newHead ≠ cfg.tape.head := by
    intro h
    have hval := congrArg Fin.val h
    simp [newHead, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hbefore] at hval
  have hactualNe : ((cfg.tape.write symbol).moveHead .right).head ≠ cfg.tape.head := by
    simpa only [newHead] using hnewNe
  have hread : (rightPendingCfg (I := I) cfg next symbol).tape.read =
      workSymbol (encodedCell cfg newHead) := by
    unfold DLBA.BoundedTape.read rightPendingCfg
    simp [encodedContents, hactualNe, newHead]
  have hnewNotRight : newHead.val ≠ n := by omega
  have htargetTransition :
      (machine M embed).transition (.putRight next)
          (workSymbol (encodedCell cfg newHead)) =
        some (.scanRight,
          workSymbol ((encodedCell cfg newHead).withTag (.head next)), .right) := by
    simp [machine, transition, continueRight, encodedCell, newHead, hnewNotRight]
  unfold SimulatorStep DLBA.step
  rw [hread]
  rw [show (rightPendingCfg (I := I) cfg next symbol).state = .putRight next from rfl]
  rw [htargetTransition]
  simp only
  unfold encodedCfgAt
  dsimp only [newHead]
  exact congrArg
    (fun tape : DLBA.BoundedTape (Alphabet I Gamma Q) n =>
      some (DLBA.Cfg.mk Phase.scanRight tape))
    (rightPending_finish_tape (I := I) cfg next symbol hbefore .right)

/-- The simulator configuration just before installing a head marker one cell to the left. -/
private def leftPendingCfg {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (next : Q) (symbol : Gamma) :
    DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n :=
  ⟨.putLeft next,
    ⟨Function.update (encodedContents cfg) cfg.tape.head
        (workSymbol ((encodedCell cfg cfg.tape.head).writeTagged symbol .plain)),
      ((cfg.tape.write symbol).moveHead .left).head⟩⟩

private theorem encodedContents_write_left
    {n : Nat} (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hpositive : 0 < cfg.tape.head.val) :
    Function.update
        (leftPendingCfg (I := I) cfg next symbol).tape.contents
        ((cfg.tape.write symbol).moveHead .left).head
        (workSymbol
          ((encodedCell cfg ((cfg.tape.write symbol).moveHead .left).head).withTag
            (.head next))) =
      encodedContents
        (I := I) (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n) := by
  let newHead : Fin (n + 1) := ((cfg.tape.write symbol).moveHead .left).head
  have hnewVal : newHead.val = cfg.tape.head.val - 1 := by
    simp [newHead, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hpositive]
  have hnewNe : newHead ≠ cfg.tape.head := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have holdNe : cfg.tape.head ≠ newHead := Ne.symm hnewNe
  change Function.update
      (Function.update (encodedContents (I := I) cfg) cfg.tape.head
        (workSymbol ((encodedCell cfg cfg.tape.head).writeTagged symbol .plain)))
      newHead
      (workSymbol ((encodedCell cfg newHead).withTag (.head next))) =
    encodedContents
      (I := I) (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n)
  funext index
  by_cases hnew : index = newHead
  · subst index
    simp [encodedContents, encodedCell, Cell.writeTagged, Cell.withTag,
      Function.update_apply, newHead, hpositive,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    intro heq
    have hval : cfg.tape.head.val - 1 = cfg.tape.head.val := by
      simpa using congrArg Fin.val heq
    omega
  · by_cases hold : index = cfg.tape.head
    · subst index
      simp [encodedContents, encodedCell, Cell.writeTagged, Cell.withTag,
        Function.update_apply, newHead, hpositive,
        DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      split
      · next heq =>
        have hval : cfg.tape.head.val = cfg.tape.head.val - 1 := by
          simpa using congrArg Fin.val heq
        omega
      · rfl
    · simp [encodedContents, encodedCell, Cell.writeTagged, Cell.withTag,
        Function.update_apply, newHead, hold, hpositive,
        DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
      split
      · next heq =>
        exfalso
        apply hnew
        apply Fin.ext
        have hval := congrArg Fin.val heq
        simp at hval
        omega
      · rfl

private theorem encodedContents_write_left_clamped
    {n : Nat} (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hleft : cfg.tape.head.val = 0) :
    Function.update (encodedContents (I := I) cfg) cfg.tape.head
        (workSymbol ((encodedCell cfg cfg.tape.head).writeTagged symbol (.head next))) =
      encodedContents
        (I := I) (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n) := by
  funext index
  by_cases hindex : index = cfg.tape.head
  · subst index
    simp [encodedContents, encodedCell, Cell.writeTagged, hleft,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  · simp [encodedContents, encodedCell, Cell.writeTagged, hindex, hleft,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_query_left_clamped_at_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .left))
    (hleft : cfg.tape.head.val = 0) (hright : cfg.tape.head.val = n) :
    SimulatorStep M embed (queryCfg cfg)
      (encodedCfgAt .scanLeft
        (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n)
        ((cfg.tape.write symbol).moveHead .left).head) := by
  have ht : M.transition cfg.state (cfg.tape.contents cfg.tape.head) =
      some (next, symbol, .left) := by
    simpa [DLBA.BoundedTape.read] using htransition
  have hnzero : n = 0 := by omega
  have hheadZero : cfg.tape.head = (0 : Fin (n + 1)) := Fin.ext hleft
  rw [hheadZero] at ht
  unfold SimulatorStep DLBA.step machine transition queryCfg encodedCfgAt encodedTapeAt
  simp [ht, encodedCell, hnzero, hheadZero, continueRight,
    DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead]
  funext index
  by_cases hindex : index = cfg.tape.head
  · subst index
    rw [hheadZero]
    simp
  · have hindexZero : index ≠ (0 : Fin (n + 1)) := by
      simpa [hheadZero] using hindex
    simp [hindexZero]

private theorem step_query_left_clamped_before_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .left))
    (hleft : cfg.tape.head.val = 0) (hbefore : cfg.tape.head.val < n) :
    SimulatorStep M embed (queryCfg cfg)
      (encodedCfgAt .scanRight
        (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n)
        ((cfg.tape.write symbol).moveHead .right).head) := by
  have ht : M.transition cfg.state (cfg.tape.contents cfg.tape.head) =
      some (next, symbol, .left) := by
    simpa [DLBA.BoundedTape.read] using htransition
  have hnotRight : cfg.tape.head.val ≠ n := by omega
  have hnpositive : 0 < n := by omega
  have hzeroNe : 0 ≠ n := by omega
  have hheadZero : cfg.tape.head = (0 : Fin (n + 1)) := Fin.ext hleft
  rw [hheadZero] at ht
  unfold SimulatorStep DLBA.step machine transition queryCfg encodedCfgAt encodedTapeAt
  simp [ht, encodedCell, hnpositive, hzeroNe, hheadZero,
    continueRight,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  funext index
  by_cases hindex : index = cfg.tape.head
  · subst index
    rw [hheadZero]
    simp [hzeroNe]
  · have hindexZero : index ≠ (0 : Fin (n + 1)) := by
      simpa [hheadZero] using hindex
    simp [hindexZero]

private theorem step_query_left_at_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .left))
    (hpositive : 0 < cfg.tape.head.val) (hright : cfg.tape.head.val = n) :
    SimulatorStep M embed (queryCfg cfg) (leftPendingCfg cfg next symbol) := by
  have ht : M.transition cfg.state (cfg.tape.contents cfg.tape.head) =
      some (next, symbol, .left) := by
    simpa [DLBA.BoundedTape.read] using htransition
  have hnotLeft : cfg.tape.head.val ≠ 0 := by omega
  have hnpositive : 0 < n := by omega
  have hnzeroNe : n ≠ 0 := by omega
  unfold SimulatorStep DLBA.step machine transition queryCfg encodedCfgAt encodedTapeAt
    leftPendingCfg
  simp [ht, encodedCell, hright, hnpositive, hnzeroNe,
    DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead]
  unfold encodedContents workSymbol encodedCell
  congr 1
  funext index
  simp

/-- Tape contents used while an interior source-left move is carried to the right endpoint and
back to its request marker. -/
private def leftRequestContents {n : Nat} (cfg : DLBA.Cfg Gamma Q n)
    (next : Q) (symbol : Gamma) : Fin (n + 1) → Alphabet I Gamma Q :=
  Function.update (encodedContents cfg) cfg.tape.head
    (workSymbol ((encodedCell cfg cfg.tape.head).writeTagged symbol (.needLeft next)))

private def leftRequestCfgAt {n : Nat} (phase : Phase Q)
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (physical : Fin (n + 1)) : DLBA.Cfg (Alphabet I Gamma Q) (Phase Q) n :=
  ⟨phase, ⟨leftRequestContents cfg next symbol, physical⟩⟩

private theorem step_query_left_interior
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .left))
    (hpositive : 0 < cfg.tape.head.val) (hbefore : cfg.tape.head.val < n) :
    SimulatorStep M embed (queryCfg cfg)
      (leftRequestCfgAt .scanRight cfg next symbol
        ((cfg.tape.write symbol).moveHead .right).head) := by
  have ht : M.transition cfg.state (cfg.tape.contents cfg.tape.head) =
      some (next, symbol, .left) := by
    simpa [DLBA.BoundedTape.read] using htransition
  have hnotLeft : cfg.tape.head.val ≠ 0 := by omega
  have hnotRight : cfg.tape.head.val ≠ n := by omega
  unfold SimulatorStep DLBA.step machine transition queryCfg encodedCfgAt encodedTapeAt
    leftRequestCfgAt leftRequestContents
  simp [ht, encodedCell, hnotLeft, hnotRight, hbefore, continueRight,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  unfold encodedContents workSymbol encodedCell
  congr 1
  funext index
  simp

private theorem step_request_scanRight_before_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (index : Fin (n + 1)) (hafter : cfg.tape.head.val < index.val)
    (hbefore : index.val < n) :
    SimulatorStep M embed
      (leftRequestCfgAt .scanRight cfg next symbol index)
      (leftRequestCfgAt .scanRight cfg next symbol ⟨index.val + 1, by omega⟩) := by
  have hne : index ≠ cfg.tape.head := by
    intro h
    subst index
    omega
  have hnotRight : index.val ≠ n := by omega
  unfold SimulatorStep DLBA.step machine transition leftRequestCfgAt leftRequestContents
    continueRight
  simp [hne, encodedContents, encodedCell, hnotRight, hbefore,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_request_scanRight_at_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (index : Fin (n + 1)) (hafter : cfg.tape.head.val < index.val)
    (hright : index.val = n) :
    SimulatorStep M embed
      (leftRequestCfgAt .scanRight cfg next symbol index)
      (leftRequestCfgAt .scanLeft cfg next symbol ⟨index.val - 1, by omega⟩) := by
  have hne : index ≠ cfg.tape.head := by
    intro h
    subst index
    omega
  have hnpositive : 0 < n := by omega
  unfold SimulatorStep DLBA.step machine transition leftRequestCfgAt leftRequestContents
    continueRight
  simp [hne, encodedContents, encodedCell, hright, hnpositive,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_request_scanLeft_above_request
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (index : Fin (n + 1)) (hafter : cfg.tape.head.val < index.val) :
    SimulatorStep M embed
      (leftRequestCfgAt .scanLeft cfg next symbol index)
      (leftRequestCfgAt .scanLeft cfg next symbol ⟨index.val - 1, by omega⟩) := by
  have hne : index ≠ cfg.tape.head := by
    intro h
    subst index
    omega
  have hpositive : 0 < index.val := by omega
  have hnotLeft : index.val ≠ 0 := by omega
  unfold SimulatorStep DLBA.step machine transition leftRequestCfgAt leftRequestContents
    continueLeft
  simp [hne, encodedContents, encodedCell, hnotLeft, hpositive,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_request_scanLeft_at_request
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hpositive : 0 < cfg.tape.head.val) :
    SimulatorStep M embed
      (leftRequestCfgAt .scanLeft cfg next symbol cfg.tape.head)
      (leftPendingCfg cfg next symbol) := by
  unfold SimulatorStep DLBA.step machine transition leftRequestCfgAt leftRequestContents
    leftPendingCfg
  simp [encodedCell, Cell.writeTagged, Cell.withTag, hpositive,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem transGen_request_scanLeft_to_pending
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hpositive : 0 < cfg.tape.head.val) :
    ∀ index : Fin (n + 1), cfg.tape.head.val ≤ index.val →
      TransGen (SimulatorStep M embed)
        (leftRequestCfgAt .scanLeft cfg next symbol index)
        (leftPendingCfg cfg next symbol) := by
  suffices H : ∀ distance, ∀ index : Fin (n + 1),
      cfg.tape.head.val ≤ index.val → index.val - cfg.tape.head.val = distance →
      TransGen (SimulatorStep M embed)
        (leftRequestCfgAt .scanLeft cfg next symbol index)
        (leftPendingCfg cfg next symbol) from
    fun index hle => H (index.val - cfg.tape.head.val) index hle rfl
  intro distance
  induction distance with
  | zero =>
      intro index hle hdistance
      have hval : index.val = cfg.tape.head.val := by omega
      have hindex : index = cfg.tape.head := Fin.ext hval
      subst index
      exact .single (step_request_scanLeft_at_request M embed cfg next symbol hpositive)
  | succ distance ih =>
      intro index hle hdistance
      have hafter : cfg.tape.head.val < index.val := by omega
      let previous : Fin (n + 1) := ⟨index.val - 1, by omega⟩
      have hpreviousLe : cfg.tape.head.val ≤ previous.val := by
        simp only [previous]
        omega
      have hpreviousDistance : previous.val - cfg.tape.head.val = distance := by
        simp only [previous]
        omega
      exact TransGen.head
        (step_request_scanLeft_above_request M embed cfg next symbol index hafter)
        (ih previous hpreviousLe hpreviousDistance)

private theorem transGen_request_scanRight_to_pending
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hpositive : 0 < cfg.tape.head.val) :
    ∀ index : Fin (n + 1), cfg.tape.head.val < index.val →
      TransGen (SimulatorStep M embed)
        (leftRequestCfgAt .scanRight cfg next symbol index)
        (leftPendingCfg cfg next symbol) := by
  suffices H : ∀ distance, ∀ index : Fin (n + 1),
      cfg.tape.head.val < index.val → n - index.val = distance →
      TransGen (SimulatorStep M embed)
        (leftRequestCfgAt .scanRight cfg next symbol index)
        (leftPendingCfg cfg next symbol) from
    fun index hafter => H (n - index.val) index hafter rfl
  intro distance
  induction distance with
  | zero =>
      intro index hafter hdistance
      have hright : index.val = n := by
        have := index.isLt
        omega
      have hboundary :=
        step_request_scanRight_at_right M embed cfg next symbol index hafter hright
      have hpreviousLe : cfg.tape.head.val ≤ index.val - 1 := by omega
      exact TransGen.head hboundary
        (transGen_request_scanLeft_to_pending M embed cfg next symbol hpositive
          ⟨index.val - 1, by omega⟩ hpreviousLe)
  | succ distance ih =>
      intro index hafter hdistance
      have hbefore : index.val < n := by omega
      let following : Fin (n + 1) := ⟨index.val + 1, by omega⟩
      have hfollowingAfter : cfg.tape.head.val < following.val := by
        simp only [following]
        omega
      have hfollowingDistance : n - following.val = distance := by
        simp only [following]
        omega
      exact TransGen.head
        (step_request_scanRight_before_right M embed cfg next symbol index hafter hbefore)
        (ih following hfollowingAfter hfollowingDistance)

private theorem leftPending_finish_tape
    {n : Nat} (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hpositive : 0 < cfg.tape.head.val) (direction : DLBA.Dir) :
    ((leftPendingCfg (I := I) cfg next symbol).tape.write
        (workSymbol
          ((encodedCell cfg ((cfg.tape.write symbol).moveHead .left).head).withTag
            (.head next)))).moveHead direction =
      encodedTapeAt
        (I := I) (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n)
        (((cfg.tape.write symbol).moveHead .left).moveHead direction).head := by
  have hcontents := encodedContents_write_left (I := I) cfg next symbol hpositive
  cases direction <;>
    simp [leftPendingCfg, encodedTapeAt, DLBA.BoundedTape.write,
      DLBA.BoundedTape.moveHead] at hcontents ⊢
  all_goals simpa [encodedContents] using hcontents

private theorem step_putLeft_at_left
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hpositive : 0 < cfg.tape.head.val)
    (hnewLeft : ((cfg.tape.write symbol).moveHead .left).head.val = 0) :
    SimulatorStep M embed (leftPendingCfg cfg next symbol)
      (encodedCfgAt .scanRight
        (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n)
        ((cfg.tape.write symbol).moveHead .left).head) := by
  let newHead : Fin (n + 1) := ((cfg.tape.write symbol).moveHead .left).head
  have hactualNe : ((cfg.tape.write symbol).moveHead .left).head ≠ cfg.tape.head := by
    intro h
    have hval := congrArg Fin.val h
    simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hpositive] at hval
    omega
  have hread : (leftPendingCfg (I := I) cfg next symbol).tape.read =
      workSymbol (encodedCell cfg newHead) := by
    unfold DLBA.BoundedTape.read leftPendingCfg
    simp [encodedContents, hactualNe, newHead]
  have htargetTransition :
      (machine M embed).transition (.putLeft next)
          (workSymbol (encodedCell cfg newHead)) =
        some (.scanRight,
          workSymbol ((encodedCell cfg newHead).withTag (.head next)), .stay) := by
    simp [machine, transition, continueLeft, encodedCell, newHead, hnewLeft]
  unfold SimulatorStep DLBA.step
  rw [hread]
  rw [show (leftPendingCfg (I := I) cfg next symbol).state = .putLeft next from rfl]
  rw [htargetTransition]
  simp only
  unfold encodedCfgAt
  dsimp only [newHead]
  exact congrArg
    (fun tape : DLBA.BoundedTape (Alphabet I Gamma Q) n =>
      some (DLBA.Cfg.mk Phase.scanRight tape))
    (leftPending_finish_tape (I := I) cfg next symbol hpositive .stay)

private theorem step_putLeft_above_left
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hpositive : 0 < cfg.tape.head.val)
    (hnewPositive : 0 < ((cfg.tape.write symbol).moveHead .left).head.val) :
    SimulatorStep M embed (leftPendingCfg cfg next symbol)
      (encodedCfgAt .scanLeft
        (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n)
        (((cfg.tape.write symbol).moveHead .left).moveHead .left).head) := by
  let newHead : Fin (n + 1) := ((cfg.tape.write symbol).moveHead .left).head
  have hactualNe : ((cfg.tape.write symbol).moveHead .left).head ≠ cfg.tape.head := by
    intro h
    have hval := congrArg Fin.val h
    simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hpositive] at hval
    omega
  have hread : (leftPendingCfg (I := I) cfg next symbol).tape.read =
      workSymbol (encodedCell cfg newHead) := by
    unfold DLBA.BoundedTape.read leftPendingCfg
    simp [encodedContents, hactualNe, newHead]
  have hnewNotLeft : newHead.val ≠ 0 := by omega
  have htargetTransition :
      (machine M embed).transition (.putLeft next)
          (workSymbol (encodedCell cfg newHead)) =
        some (.scanLeft,
          workSymbol ((encodedCell cfg newHead).withTag (.head next)), .left) := by
    simp [machine, transition, continueLeft, encodedCell, newHead, hnewNotLeft]
  unfold SimulatorStep DLBA.step
  rw [hread]
  rw [show (leftPendingCfg (I := I) cfg next symbol).state = .putLeft next from rfl]
  rw [htargetTransition]
  simp only
  unfold encodedCfgAt
  dsimp only [newHead]
  exact congrArg
    (fun tape : DLBA.BoundedTape (Alphabet I Gamma Q) n =>
      some (DLBA.Cfg.mk Phase.scanLeft tape))
    (leftPending_finish_tape (I := I) cfg next symbol hpositive .left)

private theorem step_scanLeft_positive
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (index : Fin (n + 1))
    (hpositive : 0 < index.val) :
    SimulatorStep M embed
      (encodedCfgAt .scanLeft cfg index)
      (encodedCfgAt .scanLeft cfg ⟨index.val - 1, by omega⟩) := by
  have hnotLeft : index.val ≠ 0 := by omega
  have hnotLeftFin : index ≠ (0 : Fin (n + 1)) := by
    intro hindex
    apply hnotLeft
    change index.val = 0
    exact congrArg Fin.val hindex
  unfold SimulatorStep DLBA.step machine transition continueLeft
  by_cases hhead : index = cfg.tape.head
  · have hcfgNotLeft : cfg.tape.head ≠ (0 : Fin (n + 1)) := by
      rw [← hhead]
      exact hnotLeftFin
    have hcfgPositive : 0 < cfg.tape.head.val := by
      rw [← hhead]
      exact hpositive
    simp [encodedCfgAt, encodedTapeAt, encodedCell, hhead, hcfgNotLeft, hcfgPositive,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  · simp [encodedCfgAt, encodedTapeAt, encodedCell, hhead, hnotLeftFin, hpositive,
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_scanLeft_zero
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (index : Fin (n + 1))
    (hzero : index.val = 0) :
    SimulatorStep M embed
      (encodedCfgAt .scanLeft cfg index)
      (roundCfg cfg) := by
  have hindex : index = leftIndex n := Fin.ext (by simpa [leftIndex] using hzero)
  subst index
  unfold SimulatorStep DLBA.step machine transition continueLeft roundCfg
  by_cases hhead : leftIndex n = cfg.tape.head
  · have hhead' : (0 : Fin (n + 1)) = cfg.tape.head := by
      simpa [leftIndex] using hhead
    simp [encodedCfgAt, encodedTapeAt, encodedCell, leftIndex, hhead',
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  · have hhead' : (0 : Fin (n + 1)) ≠ cfg.tape.head := by
      simpa [leftIndex] using hhead
    simp [encodedCfgAt, encodedTapeAt, encodedCell, leftIndex, hhead',
      DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem transGen_scanLeft_to_round
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) :
    ∀ index : Fin (n + 1),
      TransGen (SimulatorStep M embed)
        (encodedCfgAt .scanLeft cfg index) (roundCfg cfg) := by
  suffices H : ∀ value, ∀ index : Fin (n + 1), index.val = value →
      TransGen (SimulatorStep M embed)
        (encodedCfgAt .scanLeft cfg index) (roundCfg cfg) from
    fun index => H index.val index rfl
  intro value
  induction value with
  | zero =>
      intro index hvalue
      exact .single (step_scanLeft_zero M embed cfg index hvalue)
  | succ value ih =>
      intro index hvalue
      have hpositive : 0 < index.val := by omega
      let previous : Fin (n + 1) := ⟨index.val - 1, by omega⟩
      have hprevious : previous.val = value := by
        simp only [previous]
        omega
      exact TransGen.head
        (step_scanLeft_positive M embed cfg index hpositive)
        (ih previous hprevious)

private theorem step_scanRight_after_head_before_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (index : Fin (n + 1))
    (hafter : cfg.tape.head.val < index.val) (hbeforeRight : index.val < n) :
    SimulatorStep M embed
      (encodedCfgAt .scanRight cfg index)
      (encodedCfgAt .scanRight cfg ⟨index.val + 1, by omega⟩) := by
  have hne : index ≠ cfg.tape.head := by
    intro heq
    subst index
    omega
  have hnotRight : index.val ≠ n := by omega
  unfold SimulatorStep DLBA.step machine transition continueRight
  simp [encodedCfgAt, encodedTapeAt, encodedCell, hne, hnotRight, hbeforeRight,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_scanRight_after_head_at_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (index : Fin (n + 1))
    (hafter : cfg.tape.head.val < index.val) (hright : index.val = n) :
    SimulatorStep M embed
      (encodedCfgAt .scanRight cfg index)
      (encodedCfgAt .scanLeft cfg ⟨index.val - 1, by omega⟩) := by
  have hne : index ≠ cfg.tape.head := by
    intro heq
    subst index
    omega
  have hnpositive : 0 < n := by omega
  unfold SimulatorStep DLBA.step machine transition continueRight
  simp [encodedCfgAt, encodedTapeAt, encodedCell, hne, hright, hnpositive,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem transGen_scanRight_after_head_to_round
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) :
    ∀ index : Fin (n + 1), cfg.tape.head.val < index.val →
      TransGen (SimulatorStep M embed)
        (encodedCfgAt .scanRight cfg index) (roundCfg cfg) := by
  suffices H : ∀ distance, ∀ index : Fin (n + 1),
      cfg.tape.head.val < index.val → n - index.val = distance →
      TransGen (SimulatorStep M embed)
        (encodedCfgAt .scanRight cfg index) (roundCfg cfg) from
    fun index hafter => H (n - index.val) index hafter rfl
  intro distance
  induction distance with
  | zero =>
      intro index hafter hdistance
      have hright : index.val = n := by
        have := index.isLt
        omega
      have hboundary :=
        step_scanRight_after_head_at_right M embed cfg index hafter hright
      exact TransGen.head hboundary
        (transGen_scanLeft_to_round M embed cfg ⟨index.val - 1, by omega⟩)
  | succ distance ih =>
      intro index hafter hdistance
      have hbeforeRight : index.val < n := by omega
      let next : Fin (n + 1) := ⟨index.val + 1, by omega⟩
      have hnextAfter : cfg.tape.head.val < next.val := by
        simp only [next]
        omega
      have hnextDistance : n - next.val = distance := by
        simp only [next]
        omega
      exact TransGen.head
        (step_scanRight_after_head_before_right M embed cfg index hafter hbeforeRight)
        (ih next hnextAfter hnextDistance)

private theorem transGen_query_stay_to_round
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .stay)) :
    TransGen (SimulatorStep M embed) (queryCfg cfg)
      (roundCfg (⟨next, (cfg.tape.write symbol).moveHead .stay⟩ : DLBA.Cfg Gamma Q n)) := by
  let nextCfg : DLBA.Cfg Gamma Q n :=
    ⟨next, (cfg.tape.write symbol).moveHead .stay⟩
  by_cases hright : cfg.tape.head.val = n
  · have hstep := step_query_stay_at_right M embed cfg next symbol htransition hright
    exact TransGen.head hstep
      (transGen_scanLeft_to_round M embed nextCfg
        ((cfg.tape.write symbol).moveHead .left).head)
  · have hbefore : cfg.tape.head.val < n := by
      have := cfg.tape.head.isLt
      omega
    have hstep := step_query_stay_before_right M embed cfg next symbol htransition hbefore
    have hafter : nextCfg.tape.head.val <
        ((cfg.tape.write symbol).moveHead .right).head.val := by
      simp [nextCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hbefore]
    exact TransGen.head hstep
      (transGen_scanRight_after_head_to_round M embed nextCfg
        ((cfg.tape.write symbol).moveHead .right).head hafter)

private theorem transGen_query_right_to_round
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .right)) :
    TransGen (SimulatorStep M embed) (queryCfg cfg)
      (roundCfg (⟨next, (cfg.tape.write symbol).moveHead .right⟩ : DLBA.Cfg Gamma Q n)) := by
  let nextCfg : DLBA.Cfg Gamma Q n :=
    ⟨next, (cfg.tape.write symbol).moveHead .right⟩
  by_cases hright : cfg.tape.head.val = n
  · have hstep := step_query_right_at_boundary M embed cfg next symbol htransition hright
    exact TransGen.head hstep
      (transGen_scanLeft_to_round M embed nextCfg
        ((cfg.tape.write symbol).moveHead .left).head)
  · have hbefore : cfg.tape.head.val < n := by
      have := cfg.tape.head.isLt
      omega
    have hquery :=
      step_query_right_before_boundary M embed cfg next symbol htransition hbefore
    by_cases hnewRight : nextCfg.tape.head.val = n
    · have hput := step_putRight_at_boundary M embed cfg next symbol hbefore hnewRight
      exact TransGen.head hquery <| TransGen.head hput <|
        transGen_scanLeft_to_round M embed nextCfg
          (nextCfg.tape.moveHead .left).head
    · have hnewBefore : nextCfg.tape.head.val < n := by
        have := nextCfg.tape.head.isLt
        omega
      have hput := step_putRight_before_boundary M embed cfg next symbol hbefore hnewBefore
      have hafter : nextCfg.tape.head.val < (nextCfg.tape.moveHead .right).head.val := by
        simp [DLBA.BoundedTape.moveHead, hnewBefore]
      exact TransGen.head hquery <| TransGen.head hput <|
        transGen_scanRight_after_head_to_round M embed nextCfg
          (nextCfg.tape.moveHead .right).head hafter

private theorem transGen_leftPending_to_round
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (hpositive : 0 < cfg.tape.head.val) :
    TransGen (SimulatorStep M embed) (leftPendingCfg cfg next symbol)
      (roundCfg (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n)) := by
  let nextCfg : DLBA.Cfg Gamma Q n :=
    ⟨next, (cfg.tape.write symbol).moveHead .left⟩
  by_cases hnewLeft : nextCfg.tape.head.val = 0
  · have hstep := step_putLeft_at_left M embed cfg next symbol hpositive hnewLeft
    have hphysical : nextCfg.tape.head = leftIndex n := by
      apply Fin.ext
      simpa [leftIndex] using hnewLeft
    rw [hphysical] at hstep
    simpa [roundCfg] using (TransGen.single hstep)
  · have hnewPositive : 0 < nextCfg.tape.head.val := by omega
    have hstep := step_putLeft_above_left M embed cfg next symbol hpositive hnewPositive
    exact TransGen.head hstep
      (transGen_scanLeft_to_round M embed nextCfg
        (nextCfg.tape.moveHead .left).head)

private theorem transGen_query_left_to_round
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (next : Q) (symbol : Gamma)
    (htransition : M.transition cfg.state cfg.tape.read = some (next, symbol, .left)) :
    TransGen (SimulatorStep M embed) (queryCfg cfg)
      (roundCfg (⟨next, (cfg.tape.write symbol).moveHead .left⟩ : DLBA.Cfg Gamma Q n)) := by
  let nextCfg : DLBA.Cfg Gamma Q n :=
    ⟨next, (cfg.tape.write symbol).moveHead .left⟩
  by_cases hleft : cfg.tape.head.val = 0
  · by_cases hright : cfg.tape.head.val = n
    · have hstep :=
        step_query_left_clamped_at_right M embed cfg next symbol htransition hleft hright
      exact TransGen.head hstep
        (transGen_scanLeft_to_round M embed nextCfg nextCfg.tape.head)
    · have hbefore : cfg.tape.head.val < n := by
        have := cfg.tape.head.isLt
        omega
      have hnpositive : 0 < n := by omega
      have hstep :=
        step_query_left_clamped_before_right M embed cfg next symbol htransition hleft hbefore
      have hafter : nextCfg.tape.head.val <
          ((cfg.tape.write symbol).moveHead .right).head.val := by
        simp [nextCfg, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hleft,
          hnpositive]
      exact TransGen.head hstep
        (transGen_scanRight_after_head_to_round M embed nextCfg
          ((cfg.tape.write symbol).moveHead .right).head hafter)
  · have hpositive : 0 < cfg.tape.head.val := by omega
    have hpending := transGen_leftPending_to_round M embed cfg next symbol hpositive
    by_cases hright : cfg.tape.head.val = n
    · exact TransGen.head
        (step_query_left_at_right M embed cfg next symbol htransition hpositive hright)
        hpending
    · have hbefore : cfg.tape.head.val < n := by
        have := cfg.tape.head.isLt
        omega
      have hquery :=
        step_query_left_interior M embed cfg next symbol htransition hpositive hbefore
      have hafter : cfg.tape.head.val <
          ((cfg.tape.write symbol).moveHead .right).head.val := by
        simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hbefore]
      have hrequest := transGen_request_scanRight_to_pending M embed cfg next symbol
        hpositive ((cfg.tape.write symbol).moveHead .right).head hafter
      exact TransGen.head hquery (TransGen.trans hrequest hpending)

/-- A successful source step is simulated exactly from its query configuration to the next
canonical round boundary. -/
public theorem queryCfg_transGen_roundCfg_of_step
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    {cfg nextCfg : DLBA.Cfg Gamma Q n} (hstep : DLBA.step M cfg = some nextCfg) :
    TransGen (SimulatorStep M embed) (queryCfg cfg) (roundCfg nextCfg) := by
  unfold DLBA.step at hstep
  split at hstep
  · contradiction
  · next nextState symbol direction htransition =>
    cases direction with
    | stay =>
        simp only [Option.some.injEq] at hstep
        subst nextCfg
        exact transGen_query_stay_to_round M embed cfg nextState symbol htransition
    | right =>
        simp only [Option.some.injEq] at hstep
        subst nextCfg
        exact transGen_query_right_to_round M embed cfg nextState symbol htransition
    | left =>
        simp only [Option.some.injEq] at hstep
        subst nextCfg
        exact transGen_query_left_to_round M embed cfg nextState symbol htransition

/-- One source-machine step is simulated by a nonempty endpoint-to-endpoint macro. -/
public theorem roundCfg_transGen_roundCfg_of_step
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    {cfg nextCfg : DLBA.Cfg Gamma Q n} (hstep : DLBA.step M cfg = some nextCfg) :
    TransGen (SimulatorStep M embed) (roundCfg cfg) (roundCfg nextCfg) :=
  TransGen.trans (roundCfg_transGen_queryCfg M embed cfg)
    (queryCfg_transGen_roundCfg_of_step M embed hstep)

/-- Iteration form of the exact macro theorem. -/
public theorem exists_pos_iterateStep_roundCfg_roundCfg_of_step
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    {cfg nextCfg : DLBA.Cfg Gamma Q n} (hstep : DLBA.step M cfg = some nextCfg) :
    ∃ steps, 0 < steps ∧
      DLBA.iterateStep (machine M embed) (roundCfg cfg) steps = some (roundCfg nextCfg) :=
  exists_pos_iterateStep_of_transGen M embed
    (roundCfg_transGen_roundCfg_of_step M embed hstep)

/-! ### Initialization -/

private def initialCell (M : DLBA.Machine Gamma Q) (embed : I → Gamma)
    {n : Nat} (input : Fin (n + 1) → I) (index : Fin (n + 1)) : Cell Gamma Q :=
  { left := decide (index.val = 0)
    right := false
    symbol := embed (input index)
    tag := if index.val = 0 then .head M.initial else .plain }

private def initialPartialContents (M : DLBA.Machine Gamma Q) (embed : I → Gamma)
    {n : Nat} (input : Fin (n + 1) → I) (converted : Nat) :
    Fin (n + 1) → Alphabet I Gamma Q :=
  fun index => if index.val < converted then workSymbol (initialCell M embed input index)
    else inputEmbed (input index)

private theorem initialPartialContents_update
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) (index : Fin (n + 1)) :
    Function.update (initialPartialContents M embed input index.val) index
        (workSymbol (initialCell M embed input index)) =
      initialPartialContents M embed input (index.val + 1) := by
  funext other
  rw [Function.update_apply]
  by_cases hother : other = index
  · subst other
    simp [initialPartialContents]
  · have hval : other.val ≠ index.val := fun h => hother (Fin.ext h)
    rw [if_neg hother]
    simp only [initialPartialContents]
    by_cases hlt : other.val < index.val
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

private theorem initialPartialContents_full
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) :
    initialPartialContents M embed input (n + 1) =
      fun index => workSymbol (initialCell M embed input index) := by
  funext index
  simp [initialPartialContents, index.isLt]

private theorem step_initFirst
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) :
    SimulatorStep M embed
      (DLBA.initCfg (machine M embed) (fun index => inputEmbed (input index)))
      ⟨.initSweep,
        ⟨initialPartialContents M embed input 1,
          ((DLBA.initCfg (machine M embed)
            (fun index => inputEmbed (input index))).tape.moveHead .right).head⟩⟩ := by
  unfold SimulatorStep DLBA.step machine transition DLBA.initCfg DLBA.BoundedTape.read
  simp [DLBA.BoundedTape.write,
    DLBA.BoundedTape.moveHead]
  funext index
  by_cases hzero : index = (0 : Fin (n + 1))
  · subst index
    simp [initialPartialContents, initialCell]
  · have hval : index.val ≠ 0 := by
      intro h
      exact hzero (Fin.ext h)
    simp [initialPartialContents, hzero, hval]

private theorem step_initSweep_raw_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) (index : Fin (n + 1))
    (hpositive : 0 < index.val) (hbefore : index.val < n) :
    SimulatorStep M embed
      ⟨.initSweep, ⟨initialPartialContents M embed input index.val, index⟩⟩
      ⟨.initSweep,
        ⟨initialPartialContents M embed input (index.val + 1),
          ⟨index.val + 1, by omega⟩⟩⟩ := by
  have hupd := initialPartialContents_update M embed input index
  have hindexZero : index ≠ (0 : Fin (n + 1)) := by
    intro h
    subst index
    simp at hpositive
  unfold SimulatorStep DLBA.step machine transition DLBA.BoundedTape.read
  simp [initialPartialContents, hbefore,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  simpa [initialCell, hindexZero] using hupd

private theorem step_initSweep_raw_last
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) (index : Fin (n + 1))
    (hpositive : 0 < index.val) (hright : index.val = n) :
    SimulatorStep M embed
      ⟨.initSweep, ⟨initialPartialContents M embed input index.val, index⟩⟩
      ⟨.initSweep, ⟨initialPartialContents M embed input (index.val + 1), index⟩⟩ := by
  have hupd := initialPartialContents_update M embed input index
  have hindexZero : index ≠ (0 : Fin (n + 1)) := by
    intro h
    subst index
    simp at hpositive
  have hnotBefore : ¬ index.val < n := by omega
  unfold SimulatorStep DLBA.step machine transition DLBA.BoundedTape.read
  simp [initialPartialContents, hnotBefore,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  simpa [initialCell, hindexZero] using hupd

private theorem transGen_initSweep_convert
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) :
    ∀ index : Fin (n + 1), 1 ≤ index.val →
      TransGen (SimulatorStep M embed)
        ⟨.initSweep, ⟨initialPartialContents M embed input index.val, index⟩⟩
        ⟨.initSweep,
          ⟨initialPartialContents M embed input (n + 1), Fin.last n⟩⟩ := by
  suffices H : ∀ distance, ∀ index : Fin (n + 1), 1 ≤ index.val →
      n - index.val = distance →
      TransGen (SimulatorStep M embed)
        ⟨.initSweep, ⟨initialPartialContents M embed input index.val, index⟩⟩
        ⟨.initSweep,
          ⟨initialPartialContents M embed input (n + 1), Fin.last n⟩⟩ from
    fun index hindex => H (n - index.val) index hindex rfl
  intro distance
  induction distance with
  | zero =>
      intro index hindex hdistance
      have hright : index.val = n := by
        have := index.isLt
        omega
      have hlast : index = Fin.last n := Fin.ext (by simp [hright])
      have hstep := step_initSweep_raw_last M embed input index (by omega) hright
      subst index
      simpa using (TransGen.single hstep)
  | succ distance ih =>
      intro index hindex hdistance
      have hbefore : index.val < n := by omega
      let following : Fin (n + 1) := ⟨index.val + 1, by omega⟩
      have hfollowing : 1 ≤ following.val := by simp [following]
      have hfollowingDistance : n - following.val = distance := by
        simp only [following]
        omega
      exact TransGen.head
        (step_initSweep_raw_right M embed input index (by omega) hbefore)
        (ih following hfollowing hfollowingDistance)

private theorem initial_mark_right_contents
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) :
    Function.update (initialPartialContents M embed input (n + 1)) (Fin.last n)
        (workSymbol { initialCell M embed input (Fin.last n) with right := true }) =
      encodedContents
        (I := I) (DLBA.initCfg M (fun index => embed (input index))) := by
  funext index
  by_cases hlast : index = Fin.last n
  · subst index
    simp [initialCell, encodedContents, encodedCell, DLBA.initCfg]
  · have hnotRight : index.val ≠ n := by
      intro hval
      exact hlast (Fin.ext (by simpa using hval))
    have hle : index.val ≤ n := by
      have := index.isLt
      omega
    simp [initialPartialContents, initialCell, encodedContents,
      encodedCell, DLBA.initCfg, hlast, hnotRight, hle]

private theorem step_initSweep_mark_right
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) :
    SimulatorStep M embed
      ⟨.initSweep,
        ⟨initialPartialContents M embed input (n + 1), Fin.last n⟩⟩
      ⟨.initBack,
        ⟨encodedContents (I := I) (DLBA.initCfg M (fun index => embed (input index))),
          ((⟨initialPartialContents M embed input (n + 1), Fin.last n⟩ :
            DLBA.BoundedTape (Alphabet I Gamma Q) n).moveHead .left).head⟩⟩ := by
  have hcontents := initial_mark_right_contents (I := I) M embed input
  rw [initialPartialContents_full M embed input] at hcontents
  unfold SimulatorStep DLBA.step machine transition DLBA.BoundedTape.read
  rw [initialPartialContents_full M embed input]
  simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  exact hcontents

private theorem step_initBack_positive
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (index : Fin (n + 1))
    (hpositive : 0 < index.val) :
    SimulatorStep M embed
      (encodedCfgAt .initBack cfg index)
      (encodedCfgAt .initBack cfg ⟨index.val - 1, by omega⟩) := by
  have hnotLeft : index ≠ (0 : Fin (n + 1)) := by
    exact Fin.ne_of_gt hpositive
  unfold SimulatorStep DLBA.step machine transition
  simp [encodedCfgAt, encodedTapeAt, encodedCell, hnotLeft, hpositive,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem step_initBack_zero
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (index : Fin (n + 1))
    (hzero : index.val = 0) :
    SimulatorStep M embed
      (encodedCfgAt .initBack cfg index)
      (roundCfg cfg) := by
  have hindex : index = leftIndex n := Fin.ext (by simpa [leftIndex] using hzero)
  subst index
  unfold SimulatorStep DLBA.step machine transition roundCfg
  simp [encodedCfgAt, encodedTapeAt, encodedCell, leftIndex,
    DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

private theorem transGen_initBack_to_round
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) :
    ∀ index : Fin (n + 1),
      TransGen (SimulatorStep M embed)
        (encodedCfgAt .initBack cfg index) (roundCfg cfg) := by
  suffices H : ∀ value, ∀ index : Fin (n + 1), index.val = value →
      TransGen (SimulatorStep M embed)
        (encodedCfgAt .initBack cfg index) (roundCfg cfg) from
    fun index => H index.val index rfl
  intro value
  induction value with
  | zero =>
      intro index hvalue
      exact .single (step_initBack_zero M embed cfg index hvalue)
  | succ value ih =>
      intro index hvalue
      have hpositive : 0 < index.val := by omega
      let previous : Fin (n + 1) := ⟨index.val - 1, by omega⟩
      have hprevious : previous.val = value := by
        simp only [previous]
        omega
      exact TransGen.head
        (step_initBack_positive M embed cfg index hpositive)
        (ih previous hprevious)

/-- Initialization converts every raw input cell, installs both endpoints and the simulated
initial head, and reaches the first canonical round. -/
public theorem initCfg_transGen_roundCfg
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) :
    TransGen (SimulatorStep M embed)
      (DLBA.initCfg (machine M embed) (fun index => inputEmbed (input index)))
      (roundCfg (DLBA.initCfg M (fun index => embed (input index)))) := by
  let sourceCfg : DLBA.Cfg Gamma Q n :=
    DLBA.initCfg M (fun index => embed (input index))
  have hfirst := step_initFirst M embed input
  have hmark := step_initSweep_mark_right M embed input
  let markedHead : Fin (n + 1) :=
    ((⟨initialPartialContents M embed input (n + 1), Fin.last n⟩ :
      DLBA.BoundedTape (Alphabet I Gamma Q) n).moveHead .left).head
  have hback := transGen_initBack_to_round M embed sourceCfg markedHead
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hfirst' : SimulatorStep M embed
        (DLBA.initCfg (machine M embed) (fun index => inputEmbed (input index)))
        ⟨.initSweep,
          ⟨initialPartialContents M embed input 1, Fin.last 0⟩⟩ := by
      simpa [DLBA.initCfg, DLBA.BoundedTape.moveHead] using hfirst
    exact TransGen.head hfirst' (TransGen.head hmark hback)
  · have hfirst' : SimulatorStep M embed
        (DLBA.initCfg (machine M embed) (fun index => inputEmbed (input index)))
        ⟨.initSweep,
          ⟨initialPartialContents M embed input 1, ⟨1, by omega⟩⟩⟩ := by
      simpa [DLBA.initCfg, DLBA.BoundedTape.moveHead, hn] using hfirst
    have hconvert := transGen_initSweep_convert M embed input ⟨1, by omega⟩ (by simp)
    exact TransGen.head hfirst'
      (TransGen.trans hconvert (TransGen.head hmark hback))

/-- Iteration form of initialization, with a nonzero target-step count. -/
public theorem exists_pos_iterateStep_initCfg_roundCfg
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) :
    ∃ steps, 0 < steps ∧
      DLBA.iterateStep (machine M embed)
        (DLBA.initCfg (machine M embed) (fun index => inputEmbed (input index))) steps =
          some (roundCfg (DLBA.initCfg M (fun index => embed (input index)))) :=
  exists_pos_iterateStep_of_transGen M embed (initCfg_transGen_roundCfg M embed input)

private theorem step_queryCfg_none_of_step_none
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) (hstep : DLBA.step M cfg = none) :
    DLBA.step (machine M embed) (queryCfg cfg) = none := by
  have htransition : M.transition cfg.state cfg.tape.read = none := by
    cases h : M.transition cfg.state cfg.tape.read with
    | none => rfl
    | some result =>
        unfold DLBA.step at hstep
        rw [h] at hstep
        simp at hstep
  change M.transition cfg.state (cfg.tape.contents cfg.tape.head) = none at htransition
  unfold DLBA.step
  simp [queryCfg, encodedCfgAt, encodedTapeAt, machine, transition, encodedCell,
    htransition]

private theorem accept_queryCfg
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (cfg : DLBA.Cfg Gamma Q n) :
    (machine M embed).accept (queryCfg (I := I) cfg).state = M.accept cfg.state := by
  rfl

private theorem iterate_trans
    (N : DLBA.Machine Delta P) {n : Nat}
    {source middle target : DLBA.Cfg Delta P n}
    {first second : Nat}
    (hfirst : DLBA.iterateStep N source first = some middle)
    (hsecond : DLBA.iterateStep N middle second = some target) :
    DLBA.iterateStep N source (first + second) = some target := by
  rw [DLBA.iterateStep_add, hfirst]
  exact hsecond

private theorem lift_iterate
    (M : DLBA.Machine Gamma Q)
    (N : DLBA.Machine Delta P) {n : Nat}
    (round : DLBA.Cfg Gamma Q n → DLBA.Cfg Delta P n)
    (hmacro : ∀ {source target : DLBA.Cfg Gamma Q n},
      DLBA.step M source = some target →
        ∃ steps, 0 < steps ∧
          DLBA.iterateStep N (round source) steps = some (round target))
    {source target : DLBA.Cfg Gamma Q n} {sourceSteps : Nat}
    (hsource : DLBA.iterateStep M source sourceSteps = some target) :
    ∃ targetSteps, sourceSteps ≤ targetSteps ∧
      DLBA.iterateStep N (round source) targetSteps = some (round target) := by
  induction sourceSteps generalizing source target with
  | zero =>
      simp only [DLBA.iterateStep_zero, Option.some.injEq] at hsource
      subst target
      exact ⟨0, le_rfl, rfl⟩
  | succ sourceSteps ih =>
      rw [DLBA.iterateStep_succ] at hsource
      cases hmiddle : DLBA.iterateStep M source sourceSteps with
      | none => simp [hmiddle] at hsource
      | some middle =>
          simp only [hmiddle, Option.bind_some] at hsource
          obtain ⟨prefixSteps, hprefixLower, hprefix⟩ := ih hmiddle
          obtain ⟨macroSteps, hmacroPositive, hmacroRun⟩ := hmacro hsource
          refine ⟨prefixSteps + macroSteps, by omega, ?_⟩
          exact iterate_trans N hprefix hmacroRun

private theorem target_accepts_of_source_accepts
    (M : DLBA.Machine Gamma Q)
    (N : DLBA.Machine Delta P) {n : Nat}
    (round query : DLBA.Cfg Gamma Q n → DLBA.Cfg Delta P n)
    (sourceCfg : DLBA.Cfg Gamma Q n) (rawCfg : DLBA.Cfg Delta P n)
    (hinit : ∃ steps, 0 < steps ∧
      DLBA.iterateStep N rawCfg steps = some (round sourceCfg))
    (hmacro : ∀ {source target : DLBA.Cfg Gamma Q n},
      DLBA.step M source = some target →
        ∃ steps, 0 < steps ∧
          DLBA.iterateStep N (round source) steps = some (round target))
    (hscan : ∀ cfg, ∃ steps, 0 < steps ∧
      DLBA.iterateStep N (round cfg) steps = some (query cfg))
    (hterminal : ∀ cfg, DLBA.step M cfg = none → DLBA.step N (query cfg) = none)
    (haccept : ∀ cfg, N.accept (query cfg).state = M.accept cfg.state)
    (hsource : DLBA.Accepts M sourceCfg) :
    DLBA.Accepts N rawCfg := by
  obtain ⟨sourceSteps, hsourceHalt, terminal, hsourceRun, hterminalAccept⟩ := hsource
  have hsourceStep : DLBA.step M terminal = none := by
    rw [DLBA.iterateStep_succ, hsourceRun] at hsourceHalt
    exact hsourceHalt
  obtain ⟨initialSteps, _, hinitial⟩ := hinit
  obtain ⟨simulationSteps, _, hsimulation⟩ :=
    lift_iterate M N round hmacro hsourceRun
  obtain ⟨querySteps, _, hquery⟩ := hscan terminal
  let total := initialSteps + simulationSteps + querySteps
  have hreach : DLBA.iterateStep N rawCfg total = some (query terminal) := by
    apply iterate_trans N (middle := round terminal)
    · exact iterate_trans N hinitial hsimulation
    · exact hquery
  refine ⟨total, ?_, query terminal, hreach, ?_⟩
  · rw [DLBA.iterateStep_succ, hreach]
    exact hterminal terminal hsourceStep
  · rw [haccept]
    exact hterminalAccept

private theorem target_rejects_of_source_rejects
    (M : DLBA.Machine Gamma Q)
    (N : DLBA.Machine Delta P) {n : Nat}
    (round query : DLBA.Cfg Gamma Q n → DLBA.Cfg Delta P n)
    (sourceCfg : DLBA.Cfg Gamma Q n) (rawCfg : DLBA.Cfg Delta P n)
    (hinit : ∃ steps, 0 < steps ∧
      DLBA.iterateStep N rawCfg steps = some (round sourceCfg))
    (hmacro : ∀ {source target : DLBA.Cfg Gamma Q n},
      DLBA.step M source = some target →
        ∃ steps, 0 < steps ∧
          DLBA.iterateStep N (round source) steps = some (round target))
    (hscan : ∀ cfg, ∃ steps, 0 < steps ∧
      DLBA.iterateStep N (round cfg) steps = some (query cfg))
    (hterminal : ∀ cfg, DLBA.step M cfg = none → DLBA.step N (query cfg) = none)
    (haccept : ∀ cfg, N.accept (query cfg).state = M.accept cfg.state)
    (hsource : DLBA.Rejects M sourceCfg) :
    DLBA.Rejects N rawCfg := by
  obtain ⟨sourceSteps, hsourceHalt, terminal, hsourceRun, hterminalAccept⟩ := hsource
  have hsourceStep : DLBA.step M terminal = none := by
    rw [DLBA.iterateStep_succ, hsourceRun] at hsourceHalt
    exact hsourceHalt
  obtain ⟨initialSteps, _, hinitial⟩ := hinit
  obtain ⟨simulationSteps, _, hsimulation⟩ :=
    lift_iterate M N round hmacro hsourceRun
  obtain ⟨querySteps, _, hquery⟩ := hscan terminal
  let total := initialSteps + simulationSteps + querySteps
  have hreach : DLBA.iterateStep N rawCfg total = some (query terminal) := by
    apply iterate_trans N (middle := round terminal)
    · exact iterate_trans N hinitial hsimulation
    · exact hquery
  refine ⟨total, ?_, query terminal, hreach, ?_⟩
  · rw [DLBA.iterateStep_succ, hreach]
    exact hterminal terminal hsourceStep
  · rw [haccept]
    exact hterminalAccept

private theorem target_not_halts_of_source_not_halts
    (M : DLBA.Machine Gamma Q)
    (N : DLBA.Machine Delta P) {n : Nat}
    (round : DLBA.Cfg Gamma Q n → DLBA.Cfg Delta P n)
    (sourceCfg : DLBA.Cfg Gamma Q n) (rawCfg : DLBA.Cfg Delta P n)
    (hinit : ∃ steps, 0 < steps ∧
      DLBA.iterateStep N rawCfg steps = some (round sourceCfg))
    (hmacro : ∀ {source target : DLBA.Cfg Gamma Q n},
      DLBA.step M source = some target →
        ∃ steps, 0 < steps ∧
          DLBA.iterateStep N (round source) steps = some (round target))
    (hsource : ¬ DLBA.Halts M sourceCfg) :
    ¬ DLBA.Halts N rawCfg := by
  rintro ⟨haltSteps, hhalt⟩
  have hsourceSome : ∃ target, DLBA.iterateStep M sourceCfg haltSteps = some target := by
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    exact hsource ⟨haltSteps, hnone⟩
  obtain ⟨sourceTarget, hsourceRun⟩ := hsourceSome
  obtain ⟨initialSteps, _, hinitial⟩ := hinit
  obtain ⟨simulationSteps, hsimulationLower, hsimulation⟩ :=
    lift_iterate M N round hmacro hsourceRun
  have hlive : DLBA.iterateStep N rawCfg (initialSteps + simulationSteps) =
      some (round sourceTarget) := iterate_trans N hinitial hsimulation
  have hlower : haltSteps ≤ initialSteps + simulationSteps := by omega
  have hdead := DLBA.iterateStep_none_mono N rawCfg hhalt
    (initialSteps + simulationSteps - haltSteps)
  rw [Nat.add_sub_of_le hlower] at hdead
  rw [hlive] at hdead
  contradiction

private theorem accepts_iff_of_positive_macro_simulation
    (M : DLBA.Machine Gamma Q)
    (N : DLBA.Machine Delta P) {n : Nat}
    (round query : DLBA.Cfg Gamma Q n → DLBA.Cfg Delta P n)
    (sourceCfg : DLBA.Cfg Gamma Q n) (rawCfg : DLBA.Cfg Delta P n)
    (hinit : ∃ steps, 0 < steps ∧
      DLBA.iterateStep N rawCfg steps = some (round sourceCfg))
    (hmacro : ∀ {source target : DLBA.Cfg Gamma Q n},
      DLBA.step M source = some target →
        ∃ steps, 0 < steps ∧
          DLBA.iterateStep N (round source) steps = some (round target))
    (hscan : ∀ cfg, ∃ steps, 0 < steps ∧
      DLBA.iterateStep N (round cfg) steps = some (query cfg))
    (hterminal : ∀ cfg, DLBA.step M cfg = none → DLBA.step N (query cfg) = none)
    (haccept : ∀ cfg, N.accept (query cfg).state = M.accept cfg.state) :
    DLBA.Accepts N rawCfg ↔ DLBA.Accepts M sourceCfg := by
  constructor
  · intro htarget
    by_cases hsourceHalts : DLBA.Halts M sourceCfg
    · rcases DLBA.accepts_or_rejects_of_halts M sourceCfg hsourceHalts with
        hsourceAccepts | hsourceRejects
      · exact hsourceAccepts
      · have htargetRejects := target_rejects_of_source_rejects M N round query
          sourceCfg rawCfg hinit hmacro hscan hterminal haccept hsourceRejects
        exact False.elim (DLBA.not_accepts_and_rejects N rawCfg
          ⟨htarget, htargetRejects⟩)
    · have htargetNotHalts := target_not_halts_of_source_not_halts M N round
        sourceCfg rawCfg hinit hmacro hsourceHalts
      obtain ⟨steps, hhalt, _⟩ := htarget
      exact False.elim (htargetNotHalts ⟨steps + 1, hhalt⟩)
  · exact target_accepts_of_source_accepts M N round query sourceCfg rawCfg
      hinit hmacro hscan hterminal haccept

/-- The deterministic sweeping compiler preserves acceptance on every nonempty bounded input. -/
public theorem machine_accepts_initCfg_iff
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) {n : Nat}
    (input : Fin (n + 1) → I) :
    DLBA.Accepts (machine M embed)
        (DLBA.initCfg (machine M embed) (fun index ↦ inputEmbed (input index))) ↔
      DLBA.Accepts M
        (DLBA.initCfg M (fun index ↦ embed (input index))) := by
  apply accepts_iff_of_positive_macro_simulation M (machine M embed)
    (fun cfg ↦ roundCfg (I := I) cfg) (fun cfg ↦ queryCfg (I := I) cfg)
    (DLBA.initCfg M (fun index ↦ embed (input index)))
    (DLBA.initCfg (machine M embed) (fun index ↦ inputEmbed (input index)))
  · exact exists_pos_iterateStep_initCfg_roundCfg M embed input
  · intro source target hstep
    exact exists_pos_iterateStep_roundCfg_roundCfg_of_step M embed hstep
  · exact exists_pos_iterateStep_roundCfg_queryCfg M embed
  · exact step_queryCfg_none_of_step_none M embed
  · exact accept_queryCfg M embed

private theorem accepts_heq
    (N : DLBA.Machine Delta P) {n m : Nat}
    {cfg : DLBA.Cfg Delta P n} {cfg' : DLBA.Cfg Delta P m}
    (hn : n = m) (hcfg : HEq cfg cfg') :
    DLBA.Accepts N cfg ↔ DLBA.Accepts N cfg' := by
  subst hn
  rw [eq_of_heq hcfg]

private theorem boundedTape_heq
    {n m : Nat} (hn : n = m)
    {tape : DLBA.BoundedTape Delta n} {tape' : DLBA.BoundedTape Delta m}
    (hcontents : HEq tape.contents tape'.contents)
    (hhead : tape.head.val = tape'.head.val) : HEq tape tape' := by
  subst hn
  obtain ⟨contents, head⟩ := tape
  obtain ⟨contents', head'⟩ := tape'
  apply heq_of_eq
  simp only [DLBA.BoundedTape.mk.injEq]
  exact ⟨eq_of_heq hcontents, Fin.ext hhead⟩

private theorem cfg_heq
    {n m : Nat} (hn : n = m)
    {cfg : DLBA.Cfg Delta P n} {cfg' : DLBA.Cfg Delta P m}
    (hstate : cfg.state = cfg'.state) (htape : HEq cfg.tape cfg'.tape) :
    HEq cfg cfg' := by
  subst hn
  obtain ⟨state, tape⟩ := cfg
  obtain ⟨state', tape'⟩ := cfg'
  apply heq_of_eq
  simp only [DLBA.Cfg.mk.injEq]
  exact ⟨hstate, eq_of_heq htape⟩

private def listInput (word : List I) (hword : word ≠ []) :
    Fin (word.length - 1 + 1) → I :=
  fun index ↦ word.get ⟨index.val, by
    have hlength := List.length_pos_of_ne_nil hword
    have hindex := index.isLt
    omega⟩

private theorem initCfg_listInput_heq
    (N : DLBA.Machine Delta P) (mapSymbol : I → Delta)
    (word : List I) (hword : word ≠ [])
    (hmapped : word.map mapSymbol ≠ []) :
    HEq
      (DLBA.initCfg N (fun index ↦ mapSymbol (listInput word hword index)))
      (DLBA.initCfgList N (word.map mapSymbol) hmapped) := by
  have hdimension : word.length - 1 = (word.map mapSymbol).length - 1 := by
    simp
  refine cfg_heq hdimension rfl ?_
  refine boundedTape_heq hdimension ?_ rfl
  refine (Fin.heq_fun_iff (by
    exact congrArg (fun length ↦ length + 1) hdimension)).mpr ?_
  intro index
  simp [DLBA.initCfg, DLBA.initCfgList, DLBA.loadList, listInput,
    List.get_eq_getElem, List.getElem_map]

/-- The compiled deterministic sweeping machine recognizes exactly the source language. -/
public theorem machine_languageViaEmbed
    (M : DLBA.Machine Gamma Q) (embed : I → Gamma) :
    DLBA.LanguageViaEmbed (machine M embed) inputEmbed =
      DLBA.LanguageViaEmbed M embed := by
  funext word
  apply propext
  change
    (∃ hw : word.map inputEmbed ≠ [],
      DLBA.Accepts (machine M embed)
        (DLBA.initCfgList (machine M embed) (word.map inputEmbed) hw)) ↔
    (∃ hw : word.map embed ≠ [],
      DLBA.Accepts M (DLBA.initCfgList M (word.map embed) hw))
  constructor
  · rintro ⟨htargetNonempty, htargetAccepts⟩
    have hword : word ≠ [] := by simpa using htargetNonempty
    have hsourceNonempty : word.map embed ≠ [] := by simpa using hword
    refine ⟨hsourceNonempty, ?_⟩
    let input := listInput word hword
    have htargetInit :
        DLBA.Accepts (machine M embed)
          (DLBA.initCfg (machine M embed) (fun index ↦ inputEmbed (input index))) := by
      have hcfg := initCfg_listInput_heq (machine M embed)
        (fun symbol ↦ inputEmbed (Γ := Gamma) (Q := Q) symbol)
        word hword htargetNonempty
      exact (accepts_heq (machine M embed) (by simp) hcfg).mpr htargetAccepts
    have hsourceInit :=
      (machine_accepts_initCfg_iff M embed input).mp htargetInit
    have hcfg := initCfg_listInput_heq M embed word hword hsourceNonempty
    exact (accepts_heq M (by simp) hcfg).mp hsourceInit
  · rintro ⟨hsourceNonempty, hsourceAccepts⟩
    have hword : word ≠ [] := by simpa using hsourceNonempty
    have htargetNonempty :
        word.map (fun symbol ↦ inputEmbed (Γ := Gamma) (Q := Q) symbol) ≠ [] := by
      simpa using hword
    refine ⟨htargetNonempty, ?_⟩
    let input := listInput word hword
    have hsourceInit :
        DLBA.Accepts M
          (DLBA.initCfg M (fun index ↦ embed (input index))) := by
      have hcfg := initCfg_listInput_heq M embed word hword hsourceNonempty
      exact (accepts_heq M (by simp) hcfg).mpr hsourceAccepts
    have htargetInit :=
      (machine_accepts_initCfg_iff M embed input).mpr hsourceInit
    have hcfg := initCfg_listInput_heq (machine M embed)
      (fun symbol ↦ inputEmbed (Γ := Gamma) (Q := Q) symbol)
      word hword htargetNonempty
    exact (accepts_heq (machine M embed) (by simp) hcfg).mp htargetInit

end DLBA.DeterministicSweeping

end
