module

public import Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.Checker

@[expose]
public section

/-!
# Input-track soundness for Aho's padded rows

The work-track checker is independent of the immutable input letters and their consumed-prefix
bits.  This file isolates the latter component.  It shows that the finite input scan accepts
exactly a stationary input head for every structural certificate, and exactly one checked input
advance for `matchTerminal`.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- The running cells underlying `encodeRunRowFrom`, before applying `RowCell.run`. -/
public def encodeRunCellsFrom (g : IndexedGrammar T) (work : List (WorkSlot g))
    (inputPos cell : ℕ) : List T → List (RunCell g)
  | [] => []
  | a :: w =>
      { input := a
        consumed := decide (cell < inputPos)
        block := packedCell workWidth work cell } ::
        encodeRunCellsFrom g work inputPos (cell + 1) w

/-- The running cells underlying a packed configuration row. -/
public def encodeRunCells (g : IndexedGrammar T) (w : List T) (c : Config g) :
    List (RunCell g) :=
  encodeRunCellsFrom g c.work.slots c.inputPos 0 w

@[simp] public theorem encodeRunRowFrom_eq_map_run (g : IndexedGrammar T)
    (work : List (WorkSlot g)) (inputPos cell : ℕ) (w : List T) :
    encodeRunRowFrom g work inputPos cell w =
      (encodeRunCellsFrom g work inputPos cell w).map RowCell.run := by
  induction w generalizing cell with
  | nil => rfl
  | cons a w ih =>
      simp [encodeRunRowFrom, encodeRunCellsFrom, ih]

@[simp] public theorem encodeRunRow_eq_map_run (g : IndexedGrammar T)
    (w : List T) (c : Config g) :
    encodeRunRow g w c = (encodeRunCells g w c).map RowCell.run := by
  simp [encodeRunRow, encodeRunCells]

/-- A block-independent presentation of a running input track whose first `inputPos` cells have
their consumed bit set. -/
public def inputPositionCells (g : IndexedGrammar T) (inputPos : ℕ) :
    List T → List (RunCell g)
  | [] => []
  | a :: w =>
      { input := a
        consumed := decide (0 < inputPos)
        block := blankBlock g } ::
        inputPositionCells g (inputPos - 1) w

private theorem evalInputBlocks_encodeRunCellsFrom_eq_positionCells
    (g : IndexedGrammar T) (cert : CompositeCert g) (phase : InputPhase)
    (oldWork newWork : List (WorkSlot g)) (oldPos newPos cell : ℕ)
    (input : List T) :
    evalInputBlocks cert phase
        (encodeRunCellsFrom g oldWork oldPos cell input)
        (encodeRunCellsFrom g newWork newPos cell input) =
      evalInputBlocks cert phase
        (inputPositionCells g (oldPos - cell) input)
        (inputPositionCells g (newPos - cell) input) := by
  induction input generalizing phase cell with
  | nil => rfl
  | cons a input ih =>
      have holdBit : decide (cell < oldPos) = decide (0 < oldPos - cell) := by
        by_cases h : cell < oldPos
        · have h' : 0 < oldPos - cell := by omega
          simp [h, h']
        · have h' : ¬ 0 < oldPos - cell := by omega
          simp [h, h']
      have hnewBit : decide (cell < newPos) = decide (0 < newPos - cell) := by
        by_cases h : cell < newPos
        · have h' : 0 < newPos - cell := by omega
          simp [h, h']
        · have h' : ¬ 0 < newPos - cell := by omega
          simp [h, h']
      have holdSub : oldPos - cell - 1 = oldPos - (cell + 1) := by omega
      have hnewSub : newPos - cell - 1 = newPos - (cell + 1) := by omega
      simp only [encodeRunCellsFrom, inputPositionCells, evalInputBlocks]
      have hstep :
          inputStep cert phase
              { input := a
                consumed := decide (cell < oldPos)
                block := packedCell workWidth oldWork cell }
              { input := a
                consumed := decide (cell < newPos)
                block := packedCell workWidth newWork cell } =
            inputStep cert phase
              { input := a
                consumed := decide (0 < oldPos - cell)
                block := blankBlock g }
              { input := a
                consumed := decide (0 < newPos - cell)
                block := blankBlock g } := by
        unfold inputStep
        simp only [ne_eq, not_true_eq_false, if_false]
        rw [holdBit, hnewBit]
      rw [hstep, ih]
      rw [holdSub, hnewSub]

/-- The input scan of an encoded row depends only on the input word and the two head positions,
not on either packed work word. -/
public theorem evalInputBlocks_encodeRunCells_eq_positionCells
    (g : IndexedGrammar T) (cert : CompositeCert g) (phase : InputPhase)
    (input : List T) (old new : Config g) :
    evalInputBlocks cert phase (encodeRunCells g input old) (encodeRunCells g input new) =
      evalInputBlocks cert phase
        (inputPositionCells g old.inputPos input)
        (inputPositionCells g new.inputPos input) := by
  simpa [encodeRunCells] using
    (evalInputBlocks_encodeRunCellsFrom_eq_positionCells g cert phase
      old.work.slots new.work.slots old.inputPos new.inputPos 0 input)

/-- The input-position effect prescribed by a composite certificate. -/
public def CompositeCert.InputAction {g : IndexedGrammar T}
    (cert : CompositeCert g) (input : List T)
    (oldPos newPos : ℕ) : Prop :=
  match cert with
  | .matchTerminal a => input[oldPos]? = some a ∧ newPos = oldPos + 1
  | _ => newPos = oldPos

/-- Every semantic certificate step has the input-head action checked by the independent input
track. -/
public theorem certStep_inputAction {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) (cert : CompositeCert g) {old new : Config g}
    (hstep : CertStep g input cert old new) :
    cert.InputAction input old.inputPos new.inputPos := by
  cases cert with
  | plainBinary A B C =>
      rcases hstep with ⟨_, alpha, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | plainTerminal A a =>
      rcases hstep with ⟨_, alpha, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | plainPushSkip A B f =>
      rcases hstep with ⟨_, alpha, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | plainPushUse A B f =>
      rcases hstep with ⟨_, alpha, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | liveBinaryBoth A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | liveBinaryLeft A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | liveBinaryRight A B C =>
      rcases hstep with ⟨_, alpha, Z, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | livePushFresh A B f =>
      rcases hstep with ⟨_, alpha, Z, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | livePushCompress A B f R d =>
      rcases hstep with ⟨_, _, alpha, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | popPlain R d A B =>
      rcases hstep with ⟨_, hshape⟩
      rcases hshape with hframed | herase
      · rcases hframed with ⟨alpha, beta, gamma, _, _, hnew⟩
        simp [CompositeCert.InputAction, hnew]
      · rcases herase with ⟨alpha, gamma, _, hnew⟩
        simp [CompositeCert.InputAction, hnew]
  | popLive R d A B =>
      rcases hstep with ⟨_, _, hshape⟩
      rcases hshape with hframed | herase
      · rcases hframed with ⟨alpha, beta, gamma, _, _, hnew⟩
        simp [CompositeCert.InputAction, hnew]
      · rcases herase with ⟨alpha, gamma, _, hnew⟩
        simp [CompositeCert.InputAction, hnew]
  | matchTerminal a =>
      rcases hstep with ⟨hinput, alpha, Z, beta, _, hnew⟩
      exact ⟨hinput, by simp [hnew]⟩
  | eraseIndex R d =>
      rcases hstep with ⟨_, alpha, Z, beta, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]
  | returnFrame =>
      rcases hstep with ⟨alpha, Z, beta, gamma, _, _, _, hnew⟩
      simp [CompositeCert.InputAction, hnew]

private def CompositeCert.Nonmatching {g : IndexedGrammar T}
    (cert : CompositeCert g) : Prop :=
  match cert with
  | .matchTerminal _ => False
  | _ => True

private theorem inputStep_nonmatching {g : IndexedGrammar T}
    (cert : CompositeCert g) (hcert : cert.Nonmatching)
    (phase : InputPhase) (old new : RunCell g) :
    inputStep cert phase old new =
      if old.input ≠ new.input then .dead else
      match phase, old.consumed, new.consumed with
      | .prefix, true, true => .prefix
      | .prefix, false, false => .tail
      | .tail, false, false => .tail
      | _, _, _ => .dead := by
  unfold inputStep
  by_cases hinput : old.input ≠ new.input
  · rw [if_pos hinput, if_pos hinput]
  · rw [if_neg hinput, if_neg hinput]
    cases cert <;> simp only [CompositeCert.Nonmatching] at hcert <;>
      try contradiction
    all_goals cases phase <;> cases old.consumed <;> cases new.consumed <;> rfl

private theorem inputDone_nonmatching {g : IndexedGrammar T}
    (cert : CompositeCert g) (hcert : cert.Nonmatching) (phase : InputPhase) :
    inputDone cert phase = true ↔ phase = .prefix ∨ phase = .tail := by
  cases cert <;> cases phase <;>
    simp_all [CompositeCert.Nonmatching, inputDone]

private theorem evalInputBlocks_position_dead (g : IndexedGrammar T)
    (cert : CompositeCert g) (oldPos newPos : ℕ) (input : List T) :
    evalInputBlocks cert .dead
        (inputPositionCells g oldPos input)
        (inputPositionCells g newPos input) = .dead := by
  induction input generalizing oldPos newPos with
  | nil => rfl
  | cons a input ih =>
      simp only [inputPositionCells, evalInputBlocks]
      have hstep : inputStep cert .dead
          { input := a, consumed := decide (0 < oldPos), block := blankBlock g }
          { input := a, consumed := decide (0 < newPos), block := blankBlock g } = .dead := by
        cases cert <;> simp [inputStep]
      rw [hstep]
      exact ih _ _

private theorem evalInputBlocks_nonmatching_zero_tail (g : IndexedGrammar T)
    (cert : CompositeCert g) (hcert : cert.Nonmatching) (input : List T) :
    evalInputBlocks cert .tail
        (inputPositionCells g 0 input)
        (inputPositionCells g 0 input) = .tail := by
  induction input with
  | nil => rfl
  | cons a input ih =>
      simp only [inputPositionCells, evalInputBlocks, Nat.lt_irrefl, decide_false,
        Nat.zero_sub]
      rw [inputStep_nonmatching cert hcert]
      simp only [ne_eq, not_true_eq_false, if_false]
      exact ih

private theorem evalInputBlocks_nonmatching_accepts_iff
    (g : IndexedGrammar T) (cert : CompositeCert g) (hcert : cert.Nonmatching)
    (input : List T) (oldPos newPos : ℕ)
    (hold : oldPos ≤ input.length) (hnew : newPos ≤ input.length) :
    inputDone cert
        (evalInputBlocks cert .prefix
          (inputPositionCells g oldPos input)
          (inputPositionCells g newPos input)) = true ↔
      newPos = oldPos := by
  induction input generalizing oldPos newPos with
  | nil =>
      simp only [List.length_nil] at hold hnew
      have hold0 : oldPos = 0 := by omega
      have hnew0 : newPos = 0 := by omega
      subst oldPos
      subst newPos
      simp [inputPositionCells, evalInputBlocks, inputDone_nonmatching cert hcert]
  | cons a input ih =>
      simp only [List.length_cons] at hold hnew
      cases oldPos with
      | zero =>
          cases newPos with
          | zero =>
              rw [show evalInputBlocks cert .prefix
                    (inputPositionCells g 0 (a :: input))
                    (inputPositionCells g 0 (a :: input)) =
                  evalInputBlocks cert .tail
                    (inputPositionCells g 0 input)
                    (inputPositionCells g 0 input) by
                simp only [inputPositionCells, evalInputBlocks, Nat.lt_irrefl,
                  decide_false, Nat.zero_sub]
                rw [inputStep_nonmatching cert hcert]
                simp]
              rw [evalInputBlocks_nonmatching_zero_tail g cert hcert]
              simp [inputDone_nonmatching cert hcert]
          | succ newPos =>
              have hstep : inputStep cert .prefix
                  { input := a, consumed := false, block := blankBlock g }
                  { input := a, consumed := true, block := blankBlock g } = .dead := by
                rw [inputStep_nonmatching cert hcert]
                simp
              simp only [inputPositionCells, evalInputBlocks, Nat.lt_irrefl,
                decide_false, Nat.zero_sub, Nat.zero_lt_succ, decide_true]
              rw [hstep, evalInputBlocks_position_dead]
              simp [inputDone]
      | succ oldPos =>
          cases newPos with
          | zero =>
              have hstep : inputStep cert .prefix
                  { input := a, consumed := true, block := blankBlock g }
                  { input := a, consumed := false, block := blankBlock g } = .dead := by
                rw [inputStep_nonmatching cert hcert]
                simp
              simp only [inputPositionCells, evalInputBlocks, Nat.zero_lt_succ,
                decide_true, Nat.add_sub_cancel, Nat.lt_irrefl, decide_false, Nat.zero_sub]
              rw [hstep, evalInputBlocks_position_dead]
              simp [inputDone]
          | succ newPos =>
              have hold' : oldPos ≤ input.length := by omega
              have hnew' : newPos ≤ input.length := by omega
              simp only [inputPositionCells, evalInputBlocks, Nat.zero_lt_succ,
                decide_true, Nat.add_sub_cancel]
              rw [inputStep_nonmatching cert hcert]
              simp only [ne_eq, not_true_eq_false, if_false]
              simpa using ih oldPos newPos hold' hnew'

private theorem evalInputBlocks_match_zero_matched (g : IndexedGrammar T)
    (a : T) (input : List T) :
    evalInputBlocks (.matchTerminal (g := g) a) .matched
        (inputPositionCells g 0 input)
        (inputPositionCells g 0 input) = .matched := by
  induction input with
  | nil => rfl
  | cons b input ih =>
      simp only [inputPositionCells, evalInputBlocks, Nat.lt_irrefl, decide_false,
        Nat.zero_sub]
      simp only [inputStep, ne_eq, not_true_eq_false, if_false]
      exact ih

private theorem evalInputBlocks_match_zero_succ_dead (g : IndexedGrammar T)
    (a : T) {input : List T} (newPos : ℕ)
    (hnew : newPos + 1 ≤ input.length) :
    evalInputBlocks (.matchTerminal (g := g) a) .matched
        (inputPositionCells g 0 input)
        (inputPositionCells g (newPos + 1) input) = .dead := by
  cases input with
  | nil => simp at hnew
  | cons b input =>
      simp only [inputPositionCells, evalInputBlocks, Nat.lt_irrefl, decide_false,
        Nat.zero_sub, Nat.zero_lt_succ, decide_true, Nat.add_sub_cancel]
      rw [show inputStep (.matchTerminal (g := g) a) .matched
          { input := b, consumed := false, block := blankBlock g }
          { input := b, consumed := true, block := blankBlock g } = .dead by
        simp [inputStep]]
      exact evalInputBlocks_position_dead g (.matchTerminal (g := g) a) 0 newPos input

private theorem evalInputBlocks_match_accepts_iff
    (g : IndexedGrammar T) (a : T) (input : List T) (oldPos newPos : ℕ)
    (hold : oldPos ≤ input.length) (hnew : newPos ≤ input.length) :
    inputDone (.matchTerminal (g := g) a)
        (evalInputBlocks (.matchTerminal (g := g) a) .prefix
          (inputPositionCells g oldPos input)
          (inputPositionCells g newPos input)) = true ↔
      input[oldPos]? = some a ∧ newPos = oldPos + 1 := by
  induction input generalizing oldPos newPos with
  | nil =>
      simp only [List.length_nil] at hold hnew
      have hold0 : oldPos = 0 := by omega
      have hnew0 : newPos = 0 := by omega
      subst oldPos
      subst newPos
      simp [inputPositionCells, evalInputBlocks, inputDone]
  | cons b input ih =>
      simp only [List.length_cons] at hold hnew
      cases oldPos with
      | zero =>
          cases newPos with
          | zero =>
              simp [inputPositionCells, evalInputBlocks, inputStep, inputDone,
                evalInputBlocks_position_dead]
          | succ newPos =>
              cases newPos with
              | zero =>
                  simp only [inputPositionCells, evalInputBlocks, Nat.lt_irrefl,
                    decide_false, Nat.zero_sub, Nat.zero_lt_succ, decide_true,
                    Nat.add_sub_cancel, List.getElem?_cons_zero]
                  by_cases hba : b = a
                  · subst b
                    rw [show inputStep (.matchTerminal (g := g) a) .prefix
                        { input := a, consumed := false, block := blankBlock g }
                        { input := a, consumed := true, block := blankBlock g } = .matched by
                      simp [inputStep]]
                    rw [evalInputBlocks_match_zero_matched]
                    simp [inputDone]
                  · rw [show inputStep (.matchTerminal (g := g) a) .prefix
                        { input := b, consumed := false, block := blankBlock g }
                        { input := b, consumed := true, block := blankBlock g } = .dead by
                      simp [inputStep, hba]]
                    rw [evalInputBlocks_position_dead]
                    simp [inputDone, hba]
              | succ newPos =>
                  have hnew' : newPos + 1 ≤ input.length := by omega
                  simp only [inputPositionCells, evalInputBlocks, Nat.lt_irrefl,
                    decide_false, Nat.zero_sub, Nat.zero_lt_succ, decide_true,
                    Nat.add_sub_cancel, List.getElem?_cons_zero]
                  by_cases hba : b = a
                  · subst b
                    rw [show inputStep (.matchTerminal (g := g) a) .prefix
                        { input := a, consumed := false, block := blankBlock g }
                        { input := a, consumed := true, block := blankBlock g } = .matched by
                      simp [inputStep]]
                    rw [evalInputBlocks_match_zero_succ_dead g a newPos hnew']
                    simp [inputDone]
                  · rw [show inputStep (.matchTerminal (g := g) a) .prefix
                        { input := b, consumed := false, block := blankBlock g }
                        { input := b, consumed := true, block := blankBlock g } = .dead by
                      simp [inputStep, hba]]
                    rw [evalInputBlocks_position_dead]
                    simp [inputDone, hba]
      | succ oldPos =>
          cases newPos with
          | zero =>
              simp only [inputPositionCells, evalInputBlocks, Nat.zero_lt_succ,
                decide_true, Nat.add_sub_cancel, Nat.lt_irrefl, decide_false,
                Nat.zero_sub, List.getElem?_cons_succ]
              rw [show inputStep (.matchTerminal (g := g) a) .prefix
                  { input := b, consumed := true, block := blankBlock g }
                  { input := b, consumed := false, block := blankBlock g } = .dead by
                simp [inputStep]]
              rw [evalInputBlocks_position_dead]
              simp [inputDone]
          | succ newPos =>
              have hold' : oldPos ≤ input.length := by omega
              have hnew' : newPos ≤ input.length := by omega
              simp only [inputPositionCells, evalInputBlocks, Nat.zero_lt_succ,
                decide_true, Nat.add_sub_cancel, List.getElem?_cons_succ]
              rw [show inputStep (.matchTerminal (g := g) a) .prefix
                  { input := b, consumed := true, block := blankBlock g }
                  { input := b, consumed := true, block := blankBlock g } = .prefix by
                simp [inputStep]]
              simpa using ih oldPos newPos hold' hnew'

/-! ## Decoding arbitrary accepted physical input tracks -/

/-- Erase the packed work block while retaining exactly the input letter and consumed bit. -/
public def RunCell.clearBlock (g : IndexedGrammar T) (cell : RunCell g) : RunCell g :=
  { cell with block := blankBlock g }

/-- Block-independent view of a physical running row. -/
public def clearInputBlocks (g : IndexedGrammar T) (row : List (RunCell g)) :
    List (RunCell g) :=
  row.map (RunCell.clearBlock g)

@[simp] public theorem clearInputBlocks_length (g : IndexedGrammar T)
    (row : List (RunCell g)) :
    (clearInputBlocks g row).length = row.length := by
  simp [clearInputBlocks]

@[simp] public theorem inputPositionCells_length (g : IndexedGrammar T)
    (pos : ℕ) (input : List T) :
    (inputPositionCells g pos input).length = input.length := by
  induction input generalizing pos with
  | nil => rfl
  | cons a input ih => simp [inputPositionCells, ih]

/-- Clearing blocks from a genuine encoded row gives its canonical input-position track. -/
public theorem clearInputBlocks_encodeRunCellsFrom
    (g : IndexedGrammar T) (work : List (WorkSlot g))
    (pos cell : ℕ) (input : List T) :
    clearInputBlocks g (encodeRunCellsFrom g work pos cell input) =
      inputPositionCells g (pos - cell) input := by
  induction input generalizing cell with
  | nil => rfl
  | cons a input ih =>
      have hbit : decide (cell < pos) = decide (0 < pos - cell) := by
        by_cases h : cell < pos
        · have h' : 0 < pos - cell := by omega
          simp [h, h']
        · have h' : ¬ 0 < pos - cell := by omega
          simp [h, h']
      have hsub : pos - cell - 1 = pos - (cell + 1) := by omega
      simp only [encodeRunCellsFrom, clearInputBlocks, List.map_cons,
        RunCell.clearBlock, inputPositionCells, hbit, List.cons.injEq]
      simpa [hsub] using ih (cell + 1)

@[simp] public theorem clearInputBlocks_encodeRunCells
    (g : IndexedGrammar T) (input : List T) (c : Config g) :
    clearInputBlocks g (encodeRunCells g input c) =
      inputPositionCells g c.inputPos input := by
  simpa [encodeRunCells] using
    clearInputBlocks_encodeRunCellsFrom g c.work.slots c.inputPos 0 input

@[simp] public theorem runBlocks_map_runCells (cells : List (RunCell g)) :
    runBlocks (cells.map RowCell.run) = some (cells.map RunCell.block) := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => simp [runBlocks, ih]

/-- Packed work blocks underlying an encoded list of running cells. -/
public theorem map_block_encodeRunCellsFrom
    (g : IndexedGrammar T) (work : List (WorkSlot g))
    (pos cell : ℕ) (input : List T) :
    (encodeRunCellsFrom g work pos cell input).map RunCell.block =
      packedBlockList g work cell input.length := by
  have h := runBlocks_encodeRunRowFrom g work pos cell input
  rw [encodeRunRowFrom_eq_map_run, runBlocks_map_runCells] at h
  exact Option.some.inj h

public theorem map_block_encodeRunCells
    (g : IndexedGrammar T) (input : List T) (c : Config g) :
    (encodeRunCells g input c).map RunCell.block =
      packedBlockList g c.work.slots 0 input.length := by
  exact map_block_encodeRunCellsFrom g c.work.slots c.inputPos 0 input

/-- Running rows are determined by their input/consumption projection and their packed blocks. -/
public theorem runCells_eq_of_clearInputBlocks_eq_of_map_block_eq
    (g : IndexedGrammar T) {old new : List (RunCell g)}
    (hclear : clearInputBlocks g old = clearInputBlocks g new)
    (hblocks : old.map RunCell.block = new.map RunCell.block) :
    old = new := by
  induction old generalizing new with
  | nil =>
      cases new with
      | nil => rfl
      | cons new news => simp [clearInputBlocks] at hclear
  | cons old olds ih =>
      cases new with
      | nil => simp [clearInputBlocks] at hclear
      | cons new news =>
          simp only [clearInputBlocks, List.map_cons, List.cons.injEq] at hclear hblocks
          have hhead : old = new := by
            rcases old with ⟨oldInput, oldConsumed, oldBlock⟩
            rcases new with ⟨newInput, newConsumed, newBlock⟩
            simp only [RunCell.clearBlock, RunCell.mk.injEq] at hclear
            rcases hclear.1 with ⟨rfl, rfl, _⟩
            have hblock : oldBlock = newBlock := hblocks.1
            rw [hblock]
          subst new
          exact congrArg (List.cons old) (ih hclear.2 hblocks.2)

/-- Combine an input-track decoder with a packed-block decoder to reconstruct the exact running
cells of an encoded work cursor. -/
public theorem eq_encodeRunCellsFrom_of_clear_of_blocks
    (g : IndexedGrammar T) (row : List (RunCell g))
    (work : List (WorkSlot g)) (pos cell : ℕ) (input : List T)
    (hclear : clearInputBlocks g row = inputPositionCells g (pos - cell) input)
    (hblocks : row.map RunCell.block = packedBlockList g work cell input.length) :
    row = encodeRunCellsFrom g work pos cell input := by
  apply runCells_eq_of_clearInputBlocks_eq_of_map_block_eq g
  · rw [hclear, clearInputBlocks_encodeRunCellsFrom]
  · rw [hblocks, map_block_encodeRunCellsFrom]

@[simp] private theorem inputStep_dead (cert : CompositeCert g)
    (old new : RunCell g) : inputStep cert .dead old new = .dead := by
  cases cert <;> simp [inputStep]

@[simp] private theorem evalInputBlocks_dead (cert : CompositeCert g)
    (old new : List (RunCell g)) :
    evalInputBlocks cert .dead old new = .dead := by
  induction old generalizing new with
  | nil => cases new <;> rfl
  | cons old olds ih =>
      cases new with
      | nil => rfl
      | cons new news =>
          simp only [evalInputBlocks, inputStep_dead]
          exact ih news

private theorem decode_nonmatching_tail
    (g : IndexedGrammar T) (cert : CompositeCert g) (hcert : cert.Nonmatching)
    (old new : List (RunCell g))
    (haccept : inputDone cert (evalInputBlocks cert .tail old new) = true) :
    ∃ input : List T,
      clearInputBlocks g old = inputPositionCells g 0 input ∧
      clearInputBlocks g new = inputPositionCells g 0 input := by
  induction old generalizing new with
  | nil =>
      cases new with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons new news => simp [evalInputBlocks, inputDone] at haccept
  | cons old olds ih =>
      cases new with
      | nil => simp [evalInputBlocks, inputDone] at haccept
      | cons new news =>
          rcases old with ⟨oldInput, oldConsumed, oldBlock⟩
          rcases new with ⟨newInput, newConsumed, newBlock⟩
          by_cases hinput : oldInput = newInput
          · subst newInput
            cases oldConsumed <;> cases newConsumed
            · have htail : inputDone cert
                  (evalInputBlocks cert .tail olds news) = true := by
                simpa [evalInputBlocks, inputStep_nonmatching cert hcert] using haccept
              rcases ih news htail with ⟨input, hold, hnew⟩
              refine ⟨oldInput :: input, ?_, ?_⟩
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := false, block := blankBlock g }) hold
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := false, block := blankBlock g }) hnew
            · simp [evalInputBlocks, inputStep_nonmatching cert hcert,
                evalInputBlocks_dead, inputDone] at haccept
            · simp [evalInputBlocks, inputStep_nonmatching cert hcert,
                evalInputBlocks_dead, inputDone] at haccept
            · simp [evalInputBlocks, inputStep_nonmatching cert hcert,
                evalInputBlocks_dead, inputDone] at haccept
          · simp [evalInputBlocks, inputStep_nonmatching cert hcert, hinput,
              evalInputBlocks_dead, inputDone] at haccept

private theorem decode_nonmatching_prefix
    (g : IndexedGrammar T) (cert : CompositeCert g) (hcert : cert.Nonmatching)
    (old new : List (RunCell g))
    (haccept : inputDone cert (evalInputBlocks cert .prefix old new) = true) :
    ∃ (input : List T) (pos : ℕ),
      pos ≤ input.length ∧
      clearInputBlocks g old = inputPositionCells g pos input ∧
      clearInputBlocks g new = inputPositionCells g pos input := by
  induction old generalizing new with
  | nil =>
      cases new with
      | nil => exact ⟨[], 0, by simp, rfl, rfl⟩
      | cons new news => simp [evalInputBlocks, inputDone] at haccept
  | cons old olds ih =>
      cases new with
      | nil => simp [evalInputBlocks, inputDone] at haccept
      | cons new news =>
          rcases old with ⟨oldInput, oldConsumed, oldBlock⟩
          rcases new with ⟨newInput, newConsumed, newBlock⟩
          by_cases hinput : oldInput = newInput
          · subst newInput
            cases oldConsumed <;> cases newConsumed
            · have htail : inputDone cert
                  (evalInputBlocks cert .tail olds news) = true := by
                simpa [evalInputBlocks, inputStep_nonmatching cert hcert] using haccept
              rcases decode_nonmatching_tail g cert hcert olds news htail with
                ⟨input, hold, hnew⟩
              refine ⟨oldInput :: input, 0, by simp, ?_, ?_⟩
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := false, block := blankBlock g }) hold
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := false, block := blankBlock g }) hnew
            · simp [evalInputBlocks, inputStep_nonmatching cert hcert,
                evalInputBlocks_dead, inputDone] at haccept
            · simp [evalInputBlocks, inputStep_nonmatching cert hcert,
                evalInputBlocks_dead, inputDone] at haccept
            · have htail : inputDone cert
                  (evalInputBlocks cert .prefix olds news) = true := by
                simpa [evalInputBlocks, inputStep_nonmatching cert hcert] using haccept
              rcases ih news htail with ⟨input, pos, hpos, hold, hnew⟩
              refine ⟨oldInput :: input, pos + 1, by simp; omega, ?_, ?_⟩
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := true, block := blankBlock g }) hold
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := true, block := blankBlock g }) hnew
          · simp [evalInputBlocks, inputStep_nonmatching cert hcert, hinput,
              evalInputBlocks_dead, inputDone] at haccept

private theorem decode_match_matched
    (g : IndexedGrammar T) (a : T) (old new : List (RunCell g))
    (haccept : inputDone (.matchTerminal (g := g) a)
      (evalInputBlocks (.matchTerminal (g := g) a) .matched old new) = true) :
    ∃ input : List T,
      clearInputBlocks g old = inputPositionCells g 0 input ∧
      clearInputBlocks g new = inputPositionCells g 0 input := by
  induction old generalizing new with
  | nil =>
      cases new with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons new news => simp [evalInputBlocks, inputDone] at haccept
  | cons old olds ih =>
      cases new with
      | nil => simp [evalInputBlocks, inputDone] at haccept
      | cons new news =>
          rcases old with ⟨oldInput, oldConsumed, oldBlock⟩
          rcases new with ⟨newInput, newConsumed, newBlock⟩
          by_cases hinput : oldInput = newInput
          · subst newInput
            cases oldConsumed <;> cases newConsumed
            · have htail : inputDone (.matchTerminal (g := g) a)
                  (evalInputBlocks (.matchTerminal (g := g) a) .matched olds news) = true := by
                simpa [evalInputBlocks, inputStep] using haccept
              rcases ih news htail with ⟨input, hold, hnew⟩
              refine ⟨oldInput :: input, ?_, ?_⟩
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := false, block := blankBlock g }) hold
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := false, block := blankBlock g }) hnew
            · simp [evalInputBlocks, inputStep, evalInputBlocks_dead, inputDone] at haccept
            · simp [evalInputBlocks, inputStep, evalInputBlocks_dead, inputDone] at haccept
            · simp [evalInputBlocks, inputStep, evalInputBlocks_dead, inputDone] at haccept
          · simp [evalInputBlocks, inputStep, hinput, evalInputBlocks_dead,
              inputDone] at haccept

private theorem decode_match_prefix
    (g : IndexedGrammar T) (a : T) (old new : List (RunCell g))
    (haccept : inputDone (.matchTerminal (g := g) a)
      (evalInputBlocks (.matchTerminal (g := g) a) .prefix old new) = true) :
    ∃ (input : List T) (pos : ℕ),
      pos < input.length ∧ input[pos]? = some a ∧
      clearInputBlocks g old = inputPositionCells g pos input ∧
      clearInputBlocks g new = inputPositionCells g (pos + 1) input := by
  induction old generalizing new with
  | nil => cases new <;> simp [evalInputBlocks, inputDone] at haccept
  | cons old olds ih =>
      cases new with
      | nil => simp [evalInputBlocks, inputDone] at haccept
      | cons new news =>
          rcases old with ⟨oldInput, oldConsumed, oldBlock⟩
          rcases new with ⟨newInput, newConsumed, newBlock⟩
          by_cases hinput : oldInput = newInput
          · subst newInput
            cases oldConsumed <;> cases newConsumed
            · simp [evalInputBlocks, inputStep, evalInputBlocks_dead, inputDone] at haccept
            · by_cases hletter : oldInput = a
              · subst oldInput
                have htail : inputDone (.matchTerminal (g := g) a)
                    (evalInputBlocks (.matchTerminal (g := g) a) .matched olds news) =
                    true := by
                  simpa [evalInputBlocks, inputStep] using haccept
                rcases decode_match_matched g a olds news htail with
                  ⟨input, hold, hnew⟩
                refine ⟨a :: input, 0, by simp, by simp, ?_, ?_⟩
                · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                    congrArg (List.cons
                      { input := a, consumed := false, block := blankBlock g }) hold
                · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                    congrArg (List.cons
                      { input := a, consumed := true, block := blankBlock g }) hnew
              · simp [evalInputBlocks, inputStep, hletter, evalInputBlocks_dead,
                  inputDone] at haccept
            · simp [evalInputBlocks, inputStep, evalInputBlocks_dead, inputDone] at haccept
            · have htail : inputDone (.matchTerminal (g := g) a)
                  (evalInputBlocks (.matchTerminal (g := g) a) .prefix olds news) = true := by
                simpa [evalInputBlocks, inputStep] using haccept
              rcases ih news htail with ⟨input, pos, hpos, hletter, hold, hnew⟩
              refine ⟨oldInput :: input, pos + 1, by simp; omega, ?_, ?_, ?_⟩
              · simpa using hletter
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := true, block := blankBlock g }) hold
              · simpa [clearInputBlocks, RunCell.clearBlock, inputPositionCells] using
                  congrArg (List.cons
                    { input := oldInput, consumed := true, block := blankBlock g }) hnew
          · simp [evalInputBlocks, inputStep, hinput, evalInputBlocks_dead,
              inputDone] at haccept

/-- Soundness decoder for arbitrary physical running rows.  An accepted input scan reconstructs
a common immutable input word, canonical consumed-prefix positions, and exactly the input action
named by its certificate.  Packed work blocks are intentionally erased from the row equalities. -/
public theorem evalInputBlocks_decode
    (g : IndexedGrammar T) (cert : CompositeCert g)
    (old new : List (RunCell g))
    (haccept : inputDone cert (evalInputBlocks cert .prefix old new) = true) :
    ∃ (input : List T) (oldPos newPos : ℕ),
      oldPos ≤ input.length ∧ newPos ≤ input.length ∧
      clearInputBlocks g old = inputPositionCells g oldPos input ∧
      clearInputBlocks g new = inputPositionCells g newPos input ∧
      cert.InputAction input oldPos newPos := by
  cases cert with
  | matchTerminal a =>
      rcases decode_match_prefix g a old new haccept with
        ⟨input, pos, hpos, hletter, hold, hnew⟩
      exact ⟨input, pos, pos + 1, Nat.le_of_lt hpos, hpos,
        hold, hnew, hletter, rfl⟩
  | plainBinary A B C =>
      rcases decode_nonmatching_prefix g (.plainBinary A B C) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | plainTerminal A a =>
      rcases decode_nonmatching_prefix g (.plainTerminal A a) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | plainPushSkip A B f =>
      rcases decode_nonmatching_prefix g (.plainPushSkip A B f) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | plainPushUse A B f =>
      rcases decode_nonmatching_prefix g (.plainPushUse A B f) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | liveBinaryBoth A B C =>
      rcases decode_nonmatching_prefix g (.liveBinaryBoth A B C) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | liveBinaryLeft A B C =>
      rcases decode_nonmatching_prefix g (.liveBinaryLeft A B C) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | liveBinaryRight A B C =>
      rcases decode_nonmatching_prefix g (.liveBinaryRight A B C) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | livePushFresh A B f =>
      rcases decode_nonmatching_prefix g (.livePushFresh A B f) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | livePushCompress A B f R d =>
      rcases decode_nonmatching_prefix g (.livePushCompress A B f R d) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | popPlain R d A B =>
      rcases decode_nonmatching_prefix g (.popPlain R d A B) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | popLive R d A B =>
      rcases decode_nonmatching_prefix g (.popLive R d A B) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | eraseIndex R d =>
      rcases decode_nonmatching_prefix g (.eraseIndex R d) trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩
  | returnFrame =>
      rcases decode_nonmatching_prefix g .returnFrame trivial old new haccept with
        ⟨input, pos, hpos, hold, hnew⟩
      exact ⟨input, pos, pos, hpos, hpos, hold, hnew, rfl⟩

/-- Exact input-track correctness for encoded configurations. -/
public theorem evalInputBlocks_encodeRunCells_accepts_iff
    (g : IndexedGrammar T) (cert : CompositeCert g) (input : List T)
    (old new : Config g)
    (hold : old.inputPos ≤ input.length) (hnew : new.inputPos ≤ input.length) :
    inputDone cert
        (evalInputBlocks cert .prefix
          (encodeRunCells g input old) (encodeRunCells g input new)) = true ↔
      cert.InputAction input old.inputPos new.inputPos := by
  rw [evalInputBlocks_encodeRunCells_eq_positionCells]
  cases cert with
  | matchTerminal a =>
      exact evalInputBlocks_match_accepts_iff g a input old.inputPos new.inputPos hold hnew
  | plainBinary A B C =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.plainBinary A B C) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | plainTerminal A a =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.plainTerminal A a) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | plainPushSkip A B f =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.plainPushSkip A B f) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | plainPushUse A B f =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.plainPushUse A B f) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | liveBinaryBoth A B C =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.liveBinaryBoth A B C) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | liveBinaryLeft A B C =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.liveBinaryLeft A B C) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | liveBinaryRight A B C =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.liveBinaryRight A B C) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | livePushFresh A B f =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.livePushFresh A B f) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | livePushCompress A B f R d =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.livePushCompress A B f R d) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | popPlain R d A B =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.popPlain R d A B) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | popLive R d A B =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.popLive R d A B) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | eraseIndex R d =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g (.eraseIndex R d) (by trivial)
          input old.inputPos new.inputPos hold hnew)
  | returnFrame =>
      simpa [CompositeCert.InputAction] using
        (evalInputBlocks_nonmatching_accepts_iff g .returnFrame (by trivial)
          input old.inputPos new.inputPos hold hnew)

/-- Completeness direction of `evalInputBlocks_encodeRunCells_accepts_iff`. -/
public theorem evalInputBlocks_encodeRunCells_complete
    (g : IndexedGrammar T) (cert : CompositeCert g) (input : List T)
    (old new : Config g)
    (hold : old.inputPos ≤ input.length) (hnew : new.inputPos ≤ input.length)
    (haction : cert.InputAction input old.inputPos new.inputPos) :
    inputDone cert
        (evalInputBlocks cert .prefix
          (encodeRunCells g input old) (encodeRunCells g input new)) = true :=
  (evalInputBlocks_encodeRunCells_accepts_iff g cert input old new hold hnew).2 haction

/-- Soundness direction of `evalInputBlocks_encodeRunCells_accepts_iff`. -/
public theorem evalInputBlocks_encodeRunCells_sound
    (g : IndexedGrammar T) (cert : CompositeCert g) (input : List T)
    (old new : Config g)
    (hold : old.inputPos ≤ input.length) (hnew : new.inputPos ≤ input.length)
    (haccept : inputDone cert
      (evalInputBlocks cert .prefix
        (encodeRunCells g input old) (encodeRunCells g input new)) = true) :
    cert.InputAction input old.inputPos new.inputPos :=
  (evalInputBlocks_encodeRunCells_accepts_iff g cert input old new hold hnew).1 haccept

end Aho
end IndexedGrammar

