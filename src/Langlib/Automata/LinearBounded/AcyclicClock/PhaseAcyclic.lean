module

public import Langlib.Automata.LinearBounded.AcyclicClock.Construction
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

@[expose]
public section

/-!
# Phase acyclicity of the guarded clock compiler

This file proves the malformed-configuration, phase-local half of global acyclicity for
`AcyclicClock.machine`.  It deliberately does not prove the remaining `ready`-to-`ready`
clock-growth argument.

Every directional loop changes a one-shot bit before moving.  Counting those bits over the
entire physical tape gives a strict local rank.  The `carry`/`carryCheck` pair uses the parity
rank `2 * carryCount + stateBit`.  A phase stride larger than every local rank combines these
measures into one natural-valued potential.

The result quantifies over every bounded tape width and every raw configuration.  In particular,
no well-formedness, unique-marker, or canonical-input invariant is assumed.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- A control state is a `ready` state exactly when a completed macro may begin or end there. -/
public def State.IsReady : State Λ → Prop
  | .ready _ => True
  | _ => False

/-- Lift a Boolean predicate on work cells to the full target tape alphabet.  Raw symbols never
contribute to a work-cell count. -/
public def workPredicate
    (predicate : WorkCell T Γ Λ → Bool) :
    TapeAlpha T Γ Λ → Bool
  | .inl (some (.inr cell)) => predicate cell
  | _ => false

@[simp]
public theorem workPredicate_workSymbol
    (predicate : WorkCell T Γ Λ → Bool)
    (cell : WorkCell T Γ Λ) :
    workPredicate predicate (workSymbol cell) = predicate cell :=
  rfl

/-- Number of physical cells satisfying a tape-symbol predicate. -/
public def symbolCount {n : ℕ}
    (predicate : TapeAlpha T Γ Λ → Bool)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  ∑ i : Fin (n + 1), if predicate (tape.contents i) then 1 else 0

/-- Number of converted work cells satisfying a work-cell predicate. -/
public def workCellCount {n : ℕ}
    (predicate : WorkCell T Γ Λ → Bool)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  symbolCount (workPredicate predicate) tape

/-- Number of already converted physical cells. -/
public def convertedCount {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  workCellCount (fun _ => true) tape

/-- Number of work cells whose initialization-return bit has already been cleared. -/
public def initClearedCount {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  workCellCount (fun cell => !cell.init) tape

/-- Number of set guarded-left-sweep bits. -/
public def seekCount {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  workCellCount (fun cell => cell.seek) tape

/-- Number of set normalization bits. -/
public def normCount {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  workCellCount (fun cell => cell.norm) tape

/-- Number of converted cells whose normalization bit has been cleared. -/
public def normClearedCount {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  workCellCount (fun cell => !cell.norm) tape

/-- Number of carry-passed cells. -/
public def carryCount {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  workCellCount (fun cell => cell.carry) tape

/-- Number of guarded post-increment return cells. -/
public def postCount {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  workCellCount (fun cell => cell.post) tape

/-- Number of guarded source-mark-search cells. -/
public def scanCount {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  workCellCount (fun cell => cell.scan) tape

/-- Every symbol count is bounded by the number of physical tape cells. -/
public theorem symbolCount_le_width {n : ℕ}
    (predicate : TapeAlpha T Γ Λ → Bool)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    symbolCount predicate tape ≤ n + 1 := by
  unfold symbolCount
  calc
    (∑ i : Fin (n + 1), if predicate (tape.contents i) then 1 else 0) ≤
        ∑ _i : Fin (n + 1), 1 := by
      apply Finset.sum_le_sum
      intro i hi
      split <;> omega
    _ = n + 1 := by simp

/-- Every work-cell count is bounded by the physical tape width. -/
public theorem workCellCount_le_width {n : ℕ}
    (predicate : WorkCell T Γ Λ → Bool)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    workCellCount predicate tape ≤ n + 1 :=
  symbolCount_le_width (workPredicate predicate) tape

/-- Replacing the scanned cell changes a false predicate to true, so the global count rises by
exactly one.  Head movement is irrelevant because it does not change tape contents. -/
private theorem symbolCount_write_false_true {n : ℕ}
    (predicate : TapeAlpha T Γ Λ → Bool)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (symbol : TapeAlpha T Γ Λ) (direction : DLBA.Dir)
    (hold : predicate tape.read = false)
    (hnew : predicate symbol = true) :
    symbolCount predicate ((tape.write symbol).moveHead direction) =
      symbolCount predicate tape + 1 := by
  let oldTerm : Fin (n + 1) → ℕ :=
    fun i => if predicate (tape.contents i) then 1 else 0
  let newTerm : Fin (n + 1) → ℕ :=
    fun i =>
      if predicate (Function.update tape.contents tape.head symbol i) then 1 else 0
  have hheadOld : oldTerm tape.head = 0 := by
    change predicate (tape.contents tape.head) = false at hold
    simp [oldTerm, hold]
  have hheadNew : newTerm tape.head = 1 := by
    simp [newTerm, hnew]
  have hoff :
      ∀ i ∈ (Finset.univ.erase tape.head), newTerm i = oldTerm i := by
    intro i hi
    have hne : i ≠ tape.head := Finset.ne_of_mem_erase hi
    dsimp [newTerm, oldTerm]
    rw [Function.update_of_ne hne]
  have hsum :
      (∑ i ∈ Finset.univ.erase tape.head, newTerm i) =
        ∑ i ∈ Finset.univ.erase tape.head, oldTerm i := by
    apply Finset.sum_congr rfl
    exact hoff
  have hmem :
      tape.head ∈ (Finset.univ : Finset (Fin (n + 1))) :=
    Finset.mem_univ _
  simp only [symbolCount, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
  change (∑ i, newTerm i) = (∑ i, oldTerm i) + 1
  rw [← Finset.sum_erase_add Finset.univ newTerm hmem,
    ← Finset.sum_erase_add Finset.univ oldTerm hmem,
    hsum, hheadOld, hheadNew]

/-- Writing back the currently read symbol preserves every tape-symbol count. -/
private theorem symbolCount_write_read {n : ℕ}
    (predicate : TapeAlpha T Γ Λ → Bool)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (direction : DLBA.Dir) :
    symbolCount predicate ((tape.write tape.read).moveHead direction) =
      symbolCount predicate tape := by
  cases tape
  simp [symbolCount, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
    Function.update_eq_self]

/-- Work-cell form of the one-cell false-to-true count update. -/
private theorem workCellCount_write_false_true {n : ℕ}
    (predicate : WorkCell T Γ Λ → Bool)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (old new : WorkCell T Γ Λ) (direction : DLBA.Dir)
    (hread : tape.read = workSymbol old)
    (hold : predicate old = false)
    (hnew : predicate new = true) :
    workCellCount predicate
        ((tape.write (workSymbol new)).moveHead direction) =
      workCellCount predicate tape + 1 := by
  apply symbolCount_write_false_true
  · rw [hread]
    exact workPredicate_workSymbol predicate old ▸ hold
  · exact workPredicate_workSymbol predicate new ▸ hnew

/-- Every work-cell count is preserved when the transition writes back the scanned symbol. -/
private theorem workCellCount_write_read {n : ℕ}
    (predicate : WorkCell T Γ Λ → Bool)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (direction : DLBA.Dir) :
    workCellCount predicate ((tape.write tape.read).moveHead direction) =
      workCellCount predicate tape :=
  symbolCount_write_read (workPredicate predicate) tape direction

/-- Coarse phase number.  `carry` and `carryCheck` intentionally share one phase. -/
public def phaseIndex : State Λ → ℕ
  | .initFirst => 0
  | .initSweep => 1
  | .initBack => 2
  | .ready _ => 0
  | .mark _ => 3
  | .seek _ => 4
  | .cleanR _ => 5
  | .cleanL _ => 6
  | .carry _ | .carryCheck _ => 7
  | .returnL _ => 8
  | .findMark _ => 9

/-- Local progress rank inside one phase. -/
public def localRank {n : ℕ}
    (state : State Λ)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  match state with
  | .initSweep => convertedCount tape
  | .initBack => initClearedCount tape
  | .seek _ => seekCount tape
  | .cleanR _ => normCount tape
  | .cleanL _ => normClearedCount tape
  | .carry _ => 2 * carryCount tape + 1
  | .carryCheck _ => 2 * carryCount tape
  | .returnL _ => postCount tape
  | .findMark _ => scanCount tape
  | _ => 0

/-- One phase block is larger than every possible local rank. -/
public def phaseStride (n : ℕ) : ℕ :=
  2 * (n + 1) + 2

/-- Explicit phase potential for every raw bounded configuration. -/
public def phasePotential {n : ℕ}
    (cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) : ℕ :=
  phaseIndex cfg.state * phaseStride n + localRank cfg.state cfg.tape

/-- Every local phase rank fits strictly inside one phase block. -/
public theorem localRank_lt_phaseStride {n : ℕ}
    (state : State Λ)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    localRank state tape < phaseStride n := by
  have hconverted :
      convertedCount tape ≤ n + 1 :=
    workCellCount_le_width (fun _ => true) tape
  have hinit :
      initClearedCount tape ≤ n + 1 :=
    workCellCount_le_width (fun cell => !cell.init) tape
  have hseek :
      seekCount tape ≤ n + 1 :=
    workCellCount_le_width (fun cell => cell.seek) tape
  have hnorm :
      normCount tape ≤ n + 1 :=
    workCellCount_le_width (fun cell => cell.norm) tape
  have hnormCleared :
      normClearedCount tape ≤ n + 1 :=
    workCellCount_le_width (fun cell => !cell.norm) tape
  have hcarry :
      carryCount tape ≤ n + 1 :=
    workCellCount_le_width (fun cell => cell.carry) tape
  have hpost :
      postCount tape ≤ n + 1 :=
    workCellCount_le_width (fun cell => cell.post) tape
  have hscan :
      scanCount tape ≤ n + 1 :=
    workCellCount_le_width (fun cell => cell.scan) tape
  cases state <;>
    simp only [localRank, phaseStride] <;>
    omega

/-- Advancing to a later coarse phase strictly raises the full potential, regardless of the
new phase's local rank. -/
private theorem phasePotential_lt_of_phaseIndex_lt {n : ℕ}
    {oldState newState : State Λ}
    {oldTape newTape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n}
    (hphase : phaseIndex oldState < phaseIndex newState) :
    phasePotential (⟨oldState, oldTape⟩ :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) <
      phasePotential ⟨newState, newTape⟩ := by
  have hlocal := localRank_lt_phaseStride
    (T := T) (Γ := Γ) (Λ := Λ) oldState oldTape
  unfold phasePotential
  calc
    phaseIndex oldState * phaseStride n + localRank oldState oldTape <
        phaseIndex oldState * phaseStride n + phaseStride n :=
      Nat.add_lt_add_left hlocal _
    _ = (phaseIndex oldState + 1) * phaseStride n := by
      simp [Nat.add_mul]
    _ ≤ phaseIndex newState * phaseStride n := by
      exact Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hphase)
    _ ≤ phaseIndex newState * phaseStride n + localRank newState newTape :=
      Nat.le_add_right _ _

/-! ## Every non-ready edge raises the phase potential -/

/-- Every machine step whose source and target are both non-`ready` strictly raises the explicit
phase potential.  This is global over all raw tapes and all tape widths. -/
public theorem nonready_step_phasePotential_lt
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hstep : LBA.Step (machine M) old new)
    (hold : ¬ old.state.IsReady)
    (hnew : ¬ new.state.IsReady) :
    phasePotential old < phasePotential new := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rcases old with ⟨state, tape⟩
  rcases tape with ⟨contents, head⟩
  let tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n := ⟨contents, head⟩
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  change (next, written, direction) ∈ transition M state (contents head) at hmem
  change phasePotential (⟨state, tape⟩ :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) <
    phasePotential ⟨next, (tape.write written).moveHead direction⟩
  cases state with
  | initFirst =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · rw [hread] at hmem
        change (next, written, direction) ∈ (∅ : Set
          (State Λ × TapeAlpha T Γ Λ × DLBA.Dir)) at hmem
        exact hmem.elim
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · simp [transition, hread] at hmem
      · cases boundary with
        | false =>
            simp only [transition, hread, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact phasePotential_lt_of_phaseIndex_lt (by simp [phaseIndex])
        | true =>
            simp [transition, hread] at hmem
  | initSweep =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp only [transition, hread, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        have hcount :
            convertedCount
                ((tape.write
                  (workSymbol
                    (freshCell (clockZero M) (.inl none) false false))).moveHead
                    .right) =
              convertedCount tape + 1 := by
          apply symbolCount_write_false_true
          · change workPredicate
              (fun _ : WorkCell T Γ Λ => true) (contents head) = false
            rw [hread]
            rfl
          · rfl
        simp only [phasePotential, phaseIndex, localRank]
        rw [hcount]
        omega
      · rcases inputOrWork with input | cell
        · simp only [transition, hread, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          have hcount :
              convertedCount
                  ((tape.write
                    (workSymbol
                      (freshCell (clockZero M)
                        (.inl (some (.inl input))) false false))).moveHead
                      .right) =
                convertedCount tape + 1 := by
            apply symbolCount_write_false_true
            · change workPredicate
                (fun _ : WorkCell T Γ Λ => true) (contents head) = false
              rw [hread]
              rfl
            · rfl
          simp only [phasePotential, phaseIndex, localRank]
          rw [hcount]
          omega
        · by_cases hinit : cell.init = true
          · simp only [transition, hread, if_pos hinit,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact phasePotential_lt_of_phaseIndex_lt (by simp [phaseIndex])
          · simp [transition, hread, hinit] at hmem
      · simp only [transition, hread, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        have hcount :
            convertedCount
                ((tape.write
                  (workSymbol
                    (freshCell (clockZero M) (.inr boundary) false false))).moveHead
                    .right) =
              convertedCount tape + 1 := by
          apply symbolCount_write_false_true
          · change workPredicate
              (fun _ : WorkCell T Γ Λ => true) (contents head) = false
            rw [hread]
            rfl
          · rfl
        simp only [phasePotential, phaseIndex, localRank]
        rw [hcount]
        omega
  | initBack =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · by_cases hleft : cell.left = true
          · by_cases hinit : cell.init = true
            · simp only [transition, hread, if_pos hleft, if_pos hinit,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact (hnew trivial).elim
            · simp [transition, hread, hleft, hinit] at hmem
          · by_cases hinit : cell.init = true
            · simp only [transition, hread, if_neg hleft, if_pos hinit,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              have hcount :
                  initClearedCount
                      ((tape.write
                        (workSymbol { cell with init := false })).moveHead .left) =
                    initClearedCount tape + 1 := by
                apply workCellCount_write_false_true
                    (fun work => !work.init) tape cell
                    { cell with init := false } .left hread
                · simp [hinit]
                · rfl
              simp only [phasePotential, phaseIndex, localRank]
              rw [hcount]
              omega
            · simp [transition, hread, hleft, hinit] at hmem
      · simp [transition, hread] at hmem
  | ready source =>
      exact (hold trivial).elim
  | mark source =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · simp only [transition, hread, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          exact phasePotential_lt_of_phaseIndex_lt (by simp [phaseIndex])
      · simp [transition, hread] at hmem
  | seek source =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · by_cases hleft : cell.left = true
          · simp only [transition, hread, if_pos hleft,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact phasePotential_lt_of_phaseIndex_lt (by simp [phaseIndex])
          · by_cases hseek : cell.seek = true
            · simp [transition, hread, hleft, hseek] at hmem
            · simp only [transition, hread, if_neg hleft, if_neg hseek,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              have hcount :
                  seekCount
                      ((tape.write
                        (workSymbol { cell with seek := true })).moveHead .left) =
                    seekCount tape + 1 := by
                apply workCellCount_write_false_true
                    (fun work => work.seek) tape cell
                    { cell with seek := true } .left hread
                · simpa using hseek
                · rfl
              simp only [phasePotential, phaseIndex, localRank]
              rw [hcount]
              omega
      · simp [transition, hread] at hmem
  | cleanR source =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · by_cases hnorm : cell.norm = true
          · simp [transition, hread, hnorm] at hmem
          · by_cases hright : cell.right = true
            · simp only [transition, hread, if_neg hnorm, if_pos hright,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact phasePotential_lt_of_phaseIndex_lt (by simp [phaseIndex])
            · simp only [transition, hread, if_neg hnorm, if_neg hright,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              have hcount :
                  normCount
                      ((tape.write
                        (workSymbol cell.normalizedRight)).moveHead .right) =
                    normCount tape + 1 := by
                apply workCellCount_write_false_true
                    (fun work => work.norm) tape cell
                    cell.normalizedRight .right hread
                · simpa using hnorm
                · rfl
              simp only [phasePotential, phaseIndex, localRank]
              rw [hcount]
              omega
      · simp [transition, hread] at hmem
  | cleanL source =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · by_cases hleft : cell.left = true
          · by_cases hnorm : cell.norm = true
            · simp only [transition, hread, if_pos hleft, if_pos hnorm,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact phasePotential_lt_of_phaseIndex_lt (by simp [phaseIndex])
            · simp [transition, hread, hleft, hnorm] at hmem
          · by_cases hnorm : cell.norm = true
            · simp only [transition, hread, if_neg hleft, if_pos hnorm,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              have hcount :
                  normClearedCount
                      ((tape.write
                        (workSymbol cell.clearTransient)).moveHead .left) =
                    normClearedCount tape + 1 := by
                apply workCellCount_write_false_true
                    (fun work => !work.norm) tape cell
                    cell.clearTransient .left hread
                · simp [hnorm]
                · rfl
              simp only [phasePotential, phaseIndex, localRank]
              rw [hcount]
              omega
            · simp [transition, hread, hleft, hnorm] at hmem
      · simp [transition, hread] at hmem
  | carry source =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · by_cases hcarry : cell.carry = true
          · simp [transition, hread, hcarry] at hmem
          · cases hnext :
              (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next cell.digit with
            | some digit =>
                simp only [transition, hread, if_neg hcarry, hnext,
                  Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨rfl, rfl, rfl⟩
                exact phasePotential_lt_of_phaseIndex_lt (by simp [phaseIndex])
            | none =>
                by_cases hright : cell.right = true
                · simp [transition, hread, hcarry, hnext, hright] at hmem
                · simp only [transition, hread, if_neg hcarry, hnext,
                    if_neg hright, Set.mem_singleton_iff,
                    Prod.mk.injEq] at hmem
                  rcases hmem with ⟨rfl, rfl, rfl⟩
                  have hcount :
                      carryCount
                          ((tape.write
                            (workSymbol
                              { cell with
                                digit := clockZero M
                                carry := true })).moveHead .right) =
                        carryCount tape + 1 := by
                    apply workCellCount_write_false_true
                        (fun work => work.carry) tape cell
                        { cell with
                          digit := clockZero M
                          carry := true } .right hread
                    · simpa using hcarry
                    · rfl
                  simp only [phasePotential, phaseIndex, localRank]
                  rw [hcount]
                  omega
      · simp [transition, hread] at hmem
  | carryCheck source =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · by_cases hcarry : cell.carry = true
          · simp [transition, hread, hcarry] at hmem
          · simp only [transition, hread, if_neg hcarry,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            have hcount :
                carryCount
                    ((tape.write (workSymbol cell)).moveHead .stay) =
                  carryCount tape := by
              have hsame :
                  workSymbol cell = tape.read := hread.symm
              rw [hsame]
              exact workCellCount_write_read
                (fun work => work.carry) tape .stay
            simp only [phasePotential, phaseIndex, localRank]
            rw [hcount]
            omega
      · simp [transition, hread] at hmem
  | returnL source =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · by_cases hleft : cell.left = true
          · simp only [transition, hread, if_pos hleft,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact phasePotential_lt_of_phaseIndex_lt (by simp [phaseIndex])
          · by_cases hpost : cell.post = true
            · simp [transition, hread, hleft, hpost] at hmem
            · simp only [transition, hread, if_neg hleft, if_neg hpost,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              have hcount :
                  postCount
                      ((tape.write
                        (workSymbol cell.posted)).moveHead .left) =
                    postCount tape + 1 := by
                apply workCellCount_write_false_true
                    (fun work => work.post) tape cell
                    cell.posted .left hread
                · simpa using hpost
                · rfl
              simp only [phasePotential, phaseIndex, localRank]
              rw [hcount]
              omega
      · simp [transition, hread] at hmem
  | findMark source =>
      rcases hread : contents head with ((_ | inputOrWork) | boundary)
      · simp [transition, hread] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hread] at hmem
        · by_cases hmark : cell.mark = true
          · simp only [transition, hread, if_pos hmark,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact (hnew trivial).elim
          · by_cases hright : cell.right = true
            · simp [transition, hread, hmark, hright] at hmem
            · by_cases hscan : cell.scan = true
              · simp [transition, hread, hmark, hright, hscan] at hmem
              · simp only [transition, hread, if_neg hmark,
                  if_neg hright, if_neg hscan,
                  Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨rfl, rfl, rfl⟩
                have hcount :
                    scanCount
                        ((tape.write
                          (workSymbol cell.scanned)).moveHead .right) =
                      scanCount tape + 1 := by
                  apply workCellCount_write_false_true
                      (fun work => work.scan) tape cell
                      cell.scanned .right hread
                  · simpa using hscan
                  · rfl
                simp only [phasePotential, phaseIndex, localRank]
                rw [hcount]
                omega
      · rw [hread] at hmem
        change (next, written, direction) ∈ (∅ : Set
          (State Λ × TapeAlpha T Γ Λ × DLBA.Dir)) at hmem
        exact hmem.elim

/-! ## Non-ready paths and cycles -/

/-- The machine-step relation restricted to edges whose two endpoints are non-`ready`. -/
@[expose]
public def NonreadyStep
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) : Prop :=
  LBA.Step (machine M) old new ∧
    ¬ old.state.IsReady ∧ ¬ new.state.IsReady

/-- Every restricted non-ready edge strictly raises the phase potential. -/
public theorem nonreadyStep_phasePotential_lt
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hstep : NonreadyStep M old new) :
    phasePotential old < phasePotential new :=
  nonready_step_phasePotential_lt M hstep.1 hstep.2.1 hstep.2.2

/-- Every nonempty path in the restricted non-ready graph raises the phase potential. -/
public theorem nonreadyTransGen_phasePotential_lt
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpath : TransGen (NonreadyStep M) old new) :
    phasePotential old < phasePotential new := by
  induction hpath with
  | single hstep =>
      exact nonreadyStep_phasePotential_lt M hstep
  | tail hpath hstep ih =>
      exact ih.trans (nonreadyStep_phasePotential_lt M hstep)

/-- The complete restricted non-ready configuration graph is acyclic at every tape width. -/
public theorem nonreadyStep_acyclic
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (n : ℕ) :
    ∀ cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n,
      ¬ TransGen (NonreadyStep M) cfg cfg := by
  intro cfg hcycle
  exact (Nat.lt_irrefl _) (nonreadyTransGen_phasePotential_lt M hcycle)

/-- Every nonempty machine path either visits a `ready` configuration (with explicit prefix and
suffix reachability) or strictly raises the phase potential. -/
public theorem transGen_ready_or_phasePotential_lt
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpath : TransGen (LBA.Step (machine M)) old new) :
    (∃ readyCfg,
        readyCfg.state.IsReady ∧
          ReflTransGen (LBA.Step (machine M)) old readyCfg ∧
          ReflTransGen (LBA.Step (machine M)) readyCfg new) ∨
      phasePotential old < phasePotential new := by
  induction hpath with
  | @single endpoint hstep =>
      by_cases hold : old.state.IsReady
      · exact Or.inl ⟨old, hold, .refl, .single hstep⟩
      · by_cases hnew : endpoint.state.IsReady
        · exact Or.inl ⟨endpoint, hnew, .single hstep, .refl⟩
        · exact Or.inr
            (nonready_step_phasePotential_lt M hstep hold hnew)
  | @tail middle endpoint hpath hstep ih =>
      rcases ih with ⟨readyCfg, hready, hprefix, hsuffix⟩ | hpotential
      · exact Or.inl
          ⟨readyCfg, hready, hprefix, hsuffix.tail hstep⟩
      · by_cases hmiddle : middle.state.IsReady
        · exact Or.inl
            ⟨middle, hmiddle, hpath.to_reflTransGen, .single hstep⟩
        · by_cases hnew : endpoint.state.IsReady
          · exact Or.inl
              ⟨endpoint, hnew, (hpath.tail hstep).to_reflTransGen, .refl⟩
          · exact Or.inr
              (hpotential.trans
                (nonready_step_phasePotential_lt M hstep hmiddle hnew))

/-- Every directed machine cycle contains a `ready` configuration and can be rotated through it.
This is precisely the phase-local reduction needed before the separate `ready`-to-`ready`
clock-growth argument. -/
public theorem transGen_cycle_contains_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n)
    (hcycle : TransGen (LBA.Step (machine M)) cfg cfg) :
    ∃ readyCfg,
      readyCfg.state.IsReady ∧
        ReflTransGen (LBA.Step (machine M)) cfg readyCfg ∧
        ReflTransGen (LBA.Step (machine M)) readyCfg cfg := by
  rcases transGen_ready_or_phasePotential_lt M hcycle with hready | hlt
  · exact hready
  · exact (Nat.lt_irrefl _ hlt).elim

end LBA.AcyclicClock

end
