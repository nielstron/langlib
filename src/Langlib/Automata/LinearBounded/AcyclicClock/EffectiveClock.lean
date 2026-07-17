module

public import Langlib.Automata.LinearBounded.AcyclicClock.IntervalIncrement
public import Langlib.Automata.LinearBounded.AcyclicClock.PhaseAcyclic
public import Langlib.Automata.LinearBounded.AcyclicClock.ReadyEncoding
import Mathlib.Tactic

@[expose]
public section

/-!
# A virtual clock rank for the operational carry protocol

During a least-significant-digit-first carry, resetting a maximal digit temporarily lowers the
literal row value.  The pending carry nevertheless has a precise positional value.  This file
adds that value to the physical row while the control is in `carry` or `carryCheck`.

The slightly asymmetric `carryCheck` clause also covers malformed physical-right clamping.  If a
maximal cell falsely claims not to be a right delimiter at the last physical position, the
rightward move is clamped and the just-written `carry = true` cell is read again.  That
configuration is terminal, but assigning it the next positional weight makes the virtual clock
monotone even on this malformed edge.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

public abbrev effectiveCodec :
    RowNumeral.DigitCodec (ClockDigit T Γ Λ) :=
  clockCodec (T := T) (Γ := Γ) (Λ := Λ)

/-! ## Single-cell row arithmetic -/

/-- Updating one entry of a finite function corresponds to setting that entry in its `ofFn`
list. -/
public theorem listOfFn_update {α : Type*} {n : ℕ}
    (values : Fin (n + 1) → α) (index : Fin (n + 1)) (value : α) :
    List.ofFn (Function.update values index value) =
      (List.ofFn values).set index.val value := by
  apply List.ext_getElem
  · simp
  · intro j hjLeft hjRight
    have hj : j < n + 1 := by rw [List.length_ofFn] at hjLeft; exact hjLeft
    rw [List.getElem_ofFn, List.getElem_set]
    by_cases hindex : index.val = j
    · rw [if_pos hindex,
        show (⟨j, hj⟩ : Fin (n + 1)) = index from Fin.ext hindex.symm,
        Function.update_self]
    · rw [if_neg hindex, List.getElem_ofFn,
        Function.update_of_ne
          (fun he => hindex (congrArg Fin.val he).symm)]

/-- Replacing a digit by its codec successor raises the complete LSD-first row value by its
positional weight. -/
public theorem digitCodec_value_set_of_next
    {D : Type*} [Fintype D] [Nonempty D]
    (E : RowNumeral.DigitCodec D)
    (row : List D) (index : ℕ) (next : D)
    (hindex : index < row.length)
    (hnext : E.next row[index] = some next) :
    E.value (row.set index next) =
      E.value row + E.radix ^ index := by
  rw [List.set_eq_take_cons_drop next hindex]
  have hrow :
      row =
        row.take index ++ row[index] :: row.drop (index + 1) := by
    calc
      row = row.take index ++ row.drop index :=
        (List.take_append_drop index row).symm
      _ = row.take index ++ row[index] :: row.drop (index + 1) := by
        rw [List.drop_eq_getElem_cons hindex]
  have hvalueRow :
      E.value row =
        E.value
          (row.take index ++ row[index] :: row.drop (index + 1)) :=
    congrArg E.value hrow
  rw [hvalueRow, E.value_append, E.value_append]
  have htake : (row.take index).length = index := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hindex)]
  rw [htake]
  have hdigit := (E.next_eq_some_iff row[index] next).1 hnext
  simp only [RowNumeral.DigitCodec.value]
  rw [hdigit.2]
  ring

/-- Resetting a maximal digit to zero and forwarding its carry preserves the virtual completed
value. -/
public theorem digitCodec_value_set_zero_add_nextWeight_of_max
    {D : Type*} [Fintype D] [Nonempty D]
    (E : RowNumeral.DigitCodec D)
    (row : List D) (index : ℕ)
    (hindex : index < row.length)
    (hmax : E.next row[index] = none) :
    E.value (row.set index E.zero) + E.radix ^ (index + 1) =
      E.value row + E.radix ^ index := by
  rw [List.set_eq_take_cons_drop E.zero hindex]
  have hrow :
      row =
        row.take index ++ row[index] :: row.drop (index + 1) := by
    calc
      row = row.take index ++ row.drop index :=
        (List.take_append_drop index row).symm
      _ = row.take index ++ row[index] :: row.drop (index + 1) := by
        rw [List.drop_eq_getElem_cons hindex]
  have hvalueRow :
      E.value row =
        E.value
          (row.take index ++ row[index] :: row.drop (index + 1)) :=
    congrArg E.value hrow
  rw [hvalueRow, E.value_append, E.value_append]
  have htake : (row.take index).length = index := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hindex)]
  rw [htake]
  have hdigit := (E.next_eq_none_iff row[index]).1 hmax
  simp only [RowNumeral.DigitCodec.value, E.digitValue_zero, zero_add]
  rw [Nat.pow_succ]
  rw [← hdigit]
  ring

/-! ## Clock rows under one tape write -/

/-- Moving the head does not alter the physical clock row. -/
@[simp]
public theorem clockRowOfTape_moveHead
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (direction : DLBA.Dir) :
    clockRowOfTape M (tape.moveHead direction) =
      clockRowOfTape M tape := by
  cases tape
  cases direction <;> rfl

/-- An arbitrary tape write sets the scanned clock entry to the total projected digit of the
written symbol. -/
public theorem clockRowOfTape_write
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (symbol : TapeAlpha T Γ Λ) :
    clockRowOfTape M (tape.write symbol) =
      (clockRowOfTape M tape).set tape.head.val
        ((projectedClockDigit symbol).getD (clockZero M)) := by
  unfold clockRowOfTape DLBA.BoundedTape.write
  rw [← listOfFn_update]
  congr 1
  funext index
  rw [Function.update_apply]
  by_cases hindex : index = tape.head
  · subst index
    simp
  · simp [hindex]

/-- Arbitrary head movement after a write has no further effect on the row. -/
public theorem clockRowOfTape_write_moveHead
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (symbol : TapeAlpha T Γ Λ) (direction : DLBA.Dir) :
    clockRowOfTape M ((tape.write symbol).moveHead direction) =
      (clockRowOfTape M tape).set tape.head.val
        ((projectedClockDigit symbol).getD (clockZero M)) := by
  rw [clockRowOfTape_moveHead, clockRowOfTape_write]

/-- If a write preserves the total projected digit at the head, it preserves the complete
physical clock value. -/
public theorem clockValue_write_moveHead_eq_of_projected
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (symbol : TapeAlpha T Γ Λ) (direction : DLBA.Dir)
    (hdigit :
      (projectedClockDigit symbol).getD (clockZero M) =
        (projectedClockDigit tape.read).getD (clockZero M)) :
    clockValue M ((tape.write symbol).moveHead direction) =
      clockValue M tape := by
  let row := clockRowOfTape M tape
  have hindex : tape.head.val < row.length := by
    rw [show row.length = n + 1 by simp [row]]
    exact tape.head.isLt
  have hget :
      row[tape.head.val] =
        (projectedClockDigit tape.read).getD (clockZero M) := by
    unfold row clockRowOfTape
    rw [List.getElem_ofFn]
    rfl
  unfold clockValue
  rw [clockRowOfTape_write_moveHead, hdigit, ← hget]
  exact congrArg
    (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).value
    (List.set_getElem_self hindex)

/-- Writing a converted work symbol sets precisely the corresponding clock-row entry. -/
public theorem clockRowOfTape_write_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (cell : WorkCell T Γ Λ) :
    clockRowOfTape M (tape.write (workSymbol cell)) =
      (clockRowOfTape M tape).set tape.head.val cell.digit := by
  simpa using clockRowOfTape_write M tape (workSymbol cell)

/-- A work-cell write followed by arbitrary head movement has the same row effect. -/
public theorem clockRowOfTape_write_work_moveHead
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (cell : WorkCell T Γ Λ) (direction : DLBA.Dir) :
    clockRowOfTape M
        ((tape.write (workSymbol cell)).moveHead direction) =
      (clockRowOfTape M tape).set tape.head.val cell.digit := by
  rw [clockRowOfTape_moveHead, clockRowOfTape_write_work]

/-- Rewriting the scanned cell while preserving its digit preserves the complete clock value. -/
public theorem clockValue_write_work_moveHead_eq
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (old new : WorkCell T Γ Λ) (direction : DLBA.Dir)
    (hread : tape.read = workSymbol old)
    (hdigit : new.digit = old.digit) :
    clockValue M ((tape.write (workSymbol new)).moveHead direction) =
      clockValue M tape := by
  let row := clockRowOfTape M tape
  have hindex : tape.head.val < row.length := by
    rw [show row.length = n + 1 by simp [row]]
    exact tape.head.isLt
  have hget : row[tape.head.val] = old.digit := by
    unfold row clockRowOfTape
    rw [List.getElem_ofFn]
    change
      (projectedClockDigit (tape.contents tape.head)).getD (clockZero M) =
        old.digit
    rw [show tape.contents tape.head = workSymbol old from hread]
    rfl
  unfold clockValue
  rw [clockRowOfTape_write_work_moveHead, hdigit, ← hget]
  exact congrArg
    (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).value
    (List.set_getElem_self hindex)

/-- Writing a nonmaximal successor digit raises the physical clock by exactly the head's
positional weight. -/
public theorem clockValue_write_next
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (old : WorkCell T Γ Λ) (next : ClockDigit T Γ Λ)
    (direction : DLBA.Dir)
    (hread : tape.read = workSymbol old)
    (hnext :
      (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).next old.digit =
        some next) :
    clockValue M
        ((tape.write (workSymbol { old with digit := next })).moveHead direction) =
      clockValue M tape +
        (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix ^
          tape.head.val := by
  letI : Nonempty Λ := ⟨M.initial⟩
  let row := clockRowOfTape M tape
  have hindex : tape.head.val < row.length := by
    rw [show row.length = n + 1 by simp [row]]
    exact tape.head.isLt
  have hget : row[tape.head.val] = old.digit := by
    unfold row clockRowOfTape
    rw [List.getElem_ofFn]
    change
      (projectedClockDigit (tape.contents tape.head)).getD (clockZero M) =
        old.digit
    rw [show tape.contents tape.head = workSymbol old from hread]
    rfl
  unfold clockValue
  rw [clockRowOfTape_write_work_moveHead]
  apply digitCodec_value_set_of_next
    (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ))
    row tape.head.val next hindex
  simpa [hget] using hnext

/-- Resetting a maximal digit gives the exact arithmetic equation used by the pending-carry
virtual clock. -/
public theorem clockValue_write_zero_add_nextWeight
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (old : WorkCell T Γ Λ) (direction : DLBA.Dir)
    (hread : tape.read = workSymbol old)
    (hmax :
      (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).next old.digit =
        none) :
    clockValue M
          ((tape.write
            (workSymbol
              { old with
                digit := clockZero M
                carry := true })).moveHead direction) +
        (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix ^
          (tape.head.val + 1) =
      clockValue M tape +
        (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix ^
          tape.head.val := by
  letI : Nonempty Λ := ⟨M.initial⟩
  let row := clockRowOfTape M tape
  have hindex : tape.head.val < row.length := by
    rw [show row.length = n + 1 by simp [row]]
    exact tape.head.isLt
  have hget : row[tape.head.val] = old.digit := by
    unfold row clockRowOfTape
    rw [List.getElem_ofFn]
    change
      (projectedClockDigit (tape.contents tape.head)).getD (clockZero M) =
        old.digit
    rw [show tape.contents tape.head = workSymbol old from hread]
    rfl
  have hzero :
      clockZero M =
        (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).zero := rfl
  unfold clockValue
  rw [clockRowOfTape_write_work_moveHead, hzero]
  apply digitCodec_value_set_zero_add_nextWeight_of_max
    (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ))
    row tape.head.val hindex
  simpa [hget] using hmax

/-! ## The virtual completed clock -/

/-- The only phase in which a transition may modify the clock digit. -/
public def State.IsCarry : State Λ → Prop
  | .carry _ => True
  | _ => False

/-- Every transition outside `carry` preserves the total projected clock digit of the scanned
cell.  This includes conversion of a raw symbol, whose total projected digit is zero, to a fresh
zero-digit work cell. -/
public theorem transition_preserves_projectedClock_of_not_carry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {state next : State Λ}
    {symbol written : TapeAlpha T Γ Λ} {direction : DLBA.Dir}
    (hnot : ¬ state.IsCarry)
    (hmem : (next, written, direction) ∈ transition M state symbol) :
    (projectedClockDigit written).getD (clockZero M) =
      (projectedClockDigit symbol).getD (clockZero M) := by
  letI : Nonempty Λ := ⟨M.initial⟩
  cases state with
  | initFirst =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · simp [transition, hsymbol] at hmem
      · cases boundary with
        | false =>
            simp only [transition, hsymbol, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            rfl
        | true =>
            simp [transition, hsymbol] at hmem
  | initSweep =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp only [transition, hsymbol, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        rfl
      · rcases inputOrWork with input | cell
        · simp only [transition, hsymbol, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          rfl
        · by_cases hinit : cell.init = true
          · simp only [transition, hsymbol, if_pos hinit,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            rfl
          · simp [transition, hsymbol, hinit] at hmem
      · simp only [transition, hsymbol, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        rfl
  | initBack =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · by_cases hinit : cell.init = true
            · simp only [transition, hsymbol, if_pos hleft, if_pos hinit,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              rfl
            · simp [transition, hsymbol, hleft, hinit] at hmem
          · by_cases hinit : cell.init = true
            · simp only [transition, hsymbol, if_neg hleft, if_pos hinit,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              rfl
            · simp [transition, hsymbol, hleft, hinit] at hmem
      · simp [transition, hsymbol] at hmem
  | ready source =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hmark : cell.mark = true
          · simp only [transition, hsymbol, if_pos hmark,
              Set.mem_image] at hmem
            rcases hmem with ⟨move, _, hmove⟩
            rcases hmove
            rfl
          · simp [transition, hsymbol, hmark] at hmem
      · simp [transition, hsymbol] at hmem
  | mark source =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · simp only [transition, hsymbol, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          rfl
      · simp [transition, hsymbol] at hmem
  | seek source =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · simp only [transition, hsymbol, if_pos hleft,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            rfl
          · by_cases hseek : cell.seek = true
            · simp [transition, hsymbol, hleft, hseek] at hmem
            · simp only [transition, hsymbol, if_neg hleft, if_neg hseek,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              rfl
      · simp [transition, hsymbol] at hmem
  | cleanR source =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hnorm : cell.norm = true
          · simp [transition, hsymbol, hnorm] at hmem
          · by_cases hright : cell.right = true
            · simp only [transition, hsymbol, if_neg hnorm, if_pos hright,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              rfl
            · simp only [transition, hsymbol, if_neg hnorm, if_neg hright,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              rfl
      · simp [transition, hsymbol] at hmem
  | cleanL source =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · by_cases hnorm : cell.norm = true
            · simp only [transition, hsymbol, if_pos hleft, if_pos hnorm,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              rfl
            · simp [transition, hsymbol, hleft, hnorm] at hmem
          · by_cases hnorm : cell.norm = true
            · simp only [transition, hsymbol, if_neg hleft, if_pos hnorm,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              rfl
            · simp [transition, hsymbol, hleft, hnorm] at hmem
      · simp [transition, hsymbol] at hmem
  | carry source =>
      exact (hnot trivial).elim
  | carryCheck source =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hcarry : cell.carry = true
          · simp [transition, hsymbol, hcarry] at hmem
          · simp only [transition, hsymbol, if_neg hcarry,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            rfl
      · simp [transition, hsymbol] at hmem
  | returnL source =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · simp only [transition, hsymbol, if_pos hleft,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            rfl
          · by_cases hpost : cell.post = true
            · simp [transition, hsymbol, hleft, hpost] at hmem
            · simp only [transition, hsymbol, if_neg hleft, if_neg hpost,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              rfl
      · simp [transition, hsymbol] at hmem
  | findMark source =>
      rcases hsymbol : symbol with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hmark : cell.mark = true
          · simp only [transition, hsymbol, if_pos hmark,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            rfl
          · by_cases hright : cell.right = true
            · simp [transition, hsymbol, hmark, hright] at hmem
            · by_cases hscan : cell.scan = true
              · simp [transition, hsymbol, hmark, hright, hscan] at hmem
              · simp only [transition, hsymbol, if_neg hmark,
                  if_neg hright, if_neg hscan,
                  Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨rfl, rfl, rfl⟩
                rfl
      · simp [transition, hsymbol] at hmem

/-- Consequently, every complete machine step outside `carry` preserves the physical clock. -/
public theorem step_clockValue_eq_of_not_carry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hnot : ¬ old.state.IsCarry)
    (hstep : LBA.Step (machine M) old new) :
    clockValue M new.tape = clockValue M old.tape := by
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  apply clockValue_write_moveHead_eq_of_projected
  exact transition_preserves_projectedClock_of_not_carry M hnot hmem

/-- States belonging to an ordinary source-step macro, excluding the disconnected canonical
initialization protocol. -/
public def State.IsMacro : State Λ → Prop
  | .ready _ | .mark _ | .seek _ | .cleanR _ | .cleanL _
  | .carry _ | .carryCheck _ | .returnL _ | .findMark _ => True
  | _ => False

omit [Fintype Λ] in
public theorem State.isReady_iff_exists (state : State Λ) :
    state.IsReady ↔ ∃ source, state = .ready source := by
  cases state <;> simp [State.IsReady]

/-- Whether the work cell currently scanned by a `carryCheck` state is already marked as
carry-passed.  Raw symbols count as unmarked. -/
public def scannedCarryBit
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : Bool :=
  match asWork tape.read with
  | some cell => cell.carry
  | none => false

/-- Positional value of the carry currently in flight. -/
public def pendingCarryWeight
    (_M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (state : State Λ)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  match state with
  | .carry _ =>
      (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix ^
        tape.head.val
  | .carryCheck _ =>
      if scannedCarryBit tape then
        (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix ^
          (tape.head.val + 1)
      else
        (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix ^
          tape.head.val
  | _ => 0

/-- Physical clock value plus the exact value of an in-flight carry. -/
public def effectiveClock
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) : ℕ :=
  clockValue M cfg.tape + pendingCarryWeight M cfg.state cfg.tape

@[simp]
public theorem effectiveClock_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    effectiveClock M ⟨.ready source, tape⟩ = clockValue M tape := by
  simp [effectiveClock, pendingCarryWeight]

/-- On every Ready configuration, the virtual and physical clocks coincide. -/
public theorem effectiveClock_eq_clockValue_of_isReady
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n)
    (hready : cfg.state.IsReady) :
    effectiveClock M cfg = clockValue M cfg.tape := by
  rcases (State.isReady_iff_exists cfg.state).1 hready with
    ⟨source, hstate⟩
  simp [effectiveClock, pendingCarryWeight, hstate]

@[simp]
public theorem effectiveClock_cleanL
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    effectiveClock M ⟨.cleanL source, tape⟩ = clockValue M tape := by
  simp [effectiveClock, pendingCarryWeight]

@[simp]
public theorem effectiveClock_carry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    effectiveClock M ⟨.carry source, tape⟩ =
      clockValue M tape +
        (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix ^
          tape.head.val := by
  simp [effectiveClock, pendingCarryWeight]

/-! ## Monotonicity of the virtual clock -/

/-- The virtual completed clock is nondecreasing on every concrete machine step, including
malformed steps that immediately enter a blocked configuration. -/
public theorem step_effectiveClock_le
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hstep : LBA.Step (machine M) old new) :
    effectiveClock M old ≤ effectiveClock M new := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rcases old with ⟨state, tape⟩
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  change
    (next, written, direction) ∈
      transition M state (tape.contents tape.head) at hmem
  let targetTape := (tape.write written).moveHead direction
  change
    effectiveClock M ⟨state, tape⟩ ≤
      effectiveClock M ⟨next, targetTape⟩
  have preserved (hnot : ¬ state.IsCarry) :
      clockValue M targetTape = clockValue M tape := by
    apply clockValue_write_moveHead_eq_of_projected
    exact transition_preserves_projectedClock_of_not_carry M hnot hmem
  cases state with
  | initFirst =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · simp [transition, hsymbol] at hmem
      · cases boundary with
        | false =>
            simp only [transition, hsymbol, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
        | true =>
            simp [transition, hsymbol] at hmem
  | initSweep =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp only [transition, hsymbol, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
      · rcases inputOrWork with input | cell
        · simp only [transition, hsymbol, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
        · by_cases hinit : cell.init = true
          · simp only [transition, hsymbol, if_pos hinit,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
          · simp [transition, hsymbol, hinit] at hmem
      · simp only [transition, hsymbol, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
  | initBack =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · by_cases hinit : cell.init = true
            · simp only [transition, hsymbol, if_pos hleft, if_pos hinit,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
            · simp [transition, hsymbol, hleft, hinit] at hmem
          · by_cases hinit : cell.init = true
            · simp only [transition, hsymbol, if_neg hleft, if_pos hinit,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
            · simp [transition, hsymbol, hleft, hinit] at hmem
      · simp [transition, hsymbol] at hmem
  | ready source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hmark : cell.mark = true
          · simp only [transition, hsymbol, if_pos hmark,
              Set.mem_image] at hmem
            rcases hmem with ⟨move, _, hmove⟩
            rcases hmove
            exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
          · simp [transition, hsymbol, hmark] at hmem
      · simp [transition, hsymbol] at hmem
  | mark source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · simp only [transition, hsymbol, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
      · simp [transition, hsymbol] at hmem
  | seek source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · simp only [transition, hsymbol, if_pos hleft,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
          · by_cases hseek : cell.seek = true
            · simp [transition, hsymbol, hleft, hseek] at hmem
            · simp only [transition, hsymbol, if_neg hleft, if_neg hseek,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
      · simp [transition, hsymbol] at hmem
  | cleanR source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hnorm : cell.norm = true
          · simp [transition, hsymbol, hnorm] at hmem
          · by_cases hright : cell.right = true
            · simp only [transition, hsymbol, if_neg hnorm, if_pos hright,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
            · simp only [transition, hsymbol, if_neg hnorm, if_neg hright,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
      · simp [transition, hsymbol] at hmem
  | cleanL source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · by_cases hnorm : cell.norm = true
            · simp only [transition, hsymbol, if_pos hleft, if_pos hnorm,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              have hclock := preserved (by simp [State.IsCarry])
              simp only [effectiveClock, pendingCarryWeight]
              rw [hclock]
              exact Nat.le_add_right _ _
            · simp [transition, hsymbol, hleft, hnorm] at hmem
          · by_cases hnorm : cell.norm = true
            · simp only [transition, hsymbol, if_neg hleft, if_pos hnorm,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
            · simp [transition, hsymbol, hleft, hnorm] at hmem
      · simp [transition, hsymbol] at hmem
  | carry source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hcarry : cell.carry = true
          · simp [transition, hsymbol, hcarry] at hmem
          · cases hnext :
              (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).next
                cell.digit with
            | some digit =>
                simp only [transition, hsymbol, if_neg hcarry, hnext,
                  Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨rfl, rfl, rfl⟩
                have hclock :=
                  clockValue_write_next M tape cell digit .stay hsymbol hnext
                exact Nat.le_of_eq (by
                  simpa [effectiveClock, pendingCarryWeight, targetTape]
                    using hclock.symm)
            | none =>
                by_cases hright : cell.right = true
                · simp [transition, hsymbol, hcarry, hnext, hright] at hmem
                · simp only [transition, hsymbol, if_neg hcarry, hnext,
                    if_neg hright, Set.mem_singleton_iff,
                    Prod.mk.injEq] at hmem
                  rcases hmem with ⟨rfl, rfl, rfl⟩
                  let resetCell : WorkCell T Γ Λ :=
                    { cell with
                      digit := clockZero M
                      carry := true }
                  let resetTape :=
                    (tape.write (workSymbol resetCell)).moveHead .right
                  have hclock :=
                    clockValue_write_zero_add_nextWeight
                      M tape cell .right hsymbol hnext
                  have hpow :
                      (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                          (tape.head.val + 1) ≤
                        pendingCarryWeight M (.carryCheck source) resetTape := by
                    by_cases hmove : tape.head.val < n
                    · have hhead :
                          resetTape.head.val = tape.head.val + 1 := by
                        change
                          (if h : tape.head.val < n then
                              (⟨tape.head.val + 1, by omega⟩ :
                                Fin (n + 1))
                            else tape.head).val =
                            tape.head.val + 1
                        rw [dif_pos hmove]
                      by_cases hbit : scannedCarryBit resetTape = true
                      · change
                          (effectiveCodec
                                (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                              (tape.head.val + 1) ≤
                            (if scannedCarryBit resetTape then
                              (effectiveCodec
                                  (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                                (resetTape.head.val + 1)
                            else
                              (effectiveCodec
                                  (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                                resetTape.head.val)
                        rw [if_pos (by simpa using hbit), hhead]
                        exact Nat.pow_le_pow_right
                          (effectiveCodec
                            (T := T) (Γ := Γ) (Λ := Λ)).radix_pos
                          (by omega)
                      · change
                          (effectiveCodec
                                (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                              (tape.head.val + 1) ≤
                            (if scannedCarryBit resetTape then
                              (effectiveCodec
                                  (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                                (resetTape.head.val + 1)
                            else
                              (effectiveCodec
                                  (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                                resetTape.head.val)
                        rw [if_neg (by simpa using hbit), hhead]
                    · have hhead :
                          resetTape.head = tape.head := by
                        change
                          (if h : tape.head.val < n then
                              (⟨tape.head.val + 1, by omega⟩ :
                                Fin (n + 1))
                            else tape.head) = tape.head
                        rw [dif_neg hmove]
                      have hbit : scannedCarryBit resetTape = true := by
                        unfold scannedCarryBit
                        change
                          (match asWork
                              (resetTape.contents resetTape.head) with
                          | some work => work.carry
                          | none => false) = true
                        rw [hhead]
                        change
                          (match
                            asWork
                              (Function.update tape.contents tape.head
                                (workSymbol resetCell) tape.head) with
                          | some work => work.carry
                          | none => false) = true
                        rw [Function.update_self]
                        rfl
                      change
                        (effectiveCodec
                              (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                            (tape.head.val + 1) ≤
                          (if scannedCarryBit resetTape then
                            (effectiveCodec
                                (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                              (resetTape.head.val + 1)
                          else
                            (effectiveCodec
                                (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                              resetTape.head.val)
                      rw [if_pos (by simpa using hbit), hhead]
                  simp only [effectiveClock, pendingCarryWeight]
                  change
                    clockValue M tape +
                        (effectiveCodec
                          (T := T) (Γ := Γ) (Λ := Λ)).radix ^
                          tape.head.val ≤
                      clockValue M resetTape +
                        pendingCarryWeight M (.carryCheck source) resetTape
                  rw [← hclock]
                  exact Nat.add_le_add_left hpow _
      · simp [transition, hsymbol] at hmem
  | carryCheck source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hcarry : cell.carry = true
          · simp [transition, hsymbol, hcarry] at hmem
          · simp only [transition, hsymbol, if_neg hcarry,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            have hclock := preserved (by simp [State.IsCarry])
            have hbit : scannedCarryBit tape = false := by
              unfold scannedCarryBit
              change
                (match asWork (tape.contents tape.head) with
                | some work => work.carry
                | none => false) = false
              rw [hsymbol]
              change cell.carry = false
              exact Bool.eq_false_of_not_eq_true hcarry
            have hhead : targetTape.head = tape.head := rfl
            simp only [effectiveClock, pendingCarryWeight]
            rw [if_neg (by simpa using hbit), hclock]
            rw [hhead]
      · simp [transition, hsymbol] at hmem
  | returnL source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · simp only [transition, hsymbol, if_pos hleft,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
          · by_cases hpost : cell.post = true
            · simp [transition, hsymbol, hleft, hpost] at hmem
            · simp only [transition, hsymbol, if_neg hleft, if_neg hpost,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
      · simp [transition, hsymbol] at hmem
  | findMark source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · rw [hsymbol] at hmem
        change
          (next, written, direction) ∈
            (∅ : Set (State Λ × TapeAlpha T Γ Λ × DLBA.Dir)) at hmem
        exact hmem.elim
      · rcases inputOrWork with input | cell
        · rw [hsymbol] at hmem
          change
            (next, written, direction) ∈
              (∅ : Set (State Λ × TapeAlpha T Γ Λ × DLBA.Dir)) at hmem
          exact hmem.elim
        · rw [hsymbol] at hmem
          change
            (next, written, direction) ∈
              transition M (.findMark source) (workSymbol cell) at hmem
          by_cases hmark : cell.mark = true
          · rw [transition_findMark_work,
              if_pos (by simpa using hmark)] at hmem
            simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact Nat.le_of_eq (preserved (by simp [State.IsCarry])).symm
          · by_cases hright : cell.right = true
            · rw [transition_findMark_work,
                if_neg (by simpa using hmark),
                if_pos (by simpa using hright)] at hmem
              exact hmem.elim
            · by_cases hscan : cell.scan = true
              · rw [transition_findMark_work,
                  if_neg (by simpa using hmark),
                  if_neg (by simpa using hright),
                  if_pos (by simpa using hscan)] at hmem
                exact hmem.elim
              · rw [transition_findMark_work,
                  if_neg (by simpa using hmark),
                  if_neg (by simpa using hright),
                  if_neg (by simpa using hscan)] at hmem
                simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨rfl, rfl, rfl⟩
                exact Nat.le_of_eq
                  (preserved (by simp [State.IsCarry])).symm
      · rw [hsymbol] at hmem
        change
          (next, written, direction) ∈
            (∅ : Set (State Λ × TapeAlpha T Γ Λ × DLBA.Dir)) at hmem
        exact hmem.elim

/-! ## The strict edge in every completed macro -/

/-- The four protocol states strictly between `ready` and the first pending carry. -/
public def State.PreCarry : State Λ → Prop
  | .mark _ | .seek _ | .cleanR _ | .cleanL _ => True
  | _ => False

/-- A distinguished edge that enters the carry protocol from the normalization sweep. -/
public def CarryEntry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) : Prop :=
  LBA.Step (machine M) old new ∧
    ∃ source, old.state = .cleanL source ∧ new.state = .carry source

/-- Every enabled transition from a pre-carry state either remains pre-carry or is precisely the
entry edge into `carry`. -/
public theorem preCarry_step_or_entry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpre : old.state.PreCarry)
    (hstep : LBA.Step (machine M) old new) :
    new.state.PreCarry ∨ CarryEntry M old new := by
  letI : Nonempty Λ := ⟨M.initial⟩
  have hstepOriginal := hstep
  rcases old with ⟨state, tape⟩
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  change
    (next, written, direction) ∈
      transition M state (tape.contents tape.head) at hmem
  cases state with
  | initFirst => exact hpre.elim
  | initSweep => exact hpre.elim
  | initBack => exact hpre.elim
  | ready source => exact hpre.elim
  | mark source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · simp only [transition, hsymbol, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          exact Or.inl trivial
      · simp [transition, hsymbol] at hmem
  | seek source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · simp only [transition, hsymbol, if_pos hleft,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl⟩
            exact Or.inl trivial
          · by_cases hseek : cell.seek = true
            · simp [transition, hsymbol, hleft, hseek] at hmem
            · simp only [transition, hsymbol, if_neg hleft, if_neg hseek,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Or.inl trivial
      · simp [transition, hsymbol] at hmem
  | cleanR source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hnorm : cell.norm = true
          · simp [transition, hsymbol, hnorm] at hmem
          · by_cases hright : cell.right = true
            · simp only [transition, hsymbol, if_neg hnorm, if_pos hright,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Or.inl trivial
            · simp only [transition, hsymbol, if_neg hnorm, if_neg hright,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Or.inl trivial
      · simp [transition, hsymbol] at hmem
  | cleanL source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hleft : cell.left = true
          · by_cases hnorm : cell.norm = true
            · simp only [transition, hsymbol, if_pos hleft, if_pos hnorm,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Or.inr
                ⟨hstepOriginal, source, rfl, rfl⟩
            · simp [transition, hsymbol, hleft, hnorm] at hmem
          · by_cases hnorm : cell.norm = true
            · simp only [transition, hsymbol, if_neg hleft, if_pos hnorm,
                Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨rfl, rfl, rfl⟩
              exact Or.inl trivial
            · simp [transition, hsymbol, hleft, hnorm] at hmem
      · simp [transition, hsymbol] at hmem
  | carry source => exact hpre.elim
  | carryCheck source => exact hpre.elim
  | returnL source => exact hpre.elim
  | findMark source => exact hpre.elim

/-- The first step out of a Ready state always lands in `mark`, hence in the pre-carry region. -/
public theorem ready_step_preCarry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hready : old.state.IsReady)
    (hstep : LBA.Step (machine M) old new) :
    new.state.PreCarry := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rcases old with ⟨state, tape⟩
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  change
    (next, written, direction) ∈
      transition M state (tape.contents tape.head) at hmem
  cases state with
  | ready source =>
      rcases hsymbol : tape.contents tape.head with ((_ | inputOrWork) | boundary)
      · simp [transition, hsymbol] at hmem
      · rcases inputOrWork with input | cell
        · simp [transition, hsymbol] at hmem
        · by_cases hmark : cell.mark = true
          · simp only [transition, hsymbol, if_pos hmark,
              Set.mem_image] at hmem
            rcases hmem with ⟨move, _, hmove⟩
            rcases hmove
            trivial
          · simp [transition, hsymbol, hmark] at hmem
      · simp [transition, hsymbol] at hmem
  | initFirst => exact hready.elim
  | initSweep => exact hready.elim
  | initBack => exact hready.elim
  | mark source => exact hready.elim
  | seek source => exact hready.elim
  | cleanR source => exact hready.elim
  | cleanL source => exact hready.elim
  | carry source => exact hready.elim
  | carryCheck source => exact hready.elim
  | returnL source => exact hready.elim
  | findMark source => exact hready.elim

/-- A carry-entry edge raises the virtual clock strictly by the positive positional weight at
the physical head. -/
public theorem carryEntry_effectiveClock_lt
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hentry : CarryEntry M old new) :
    effectiveClock M old < effectiveClock M new := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rcases hentry with ⟨hstep, source, hold, hnew⟩
  rcases old with ⟨oldState, oldTape⟩
  rcases new with ⟨newState, newTape⟩
  simp only at hold hnew
  subst oldState
  subst newState
  have hclock :
      clockValue M newTape = clockValue M oldTape :=
    step_clockValue_eq_of_not_carry M (by simp [State.IsCarry]) hstep
  rcases hstep with ⟨next, written, direction, hmem, hcfg⟩
  have hhead : newTape.head = oldTape.head := by
    change
      (⟨State.carry source, newTape⟩ :
        DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) =
        ⟨next, (oldTape.write written).moveHead direction⟩ at hcfg
    have hnext : next = .carry source :=
      congrArg (fun cfg => cfg.state) hcfg |>.symm
    subst next
    have htape :
        newTape = (oldTape.write written).moveHead direction :=
      congrArg (fun cfg => cfg.tape) hcfg
    change
      (State.carry source, written, direction) ∈
        transition M (.cleanL source)
          (oldTape.contents oldTape.head) at hmem
    rcases hsymbol : oldTape.contents oldTape.head with
      ((_ | inputOrWork) | boundary)
    · simp [transition, hsymbol] at hmem
    · rcases inputOrWork with input | cell
      · simp [transition, hsymbol] at hmem
      · by_cases hleft : cell.left = true
        · by_cases hnorm : cell.norm = true
          · simp only [transition, hsymbol, if_pos hleft, if_pos hnorm,
              Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl, rfl⟩
            rw [htape]
            rfl
          · simp [transition, hsymbol, hleft, hnorm] at hmem
        · by_cases hnorm : cell.norm = true
          · simp [transition, hsymbol, hleft, hnorm] at hmem
          · simp [transition, hsymbol, hleft, hnorm] at hmem
    · simp [transition, hsymbol] at hmem
  simp only [effectiveClock, pendingCarryWeight]
  rw [hclock, hhead]
  exact Nat.lt_add_of_pos_right
    (Nat.pow_pos
      (effectiveCodec (T := T) (Γ := Γ) (Λ := Λ)).radix_pos)

/-! ## Path decomposition and Ready-to-Ready growth -/

/-- A path beginning in the pre-carry region either remains there or contains an explicit
carry-entry edge, together with prefix and suffix paths locating that edge. -/
public theorem reflTransGen_preCarry_or_contains_entry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpre : old.state.PreCarry)
    (hpath : ReflTransGen (LBA.Step (machine M)) old new) :
    new.state.PreCarry ∨
      ∃ before after,
        ReflTransGen (LBA.Step (machine M)) old before ∧
          CarryEntry M before after ∧
          ReflTransGen (LBA.Step (machine M)) after new := by
  induction hpath with
  | refl =>
      exact Or.inl hpre
  | @tail middle endpoint hpath hstep ih =>
      rcases ih with hmiddle | ⟨before, after, hprefix, hentry, hsuffix⟩
      · rcases preCarry_step_or_entry M hmiddle hstep with
          hendpoint | hentry
        · exact Or.inl hendpoint
        · exact Or.inr
            ⟨middle, endpoint, hpath, hentry, ReflTransGen.refl⟩
      · exact Or.inr
          ⟨before, after, hprefix, hentry, hsuffix.tail hstep⟩

/-- Effective-clock monotonicity extends to arbitrary reflexive-transitive paths. -/
public theorem reflTransGen_effectiveClock_le
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpath : ReflTransGen (LBA.Step (machine M)) old new) :
    effectiveClock M old ≤ effectiveClock M new := by
  induction hpath with
  | refl => exact Nat.le_refl _
  | tail hpath hstep ih =>
      exact ih.trans (step_effectiveClock_le M hstep)

/-- Every nonempty path from Ready to Ready contains a carry-entry edge. -/
public theorem ready_transGen_contains_entry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hold : old.state.IsReady)
    (hnew : new.state.IsReady)
    (hpath : TransGen (LBA.Step (machine M)) old new) :
    ∃ before after,
      ReflTransGen (LBA.Step (machine M)) old before ∧
        CarryEntry M before after ∧
        ReflTransGen (LBA.Step (machine M)) after new := by
  rcases TransGen.head'_iff.mp hpath with ⟨first, hfirst, hrest⟩
  have hpre := ready_step_preCarry M hold hfirst
  rcases reflTransGen_preCarry_or_contains_entry M hpre hrest with
    hstill | hentry
  · rcases (State.isReady_iff_exists new.state).1 hnew with
      ⟨source, hsource⟩
    rw [hsource] at hstill
    exact hstill.elim
  · rcases hentry with
      ⟨before, after, hprefix, hentry, hsuffix⟩
    exact
      ⟨before, after, ReflTransGen.head hfirst hprefix,
        hentry, hsuffix⟩

/-- **Ready-to-Ready clock growth.**  This is global over arbitrary malformed tapes: no
delimiter, mark, or scratch-track invariant is assumed. -/
public theorem ready_transGen_clockValue_lt
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hold : old.state.IsReady)
    (hnew : new.state.IsReady)
    (hpath : TransGen (LBA.Step (machine M)) old new) :
    clockValue M old.tape < clockValue M new.tape := by
  rcases ready_transGen_contains_entry M hold hnew hpath with
    ⟨before, after, hprefix, hentry, hsuffix⟩
  have hstrict :
      effectiveClock M old < effectiveClock M new :=
    (reflTransGen_effectiveClock_le M hprefix).trans_lt
      ((carryEntry_effectiveClock_lt M hentry).trans_le
        (reflTransGen_effectiveClock_le M hsuffix))
  rw [effectiveClock_eq_clockValue_of_isReady M old hold,
    effectiveClock_eq_clockValue_of_isReady M new hnew] at hstrict
  exact hstrict

end LBA.AcyclicClock

end
