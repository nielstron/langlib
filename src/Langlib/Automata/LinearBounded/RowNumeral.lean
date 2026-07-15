module

public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.List.GetD
import Mathlib.Tactic

@[expose]
public section

/-!
# Synchronous finite-row numerals

This file supplies small, reusable finite-state verifiers for counters stored across a row.
Digits are written **least significant first**, so carry propagation is checked in one
left-to-right sweep, exactly the direction used by `CertifiedRowSystem`.

The digit order is made explicit by a `DigitCodec`.  This keeps the scanners independent of a
particular order instance; `orderedCodec` supplies the canonical increasing codec for every
finite linear order.
-/

namespace RowNumeral

/-- A numbering of a finite digit type by `0, ..., card D - 1`. -/
public structure DigitCodec (D : Type*) [Fintype D] where
  toFin : D ≃ Fin (Fintype.card D)

/-- The canonical increasing numbering of a finite linearly ordered digit type. -/
public def orderedCodec (D : Type*) [Fintype D] [LinearOrder D] : DigitCodec D where
  toFin := (monoEquivOfFin D rfl).symm.toEquiv

variable {D : Type*} [Fintype D] [Nonempty D]

/-- The radix of a row numeral. -/
@[simp]
public def DigitCodec.radix (_E : DigitCodec D) : Nat :=
  Fintype.card D

public theorem DigitCodec.radix_pos (E : DigitCodec D) : 0 < E.radix := by
  simp only [DigitCodec.radix]
  exact Fintype.card_pos

/-- Numeric value of one digit. -/
public def DigitCodec.digitValue (E : DigitCodec D) (d : D) : Nat :=
  (E.toFin d).val

omit [Nonempty D] in
public theorem DigitCodec.digitValue_lt (E : DigitCodec D) (d : D) :
    E.digitValue d < E.radix :=
  (E.toFin d).isLt

/-- The zero digit. -/
public def DigitCodec.zero (E : DigitCodec D) : D :=
  E.toFin.symm ⟨0, E.radix_pos⟩

@[simp]
public theorem DigitCodec.toFin_zero (E : DigitCodec D) :
    E.toFin E.zero = ⟨0, E.radix_pos⟩ := by
  simp [DigitCodec.zero]

@[simp]
public theorem DigitCodec.digitValue_zero (E : DigitCodec D) : E.digitValue E.zero = 0 := by
  simp [DigitCodec.digitValue]

/-- The greatest digit. -/
public def DigitCodec.last (E : DigitCodec D) : D :=
  E.toFin.symm ⟨E.radix - 1, by
    change E.radix - 1 < E.radix
    have := E.radix_pos
    omega⟩

@[simp]
public theorem DigitCodec.digitValue_last (E : DigitCodec D) :
    E.digitValue E.last = E.radix - 1 := by
  simp [DigitCodec.last, DigitCodec.digitValue]

omit [Nonempty D] in
public theorem DigitCodec.digitValue_injective (E : DigitCodec D) :
    Function.Injective E.digitValue := by
  intro d e h
  apply E.toFin.injective
  exact Fin.ext h

/-- The next digit, or `none` at the greatest digit. -/
public def DigitCodec.next (E : DigitCodec D) (d : D) : Option D :=
  if h : E.digitValue d + 1 < E.radix then
    some (E.toFin.symm ⟨E.digitValue d + 1, h⟩)
  else
    none

omit [Nonempty D] in
public theorem DigitCodec.next_eq_some_iff (E : DigitCodec D) (d d' : D) :
    E.next d = some d' ↔ E.digitValue d + 1 < E.radix ∧
      E.digitValue d' = E.digitValue d + 1 := by
  constructor
  · intro hs
    unfold DigitCodec.next at hs
    split at hs
    · rename_i h
      simp only [Option.some.injEq] at hs
      subst d'
      refine ⟨h, ?_⟩
      simp [DigitCodec.digitValue]
    · simp at hs
  · rintro ⟨h, hv⟩
    unfold DigitCodec.next
    rw [dif_pos h]
    apply congrArg some
    apply E.toFin.injective
    apply Fin.ext
    simpa [DigitCodec.digitValue] using hv.symm

omit [Nonempty D] in
public theorem DigitCodec.next_eq_none_iff (E : DigitCodec D) (d : D) :
    E.next d = none ↔ E.digitValue d + 1 = E.radix := by
  constructor
  · intro hn
    unfold DigitCodec.next at hn
    split at hn
    · simp at hn
    · rename_i h
      have hd := E.digitValue_lt d
      omega
  · intro h
    unfold DigitCodec.next
    rw [dif_neg]
    intro hlt
    omega

public theorem DigitCodec.next_eq_none_iff_eq_last (E : DigitCodec D) (d : D) :
    E.next d = none ↔ d = E.last := by
  rw [E.next_eq_none_iff]
  constructor
  · intro h
    apply E.digitValue_injective
    rw [E.digitValue_last]
    have hd := E.digitValue_lt d
    have hp := E.radix_pos
    omega
  · rintro rfl
    rw [E.digitValue_last]
    have hp := E.radix_pos
    omega

/-- The digit one, available when the radix is at least two. -/
public def DigitCodec.one (E : DigitCodec D) (h : 1 < E.radix) : D :=
  E.toFin.symm ⟨1, h⟩

omit [Nonempty D] in
@[simp]
public theorem DigitCodec.digitValue_one (E : DigitCodec D) (h : 1 < E.radix) :
    E.digitValue (E.one h) = 1 := by
  simp [DigitCodec.one, DigitCodec.digitValue]

/-- Value of an LSD-first digit row. -/
public def DigitCodec.value (E : DigitCodec D) : List D → Nat
  | [] => 0
  | d :: ds => E.digitValue d + E.radix * E.value ds

/-- The all-zero row of a given width. -/
public def DigitCodec.zeroRow (E : DigitCodec D) (width : Nat) : List D :=
  List.replicate width E.zero

/-- The numeral one at a positive width.  At width zero it is the empty row. -/
public def DigitCodec.oneRow (E : DigitCodec D) (h : 1 < E.radix) : Nat → List D
  | 0 => []
  | n + 1 => E.one h :: E.zeroRow n

@[simp]
public theorem DigitCodec.length_zeroRow (E : DigitCodec D) (width : Nat) :
    (E.zeroRow width).length = width := by
  simp [DigitCodec.zeroRow]

@[simp]
public theorem DigitCodec.length_oneRow (E : DigitCodec D) (h : 1 < E.radix) (width : Nat) :
    (E.oneRow h width).length = width := by
  cases width <;> simp [DigitCodec.oneRow]

@[simp]
public theorem DigitCodec.value_zeroRow (E : DigitCodec D) (width : Nat) :
    E.value (E.zeroRow width) = 0 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [show E.zeroRow (Nat.succ width) = E.zero :: E.zeroRow width by
        simp only [DigitCodec.zeroRow, Nat.succ_eq_add_one, List.replicate_succ]]
      simp [DigitCodec.value, ih]

@[simp]
public theorem DigitCodec.value_oneRow (E : DigitCodec D) (h : 1 < E.radix)
    {width : Nat} (hw : 0 < width) : E.value (E.oneRow h width) = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  simp [DigitCodec.oneRow, DigitCodec.value]

/-! ## Cellwise zero and copy checks -/

/-- One cell of an all-zero check.  `false` is an absorbing failure state. -/
public def DigitCodec.zeroStep [DecidableEq D] (E : DigitCodec D) (ok : Bool) (d : D) : Bool :=
  ok && decide (d = E.zero)

/-- One cell of a synchronous equality/copy check. -/
public def DigitCodec.copyStep [DecidableEq D]
    (_E : DigitCodec D) (ok : Bool) (old new : D) : Bool :=
  ok && decide (new = old)

/-- State of the one-row checker. -/
public inductive OneState where
  | first
  | rest
  | bad
  deriving DecidableEq, Fintype, Repr

/-- Check one digit of the canonical positive-width numeral one. -/
public def DigitCodec.oneStep [DecidableEq D] (E : DigitCodec D) (h : 1 < E.radix) :
    OneState → D → OneState
  | .bad, _ => .bad
  | .first, d => if d = E.one h then .rest else .bad
  | .rest, d => if d = E.zero then .rest else .bad

/-- Run a zero checker over a whole row. -/
public def DigitCodec.checkZero [DecidableEq D] (E : DigitCodec D) : List D → Bool
  | [] => true
  | d :: ds => decide (d = E.zero) && E.checkZero ds

/-- Run a copy/equality checker over two rows; a length mismatch rejects. -/
public def DigitCodec.checkCopy [DecidableEq D] (E : DigitCodec D) :
    List D → List D → Bool
  | [], [] => true
  | old :: olds, new :: news => decide (new = old) && E.checkCopy olds news
  | _, _ => false

/-- Run the canonical-one checker.  The empty row rejects. -/
public def DigitCodec.checkOne [DecidableEq D]
    (E : DigitCodec D) (h : 1 < E.radix) : List D → Bool
  | [] => false
  | d :: ds => decide (d = E.one h) && E.checkZero ds

@[simp]
public theorem DigitCodec.checkZero_eq_true_iff [DecidableEq D]
    (E : DigitCodec D) (row : List D) :
    E.checkZero row = true ↔ row = E.zeroRow row.length := by
  induction row with
  | nil => simp [DigitCodec.checkZero, DigitCodec.zeroRow]
  | cons d ds ih =>
      simp only [DigitCodec.checkZero, Bool.and_eq_true, decide_eq_true_eq, ih,
        DigitCodec.zeroRow, List.length_cons, List.replicate_succ]
      constructor
      · rintro ⟨hd, hds⟩
        subst d
        exact congrArg (List.cons E.zero) hds
      · intro h
        exact List.cons.inj h

omit [Nonempty D] in
@[simp]
public theorem DigitCodec.checkCopy_eq_true_iff [DecidableEq D]
    (E : DigitCodec D) (old new : List D) :
    E.checkCopy old new = true ↔ new = old := by
  induction old generalizing new with
  | nil => cases new <;> simp [DigitCodec.checkCopy]
  | cons d ds ih =>
      cases new with
      | nil => simp [DigitCodec.checkCopy]
      | cons e es => simp [DigitCodec.checkCopy, ih]

@[simp]
public theorem DigitCodec.checkOne_eq_true_iff [DecidableEq D]
    (E : DigitCodec D) (h : 1 < E.radix) (row : List D) :
    E.checkOne h row = true ↔ 0 < row.length ∧ row = E.oneRow h row.length := by
  cases row with
  | nil => simp [DigitCodec.checkOne]
  | cons d ds =>
      simp only [DigitCodec.checkOne, Bool.and_eq_true, decide_eq_true_eq,
        E.checkZero_eq_true_iff, List.length_cons, Nat.succ_pos, true_and]
      constructor
      · rintro ⟨rfl, hds⟩
        exact congrArg (List.cons (E.one h)) hds
      · intro hr
        simpa [DigitCodec.oneRow] using List.cons.inj hr

/-! ## Synchronous successor -/

/-- State of the one-pass successor verifier. -/
public inductive CarryState where
  | carry
  | done
  | bad
  deriving DecidableEq, Fintype, Repr

/-- Check one aligned pair of digits while propagating a carry from left to right. -/
public def DigitCodec.succStep [DecidableEq D]
    (E : DigitCodec D) : CarryState → D → D → CarryState
  | .bad, _, _ => .bad
  | .done, old, new => if new = old then .done else .bad
  | .carry, old, new =>
      match E.next old with
      | some d => if new = d then .done else .bad
      | none => if new = E.zero then .carry else .bad

/-- Run the synchronous successor verifier; a length mismatch rejects. -/
public def DigitCodec.evalSucc [DecidableEq D] (E : DigitCodec D) :
    CarryState → List D → List D → Option CarryState
  | q, [], [] => some q
  | q, old :: olds, new :: news => E.evalSucc (E.succStep q old new) olds news
  | _, _, _ => none

/-- Increment an LSD-first row, returning an overflow bit. -/
public def DigitCodec.increment (E : DigitCodec D) : List D → List D × Bool
  | [] => ([], true)
  | d :: ds =>
      match E.next d with
      | some d' => (d' :: ds, false)
      | none =>
          let tail := E.increment ds
          (E.zero :: tail.1, tail.2)

@[simp]
public theorem DigitCodec.increment_length (E : DigitCodec D) (row : List D) :
    (E.increment row).1.length = row.length := by
  induction row with
  | nil => rfl
  | cons d ds ih =>
      simp only [DigitCodec.increment]
      split <;> simp [ih]

/-- Overflow occurs exactly at the all-greatest digit row. -/
public theorem DigitCodec.increment_overflow_iff (E : DigitCodec D) (row : List D) :
    (E.increment row).2 = true ↔ row = List.replicate row.length E.last := by
  induction row with
  | nil => simp [DigitCodec.increment]
  | cons d ds ih =>
      cases hnext : E.next d with
      | some d' =>
          have hd : d ≠ E.last := by
            intro heq
            subst d
            have := (E.next_eq_none_iff_eq_last E.last).2 rfl
            rw [hnext] at this
            simp at this
          simp [DigitCodec.increment, hnext, List.replicate_succ, hd]
      | none =>
          have hd : d = E.last := (E.next_eq_none_iff_eq_last d).1 hnext
          subst d
          have hlast : E.next E.last = none := (E.next_eq_none_iff_eq_last E.last).2 rfl
          simp [DigitCodec.increment, hlast, List.replicate_succ, ih]

/-- On overflow, canonical increment wraps to the all-zero row. -/
public theorem DigitCodec.increment_fst_of_overflow (E : DigitCodec D) (row : List D)
    (h : (E.increment row).2 = true) :
    (E.increment row).1 = E.zeroRow row.length := by
  induction row with
  | nil => rfl
  | cons d ds ih =>
      cases hnext : E.next d with
      | some d' => simp [DigitCodec.increment, hnext] at h
      | none =>
          have ht : (E.increment ds).2 = true := by
            simpa [DigitCodec.increment, hnext] using h
          rw [DigitCodec.increment]
          simp only [hnext]
          rw [show E.zeroRow (d :: ds).length = E.zero :: E.zeroRow ds.length by
            simp [DigitCodec.zeroRow, List.replicate_succ]]
          simp [ih ht]

public theorem DigitCodec.evalSucc_bad_eq_some_iff [DecidableEq D]
    (E : DigitCodec D) (old new : List D) (q : CarryState) :
    E.evalSucc .bad old new = some q ↔ old.length = new.length ∧ q = .bad := by
  induction old generalizing new with
  | nil => cases new <;> cases q <;> simp [DigitCodec.evalSucc]
  | cons d ds ih =>
      cases new with
      | nil => simp [DigitCodec.evalSucc]
      | cons e es =>
          simp only [DigitCodec.evalSucc, DigitCodec.succStep, List.length_cons,
            Nat.succ.injEq]
          exact ih es

public theorem DigitCodec.evalSucc_done_eq_some_iff [DecidableEq D]
    (E : DigitCodec D) (old new : List D) (q : CarryState) :
    E.evalSucc .done old new = some q ∧ q ≠ .bad ↔
      new = old ∧ q = .done := by
  induction old generalizing new with
  | nil => cases new <;> cases q <;> simp [DigitCodec.evalSucc]
  | cons d ds ih =>
      cases new with
      | nil => simp [DigitCodec.evalSucc]
      | cons e es =>
          by_cases h : e = d
          · subst e
            simp [DigitCodec.evalSucc, DigitCodec.succStep, ih]
          · rw [DigitCodec.evalSucc]
            simp only [DigitCodec.succStep, if_neg h]
            rw [E.evalSucc_bad_eq_some_iff]
            simp [h]

public theorem DigitCodec.evalSucc_done_iff [DecidableEq D]
    (E : DigitCodec D) (old new : List D) :
    E.evalSucc .done old new = some .done ↔ new = old := by
  have h := E.evalSucc_done_eq_some_iff old new .done
  simpa using h

public theorem DigitCodec.evalSucc_carry_iff [DecidableEq D]
    (E : DigitCodec D) (old new : List D) (q : CarryState) :
    E.evalSucc .carry old new = some q ∧ q ≠ .bad ↔
      new = (E.increment old).1 ∧
        q = if (E.increment old).2 then .carry else .done := by
  induction old generalizing new q with
  | nil =>
      cases new <;> cases q <;> simp [DigitCodec.evalSucc, DigitCodec.increment]
  | cons d ds ih =>
      cases new with
      | nil =>
          cases hnext : E.next d <;>
            simp [DigitCodec.evalSucc, DigitCodec.increment, hnext]
      | cons e es =>
          cases hnext : E.next d with
          | some d' =>
            by_cases he : e = d'
            · subst e
              simp [DigitCodec.increment, DigitCodec.evalSucc, DigitCodec.succStep, hnext,
                E.evalSucc_done_eq_some_iff]
            · rw [DigitCodec.evalSucc]
              simp only [DigitCodec.succStep, hnext, if_neg he]
              rw [E.evalSucc_bad_eq_some_iff]
              simp [DigitCodec.increment, hnext, he]
          | none =>
            by_cases he : e = E.zero
            · subst e
              simpa [DigitCodec.increment, DigitCodec.evalSucc, DigitCodec.succStep,
                hnext] using ih es q
            · rw [DigitCodec.evalSucc]
              simp only [DigitCodec.succStep, hnext, if_neg he]
              rw [E.evalSucc_bad_eq_some_iff]
              simp [DigitCodec.increment, hnext, he]

/-- A successful non-overflowing scan is exactly canonical row successor. -/
public theorem DigitCodec.evalSucc_eq_done_iff [DecidableEq D]
    (E : DigitCodec D) (old new : List D) :
    E.evalSucc .carry old new = some .done ↔
      new = (E.increment old).1 ∧ (E.increment old).2 = false := by
  have h := E.evalSucc_carry_iff old new .done
  constructor
  · intro hs
    have hc := h.mp ⟨hs, by decide⟩
    refine ⟨hc.1, ?_⟩
    cases hb : (E.increment old).2
    · rfl
    · simp [hb] at hc
  · rintro ⟨hnew, hover⟩
    exact (h.mpr ⟨hnew, by simp [hover]⟩).1

/-- A carry remaining after the last cell is exactly canonical overflow. -/
public theorem DigitCodec.evalSucc_eq_carry_iff [DecidableEq D]
    (E : DigitCodec D) (old new : List D) :
    E.evalSucc .carry old new = some .carry ↔
      new = (E.increment old).1 ∧ (E.increment old).2 = true := by
  have h := E.evalSucc_carry_iff old new .carry
  constructor
  · intro hs
    have hc := h.mp ⟨hs, by decide⟩
    refine ⟨hc.1, ?_⟩
    cases hb : (E.increment old).2
    · simp [hb] at hc
    · rfl
  · rintro ⟨hnew, hover⟩
    exact (h.mpr ⟨hnew, by simp [hover]⟩).1

/-! ## Synchronous comparison

The scan still runs from least to most significant digit.  A newly read unequal digit is more
significant than everything seen before, so it replaces the accumulated ordering.
-/

/-- Compare one aligned pair during an LSD-first scan. -/
public def DigitCodec.compareStep (E : DigitCodec D)
    (q : Ordering) (x y : D) : Ordering :=
  match compare (E.digitValue x) (E.digitValue y) with
  | .eq => q
  | q' => q'

/-- Run the synchronous comparison scan; a length mismatch rejects. -/
public def DigitCodec.evalCompare (E : DigitCodec D) :
    Ordering → List D → List D → Option Ordering
  | q, [], [] => some q
  | q, x :: xs, y :: ys => E.evalCompare (E.compareStep q x y) xs ys
  | _, _, _ => none

/-- Canonical LSD-first comparison of two rows. -/
public def DigitCodec.compareRows (E : DigitCodec D) (xs ys : List D) : Option Ordering :=
  E.evalCompare .eq xs ys

omit [Nonempty D] in
public theorem DigitCodec.evalCompare_eq_compareRows (E : DigitCodec D)
    (xs ys : List D) : E.evalCompare .eq xs ys = E.compareRows xs ys := by
  rfl

/-- Equality result of the synchronous comparison. -/
public def DigitCodec.rowsEqual (E : DigitCodec D) (xs ys : List D) : Prop :=
  E.compareRows xs ys = some .eq

/-- Strict less-than result of the synchronous comparison. -/
public def DigitCodec.rowsLess (E : DigitCodec D) (xs ys : List D) : Prop :=
  E.compareRows xs ys = some .lt

end RowNumeral
