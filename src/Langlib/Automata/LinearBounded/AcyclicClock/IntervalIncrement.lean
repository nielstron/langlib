module

public import Langlib.Automata.LinearBounded.RowEnumeration
import Mathlib.Tactic

@[expose]
public section

/-!
# Arithmetic of an odometer started inside a physical row

The guarded clock compiler may encounter a malformed left delimiter away from physical cell zero.
Its carry sweep then increments the suffix beginning at that delimiter.  The whole physical clock
still increases: with least-significant digits first, incrementing a suffix at offset `k` raises
the complete row value by exactly `radix ^ k`.

These lemmas are generic over every finite digit codec.  They isolate the arithmetic part of the
malformed-configuration macro proof from its one-tape sweep invariants.
-/

namespace RowNumeral

variable {D : Type*} [Fintype D]

/-- Value of an LSD-first concatenation.  Digits in `low` are less significant than every digit
in `high`. -/
public theorem DigitCodec.value_append
    (E : DigitCodec D) (low high : List D) :
    E.value (low ++ high) =
      E.value low + E.radix ^ low.length * E.value high := by
  induction low with
  | nil => simp [DigitCodec.value]
  | cons digit low ih =>
      simp only [List.cons_append, DigitCodec.value, List.length_cons, ih]
      rw [Nat.pow_succ]
      ring

variable [Nonempty D]

/-- A nonoverflowing increment of a suffix raises the value of the complete row by the positional
weight of that suffix. -/
public theorem DigitCodec.value_append_increment_of_not_overflow
    (E : DigitCodec D) (low high : List D)
    (hno : (E.increment high).2 = false) :
    E.value (low ++ (E.increment high).1) =
      E.value (low ++ high) + E.radix ^ low.length := by
  rw [E.value_append, E.value_append,
    E.value_increment_of_not_overflow high hno]
  ring

/-- Increment the suffix beginning at list offset `offset`, leaving less-significant cells
unchanged. -/
public def DigitCodec.incrementFrom
    (E : DigitCodec D) (offset : ℕ) (row : List D) : List D :=
  row.take offset ++ (E.increment (row.drop offset)).1

/-- Suffix increment preserves the physical row length. -/
@[simp]
public theorem DigitCodec.length_incrementFrom
    (E : DigitCodec D) (offset : ℕ) (row : List D) :
    (E.incrementFrom offset row).length = row.length := by
  rw [DigitCodec.incrementFrom, List.length_append, E.increment_length,
    List.length_take, List.length_drop]
  omega

/-- Exact whole-row increase for a nonoverflowing suffix increment.  The theorem does not require
`offset ≤ row.length`; `List.take` supplies the effective offset in the out-of-range case. -/
public theorem DigitCodec.value_incrementFrom_of_not_overflow
    (E : DigitCodec D) (offset : ℕ) (row : List D)
    (hno : (E.increment (row.drop offset)).2 = false) :
    E.value (E.incrementFrom offset row) =
      E.value row + E.radix ^ (row.take offset).length := by
  rw [DigitCodec.incrementFrom,
    E.value_append_increment_of_not_overflow _ _ hno,
    List.take_append_drop offset row]

/-- At an actual physical offset, suffix increment raises the whole row by exactly
`radix ^ offset`, and therefore strictly raises it. -/
public theorem DigitCodec.value_incrementFrom_eq_add_pow
    (E : DigitCodec D) {offset : ℕ} (row : List D)
    (hoffset : offset ≤ row.length)
    (hno : (E.increment (row.drop offset)).2 = false) :
    E.value (E.incrementFrom offset row) =
      E.value row + E.radix ^ offset := by
  simpa [List.length_take, Nat.min_eq_left hoffset] using
    E.value_incrementFrom_of_not_overflow offset row hno

/-- Strict whole-row growth of every nonoverflowing suffix increment at a physical offset. -/
public theorem DigitCodec.value_lt_value_incrementFrom
    (E : DigitCodec D) {offset : ℕ} (row : List D)
    (hoffset : offset ≤ row.length)
    (hno : (E.increment (row.drop offset)).2 = false) :
    E.value row < E.value (E.incrementFrom offset row) := by
  rw [E.value_incrementFrom_eq_add_pow row hoffset hno]
  exact Nat.lt_add_of_pos_right (Nat.pow_pos E.radix_pos)

end RowNumeral

end
