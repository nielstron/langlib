module

public import Langlib.Automata.LinearBounded.RowNumeral
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical enumeration of fixed-width finite rows

`RowNumeral` implements least-significant-digit-first counters and their synchronous
finite-state verifiers.  This file supplies their arithmetic semantics.  A row of
length `n` over a finite alphabet `A` has a unique rank below `|A| ^ n`; starting at
the zero row and repeatedly applying fixed-width increment visits every such row
exactly once before overflowing.

The final section chooses a codec for `Option A`.  Its radix is `|A| + 1`, so on every
positive-width input it has room for the endpoint `|A| ^ n` as well as all smaller
row ranks.  These are the fuel and depth counters used by the linear-space
inductive-counting verifier.
-/

namespace RowNumeral

/-- A choice-free-at-use-site digit codec for any finite type.  Unlike
`orderedCodec`, this does not require the caller to install a `LinearOrder`; the
noncomputable choice is made once when the verifier is constructed. -/
public noncomputable def fintypeCodec (D : Type*) [Fintype D] : DigitCodec D where
  toFin := Fintype.equivFin D

variable {D : Type*} [Fintype D] [Nonempty D]

/-! ## Rank bounds and uniqueness -/

omit [Nonempty D] in
/-- The numeric value of a row is below the number of rows of that length. -/
public theorem DigitCodec.value_lt_pow_length (E : DigitCodec D) (row : List D) :
    E.value row < E.radix ^ row.length := by
  induction row with
  | nil => simp [DigitCodec.value]
  | cons d ds ih =>
      have hd := E.digitValue_lt d
      have hs : E.value ds + 1 ≤ E.radix ^ ds.length := Nat.succ_le_iff.mpr ih
      have hmul := Nat.mul_le_mul_left E.radix hs
      rw [Nat.mul_add] at hmul
      simp only [DigitCodec.value, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (E.radix ^ ds.length) E.radix]
      omega

/-- Equal-length rows with equal numeric values are equal. -/
public theorem DigitCodec.value_injective_of_length_eq (E : DigitCodec D)
    {xs ys : List D} (hlen : xs.length = ys.length) (hvalue : E.value xs = E.value ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hmod := congrArg (fun n => n % E.radix) hvalue
          have hxlt := E.digitValue_lt x
          have hylt := E.digitValue_lt y
          simp only [DigitCodec.value, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hmod
          have hxy : x = y := E.digitValue_injective hmod
          subst y
          have htailMul : E.radix * E.value xs = E.radix * E.value ys :=
            Nat.add_left_cancel hvalue
          have htail : E.value xs = E.value ys :=
            Nat.mul_left_cancel E.radix_pos htailMul
          exact congrArg (List.cons x) (ih hlen htail)

/-- On rows of one fixed length, `value` is injective. -/
public theorem DigitCodec.value_injective_on_length (E : DigitCodec D) (n : Nat) :
    Set.InjOn E.value {row : List D | row.length = n} := by
  intro xs hxs ys hys hvalue
  exact E.value_injective_of_length_eq (hxs.trans hys.symm) hvalue

/-! ## Greatest row and increment arithmetic -/

/-- The all-greatest-digit row of a fixed width. -/
public def DigitCodec.lastRow (E : DigitCodec D) (width : Nat) : List D :=
  List.replicate width E.last

@[simp]
public theorem DigitCodec.length_lastRow (E : DigitCodec D) (width : Nat) :
    (E.lastRow width).length = width := by
  simp [DigitCodec.lastRow]

/-- The greatest row has rank `radix ^ width - 1`, stated without subtraction. -/
public theorem DigitCodec.value_lastRow_add_one (E : DigitCodec D) (width : Nat) :
    E.value (E.lastRow width) + 1 = E.radix ^ width := by
  induction width with
  | zero => simp [DigitCodec.lastRow, DigitCodec.value]
  | succ width ih =>
      rw [show E.lastRow width.succ = E.last :: E.lastRow width by
        simp [DigitCodec.lastRow, List.replicate_succ]]
      simp only [DigitCodec.value, E.digitValue_last, Nat.pow_succ]
      have hp := E.radix_pos
      have hmul := congrArg (fun n => E.radix * n) ih
      change E.radix * (E.value (E.lastRow width) + 1) =
        E.radix * (E.radix ^ width) at hmul
      rw [Nat.mul_add] at hmul
      rw [Nat.mul_comm (E.radix ^ width) E.radix]
      omega

/-- Overflow is equivalent to the old rank being the greatest possible rank. -/
public theorem DigitCodec.increment_overflow_iff_value (E : DigitCodec D) (row : List D) :
    (E.increment row).2 = true ↔ E.value row + 1 = E.radix ^ row.length := by
  rw [E.increment_overflow_iff]
  change row = E.lastRow row.length ↔ E.value row + 1 = E.radix ^ row.length
  constructor
  · intro hrow
    have hvalue : E.value row = E.value (E.lastRow row.length) := congrArg E.value hrow
    rw [hvalue]
    exact E.value_lastRow_add_one _
  · intro hvalue
    apply E.value_injective_of_length_eq
    · simp
    · have hlast := E.value_lastRow_add_one row.length
      omega

/-- A nonoverflowing increment raises the rank by exactly one. -/
public theorem DigitCodec.value_increment_of_not_overflow (E : DigitCodec D) (row : List D)
    (hno : (E.increment row).2 = false) :
    E.value (E.increment row).1 = E.value row + 1 := by
  induction row with
  | nil => simp [DigitCodec.increment] at hno
  | cons d ds ih =>
      cases hnext : E.next d with
      | some d' =>
          have hd' := (E.next_eq_some_iff d d').1 hnext
          simp only [DigitCodec.increment, hnext, DigitCodec.value]
          omega
      | none =>
          have hd : E.digitValue d + 1 = E.radix :=
            (E.next_eq_none_iff d).1 hnext
          have htail : (E.increment ds).2 = false := by
            simpa [DigitCodec.increment, hnext] using hno
          have iht := ih htail
          simp only [DigitCodec.increment, hnext, DigitCodec.value,
            E.digitValue_zero, zero_add]
          rw [iht, Nat.mul_add]
          omega

/-- The rank of fixed-width increment: on overflow it wraps to zero, otherwise it
is the old rank plus one. -/
public theorem DigitCodec.value_increment (E : DigitCodec D) (row : List D) :
    E.value (E.increment row).1 =
      if (E.increment row).2 then 0 else E.value row + 1 := by
  cases h : (E.increment row).2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact E.value_increment_of_not_overflow row h
  · simp only [↓reduceIte]
    rw [E.increment_fst_of_overflow row h, E.value_zeroRow]

/-- Fixed-width increment wraps to zero precisely after the greatest row. -/
public theorem DigitCodec.increment_overflow_result (E : DigitCodec D) (row : List D)
    (h : (E.increment row).2 = true) :
    (E.increment row).1 = E.zeroRow row.length :=
  E.increment_fst_of_overflow row h

/-- The row-only fixed-width successor. -/
public def DigitCodec.nextRow (E : DigitCodec D) (row : List D) : List D :=
  (E.increment row).1

@[simp]
public theorem DigitCodec.nextRow_length (E : DigitCodec D) (row : List D) :
    (E.nextRow row).length = row.length := by
  exact E.increment_length row

@[simp]
public theorem DigitCodec.iterate_nextRow_length (E : DigitCodec D) (k : Nat)
    (row : List D) : (E.nextRow^[k] row).length = row.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (E.nextRow_length _).trans ih

/-! ## Canonical fixed-width enumeration -/

/-- Before overflow, the rank of the `k`th row reached from zero is exactly `k`. -/
public theorem DigitCodec.value_iterate_nextRow_zeroRow (E : DigitCodec D)
    {width k : Nat} (hk : k < E.radix ^ width) :
    E.value (E.nextRow^[k] (E.zeroRow width)) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < E.radix ^ width := Nat.lt_of_succ_lt hk
      have ih' := ih hk'
      let row := E.nextRow^[k] (E.zeroRow width)
      have hlen : row.length = width := by
        simp [row]
      have hno : (E.increment row).2 = false := by
        cases hflag : (E.increment row).2
        · rfl
        · have hover := (E.increment_overflow_iff_value row).1 hflag
          rw [show E.value row = k by simpa [row] using ih', hlen] at hover
          omega
      rw [Function.iterate_succ_apply']
      change E.value (E.nextRow row) = k + 1
      simpa [DigitCodec.nextRow, ih', row] using
        E.value_increment_of_not_overflow row hno

/-- Every value below `radix ^ width` is represented by the corresponding iterate
of fixed-width successor from zero. -/
public theorem DigitCodec.exists_row_of_value (E : DigitCodec D) {width value : Nat}
    (hvalue : value < E.radix ^ width) :
    ∃ row : List D, row.length = width ∧ E.value row = value := by
  refine ⟨E.nextRow^[value] (E.zeroRow width), ?_, ?_⟩
  · simp
  · exact E.value_iterate_nextRow_zeroRow hvalue

/-- Every fixed-width row occurs in the canonical successor enumeration, at its
numeric rank. -/
public theorem DigitCodec.iterate_nextRow_value_eq (E : DigitCodec D) (row : List D) :
    E.nextRow^[E.value row] (E.zeroRow row.length) = row := by
  apply E.value_injective_of_length_eq
  · simp
  · exact E.value_iterate_nextRow_zeroRow (E.value_lt_pow_length row)

/-- Equality of two in-range enumeration positions forces equality of their ranks. -/
public theorem DigitCodec.eq_of_iterate_nextRow_eq (E : DigitCodec D)
    {width i j : Nat} (hi : i < E.radix ^ width) (hj : j < E.radix ^ width)
    (hrows : E.nextRow^[i] (E.zeroRow width) =
      E.nextRow^[j] (E.zeroRow width)) : i = j := by
  have := congrArg E.value hrows
  rwa [E.value_iterate_nextRow_zeroRow hi,
    E.value_iterate_nextRow_zeroRow hj] at this

/-- A fixed-width row occurs at a unique in-range enumeration position. -/
public theorem DigitCodec.existsUnique_iterate_nextRow_eq (E : DigitCodec D)
    {width : Nat} (row : List D) (hlen : row.length = width) :
    ∃! k : Nat, k < E.radix ^ width ∧
      E.nextRow^[k] (E.zeroRow width) = row := by
  refine ⟨E.value row, ?_, ?_⟩
  · constructor
    · simpa [hlen] using E.value_lt_pow_length row
    · simpa [hlen] using E.iterate_nextRow_value_eq row
  · intro k hk
    have hcanon : E.nextRow^[E.value row] (E.zeroRow width) = row := by
      simpa [hlen] using E.iterate_nextRow_value_eq row
    exact E.eq_of_iterate_nextRow_eq hk.1
      (by simpa [hlen] using E.value_lt_pow_length row) (hk.2.trans hcanon.symm)

/-- At an in-range enumeration position, the following increment overflows exactly
when that position is the final rank. -/
public theorem DigitCodec.increment_iterate_nextRow_overflow_iff (E : DigitCodec D)
    {width k : Nat} (hk : k < E.radix ^ width) :
    (E.increment (E.nextRow^[k] (E.zeroRow width))).2 = true ↔
      k + 1 = E.radix ^ width := by
  rw [E.increment_overflow_iff_value,
    E.value_iterate_nextRow_zeroRow hk, E.iterate_nextRow_length]
  simp

/-- Equivalently, another nonoverflowing enumeration step exists exactly before the
last rank. -/
public theorem DigitCodec.increment_iterate_nextRow_not_overflow_iff (E : DigitCodec D)
    {width k : Nat} (hk : k < E.radix ^ width) :
    (E.increment (E.nextRow^[k] (E.zeroRow width))).2 = false ↔
      k + 1 < E.radix ^ width := by
  rw [← Bool.not_eq_true, E.increment_iterate_nextRow_overflow_iff hk]
  omega

/-- Incrementing the greatest row wraps to the zero row. -/
@[simp]
public theorem DigitCodec.nextRow_lastRow (E : DigitCodec D) (width : Nat) :
    E.nextRow (E.lastRow width) = E.zeroRow width := by
  have hover : (E.increment (E.lastRow width)).2 = true := by
    rw [E.increment_overflow_iff]
    simp [DigitCodec.lastRow]
  simpa [DigitCodec.nextRow] using
    E.increment_fst_of_overflow (E.lastRow width) hover

/-- After exactly `radix ^ width` successors the enumeration has wrapped back to
the zero row. -/
public theorem DigitCodec.iterate_nextRow_capacity (E : DigitCodec D) (width : Nat) :
    E.nextRow^[E.radix ^ width] (E.zeroRow width) = E.zeroRow width := by
  have hcap : 0 < E.radix ^ width := Nat.pow_pos E.radix_pos
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcap)
  rw [hk, Function.iterate_succ_apply']
  have hklt : k < E.radix ^ width := by omega
  have hvalue := E.value_iterate_nextRow_zeroRow hklt
  have hlastValue := E.value_lastRow_add_one width
  have hrow : E.nextRow^[k] (E.zeroRow width) = E.lastRow width := by
    apply E.value_injective_of_length_eq
    · simp
    · omega
  rw [hrow, E.nextRow_lastRow]

/-- The canonical list of every row of one width, in increasing numeric rank. -/
public def DigitCodec.rowEnumeration (E : DigitCodec D) (width : Nat) : List (List D) :=
  (List.range (E.radix ^ width)).map fun k =>
    E.nextRow^[k] (E.zeroRow width)

@[simp]
public theorem DigitCodec.length_rowEnumeration (E : DigitCodec D) (width : Nat) :
    (E.rowEnumeration width).length = E.radix ^ width := by
  simp [DigitCodec.rowEnumeration]

/-- The canonical enumeration has no duplicate rows. -/
public theorem DigitCodec.rowEnumeration_nodup (E : DigitCodec D) (width : Nat) :
    (E.rowEnumeration width).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj hij
    rw [List.mem_range] at hi hj
    exact E.eq_of_iterate_nextRow_eq hi hj hij
  · exact List.nodup_range

/-- Membership in the canonical enumeration is exactly having the specified length. -/
public theorem DigitCodec.mem_rowEnumeration_iff (E : DigitCodec D)
    (width : Nat) (row : List D) :
    row ∈ E.rowEnumeration width ↔ row.length = width := by
  constructor
  · intro hrow
    rw [DigitCodec.rowEnumeration, List.mem_map] at hrow
    obtain ⟨k, hk, rfl⟩ := hrow
    rw [List.mem_range] at hk
    simp
  · intro hlen
    rw [DigitCodec.rowEnumeration, List.mem_map]
    refine ⟨E.value row, ?_, ?_⟩
    · rw [List.mem_range]
      simpa [hlen] using E.value_lt_pow_length row
    · simpa [hlen] using E.iterate_nextRow_value_eq row

/-! ## Correctness of synchronous row comparison -/

private theorem digit_add_mul_lt_iff {a b x y radix : Nat}
    (ha : a < radix) (hb : b < radix) :
    a + radix * x < b + radix * y ↔ x < y ∨ (x = y ∧ a < b) := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hmul := Nat.mul_le_mul_left radix (Nat.succ_le_iff.mpr hxy)
    simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
    constructor <;> omega
  · subst y
    constructor <;> omega
  · have hmul := Nat.mul_le_mul_left radix (Nat.succ_le_iff.mpr hyx)
    simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
    constructor <;> omega

private theorem digit_add_mul_eq_iff {a b x y radix : Nat}
    (ha : a < radix) (hb : b < radix) :
    a + radix * x = b + radix * y ↔ x = y ∧ a = b := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hmul := Nat.mul_le_mul_left radix (Nat.succ_le_iff.mpr hxy)
    simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
    constructor <;> omega
  · subst y
    constructor <;> omega
  · have hmul := Nat.mul_le_mul_left radix (Nat.succ_le_iff.mpr hyx)
    simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
    constructor <;> omega

omit [Nonempty D] in
public theorem DigitCodec.compareStep_eq_lt_iff (E : DigitCodec D)
    (q : Ordering) (x y : D) :
    E.compareStep q x y = .lt ↔
      E.digitValue x < E.digitValue y ∨
        (E.digitValue x = E.digitValue y ∧ q = .lt) := by
  unfold DigitCodec.compareStep
  rcases lt_trichotomy (E.digitValue x) (E.digitValue y) with hlt | heq | hgt
  · rw [show compare (E.digitValue x) (E.digitValue y) = .lt from
      compare_lt_iff_lt.mpr hlt]
    constructor
    · intro _
      exact Or.inl hlt
    · intro _
      rfl
  · rw [show compare (E.digitValue x) (E.digitValue y) = .eq from
      compare_eq_iff_eq.mpr heq]
    constructor
    · intro hq
      exact Or.inr ⟨heq, hq⟩
    · rintro (hlt | ⟨_, hq⟩)
      · exact (Nat.ne_of_lt hlt heq).elim
      · exact hq
  · rw [show compare (E.digitValue x) (E.digitValue y) = .gt from
      compare_gt_iff_gt.mpr hgt]
    constructor
    · intro h
      contradiction
    · rintro (hlt | ⟨heq, _⟩)
      · omega
      · omega

omit [Nonempty D] in
public theorem DigitCodec.compareStep_eq_eq_iff (E : DigitCodec D)
    (q : Ordering) (x y : D) :
    E.compareStep q x y = .eq ↔
      E.digitValue x = E.digitValue y ∧ q = .eq := by
  unfold DigitCodec.compareStep
  rcases lt_trichotomy (E.digitValue x) (E.digitValue y) with hlt | heq | hgt
  · rw [show compare (E.digitValue x) (E.digitValue y) = .lt from
      compare_lt_iff_lt.mpr hlt]
    constructor
    · intro h
      contradiction
    · rintro ⟨heq, _⟩
      exact (Nat.ne_of_lt hlt heq).elim
  · rw [show compare (E.digitValue x) (E.digitValue y) = .eq from
      compare_eq_iff_eq.mpr heq]
    constructor
    · intro hq
      exact ⟨heq, hq⟩
    · exact fun h => h.2
  · rw [show compare (E.digitValue x) (E.digitValue y) = .gt from
      compare_gt_iff_gt.mpr hgt]
    constructor
    · intro h
      contradiction
    · rintro ⟨heq, _⟩
      omega

omit [Nonempty D] in
/-- General comparison invariant: the already-scanned ordering matters exactly when
the remaining (more-significant) suffixes have equal value. -/
public theorem DigitCodec.evalCompare_eq_lt_iff (E : DigitCodec D)
    (q : Ordering) {xs ys : List D} (hlen : xs.length = ys.length) :
    E.evalCompare q xs ys = some .lt ↔
      E.value xs < E.value ys ∨ (E.value xs = E.value ys ∧ q = .lt) := by
  induction xs generalizing ys q with
  | nil =>
      cases ys with
      | nil => simp [DigitCodec.evalCompare, DigitCodec.value]
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [DigitCodec.evalCompare, ih (q := E.compareStep q x y) hlen,
            E.compareStep_eq_lt_iff]
          simp only [DigitCodec.value]
          rw [digit_add_mul_lt_iff (E.digitValue_lt x) (E.digitValue_lt y),
            digit_add_mul_eq_iff (E.digitValue_lt x) (E.digitValue_lt y)]
          tauto

omit [Nonempty D] in
/-- Equality variant of the general comparison invariant. -/
public theorem DigitCodec.evalCompare_eq_eq_iff (E : DigitCodec D)
    (q : Ordering) {xs ys : List D} (hlen : xs.length = ys.length) :
    E.evalCompare q xs ys = some .eq ↔ E.value xs = E.value ys ∧ q = .eq := by
  induction xs generalizing ys q with
  | nil =>
      cases ys with
      | nil => simp [DigitCodec.evalCompare, DigitCodec.value]
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [DigitCodec.evalCompare, ih (q := E.compareStep q x y) hlen,
            E.compareStep_eq_eq_iff]
          simp only [DigitCodec.value]
          rw [digit_add_mul_eq_iff (E.digitValue_lt x) (E.digitValue_lt y)]
          tauto

omit [Nonempty D] in
/-- The synchronous comparison reports strict inequality exactly when the numeric
ranks are strictly ordered. -/
public theorem DigitCodec.compareRows_eq_lt_iff (E : DigitCodec D)
    {xs ys : List D} (hlen : xs.length = ys.length) :
    E.compareRows xs ys = some .lt ↔ E.value xs < E.value ys := by
  unfold DigitCodec.compareRows
  simpa using E.evalCompare_eq_lt_iff .eq hlen

omit [Nonempty D] in
/-- The synchronous comparison reports equality exactly when the numeric ranks are
equal (for equal-length rows). -/
public theorem DigitCodec.compareRows_eq_eq_iff (E : DigitCodec D)
    {xs ys : List D} (hlen : xs.length = ys.length) :
    E.compareRows xs ys = some .eq ↔ E.value xs = E.value ys := by
  unfold DigitCodec.compareRows
  simpa using E.evalCompare_eq_eq_iff .eq hlen

/-! ## Boolean scanner acceptance predicates -/

/-- Boolean acceptance predicate for a nonoverflowing synchronous successor scan. -/
public def DigitCodec.checkSucc [DecidableEq D] (E : DigitCodec D)
    (old new : List D) : Bool :=
  decide (E.evalSucc .carry old new = some .done)

@[simp]
public theorem DigitCodec.checkSucc_eq_true_iff [DecidableEq D] (E : DigitCodec D)
    (old new : List D) :
    E.checkSucc old new = true ↔
      new = (E.increment old).1 ∧ (E.increment old).2 = false := by
  simp [DigitCodec.checkSucc, E.evalSucc_eq_done_iff]

/-- Boolean acceptance predicate for `value xs ≤ value ys`.  A length mismatch is
rejected because neither comparison result can be produced. -/
public def DigitCodec.checkLE (E : DigitCodec D) (xs ys : List D) : Bool :=
  decide (E.compareRows xs ys = some .lt ∨ E.compareRows xs ys = some .eq)

omit [Nonempty D] in
@[simp]
public theorem DigitCodec.checkLE_eq_true_iff (E : DigitCodec D)
    {xs ys : List D} (hlen : xs.length = ys.length) :
    E.checkLE xs ys = true ↔ E.value xs ≤ E.value ys := by
  rw [DigitCodec.checkLE, decide_eq_true_eq, E.compareRows_eq_lt_iff hlen,
    E.compareRows_eq_eq_iff hlen]
  constructor
  · rintro (hlt | heq)
    · exact Nat.le_of_lt hlt
    · exact Nat.le_of_eq heq
  · exact Nat.lt_or_eq_of_le

/-! ## The base-`Option A` fuel counter -/

/-- The canonical fuel codec.  The extra `none` digit raises its radix from `|A|`
to `|A| + 1`, independently of how the `Fintype` instance orders the digits. -/
public noncomputable def fuelCodec (A : Type*) [inst : Fintype A] :
    @DigitCodec (Option A) (@instFintypeOption A inst) :=
  @fintypeCodec (Option A) (@instFintypeOption A inst)

@[simp]
public theorem fuelCodec_radix (A : Type*) [Fintype A] :
    (fuelCodec A).radix = Fintype.card A + 1 := by
  change Fintype.card (Option A) = Fintype.card A + 1
  exact Fintype.card_option

/-- Pure cardinal-arithmetic form of the fuel-capacity bound. -/
public theorem card_pow_lt_succ_card_pow (A : Type*) [Fintype A]
    {width : Nat} (hwidth : 0 < width) :
    Fintype.card A ^ width < (Fintype.card A + 1) ^ width :=
  Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.ne_of_gt hwidth)

/-- On every positive width, an `Option A` counter has strictly more values than
there are width-`n` rows over `A`. -/
public theorem rowCapacity_lt_fuelCapacity (A : Type*) [Fintype A]
    {width : Nat} (hwidth : 0 < width) :
    Fintype.card A ^ width < (fuelCodec A).radix ^ width := by
  rw [fuelCodec_radix]
  exact card_pow_lt_succ_card_pow A hwidth

/-- Every number up to and including the number of width-`n` rows over `A` fits in
the width-`n` base-`Option A` fuel counter. -/
public theorem exists_fuelRow_of_le_rowCapacity (A : Type*) [Fintype A]
    {width value : Nat} (hwidth : 0 < width)
    (hvalue : value ≤ Fintype.card A ^ width) :
    ∃ row : List (Option A), row.length = width ∧
      (fuelCodec A).value row = value := by
  exact (fuelCodec A).exists_row_of_value
    (lt_of_le_of_lt hvalue (rowCapacity_lt_fuelCapacity A hwidth))

/-- A concrete `Fin (|A| + 1)` codec, useful when a construction wants the count
digits themselves rather than the equivalent `Option A` representation. -/
public def countDigitCodec (A : Type*) [Fintype A] :
    DigitCodec (Fin (Fintype.card A + 1)) where
  toFin := finCongr (Fintype.card_fin _).symm

@[simp]
public theorem countDigitCodec_radix (A : Type*) [Fintype A] :
    (countDigitCodec A).radix = Fintype.card A + 1 := by
  simp [DigitCodec.radix]

/-- Concrete count-row form of `exists_fuelRow_of_le_rowCapacity`. -/
public theorem exists_countRow_of_le_rowCapacity (A : Type*) [Fintype A]
    {width value : Nat} (hwidth : 0 < width)
    (hvalue : value ≤ Fintype.card A ^ width) :
    ∃ row : List (Fin (Fintype.card A + 1)), row.length = width ∧
      (countDigitCodec A).value row = value := by
  apply (countDigitCodec A).exists_row_of_value
  rw [countDigitCodec_radix]
  exact lt_of_le_of_lt hvalue (card_pow_lt_succ_card_pow A hwidth)

end RowNumeral
