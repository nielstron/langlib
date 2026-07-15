module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Ranked fixed-width rows

The complement protocol enumerates width-`n` source rows as least-significant-first
numerals.  This file packages that enumeration as the finite vertex type
`Fin (|A| ^ n)` and records the arithmetic facts used by the semantic proof.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {I A Q F : Type*} [Fintype A] [Nonempty A]

/-- Ranks of all width-`n` rows over `A`. -/
public abbrev RankVertex (A : Type*) [Fintype A] (n : Nat) :=
  Fin (Fintype.card A ^ n)

/-- The row at a given rank in the protocol's canonical enumeration. -/
public noncomputable def rankRow (n : Nat) (v : RankVertex A n) : List A :=
  (vertexCodec A).nextRow^[v.val] ((vertexCodec A).zeroRow n)

@[simp]
public theorem length_rankRow (n : Nat) (v : RankVertex A n) :
    (rankRow n v).length = n := by
  simp [rankRow]

/-- Rank a row whose length is known to be `n`. -/
public noncomputable def rankOfRow (n : Nat) (row : List A)
    (hlen : row.length = n) : RankVertex A n :=
  ⟨(vertexCodec A).value row, by
    have h := (vertexCodec A).value_lt_pow_length row
    simpa [RowNumeral.DigitCodec.radix, vertexCodec, hlen] using h⟩

@[simp]
public theorem rankRow_rankOfRow (n : Nat) (row : List A) (hlen : row.length = n) :
    rankRow n (rankOfRow n row hlen) = row := by
  simpa [rankRow, rankOfRow, hlen] using
    (vertexCodec A).iterate_nextRow_value_eq row

@[simp]
public theorem rankOfRow_rankRow (n : Nat) (v : RankVertex A n) :
    rankOfRow n (rankRow n v) (length_rankRow n v) = v := by
  apply Fin.ext
  simp only [rankOfRow]
  exact (vertexCodec A).value_iterate_nextRow_zeroRow (by
    simp only [RowNumeral.DigitCodec.radix]
    exact v.isLt)

/-- Canonical equivalence between ranks and width-indexed list rows. -/
public noncomputable def rankRowEquiv (n : Nat) :
    RankVertex A n ≃ { row : List A // row.length = n } where
  toFun v := ⟨rankRow n v, length_rankRow n v⟩
  invFun row := rankOfRow n row.1 row.2
  left_inv := rankOfRow_rankRow n
  right_inv row := Subtype.ext (rankRow_rankOfRow n row.1 row.2)

/-- The rank graph induced by a certified row system at one fixed width. -/
public def rankEdge (D : CertifiedRowSystem I A Unit Q F) (n : Nat) :
    RankVertex A n → RankVertex A n → Prop :=
  fun old new ↦ D.RowStep (rankRow n old) (rankRow n new)

/-- The final predicate transported to ranked rows. -/
public def rankFinal (D : CertifiedRowSystem I A Unit Q F) (n : Nat) :
    RankVertex A n → Prop :=
  fun row ↦ D.Final (rankRow n row)

/-- The ranked source vertex corresponding to a concrete source row. -/
public noncomputable def sourceRank (n : Nat) (source : List A)
    (hlen : source.length = n) : RankVertex A n :=
  rankOfRow n source hlen

@[simp]
public theorem rankRow_sourceRank (n : Nat) (source : List A)
    (hlen : source.length = n) :
    rankRow n (sourceRank n source hlen) = source := by
  exact rankRow_rankOfRow n source hlen

/-- A ranked edge preserves the intended list-level edge exactly. -/
@[simp]
public theorem rankEdge_iff (D : CertifiedRowSystem I A Unit Q F) (n : Nat)
    (old new : RankVertex A n) :
    rankEdge D n old new ↔ D.RowStep (rankRow n old) (rankRow n new) :=
  Iff.rfl

/-- Ranked reachability maps to source-row reachability. -/
public theorem rankReach_sound (D : CertifiedRowSystem I A Unit Q F) (n : Nat)
    {old new : RankVertex A n}
    (h : Relation.ReflTransGen (rankEdge D n) old new) :
    Relation.ReflTransGen D.RowStep (rankRow n old) (rankRow n new) := by
  induction h with
  | refl => exact .refl
  | tail hstep hedge ih => exact ih.tail hedge

/-- Every list-level path starting at a ranked row stays at the fixed width and can be
transported back to the rank graph. -/
public theorem rankReach_complete (D : CertifiedRowSystem I A Unit Q F) (n : Nat)
    {old : RankVertex A n} {row : List A}
    (h : Relation.ReflTransGen D.RowStep (rankRow n old) row) :
    ∃ new : RankVertex A n,
      rankRow n new = row ∧ Relation.ReflTransGen (rankEdge D n) old new := by
  induction h with
  | refl => exact ⟨old, rfl, .refl⟩
  | @tail middle target hreach hedge ih =>
      obtain ⟨middleRank, hmiddle, hrank⟩ := ih
      have htarget : target.length = n := by
        rw [← D.rowStep_length hedge, ← hmiddle]
        exact length_rankRow n middleRank
      let targetRank := rankOfRow n target htarget
      refine ⟨targetRank, rankRow_rankOfRow n target htarget, hrank.tail ?_⟩
      change D.RowStep (rankRow n middleRank) (rankRow n targetRank)
      simpa [hmiddle, targetRank] using hedge

/-- Reachability between ranked endpoints is exactly list-level row reachability. -/
public theorem rankReach_iff (D : CertifiedRowSystem I A Unit Q F) (n : Nat)
    (old new : RankVertex A n) :
    Relation.ReflTransGen (rankEdge D n) old new ↔
      Relation.ReflTransGen D.RowStep (rankRow n old) (rankRow n new) := by
  constructor
  · exact rankReach_sound D n
  · intro h
    obtain ⟨target, htarget, hreach⟩ := rankReach_complete D n h
    have : target = new := by
      apply (rankRowEquiv (A := A) n).injective
      exact Subtype.ext htarget
    simpa [this] using hreach

/-! ## Canonical numeral rows -/

/-- The canonical width-`n` source-alphabet numeral for the natural number `k`.
Values outside the row capacity wrap around; semantic uses always carry an in-range proof. -/
public noncomputable def vertexNumeral (n k : Nat) : List A :=
  (vertexCodec A).nextRow^[k] ((vertexCodec A).zeroRow n)

@[simp]
public theorem vertexNumeral_zero (n : Nat) :
    vertexNumeral (A := A) n 0 = (vertexCodec A).zeroRow n := rfl

@[simp]
public theorem length_vertexNumeral (n k : Nat) :
    (vertexNumeral (A := A) n k).length = n := by
  simp [vertexNumeral]

public theorem value_vertexNumeral {n k : Nat}
    (hk : k < Fintype.card A ^ n) :
    (vertexCodec A).value (vertexNumeral (A := A) n k) = k := by
  simpa [vertexNumeral, RowNumeral.DigitCodec.radix, vertexCodec] using
    (vertexCodec A).value_iterate_nextRow_zeroRow (width := n) hk

public theorem vertexNumeral_injective {n i j : Nat}
    (hi : i < Fintype.card A ^ n) (hj : j < Fintype.card A ^ n) :
    vertexNumeral (A := A) n i = vertexNumeral n j ↔ i = j := by
  constructor
  · exact (vertexCodec A).eq_of_iterate_nextRow_eq
      (by simpa [RowNumeral.DigitCodec.radix, vertexCodec] using hi)
      (by simpa [RowNumeral.DigitCodec.radix, vertexCodec] using hj)
  · rintro rfl
    rfl

public theorem nextRow_vertexNumeral (n k : Nat) :
    (vertexCodec A).nextRow (vertexNumeral (A := A) n k) =
      vertexNumeral n (k + 1) := by
  simp [vertexNumeral, Function.iterate_succ_apply']

public theorem increment_vertexNumeral_overflow_iff {n k : Nat}
    (hk : k < Fintype.card A ^ n) :
    ((vertexCodec A).increment (vertexNumeral (A := A) n k)).2 = true ↔
      k + 1 = Fintype.card A ^ n := by
  simpa [vertexNumeral, RowNumeral.DigitCodec.radix, vertexCodec] using
    (vertexCodec A).increment_iterate_nextRow_overflow_iff
      (by simpa [RowNumeral.DigitCodec.radix, vertexCodec] using hk)

@[simp]
public theorem vertexNumeral_capacity (n : Nat) :
    vertexNumeral (A := A) n (Fintype.card A ^ n) = vertexNumeral n 0 := by
  simpa [vertexNumeral, RowNumeral.DigitCodec.radix] using
    (vertexCodec A).iterate_nextRow_capacity n

/-- The canonical width-`n` larger-radix count numeral. -/
public def countNumeral (n k : Nat) : List (CountDigit A) :=
  (countCodec A).nextRow^[k] ((countCodec A).zeroRow n)

omit [Nonempty A] in
@[simp]
public theorem countNumeral_zero (n : Nat) :
    countNumeral (A := A) n 0 = (countCodec A).zeroRow n := rfl

omit [Nonempty A] in
@[simp]
public theorem countCodec_radix :
    (countCodec A).radix = Fintype.card A + 1 := by
  simp [CountDigit, RowNumeral.DigitCodec.radix]

omit [Nonempty A] in
@[simp]
public theorem length_countNumeral (n k : Nat) :
    (countNumeral (A := A) n k).length = n := by
  simp [countNumeral]

omit [Nonempty A] in
public theorem value_countNumeral {n k : Nat}
    (hk : k < (Fintype.card A + 1) ^ n) :
    (countCodec A).value (countNumeral (A := A) n k) = k := by
  have hk' : k < (countCodec A).radix ^ n := by
    simpa only [countCodec_radix] using hk
  simpa [countNumeral] using
    (countCodec A).value_iterate_nextRow_zeroRow (width := n) hk'

omit [Nonempty A] in
public theorem countNumeral_injective {n i j : Nat}
    (hi : i < (Fintype.card A + 1) ^ n)
    (hj : j < (Fintype.card A + 1) ^ n) :
    countNumeral (A := A) n i = countNumeral n j ↔ i = j := by
  constructor
  · exact (countCodec A).eq_of_iterate_nextRow_eq
      (by simpa [countCodec_radix (A := A)] using hi)
      (by simpa [countCodec_radix (A := A)] using hj)
  · rintro rfl
    rfl

omit [Nonempty A] in
public theorem nextRow_countNumeral (n k : Nat) :
    (countCodec A).nextRow (countNumeral (A := A) n k) =
      countNumeral n (k + 1) := by
  simp [countNumeral, Function.iterate_succ_apply']

omit [Nonempty A] in
public theorem increment_countNumeral_overflow_iff {n k : Nat}
    (hk : k < (Fintype.card A + 1) ^ n) :
    ((countCodec A).increment (countNumeral (A := A) n k)).2 = true ↔
      k + 1 = (Fintype.card A + 1) ^ n := by
  simpa [countNumeral, countCodec_radix (A := A)] using
    (countCodec A).increment_iterate_nextRow_overflow_iff
      (by simpa [countCodec_radix (A := A)] using hk)

omit [Nonempty A] in
/-- The larger-radix count track can represent every number up to the number of
width-`n` source rows, provided the physical row is nonempty. -/
public theorem rowCapacity_lt_countCapacity {n : Nat} (hn : 0 < n) :
    Fintype.card A ^ n < (Fintype.card A + 1) ^ n :=
  RowNumeral.card_pow_lt_succ_card_pow A hn

omit [Nonempty A] in
/-- Count numerals are injective throughout the complete range of possible reachable
vertex counts. -/
public theorem countNumeral_injective_of_le_rowCapacity {n i j : Nat}
    (hn : 0 < n) (hi : i ≤ Fintype.card A ^ n)
    (hj : j ≤ Fintype.card A ^ n) :
    countNumeral (A := A) n i = countNumeral n j ↔ i = j := by
  apply countNumeral_injective
  · exact lt_of_le_of_lt hi (rowCapacity_lt_countCapacity hn)
  · exact lt_of_le_of_lt hj (rowCapacity_lt_countCapacity hn)

/-- The first successor of the zero count row is the boot scanner's LSD-first numeral
one. -/
public theorem countNumeral_one {n : Nat} (hn : 0 < n) :
    countNumeral (A := A) n 1 =
      (countCodec A).oneRow (countRadix_gt_one A) n := by
  apply (countCodec A).value_injective_of_length_eq
  · simp
  · rw [value_countNumeral]
    · rw [(countCodec A).value_oneRow (countRadix_gt_one A) hn]
    · have hcap := rowCapacity_lt_countCapacity (A := A) hn
      have hone : 1 ≤ Fintype.card A ^ n := by
        exact Nat.one_le_pow _ _ Fintype.card_pos
      exact lt_of_le_of_lt hone hcap

/-! ## Prefixes of the canonical vertex enumeration -/

/-- The first `i` ranked vertices. -/
public def rankPrefix (n i : Nat) : Finset (RankVertex A n) :=
  Finset.univ.filter fun v ↦ v.val < i

omit [Nonempty A] in
@[simp]
public theorem mem_rankPrefix {n i : Nat} (v : RankVertex A n) :
    v ∈ rankPrefix (A := A) n i ↔ v.val < i := by
  simp [rankPrefix]

omit [Nonempty A] in
@[simp]
public theorem rankPrefix_zero (n : Nat) :
    rankPrefix (A := A) n 0 = ∅ := by
  ext v
  simp

omit [Nonempty A] in
public theorem rankPrefix_mono {n i j : Nat} (hij : i ≤ j) :
    rankPrefix (A := A) n i ⊆ rankPrefix n j := by
  intro v hv
  rw [mem_rankPrefix] at hv ⊢
  omega

omit [Nonempty A] in
@[simp]
public theorem rankPrefix_capacity (n : Nat) :
    rankPrefix (A := A) n (Fintype.card A ^ n) = Finset.univ := by
  ext v
  simp [rankPrefix]

omit [Nonempty A] in
public theorem rankPrefix_succ {n i : Nat}
    (hi : i < Fintype.card A ^ n) :
    rankPrefix (A := A) n (i + 1) =
      insert ⟨i, hi⟩ (rankPrefix n i) := by
  ext v
  simp only [mem_rankPrefix, Finset.mem_insert, Fin.ext_iff]
  omega

omit [Nonempty A] in
public theorem card_rankPrefix {n i : Nat}
    (hi : i ≤ Fintype.card A ^ n) :
    (rankPrefix (A := A) n i).card = i := by
  induction i with
  | zero => rw [rankPrefix_zero]; rfl
  | succ i ih =>
      have hi' : i < Fintype.card A ^ n := by omega
      rw [rankPrefix_succ hi', Finset.card_insert_of_notMem]
      · rw [ih (by omega)]
      · simp

end CertifiedRowSystem.Complement
