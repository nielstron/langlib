module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.RowPredicates
public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.StepPredicates
public import Langlib.Classes.Regular.Closure.Reverse

@[expose]
public section

/-!
# Regular final-row error predicates

The last row is read forwards or backwards according to its index parity.
Both possibilities are regular and together realize exactly the relaxed
bad-final component.
-/

namespace ContextFree.MalformedHistories

namespace Rows

theorem last_eq_getLast_toList (h : Rows A) :
    h.last = h.toList.getLast (by simp [Rows.toList]) := by
  rcases h with ⟨first, tail⟩
  cases tail with
  | nil => rfl
  | cons next tail =>
      simp only [Rows.last, Rows.toList, List.getLast_cons]
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
      rfl

end Rows

namespace RowVerifier

variable {A C F : Type} (V : RowVerifier A F)

/-- Rejected rows written backwards, followed by their separator. -/
def reverseRejectBlockLanguage : Language (Symbol A) :=
  V.rejectLanguage.reverse *
    ({[Symbol.separator]} : Language (Symbol A))

section Finite

variable [Fintype A] [Fintype F]

theorem reverseRejectBlockLanguage_isRegular :
    V.reverseRejectBlockLanguage.IsRegular :=
  ((Language.isRegular_reverse_iff').mpr V.rejectLanguage_isRegular).mul'
    (Language.isRegular_singleton_word [Symbol.separator])

theorem mem_reverseRejectBlockLanguage_iff (w : List (Symbol A)) :
    w ∈ V.reverseRejectBlockLanguage ↔
      ∃ row : List A,
        w = row.reverse.map Symbol.cell ++ [Symbol.separator] ∧
          ¬ V.Accepts row := by
  rw [reverseRejectBlockLanguage, Language.mem_mul]
  constructor
  · rintro ⟨cells, hcells, suffix, hsuffix, rfl⟩
    change cells.reverse ∈ V.rejectLanguage at hcells
    obtain ⟨row, hrow, hreject⟩ := hcells
    change suffix = [Symbol.separator] at hsuffix
    subst suffix
    refine ⟨row, ?_, hreject⟩
    have hcells' : cells = row.reverse.map Symbol.cell := by
      calc
        cells = cells.reverse.reverse := (List.reverse_reverse cells).symm
        _ = (row.map Symbol.cell).reverse := congrArg List.reverse hrow
        _ = row.reverse.map Symbol.cell := by simp
    rw [hcells']
  · rintro ⟨row, rfl, hreject⟩
    refine ⟨row.reverse.map Symbol.cell, ?_, [Symbol.separator],
      Set.mem_singleton _, rfl⟩
    change (row.reverse.map Symbol.cell).reverse ∈ V.rejectLanguage
    simpa using (⟨row, rfl, hreject⟩ : row.map Symbol.cell ∈
      V.rejectLanguage)

end Finite

/-- A verifier on bundled rows that ignores incoming certificates. -/
def bundledFinalVerifier (V : RowVerifier A F) :
    RowVerifier (BundledCell A C) F where
  start := V.start
  step q cell := V.step q cell.1
  done := V.done

@[simp] theorem bundledFinalVerifier_eval
    (row : List (BundledCell A C)) :
    (bundledFinalVerifier (C := C) V).eval row =
      V.eval (underlyingRow row) := by
  simp [RowVerifier.eval, bundledFinalVerifier, underlyingRow,
    List.foldl_map]

theorem bundledFinalVerifier_accepts_iff
    (row : List (BundledCell A C)) :
    (bundledFinalVerifier (C := C) V).Accepts row ↔
      BundledFinal V row := by
  change V.done ((bundledFinalVerifier (C := C) V).eval row) = true ↔
    V.done (V.eval (underlyingRow row)) = true
  rw [bundledFinalVerifier_eval]

/-- Select the last row in either alternating orientation and reject it with
the finite row verifier. -/
def badFinalRealization : Language (Symbol A) :=
  (evenPrefixLanguage * V.rejectBlockLanguage) +
    (oddPrefixLanguage * V.reverseRejectBlockLanguage)

section FiniteRealization

variable [Fintype A] [Fintype F]

theorem badFinalRealization_isRegular :
    V.badFinalRealization.IsRegular :=
  (evenPrefixLanguage_isRegular.mul' V.rejectBlockLanguage_isRegular).add
    (oddPrefixLanguage_isRegular.mul'
      V.reverseRejectBlockLanguage_isRegular)

end FiniteRealization

private def evenFinalHistory (pairs : List (List A × List A))
    (final : List A) : Rows A :=
  match pairs with
  | [] => (final, [])
  | (first, second) :: pairs =>
      (first, second :: rowsOfPairs pairs ++ [final])

@[simp] private theorem evenFinalHistory_toList
    (pairs : List (List A × List A)) (final : List A) :
    (evenFinalHistory pairs final).toList =
      rowsOfPairs pairs ++ [final] := by
  cases pairs with
  | nil => rfl
  | cons pair pairs =>
      rcases pair with ⟨first, second⟩
      rfl

private def oddFinalHistory (pairs : List (List A × List A))
    (prior final : List A) : Rows A :=
  match pairs with
  | [] => (prior, [final])
  | (first, second) :: pairs =>
      (first, second :: rowsOfPairs pairs ++ [prior, final])

@[simp] private theorem oddFinalHistory_toList
    (pairs : List (List A × List A)) (prior final : List A) :
    (oddFinalHistory pairs prior final).toList =
      rowsOfPairs pairs ++ [prior, final] := by
  cases pairs with
  | nil => rfl
  | cons pair pairs =>
      rcases pair with ⟨first, second⟩
      rfl

private theorem encode_evenFinal_eq
    (pairs : List (List A × List A)) (final : List A) :
    encode (rowsOfPairs pairs ++ [final]) =
      (Symbol.separator :: encodeAux true (rowsOfPairs pairs)) ++
        (final.map Symbol.cell ++ [Symbol.separator]) := by
  simp [encode, encodeAux_rowsOfPairs_append, encodeAux, orientRow,
    List.append_assoc]

private theorem encode_oddFinal_eq
    (pairs : List (List A × List A)) (prior final : List A) :
    encode (rowsOfPairs pairs ++ [prior, final]) =
      (Symbol.separator ::
          encodeAux true (rowsOfPairs pairs ++ [prior])) ++
        (final.reverse.map Symbol.cell ++ [Symbol.separator]) := by
  simp [encode, encodeAux_rowsOfPairs_append, encodeAux, orientRow,
    List.append_assoc]

section ExactRealization

variable [Fintype A] [Fintype F]

theorem badFinalRealization_eq :
    V.badFinalRealization = relaxedBadFinalLanguage V.Accepts := by
  ext w
  constructor
  · intro hw
    rw [badFinalRealization, Language.mem_add] at hw
    rcases hw with heven | hodd
    · rw [Language.mem_mul] at heven
      obtain ⟨pre, hpre, block, hblock, rfl⟩ := heven
      obtain ⟨pairs, hpre⟩ :=
        (mem_evenPrefixLanguage_iff pre).mp hpre
      obtain ⟨final, hblock, hreject⟩ :=
        (V.mem_rejectBlockLanguage_iff block).mp hblock
      subst pre
      subst block
      let h := evenFinalHistory pairs final
      refine ⟨h, ?_, ?_⟩
      · simpa [RawRepresents, h] using encode_evenFinal_eq pairs final
      · have hlast : h.last = final := by
          rw [Rows.last_eq_getLast_toList]
          simp [h]
        simpa [hlast] using hreject
    · rw [Language.mem_mul] at hodd
      obtain ⟨pre, hpre, block, hblock, rfl⟩ := hodd
      obtain ⟨pairs, prior, hpre⟩ :=
        (mem_oddPrefixLanguage_iff pre).mp hpre
      obtain ⟨final, hblock, hreject⟩ :=
        (V.mem_reverseRejectBlockLanguage_iff block).mp hblock
      subst pre
      subst block
      let h := oddFinalHistory pairs prior final
      refine ⟨h, ?_, ?_⟩
      · simpa [RawRepresents, h] using
          encode_oddFinal_eq pairs prior final
      · have hlast : h.last = final := by
          rw [Rows.last_eq_getLast_toList]
          simp [h]
        simpa [hlast] using hreject
  · rintro ⟨h, hraw, hreject⟩
    have hne : h.toList ≠ [] := by simp [Rows.toList]
    let final := h.toList.getLast hne
    let preRows := h.toList.dropLast
    have hlast : h.last = final := by
      exact Rows.last_eq_getLast_toList h
    have hrejectFinal : ¬ V.Accepts final := by
      simpa [hlast] using hreject
    have hsplit : preRows ++ [final] = h.toList := by
      exact List.dropLast_append_getLast hne
    rcases Nat.mod_two_eq_zero_or_one preRows.length with heven | hodd
    · obtain ⟨n, hn⟩ := even_iff_exists_two_mul.mp
        (Nat.even_iff.mpr heven)
      obtain ⟨pairs, hpairs⟩ :=
        exists_rowsOfPairs_of_length_eq_two_mul preRows n hn
      left
      rw [Language.mem_mul]
      let pre := Symbol.separator :: encodeAux true (rowsOfPairs pairs)
      let block := final.map Symbol.cell ++ [Symbol.separator]
      refine ⟨pre, (mem_evenPrefixLanguage_iff pre).mpr ⟨pairs, rfl⟩,
        block, (V.mem_rejectBlockLanguage_iff block).mpr
          ⟨final, rfl, hrejectFinal⟩,
        ?_⟩
      have hrows : h.toList = rowsOfPairs pairs ++ [final] := by
        rw [← hsplit, hpairs]
      exact (encode_evenFinal_eq pairs final).symm.trans
        ((congrArg encode hrows).symm.trans hraw)
    · obtain ⟨n, hn⟩ := odd_iff_exists_bit1.mp
        (Nat.odd_iff.mpr hodd)
      obtain ⟨pairs, prior, hpairs⟩ :=
        exists_rowsOfPairs_append_singleton_of_length_eq preRows n hn
      right
      rw [Language.mem_mul]
      let pre := Symbol.separator ::
        encodeAux true (rowsOfPairs pairs ++ [prior])
      let block := final.reverse.map Symbol.cell ++ [Symbol.separator]
      refine ⟨pre, (mem_oddPrefixLanguage_iff pre).mpr
          ⟨pairs, prior, rfl⟩,
        block, (V.mem_reverseRejectBlockLanguage_iff block).mpr
          ⟨final, rfl, hrejectFinal⟩,
        ?_⟩
      have hrows : h.toList = rowsOfPairs pairs ++ [prior, final] := by
        rw [← hsplit, ← hpairs]
        simp [List.append_assoc]
      exact (encode_oddFinal_eq pairs prior final).symm.trans
        ((congrArg encode hrows).symm.trans hraw)

theorem relaxedBadFinalLanguage_is_CF :
    is_CF (relaxedBadFinalLanguage V.Accepts) := by
  rw [← V.badFinalRealization_eq]
  exact is_CF_of_is_RG (is_RG_of_isRegular V.badFinalRealization_isRegular)

end ExactRealization

section Bundled

variable [Fintype A] [Fintype C] [Fintype F]

theorem relaxedBundledBadFinalLanguage_is_CF :
    is_CF (relaxedBadFinalLanguage (BundledFinal (C := C) V)) := by
  have hcf := (bundledFinalVerifier (C := C) V).relaxedBadFinalLanguage_is_CF
  have hpred : BundledFinal (C := C) V =
      (bundledFinalVerifier (C := C) V).Accepts := by
    funext row
    apply propext
    exact (bundledFinalVerifier_accepts_iff (C := C) V row).symm
  rw [hpred]
  exact hcf

end Bundled

end RowVerifier

end ContextFree.MalformedHistories
