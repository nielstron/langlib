module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.Syntax
public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.StepPredicates
public import Langlib.Classes.ContextFree.Decidability.MirrorPair
public import Langlib.Classes.ContextFree.Closure.Concatenation
public import Langlib.Classes.ContextFree.Closure.Union
public import Langlib.Classes.Regular.Closure.Complement
public import Langlib.Classes.Regular.Inclusion.ContextFree

@[expose]
public section

/-!
# Context-free realization of malformed history syntax

A word fails to be a positive-width rectangular alternating history precisely
when it is not raw history syntax, its first row is empty, or some adjacent pair
has unequal widths.  The last alternative is selected at either parity by a
regular prefix and checked by the mirror grammar from `MirrorPair`.
-/

namespace ContextFree.MalformedHistories

variable {A : Type}

def SameWidth (left right : List A) : Prop :=
  left.length = right.length

private theorem all_same_length_of_chain (first : List A) (tail : List (List A))
    (hchain : (first :: tail).IsChain SameWidth) :
    ∀ row ∈ first :: tail, row.length = first.length := by
  induction tail generalizing first with
  | nil => simp
  | cons second tail ih =>
      rw [List.isChain_cons_cons] at hchain
      intro row hrow
      simp only [List.mem_cons] at hrow
      rcases hrow with hrow | hrow
      · subst row; rfl
      · exact (ih second hchain.2 row (by simpa using hrow)).trans hchain.1.symm

private theorem rectangular_iff_first_nonempty_chain (h : Rows A) :
    h.Rectangular ↔
      h.first ≠ [] ∧ h.toList.IsChain SameWidth := by
  constructor
  · rintro ⟨width, hwidth, hall⟩
    have hfirst : h.first.length = width :=
      hall h.first (by simp [Rows.toList, Rows.first])
    constructor
    · intro hempty
      rw [hempty] at hfirst
      simp at hfirst
      omega
    · rw [List.isChain_iff_getElem]
      intro i hi
      have hleft := hall h.toList[i]
        (List.getElem_mem (by omega : i < h.toList.length))
      have hright := hall h.toList[i + 1]
        (List.getElem_mem (by omega))
      exact hleft.trans hright.symm
  · rintro ⟨hfirst, hchain⟩
    refine ⟨h.first.length, List.length_pos_of_ne_nil hfirst, ?_⟩
    exact all_same_length_of_chain h.first h.2 hchain

/-- Failure of positive-width rectangularity is either an empty first row or
an unequal adjacent pair of one of the two parities. -/
theorem not_rectangular_iff (h : Rows A) :
    ¬ h.Rectangular ↔
      h.first = [] ∨ BadStepAtParity 0 SameWidth h ∨
        BadStepAtParity 1 SameWidth h := by
  rw [rectangular_iff_first_nonempty_chain]
  rw [not_and_or, not_isChain_iff_badStepAtParity]
  simp only [not_not]

private theorem rowsOfPairs_length (pairs : List (List A × List A)) :
    (rowsOfPairs pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p pairs => simp [rowsOfPairs, *]; omega

private theorem exists_rowsOfPairs_of_mod_two_eq_zero
    (rows : List (List A)) (hrows : rows.length % 2 = 0) :
    ∃ pairs : List (List A × List A), rows = rowsOfPairs pairs := by
  induction rows using List.twoStepInduction with
  | nil => exact ⟨[], rfl⟩
  | singleton first => simp at hrows
  | cons_cons first second rows ih _ =>
      have htail : rows.length % 2 = 0 := by
        have hmod := Nat.add_mul_mod_self_left rows.length 2 1
        simp only [List.length_cons] at hrows
        have hadd : rows.length + 1 + 1 = rows.length + 2 := by omega
        rw [hadd] at hrows
        have hmod' : (rows.length + 2) % 2 = rows.length % 2 := by
          simpa using hmod
        rwa [hmod'] at hrows
      obtain ⟨pairs, rfl⟩ := ih htail
      exact ⟨(first, second) :: pairs, rfl⟩

private theorem exists_rowsOfPairs_append_singleton_of_mod_two_eq_one
    (rows : List (List A)) (hrows : rows.length % 2 = 1) :
    ∃ (pairs : List (List A × List A)) (last : List A),
      rows = rowsOfPairs pairs ++ [last] := by
  induction rows using List.twoStepInduction with
  | nil => simp at hrows
  | singleton first => exact ⟨[], first, rfl⟩
  | cons_cons first second rows ih _ =>
      have htail : rows.length % 2 = 1 := by
        have hmod := Nat.add_mul_mod_self_left rows.length 2 1
        simp only [List.length_cons] at hrows
        have hadd : rows.length + 1 + 1 = rows.length + 2 := by omega
        rw [hadd] at hrows
        have hmod' : (rows.length + 2) % 2 = rows.length % 2 := by
          simpa using hmod
        rwa [hmod'] at hrows
      obtain ⟨pairs, last, rfl⟩ := ih htail
      exact ⟨(first, second) :: pairs, last, by
        simp [rowsOfPairs, List.append_assoc]⟩

private theorem split_at_adjacent (rows : List (List A))
    (i : ℕ) (hi : i + 1 < rows.length) :
    rows = rows.take i ++ rows[i] :: rows[i + 1] :: rows.drop (i + 2) := by
  calc
    rows = rows.take i ++ rows.drop i := (List.take_append_drop i rows).symm
    _ = rows.take i ++ rows[i] :: rows.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
    _ = rows.take i ++ rows[i] :: rows[i + 1] :: rows.drop (i + 2) := by
      rw [List.drop_eq_getElem_cons (by omega)]

/-- Two unequal-width adjacent rows, including the separator terminating the
second row. -/
def widthMismatchBlockLanguage : Language (Symbol A) :=
  lengthMismatchLanguage A *
    ({[Symbol.separator]} : Language (Symbol A))

theorem mem_widthMismatchBlockLanguage_iff (w : List (Symbol A)) :
    w ∈ widthMismatchBlockLanguage (A := A) ↔
      ∃ old new : List A, old.length ≠ new.length ∧
        w = old.map Symbol.cell ++ Symbol.separator ::
          new.reverse.map Symbol.cell ++ [Symbol.separator] := by
  rw [widthMismatchBlockLanguage, Language.mem_mul]
  constructor
  · rintro ⟨core, ⟨old, new, hlen, rfl⟩, suffix, hsuffix, rfl⟩
    change suffix = [Symbol.separator] at hsuffix
    subst suffix
    exact ⟨old, new, hlen, by simp [List.append_assoc]⟩
  · rintro ⟨old, new, hlen, rfl⟩
    refine ⟨old.map Symbol.cell ++
        Symbol.separator :: new.reverse.map Symbol.cell,
      ⟨old, new, hlen, rfl⟩, [Symbol.separator],
      Set.mem_singleton _, ?_⟩
    simp [List.append_assoc]

theorem widthMismatchBlockLanguage_is_CF [Fintype A] [DecidableEq A] :
    is_CF (widthMismatchBlockLanguage (A := A)) :=
  CF_of_CF_c_CF _ _ ⟨lengthMismatchLanguage_is_CF,
    is_CF_of_is_RG (singletonWordLanguage_is_RG [Symbol.separator])⟩

/-- A selected unequal-width pair beginning at an even row index. -/
def evenWidthErrorLanguage : Language (Symbol A) :=
  evenPrefixLanguage * (widthMismatchBlockLanguage * blocksLanguage)

/-- A selected unequal-width pair beginning at an odd row index. -/
def oddWidthErrorLanguage : Language (Symbol A) :=
  oddPrefixLanguage * (widthMismatchBlockLanguage * blocksLanguage)

theorem evenWidthErrorLanguage_is_CF [Fintype A] [DecidableEq A] :
    is_CF (evenWidthErrorLanguage (A := A)) := by
  apply CF_of_CF_c_CF
  constructor
  · exact is_CF_of_is_RG (is_RG_of_isRegular evenPrefixLanguage_isRegular)
  · apply CF_of_CF_c_CF
    exact ⟨widthMismatchBlockLanguage_is_CF,
      is_CF_of_is_RG (is_RG_of_isRegular blocksLanguage_isRegular)⟩

theorem oddWidthErrorLanguage_is_CF [Fintype A] [DecidableEq A] :
    is_CF (oddWidthErrorLanguage (A := A)) := by
  apply CF_of_CF_c_CF
  constructor
  · exact is_CF_of_is_RG (is_RG_of_isRegular oddPrefixLanguage_isRegular)
  · apply CF_of_CF_c_CF
    exact ⟨widthMismatchBlockLanguage_is_CF,
      is_CF_of_is_RG (is_RG_of_isRegular blocksLanguage_isRegular)⟩

private def evenWidthSelectedHistory
    (pairs : List (List A × List A))
    (old new : List A) (tail : List (List A)) : Rows A :=
  match pairs with
  | [] => (old, new :: tail)
  | (first, second) :: pairs =>
      (first, second :: rowsOfPairs pairs ++ old :: new :: tail)

@[simp] private theorem evenWidthSelectedHistory_toList
    (pairs : List (List A × List A)) (old new : List A)
    (tail : List (List A)) :
    (evenWidthSelectedHistory pairs old new tail).toList =
      rowsOfPairs pairs ++ old :: new :: tail := by
  cases pairs with
  | nil => rfl
  | cons pair pairs =>
      rcases pair with ⟨first, second⟩
      rfl

private def oddWidthSelectedHistory
    (pairs : List (List A × List A))
    (prior old new : List A) (tail : List (List A)) : Rows A :=
  match pairs with
  | [] => (prior, old :: new :: tail)
  | (first, second) :: pairs =>
      (first,
        second :: rowsOfPairs pairs ++ prior :: old :: new :: tail)

@[simp] private theorem oddWidthSelectedHistory_toList
    (pairs : List (List A × List A)) (prior old new : List A)
    (tail : List (List A)) :
    (oddWidthSelectedHistory pairs prior old new tail).toList =
      rowsOfPairs pairs ++ prior :: old :: new :: tail := by
  cases pairs with
  | nil => rfl
  | cons pair pairs =>
      rcases pair with ⟨first, second⟩
      rfl

private theorem encode_evenWidthSelected_eq
    (pairs : List (List A × List A)) (old new : List A)
    (tail : List (List A)) :
    encode (rowsOfPairs pairs ++ old :: new :: tail) =
      (Symbol.separator :: encodeAux true (rowsOfPairs pairs)) ++
        ((old.map Symbol.cell ++ Symbol.separator ::
            new.reverse.map Symbol.cell ++ [Symbol.separator]) ++
          encodeAux true tail) := by
  simp [encode, encodeAux_rowsOfPairs_append, encodeAux, orientRow,
    List.append_assoc]

private theorem encode_oddWidthSelected_eq
    (pairs : List (List A × List A)) (prior old new : List A)
    (tail : List (List A)) :
    encode (rowsOfPairs pairs ++ prior :: old :: new :: tail) =
      (Symbol.separator ::
          encodeAux true (rowsOfPairs pairs ++ [prior])) ++
        ((old.reverse.map Symbol.cell ++ Symbol.separator ::
            new.map Symbol.cell ++ [Symbol.separator]) ++
          encodeAux false tail) := by
  simp [encode, encodeAux_rowsOfPairs_append, encodeAux, orientRow,
    List.append_assoc]

/-- The even selected-width grammar recognizes exactly raw histories with an
unequal-width adjacent pair at an even index. -/
theorem evenWidthErrorLanguage_eq :
    evenWidthErrorLanguage (A := A) =
      relaxedBadStepLanguage 0 SameWidth := by
  ext w
  constructor
  · intro hw
    rw [evenWidthErrorLanguage, Language.mem_mul] at hw
    obtain ⟨pre, hpre, rest, hrest, rfl⟩ := hw
    rw [Language.mem_mul] at hrest
    obtain ⟨block, hblock, suffix, hsuffix, rfl⟩ := hrest
    obtain ⟨pairs, hpre⟩ := (mem_evenPrefixLanguage_iff pre).mp hpre
    obtain ⟨old, new, hlength, hblock⟩ :=
      (mem_widthMismatchBlockLanguage_iff block).mp hblock
    obtain ⟨tail, hsuffix⟩ :=
      (mem_blocksLanguage_iff_exists_encodeAux true suffix).mp hsuffix
    subst pre
    subst block
    rw [← hsuffix]
    let h := evenWidthSelectedHistory pairs old new tail
    refine ⟨h, ?_, ?_⟩
    · simpa [RawRepresents, h] using
        encode_evenWidthSelected_eq pairs old new tail
    · apply (badStepAtParity_zero_iff SameWidth h).mpr
      exact ⟨pairs, old, new, tail, by simp [h], hlength⟩
  · rintro ⟨h, hraw, hbad⟩
    obtain ⟨pairs, old, new, tail, hrows, hlength⟩ :=
      (badStepAtParity_zero_iff SameWidth h).mp hbad
    let pre := Symbol.separator :: encodeAux true (rowsOfPairs pairs)
    let block := old.map Symbol.cell ++ Symbol.separator ::
      new.reverse.map Symbol.cell ++ [Symbol.separator]
    let suffix := encodeAux true tail
    rw [evenWidthErrorLanguage, Language.mem_mul]
    refine ⟨pre, (mem_evenPrefixLanguage_iff pre).mpr ⟨pairs, rfl⟩,
      block ++ suffix, ?_, ?_⟩
    · rw [Language.mem_mul]
      exact ⟨block, (mem_widthMismatchBlockLanguage_iff block).mpr
          ⟨old, new, hlength, rfl⟩,
        suffix,
        (mem_blocksLanguage_iff_exists_encodeAux true suffix).mpr
          ⟨tail, rfl⟩,
        rfl⟩
    · have hencoded := encode_evenWidthSelected_eq pairs old new tail
      exact hencoded.symm.trans
        ((congrArg encode hrows).symm.trans hraw)

/-- The odd selected-width grammar recognizes exactly raw histories with an
unequal-width adjacent pair at an odd index. -/
theorem oddWidthErrorLanguage_eq :
    oddWidthErrorLanguage (A := A) =
      relaxedBadStepLanguage 1 SameWidth := by
  ext w
  constructor
  · intro hw
    rw [oddWidthErrorLanguage, Language.mem_mul] at hw
    obtain ⟨pre, hpre, rest, hrest, rfl⟩ := hw
    rw [Language.mem_mul] at hrest
    obtain ⟨block, hblock, suffix, hsuffix, rfl⟩ := hrest
    obtain ⟨pairs, prior, hpre⟩ :=
      (mem_oddPrefixLanguage_iff pre).mp hpre
    obtain ⟨xs, ys, hlength, hblock⟩ :=
      (mem_widthMismatchBlockLanguage_iff block).mp hblock
    obtain ⟨tail, hsuffix⟩ :=
      (mem_blocksLanguage_iff_exists_encodeAux false suffix).mp hsuffix
    subst pre
    subst block
    rw [← hsuffix]
    let old := xs.reverse
    let new := ys.reverse
    let h := oddWidthSelectedHistory pairs prior old new tail
    refine ⟨h, ?_, ?_⟩
    · simpa [RawRepresents, h, old, new] using
        encode_oddWidthSelected_eq pairs prior old new tail
    · apply (badStepAtParity_one_iff SameWidth h).mpr
      refine ⟨pairs, prior, old, new, tail, by simp [h], ?_⟩
      simpa [SameWidth, old, new] using hlength
  · rintro ⟨h, hraw, hbad⟩
    obtain ⟨pairs, prior, old, new, tail, hrows, hlength⟩ :=
      (badStepAtParity_one_iff SameWidth h).mp hbad
    let pre := Symbol.separator ::
      encodeAux true (rowsOfPairs pairs ++ [prior])
    let block := old.reverse.map Symbol.cell ++ Symbol.separator ::
      new.map Symbol.cell ++ [Symbol.separator]
    let suffix := encodeAux false tail
    rw [oddWidthErrorLanguage, Language.mem_mul]
    refine ⟨pre, (mem_oddPrefixLanguage_iff pre).mpr
        ⟨pairs, prior, rfl⟩,
      block ++ suffix, ?_, ?_⟩
    · rw [Language.mem_mul]
      exact ⟨block, (mem_widthMismatchBlockLanguage_iff block).mpr
          ⟨old.reverse, new.reverse, by simpa [SameWidth] using hlength,
            by simp [block]⟩,
        suffix,
        (mem_blocksLanguage_iff_exists_encodeAux false suffix).mpr
          ⟨tail, rfl⟩,
        rfl⟩
    · have hencoded := encode_oddWidthSelected_eq pairs prior old new tail
      exact hencoded.symm.trans
        ((congrArg encode hrows).symm.trans hraw)

/-- Context-free realization of all words that fail to encode a nonempty,
positive-width rectangular history. -/
def malformedSyntaxLanguage : Language (Symbol A) :=
  (rawFormatLanguage (A := A))ᶜ +
    (emptyFirstLanguage +
      (evenWidthErrorLanguage + oddWidthErrorLanguage))

private theorem mem_malformedLanguage_iff (w : List (Symbol A)) :
    w ∈ malformedLanguage ↔
      (¬ ∃ h : Rows A, RawRepresents h w) ∨
        ∃ h : Rows A, RawRepresents h w ∧ ¬ h.Rectangular := by
  constructor
  · intro hw
    by_cases hraw : ∃ h : Rows A, RawRepresents h w
    · right
      obtain ⟨h, hhw⟩ := hraw
      exact ⟨h, hhw, fun hrect => hw ⟨h, hrect, hhw⟩⟩
    · exact Or.inl hraw
  · rintro (hraw | ⟨h, hhw, hrect⟩)
    · rintro ⟨h, -, hhw⟩
      exact hraw ⟨h, hhw⟩
    · rintro ⟨h', hrect', hhw'⟩
      have heq := rawRepresents_unique hhw hhw'
      subst h'
      exact hrect hrect'

/-- The grammar-side malformed syntax realization is extensionally exact. -/
theorem malformedSyntaxLanguage_eq :
    malformedSyntaxLanguage (A := A) = malformedLanguage := by
  ext w
  rw [mem_malformedLanguage_iff]
  simp only [malformedSyntaxLanguage, Language.mem_add, Set.mem_compl_iff]
  rw [evenWidthErrorLanguage_eq, oddWidthErrorLanguage_eq]
  simp only [relaxedBadStepLanguage]
  constructor
  · rintro (hraw | hempty | heven | hodd)
    · left
      change w ∉ rawFormatLanguage at hraw
      rw [mem_rawFormatLanguage_iff] at hraw
      exact hraw
    · right
      obtain ⟨h, hhw, hfirst⟩ :=
        (mem_emptyFirstLanguage_iff w).mp hempty
      refine ⟨h, hhw, ?_⟩
      exact (not_rectangular_iff h).mpr (Or.inl hfirst)
    · right
      obtain ⟨h, hhw, hbad⟩ := heven
      exact ⟨h, hhw,
        (not_rectangular_iff h).mpr (Or.inr (Or.inl hbad))⟩
    · right
      obtain ⟨h, hhw, hbad⟩ := hodd
      exact ⟨h, hhw,
        (not_rectangular_iff h).mpr (Or.inr (Or.inr hbad))⟩
  · rintro (hraw | ⟨h, hhw, hrect⟩)
    · left
      change w ∉ rawFormatLanguage
      rw [mem_rawFormatLanguage_iff]
      exact hraw
    · rcases (not_rectangular_iff h).mp hrect with
        hfirst | heven | hodd
      · right; left
        exact (mem_emptyFirstLanguage_iff w).mpr ⟨h, hhw, hfirst⟩
      · right; right; left
        exact ⟨h, hhw, heven⟩
      · right; right; right
        exact ⟨h, hhw, hodd⟩

/-- Malformed alternating histories form a context-free language. -/
theorem malformedLanguage_is_CF [Fintype A] [DecidableEq A] :
    is_CF (malformedLanguage : Language (Symbol A)) := by
  rw [← malformedSyntaxLanguage_eq]
  apply CF_of_CF_u_CF
  constructor
  · exact is_CF_of_is_RG (is_RG_of_isRegular
      rawFormatLanguage_isRegular.compl)
  · apply CF_of_CF_u_CF
    constructor
    · exact is_CF_of_is_RG (is_RG_of_isRegular
        emptyFirstLanguage_isRegular)
    · apply CF_of_CF_u_CF
      exact ⟨evenWidthErrorLanguage_is_CF,
        oddWidthErrorLanguage_is_CF⟩

end ContextFree.MalformedHistories
