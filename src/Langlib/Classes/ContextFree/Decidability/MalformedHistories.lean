module

public import Mathlib.Computability.Language
public import Mathlib.Data.List.Chain

@[expose]
public section

/-!
# Alternating computation histories

This file isolates the semantic core of the malformed-history reduction used
for context-free universality.  Consecutive rows are written in alternating
directions.  Thus either parity of adjacent-row comparisons can later be
checked by one pushdown scan.

The history alphabet is deliberately explicit: it has one separator in
addition to the finite row alphabet.  No target-alphabet embedding is chosen
in this file.
-/

namespace ContextFree.MalformedHistories

variable {A : Type}

/-- A history letter is either a row cell or the distinguished row separator. -/
inductive Symbol (A : Type) where
  | separator
  | cell (a : A)
  deriving DecidableEq, Fintype

@[simp] theorem card_symbol [Fintype A] : Fintype.card (Symbol A) = Fintype.card A + 1 := by
  let e : Symbol A ≃ A ⊕ Unit :=
    { toFun := fun
        | .separator => .inr ()
        | .cell a => .inl a
      invFun := fun
        | .inl a => .cell a
        | .inr _ => .separator
      left_inv := by intro x; cases x <;> rfl
      right_inv := by
        intro x
        cases x with
        | inl a => rfl
        | inr u => cases u; rfl }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_unit]

/-- Reverse exactly the odd-numbered rows. -/
def orientRow (even : Bool) (row : List A) : List A :=
  if even then row else row.reverse

def encodeAux : Bool → List (List A) → List (Symbol A)
  | _, [] => []
  | even, row :: rows =>
      (orientRow even row).map .cell ++
        .separator :: encodeAux (!even) rows

/-- Encode `# r₀ # reverse(r₁) # r₂ # ... #`. -/
def encode (rows : List (List A)) : List (Symbol A) :=
  .separator :: encodeAux true rows

private theorem cells_separator_injective
    {xs ys : List A} {u v : List (Symbol A)}
    (h : xs.map Symbol.cell ++ Symbol.separator :: u =
      ys.map Symbol.cell ++ Symbol.separator :: v) :
    xs = ys ∧ u = v := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simpa using h
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
          obtain ⟨hxy, htail⟩ := h
          cases hxy
          obtain ⟨hrows, huv⟩ := ih htail
          exact ⟨congrArg (List.cons x) hrows, huv⟩

private theorem orientRow_injective (even : Bool) :
    Function.Injective (orientRow (A := A) even) := by
  intro xs ys h
  cases even with
  | false =>
      simp only [orientRow, Bool.false_eq_true, ↓reduceIte] at h
      simpa using congrArg List.reverse h
  | true => simpa [orientRow] using h

private theorem encodeAux_injective (even : Bool) :
    Function.Injective (encodeAux (A := A) even) := by
  intro rows
  induction rows generalizing even with
  | nil =>
      intro other h
      cases other with
      | nil => rfl
      | cons row rows =>
          simp [encodeAux] at h
  | cons row rows ih =>
      intro other h
      cases other with
      | nil => simp [encodeAux] at h
      | cons row' rows' =>
          simp only [encodeAux] at h
          obtain ⟨hrow, htail⟩ := cells_separator_injective h
          have hrow' := orientRow_injective even hrow
          have hrows : rows = rows' := ih (!even) htail
          exact congrArg₂ List.cons hrow' hrows

/-- Alternating history encoding is injective, including empty rows. -/
theorem encode_injective : Function.Injective (encode (A := A)) := by
  intro rows rows' h
  exact encodeAux_injective true (List.cons.inj h).2

/-- A nonempty sequence of rows, represented by its first row and tail. -/
abbrev Rows (A : Type) := List A × List (List A)

namespace Rows

def toList (h : Rows A) : List (List A) := h.1 :: h.2

def first (h : Rows A) : List A := h.1

def last (h : Rows A) : List A := h.2.getLast?.getD h.1

/-- Every row has one common positive width. -/
def Rectangular (h : Rows A) : Prop :=
  ∃ width, 0 < width ∧ ∀ row ∈ h.toList, row.length = width

theorem toList_injective : Function.Injective (toList : Rows A → List (List A)) := by
  rintro ⟨first, tail⟩ ⟨first', tail'⟩ h
  simp only [toList, List.cons.injEq] at h
  cases h.1
  cases h.2
  rfl

end Rows

/-- `h` is the unique positive-width rectangular row sequence encoded by `w`. -/
def Represents (h : Rows A) (w : List (Symbol A)) : Prop :=
  h.Rectangular ∧ encode h.toList = w

/-- Merely parse `w` as a nonempty row sequence; no width condition is imposed. -/
def RawRepresents (h : Rows A) (w : List (Symbol A)) : Prop :=
  encode h.toList = w

theorem rawRepresents_unique {h₁ h₂ : Rows A} {w : List (Symbol A)}
    (h₁w : RawRepresents h₁ w) (h₂w : RawRepresents h₂ w) : h₁ = h₂ := by
  apply Rows.toList_injective
  apply encode_injective
  exact h₁w.trans h₂w.symm

theorem represents_unique {h₁ h₂ : Rows A} {w : List (Symbol A)}
    (h₁w : Represents h₁ w) (h₂w : Represents h₂ w) : h₁ = h₂ := by
  apply Rows.toList_injective
  apply encode_injective
  exact h₁w.2.trans h₂w.2.symm

/-- An adjacent transition failure whose source-row index has parity `parity`. -/
def BadStepAtParity (parity : Nat)
    (Step : List A → List A → Prop) (h : Rows A) : Prop :=
  ∃ (i : Nat) (hi : i + 1 < h.toList.length),
    i % 2 = parity ∧ ¬ Step h.toList[i] h.toList[i + 1]

theorem not_isChain_iff_badStepAtParity
    (Step : List A → List A → Prop) (h : Rows A) :
    ¬ h.toList.IsChain Step ↔
      BadStepAtParity 0 Step h ∨ BadStepAtParity 1 Step h := by
  classical
  constructor
  · intro hbad
    rw [List.isChain_iff_getElem] at hbad
    push_neg at hbad
    obtain ⟨i, hi, hstep⟩ := hbad
    rcases Nat.mod_two_eq_zero_or_one i with hparity | hparity
    · exact Or.inl ⟨i, hi, hparity, hstep⟩
    · exact Or.inr ⟨i, hi, hparity, hstep⟩
  · rintro (hbad | hbad) hchain
    · obtain ⟨i, hi, -, hstep⟩ := hbad
      exact hstep (hchain.getElem i hi)
    · obtain ⟨i, hi, -, hstep⟩ := hbad
      exact hstep (hchain.getElem i hi)

private theorem length_eq_first_of_isChain
    (first : List A) (tail : List (List A))
    (hchain : (first :: tail).IsChain
      (fun old new => old.length = new.length)) :
    ∀ row ∈ first :: tail, row.length = first.length := by
  induction tail generalizing first with
  | nil => simp
  | cons next tail ih =>
      rw [List.isChain_cons_cons] at hchain
      intro row hrow
      simp only [List.mem_cons] at hrow
      rcases hrow with rfl | rfl | hrow
      · rfl
      · exact hchain.1.symm
      · exact (ih next hchain.2 row (by simp [hrow])).trans hchain.1.symm

/-- Positive rectangularity is exactly a nonempty first row plus equality of
all adjacent row lengths. -/
theorem rectangular_iff_first_ne_and_length_chain (h : Rows A) :
    h.Rectangular ↔
      h.first ≠ [] ∧ h.toList.IsChain
        (fun old new => old.length = new.length) := by
  constructor
  · rintro ⟨width, hwidth, hall⟩
    have hfirst : h.first.length = width := hall h.first (by simp [Rows.toList, Rows.first])
    constructor
    · intro hempty
      rw [hempty] at hfirst
      simp at hfirst
      omega
    · rw [List.isChain_iff_getElem]
      intro i hi
      rw [hall h.toList[i] (List.getElem_mem _),
        hall h.toList[i + 1] (List.getElem_mem _)]
  · rintro ⟨hfirst, hchain⟩
    refine ⟨h.first.length, List.length_pos_of_ne_nil hfirst, ?_⟩
    intro row hrow
    exact length_eq_first_of_isChain h.first h.2 hchain row hrow

/-- The global width error splits into an empty first row or one selected
adjacent length mismatch of either parity. -/
theorem not_rectangular_iff_empty_or_bad_length (h : Rows A) :
    ¬ h.Rectangular ↔
      h.first = [] ∨
        BadStepAtParity 0 (fun old new => old.length = new.length) h ∨
        BadStepAtParity 1 (fun old new => old.length = new.length) h := by
  classical
  rw [rectangular_iff_first_ne_and_length_chain, not_and_or,
    not_ne_iff]
  constructor
  · rintro (hempty | hchain)
    · exact Or.inl hempty
    · exact Or.inr ((not_isChain_iff_badStepAtParity _ h).mp hchain)
  · rintro (hempty | hbad)
    · exact Or.inl hempty
    · exact Or.inr ((not_isChain_iff_badStepAtParity _ h).mpr hbad)

/-- Correct accepting histories for fixed row predicates and transition relation. -/
def validLanguage
    (Initial Final : List A → Prop)
    (Step : List A → List A → Prop) : Language (Symbol A) :=
  {w | ∃ h, Represents h w ∧ Initial h.first ∧ Final h.last ∧
    h.toList.IsChain Step}

/-- Words that are not positive-width rectangular history encodings. -/
def malformedLanguage : Language (Symbol A) :=
  {w | ¬ ∃ h, Represents h w}

def badInitialLanguage (Initial : List A → Prop) : Language (Symbol A) :=
  {w | ∃ h, Represents h w ∧ ¬ Initial h.first}

def badFinalLanguage (Final : List A → Prop) : Language (Symbol A) :=
  {w | ∃ h, Represents h w ∧ ¬ Final h.last}

def badStepLanguage (parity : Nat)
    (Step : List A → List A → Prop) : Language (Symbol A) :=
  {w | ∃ h, Represents h w ∧ BadStepAtParity parity Step h}

/-! The realizable error components deliberately inspect only the rows they
need.  Requiring global rectangularity in each component would introduce an
`aⁿ bⁿ cⁿ`-style non-context-free side condition. -/

def relaxedBadInitialLanguage
    (Initial : List A → Prop) : Language (Symbol A) :=
  {w | ∃ h, RawRepresents h w ∧ ¬ Initial h.first}

def relaxedBadFinalLanguage
    (Final : List A → Prop) : Language (Symbol A) :=
  {w | ∃ h, RawRepresents h w ∧ ¬ Final h.last}

def relaxedBadStepLanguage (parity : Nat)
    (Step : List A → List A → Prop) : Language (Symbol A) :=
  {w | ∃ h, RawRepresents h w ∧ BadStepAtParity parity Step h}

/-- Exact semantic decomposition used by the malformed-history reduction.
The two last components are the two alternating pushdown comparisons. -/
theorem compl_validLanguage
    (Initial Final : List A → Prop)
    (Step : List A → List A → Prop) :
    (validLanguage Initial Final Step)ᶜ =
      malformedLanguage + (badInitialLanguage Initial +
        (badFinalLanguage Final + (badStepLanguage 0 Step +
          badStepLanguage 1 Step))) := by
  classical
  ext w
  simp only [Set.mem_compl_iff, Language.mem_add, validLanguage,
    malformedLanguage, badInitialLanguage, badFinalLanguage,
    badStepLanguage, Set.mem_setOf_eq]
  constructor
  · intro hw
    by_cases hrep : ∃ h, Represents h w
    · obtain ⟨h, hhw⟩ := hrep
      have hfail : ¬ (Initial h.first ∧ Final h.last ∧
          h.toList.IsChain Step) := by
        intro hall
        exact hw ⟨h, hhw, hall⟩
      rcases not_and_or.mp hfail with hinit | hrest
      · exact Or.inr (Or.inl ⟨h, hhw, hinit⟩)
      · rcases not_and_or.mp hrest with hfinal | hstep
        · exact Or.inr (Or.inr (Or.inl ⟨h, hhw, hfinal⟩))
        · rcases (not_isChain_iff_badStepAtParity Step h).mp hstep with
            heven | hodd
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hhw, heven⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hhw, hodd⟩)))
    · exact Or.inl hrep
  · intro hw hvalid
    obtain ⟨h, hhw, hinit, hfinal, hstep⟩ := hvalid
    rcases hw with hmalformed | hbadInitial | hbadFinal | hbadEven | hbadOdd
    · exact hmalformed ⟨h, hhw⟩
    · obtain ⟨h', hh'w, hbad⟩ := hbadInitial
      have heq := represents_unique hh'w hhw
      subst h'
      exact hbad hinit
    · obtain ⟨h', hh'w, hbad⟩ := hbadFinal
      have heq := represents_unique hh'w hhw
      subst h'
      exact hbad hfinal
    · obtain ⟨h', hh'w, hbad⟩ := hbadEven
      have heq := represents_unique hh'w hhw
      subst h'
      obtain ⟨i, hi, -, hbad⟩ := hbad
      exact hbad (hstep.getElem i hi)
    · obtain ⟨h', hh'w, hbad⟩ := hbadOdd
      have heq := represents_unique hh'w hhw
      subst h'
      obtain ⟨i, hi, -, hbad⟩ := hbad
      exact hbad (hstep.getElem i hi)

/-- Exact decomposition using the relaxed, context-free-realizable error
components.  Their possible overacceptance occurs only on malformed histories,
which are already outside `validLanguage`. -/
theorem compl_validLanguage_relaxed
    (Initial Final : List A → Prop)
    (Step : List A → List A → Prop) :
    (validLanguage Initial Final Step)ᶜ =
      malformedLanguage + (relaxedBadInitialLanguage Initial +
        (relaxedBadFinalLanguage Final + (relaxedBadStepLanguage 0 Step +
          relaxedBadStepLanguage 1 Step))) := by
  classical
  ext w
  simp only [Language.mem_add, validLanguage, malformedLanguage,
    relaxedBadInitialLanguage, relaxedBadFinalLanguage,
    relaxedBadStepLanguage]
  constructor
  · intro hw
    by_cases hrep : ∃ h, Represents h w
    · obtain ⟨h, hrect, hraw⟩ := hrep
      have hfail : ¬ (Initial h.first ∧ Final h.last ∧
          h.toList.IsChain Step) := by
        intro hall
        exact hw ⟨h, ⟨hrect, hraw⟩, hall⟩
      rcases not_and_or.mp hfail with hinit | hrest
      · exact Or.inr (Or.inl ⟨h, hraw, hinit⟩)
      · rcases not_and_or.mp hrest with hfinal | hstep
        · exact Or.inr (Or.inr (Or.inl ⟨h, hraw, hfinal⟩))
        · rcases (not_isChain_iff_badStepAtParity Step h).mp hstep with
            heven | hodd
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hraw, heven⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hraw, hodd⟩)))
    · exact Or.inl hrep
  · rintro (hmalformed | hbadInitial | hbadFinal | hbadEven | hbadOdd)
      ⟨h, ⟨hrect, hraw⟩, hinit, hfinal, hstep⟩
    · exact hmalformed ⟨h, hrect, hraw⟩
    · obtain ⟨h', hh'w, hbad⟩ := hbadInitial
      have heq := rawRepresents_unique hh'w hraw
      subst h'
      exact hbad hinit
    · obtain ⟨h', hh'w, hbad⟩ := hbadFinal
      have heq := rawRepresents_unique hh'w hraw
      subst h'
      exact hbad hfinal
    · obtain ⟨h', hh'w, i, hi, -, hbad⟩ := hbadEven
      have heq := rawRepresents_unique hh'w hraw
      subst h'
      exact hbad (hstep.getElem i hi)
    · obtain ⟨h', hh'w, i, hi, -, hbad⟩ := hbadOdd
      have heq := rawRepresents_unique hh'w hraw
      subst h'
      exact hbad (hstep.getElem i hi)

end ContextFree.MalformedHistories
