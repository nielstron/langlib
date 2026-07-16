module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.FiniteVerifier
public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.Syntax
public import Langlib.Classes.Regular.Closure.Intersection
public import Langlib.Classes.Regular.Inclusion.ContextFree

@[expose]
public section

/-!
# Finite-state row predicates in malformed histories

The initial-row component is kept fully parametric in its finite verifier.  In
the final reduction this is the only component whose code depends on the input
program.
-/

namespace ContextFree.MalformedHistories

namespace RowVerifier

variable {A F : Type} (V : RowVerifier A F)

section Finite

variable [Fintype A] [Fintype F]

def dfa : DFA (Symbol A) (Option F) where
  start := some V.start
  step
    | some q, .cell a => some (V.step q a)
    | _, _ => none
  accept := {q | ∃ r, q = some r ∧ V.done r = true}

private theorem dfa_evalFrom_none (w : List (Symbol A)) :
    V.dfa.evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons s w ih => cases s <;> simpa [DFA.evalFrom, dfa] using ih

private theorem dfa_evalFrom_some_iff (q r : F) (w : List (Symbol A)) :
    V.dfa.evalFrom (some q) w = some r ↔
      ∃ row : List A,
        w = row.map Symbol.cell ∧ row.foldl V.step q = r := by
  induction w generalizing q with
  | nil =>
      constructor
      · intro h
        exact ⟨[], rfl, Option.some.inj h⟩
      · rintro ⟨row, hrow, hfold⟩
        cases row <;> simp at hrow
        simpa using hfold
  | cons s w ih =>
      cases s with
      | separator =>
          constructor
          · intro h
            change V.dfa.evalFrom none w = some r at h
            rw [V.dfa_evalFrom_none] at h
            contradiction
          · rintro ⟨row, hrow, -⟩
            cases row <;> simp at hrow
      | cell a =>
          rw [DFA.evalFrom_cons]
          change V.dfa.evalFrom (some (V.step q a)) w = some r ↔ _
          rw [ih]
          constructor
          · rintro ⟨row, rfl, hfold⟩
            exact ⟨a :: row, rfl, hfold⟩
          · rintro ⟨row, hrow, hfold⟩
            cases row with
            | nil => simp at hrow
            | cons b row =>
                simp only [List.map_cons, List.cons.injEq] at hrow
                have hab : a = b := Symbol.cell.inj hrow.1
                subst b
                exact ⟨row, hrow.2, hfold⟩

/-- Cell-only words whose underlying row is accepted by `V`. -/
def acceptLanguage : Language (Symbol A) :=
  {w | ∃ row : List A, w = row.map Symbol.cell ∧ V.Accepts row}

theorem dfa_accepts : V.dfa.accepts = V.acceptLanguage := by
  ext w
  change (∃ r, V.dfa.eval w = some r ∧ V.done r = true) ↔ _
  constructor
  · rintro ⟨r, hr, hdone⟩
    obtain ⟨row, rfl, hfold⟩ := (dfa_evalFrom_some_iff V V.start r w).mp hr
    refine ⟨row, rfl, ?_⟩
    simp [Accepts, eval, hfold, hdone]
  · rintro ⟨row, rfl, hdone⟩
    refine ⟨row.foldl V.step V.start, ?_, hdone⟩
    exact (dfa_evalFrom_some_iff V V.start _ _).mpr ⟨row, rfl, rfl⟩

theorem acceptLanguage_isRegular : V.acceptLanguage.IsRegular :=
  ⟨Option F, inferInstance, V.dfa, V.dfa_accepts⟩

/-- Cell-only words whose underlying row is rejected by `V`. -/
def rejectLanguage : Language (Symbol A) :=
  {w | ∃ row : List A, w = row.map Symbol.cell ∧ ¬ V.Accepts row}

private theorem rejectLanguage_eq :
    V.rejectLanguage =
      cellWordLanguage ⊓ (V.acceptLanguage)ᶜ := by
  ext w
  constructor
  · rintro ⟨row, rfl, hreject⟩
    refine ⟨⟨row, rfl⟩, ?_⟩
    rintro ⟨row', hrow', haccept⟩
    have heq : row = row' := by
      exact Function.Injective.list_map (fun _ _ h => Symbol.cell.inj h) hrow'
    subst row'
    exact hreject haccept
  · rintro ⟨⟨row, hrow⟩, hreject⟩
    refine ⟨row, hrow, ?_⟩
    intro haccept
    exact hreject ⟨row, hrow, haccept⟩

theorem rejectLanguage_isRegular : V.rejectLanguage.IsRegular := by
  rw [rejectLanguage_eq]
  exact cellWordLanguage_isRegular.inf' V.acceptLanguage_isRegular.compl

/-- A rejected row followed by its separator. -/
def rejectBlockLanguage : Language (Symbol A) :=
  V.rejectLanguage * ({[Symbol.separator]} : Language (Symbol A))

theorem rejectBlockLanguage_isRegular : V.rejectBlockLanguage.IsRegular :=
  V.rejectLanguage_isRegular.mul'
    (Language.isRegular_singleton_word [Symbol.separator])

theorem mem_rejectBlockLanguage_iff (w : List (Symbol A)) :
    w ∈ V.rejectBlockLanguage ↔
      ∃ row : List A,
        w = row.map Symbol.cell ++ [Symbol.separator] ∧
          ¬ V.Accepts row := by
  rw [rejectBlockLanguage, Language.mem_mul]
  constructor
  · rintro ⟨cells, ⟨row, rfl, hreject⟩, suffix, hsuffix, rfl⟩
    change suffix = [Symbol.separator] at hsuffix
    subst suffix
    exact ⟨row, rfl, hreject⟩
  · rintro ⟨row, rfl, hreject⟩
    exact ⟨row.map Symbol.cell, ⟨row, rfl, hreject⟩,
      [Symbol.separator], Set.mem_singleton _, rfl⟩

/-- The realizable bad-initial component. -/
def badInitialRealization : Language (Symbol A) :=
  ({[Symbol.separator]} : Language (Symbol A)) *
    (V.rejectBlockLanguage * blocksLanguage)

theorem badInitialRealization_isRegular : V.badInitialRealization.IsRegular :=
  (Language.isRegular_singleton_word [Symbol.separator]).mul'
    (V.rejectBlockLanguage_isRegular.mul' blocksLanguage_isRegular)

theorem badInitialRealization_eq :
    V.badInitialRealization =
      relaxedBadInitialLanguage V.Accepts := by
  ext w
  constructor
  · intro hw
    rw [badInitialRealization, Language.mem_mul] at hw
    obtain ⟨pre, hpre, suffix, hsuffix, rfl⟩ := hw
    change pre = [Symbol.separator] at hpre
    subst pre
    rw [Language.mem_mul] at hsuffix
    obtain ⟨firstBlock, hfirst, tailWord, htail, rfl⟩ := hsuffix
    obtain ⟨first, rfl, hreject⟩ :=
      (V.mem_rejectBlockLanguage_iff _).mp hfirst
    obtain ⟨tail, htail⟩ :=
      (mem_blocksLanguage_iff_exists_encodeAux false tailWord).mp htail
    refine ⟨⟨first, tail⟩, ?_, hreject⟩
    simp [RawRepresents, encode, Rows.toList, encodeAux, orientRow, htail]
  · rintro ⟨⟨first, tail⟩, hraw, hreject⟩
    refine ⟨[Symbol.separator], Set.mem_singleton _,
      first.map Symbol.cell ++ Symbol.separator :: encodeAux false tail, ?_, ?_⟩
    · rw [Language.mem_mul]
      refine ⟨first.map Symbol.cell ++ [Symbol.separator],
        (V.mem_rejectBlockLanguage_iff _).mpr ⟨first, rfl, hreject⟩,
        encodeAux false tail,
        (mem_blocksLanguage_iff_exists_encodeAux false _).mpr ⟨tail, rfl⟩, ?_⟩
      simp
    · simpa [RawRepresents, encode, Rows.toList, encodeAux, orientRow] using hraw

/-- In particular, the relaxed initial-error language is context-free. -/
theorem relaxedBadInitialLanguage_is_CF :
    is_CF (relaxedBadInitialLanguage V.Accepts) := by
  rw [← V.badInitialRealization_eq]
  exact is_CF_of_is_RG (is_RG_of_isRegular V.badInitialRealization_isRegular)

end Finite

/-! ## Initial predicates on certificate-bundled rows -/

/-- Run the unannotated initial-row verifier while also remembering whether
every incoming-certificate field was absent. -/
def bundledInitialVerifier {C : Type} (V : RowVerifier A F) :
    RowVerifier (BundledCell A C) (F × Bool) where
  start := (V.start, true)
  step state cell :=
    (V.step state.1 cell.1, state.2 && cell.2.isNone)
  done state := state.2 && V.done state.1

private theorem bundledInitialVerifier_foldl {C : Type}
    (V : RowVerifier A F) (row : List (BundledCell A C))
    (q : F) (ok : Bool) :
    row.foldl (bundledInitialVerifier V).step (q, ok) =
      ((underlyingRow row).foldl V.step q,
        ok && row.all fun cell => cell.2.isNone) := by
  induction row generalizing q ok with
  | nil => simp [underlyingRow]
  | cons cell row ih =>
      change row.foldl (bundledInitialVerifier V).step
          (V.step q cell.1, ok && cell.2.isNone) =
        ((underlyingRow row).foldl V.step (V.step q cell.1),
          ok && (cell.2.isNone && row.all fun cell => cell.2.isNone))
      rw [ih]
      simp [Bool.and_assoc]

@[simp] theorem bundledInitialVerifier_eval {C : Type}
    (V : RowVerifier A F) (row : List (BundledCell A C)) :
    (bundledInitialVerifier V).eval row =
      (V.eval (underlyingRow row),
        row.all fun cell => cell.2.isNone) := by
  exact bundledInitialVerifier_foldl V row V.start true

private theorem all_isNone_iff_isFirstBundledRow {C : Type}
    (row : List (BundledCell A C)) :
    (row.all fun cell => cell.2.isNone) = true ↔
      IsFirstBundledRow row := by
  rw [isFirstBundledRow_iff_forall]
  induction row with
  | nil => simp
  | cons cell row ih =>
      rcases cell with ⟨a, none | cert⟩ <;> simp_all

theorem bundledInitialVerifier_accepts_iff {C : Type}
    (V : RowVerifier A F) (row : List (BundledCell A C)) :
    (bundledInitialVerifier V).Accepts row ↔
      BundledInitial V row := by
  rw [RowVerifier.Accepts, bundledInitialVerifier_eval,
    bundledInitialVerifier, BundledInitial, Bool.and_eq_true,
    all_isNone_iff_isFirstBundledRow]
  rfl

section BundledFinite

variable {C : Type} [Fintype A] [Fintype C] [Fintype F]

theorem relaxedBundledBadInitialLanguage_is_CF :
    is_CF (relaxedBadInitialLanguage (BundledInitial (C := C) V)) := by
  have hcf := (bundledInitialVerifier (C := C) V).relaxedBadInitialLanguage_is_CF
  have hpred : BundledInitial (C := C) V =
      (bundledInitialVerifier (C := C) V).Accepts := by
    funext row
    apply propext
    exact (bundledInitialVerifier_accepts_iff (C := C) V row).symm
  rw [hpred]
  exact hcf

end BundledFinite

end RowVerifier

end ContextFree.MalformedHistories
