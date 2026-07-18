module

public import Langlib.Automata.LinearBounded.Cofunctional.ClampedObstruction
import Mathlib.Tactic

@[expose]
public section

/-!
# Globally cofunctional clamped LBAs recognize only trivial endmarker languages

The repository's `LBA.Machine.Cofunctional` predicate quantifies over the complete raw
configuration graph at every tape width.  Boundary clamping then rules out every enabled
directional transition.  Consequently a run can inspect and rewrite only the cell initially
under the head.  In the canonical endmarker presentation that cell is always the left marker,
independently of the input word, so acceptance is input-independent.

This file packages that observation as an exact language-class characterization: finite
globally cofunctional endmarker LBAs recognize exactly the empty and universal languages.  Both
languages have transition-free deterministic presentations, giving a direct inclusion of this
restricted class in `DLBA` over every finite terminal alphabet, with no cardinality or
inhabitedness assumption on that alphabet.

This collapse concerns the literal all-raw-configurations predicate.  It does not apply to a
cofunctionality promise restricted to well-formed configurations or to an unclamped tape model.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- Canonical endmarker acceptance by a globally cofunctional clamped LBA is independent of the
input word.  No finiteness or nonemptiness assumptions on the component types are needed. -/
public theorem Machine.languageEnd_iff_of_cofunctional
    {T : Type*} (M : Machine (EndAlpha T Γ) Λ) (hco : M.Cofunctional)
    (left right : List T) :
    LanguageEnd M left ↔ LanguageEnd M right := by
  apply M.accepts_iff_of_same_state_read_of_cofunctional hco
  · rfl
  · simp [initCfgEnd, loadEnd, DLBA.BoundedTape.read]

/-- A transition-free one-state LBA, parameterized by whether its unique state accepts. -/
public def Machine.trivialCofunctional (Γ : Type*) (accepts : Bool) : Machine Γ Unit where
  transition _ _ := ∅
  accept _ := accepts
  initial := ()

/-- A transition-free machine is cofunctional on every raw bounded tape. -/
public theorem Machine.trivialCofunctional_cofunctional
    (Γ : Type*) (accepts : Bool) :
    (Machine.trivialCofunctional Γ accepts).Cofunctional := by
  intro n left right target hleft _hright
  rcases hleft with ⟨next, written, direction, henabled, _⟩
  simp [Machine.trivialCofunctional] at henabled

/-- The rejecting transition-free LBA recognizes the empty canonical endmarker language. -/
public theorem Machine.languageEnd_trivialCofunctional_false
    {T Γ : Type*} :
    LanguageEnd (Machine.trivialCofunctional (EndAlpha T Γ) false) =
      (∅ : Set (List T)) := by
  ext input
  constructor
  · rintro ⟨target, _hreach, haccept⟩
    simp [Machine.trivialCofunctional] at haccept
  · intro hmem
    exact hmem.elim

/-- The accepting transition-free LBA recognizes the universal canonical endmarker language. -/
public theorem Machine.languageEnd_trivialCofunctional_true
    {T Γ : Type*} :
    LanguageEnd (Machine.trivialCofunctional (EndAlpha T Γ) true) =
      (Set.univ : Set (List T)) := by
  ext input
  change Accepts (Machine.trivialCofunctional (EndAlpha T Γ) true)
      (initCfgEnd (Machine.trivialCofunctional (EndAlpha T Γ) true) input) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨initCfgEnd (Machine.trivialCofunctional (EndAlpha T Γ) true) input,
      .refl, rfl⟩

end LBA

/-! ## Exact cofunctional language class -/

/-- A language has a globally cofunctional LBA presentation when it is recognized by a finite
canonical endmarker machine whose complete raw clamped configuration relation is cofunctional at
every tape width. -/
public def is_CofunctionalLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.Cofunctional ∧ LBA.LanguageEnd M = L

/-- Languages with a finite, globally cofunctional, canonical endmarker LBA presentation. -/
public def CofunctionalLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_CofunctionalLBA

/-- The empty language has a globally cofunctional endmarker presentation. -/
public theorem is_CofunctionalLBA_empty
    {T : Type} [Fintype T] [DecidableEq T] :
    is_CofunctionalLBA (∅ : Set (List T)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    LBA.Machine.trivialCofunctional (LBA.EndAlpha T Unit) false,
    LBA.Machine.trivialCofunctional_cofunctional _ _, ?_⟩
  exact LBA.Machine.languageEnd_trivialCofunctional_false

/-- The universal language has a globally cofunctional endmarker presentation. -/
public theorem is_CofunctionalLBA_univ
    {T : Type} [Fintype T] [DecidableEq T] :
    is_CofunctionalLBA (Set.univ : Set (List T)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    LBA.Machine.trivialCofunctional (LBA.EndAlpha T Unit) true,
    LBA.Machine.trivialCofunctional_cofunctional _ _, ?_⟩
  exact LBA.Machine.languageEnd_trivialCofunctional_true

/-- A finite globally cofunctional endmarker LBA recognizes exactly an empty or universal
language.  This holds for every finite terminal type, including the empty type. -/
public theorem is_CofunctionalLBA_iff_eq_empty_or_univ
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T} :
    is_CofunctionalLBA L ↔
      L = (∅ : Set (List T)) ∨ L = (Set.univ : Set (List T)) := by
  constructor
  · rintro ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hco, hlanguage⟩
    letI := hΓ
    letI := hΛ
    letI := hdecΓ
    letI := hdecΛ
    by_cases hemptyInput : LBA.LanguageEnd M ([] : List T)
    · right
      rw [← hlanguage]
      ext input
      change LBA.LanguageEnd M input ↔ True
      constructor
      · intro _
        trivial
      · intro _
        exact (M.languageEnd_iff_of_cofunctional hco input []).2 hemptyInput
    · left
      rw [← hlanguage]
      ext input
      change LBA.LanguageEnd M input ↔ False
      constructor
      · intro haccept
        exact hemptyInput ((M.languageEnd_iff_of_cofunctional hco input []).1 haccept)
      · intro hfalse
        exact hfalse.elim
  · rintro (hempty | huniv)
    · rw [hempty]
      exact is_CofunctionalLBA_empty
    · rw [huniv]
      exact is_CofunctionalLBA_univ

/-- The globally cofunctional endmarker-LBA class is exactly the two trivial languages. -/
public theorem cofunctionalLBA_eq_trivial_languages
    {T : Type} [Fintype T] [DecidableEq T] :
    (CofunctionalLBA : Set (Language T)) =
      ({(∅ : Set (List T)), (Set.univ : Set (List T))} : Set (Language T)) := by
  ext L
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact is_CofunctionalLBA_iff_eq_empty_or_univ

/-! ## Direct deterministic presentations -/

namespace DLBA

/-- A deterministic transition-free one-state bounded machine. -/
public def Machine.trivialHalt (Γ : Type*) (accepts : Bool) : Machine Γ Unit where
  transition _ _ := none
  accept _ := accepts
  initial := ()

/-- With a rejecting state and a rejecting empty-word bit, `trivialHalt` recognizes the empty
language through every input embedding. -/
public theorem Machine.languageRecognized_trivialHalt_false
    {T Γ : Type*} (embed : T → Γ) :
    LanguageRecognized (Machine.trivialHalt Γ false) embed false =
      (∅ : Set (List T)) := by
  ext input
  change ((false = true ∧ input = []) ∨
    ∃ (hw : input.map embed ≠ []),
      Accepts (Machine.trivialHalt Γ false)
        (initCfgList (Machine.trivialHalt Γ false) (input.map embed) hw)) ↔ False
  constructor
  · rintro (hempty | ⟨_hw, haccept⟩)
    · simp at hempty
    · rcases haccept with ⟨steps, hhalt, target, htarget, haccept⟩
      simp [Machine.trivialHalt] at haccept
  · exact False.elim

/-- With an accepting state and an accepting empty-word bit, `trivialHalt` recognizes the
universal language through every input embedding. -/
public theorem Machine.languageRecognized_trivialHalt_true
    {T Γ : Type*} (embed : T → Γ) :
    LanguageRecognized (Machine.trivialHalt Γ true) embed true =
      (Set.univ : Set (List T)) := by
  ext input
  change ((true = true ∧ input = []) ∨
    ∃ (hw : input.map embed ≠ []),
      Accepts (Machine.trivialHalt Γ true)
        (initCfgList (Machine.trivialHalt Γ true) (input.map embed) hw)) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    by_cases hempty : input = []
    · exact Or.inl ⟨rfl, hempty⟩
    · have hmap : input.map embed ≠ [] := by simpa using hempty
      refine Or.inr ⟨hmap, ?_⟩
      let source := initCfgList (Machine.trivialHalt Γ true) (input.map embed) hmap
      exact ⟨0, rfl, source, rfl, rfl⟩

end DLBA

/-- The empty language has a transition-free deterministic LBA presentation. -/
public theorem is_DLBA_empty_language
    {T : Type} [Fintype T] [DecidableEq T] :
    is_DLBA (∅ : Set (List T)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    false, DLBA.Machine.trivialHalt (Option (T ⊕ Unit)) false, ?_⟩
  exact DLBA.Machine.languageRecognized_trivialHalt_false _

/-- The universal language has a transition-free deterministic LBA presentation. -/
public theorem is_DLBA_univ_language
    {T : Type} [Fintype T] [DecidableEq T] :
    is_DLBA (Set.univ : Set (List T)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    true, DLBA.Machine.trivialHalt (Option (T ⊕ Unit)) true, ?_⟩
  exact DLBA.Machine.languageRecognized_trivialHalt_true _

/-- Every globally cofunctional endmarker-LBA language has a deterministic LBA presentation. -/
public theorem is_DLBA_of_is_CofunctionalLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_CofunctionalLBA L) : is_DLBA L := by
  rcases is_CofunctionalLBA_iff_eq_empty_or_univ.mp hL with hempty | huniv
  · rw [hempty]
    exact is_DLBA_empty_language
  · rw [huniv]
    exact is_DLBA_univ_language

/-- Set-theoretic form of the direct inclusion into deterministic LBA languages. -/
public theorem cofunctionalLBA_subset_DLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (CofunctionalLBA : Set (Language T)) ⊆ DLBA :=
  fun _ hL => is_DLBA_of_is_CofunctionalLBA hL

end
