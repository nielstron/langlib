module

public import Langlib.Automata.LinearBounded.Cofunctional.ClampedObstruction
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.Reversible
import Mathlib.Tactic

@[expose]
public section

/-!
# Configuration-reversible clamped LBAs recognize only trivial languages

`Machine.ConfigurationBiUnique` quantifies over the complete raw configuration graph at every
tape width.  The clamping obstruction therefore applies: its left-unique half rules out every
enabled `left` or `right` local transition.  Runs can only rewrite the cell initially under the
head.  In the canonical endmarker model that cell is always the same left marker, independently
of the input word, so acceptance is input-independent.

This collapses the currently defined `ReversibleLBA` class exactly to the empty and universal
languages.  It does not concern reversible machines defined over a promised well-formed subset
of configurations or over an unclamped tape model.
-/

namespace LBA

open Relation

variable {Γ Λ : Type*}

/-- The left-unique half of configuration biuniqueness is global cofunctionality. -/
public theorem Machine.cofunctional_of_configurationBiUnique
    (M : Machine Γ Λ) (hreversible : M.ConfigurationBiUnique) :
    M.Cofunctional := by
  intro n left right target hleft hright
  exact (hreversible n).1 hleft hright

/-- Every enabled local transition of a configuration-reversible clamped LBA is stationary. -/
public theorem Machine.direction_eq_stay_of_configurationBiUnique
    (M : Machine Γ Λ) (hreversible : M.ConfigurationBiUnique)
    {source target : Λ} {read written : Γ} {direction : DLBA.Dir}
    (henabled : (target, written, direction) ∈ M.transition source read) :
    direction = .stay :=
  M.direction_eq_stay_of_cofunctional
    (M.cofunctional_of_configurationBiUnique hreversible) henabled

/-- Canonical endmarker acceptance by a configuration-reversible machine is independent of the
input word. -/
public theorem Machine.languageEnd_iff_of_configurationBiUnique
    {T : Type*} (M : Machine (EndAlpha T Γ) Λ)
    (hreversible : M.ConfigurationBiUnique) (left right : List T) :
    LanguageEnd M left ↔ LanguageEnd M right := by
  apply M.accepts_iff_of_same_state_read_of_cofunctional
    (M.cofunctional_of_configurationBiUnique hreversible)
  · rfl
  · simp [initCfgEnd, loadEnd, DLBA.BoundedTape.read]

/-- The transition-free one-state LBA, parameterized by whether its unique state accepts. -/
public def Machine.trivialReversible (Γ : Type*) (accepts : Bool) : Machine Γ Unit where
  transition _ _ := ∅
  accept _ := accepts
  initial := ()

/-- The transition-free machine is configuration-biunique on every raw tape. -/
public theorem Machine.trivialReversible_configurationBiUnique
    (Γ : Type*) (accepts : Bool) :
    (Machine.trivialReversible Γ accepts).ConfigurationBiUnique := by
  intro n
  constructor
  · intro left right target hleft _hright
    rcases hleft with ⟨next, written, direction, henabled, _⟩
    simp [Machine.trivialReversible] at henabled
  · intro source left right hleft _hright
    rcases hleft with ⟨next, written, direction, henabled, _⟩
    simp [Machine.trivialReversible] at henabled

/-- The rejecting transition-free machine recognizes the empty endmarker language. -/
public theorem Machine.languageEnd_trivialReversible_false
    {T Γ : Type*} :
    LanguageEnd (Machine.trivialReversible (EndAlpha T Γ) false) =
      (∅ : Set (List T)) := by
  ext input
  constructor
  · rintro ⟨target, _hreach, haccept⟩
    simp [Machine.trivialReversible] at haccept
  · intro hmem
    exact hmem.elim

/-- The accepting transition-free machine recognizes the universal endmarker language. -/
public theorem Machine.languageEnd_trivialReversible_true
    {T Γ : Type*} :
    LanguageEnd (Machine.trivialReversible (EndAlpha T Γ) true) =
      (Set.univ : Set (List T)) := by
  ext input
  change Accepts (Machine.trivialReversible (EndAlpha T Γ) true)
      (initCfgEnd (Machine.trivialReversible (EndAlpha T Γ) true) input) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨initCfgEnd (Machine.trivialReversible (EndAlpha T Γ) true) input,
      .refl, rfl⟩

end LBA

/-! ## Exact class characterization -/

/-- The empty language has a configuration-reversible endmarker presentation. -/
public theorem is_ReversibleLBA_empty
    {T : Type} [Fintype T] [DecidableEq T] :
    is_ReversibleLBA (∅ : Set (List T)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    LBA.Machine.trivialReversible (LBA.EndAlpha T Unit) false,
    LBA.Machine.trivialReversible_configurationBiUnique _ _, ?_⟩
  exact LBA.Machine.languageEnd_trivialReversible_false

/-- The universal language has a configuration-reversible endmarker presentation. -/
public theorem is_ReversibleLBA_univ
    {T : Type} [Fintype T] [DecidableEq T] :
    is_ReversibleLBA (Set.univ : Set (List T)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    LBA.Machine.trivialReversible (LBA.EndAlpha T Unit) true,
    LBA.Machine.trivialReversible_configurationBiUnique _ _, ?_⟩
  exact LBA.Machine.languageEnd_trivialReversible_true

/-- Every configuration-reversible endmarker language is either empty or universal. -/
public theorem is_ReversibleLBA_iff_eq_empty_or_univ
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T} :
    is_ReversibleLBA L ↔
      L = (∅ : Set (List T)) ∨ L = (Set.univ : Set (List T)) := by
  constructor
  · rintro ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hreversible, hlanguage⟩
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
        exact (M.languageEnd_iff_of_configurationBiUnique
          hreversible input []).2 hemptyInput
    · left
      rw [← hlanguage]
      ext input
      change LBA.LanguageEnd M input ↔ False
      constructor
      · intro haccept
        exact hemptyInput ((M.languageEnd_iff_of_configurationBiUnique
          hreversible input []).1 haccept)
      · intro hfalse
        exact hfalse.elim
  · rintro (hempty | huniv)
    · rw [hempty]
      exact is_ReversibleLBA_empty
    · rw [huniv]
      exact is_ReversibleLBA_univ

/-- The currently defined configuration-reversible LBA class is exactly the two trivial
languages. -/
public theorem reversibleLBA_eq_trivial_languages
    {T : Type} [Fintype T] [DecidableEq T] :
    (ReversibleLBA : Set (Language T)) =
      ({(∅ : Set (List T)), (Set.univ : Set (List T))} : Set (Language T)) := by
  ext L
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact is_ReversibleLBA_iff_eq_empty_or_univ
