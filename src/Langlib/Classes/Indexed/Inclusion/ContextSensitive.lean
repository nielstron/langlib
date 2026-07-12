module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Classes.ContextSensitive.Closure.FiniteLanguage
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
public import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
public import Langlib.Classes.Indexed.Basics.FiniteSupport
public import Langlib.Grammars.Indexed.NormalForm.Aho.Inclusion
@[expose]
public section

/-! # Reducing indexed-to-CS inclusion to the finite normal-form core

The remaining constructive part of the inclusion `Indexed ⊆ CS` is the finite-alphabet,
finite-support, normal-form indexed grammar simulation. This file keeps the class-level
reduction explicit while the normal-form infrastructure is developed in the grammar modules.
-/

variable {T : Type}

/-- The LBA finite-normal-form core implies the context-sensitive finite-normal-form core. -/
public theorem finite_normalForm_CS_core_of_LBA_core
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) :
    ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language := by
  intro A _ _ _ g _ _ _ hNF
  exact is_LBA_pos_imp_isCS (hcore g hNF)

/-- If every finite-support normal-form indexed grammar over a finite inhabited alphabet is
context-sensitive, then every ε-free indexed language is context-sensitive. -/
public theorem is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_core [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed_noEpsilon L) : is_CS L := by
  obtain ⟨A, hA, hAdec, hAinh, f, g, hnt, hflag, hdec, hNF, hmap⟩ :=
    is_Indexed_noEpsilon_exists_fintype_normalForm_image (L := L) hL
  haveI := hA
  haveI := hAdec
  haveI := hAinh
  haveI := hnt
  haveI := hflag
  haveI := hdec
  have hCSg : is_CS g.Language := hcore g hNF
  have hImage : is_CS (g.Language.homomorphicImage fun a => [f a]) :=
    is_CS_homomorphicImage_epsfree g.Language (fun a => [f a]) (fun _ => by simp) hCSg
  rw [Language.homomorphicImage, Language.subst_singletons_eq_map] at hImage
  rwa [hmap] at hImage

/-- If the finite normal-form indexed grammars are recognized by bounded-tape LBAs, then every
ε-free indexed language is context-sensitive. -/
public theorem is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_LBA_core [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed_noEpsilon L) : is_CS L :=
  is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_core
    (finite_normalForm_CS_core_of_LBA_core hcore) hL

/-- Once epsilon elimination supplies an ε-free indexed witness for `L \ {ε}`, the existing
finite-normal-form core proves `L` context-sensitive. -/
public theorem is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_core [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hpart : is_Indexed_noEpsilon (L \ ({[]} : Set (List T)))) : is_CS L := by
  exact is_CS_of_diff_empty_of_is_CS
    (is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_core hcore hpart)

/-- LBA-core variant of
`is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_LBA_core
    [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hpart : is_Indexed_noEpsilon (L \ ({[]} : Set (List T)))) : is_CS L :=
  is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_core
    (finite_normalForm_CS_core_of_LBA_core hcore) hpart

/-- Epsilon elimination for indexed languages: the nonempty part of every indexed language has
an ε-free indexed grammar witness. -/
public theorem is_Indexed_noEpsilon_diff_empty {L : Language T}
    (hL : is_Indexed L) :
    is_Indexed_noEpsilon (L \ ({[]} : Set (List T))) := by
  obtain ⟨g, hg_lang⟩ := hL
  obtain ⟨g', hne', hlang'⟩ := g.exists_noEpsilon_preserving_nonempty
  refine ⟨g', hne', ?_⟩
  ext w
  by_cases hw : w = []
  · subst w
    constructor
    · intro hgen
      exact False.elim (g'.not_generates_nil_of_noEpsilon hne' hgen)
    · intro hwL
      exact False.elim (hwL.2 (by simp))
  · change g'.Generates w ↔ w ∈ L ∧ w ∉ ({[]} : Set (List T))
    rw [hlang' w hw]
    change w ∈ g.Language ↔ w ∈ L ∧ w ∉ ({[]} : Set (List T))
    rw [hg_lang]
    constructor
    · intro hgen
      exact ⟨hgen, by simpa [Set.mem_singleton_iff] using hw⟩
    · intro hmem
      exact hmem.1

private theorem is_CS_of_is_Indexed_of_finite_normalForm_core_of_inhabited [Inhabited T]
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L := by
  obtain ⟨A, hA, hAdec, hAinh, f, g, hnt, hflag, hdec, hNF, hmap⟩ :=
    is_Indexed_exists_fintype_normalForm_nonempty_image (L := L) hL
  haveI := hA
  haveI := hAdec
  haveI := hAinh
  haveI := hnt
  haveI := hflag
  haveI := hdec
  have hCSg : is_CS g.Language := hcore g hNF
  have hImage : is_CS (g.Language.homomorphicImage fun a => [f a]) :=
    is_CS_homomorphicImage_epsfree g.Language (fun a => [f a]) (fun _ => by simp) hCSg
  rw [Language.homomorphicImage, Language.subst_singletons_eq_map] at hImage
  rw [hmap] at hImage
  exact is_CS_of_diff_empty_of_is_CS hImage

/-- With epsilon elimination discharged, the remaining class-level indexed-to-CS reduction only
needs the finite normal-form core. No inhabitedness assumption on the terminal alphabet is needed:
over an empty alphabet every language is a subset of the singleton language `{ε}` and is finite. -/
public theorem is_CS_of_is_Indexed_of_finite_normalForm_core
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L := by
  classical
  rcases isEmpty_or_nonempty T with hT | hT
  · letI : Fintype T := ⟨∅, fun t => (hT.false t).elim⟩
    apply is_CS_of_finite_language
    refine (Set.finite_singleton ([] : List T)).subset ?_
    intro w _
    have hw : w = [] := by
      cases w with
      | nil => rfl
      | cons t _ => exact (hT.false t).elim
    simpa only [Set.mem_singleton_iff] using hw
  · letI : Inhabited T := ⟨Classical.choice hT⟩
    exact is_CS_of_is_Indexed_of_finite_normalForm_core_of_inhabited hcore hL

/-- The finite normal-form core, once supplied, gives the class-level inclusion
`Indexed ⊆ CS` over every terminal alphabet. -/
public theorem Indexed_subclass_CS_of_finite_normalForm_core
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) :
    (Indexed : Set (Language T)) ⊆ (CS : Set (Language T)) := by
  intro L hL
  exact is_CS_of_is_Indexed_of_finite_normalForm_core hcore hL

/-- LBA-core variant of `is_CS_of_is_Indexed_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_of_finite_normalForm_LBA_core
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_finite_normalForm_core
    (finite_normalForm_CS_core_of_LBA_core hcore) hL

/-- If ε-elimination is proved for terminal-isolated, flag-separated grammars, then every
indexed language has an ε-free indexed witness for its nonempty part. -/
public theorem is_Indexed_noEpsilon_diff_empty_of_structural_epsilon_elim
    (helim : ∀ g₀ : IndexedGrammar T,
      g₀.TerminalsIsolated → g₀.FlagsSeparated →
        ∃ g' : IndexedGrammar T,
          g'.NoEpsilon' ∧
          ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g₀.Generates w))
    {L : Language T} (hL : is_Indexed L) :
    is_Indexed_noEpsilon (L \ ({[]} : Set (List T))) := by
  obtain ⟨g, hg_lang⟩ := hL
  obtain ⟨g₀, hg₀_ti, hg₀_fs, _hg₀_fresh_of, hg₀_lang⟩ :=
    g.exists_terminalIsolated_flagsSeparated_all
  obtain ⟨g', hne', hlang'⟩ := helim g₀ hg₀_ti hg₀_fs
  refine ⟨g', hne', ?_⟩
  ext w
  by_cases hw : w = []
  · subst w
    constructor
    · intro hgen
      exact False.elim (g'.not_generates_nil_of_noEpsilon hne' hgen)
    · intro hwL
      exact False.elim (hwL.2 (by simp))
  · change g'.Generates w ↔ w ∈ L ∧ w ∉ ({[]} : Set (List T))
    rw [hlang' w hw, hg₀_lang w]
    change w ∈ g.Language ↔ w ∈ L ∧ w ∉ ({[]} : Set (List T))
    rw [hg_lang]
    constructor
    · intro hgen
      exact ⟨hgen, by simpa [Set.mem_singleton_iff] using hw⟩
    · intro hmem
      exact hmem.1

/-- Class-level reduction: arbitrary indexed languages reduce to the no-ε inclusion once the
epsilon-elimination theorem provides `L \ {ε}` as an ε-free indexed language. -/
public theorem is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_core [Inhabited T]
    (helim : ∀ {L : Language T}, is_Indexed L →
      is_Indexed_noEpsilon (L \ ({[]} : Set (List T))))
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_nonemptyPart_noEpsilon_of_finite_normalForm_core
    hcore (helim hL)

/-- LBA-core variant of
`is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_LBA_core [Inhabited T]
    (helim : ∀ {L : Language T}, is_Indexed L →
      is_Indexed_noEpsilon (L \ ({[]} : Set (List T))))
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_core
    helim (finite_normalForm_CS_core_of_LBA_core hcore) hL

/-- Class-level reduction using the structurally normalized ε-elimination target. -/
public theorem is_CS_of_is_Indexed_of_structural_epsilon_elim_of_finite_normalForm_core
    [Inhabited T]
    (helim : ∀ g₀ : IndexedGrammar T,
      g₀.TerminalsIsolated → g₀.FlagsSeparated →
        ∃ g' : IndexedGrammar T,
          g'.NoEpsilon' ∧
          ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g₀.Generates w))
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_CS g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_epsilon_elim_of_finite_normalForm_core
    (fun h => is_Indexed_noEpsilon_diff_empty_of_structural_epsilon_elim helim h)
    hcore hL

/-- LBA-core variant of
`is_CS_of_is_Indexed_of_structural_epsilon_elim_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_of_structural_epsilon_elim_of_finite_normalForm_LBA_core
    [Inhabited T]
    (helim : ∀ g₀ : IndexedGrammar T,
      g₀.TerminalsIsolated → g₀.FlagsSeparated →
        ∃ g' : IndexedGrammar T,
          g'.NoEpsilon' ∧
          ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g₀.Generates w))
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_structural_epsilon_elim_of_finite_normalForm_core
    helim (finite_normalForm_CS_core_of_LBA_core hcore) hL

/-- The completed Aho simulation supplies the finite normal-form LBA core used by the
class-level reduction. -/
public theorem finite_normalForm_indexed_language_is_LBA_pos
    {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) : is_LBA_pos g.Language :=
  IndexedGrammar.Aho.is_LBA_pos_language hNF

/-- Every indexed language is context-sensitive. -/
public theorem is_CS_of_is_Indexed {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_finite_normalForm_LBA_core
    finite_normalForm_indexed_language_is_LBA_pos hL

/-- Class-level capstone: the finite normal-form Aho LBA core, together with the preceding
finite-support normalization and empty-word reduction, places every indexed language in `CS`. -/
public theorem Indexed_subclass_CS :
    (Indexed : Set (Language T)) ⊆ (CS : Set (Language T)) := by
  intro L hL
  exact is_CS_of_is_Indexed hL
