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

/-- LBA-core variant of `is_CS_of_is_Indexed_of_finite_normalForm_core`. -/
public theorem is_CS_of_is_Indexed_of_finite_normalForm_LBA_core
    (hcore : ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
      (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
      g.IsNormalForm → is_LBA_pos g.Language) {L : Language T}
    (hL : is_Indexed L) : is_CS L :=
  is_CS_of_is_Indexed_of_finite_normalForm_core
    (finite_normalForm_CS_core_of_LBA_core hcore) hL

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
