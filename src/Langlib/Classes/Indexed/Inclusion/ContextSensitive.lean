module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
public import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
public import Langlib.Classes.Indexed.Basics.FiniteSupport
public import Langlib.Grammars.Indexed.NormalForm.BoundedStackGrammar
public import Langlib.Grammars.Indexed.NormalForm.Shrinking
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

/-- Every fixed bounded-stack slice of a finite normal-form indexed grammar is recognized by
the bounded-tape LBA model, via the existing Kuroda construction for finite noncontracting
grammars. -/
public theorem is_LBA_pos_boundedStackGrammar_language_of_isNormalForm
    {A : Type} [Fintype A] [DecidableEq A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (B : ℕ) :
    is_LBA_pos (grammar_language (IndexedGrammar.boundedStackGrammar g B)) := by
  classical
  haveI : Fintype (IndexedGrammar.BoundedStackNT g B) :=
    IndexedGrammar.boundedStackNTFintype (g := g) B
  have hfin : Finite (IndexedGrammar.boundedStackGrammar g B).nt := by
    change Finite (IndexedGrammar.BoundedStackNT g B)
    exact Finite.of_fintype _
  exact KurodaConstruction.noncontracting_finite_to_LBA
    (IndexedGrammar.boundedStackGrammar g B) hfin
    (IndexedGrammar.boundedStackGrammar_noncontracting hNF)

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
