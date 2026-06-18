module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
public import Langlib.Classes.Indexed.Basics.FiniteSupport
@[expose]
public section

/-! # Reducing indexed-to-CS inclusion to the finite normal-form core

The remaining constructive part of the inclusion `Indexed ⊆ CS` is the finite-alphabet,
finite-support, normal-form indexed grammar simulation. This file packages the class-level
reduction to that core statement.
-/

variable {T : Type}

/-- The finite normal-form core statement needed for the ε-free indexed-to-CS inclusion. -/
public def IndexedFiniteNormalFormSubsetCS : Prop :=
  ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
    g.IsNormalForm → is_CS g.Language

/-- The automata-level finite normal-form core: every finite-support normal-form indexed
grammar over a finite inhabited alphabet is recognized by the ε-free bounded-tape LBA model. -/
public def IndexedFiniteNormalFormSubsetLBA : Prop :=
  ∀ {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    (g : IndexedGrammar A) [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt],
    g.IsNormalForm → is_LBA_pos g.Language

/-- The LBA finite-normal-form core implies the context-sensitive finite-normal-form core. -/
public theorem finite_normalForm_CS_core_of_LBA_core
    (hcore : IndexedFiniteNormalFormSubsetLBA) :
    IndexedFiniteNormalFormSubsetCS := by
  intro A _ _ _ g _ _ _ hNF
  exact is_LBA_pos_imp_isCS (hcore g hNF)

/-- If every finite-support normal-form indexed grammar over a finite inhabited alphabet is
context-sensitive, then every ε-free indexed language is context-sensitive. -/
public theorem is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_core [Inhabited T]
    (hcore : IndexedFiniteNormalFormSubsetCS) {L : Language T}
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
    (hcore : IndexedFiniteNormalFormSubsetLBA) {L : Language T}
    (hL : is_Indexed_noEpsilon L) : is_CS L :=
  is_CS_of_is_Indexed_noEpsilon_of_finite_normalForm_core
    (finite_normalForm_CS_core_of_LBA_core hcore) hL
