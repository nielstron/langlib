module

public import Langlib.Classes.Indexed.Basics.Elementary
public import Langlib.Classes.Indexed.Basics.FiniteAlphabet
public import Langlib.Classes.Indexed.Definition
public import Langlib.Grammars.Indexed.Basics.FiniteSupport
public import Langlib.Grammars.Indexed.NormalForm.NormalForm
@[expose]
public section

/-! # Finite-support witnesses for indexed languages

Every indexed language has an indexed-grammar witness whose nonterminal and flag types are
finite. This packages the grammar-level finite-support restriction for class-level use.
-/

variable {T : Type}

/-- Every indexed language has a grammar witness with finite nonterminal and flag types. -/
public theorem is_Indexed_exists_finiteSupport_grammar {L : Language T}
    (hL : is_Indexed L) :
    ∃ g : IndexedGrammar T, ∃ _ : Fintype g.nt, ∃ _ : Fintype g.flag,
      g.Language = L := by
  obtain ⟨g, hlang⟩ := hL
  obtain ⟨g', hnt, hflag, hlang'⟩ := g.exists_finiteSupport
  exact ⟨g', hnt, hflag, hlang'.trans hlang⟩

/-- Indexed languages are unchanged if their witnesses are required to use finite
nonterminal and flag types. -/
public theorem is_Indexed_iff_exists_finiteSupport_grammar {L : Language T} :
    is_Indexed L ↔
      ∃ g : IndexedGrammar T, ∃ _ : Fintype g.nt, ∃ _ : Fintype g.flag,
        g.Language = L := by
  constructor
  · exact is_Indexed_exists_finiteSupport_grammar
  · rintro ⟨g, _, _, hlang⟩
    exact ⟨g, hlang⟩

/-- ε-free indexed languages have finite-support normal-form grammar witnesses. -/
public theorem is_Indexed_noEpsilon_exists_finiteSupport_normalForm [Inhabited T]
    {L : Language T} (hL : is_Indexed_noEpsilon L) :
    ∃ g : IndexedGrammar T, ∃ _ : Fintype g.nt, ∃ _ : Fintype g.flag,
      ∃ _ : DecidableEq g.nt, g.IsNormalForm ∧ g.Language = L := by
  obtain ⟨g, hne, hlang⟩ := hL
  obtain ⟨g', hnt, hflag, hdec, hNF, hgen⟩ := g.exists_finiteSupport_normalForm hne
  refine ⟨g', hnt, hflag, hdec, hNF, ?_⟩
  ext w
  by_cases hw : w = []
  · subst w
    change g'.Generates [] ↔ [] ∈ L
    constructor
    · intro hnil
      haveI := hdec
      exact False.elim ((g'.not_generates_nil_of_noEpsilon
        (g'.noEpsilon_of_isNormalForm hNF)) hnil)
    · intro hnil
      have hgnil : g.Generates [] := by
        change [] ∈ g.Language
        rw [hlang]
        exact hnil
      exact False.elim ((g.not_generates_nil_of_noEpsilon hne) hgnil)
  · change g'.Generates w ↔ w ∈ L
    rw [hgen w hw]
    rw [← hlang]
    rfl

/-- Every ε-free indexed language is the image of a finite-alphabet, finite-support,
normal-form indexed grammar.

This packages all reductions needed before the final indexed-to-CS simulation: the terminal
alphabet, nonterminal type, and flag type are finite, the terminal alphabet is inhabited, and
the grammar is in indexed normal form. -/
public theorem is_Indexed_noEpsilon_exists_fintype_normalForm_image [Inhabited T]
    {L : Language T} (hL : is_Indexed_noEpsilon L) :
    ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (_ : Inhabited A)
      (f : A → T) (g : IndexedGrammar A),
      ∃ _ : Fintype g.nt, ∃ _ : Fintype g.flag, ∃ _ : DecidableEq g.nt,
        g.IsNormalForm ∧ Language.map f g.Language = L := by
  classical
  obtain ⟨S, L', hL', hmap⟩ :=
    is_Indexed_noEpsilon_exists_finiteAlphabet_Indexed_noEpsilon_image (L := L) hL
  by_cases hS : Nonempty {t : T // t ∈ S}
  · haveI : Inhabited {t : T // t ∈ S} := ⟨Classical.choice hS⟩
    obtain ⟨g, hnt, hflag, hdec, hNF, hlang⟩ :=
      is_Indexed_noEpsilon_exists_finiteSupport_normalForm (L := L') hL'
    refine ⟨{t : T // t ∈ S}, inferInstance, inferInstance, inferInstance,
      (fun t => t.1), g, hnt, hflag, hdec, hNF, ?_⟩
    rw [hlang]
    exact hmap
  · have hL'_empty : L' = (0 : Language {t : T // t ∈ S}) := by
      ext w
      constructor
      · intro hw
        obtain ⟨g, hne, hlang⟩ := hL'
        have hwg : w ∈ g.Language := by
          rw [hlang]
          exact hw
        cases w with
        | nil =>
            exact False.elim ((g.not_generates_nil_of_noEpsilon hne) hwg)
        | cons a rest =>
            exact False.elim (hS ⟨a⟩)
      · intro h
        cases h
    have hL_empty : L = (0 : Language T) := by
      rw [← hmap, hL'_empty]
      ext w
      constructor
      · rintro ⟨u, hu, hwu⟩
        cases hu
      · intro h
        cases h
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, (fun _ => default),
      IndexedGrammar.emptyGrammar PUnit, inferInstance, inferInstance,
      IndexedGrammar.emptyGrammar_nt_decidableEq PUnit,
      IndexedGrammar.emptyGrammar_isNormalForm PUnit, ?_⟩
    rw [IndexedGrammar.emptyGrammar_language, hL_empty]
    ext w
    constructor
    · rintro ⟨u, hu, hwu⟩
      cases hu
    · intro h
      cases h

end
