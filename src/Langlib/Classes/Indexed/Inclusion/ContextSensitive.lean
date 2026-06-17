import Langlib.Classes.ContextSensitive.Definition
import Langlib.Classes.Indexed.Definition
import Langlib.Grammars.Indexed.NormalForm.NormalForm

/-! # Indexed Languages and the Current Context-Sensitive Predicate

This file records the empty-word boundary that matters for the indexed-to-CSL
development.  The repository's current `CS` predicate uses the strictly
noncontracting grammar convention, so no `is_CS` language contains `[]`.
Unrestricted indexed grammars can generate `[]`.
-/

open Relation

variable {T : Type}

namespace IndexedGrammar

/-- The indexed grammar with one ε-production from the start symbol. -/
def emptyWordGrammar (T : Type) : IndexedGrammar T where
  nt := PUnit
  flag := Empty
  initial := PUnit.unit
  rules := [{ lhs := PUnit.unit, consume := none, rhs := [] }]

theorem emptyWordGrammar_generates_nil :
    (emptyWordGrammar T).Generates [] := by
  unfold Generates Derives Transforms emptyWordGrammar expandRhs
  exact ReflTransGen.single
    ⟨⟨PUnit.unit, none, []⟩, [], [], [], by simp, by simp, by simp⟩

end IndexedGrammar

/-- Indexed grammars can generate the empty word. -/
theorem exists_indexed_language_mem_nil :
    ∃ L : Language T, is_Indexed L ∧ [] ∈ L := by
  refine ⟨(IndexedGrammar.emptyWordGrammar T).Language, ?_, ?_⟩
  · exact ⟨IndexedGrammar.emptyWordGrammar T, rfl⟩
  · exact IndexedGrammar.emptyWordGrammar_generates_nil

/--
An ε-free indexed witness can be replaced by a normal-form indexed grammar
that recognizes the same nonempty part of the language.
-/
theorem exists_normalForm_of_is_Indexed_noEpsilon [Inhabited T]
    {L : Language T} (hL : is_Indexed_noEpsilon L) :
    ∃ g' : IndexedGrammar T,
      (∃ _ : DecidableEq g'.nt, g'.IsNormalForm) ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ w ∈ L) := by
  rcases hL with ⟨g, hne, hgL⟩
  obtain ⟨g', hnf, hlang⟩ := IndexedGrammar.exists_normalForm g hne
  refine ⟨g', hnf, ?_⟩
  intro w hw
  have hmem : g.Generates w ↔ w ∈ L := by
    change w ∈ g.Language ↔ w ∈ L
    rw [hgL]
  exact (hlang w hw).trans hmem

theorem withoutEpsilon_eq_self_of_is_Indexed_noEpsilon
    {L : Language T} (hL : is_Indexed_noEpsilon L) :
    withoutEpsilon L = L := by
  rcases hL with ⟨g, hne, hgL⟩
  ext w
  constructor
  · intro hw
    exact hw.1
  · intro hw
    refine ⟨hw, ?_⟩
    intro hnil
    subst w
    have hgen : g.Generates [] := by
      change [] ∈ g.Language
      rw [hgL]
      exact hw
    exact IndexedGrammar.not_generates_nil_of_noEpsilon g hne hgen

/--
With the repository's current `CS` definition, the literal inclusion
`Indexed ⊆ CS` is false because `CS` excludes `[]`.
-/
theorem not_Indexed_subclass_CS : ¬ ((Indexed : Set (Language T)) ⊆ CS) := by
  intro hsub
  let L : Language T := (IndexedGrammar.emptyWordGrammar T).Language
  have hIndexed : L ∈ (Indexed : Set (Language T)) :=
    ⟨IndexedGrammar.emptyWordGrammar T, rfl⟩
  have hCS : is_CS L := hsub hIndexed
  exact nil_not_mem_of_is_CS hCS IndexedGrammar.emptyWordGrammar_generates_nil
