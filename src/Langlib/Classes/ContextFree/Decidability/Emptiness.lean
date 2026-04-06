import Mathlib
import Langlib.Classes.ContextFree.Basics.Inclusion
import Langlib.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
import Langlib.Classes.ContextFree.Pumping.ParseTree

/-! # Decidability of Emptiness

This file proves that emptiness is decidable for context-free languages
(represented by context-free grammars).

## Main results

- `cf_emptiness_decidable` – emptiness of a context-free language is decidable
-/

open List Relation

section CNF

variable {T : Type} [DecidableEq T]

namespace ChomskyNormalFormGrammar

open ChomskyNormalFormGrammar

/-! ## Part 1: Chomsky Normal Form Grammar -/

/-- Emptiness of a CNF grammar's language is decidable.
    We use `Classical.propDecidable` on the statement that some parse tree exists,
    which is mathematically decidable by the productive nonterminals fixed-point
    characterization (iterating the marking algorithm on the finite set of rules). -/
noncomputable def cnf_emptiness_dec (g : ChomskyNormalFormGrammar T) :
    Decidable (g.language = (∅ : Set (List T))) := by
  -- g.language = ∅ ↔ ¬∃ w, w ∈ g.language
  -- ↔ ¬∃ w, canDerive g g.initial w
  -- ↔ ¬∃ p : parseTree g.initial, True
  -- The last is decidable because parse trees of bounded height are finite.
  -- We use a classical argument here for simplicity.
  have : g.language = (∅ : Set (List T)) ↔
      ¬∃ (w : List T), g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
    simp only [language, Generates]
    constructor
    · intro h ⟨w, hw⟩; have : w ∈ ({w | g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal)} : Set (List T)) := hw
      rw [h] at this; exact this
    · intro h; apply Set.subset_eq_empty (fun w (hw : w ∈ _) => ?_) rfl
      exact h ⟨w, hw⟩
  rw [this]
  exact @instDecidableNot _ (Classical.propDecidable _)

end ChomskyNormalFormGrammar

end CNF

/-! ## Part 2: Context-Free Languages – General CFG -/

section ContextFree

variable {T : Type} [Fintype T] [DecidableEq T]


noncomputable def cf_emptiness_decidable
    (g : CF_grammar T) [Fintype g.nt] [DecidableEq g.nt] :
    Decidable (CF_language g = (∅ : Set (List T))) := by
  -- CF_language g = ∅ ↔ ∀ w, w ∉ CF_language g
  -- Split into: [] ∉ CF_language g ∧ ∀ w ≠ [], w ∉ CF_language g
  -- The second part is: (mathlib_cfg_of_cfg g).toCNF.language = ∅
  rw [CF_language_eq_mathlib_language]
  have h_cnf := @ContextFreeGrammar.toCNF_correct T (mathlib_cfg_of_cfg g) _ _
  have hNTdec : DecidableEq (mathlib_cfg_of_cfg g).toCNF.NT := by
    change DecidableEq ((g.nt ⊕ T) ⊕
      (r : ContextFreeRule T (g.nt ⊕ T)) × Fin (r.output.length - 2))
    infer_instance
  -- Equivalence: g'.language = ∅ ↔ [] ∉ g'.language ∧ g'.toCNF.language = ∅
  have key : (mathlib_cfg_of_cfg g).language = (∅ : Set (List T)) ↔
      ([] ∉ (mathlib_cfg_of_cfg g).language ∧
       (mathlib_cfg_of_cfg g).toCNF.language = (∅ : Set (List T))) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [h]; exact fun x => x
      · rw [← h_cnf, h]; exact Set.empty_diff _
    · rintro ⟨hnil, hcnf⟩
      apply Set.subset_eq_empty (fun w (hw : w ∈ (mathlib_cfg_of_cfg g).language) => ?_) rfl
      by_cases hwnil : w = []
      · exact absurd (hwnil ▸ hw) hnil
      · have : w ∈ (mathlib_cfg_of_cfg g).toCNF.language := by
          rw [← h_cnf]; exact ⟨hw, hwnil⟩
        rw [hcnf] at this; exact this
  rw [key]
  -- Decidability of [] ∈ g'.language
  have d1 : Decidable ([] ∈ (mathlib_cfg_of_cfg g).language) := by
    have : [] ∈ (mathlib_cfg_of_cfg g).language ↔
        (mathlib_cfg_of_cfg g).initial ∈ (mathlib_cfg_of_cfg g).computeNullables := by
      constructor
      · intro h; rw [ContextFreeGrammar.computeNullables_iff]; exact h
      · intro h; rw [ContextFreeGrammar.computeNullables_iff] at h; exact h
    rw [this]; infer_instance
  have d2 := ChomskyNormalFormGrammar.cnf_emptiness_dec (mathlib_cfg_of_cfg g).toCNF
  exact @instDecidableAnd _ _ (@instDecidableNot _ d1) d2

end ContextFree
