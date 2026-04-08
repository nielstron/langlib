import Langlib.Grammars.ContextSensitive.Toolbox
import Langlib.Classes.ContextSensitive.Basics.Inclusion
import Langlib.Grammars.ContextSensitive.UnrestrictedCharacterization
import Langlib.Classes.RecursivelyEnumerable.Closure.Reverse
import Langlib.Utilities.LanguageOperations
import Langlib.Utilities.ListUtils

/-! # Context-Sensitive Closure Under Reversal

This file proves that context-sensitive languages are closed under word reversal.

## Strategy

We reuse `grammar_language_reversal_grammar` (the unrestricted result) together with
a commutation lemma showing that reversing a CS grammar and embedding it as an
unrestricted grammar gives the same result as embedding first and then reversing.

## Main declarations

- `reversal_csrule`     — reverse a single CS rule
- `reversal_CS_grammar` — reverse every rule of a CS grammar
- `grammar_of_csg_reversal_comm` — commutation with the CS→unrestricted embedding
- `CS_of_reverse_CS`
- `CS_of_reverse_CS_rev`
- `CS_reverse_iff_CS`
-/

variable {T : Type}

section reversal_defs

/-- Reverse a single context-sensitive rule: swap and reverse the contexts, reverse the
output string. -/
def reversal_csrule {N : Type} (r : csrule T N) : csrule T N :=
  csrule.mk r.context_right.reverse r.input_nonterminal r.context_left.reverse r.output_string.reverse

private lemma dual_of_reversal_csrule {N : Type} (r : csrule T N) :
    reversal_csrule (reversal_csrule r) = r := by
  cases r
  unfold reversal_csrule
  simp [List.reverse_reverse]

private lemma reversal_csrule_reversal_csrule {N : Type} :
    @reversal_csrule T N ∘ @reversal_csrule T N = id := by
  ext; apply dual_of_reversal_csrule

/-- Reverse every rule of a context-sensitive grammar. -/
def reversal_CS_grammar (g : CS_grammar T) : CS_grammar T :=
  CS_grammar.mk g.nt g.initial (List.map reversal_csrule g.rules)
  ( by
  intros r rh
  have x := g.output_nonempty
  simp only [List.mem_map] at rh
  rcases rh with ⟨a, ha_rules, ha_eq⟩
  unfold reversal_csrule at ha_eq
  simp only [ha_eq.symm, ne_eq, List.reverse_eq_nil_iff]
  exact g.output_nonempty a ha_rules
  )

lemma dual_of_reversal_CS_grammar (g : CS_grammar T) :
    reversal_CS_grammar (reversal_CS_grammar g) = g := by
  cases g
  unfold reversal_CS_grammar
  simp [List.map_map, reversal_csrule_reversal_csrule]

end reversal_defs

section commutation

/-- Reversing a CS grammar and then embedding it as an unrestricted grammar gives the
same grammar as embedding first and then applying the unrestricted reversal. -/
theorem grammar_of_csg_reversal_comm (g : CS_grammar T) :
    grammar_of_csg (reversal_CS_grammar g) = reversal_grammar (grammar_of_csg g) := by
  cases g with
  | mk nt initial rules =>
    simp only [reversal_CS_grammar, grammar_of_csg, reversal_grammar]
    congr 1
    rw [List.map_map, List.map_map]
    congr 1
    ext r
    simp [reversal_grule, reversal_csrule, List.reverse_append]

end commutation

section closure

/-- The class of context-sensitive languages is closed under reversal. -/
theorem CS_of_reverse_CS (L : Language T) :
    is_CS L → is_CS (L.reverse) := by
  intro h
  obtain ⟨g, hgL⟩ := is_CS_implies_is_CS_via_csg h
  apply is_CS_via_csg_implies_is_CS
  refine ⟨reversal_CS_grammar g, ?_⟩
  rw [CS_language_eq_grammar_language, grammar_of_csg_reversal_comm,
      grammar_language_reversal_grammar, ← CS_language_eq_grammar_language, hgL]

/-- The converse direction: if the reversal is CS then so is the original. -/
theorem CS_of_reverse_CS_rev (L : Language T) :
    is_CS (L.reverse) → is_CS L := by
  intro h
  have h' := CS_of_reverse_CS L.reverse h
  simpa using h'

/-- A language is context-sensitive iff its reversal is. -/
@[simp] theorem CS_reverse_iff_CS (L : Language T) :
    is_CS (L.reverse) ↔ is_CS L := by
  constructor
  · exact CS_of_reverse_CS_rev L
  · exact CS_of_reverse_CS L

end closure
