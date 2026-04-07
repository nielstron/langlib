import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Classes.RecursivelyEnumerable.Closure.Reverse
import Langlib.Utilities.LanguageOperations
import Langlib.Utilities.ListUtils
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Basics.InclusionCS

/-! # Context-Free Closure Under Reversal

This file proves that context-free languages are closed under word reversal.

## Strategy

Instead of re-proving the derivation-reversal argument from scratch, we reuse
`grammar_language_reversal_grammar` (the unrestricted result) together with a
commutation lemma that shows reversing a CF grammar and then embedding it into
an unrestricted grammar gives the same result as embedding first and then reversing.

## Main declarations

- `reversal_CF_grammar`  — reverse the RHS of every CF rule
- `grammar_of_cfg_reversal_comm` — commutation with the CF→unrestricted embedding
- `CF_of_reverse_CF`
- `CF_of_reverse_CF_rev`
- `CF_reverse_iff_CF`
-/

variable {T : Type}

section reversal_defs

/-- Reverse the right-hand side of every rule in a context-free grammar. -/
def reversal_CF_grammar (g : CF_grammar T) : CF_grammar T :=
  CF_grammar.mk g.nt g.initial (List.map (
      fun r : g.nt × List (symbol T g.nt) => (r.fst, List.reverse r.snd)
    ) g.rules)

private lemma map_reverse_reverse_comp {nt : Type} (rules : List (nt × List (symbol T nt))) :
    List.map ((fun r => (r.1, r.2.reverse)) ∘ fun r => (r.1, r.2.reverse)) rules = rules := by
  induction rules with
  | nil => rfl
  | cons h t ih =>
    cases h
    simp [Function.comp, List.reverse_reverse, ih]

lemma dual_of_reversal_CF_grammar (g : CF_grammar T) :
    reversal_CF_grammar (reversal_CF_grammar g) = g := by
  cases g with
  | mk nt initial rules =>
    simp [reversal_CF_grammar, map_reverse_reverse_comp]

end reversal_defs

section commutation

/-- Reversing a CF grammar and then embedding it as an unrestricted grammar gives the
same grammar as embedding first and then applying the unrestricted reversal. -/
theorem grammar_of_cfg_reversal_comm (g : CF_grammar T) :
    grammar_of_cfg (reversal_CF_grammar g) = reversal_grammar (grammar_of_cfg g) := by
  cases g with
  | mk nt initial rules =>
    simp only [reversal_CF_grammar, grammar_of_cfg, reversal_grammar]
    congr 1
    rw [List.map_map, List.map_map]
    congr 1

end commutation

section closure

/-- The class of context-free languages is closed under reversal. -/
theorem CF_of_reverse_CF (L : Language T) :
    is_CF L → is_CF (L.reverse) := by
  rintro ⟨g, hgL⟩
  refine ⟨reversal_CF_grammar g, ?_⟩
  rw [CF_language_eq_grammar_language, grammar_of_cfg_reversal_comm,
      grammar_language_reversal_grammar, ← CF_language_eq_grammar_language, hgL]

/-- The converse direction of `CF_of_reverse_CF`, using that reversal is an involution. -/
theorem CF_of_reverse_CF_rev (L : Language T) :
    is_CF (L.reverse) → is_CF L := by
  intro h
  have h' := CF_of_reverse_CF L.reverse h
  simpa using h'

/-- A language is context-free iff its reversal is context-free. -/
@[simp] theorem CF_reverse_iff_CF (L : Language T) :
    is_CF (L.reverse) ↔ is_CF L := by
  constructor
  · exact CF_of_reverse_CF_rev L
  · exact CF_of_reverse_CF L

end closure
