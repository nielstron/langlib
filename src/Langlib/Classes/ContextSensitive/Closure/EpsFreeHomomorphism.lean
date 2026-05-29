module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.RecursivelyEnumerable.Closure.Homomorphism
import Langlib.Grammars.ContextSensitive.UnrestrictedCharacterization

/-! # Context-Sensitive Closure Under ε-Free Homomorphism

This file proves that context-sensitive languages, with the current non-contracting
definition, are closed under string homomorphisms that do not erase symbols.

Proof idea: reuse the unrestricted homomorphism grammar, but build it as a
context-sensitive grammar. Original CS rules are lifted unchanged, and each
terminal marker for `a` expands to the nonempty word `h a`; the ε-free hypothesis
is exactly what keeps these expansion rules non-contracting.
-/

variable {α β : Type}

private def epsfreeHomLiftCSRule {N : Type} (r : csrule α N) : csrule β (N ⊕ α) :=
  csrule.mk (homLiftStr r.context_left) (Sum.inl r.input_nonterminal)
    (homLiftStr r.context_right) (homLiftStr r.output_string)

private def epsfreeHomExpandCSRule {N : Type} (h : α → List β) (a : α) :
    csrule β (N ⊕ α) :=
  csrule.mk [] (Sum.inr a) [] ((h a).map symbol.terminal)

private def epsfreeHomCSGrammar (g : CS_grammar α) (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) : CS_grammar β where
  nt := g.nt ⊕ α
  initial := Sum.inl g.initial
  rules :=
    g.rules.map epsfreeHomLiftCSRule ++
      (all_used_terminals (grammar_of_csg g)).map (epsfreeHomExpandCSRule h)
  output_nonempty := by
    intro r hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      simp [epsfreeHomLiftCSRule, homLiftStr]
      exact g.output_nonempty r₀ hr₀
    · obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hr
      simp [epsfreeHomExpandCSRule]
      exact heps a

private theorem grammar_of_csg_epsfreeHom_comm (g : CS_grammar α) (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) :
    grammar_of_csg (epsfreeHomCSGrammar g h heps) = hom_grammar (grammar_of_csg g) h := by
  unfold grammar_of_csg epsfreeHomCSGrammar hom_grammar epsfreeHomLiftCSRule
    epsfreeHomExpandCSRule homLiftRule homExpandRule homLiftStr
  simp [grammar_of_csg, List.map_map, List.map_append, List.append_assoc, Function.comp_def]

private theorem epsfreeHomCSGrammar_language (g : CS_grammar α) (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) :
    CS_language (epsfreeHomCSGrammar g h heps) =
      (CS_language g).homomorphicImage h := by
  rw [CS_language_eq_grammar_language, grammar_of_csg_epsfreeHom_comm,
    hom_grammar_language_epsfree (grammar_of_csg g) h heps, CS_language_eq_grammar_language]

/-- Context-sensitive languages are closed under ε-free string homomorphism. -/
public theorem CS_closedUnderEpsFreeHomomorphism :
    ClosedUnderEpsFreeHomomorphism is_CS := by
  intro α β _ _ L h heps hL
  obtain ⟨g, hgL⟩ := is_CS_implies_is_CS_via_csg hL
  exact is_CS_via_csg_implies_is_CS
    ⟨epsfreeHomCSGrammar g h heps, by rw [epsfreeHomCSGrammar_language, hgL]⟩
