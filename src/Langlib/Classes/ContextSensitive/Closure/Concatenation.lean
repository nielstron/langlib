import Langlib.Classes.ContextSensitive.Basics.Inclusion
import Langlib.Grammars.ContextSensitive.UnrestrictedCharacterization
import Langlib.Classes.RecursivelyEnumerable.Closure.Concatenation

/-! # Context-Sensitive Concatenation Construction

This file sketches a concatenation construction for context-sensitive languages by reusing the unrestricted one.

## Main declarations

- `bonus_CS_of_CS_c_CS`
-/

variable {T : Type}


private def wrap_CS_rule₁ {N₁ : Type} (N₂ : Type) (r : csrule T N₁) :
  csrule T (nnn T N₁ N₂) :=
csrule.mk
  (List.map (wrap_symbol₁ N₂) r.context_left)
  (Sum.inl (some (Sum.inl r.input_nonterminal)))
  (List.map (wrap_symbol₁ N₂) r.context_right)
  (List.map (wrap_symbol₁ N₂) r.output_string)

private def wrap_CS_rule₂ {N₂ : Type} (N₁ : Type) (r : csrule T N₂) :
  csrule T (nnn T N₁ N₂) :=
csrule.mk
  (List.map (wrap_symbol₂ N₁) r.context_left)
  (Sum.inl (some (Sum.inr r.input_nonterminal)))
  (List.map (wrap_symbol₂ N₁) r.context_right)
  (List.map (wrap_symbol₂ N₁) r.output_string)

private def CS_rules_for_terminals₁ (N₂ : Type) (g : CS_grammar T) :
  List (csrule T (nnn T g.nt N₂)) :=
List.map (fun t => csrule.mk [] (Sum.inr (Sum.inl t)) [] [symbol.terminal t])
  (all_used_terminals (grammar_of_csg g))

private def CS_rules_for_terminals₂ (N₁ : Type) (g : CS_grammar T) :
  List (csrule T (nnn T N₁ g.nt)) :=
List.map (fun t => csrule.mk [] (Sum.inr (Sum.inr t)) [] [symbol.terminal t])
  (all_used_terminals (grammar_of_csg g))

private def big_CS_grammar (g₁ g₂ : CS_grammar T) : CS_grammar T where
  nt := nnn T g₁.nt g₂.nt
  initial := Sum.inl none
  rules :=
    (csrule.mk [] (Sum.inl none) [] [
      symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
      symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))]
    ) :: (
      (List.map (wrap_CS_rule₁ g₂.nt) g₁.rules ++ List.map (wrap_CS_rule₂ g₁.nt) g₂.rules) ++
      (CS_rules_for_terminals₁ g₂.nt g₁ ++ CS_rules_for_terminals₂ g₁.nt g₂)
    )
  output_nonempty := by
    intro r hr
    simp [List.mem_cons] at hr
    rcases hr with rfl | hr
    · nofun
    · rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩ | hr | hr
      · -- wrap_CS_rule₁
        simp [wrap_CS_rule₁, csrule.output_string]
        exact g₁.output_nonempty r' hr'
      · -- wrap_CS_rule₂
        simp [wrap_CS_rule₂, csrule.output_string]
        exact g₂.output_nonempty r' hr'
      · -- CS_rules_for_terminals₁
        simp [CS_rules_for_terminals₁, List.mem_map] at hr
        obtain ⟨t, _, rfl⟩ := hr
        simp
      · -- CS_rules_for_terminals₂
        simp [CS_rules_for_terminals₂, List.mem_map] at hr
        obtain ⟨t, _, rfl⟩ := hr
        simp

/-
PROVIDED SOLUTION
Rewrite using CS_language_eq_grammar_language to get grammar_language (grammar_of_csg (big_CS_grammar g₁ g₂)) = grammar_language (big_grammar (grammar_of_csg g₁) (grammar_of_csg g₂)).

Then show that grammar_of_csg (big_CS_grammar g₁ g₂) = big_grammar (grammar_of_csg g₁) (grammar_of_csg g₂).

This is a definitional equality: both grammars have:
- Same nt type: nnn T g₁.nt g₂.nt
- Same initial: Sum.inl none
- Same rules (need to show the rule lists are equal)

For the rules, unfold everything (grammar_of_csg, big_CS_grammar, big_grammar, wrap_CS_rule₁, wrap_CS_rule₂, CS_rules_for_terminals₁, CS_rules_for_terminals₂, wrap_grule₁, wrap_grule₂, rules_for_terminals₁, rules_for_terminals₂) and use:
- List.map_map to compose functions
- List.map_append for map over concatenation
- ext/funext to show the composed functions are equal elementwise
- For each csrule r, grammar_of_csg maps it to grule with output_string = r.context_left ++ r.output_string ++ r.context_right. Then wrap_grule₁ maps this grule by mapping wrap_symbol₁ over everything, giving output = map wrap₁ (r.context_left ++ r.output_string ++ r.context_right) = map wrap₁ r.context_left ++ map wrap₁ r.output_string ++ map wrap₁ r.context_right. On the other side, wrap_CS_rule₁ maps the csrule first by wrapping, then grammar_of_csg maps the result giving output = map wrap₁ r.context_left ++ map wrap₁ r.output_string ++ map wrap₁ r.context_right. So they're equal.

For terminal rules: CS_rules_for_terminals₁ uses all_used_terminals (grammar_of_csg g₁), and rules_for_terminals₁ also uses all_used_terminals. The CS terminal rules have context_left = [], context_right = [], output_string = [terminal t]. After grammar_of_csg, they become grule.mk [] (Sum.inr (Sum.inl t)) [] ([] ++ [terminal t] ++ []) = grule.mk [] ... [] [terminal t]. This matches rules_for_terminals₁.

So unfold everything and use `congr`, `ext`, `simp [List.map_append, List.map_map]`, and `rfl`.
-/
private lemma big_CS_grammar_same_language (g₁ g₂ : CS_grammar T) :
  CS_language (big_CS_grammar g₁ g₂) = grammar_language (big_grammar (grammar_of_csg g₁) (grammar_of_csg g₂)) :=
by
  convert CS_language_eq_grammar_language ( big_CS_grammar g₁ g₂ ) using 2;
  unfold grammar_of_csg big_grammar big_CS_grammar;
  unfold CS_rules_for_terminals₁ CS_rules_for_terminals₂; simp +decide [ List.map_append, List.map_map ] ;
  congr! 2;
  · ext; simp +decide [ wrap_CS_rule₁ ] ;
    exact congr_arg₂ _ ( by aesop ) ( by aesop );
  · unfold wrap_CS_rule₂; simp +decide [ List.map_append, List.map_map ] ;
    intros; congr! 1;
    rw [ ← List.map_append, ← List.map_append ];
    rfl

theorem CS_of_CS_c_CS (L₁ : Language T) (L₂ : Language T) :
  is_CS L₁  ∧  is_CS L₂   →   is_CS (L₁ * L₂)   :=
by
  rintro ⟨h₁, h₂⟩
  obtain ⟨g₁, eq_L₁⟩ := is_CS_implies_is_CS_via_csg h₁
  obtain ⟨g₂, eq_L₂⟩ := is_CS_implies_is_CS_via_csg h₂
  rw [CS_language_eq_grammar_language g₁] at eq_L₁
  rw [CS_language_eq_grammar_language g₂] at eq_L₂

  apply is_CS_via_csg_implies_is_CS
  use big_CS_grammar g₁ g₂
  rw [big_CS_grammar_same_language]

  apply Set.Subset.antisymm
  ·
    intros w hyp
    rw [←eq_L₁]
    rw [←eq_L₂]
    exact in_concatenated_of_in_big hyp
  ·
    intros w hyp
    rw [←eq_L₁] at hyp
    rw [←eq_L₂] at hyp
    exact in_big_of_in_concatenated hyp
