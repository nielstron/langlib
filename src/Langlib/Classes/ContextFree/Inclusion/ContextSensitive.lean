import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextSensitive.Definition
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Langlib.Grammars.ContextSensitive.UnrestrictedCharacterization
import Mathlib.Computability.ContextFreeGrammar

/-! # Context-Free Inclusions

This file relates the project's context-free grammars to context-sensitive, unrestricted, and mathlib formulations.

## Main declarations

- `CF_subclass_CS`
- `CF_subclass_RE`
- `is_CF_iff_isContextFree`
-/

variable {T : Type}


/-- A context-free grammar has no ε-productions (every rule has a non-empty right-hand side). -/
def CF_no_epsilon' (g : CF_grammar T) : Prop :=
  ∀ r ∈ g.rules, r.snd ≠ []

/-- Convert a context-free grammar without ε-productions to a context-sensitive grammar.
    The CS rules have empty context (α = β = []) and γ = rule output. -/
def csg_of_cfg (g : CF_grammar T) (hne : CF_no_epsilon' g) : CS_grammar T where
  nt := g.nt
  initial := g.initial
  rules := List.map (fun r : g.nt × (List (symbol T g.nt)) =>
    csrule.mk [] r.fst [] r.snd) g.rules
  output_nonempty := by
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    exact hne r₀ hr₀

lemma grammar_of_cfg_well_defined (g : CF_grammar T) (hne : CF_no_epsilon' g) :
  grammar_of_csg (csg_of_cfg g hne) = grammar_of_cfg g :=
by
  cases g with
  | mk nt initial rules =>
    simp [grammar_of_csg, csg_of_cfg, grammar_of_cfg, List.map_map, List.append_nil]

lemma CF_language_eq_CS_language (g : CF_grammar T) (hne : CF_no_epsilon' g) :
  CF_language g = CS_language (csg_of_cfg g hne) :=
by
  unfold CF_language
  unfold CS_language
  ext1 w
  change
    CF_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w) ↔
    CS_derives (csg_of_cfg g hne) [symbol.nonterminal (csg_of_cfg g hne).initial]
      (List.map symbol.terminal w)
  constructor
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CF_derives g [symbol.nonterminal g.initial] v →
          CS_derives (csg_of_cfg g hne) [symbol.nonterminal (csg_of_cfg g hne).initial] v :=
    by
      intro v h
      induction h with
      | refl =>
        apply CS_deri_self
      | tail _ hyp ih =>
        apply CS_deri_of_deri_tran ih
        unfold CF_transforms at hyp
        unfold CS_transforms
        rcases hyp with ⟨r, u, w, rin, bef, aft⟩
        refine ⟨csrule.mk [] r.fst [] r.snd, u, w, ?_, ?_, ?_⟩
        ·
          show _ ∈ (csg_of_cfg g hne).rules
          change _ ∈ List.map _ g.rules
          exact List.mem_map.mpr ⟨r, rin, rfl⟩
        ·
          simpa [List.append_nil] using bef
        ·
          simpa [List.append_nil] using aft
    exact indu (List.map symbol.terminal w)
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CS_derives (csg_of_cfg g hne) [symbol.nonterminal g.initial] v →
          CF_derives g [symbol.nonterminal (csg_of_cfg g hne).initial] v :=
    by
      intro v h
      induction h with
      | refl =>
        apply CF_deri_self
      | tail _ hyp ih =>
        apply CF_deri_of_deri_tran ih
        unfold CS_transforms at hyp
        unfold CF_transforms
        rcases hyp with ⟨r, u, w, rin, bef, aft⟩
        change r ∈ List.map _ g.rules at rin
        obtain ⟨r₀, r₀_in, r_eq⟩ := List.mem_map.mp rin
        rw [← r_eq] at bef aft
        simp at bef aft
        refine ⟨r₀, u, w, r₀_in, ?_, ?_⟩
        · simpa [List.singleton_append] using bef
        · simpa [List.append_assoc] using aft
    exact indu (List.map symbol.terminal w)

/-- Context-free languages without ε-productions are context-sensitive.

Note: the standard inclusion CF ⊆ CS requires that the context-free grammar has no
ε-productions, since context-sensitive grammars require non-empty output strings. -/
theorem CF_subclass_CS {L : Language T}
    (hne : ∃ g : CF_grammar T, CF_no_epsilon' g ∧ CF_language g = L) :
    is_CS L := by
  obtain ⟨g, hg, rfl⟩ := hne
  exact is_CS_via_csg_implies_is_CS ⟨csg_of_cfg g hg, (CF_language_eq_CS_language g hg).symm⟩

theorem CF_subclass_RE {L : Language T} :
  is_CF L → is_RE L := by
  intro h
  obtain ⟨g, eq_L⟩ := is_CF_implies_is_CF_via_cfg h
  exact ⟨grammar_of_cfg g, by rw [← eq_L, CF_language_eq_grammar_language]⟩
