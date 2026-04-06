import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Classes.ContextSensitive.Basics.Inclusion
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextSensitive.Definition
import Langlib.Classes.RecursivelyEnumerable.Definition
import Mathlib.Computability.ContextFreeGrammar

/-! # Context-Free Inclusions

This file relates the project's context-free grammars to context-sensitive, unrestricted, and mathlib formulations.

## Main declarations

- `CF_subclass_CS`
- `CF_subclass_RE`
- `is_CF_iff_isContextFree`
-/

variable {T : Type}

private def Symbol_of_symbol {T N : Type} : symbol T N → Symbol T N
| symbol.terminal t => Symbol.terminal t
| symbol.nonterminal n => Symbol.nonterminal n

private def symbol_of_Symbol {T N : Type} : Symbol T N → symbol T N
| Symbol.terminal t => symbol.terminal t
| Symbol.nonterminal n => symbol.nonterminal n

private def lsSymbol_of_lssymbol {T N : Type} : List (symbol T N) → List (Symbol T N) :=
  List.map Symbol_of_symbol

private def lssymbol_of_lsSymbol {T N : Type} : List (Symbol T N) → List (symbol T N) :=
  List.map symbol_of_Symbol

@[simp] private lemma symbol_of_Symbol_of_symbol {T N : Type} (s : symbol T N) :
  symbol_of_Symbol (Symbol_of_symbol s) = s := by
  cases s <;> rfl

@[simp] private lemma Symbol_of_symbol_of_Symbol {T N : Type} (s : Symbol T N) :
  Symbol_of_symbol (symbol_of_Symbol s) = s := by
  cases s <;> rfl

@[simp] private lemma lssymbol_of_lsSymbol_of_lssymbol {T N : Type} (s : List (symbol T N)) :
  lssymbol_of_lsSymbol (lsSymbol_of_lssymbol s) = s := by
  induction s with
  | nil => rfl
  | cons h t ih =>
    simpa [lsSymbol_of_lssymbol, lssymbol_of_lsSymbol, List.map_map] using ih

@[simp] private lemma lsSymbol_of_lssymbol_of_lsSymbol {T N : Type} (s : List (Symbol T N)) :
  lsSymbol_of_lssymbol (lssymbol_of_lsSymbol s) = s := by
  induction s with
  | nil => rfl
  | cons h t ih =>
    simpa [lsSymbol_of_lssymbol, lssymbol_of_lsSymbol, List.map_map] using ih

noncomputable def mathlib_cfg_of_cfg (g : CF_grammar T) : ContextFreeGrammar T :=
  by
    classical
    exact ⟨g.nt, g.initial, (g.rules.map fun r => ⟨r.fst, lsSymbol_of_lssymbol r.snd⟩).toFinset⟩

noncomputable def cfg_of_mathlib_cfg (g : ContextFreeGrammar T) : CF_grammar T :=
  ⟨g.NT, g.initial, g.rules.toList.map fun r => (r.input, lssymbol_of_lsSymbol r.output)⟩

/-- A context-free grammar has no ε-productions (every rule has a non-empty right-hand side). -/
def CF_no_epsilon (g : CF_grammar T) : Prop :=
  ∀ r ∈ g.rules, r.snd ≠ []

/-- Convert a context-free grammar without ε-productions to a context-sensitive grammar.
    The CS rules have empty context (α = β = []) and γ = rule output. -/
def csg_of_cfg (g : CF_grammar T) (hne : CF_no_epsilon g) : CS_grammar T where
  nt := g.nt
  initial := g.initial
  rules := List.map (fun r : g.nt × (List (symbol T g.nt)) =>
    csrule.mk [] r.fst [] r.snd) g.rules
  output_nonempty := by
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    exact hne r₀ hr₀

def grammar_of_cfg (g : CF_grammar T) : grammar T :=
grammar.mk g.nt g.initial (List.map (fun r : g.nt × (List (symbol T g.nt)) =>
  grule.mk [] r.fst [] r.snd) g.rules)

lemma grammar_of_cfg_well_defined (g : CF_grammar T) (hne : CF_no_epsilon g) :
  grammar_of_csg (csg_of_cfg g hne) = grammar_of_cfg g :=
by
  cases g with
  | mk nt initial rules =>
    simp [grammar_of_csg, csg_of_cfg, grammar_of_cfg, List.map_map, List.append_nil]

lemma CF_language_eq_CS_language (g : CF_grammar T) (hne : CF_no_epsilon g) :
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

lemma CF_language_eq_grammar_language (g : CF_grammar T) :
  CF_language g = grammar_language (grammar_of_cfg g) :=
by
  unfold CF_language
  unfold grammar_language
  ext1 w
  rw [Set.mem_setOf_eq]
  unfold grammar_generates
  constructor
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CF_derives g [symbol.nonterminal g.initial] v →
          grammar_derives (grammar_of_cfg g) [symbol.nonterminal (grammar_of_cfg g).initial] v :=
    by
      clear w
      intros v hypo
      induction hypo with
      | refl =>
        apply grammar_deri_self
      | tail _ step ih =>
        apply grammar_deri_of_deri_tran
        · exact ih
        unfold CF_transforms at step
        unfold grammar_transforms
        delta grammar_of_cfg
        dsimp only
        rcases step with ⟨r, u, w, rin, bef, aft⟩
        use grule.mk [] r.fst [] r.snd
        constructor
        ·
          rw [List.mem_map]
          refine ⟨r, rin, ?_⟩
          rfl
        ·
          use u
          use w
          constructor
          · simpa [List.append_nil] using bef
          · simpa [List.append_nil] using aft
    exact indu (List.map symbol.terminal w)
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        grammar_derives (grammar_of_cfg g) [symbol.nonterminal (grammar_of_cfg g).initial] v →
          CF_derives g [symbol.nonterminal g.initial] v :=
    by
      clear w
      intros v hypo
      induction hypo with
      | refl =>
        apply CF_deri_self
      | tail _ step ih =>
        apply CF_deri_of_deri_tran
        · exact ih
        unfold grammar_transforms at step
        unfold CF_transforms
        delta grammar_of_cfg at step
        dsimp only at step
        rcases step with ⟨r, rin, u, w, bef, aft⟩
        rcases (List.mem_map.1 rin) with ⟨r', new_rule_in, new_rule_def⟩
        rw [← new_rule_def] at bef aft
        refine ⟨r', u, w, new_rule_in, ?_, ?_⟩
        · simpa [List.append_nil] using bef
        · simpa [List.append_nil] using aft
    exact indu (List.map symbol.terminal w)

/-- Context-free languages without ε-productions are context-sensitive.

Note: the standard inclusion CF ⊆ CS requires that the context-free grammar has no
ε-productions, since context-sensitive grammars require non-empty output strings. -/
theorem CF_subclass_CS {L : Language T}
    (hne : ∃ g : CF_grammar T, CF_no_epsilon g ∧ CF_language g = L) :
    is_CS L := by
  obtain ⟨g, hg, rfl⟩ := hne
  exact ⟨csg_of_cfg g hg, (CF_language_eq_CS_language g hg).symm⟩

theorem CF_subclass_RE {L : Language T} :
  is_CF L → is_RE L :=
by
  rintro ⟨g, eq_L⟩
  exact ⟨grammar_of_cfg g, by rw [← eq_L, CF_language_eq_grammar_language]⟩

lemma CF_language_eq_mathlib_language (g : CF_grammar T) :
  CF_language g = (mathlib_cfg_of_cfg g).language := by
  classical
  unfold CF_language ContextFreeGrammar.language
  ext w
  change
    CF_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w) ↔
      (mathlib_cfg_of_cfg g).Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)
  constructor
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CF_derives g [symbol.nonterminal g.initial] v →
          (mathlib_cfg_of_cfg g).Derives [Symbol.nonterminal g.initial] (lsSymbol_of_lssymbol v) :=
    by
      intro v h
      induction h with
      | refl =>
        apply ContextFreeGrammar.Derives.refl
      | tail _ hyp ih =>
        apply ContextFreeGrammar.Derives.trans_produces ih
        rcases hyp with ⟨r, x, y, rin, bef, aft⟩
        refine ⟨⟨r.fst, lsSymbol_of_lssymbol r.snd⟩, ?_, ?_⟩
        ·
          have hr :
              (⟨r.fst, lsSymbol_of_lssymbol r.snd⟩ : ContextFreeRule T g.nt) ∈
                g.rules.map (fun r => ⟨r.fst, lsSymbol_of_lssymbol r.snd⟩) := by
            exact List.mem_map.mpr ⟨r, rin, rfl⟩
          simpa [mathlib_cfg_of_cfg] using hr
        ·
          have hrew :
              (⟨r.fst, lsSymbol_of_lssymbol r.snd⟩ : ContextFreeRule T g.nt).Rewrites
                (lsSymbol_of_lssymbol (x ++ [symbol.nonterminal r.fst] ++ y))
                (lsSymbol_of_lssymbol (x ++ r.snd ++ y)) := by
            simpa [lsSymbol_of_lssymbol, List.map_append] using
              (ContextFreeRule.rewrites_of_exists_parts
                (⟨r.fst, lsSymbol_of_lssymbol r.snd⟩ : ContextFreeRule T g.nt)
                (lsSymbol_of_lssymbol x) (lsSymbol_of_lssymbol y))
          simpa [bef, aft] using hrew
    simpa [lsSymbol_of_lssymbol, List.map_map] using indu (List.map symbol.terminal w)
  ·
    have indu :
      ∀ v : List (Symbol T g.nt),
        (mathlib_cfg_of_cfg g).Derives [Symbol.nonterminal g.initial] v →
          CF_derives g [symbol.nonterminal g.initial] (lssymbol_of_lsSymbol v) :=
    by
      intro v h
      induction h with
      | refl =>
        apply CF_deri_self
      | tail _ hyp ih =>
        apply CF_deri_of_deri_tran ih
        rcases hyp with ⟨r, rin, hrew⟩
        have rin' : r ∈ g.rules.map (fun r => ⟨r.fst, lsSymbol_of_lssymbol r.snd⟩) := by
          simpa [mathlib_cfg_of_cfg] using rin
        rcases (List.mem_map.1 rin') with ⟨r₀, r₀_in, r_eq⟩
        rcases ContextFreeRule.Rewrites.exists_parts hrew with ⟨p, q, bef, aft⟩
        use (r₀.fst, r₀.snd), lssymbol_of_lsSymbol p, lssymbol_of_lsSymbol q
        constructor
        · exact r₀_in
        · constructor
          ·
            cases r_eq
            apply congrArg lssymbol_of_lsSymbol at bef
            simpa [lssymbol_of_lsSymbol, List.map_append] using bef
          ·
            cases r_eq
            have aft' := congrArg lssymbol_of_lsSymbol aft
            have hm : List.map symbol_of_Symbol (lsSymbol_of_lssymbol r₀.2) = r₀.2 :=
              lssymbol_of_lsSymbol_of_lssymbol r₀.2
            simp only [lssymbol_of_lsSymbol, List.map_append] at aft'
            rw [hm] at aft'
            simpa [lssymbol_of_lsSymbol, List.map_append] using aft'
    intro h
    simpa [lssymbol_of_lsSymbol, List.map_map] using indu (List.map Symbol.terminal w) h

lemma mathlib_cfg_of_cfg_of_mathlib_cfg (g : ContextFreeGrammar T) :
  mathlib_cfg_of_cfg (cfg_of_mathlib_cfg g) = g := by
  classical
  cases g with
  | mk NT initial rules =>
    have hrules :
        (List.map
          ((fun r => ⟨r.1, lsSymbol_of_lssymbol r.2⟩) ∘
            fun r => (r.input, lssymbol_of_lsSymbol r.output))
          rules.toList).toFinset = rules := by
      ext r
      simp [List.mem_map]
    simp [mathlib_cfg_of_cfg, cfg_of_mathlib_cfg, hrules]

lemma mathlib_language_eq_CF_language (g : ContextFreeGrammar T) :
  g.language = CF_language (cfg_of_mathlib_cfg g) := by
  have h := CF_language_eq_mathlib_language (cfg_of_mathlib_cfg g)
  rw [mathlib_cfg_of_cfg_of_mathlib_cfg g] at h
  exact h.symm

theorem is_CF_iff_isContextFree {L : Language T} :
  is_CF L ↔ L.IsContextFree := by
  constructor
  ·
    rintro ⟨g, rfl⟩
    exact ⟨mathlib_cfg_of_cfg g, (CF_language_eq_mathlib_language g).symm⟩
  ·
    rintro ⟨g, rfl⟩
    exact ⟨cfg_of_mathlib_cfg g, (mathlib_language_eq_CF_language g).symm⟩
