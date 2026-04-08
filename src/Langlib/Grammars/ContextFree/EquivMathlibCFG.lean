import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Classes.ContextSensitive.Basics.Inclusion
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextSensitive.Definition
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Mathlib.Computability.ContextFreeGrammar

/-! # Context-Free Definition Equivalence with Mathlib's ContextFreeGrammar

This file relates the project's context-free grammars to context-sensitive, unrestricted, and mathlib formulations.

## Main declarations

- `is_CF_iff_isContextFree`
-/

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
    intro h
    obtain ⟨g, rfl⟩ := is_CF_implies_is_CF_via_cfg h
    exact ⟨mathlib_cfg_of_cfg g, (CF_language_eq_mathlib_language g).symm⟩
  ·
    rintro ⟨g, rfl⟩
    exact is_CF_via_cfg_implies_is_CF ⟨cfg_of_mathlib_cfg g, (mathlib_language_eq_CF_language g).symm⟩
