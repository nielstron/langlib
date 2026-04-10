import Mathlib
import Langlib.Grammars.Indexed.Definition
import Langlib.Grammars.ContextFree.Definition
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Langlib.Classes.Indexed.Definition
import Langlib.Classes.ContextFree.Definition

/-! # Indexed Language Inclusions

This file proves that every context-free language is an indexed language.

The key idea: a context-free grammar can be viewed as an indexed grammar with an empty
flag type (`Empty`). Since there are no flags, no rule consumes or pushes flags, and
every nonterminal carries the trivial empty stack throughout derivations.

## Main declarations

- `indexed_of_cfg` — convert a CF grammar to an equivalent indexed grammar
- `CF_subclass_Indexed` — `is_CF L → is_Indexed L`
-/

open List

variable {T : Type}

/-- Convert a context-free grammar to an indexed grammar (with no flags). -/
def indexed_of_cfg (g : CF_grammar T) : IndexedGrammar T where
  nt := g.nt
  flag := Empty
  initial := g.initial
  rules := g.rules.map fun r =>
    { lhs := r.fst
      consume := none
      rhs := r.snd.map fun s =>
        match s with
        | symbol.terminal t => IRhsSymbol.terminal t
        | symbol.nonterminal n => IRhsSymbol.nonterminal n none }

private def cf_to_isym (g : CF_grammar T) (s : symbol T g.nt) :
    (indexed_of_cfg g).ISym :=
  match s with
  | symbol.terminal t => IndexedGrammar.ISym.terminal t
  | symbol.nonterminal n => IndexedGrammar.ISym.indexed n []

private def decode (g : CF_grammar T) (s : (indexed_of_cfg g).ISym) : symbol T g.nt :=
  match s with
  | IndexedGrammar.ISym.terminal t => symbol.terminal t
  | IndexedGrammar.ISym.indexed n _ => symbol.nonterminal n

private lemma expandRhs_map_eq (g : CF_grammar T) (rhs : List (symbol T g.nt)) :
    (indexed_of_cfg g).expandRhs
      (rhs.map fun s =>
        match s with
        | symbol.terminal t => IRhsSymbol.terminal t
        | symbol.nonterminal n => IRhsSymbol.nonterminal n none) [] =
    rhs.map (cf_to_isym g) := by
      -- By definition of `expandRhs`, we can see that it is the identity function on the_rhs.
      simp [indexed_of_cfg, IndexedGrammar.expandRhs];
      intro a ha; cases a <;> rfl;

/-
Forward direction: CF one-step maps to Indexed one-step.
-/
private lemma cf_tran_to_indexed_tran (g : CF_grammar T)
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_transforms g w₁ w₂) :
    (indexed_of_cfg g).Transforms (w₁.map (cf_to_isym g)) (w₂.map (cf_to_isym g)) := by
      rcases h with ⟨ r, u, v, hr, hw₁, hw₂ ⟩;
      use ⟨ r.1, none, r.2.map fun s => match s with | symbol.terminal t => IRhsSymbol.terminal t | symbol.nonterminal n => IRhsSymbol.nonterminal n none ⟩, u.map ( cf_to_isym g ), v.map ( cf_to_isym g ), [ ];
      refine' ⟨ _, _, _ ⟩;
      · unfold indexed_of_cfg; aesop;
      · aesop;
      · rw [ hw₂, map_append, map_append ];
        exact congr_arg₂ _ ( congr_arg₂ _ rfl ( by exact? ) ) rfl

private lemma cf_deri_to_indexed_deri (g : CF_grammar T)
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_derives g w₁ w₂) :
    (indexed_of_cfg g).Derives (w₁.map (cf_to_isym g)) (w₂.map (cf_to_isym g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (cf_tran_to_indexed_tran g ht)

/-
All stacks are empty in any sentential form reachable from the initial config.
-/
private lemma stacks_empty (g : CF_grammar T)
    {w : List ((indexed_of_cfg g).ISym)}
    (h : (indexed_of_cfg g).Derives [IndexedGrammar.ISym.indexed g.initial []] w) :
    ∀ s ∈ w, match s with
      | IndexedGrammar.ISym.terminal _ => True
      | IndexedGrammar.ISym.indexed _ σ => σ = [] := by
        contrapose h;
        push_neg at h;
        obtain ⟨ s, hs₁, hs₂ ⟩ := h;
        cases s <;> simp_all +decide [ indexed_of_cfg ];
        cases ‹List ( indexed_of_cfg g ).flag› <;> tauto

/-
One indexed step (with empty stacks) gives a CF step on decoded forms.
-/
private lemma indexed_tran_decode (g : CF_grammar T)
    {w₁ w₂ : List ((indexed_of_cfg g).ISym)}
    (ht : (indexed_of_cfg g).Transforms w₁ w₂)
    (hempty : ∀ s ∈ w₁, match s with
      | IndexedGrammar.ISym.terminal _ => True
      | IndexedGrammar.ISym.indexed _ σ => σ = []) :
    CF_transforms g (w₁.map (decode g)) (w₂.map (decode g)) := by
      obtain ⟨r, u, v, σ, hr⟩ := ht;
      rcases hr with ⟨ hr₁, hr₂, hr₃ ⟩;
      obtain ⟨r₀, hr₀⟩ : ∃ r₀ ∈ g.rules, r = { lhs := r₀.fst, consume := none, rhs := r₀.snd.map fun s => match s with | symbol.terminal t => IRhsSymbol.terminal t | symbol.nonterminal n => IRhsSymbol.nonterminal n none } := by
                                                unfold indexed_of_cfg at hr₁; aesop;
      use r₀, u.map (decode g), v.map (decode g);
      rcases σ with ⟨ ⟨ ⟩ ⟩;
      · have h_expand : (indexed_of_cfg g).expandRhs r.rhs [] = r₀.2.map (cf_to_isym g) := by
          rw [ hr₀.2 ];
          exact?;
        simp_all +decide [ List.map_append ];
        exact ⟨ rfl, by rw [ show decode g ∘ cf_to_isym g = id from funext fun x => by cases x <;> rfl ] ; simp +decide ⟩;
      · cases ‹ ( indexed_of_cfg g ).flag ›

/-- Indexed derivation from initial implies CF derivation (decoded). -/
private lemma indexed_deri_to_cf_deri (g : CF_grammar T)
    {w : List ((indexed_of_cfg g).ISym)}
    (h : (indexed_of_cfg g).Derives [IndexedGrammar.ISym.indexed g.initial []] w) :
    CF_derives g [symbol.nonterminal g.initial] (w.map (decode g)) := by
  induction h with
  | refl => simp [decode]; exact Relation.ReflTransGen.refl
  | tail hd ht ih => exact ih.tail (indexed_tran_decode g ht (stacks_empty g hd))

private lemma decode_terminal_map (g : CF_grammar T) (w : List T) :
    (w.map IndexedGrammar.ISym.terminal).map (decode g) = w.map symbol.terminal := by
  simp [List.map_map, decode]

private lemma cf_to_isym_terminal_map (g : CF_grammar T) (w : List T) :
    w.map (cf_to_isym g ∘ symbol.terminal) = w.map IndexedGrammar.ISym.terminal := by
  simp [cf_to_isym, Function.comp_def]

/-- The language of `indexed_of_cfg g` equals `CF_language g`. -/
theorem indexed_of_cfg_language (g : CF_grammar T) :
    (indexed_of_cfg g).Language = CF_language g := by
  ext w
  change (indexed_of_cfg g).Generates w ↔ CF_generates g w
  unfold IndexedGrammar.Generates CF_generates CF_generates_str
  constructor
  · intro h
    have := indexed_deri_to_cf_deri g h
    rwa [decode_terminal_map] at this
  · intro h
    have hd := cf_deri_to_indexed_deri g h
    convert hd using 1 <;> simp [cf_to_isym, List.map_map, Function.comp_def, indexed_of_cfg]

/-- Every context-free language is an indexed language. -/
theorem CF_subclass_Indexed {L : Language T} :
    is_CF L → is_Indexed L := by
  intro h
  obtain ⟨g, rfl⟩ := is_CF_implies_is_CF_via_cfg h
  exact ⟨indexed_of_cfg g, indexed_of_cfg_language g⟩
