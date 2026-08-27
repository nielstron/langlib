module

public import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
public import Langlib.Grammars.LR.Definition

@[expose]
public section

/-!
# LR(k) Grammars as Unrestricted Grammars

This file proves that the direct LR(k) definitions on unrestricted grammars agree
with the established definitions on `CF_grammar` whenever the unrestricted
grammar is context-free.  It also proves that the resulting language classes are
equivalent.

## Main declarations

* `grammar_of_cfg_isLRk_iff` identifies LR(k) for a `CF_grammar` and its
  unrestricted representation.
* `grammar_lrk_iff_cfg_of_grammar_isLRk` identifies LR(k) for a context-free
  unrestricted grammar and its `CF_grammar` representation.
* `is_LRk_iff_is_LRk_via_cfg` identifies the two language-class presentations.
-/

open Language

variable {T N : Type}

/-! ## Rules and rightmost derivations -/

/-- Regard a context-free rule as an unrestricted rule with empty context. -/
public def grule_of_cfrule (r : N × List (symbol T N)) : grule T N :=
  ⟨[], r.1, [], r.2⟩

public theorem grule_of_cfrule_injective :
    Function.Injective (@grule_of_cfrule T N) := by
  rintro ⟨A, u⟩ ⟨B, v⟩ h
  cases h
  rfl

public theorem grammar_of_cfg_rules (G : CF_grammar T) :
    (grammar_of_cfg G).rules = G.rules.map grule_of_cfrule := rfl

public theorem grammar_of_cfg_rewritesRightmost_iff
    (r : N × List (symbol T N)) (u v : List (symbol T N)) :
    grammar.RewritesRightmost (grule_of_cfrule r) u v ↔
      CF_grammar.RewritesRightmost r u v := by
  simp only [grammar.RewritesRightmost, CF_grammar.RewritesRightmost,
    grule_of_cfrule, List.append_nil]

public theorem grammar_of_cfg_producesRightmost_iff (G : CF_grammar T)
    (u v : List (symbol T G.nt)) :
    (grammar_of_cfg G).ProducesRightmost u v ↔ G.ProducesRightmost u v := by
  constructor
  · rintro ⟨R, hR, hrewrite⟩
    rw [grammar_of_cfg_rules] at hR
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hR
    exact ⟨r, hr, (grammar_of_cfg_rewritesRightmost_iff r u v).mp hrewrite⟩
  · rintro ⟨r, hr, hrewrite⟩
    refine ⟨grule_of_cfrule r, ?_,
      (grammar_of_cfg_rewritesRightmost_iff r u v).mpr hrewrite⟩
    rw [grammar_of_cfg_rules]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩

public theorem grammar_of_cfg_derivesRightmost_iff (G : CF_grammar T)
    (u v : List (symbol T G.nt)) :
    (grammar_of_cfg G).DerivesRightmost u v ↔ G.DerivesRightmost u v := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
        exact ih.tail ((grammar_of_cfg_producesRightmost_iff G _ _).mp hstep)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
        exact ih.tail ((grammar_of_cfg_producesRightmost_iff G _ _).mpr hstep)

private theorem normalize_context_free_handle
    (p s : List (symbol T N)) (A : N) :
    p ++ [] ++ [symbol.nonterminal A] ++ [] ++ s =
      p ++ [symbol.nonterminal A] ++ s := by
  simp

/-! ## Grammar-level LR(k) equivalence -/

public theorem grammar_of_cfg_coreIsLRk_iff (G : CF_grammar T) (k : ℕ) :
    (grammar_of_cfg G).CoreIsLRk k ↔ G.CoreIsLRk k := by
  constructor
  · intro h r₁ r₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y hd₁ hd₂ hform hlook
    have hd₁' : (grammar_of_cfg G).DerivesRightmost
        [symbol.nonterminal (grammar_of_cfg G).initial]
        (p₁ ++ [symbol.nonterminal r₁.1] ++ s₁.map symbol.terminal) :=
      (grammar_of_cfg_derivesRightmost_iff G _ _).mpr
        (by simpa [grammar_of_cfg] using hd₁)
    have hd₂' : (grammar_of_cfg G).DerivesRightmost
        [symbol.nonterminal (grammar_of_cfg G).initial]
        (p₂ ++ [symbol.nonterminal r₂.1] ++ s₂.map symbol.terminal) :=
      (grammar_of_cfg_derivesRightmost_iff G _ _).mpr
        (by simpa [grammar_of_cfg] using hd₂)
    have hout := h (grule_of_cfrule r₁) (grule_of_cfrule r₂)
      (by
        rw [grammar_of_cfg_rules]
        exact List.mem_map.mpr ⟨r₁, hr₁, rfl⟩)
      (by
        rw [grammar_of_cfg_rules]
        exact List.mem_map.mpr ⟨r₂, hr₂, rfl⟩)
      p₁ p₂ s₁ s₂ y
      (by
        exact (normalize_context_free_handle p₁
          (s₁.map symbol.terminal) r₁.1).symm ▸ hd₁')
      (by
        exact (normalize_context_free_handle p₂
          (s₂.map symbol.terminal) r₂.1).symm ▸ hd₂')
      hform
      (by
        simpa [grammar.lrLookahead, CF_grammar.lrLookahead] using hlook)
    exact ⟨hout.1, grule_of_cfrule_injective hout.2⟩
  · intro h R₁ R₂ hR₁ hR₂ p₁ p₂ s₁ s₂ y hd₁ hd₂ hform hlook
    change grule T G.nt at R₁ R₂
    change List (symbol T G.nt) at p₁ p₂
    rw [grammar_of_cfg_rules] at hR₁ hR₂
    obtain ⟨r₁, hr₁, rfl⟩ := List.mem_map.mp hR₁
    obtain ⟨r₂, hr₂, rfl⟩ := List.mem_map.mp hR₂
    have hd₁' : G.DerivesRightmost [symbol.nonterminal G.initial]
        (p₁ ++ [symbol.nonterminal r₁.1] ++ s₁.map symbol.terminal) := by
      apply (grammar_of_cfg_derivesRightmost_iff G _ _).mp
      exact normalize_context_free_handle p₁
        (s₁.map symbol.terminal) r₁.1 ▸ hd₁
    have hd₂' : G.DerivesRightmost [symbol.nonterminal G.initial]
        (p₂ ++ [symbol.nonterminal r₂.1] ++ s₂.map symbol.terminal) := by
      apply (grammar_of_cfg_derivesRightmost_iff G _ _).mp
      exact normalize_context_free_handle p₂
        (s₂.map symbol.terminal) r₂.1 ▸ hd₂
    have hout := h r₁ r₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y hd₁' hd₂'
      hform (by
        simpa [grammar.lrLookahead, CF_grammar.lrLookahead] using hlook)
    exact ⟨hout.1, congrArg grule_of_cfrule hout.2⟩

public theorem grammar_augment_grammar_of_cfg (G : CF_grammar T) :
    grammar.augment (grammar_of_cfg G) = grammar_of_cfg G.augment := by
  cases G with
  | mk nt initial rules =>
      simp [grammar.augment, grammar.augmentStartRule, grammar.augmentRule,
        grammar.augmentString, grammar.augmentSymbol, grammar_of_cfg,
        CF_grammar.augment, CF_grammar.augmentStartRule,
        CF_grammar.augmentRule, CF_grammar.augmentString,
        CF_grammar.augmentSymbol, List.map_map, Function.comp_def]

public theorem grammar_of_cfg_isLRk_iff (G : CF_grammar T) (k : ℕ) :
    (grammar_of_cfg G).IsLRk k ↔ G.IsLRk k := by
  rw [grammar.IsLRk, grammar_augment_grammar_of_cfg, CF_grammar.IsLRk]
  exact grammar_of_cfg_coreIsLRk_iff G.augment k

/-! ## Context-free unrestricted grammars -/

public theorem grammar_of_cfg_cfg_of_grammar (g : grammar T)
    (hg : grammar_context_free g) :
    grammar_of_cfg (cfg_of_grammar g hg) = g := by
  cases g with
  | mk nt initial rules =>
      unfold grammar_context_free at hg
      simp only [cfg_of_grammar, grammar_of_cfg]
      congr 1
      induction rules with
      | nil => rfl
      | cons r rs ih =>
          have hr := hg r (by simp)
          have hrs : ∀ q ∈ rs, q.input_L = [] ∧ q.input_R = [] := by
            intro q hq
            exact hg q (by simp [hq])
          simp only [List.map_cons]
          congr 1
          · cases r with
            | mk input_L input_N input_R output_string =>
                simp only at hr ⊢
                rw [hr.1, hr.2]
                rfl
          · exact ih hrs

public theorem grammar_lrk_iff_cfg_of_grammar_isLRk (g : grammar T)
    (hg : grammar_context_free g) (k : ℕ) :
    grammar_lrk k g ↔ (cfg_of_grammar g hg).IsLRk k := by
  constructor
  · intro h
    apply (grammar_of_cfg_isLRk_iff (cfg_of_grammar g hg) k).mp
    simpa only [grammar_of_cfg_cfg_of_grammar g hg] using h.2
  · intro h
    refine ⟨hg, ?_⟩
    have h' := (grammar_of_cfg_isLRk_iff (cfg_of_grammar g hg) k).mpr h
    simpa only [grammar_of_cfg_cfg_of_grammar g hg] using h'

/-! ## Language-class equivalence -/

public theorem is_LRk_iff_is_LRk_via_cfg {k : ℕ} {L : Language T} :
    is_LRk k L ↔ is_LRk_via_cfg k L := by
  constructor
  · rintro ⟨g, ⟨hg, hLR⟩, hL⟩
    refine ⟨cfg_of_grammar g hg, ?_, (cfg_of_grammar_language_eq g hg).trans hL⟩
    exact (grammar_lrk_iff_cfg_of_grammar_isLRk g hg k).mp ⟨hg, hLR⟩
  · rintro ⟨G, hLR, hL⟩
    refine ⟨grammar_of_cfg G, ?_, (CF_language_eq_grammar_language G).symm.trans hL⟩
    refine ⟨grammar_of_cfg_context_free G, ?_⟩
    exact (grammar_of_cfg_isLRk_iff G k).mpr hLR
