module

/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Grammars.LR.Definition
public import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Mathlib.Logic.Function.Basic

@[expose]
public section

/-! # LR Languages Under Injective Terminal Maps

This file proves that LR(k) languages are closed under injective letter-to-letter
terminal maps. The construction relabels terminals in a context-free grammar and
uses injectivity to reflect rightmost derivations back to the original grammar,
where the LR(k) uniqueness condition is available.
-/

open Language

variable {T₁ T₂ : Type}

/-- Map a context-free rule along a terminal map, leaving nonterminals unchanged. -/
@[expose, reducible]
public def map_CF_rule {N : Type} (f : T₁ → T₂)
    (r : N × List (symbol T₁ N)) : N × List (symbol T₂ N) :=
  (r.1, r.2.map (map_symbol_fn f))

/-- Map a context-free grammar along a terminal map, leaving nonterminals unchanged. -/
@[expose, reducible]
public def map_CF_grammar (g : CF_grammar T₁) (f : T₁ → T₂) : CF_grammar T₂ where
  nt := g.nt
  initial := g.initial
  rules := g.rules.map (map_CF_rule f)

private lemma grammar_of_cfg_map_CF_grammar_comm (g : CF_grammar T₁) (f : T₁ → T₂) :
    grammar_of_cfg (map_CF_grammar g f) = map_grammar (grammar_of_cfg g) f := by
  unfold grammar_of_cfg map_CF_grammar map_grammar map_CF_rule
  simp

/-- The relabelled context-free grammar generates exactly the image language. -/
public theorem map_CF_grammar_language_of_leftInverse (g : CF_grammar T₁)
    {f : T₁ → T₂} {g' : T₂ → T₁} (hfg : Function.LeftInverse g' f) :
    CF_language (map_CF_grammar g f) = Language.map f (CF_language g) := by
  rw [CF_language_eq_grammar_language, grammar_of_cfg_map_CF_grammar_comm,
    map_grammar_language_of_leftInverse (grammar_of_cfg g) hfg,
    ← CF_language_eq_grammar_language]

private lemma map_CF_grammar_producesRightmost_reflect (g : CF_grammar T₁)
    {f : T₁ → T₂} {g' : T₂ → T₁} (hfg : Function.LeftInverse g' f)
    {u v : List (symbol T₂ (map_CF_grammar g f).nt)}
    (h : (map_CF_grammar g f).ProducesRightmost u v) :
    g.ProducesRightmost (u.map (map_symbol_fn g')) (v.map (map_symbol_fn g')) := by
  rcases h with ⟨r, hr, p, lookahead, hu, hv⟩
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  have hleft : map_symbol_fn g' ∘ map_symbol_fn f = @id (symbol T₁ g.nt) := by
    funext s
    exact map_symbol_fn_leftInverse hfg s
  refine ⟨r', hr', p.map (map_symbol_fn g'), lookahead.map g', ?_, ?_⟩
  · have hu' := congrArg (List.map (map_symbol_fn g')) hu
    simpa [map_CF_grammar, map_CF_rule, List.map_append, List.map_map, map_symbol_fn] using hu'
  · have hv' := congrArg (List.map (map_symbol_fn g')) hv
    simpa [map_CF_grammar, map_CF_rule, List.map_append, List.map_map, map_symbol_fn, hleft] using hv'

private lemma map_CF_grammar_derivesRightmost_reflect (g : CF_grammar T₁)
    {f : T₁ → T₂} {g' : T₂ → T₁} (hfg : Function.LeftInverse g' f)
    {u v : List (symbol T₂ (map_CF_grammar g f).nt)}
    (h : (map_CF_grammar g f).DerivesRightmost u v) :
    g.DerivesRightmost (u.map (map_symbol_fn g')) (v.map (map_symbol_fn g')) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih
        (map_CF_grammar_producesRightmost_reflect g hfg step)

/-- Relabelling a grammar by an injective terminal map preserves the LR(k) condition. -/
public theorem map_CF_grammar_isLRk_of_injective [Nonempty T₁] (g : CF_grammar T₁)
    {f : T₁ → T₂} (hf : Function.Injective f) {k : ℕ}
    (hg : g.IsLRk k) : (map_CF_grammar g f).IsLRk k := by
  let g' : T₂ → T₁ := Function.invFun f
  have hfg : Function.LeftInverse g' f := Function.leftInverse_invFun hf
  intro r₁ r₂ hr₁ hr₂ p₁ p₂ core s₁ s₂ hd₁ hd₂ hc₁ hc₂ hlook
  obtain ⟨r₁', hr₁', rfl⟩ := List.mem_map.mp hr₁
  obtain ⟨r₂', hr₂', rfl⟩ := List.mem_map.mp hr₂
  have hd₁' :
      g.DerivesRightmost [symbol.nonterminal g.initial]
        (p₁.map (map_symbol_fn g') ++ [symbol.nonterminal r₁'.1] ++
          (s₁.map g').map symbol.terminal) := by
    have h := map_CF_grammar_derivesRightmost_reflect g hfg hd₁
    simpa [map_CF_grammar, map_CF_rule, List.map_append, map_symbol_fn, List.map_map] using h
  have hd₂' :
      g.DerivesRightmost [symbol.nonterminal g.initial]
        (p₂.map (map_symbol_fn g') ++ [symbol.nonterminal r₂'.1] ++
          (s₂.map g').map symbol.terminal) := by
    have h := map_CF_grammar_derivesRightmost_reflect g hfg hd₂
    simpa [map_CF_grammar, map_CF_rule, List.map_append, map_symbol_fn, List.map_map] using h
  have hc₁' : p₁.map (map_symbol_fn g') ++ r₁'.2 = core.map (map_symbol_fn g') := by
    have h := congrArg (List.map (map_symbol_fn g')) hc₁
    have hleft : map_symbol_fn g' ∘ map_symbol_fn f = @id (symbol T₁ g.nt) := by
      funext s
      exact map_symbol_fn_leftInverse hfg s
    simpa [map_CF_rule, List.map_append, List.map_map, hleft] using h
  have hc₂' : p₂.map (map_symbol_fn g') ++ r₂'.2 = core.map (map_symbol_fn g') := by
    have h := congrArg (List.map (map_symbol_fn g')) hc₂
    have hleft : map_symbol_fn g' ∘ map_symbol_fn f = @id (symbol T₁ g.nt) := by
      funext s
      exact map_symbol_fn_leftInverse hfg s
    simpa [map_CF_rule, List.map_append, List.map_map, hleft] using h
  have hlook' : CF_grammar.lrLookahead k (s₁.map g') =
      CF_grammar.lrLookahead k (s₂.map g') := by
    simpa [CF_grammar.lrLookahead, List.map_take] using congrArg (List.map g') hlook
  obtain ⟨_, hrules⟩ :=
    hg r₁' r₂' hr₁' hr₂' (p₁.map (map_symbol_fn g')) (p₂.map (map_symbol_fn g'))
      (core.map (map_symbol_fn g')) (s₁.map g') (s₂.map g') hd₁' hd₂' hc₁' hc₂' hlook'
  have hprefix : p₁ = p₂ := by
    apply List.append_cancel_right
    calc
      p₁ ++ r₁'.2.map (map_symbol_fn f) = core := hc₁
      _ = p₂ ++ r₂'.2.map (map_symbol_fn f) := hc₂.symm
      _ = p₂ ++ r₁'.2.map (map_symbol_fn f) := by rw [hrules]
  exact ⟨hprefix, by rw [hrules]⟩

/-- LR(k) languages are closed under injective terminal maps. -/
public theorem is_LRk_map_injective [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) {k : ℕ} {L : Language T₁}
    (hL : is_LRk k L) : is_LRk k (Language.map f L) := by
  obtain ⟨g, hg, hlang⟩ := hL
  refine ⟨map_CF_grammar g f, map_CF_grammar_isLRk_of_injective g hf hg, ?_⟩
  rw [map_CF_grammar_language_of_leftInverse g (Function.leftInverse_invFun hf), hlang]

/-- LR languages are closed under injective terminal maps. -/
public theorem is_LR_map_injective [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) {L : Language T₁}
    (hL : is_LR L) : is_LR (Language.map f L) := by
  obtain ⟨k, hk⟩ := hL
  exact ⟨k, is_LRk_map_injective hf hk⟩
