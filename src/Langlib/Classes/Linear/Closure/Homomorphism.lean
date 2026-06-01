module

/-
Copyright (c) 2026 Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Linear.Definition
public import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
public import Langlib.Grammars.Unrestricted.Toolbox
import Mathlib.Logic.Function.Basic
@[expose]
public section



/-! # Linear languages are closed under terminal homomorphisms

Relabelling the terminals of a grammar by a letter map `f : T₁ → T₂` (the
construction `map_grammar`) keeps the nonterminals untouched, so it preserves the
linear rule shape. Because a linear grammar's rules have empty left/right context,
the relabelled grammar generates exactly the `f`-image of the original language —
even when `f` is not injective. This yields:

- `is_Linear_map`              — `Linear` is closed under terminal maps `map f`.
- `is_Linear_of_map_injective` — and reflects them along injective maps.

The reflection direction is what lets a non-linearity result over a small concrete
alphabet (e.g. `Fin 4`) be transported to any larger alphabet.
-/

open Language List

variable {T₁ T₂ : Type}

/-- A symbol list whose entries are all terminals is the image of a terminal word. -/
public theorem eq_map_terminal_of_all {N : Type} :
    ∀ {l : List (symbol T₁ N)}, (∀ s ∈ l, ∃ t, s = symbol.terminal t) →
      ∃ o : List T₁, l = o.map symbol.terminal
  | [], _ => ⟨[], rfl⟩
  | a :: as, h => by
      obtain ⟨t, rfl⟩ := h a (List.mem_cons_self ..)
      obtain ⟨o, ho⟩ := eq_map_terminal_of_all (fun y hy => h y (List.mem_cons_of_mem _ hy))
      exact ⟨t :: o, by simp [ho]⟩

/-- Relabelling preserves the linear rule shape (nonterminals are untouched). -/
public theorem map_grammar_linear {g : grammar T₁} (hg : grammar_linear g) (f : T₁ → T₂) :
    grammar_linear (map_grammar g f) := by
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  obtain ⟨hL, hR, hlin⟩ := hg r' hr'
  refine ⟨by simp [map_grammar, hL], by simp [map_grammar, hR], ?_⟩
  rcases hlin with hterm | ⟨u, C, v, hout⟩
  · left
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hterm s hs
    exact ⟨f t, rfl⟩
  · right
    refine ⟨u.map f, C, v.map f, ?_⟩
    have hcomp : (map_symbol_fn f) ∘ (symbol.terminal : T₁ → symbol T₁ g.nt)
               = (symbol.terminal : T₂ → symbol T₂ g.nt) ∘ f := by funext t; rfl
    rw [hout]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, map_symbol_fn, hcomp]

/-- Forward relabelling of derivations. -/
public theorem map_grammar_derives {g : grammar T₁} (f : T₁ → T₂)
    {x y : List (symbol T₁ g.nt)} (h : grammar_derives g x y) :
    grammar_derives (map_grammar g f) (x.map (map_symbol_fn f)) (y.map (map_symbol_fn f)) := by
  induction h with
  | refl => exact grammar_deri_self
  | tail _ step ih =>
      refine grammar_deri_of_deri_tran ih ?_
      rcases step with ⟨r, hr, u, v, hu, hv⟩
      refine ⟨_, List.mem_map.2 ⟨r, hr, rfl⟩, u.map (map_symbol_fn f), v.map (map_symbol_fn f),
        ?_, ?_⟩
      · rw [hu]; simp [List.map_append, map_symbol_fn]
      · rw [hv]; simp [List.map_append]

/-- A relabelled list splits around a nonterminal exactly as the original does. -/
public theorem map_symbol_fn_eq_sandwich {N : Type} {f : T₁ → T₂} {N0 : N} :
    ∀ {x : List (symbol T₁ N)} {U V : List (symbol T₂ N)},
      x.map (map_symbol_fn f) = U ++ [symbol.nonterminal N0] ++ V →
      ∃ Ux Vx, x = Ux ++ [symbol.nonterminal N0] ++ Vx ∧
        U = Ux.map (map_symbol_fn f) ∧ V = Vx.map (map_symbol_fn f) := by
  intro x
  induction x with
  | nil => intro U V h; simp [List.append_assoc] at h
  | cons a xs ih =>
      intro U V h
      cases U with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.map_cons] at h
          obtain ⟨ha, hxs⟩ := List.cons.inj h
          have hae : a = symbol.nonterminal N0 := by cases a <;> simp_all [map_symbol_fn]
          exact ⟨[], xs, by simp [hae], rfl, hxs.symm⟩
      | cons b U' =>
          simp only [List.cons_append, List.map_cons] at h
          obtain ⟨hab, hxs⟩ := List.cons.inj h
          obtain ⟨Ux, Vx, hx, hU', hV⟩ := ih hxs
          subst hx
          refine ⟨a :: Ux, Vx, rfl, ?_, hV⟩
          rw [hU', ← hab]; rfl

/-- Reflection of derivations: any derivation of the relabelled (linear) grammar comes from a
derivation of the original grammar (this uses the empty context of linear rules). -/
public theorem map_grammar_derives_reflect {g : grammar T₁} (hg : grammar_linear g) (f : T₁ → T₂)
    {z : List (symbol T₂ g.nt)}
    (h : grammar_derives (map_grammar g f) [symbol.nonterminal g.initial] z) :
    ∃ x, z = x.map (map_symbol_fn f) ∧
      grammar_derives g [symbol.nonterminal g.initial] x := by
  induction h with
  | refl => exact ⟨[symbol.nonterminal g.initial], rfl, grammar_deri_self⟩
  | tail _ step ih =>
      obtain ⟨x, rfl, hdx⟩ := ih
      rcases step with ⟨r, hr, U, V, hsrc, htgt⟩
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      obtain ⟨hL, hR, -⟩ := hg r' hr'
      simp only [map_grammar, hL, hR, List.map_nil, List.append_nil] at hsrc htgt
      obtain ⟨Ux, Vx, hx, hUx, hVx⟩ := map_symbol_fn_eq_sandwich hsrc
      refine ⟨Ux ++ r'.output_string ++ Vx, ?_, ?_⟩
      · rw [htgt, hUx, hVx]; simp [List.map_append]
      · refine grammar_deri_of_deri_tran hdx ?_
        exact ⟨r', hr', Ux, Vx, by rw [hx, hL, hR]; simp, by simp⟩

/-- The relabelled grammar generates exactly the `f`-image of the original language. -/
public theorem map_grammar_language_linear {g : grammar T₁} (hg : grammar_linear g) (f : T₁ → T₂) :
    grammar_language (map_grammar g f) = Language.map f (grammar_language g) := by
  have hinj : Function.Injective (symbol.terminal (T := T₂) (N := g.nt)) :=
    fun a b hab => by injection hab
  have hfe : (map_symbol_fn f) ∘ (symbol.terminal : T₁ → symbol T₁ g.nt)
           = (symbol.terminal : T₂ → symbol T₂ g.nt) ∘ f := funext (fun _ => rfl)
  ext w
  constructor
  · intro hw
    obtain ⟨x, hxw, hdx⟩ :=
      map_grammar_derives_reflect hg f
        (show grammar_derives (map_grammar g f) [symbol.nonterminal g.initial]
          (List.map symbol.terminal w) from hw)
    -- the derived terminal word lifts to a terminal word `v` over `T₁`
    have hxterm : ∀ s ∈ x, ∃ t, s = symbol.terminal t := by
      intro s hs
      have hmem : map_symbol_fn f s ∈ List.map symbol.terminal w := hxw ▸ List.mem_map_of_mem hs
      rw [List.mem_map] at hmem
      obtain ⟨t, _, ht⟩ := hmem
      cases s with
      | terminal t' => exact ⟨t', rfl⟩
      | nonterminal n => simp [map_symbol_fn] at ht
    obtain ⟨v, rfl⟩ := eq_map_terminal_of_all hxterm
    have hwv : List.map f v = w := by
      have heq : List.map (symbol.terminal (N := g.nt)) w
               = List.map (symbol.terminal (N := g.nt)) (List.map f v) := by
        rw [hxw, List.map_map, List.map_map, hfe]
      exact (hinj.list_map heq).symm
    exact ⟨v, hdx, hwv⟩
  · rintro ⟨v, hv, rfl⟩
    have hd := map_grammar_derives (g := g) f
      (show grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal v) from hv)
    show grammar_derives (map_grammar g f) [symbol.nonterminal g.initial]
      (List.map symbol.terminal (List.map f v))
    have h2 : List.map (map_symbol_fn f) (List.map (symbol.terminal (N := g.nt)) v)
            = List.map (symbol.terminal (N := g.nt)) (List.map f v) := by
      rw [List.map_map, List.map_map, hfe]
    rwa [List.map_cons, List.map_nil, map_symbol_fn, h2] at hd

/-- **Linear languages are closed under terminal maps.** -/
public theorem is_Linear_map {L : Language T₁} (hL : is_Linear L) (f : T₁ → T₂) :
    is_Linear (Language.map f L) := by
  obtain ⟨g, hg, rfl⟩ := hL
  exact ⟨map_grammar g f, map_grammar_linear hg f, map_grammar_language_linear hg f⟩

/-- Linearity is reflected along injective terminal maps. -/
public theorem is_Linear_of_map_injective [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) {L : Language T₁} (h : is_Linear (Language.map f L)) :
    is_Linear L := by
  have hg' := is_Linear_map h (Function.invFun f)
  rw [Language.map_map] at hg'
  rwa [show Function.invFun f ∘ f = id from funext (Function.leftInverse_invFun hf),
    Language.map_id] at hg'
