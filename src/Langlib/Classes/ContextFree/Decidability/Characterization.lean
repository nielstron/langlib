module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.ContextFree.Decidability.Helper
public import Langlib.Classes.ContextFree.Basics.Lifting
public import Langlib.Classes.ContextFree.Basics.EncodedCFG
public import Langlib.Classes.ContextFree.Basics.FiniteNT
public import Langlib.Classes.ContextFree.Definition
public import Langlib.Grammars.ContextFree.EquivMathlibCFG
public import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
@[expose]
public section



/-! # `EncodedCFG` characterizes the context-free languages

This file proves that the encoded-grammar encoding `EncodedCFG` denotes exactly the
context-free languages:

`∀ L, L ∈ CF ↔ ∃ c : EncodedCFG T, contextFreeLanguageOf c = L`

**Soundness** (every code denotes a context-free language): an `EncodedCFG` decodes —
by construction — to a `CF_grammar` (`toCFGrammar`), so its language is `is_CF_via_cfg`,
hence `is_CF`.

**Completeness** (every context-free language is encoded): a context-free language has a
`CF_grammar` presentation with *finitely many* nonterminals (`exists_fintype_nt`); we
reindex those nonterminals to `Fin (n+1)` and read the grammar off as an `EncodedCFG`.
Reindexing the nonterminals along an equivalence preserves the language
(`cf_language_eq_of_rename`), proved with the lifting machinery (`lift_deri` / `sink_deri`).
-/

namespace ContextFree.EncodedCFG

variable {T : Type}

open EncodedCFG

/-! ## Renaming nonterminals preserves the language -/

/-- Renaming the nonterminals of a context-free grammar along an equivalence preserves
its language. Both directions go through the lifting machinery: `lift_deri` pushes a
derivation forward along `e`, and `sink_deri` pulls one back along `e.symm`. -/
public theorem cf_language_eq_of_rename {g₀ g : CF_grammar T} (e : g₀.nt ≃ g.nt)
    (hinit : g.initial = e g₀.initial)
    (hfwd : ∀ r ∈ g₀.rules, lift_rule (⇑e) r ∈ g.rules)
    (hbwd : ∀ r ∈ g.rules, ∃ r₀ ∈ g₀.rules, lift_rule (⇑e) r₀ = r) :
    CF_language g = CF_language g₀ := by
  let lg : lifted_grammar T :=
    { g₀ := g₀, g := g, lift_nt := ⇑e, lift_inj := e.injective
      corresponding_rules := hfwd
      sink_nt := fun x => some (e.symm x)
      sink_inj := fun x y h => Or.inl (e.symm.injective (Option.some.inj h))
      preimage_of_rules := fun r hr => hbwd r hr.1
      lift_nt_sink := fun n₀ => by simp }
  ext w
  constructor
  · -- `w ∈ CF_language g → w ∈ CF_language g₀` : pull the derivation back along `e.symm`.
    intro hw
    have hd : CF_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w) := hw
    have hgood : good_string (lg := lg) [symbol.nonterminal g.initial] := by
      intro a ha
      rw [List.mem_singleton] at ha; subst ha
      exact ⟨e.symm g.initial, rfl⟩
    have hsink :=
      (sink_deri lg [symbol.nonterminal g.initial] (List.map symbol.terminal w) hd hgood).1
    have hstart : sink_string lg.sink_nt ([symbol.nonterminal g.initial] : List (symbol T g.nt))
        = ([symbol.nonterminal g₀.initial] : List (symbol T g₀.nt)) := by
      simp [sink_string, sink_symbol, lg, hinit, Equiv.symm_apply_apply]
    rw [hstart, sink_string_map_terminal lg w] at hsink
    exact hsink
  · -- `w ∈ CF_language g₀ → w ∈ CF_language g` : push the derivation forward along `e`.
    intro hw
    have hd : CF_derives g₀ [symbol.nonterminal g₀.initial] (List.map symbol.terminal w) := hw
    have hlift := lift_deri (lg := lg) hd
    have hstart : lift_string lg.lift_nt ([symbol.nonterminal g₀.initial] : List (symbol T g₀.nt))
        = ([symbol.nonterminal g.initial] : List (symbol T g.nt)) := by
      simp [lift_string, lift_symbol, lg, hinit]
    rw [hstart, lift_string_map_terminal lg w] at hlift
    exact hlift

/-! ## The encoding -/

/-- Encode a symbol over `Fin (k+1)`-valued nonterminals into the raw `ℕ ⊕ T` format. -/
@[expose]
public def encodeSymbol {N : Type} {k : ℕ} (f : N → Fin (k + 1)) :
    symbol T N → ℕ ⊕ T
  | symbol.terminal t => Sum.inr t
  | symbol.nonterminal m => Sum.inl (f m).val

/-- Encode a context-free grammar whose nonterminals are indexed by `Fin (k+1)` (via the
equivalence `e`) as an `EncodedCFG`. -/
@[expose]
public def encodeCFG {k : ℕ} (g : CF_grammar T) (e : g.nt ≃ Fin (k + 1)) : EncodedCFG T :=
  (k, (e g.initial).val,
    g.rules.map (fun r => ((e r.1).val, r.2.map (encodeSymbol (⇑e)))))

/-- `toNT` is the identity (up to `Fin.val`) on indices already in range. -/
theorem toNT_val {G : EncodedCFG T} (A : Fin G.ntCount) : G.toNT A.val = A := by
  apply Fin.ext
  simp [EncodedCFG.toNT, Nat.mod_eq_of_lt A.isLt]

theorem encodeCFG_initial {k : ℕ} (g : CF_grammar T) (e : g.nt ≃ Fin (k + 1)) :
    (encodeCFG g e).toCFGrammar.initial = e g.initial :=
  toNT_val (G := encodeCFG g e) (e g.initial)

theorem encodeCFG_rules {k : ℕ} (g : CF_grammar T) (e : g.nt ≃ Fin (k + 1)) :
    (encodeCFG g e).toCFGrammar.rules = g.rules.map (lift_rule (⇑e)) := by
  show (encodeCFG g e).rawRules.map _ = _
  rw [show (encodeCFG g e).rawRules
        = g.rules.map (fun r => ((e r.1).val, r.2.map (encodeSymbol (⇑e)))) from rfl,
      List.map_map]
  apply List.map_congr_left
  intro r _
  obtain ⟨lhs, rhs⟩ := r
  refine Prod.ext ?_ ?_
  · exact toNT_val (G := encodeCFG g e) (e lhs)
  · show (rhs.map (encodeSymbol (⇑e))).map (encodeCFG g e).toSymbol = lift_string (⇑e) rhs
    rw [List.map_map]
    apply List.map_congr_left
    intro s _
    cases s with
    | terminal t => rfl
    | nonterminal m =>
      show (encodeCFG g e).toSymbol (Sum.inl (e m).val) = symbol.nonterminal (e m)
      simp [EncodedCFG.toSymbol, toNT_val]

/-! ## Soundness and completeness -/

/-- **Soundness:** every code denotes a context-free language. -/
public theorem contextFreeLanguageOf_isCF (G : EncodedCFG T) :
    contextFreeLanguageOf G ∈ CF := by
  rw [show (contextFreeLanguageOf G ∈ CF) = is_CF (contextFreeLanguageOf G) from rfl]
  exact is_CF_via_cfg_implies_is_CF ⟨G.toCFGrammar, rfl⟩

/-- The language of the encoding of a finite-nonterminal grammar is the grammar's
language. -/
theorem cf_language_encodeCFG {k : ℕ} (g : CF_grammar T) (e : g.nt ≃ Fin (k + 1)) :
    CF_language (encodeCFG g e).toCFGrammar = CF_language g := by
  apply cf_language_eq_of_rename e
  · exact encodeCFG_initial g e
  · intro r hr
    rw [encodeCFG_rules]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  · intro r hr
    rw [encodeCFG_rules] at hr
    exact List.mem_map.mp hr

/-- **Completeness:** every context-free language is denoted by some code. -/
public theorem contextFreeLanguageOf_complete (L : Language T) (hL : L ∈ CF) :
    ∃ G : EncodedCFG T, contextFreeLanguageOf G = L := by
  classical
  rw [show (L ∈ CF) = is_CF L from rfl, is_CF_iff_isContextFree] at hL
  obtain ⟨gml, hfin, hlang⟩ := ContextFreeGrammar.exists_fintype_nt L hL
  set g : CF_grammar T := cfg_of_mathlib_cfg gml with hg
  have hg_lang : CF_language g = L := by
    rw [hg, ← mathlib_language_eq_CF_language]; exact hlang
  letI : Fintype g.nt := hfin
  have hpos : 0 < Fintype.card g.nt := Fintype.card_pos_iff.mpr ⟨g.initial⟩
  let e : g.nt ≃ Fin (Fintype.card g.nt - 1 + 1) :=
    (Fintype.equivFin g.nt).trans (finCongr (Nat.succ_pred_eq_of_pos hpos).symm)
  refine ⟨encodeCFG g e, ?_⟩
  show CF_language (encodeCFG g e).toCFGrammar = L
  rw [cf_language_encodeCFG g e]
  exact hg_lang

/-- **`EncodedCFG` characterizes the context-free languages** (the library's class `CF`). -/
public theorem contextFreeLanguageOf_characterizes :
    Characterizes CF (contextFreeLanguageOf : EncodedCFG T → Language T) := by
  intro L
  exact ⟨fun hL => contextFreeLanguageOf_complete L hL,
    fun ⟨G, hG⟩ => hG ▸ contextFreeLanguageOf_isCF G⟩

end ContextFree.EncodedCFG
