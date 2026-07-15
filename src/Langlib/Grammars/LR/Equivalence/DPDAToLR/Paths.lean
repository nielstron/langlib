module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Rules

/-!
# Computation semantics of productive characteristic nonterminals

The PDA-to-CFG correctness theorem is stated for Mathlib's grammar and for
leftmost derivations.  The reduced LR grammar, however, records productivity
using Langlib's grammar representation.  This file bridges those interfaces
and turns productivity of a characteristic nonterminal into an actual
net-pop computation of the normalized empty-stack PDA.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

@[simp]
private theorem upper_lower_symbols (w : List (Symbol T N)) :
    lsSymbol_of_lssymbol (lssymbol_of_lsSymbol w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change Symbol_of_symbol (symbol_of_Symbol a) ::
        lsSymbol_of_lssymbol (lssymbol_of_lsSymbol w) = a :: w
      cases a <;> simp [Symbol_of_symbol, symbol_of_Symbol, ih]

/-- Translate an arbitrary Langlib CFG derivation to the corresponding
Mathlib CFG derivation.  The library's language-equivalence theorem only
exposes the special case starting at the initial nonterminal, so the general
form is recorded here. -/
public theorem mathlib_derives_of_CF_derives (g : CF_grammar T)
    {u v : List (symbol T g.nt)}
    (h : CF_derives g u v) :
    (mathlib_cfg_of_cfg g).Derives
      (lsSymbol_of_lssymbol u) (lsSymbol_of_lssymbol v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      apply ContextFreeGrammar.Derives.trans_produces ih
      rcases hstep with ⟨r, x, y, hr, hu, hv⟩
      refine ⟨⟨r.1, lsSymbol_of_lssymbol r.2⟩, ?_, ?_⟩
      · simp only [mathlib_cfg_of_cfg, List.mem_toFinset,
          List.mem_map]
        exact ⟨r, hr, rfl⟩
      · rw [hu, hv]
        simpa [lsSymbol_of_lssymbol, List.map_append] using
          (ContextFreeRule.rewrites_of_exists_parts
            (⟨r.1, lsSymbol_of_lssymbol r.2⟩ :
              ContextFreeRule T g.nt)
            (lsSymbol_of_lssymbol x) (lsSymbol_of_lssymbol y))

/-- A raw characteristic derivation is a derivation in the original Mathlib
characteristic grammar. -/
public theorem characteristic_mathlib_derives_of_raw (M : DPDA Q T S)
    {u v : List (symbol T (rawCharacteristicGrammar M).nt)}
    (h : CF_derives (rawCharacteristicGrammar M) u v) :
    (mathlibCharacteristicGrammar M).Derives
      (lsSymbol_of_lssymbol u) (lsSymbol_of_lssymbol v) := by
  have hm := mathlib_derives_of_CF_derives (rawCharacteristicGrammar M) h
  change (mathlib_cfg_of_cfg
    (cfg_of_mathlib_cfg (mathlibCharacteristicGrammar M))).Derives
      (lsSymbol_of_lssymbol u) (lsSymbol_of_lssymbol v) at hm
  have hrules :
      (mathlib_cfg_of_cfg
        (cfg_of_mathlib_cfg (mathlibCharacteristicGrammar M))).rules =
      (mathlibCharacteristicGrammar M).rules := by
    classical
    ext r
    simp [mathlib_cfg_of_cfg, cfg_of_mathlib_cfg, List.mem_map,
      upper_lower_symbols]
  apply Relation.ReflTransGen.mono (r :=
    (mathlib_cfg_of_cfg
      (cfg_of_mathlib_cfg (mathlibCharacteristicGrammar M))).Produces)
    (p := (mathlibCharacteristicGrammar M).Produces) ?_ hm
  intro a b hstep
  rcases hstep with ⟨r, hr, hrewrite⟩
  rw [hrules] at hr
  exact ⟨r, hr, hrewrite⟩

/-- A terminal derivation of a characteristic list nonterminal realizes the
net-pop computation encoded by that nonterminal. -/
public theorem reaches_of_mathlib_derives_list (M : DPDA Q T S)
    {q p : State M} {γ : List (StackSymbol M)} {w : List T}
    (hγ : γ.length ≤ PDA_to_CFG.max_push (emptyStackPDA M))
    (hderive : (mathlibCharacteristicGrammar M).Derives
      [Symbol.nonterminal (PDA_to_CFG.N.list q γ p)]
      (w.map Symbol.terminal)) :
    (emptyStackPDA M).Reaches ⟨q, w, γ⟩ ⟨p, [], []⟩ := by
  have hleftmost : (mathlibCharacteristicGrammar M).DerivesLeftmost
      [Symbol.nonterminal (PDA_to_CFG.N.list q γ p)]
      (w.map Symbol.terminal) :=
    ContextFreeGrammar.derives_leftmost_iff.mpr hderive
  obtain ⟨n, hn⟩ :=
    (ContextFreeGrammar.derivesLeftmost_iff_derivesLeftmostIn
      (mathlibCharacteristicGrammar M) _ _).mp hleftmost
  exact PDA_to_CFG.reachesIn_of_derivesLeftmostIn hγ hn

/-- Productivity of a list nonterminal gives a concrete net-pop computation. -/
public theorem reaches_of_productive_list (M : DPDA Q T S)
    {q p : State M} {γ : List (StackSymbol M)}
    (hγ : γ.length ≤ PDA_to_CFG.max_push (emptyStackPDA M))
    (hprod : productive (rawCharacteristicGrammar M)
      (PDA_to_CFG.N.list q γ p)) :
    ∃ w : List T,
      (emptyStackPDA M).Reaches ⟨q, w, γ⟩ ⟨p, [], []⟩ := by
  obtain ⟨w, hw⟩ := hprod
  have hmath := characteristic_mathlib_derives_of_raw M hw
  refine ⟨w, reaches_of_mathlib_derives_list M hγ ?_⟩
  simpa [lsSymbol_of_lssymbol, List.map_map] using hmath

/-- Productivity of a single-symbol nonterminal gives its concrete net-pop
computation.  We reduce this to the existing correctness theorem for list
nonterminals by adjoining the split rule and the empty-list rule. -/
public theorem reaches_of_productive_single (M : DPDA Q T S)
    {q p : State M} {Z : StackSymbol M}
    (hprod : productive (rawCharacteristicGrammar M)
      (PDA_to_CFG.N.single q Z p)) :
    ∃ w : List T,
      (emptyStackPDA M).Reaches ⟨q, w, [Z]⟩ ⟨p, [], []⟩ := by
  obtain ⟨w, hw⟩ := hprod
  have hsingle := characteristic_mathlib_derives_of_raw M hw
  have hsingle' : (mathlibCharacteristicGrammar M).Derives
      [Symbol.nonterminal (PDA_to_CFG.N.single q Z p)]
      (w.map Symbol.terminal) := by
    simpa [lsSymbol_of_lssymbol, List.map_map] using hsingle
  have hsplit : (mathlibCharacteristicGrammar M).Derives
      [Symbol.nonterminal (PDA_to_CFG.N.list q [Z] p)]
      [Symbol.nonterminal (PDA_to_CFG.N.single q Z p),
        Symbol.nonterminal (PDA_to_CFG.N.list p [] p)] :=
    (PDA_to_CFG.produces_split q p p (by simp)).single
  have hepsilon : (mathlibCharacteristicGrammar M).Derives
      [Symbol.nonterminal (PDA_to_CFG.N.list p [] p)] [] :=
    (PDA_to_CFG.produces_epsilon p).single
  have hmiddle := hsingle'.append_right
    [Symbol.nonterminal (PDA_to_CFG.N.list p [] p)]
  have hlast := hepsilon.append_left (w.map Symbol.terminal)
  have hderive : (mathlibCharacteristicGrammar M).Derives
      [Symbol.nonterminal (PDA_to_CFG.N.list q [Z] p)]
      (w.map Symbol.terminal) := by
    simpa using hsplit.trans (hmiddle.trans hlast)
  exact ⟨w, reaches_of_mathlib_derives_list M (by simp) hderive⟩

/-- Both sides of every retained characteristic rule are productive in the
raw grammar. -/
public theorem characteristic_rule_lhs_productive (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules) :
    productive (rawCharacteristicGrammar M) r.1 :=
  (characteristic_rule_fullyProductive M hr).1

public theorem characteristic_rule_rhs_productive (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules)
    {A : (characteristicGrammar M).nt}
    (hA : symbol.nonterminal A ∈ r.2) :
    productive (rawCharacteristicGrammar M) A :=
  (characteristic_rule_fullyProductive M hr).2 A hA

end

end DPDA_to_LR
