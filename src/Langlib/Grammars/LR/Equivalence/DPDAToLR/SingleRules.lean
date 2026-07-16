module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Productivity
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.PredictiveUniqueness

/-!
# Productive transition rules

A retained rule headed by a characteristic `single` nonterminal is precisely
the first move of a net-pop computation.  This file packages that observation
with the *actual* terminal completion of the rule's right side.  It is the
local semantic ingredient in the reverse-handle argument: equal one-symbol
lookahead makes two productive rules for the same `single` nonterminal equal.
-/

@[expose]
public section

open Language
open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A terminal derivation in the reduced characteristic grammar is also a
derivation in the unreduced Mathlib characteristic grammar. -/
private theorem mathlib_derives_of_characteristic (M : DPDA Q T S)
    {u v : List (symbol T (characteristicGrammar M).nt)}
    (h : CF_derives (characteristicGrammar M) u v) :
    (mathlibCharacteristicGrammar M).Derives
      (lsSymbol_of_lssymbol u) (lsSymbol_of_lssymbol v) := by
  have hraw : CF_derives (rawCharacteristicGrammar M) u v := by
    apply CF_derives_mono
      (g := rawCharacteristicGrammar M)
      (rules₁ := (characteristicGrammar M).rules)
      (rules₂ := (rawCharacteristicGrammar M).rules)
    · intro r hr
      simp only [characteristicGrammar, productiveGrammar,
        List.mem_filter, decide_eq_true_eq] at hr
      exact hr.1
    · exact h
  exact characteristic_mathlib_derives_of_raw M hraw

/-- An exact terminal completion of a retained list nonterminal realizes its
encoded net-pop computation. -/
public theorem reaches_of_characteristic_derives_list (M : DPDA Q T S)
    {q p : State M} {gamma : List (StackSymbol M)} {w : List T}
    (hgamma : gamma.length ≤ PDA_to_CFG.max_push (emptyStackPDA M))
    (hderive : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.list q gamma p)]
      (w.map symbol.terminal)) :
    (emptyStackPDA M).Reaches
      ⟨q, w, gamma⟩ ⟨p, [], []⟩ := by
  have hmath := mathlib_derives_of_characteristic M
    (CF_grammar.derives_of_derivesRightmost hderive)
  apply reaches_of_mathlib_derives_list M hgamma
  simpa [lsSymbol_of_lssymbol, List.map_map] using hmath

/-- An exact terminal completion of a retained `single` nonterminal realizes
the corresponding one-symbol net-pop computation. -/
public theorem reaches_of_characteristic_derives_single (M : DPDA Q T S)
    {q p : State M} {Z : StackSymbol M} {w : List T}
    (hderive : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.single q Z p)]
      (w.map symbol.terminal)) :
    (emptyStackPDA M).Reaches
      ⟨q, w, [Z]⟩ ⟨p, [], []⟩ := by
  have hsingle := mathlib_derives_of_characteristic M
    (CF_grammar.derives_of_derivesRightmost hderive)
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
  have hderive' : (mathlibCharacteristicGrammar M).Derives
      [Symbol.nonterminal (PDA_to_CFG.N.list q [Z] p)]
      (w.map Symbol.terminal) := by
    simpa using hsplit.trans (hmiddle.trans hlast)
  exact reaches_of_mathlib_derives_list M (by simp) hderive'

private theorem terminal_single_completion_eq (G : CF_grammar T)
    {a : T} {w : List T}
    (h : G.DerivesRightmost [symbol.terminal a]
      (w.map symbol.terminal)) :
    w = [a] := by
  have h' : G.DerivesRightmost
      ([a].map (symbol.terminal (N := G.nt)))
      (w.map symbol.terminal) := by
    simpa using h
  have heq := h'.eq_of_map_terminal_source
  have hinj : Function.Injective
      (symbol.terminal (T := T) (N := G.nt)) :=
    fun _ _ h => symbol.terminal.inj h
  have hmaps : w.map (symbol.terminal (N := G.nt)) =
      [a].map symbol.terminal := by
    simpa using heq
  exact (List.map_injective_iff.mpr hinj) hmaps

/-- A retained transition rule, together with a concrete terminal completion
of its right side, supplies its productive first-move signature. -/
public theorem productiveFirstMove_of_single_rule (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules)
    {q target : State M} {Z : StackSymbol M}
    (hlhs : r.1 = PDA_to_CFG.N.single q Z target)
    {w : List T}
    (hcomplete : (characteristicGrammar M).DerivesRightmost
      r.2 (w.map symbol.terminal)) :
    ∃ sig : FirstMoveSignature M,
      ProductiveFirstMove M q Z w target sig ∧
      (match sig.consumes with
        | true => ∃ a tail,
            w = a :: tail ∧
            r.2 = [symbol.terminal a,
              symbol.nonterminal
                (PDA_to_CFG.N.list sig.nextState sig.replacement target)]
        | false =>
            r.2 = [symbol.nonterminal
              (PDA_to_CFG.N.list sig.nextState sig.replacement target)]) := by
  rcases characteristicGrammar_rule_shape M hr with
    hbase | hread | hepsilon | hsplit | hstart
  · rcases hbase with ⟨state, hrule⟩
    rw [hrule] at hlhs
    cases hlhs
  · rcases hread with
      ⟨q₀, p₀, q', a, Z₀, alpha, htransition, hrule⟩
    rw [hrule] at hlhs hcomplete ⊢
    injection hlhs with hq hZ hp
    subst q₀
    subst Z₀
    subst p₀
    change (characteristicGrammar M).DerivesRightmost
      ([symbol.terminal a] ++
        [symbol.nonterminal (PDA_to_CFG.N.list q' alpha target)])
      (w.map symbol.terminal) at hcomplete
    obtain ⟨wa, tail, hw, ha, htail⟩ :=
      CF_grammar.DerivesRightmost.append_to_terminals_split
        (G := characteristicGrammar M)
        (u := [symbol.terminal a])
        (v := [symbol.nonterminal
          (PDA_to_CFG.N.list q' alpha target)]) hcomplete
    have hwa : wa = [a] := terminal_single_completion_eq _ ha
    subst wa
    have hw' : w = a :: tail := by simpa using hw
    have hlen : alpha.length ≤
        PDA_to_CFG.max_push (emptyStackPDA M) := by
      apply PDA_to_CFG.push_le_max_push
      exact ⟨(q', alpha), htransition, rfl⟩
    have hreach := reaches_of_characteristic_derives_list M hlen htail
    refine ⟨⟨true, q', alpha⟩, ?_, ?_⟩
    · constructor
      · rw [hw']
        exact HasFirstMove.read a tail q' alpha htransition
      · simpa [inputAfter, hw'] using hreach
    · simp only
      exact ⟨a, tail, hw', rfl⟩
  · rcases hepsilon with
      ⟨q₀, p₀, q', Z₀, alpha, htransition, hrule⟩
    rw [hrule] at hlhs hcomplete ⊢
    injection hlhs with hq hZ hp
    subst q₀
    subst Z₀
    subst p₀
    have hlen : alpha.length ≤
        PDA_to_CFG.max_push (emptyStackPDA M) := by
      apply PDA_to_CFG.push_le_max_push'
      exact ⟨(q', alpha), htransition, rfl⟩
    have hreach := reaches_of_characteristic_derives_list M hlen hcomplete
    refine ⟨⟨false, q', alpha⟩, ?_, ?_⟩
    · constructor
      · exact HasFirstMove.epsilon w q' alpha htransition
      · simpa [inputAfter] using hreach
    · rfl
  · rcases hsplit with ⟨q₀, q', p₀, Z₀, alpha, _, hrule⟩
    rw [hrule] at hlhs
    cases hlhs
  · rcases hstart with ⟨p, hrule⟩
    rw [hrule] at hlhs
    cases hlhs

/-- Productive retained rules for the same `single` nonterminal are selected
uniquely by one terminal of their completed yields. -/
public theorem single_rule_unique_of_completion (M : DPDA Q T S)
    {r₁ r₂ : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr₁ : r₁ ∈ (characteristicGrammar M).rules)
    (hr₂ : r₂ ∈ (characteristicGrammar M).rules)
    {q target : State M} {Z : StackSymbol M}
    (hlhs₁ : r₁.1 = PDA_to_CFG.N.single q Z target)
    (hlhs₂ : r₂.1 = PDA_to_CFG.N.single q Z target)
    {x y : List T}
    (hx : (characteristicGrammar M).DerivesRightmost
      r₁.2 (x.map symbol.terminal))
    (hy : (characteristicGrammar M).DerivesRightmost
      r₂.2 (y.map symbol.terminal))
    (hlook : x.take 1 = y.take 1) :
    r₁ = r₂ := by
  obtain ⟨sig₁, hmove₁, hshape₁⟩ :=
    productiveFirstMove_of_single_rule M hr₁ hlhs₁ hx
  obtain ⟨sig₂, hmove₂, hshape₂⟩ :=
    productiveFirstMove_of_single_rule M hr₂ hlhs₂ hy
  have hsig : sig₁ = sig₂ :=
    productiveFirstMove_unique M hlook hmove₁ hmove₂
  subst sig₂
  apply Prod.ext
  · exact hlhs₁.trans hlhs₂.symm
  · cases hconsumes : sig₁.consumes with
    | false =>
        simp only [hconsumes] at hshape₁ hshape₂
        exact hshape₁.trans hshape₂.symm
    | true =>
        simp only [hconsumes] at hshape₁ hshape₂
        rcases hshape₁ with ⟨a₁, tail₁, hx', hrhs₁⟩
        rcases hshape₂ with ⟨a₂, tail₂, hy', hrhs₂⟩
        have ha : a₁ = a₂ := by
          rw [hx', hy'] at hlook
          simpa using congrArg List.head? hlook
        subst a₂
        exact hrhs₁.trans hrhs₂.symm

end

end DPDA_to_LR
