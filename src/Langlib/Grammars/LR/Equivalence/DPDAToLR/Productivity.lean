module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Paths
public import Langlib.Grammars.LR.Rightmost

/-!
# Productive completion of characteristic right-sentential forms

Every retained characteristic rule is fully productive.  Consequently every
nonterminal in a reachable right-sentential form can be completed, and the
completion can be scheduled rightmost.  These facts let the LR proof extend a
candidate handle to a genuine accepting computation.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Productivity is unchanged by the productive-rule filter. -/
public theorem productive_characteristic_iff_raw (M : DPDA Q T S)
    {A : (characteristicGrammar M).nt} :
    productive (characteristicGrammar M) A ↔
      productive (rawCharacteristicGrammar M) A := by
  exact productive_iff_productiveGrammar.symm

/-- The left side of every retained rule is productive in the reduced
grammar. -/
public theorem characteristic_rule_lhs_productive_reduced (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules) :
    productive (characteristicGrammar M) r.1 :=
  (productive_characteristic_iff_raw M).mpr
    (characteristic_rule_lhs_productive M hr)

/-- Every nonterminal on the right side of a retained rule is productive in
the reduced grammar. -/
public theorem characteristic_rule_rhs_productive_reduced (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules)
    {A : (characteristicGrammar M).nt}
    (hA : symbol.nonterminal A ∈ r.2) :
    productive (characteristicGrammar M) A :=
  productiveGrammar_allRulesFullyProductive
    (rawCharacteristicGrammar M) r hr A hA

/-- A list whose nonterminals are productive has a terminal rightmost
completion. -/
public theorem derivesRightmost_terminal_of_all_productive
    (G : CF_grammar T) {u : List (symbol T G.nt)}
    (hprod : ∀ A, symbol.nonterminal A ∈ u → productive G A) :
    ∃ w : List T,
      G.DerivesRightmost u (w.map symbol.terminal) := by
  induction u with
  | nil => exact ⟨[], Relation.ReflTransGen.refl⟩
  | cons x u ih =>
      have htail : ∀ A, symbol.nonterminal A ∈ u → productive G A := by
        intro A hA
        exact hprod A (by simp [hA])
      obtain ⟨wu, hu⟩ := ih htail
      cases x with
      | terminal t =>
          have ht : G.DerivesRightmost
              [symbol.terminal t] ([t].map symbol.terminal) :=
            Relation.ReflTransGen.refl
          refine ⟨t :: wu, ?_⟩
          simpa [List.map_append] using ht.append_to_terminals hu
      | nonterminal A =>
          obtain ⟨wA, hA⟩ := hprod A (by simp)
          have hA' := CF_grammar.derivesRightmost_of_derives hA
          refine ⟨wA ++ wu, ?_⟩
          simpa [List.map_append] using hA'.append_to_terminals hu

/-- Full productivity is invariant under a derivation when every rule has a
fully productive right side. -/
private theorem all_productive_of_derivesRightmost
    (G : CF_grammar T)
    (hrules : ∀ (r : G.nt × List (symbol T G.nt)), r ∈ G.rules →
      ∀ A, symbol.nonterminal A ∈ r.2 → productive G A)
    {u v : List (symbol T G.nt)}
    (hu : ∀ A, symbol.nonterminal A ∈ u → productive G A)
    (hderive : G.DerivesRightmost u v) :
    ∀ A, symbol.nonterminal A ∈ v → productive G A := by
  induction hderive with
  | refl => exact hu
  | @tail v w hprev hstep ih =>
      rcases hstep with ⟨r, hr, p, s, hv, hw⟩
      intro A hA
      rw [hw] at hA
      simp only [List.mem_append] at hA
      rcases hA with (hp | hrhs) | hs
      · apply ih A
        rw [hv]
        simp [hp]
      · exact hrules r hr A hrhs
      · simp at hs

/-- A reachable prehandle witnesses productivity of the grammar's initial
nonterminal.  In the reflexive case the displayed handle itself is initial;
otherwise the first rule of the derivation is headed by the initial symbol. -/
private theorem characteristic_initial_productive_of_prehandle
    (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules)
    {p : List (symbol T (characteristicGrammar M).nt)} {s : List T}
    (hderive : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal r.1] ++ s.map symbol.terminal)) :
    productive (characteristicGrammar M)
      (characteristicGrammar M).initial := by
  rcases Relation.ReflTransGen.cases_head hderive with heq | hnonempty
  · have hmem : symbol.nonterminal (T := T) r.1 ∈
        [symbol.nonterminal (T := T) (characteristicGrammar M).initial] := by
      rw [heq]
      simp
    have hrinit : r.1 = (characteristicGrammar M).initial := by
      simpa using hmem
    rw [← hrinit]
    exact characteristic_rule_lhs_productive_reduced M hr
  · obtain ⟨v, hfirst, _⟩ := hnonempty
    rcases hfirst with ⟨r₀, hr₀, p₀, s₀, hsource, _⟩
    have hmem : symbol.nonterminal (T := T) r₀.1 ∈
        [symbol.nonterminal (T := T) (characteristicGrammar M).initial] := by
      rw [hsource]
      simp
    have hrinit : r₀.1 = (characteristicGrammar M).initial := by
      simpa using hmem
    rw [← hrinit]
    exact characteristic_rule_lhs_productive_reduced M hr₀

/-- Every nonterminal in a reachable characteristic prehandle is productive. -/
public theorem prehandle_all_nonterminals_productive (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules)
    {p : List (symbol T (characteristicGrammar M).nt)} {s : List T}
    (hderive : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal r.1] ++ s.map symbol.terminal)) :
    ∀ A, symbol.nonterminal A ∈
        (p ++ [symbol.nonterminal r.1] ++ s.map symbol.terminal) →
      productive (characteristicGrammar M) A := by
  apply all_productive_of_derivesRightmost (characteristicGrammar M)
    (fun rule hRule A hA =>
      characteristic_rule_rhs_productive_reduced M hRule hA)
    ?_ hderive
  intro A hA
  have hAeq : A = (characteristicGrammar M).initial := by
    simpa using hA
  subst A
  exact characteristic_initial_productive_of_prehandle M hr hderive

/-- The prefix before a reachable handle has a terminal rightmost completion. -/
public theorem prehandle_prefix_completion (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules)
    {p : List (symbol T (characteristicGrammar M).nt)} {s : List T}
    (hderive : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal r.1] ++ s.map symbol.terminal)) :
    ∃ w : List T,
      (characteristicGrammar M).DerivesRightmost p
        (w.map symbol.terminal) := by
  apply derivesRightmost_terminal_of_all_productive
  intro A hA
  exact prehandle_all_nonterminals_productive M hr hderive A (by simp [hA])

/-- The right side of a retained rule has a terminal rightmost completion. -/
public theorem characteristic_rule_rhs_completion (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules) :
    ∃ w : List T,
      (characteristicGrammar M).DerivesRightmost r.2
        (w.map symbol.terminal) := by
  apply derivesRightmost_terminal_of_all_productive
  intro A hA
  exact characteristic_rule_rhs_productive_reduced M hr hA

/-- Applying a reachable rule and completing its result yields a terminal
rightmost derivation. -/
public theorem prehandle_post_completion (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules)
    {p : List (symbol T (characteristicGrammar M).nt)} {s : List T}
    (hderive : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal r.1] ++ s.map symbol.terminal)) :
    ∃ w : List T,
      (characteristicGrammar M).DerivesRightmost
        (p ++ r.2 ++ s.map symbol.terminal)
        (w.map symbol.terminal) := by
  apply derivesRightmost_terminal_of_all_productive
  intro A hA
  simp only [List.mem_append] at hA
  rcases hA with (hp | hrhs) | hs
  · exact prehandle_all_nonterminals_productive M hr hderive A (by simp [hp])
  · exact characteristic_rule_rhs_productive_reduced M hr hrhs
  · simp at hs

end

end DPDA_to_LR
