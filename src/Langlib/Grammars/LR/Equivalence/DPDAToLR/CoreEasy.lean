module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CoreSyntax
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.AcceptingPaths

/-!
# Syntactic characteristic-rule collision cases

These are the LR-core cases decided solely by the rigid characteristic rule
shapes.  They deliberately do not use the operational cut invariant needed
for collisions between transition rules (or between two empty-list rules).
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A post-handle form with no `list` symbol cannot equal one whose rule
right side ends in a `list` symbol.  This disposes of every base/nonbase pair. -/
public theorem base_nonbase_post_impossible (M : DPDA Q T S)
    {plain pre : List (symbol T (Nonterminal M))}
    {suffixPlain suffixList : List T}
    {q target : State M} {gamma : List (StackSymbol M)}
    (hplain : ∀ X ∈ plain, ¬ IsListSymbol M X)
    (heq : plain ++ suffixPlain.map symbol.terminal =
      pre ++
        [symbol.nonterminal (PDA_to_CFG.N.list q gamma target)] ++
          suffixList.map symbol.terminal) : False := by
  apply no_marker_ne_append_marker
    (P := IsListSymbol M)
    (plain := plain ++ suffixPlain.map symbol.terminal)
    (left := pre)
    (right := suffixList.map symbol.terminal)
  · intro X hX
    simp only [List.mem_append] at hX
    rcases hX with hp | hs
    · exact hplain X hp
    · exact terminals_noList M suffixPlain X hs
  · exact isListSymbol_list M q target gamma
  · simpa [List.append_assoc] using heq

/-- Two split rules with equal post-handle forms have the same handle
position and are literally the same production. -/
public theorem split_split_collision (M : DPDA Q T S)
    {p₁ p₂ : List (symbol T (Nonterminal M))} {s₂ y : List T}
    {q₁ q₂ middle₁ middle₂ target₁ target₂ : State M}
    {Z₁ Z₂ : StackSymbol M}
    {alpha₁ alpha₂ : List (StackSymbol M)}
    (hp₁ : PendingPrefix M p₁) (hp₂ : PendingPrefix M p₂)
    (heq :
      p₂ ++
          [symbol.nonterminal (PDA_to_CFG.N.single q₂ Z₂ middle₂),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle₂ alpha₂ target₂)] ++
          s₂.map symbol.terminal =
        p₁ ++
          [symbol.nonterminal (PDA_to_CFG.N.single q₁ Z₁ middle₁),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle₁ alpha₁ target₁)] ++
          y.map symbol.terminal) :
    p₁ = p₂ ∧
      ((PDA_to_CFG.N.list q₁ (Z₁ :: alpha₁) target₁,
          [symbol.nonterminal (PDA_to_CFG.N.single q₁ Z₁ middle₁),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle₁ alpha₁ target₁)]) :
        Nonterminal M × List (symbol T (Nonterminal M))) =
        ((PDA_to_CFG.N.list q₂ (Z₂ :: alpha₂) target₂,
          [symbol.nonterminal (PDA_to_CFG.N.single q₂ Z₂ middle₂),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle₂ alpha₂ target₂)]) :
        Nonterminal M × List (symbol T (Nonterminal M))) := by
  have heq' :
      (p₂ ++
          [symbol.nonterminal
            (PDA_to_CFG.N.single q₂ Z₂ middle₂)]) ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list middle₂ alpha₂ target₂)] ++
          s₂.map symbol.terminal =
        (p₁ ++
          [symbol.nonterminal
            (PDA_to_CFG.N.single q₁ Z₁ middle₁)]) ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list middle₁ alpha₁ target₁)] ++
          y.map symbol.terminal := by
    simpa [List.append_assoc] using heq
  obtain ⟨haction, hmiddle, halpha, htarget, _⟩ :=
    cancel_characteristic_list_marker M
      (hp₁.noList_append_single M q₁ middle₁ Z₁)
      (hp₂.noList_append_single M q₂ middle₂ Z₂) heq'
  obtain ⟨hp, hsingle⟩ := append_singleton_injective haction
  have hN : PDA_to_CFG.N.single q₂ Z₂ middle₂ =
      PDA_to_CFG.N.single q₁ Z₁ middle₁ :=
    symbol.nonterminal.inj hsingle
  injection hN with hq hZ hmiddle'
  subst q₂
  subst Z₂
  subst middle₂
  subst alpha₂
  subst target₂
  exact ⟨hp.symm, rfl⟩

/-- A read-rule prefix and a split-rule prefix cannot be equal: after
cancelling the final list marker, one ends in a terminal and the other in a
nonterminal. -/
public theorem read_split_post_impossible (M : DPDA Q T S)
    {pRead pSplit : List (symbol T (Nonterminal M))} {sRead sSplit : List T}
    {a : T} {q middle next targetRead targetSplit : State M}
    {Z : StackSymbol M}
    {alpha beta : List (StackSymbol M)}
    (hpRead : PendingPrefix M pRead) (hpSplit : PendingPrefix M pSplit)
    (heq :
      pSplit ++
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle beta targetSplit)] ++
          sSplit.map symbol.terminal =
        pRead ++
          [symbol.terminal a,
            symbol.nonterminal
              (PDA_to_CFG.N.list next alpha targetRead)] ++
          sRead.map symbol.terminal) : False := by
  have heq' :
      (pSplit ++
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)]) ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list middle beta targetSplit)] ++
          sSplit.map symbol.terminal =
        (pRead ++ [symbol.terminal a]) ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list next alpha targetRead)] ++
          sRead.map symbol.terminal := by
    simpa [List.append_assoc] using heq
  obtain ⟨haction, _, _, _, _⟩ := cancel_characteristic_list_marker M
    (hpRead.noList_append_terminal M a)
    (hpSplit.noList_append_single M q middle Z) heq'
  obtain ⟨_, hlast⟩ := append_singleton_injective haction
  cases hlast

/-- Symmetric orientation of `read_split_post_impossible`. -/
public theorem split_read_post_impossible (M : DPDA Q T S)
    {pRead pSplit : List (symbol T (Nonterminal M))} {sRead sSplit : List T}
    {a : T} {q middle next targetRead targetSplit : State M}
    {Z : StackSymbol M}
    {alpha beta : List (StackSymbol M)}
    (hpRead : PendingPrefix M pRead) (hpSplit : PendingPrefix M pSplit)
    (heq :
      pRead ++
          [symbol.terminal a,
            symbol.nonterminal
              (PDA_to_CFG.N.list next alpha targetRead)] ++
          sRead.map symbol.terminal =
        pSplit ++
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle beta targetSplit)] ++
          sSplit.map symbol.terminal) : False := by
  exact read_split_post_impossible M hpRead hpSplit heq.symm

/-- The untouched characteristic start occurrence fixes its entire
prehandle: there is no prefix and no terminal suffix. -/
public theorem start_prehandle_eq_nil (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {s : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal PDA_to_CFG.N.start] ++
        s.map symbol.terminal)) : p = [] ∧ s = [] := by
  rcases (characteristic_prehandle_classification M h).2 with
      hstart | hsingle | hlist
  · exact ⟨hstart.2.1, hstart.2.2⟩
  · rcases hsingle with ⟨q, target, Z, hbad⟩
    cases hbad
  · rcases hlist with ⟨q, target, gamma, hbad⟩
    cases hbad

/-- Every retained start rule targets the distinguished global drain state.
Productivity supplies a complete empty-stack run, and global accepting runs
cannot finish in a boot or simulation state. -/
public theorem retained_start_target_eq_drain (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules) {target : State M}
    (hrule : r =
      (PDA_to_CFG.N.start,
        [symbol.nonterminal (PDA_to_CFG.N.list
          (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target)])) :
    target = Sum.inr 1 := by
  have hmem : symbol.nonterminal (PDA_to_CFG.N.list
        (emptyStackPDA M).initial_state
        [(emptyStackPDA M).start_symbol] target) ∈ r.2 := by
    rw [hrule]
    simp
  have hprod := characteristic_rule_rhs_productive M hr hmem
  obtain ⟨w, hreach⟩ := reaches_of_productive_list M (by simp) hprod
  exact emptyStack_accepting_state_eq_drain M hreach

/-- In particular, the productive reduction retains at most one start
production. -/
public theorem retained_start_rules_unique (M : DPDA Q T S)
    {r₁ r₂ : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr₁ : r₁ ∈ (characteristicGrammar M).rules)
    (hr₂ : r₂ ∈ (characteristicGrammar M).rules)
    {target₁ target₂ : State M}
    (hshape₁ : r₁ =
      (PDA_to_CFG.N.start,
        [symbol.nonterminal (PDA_to_CFG.N.list
          (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target₁)]))
    (hshape₂ : r₂ =
      (PDA_to_CFG.N.start,
        [symbol.nonterminal (PDA_to_CFG.N.list
          (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target₂)])) :
    r₁ = r₂ := by
  have ht₁ := retained_start_target_eq_drain M hr₁ hshape₁
  have ht₂ := retained_start_target_eq_drain M hr₂ hshape₂
  rw [hshape₁, hshape₂, ht₁, ht₂]

/-- Two reachable start rules with equal post-handle forms coincide. -/
public theorem start_start_collision (M : DPDA Q T S)
    {p₁ p₂ : List (symbol T (Nonterminal M))} {s₁ s₂ y : List T}
    {target₁ target₂ : State M}
    (hd₁ : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p₁ ++ [symbol.nonterminal PDA_to_CFG.N.start] ++
        s₁.map symbol.terminal))
    (hd₂ : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p₂ ++ [symbol.nonterminal PDA_to_CFG.N.start] ++
        s₂.map symbol.terminal))
    (heq : p₂ ++
        [symbol.nonterminal (PDA_to_CFG.N.list
          (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target₂)] ++
          s₂.map symbol.terminal =
      p₁ ++
        [symbol.nonterminal (PDA_to_CFG.N.list
          (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target₁)] ++
          y.map symbol.terminal) :
    p₁ = p₂ ∧
      ((PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target₁)]) :
        Nonterminal M × List (symbol T (Nonterminal M))) =
        ((PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target₂)]) :
        Nonterminal M × List (symbol T (Nonterminal M))) := by
  obtain ⟨hp₁, _⟩ := start_prehandle_eq_nil M hd₁
  obtain ⟨hp₂, _⟩ := start_prehandle_eq_nil M hd₂
  subst p₁
  subst p₂
  obtain ⟨_, _, _, htarget, _⟩ :=
    cancel_characteristic_list_marker M
      (fun X hX => by simp at hX)
      (fun X hX => by simp at hX) heq
  subst target₂
  exact ⟨rfl, rfl⟩

/-- A start-rule postform cannot coincide with a read or split postform:
the start occurrence has empty prefix, whereas those rule right sides put one
non-list symbol before their final list marker. -/
public theorem start_nonempty_action_post_impossible (M : DPDA Q T S)
    {pStart pOther : List (symbol T (Nonterminal M))}
    {sStart sOther : List T} {X : symbol T (Nonterminal M)}
    {qStart qOther targetStart targetOther : State M}
    {gammaStart gammaOther : List (StackSymbol M)}
    (hdStart : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (pStart ++ [symbol.nonterminal PDA_to_CFG.N.start] ++
        sStart.map symbol.terminal))
    (hpOther : PendingPrefix M pOther)
    (hX : ¬ IsListSymbol M X)
    (heq :
      pOther ++ [X] ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list qOther gammaOther targetOther)] ++
          sOther.map symbol.terminal =
        pStart ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list qStart gammaStart targetStart)] ++
          sStart.map symbol.terminal) : False := by
  obtain ⟨hpStart, _⟩ := start_prehandle_eq_nil M hdStart
  subst pStart
  have hleftOther : ∀ Y ∈ pOther ++ [X], ¬ IsListSymbol M Y := by
    intro Y hY
    simp only [List.mem_append, List.mem_singleton] at hY
    rcases hY with hpY | rfl
    · exact hpOther.noList M Y hpY
    · exact hX
  have heq' :
      (pOther ++ [X]) ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list qOther gammaOther targetOther)] ++
          sOther.map symbol.terminal =
        ([] : List (symbol T (Nonterminal M))) ++
          [symbol.nonterminal
            (PDA_to_CFG.N.list qStart gammaStart targetStart)] ++
          sStart.map symbol.terminal := by
    simpa [List.append_assoc] using heq
  obtain ⟨haction, _, _, _, _⟩ := cancel_characteristic_list_marker M
    (fun Y hY => by simp at hY)
    hleftOther heq'
  simp at haction

end

end DPDA_to_LR
