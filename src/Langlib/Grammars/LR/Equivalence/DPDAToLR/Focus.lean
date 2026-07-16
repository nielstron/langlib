module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SingleRules
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Frontiers

/-!
# Computation zipper for characteristic rightmost derivations

An occurrence in a right-sentential form has two pieces of operational
meaning.  A terminal completion of the symbols to its left drives the
empty-stack PDA from its initial configuration to the configuration encoded
by the occurrence.  A terminal completion of the symbols to its right drives
the saved stack context from the occurrence's target state to empty stack.
This is the formal partial-tree invariant used in Knuth's DPDA-to-LR proof.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Operational meaning of a focused characteristic nonterminal. -/
public inductive Focused (M : DPDA Q T S) :
    Nonterminal M → List T → List T → Prop
  | start : Focused M PDA_to_CFG.N.start [] []
  | single (q target : State M) (Z : StackSymbol M)
      (preWord postWord : List T) (context : List (StackSymbol M))
      (final : State M)
      (prefixPath : (emptyStackPDA M).Reaches
        ⟨(emptyStackPDA M).initial_state, preWord,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q, [], Z :: context⟩)
      (continuation : (emptyStackPDA M).Reaches
        ⟨target, postWord, context⟩ ⟨final, [], []⟩) :
      Focused M (PDA_to_CFG.N.single q Z target) preWord postWord
  | list (q target : State M) (gamma : List (StackSymbol M))
      (preWord postWord : List T) (context : List (StackSymbol M))
      (final : State M)
      (prefixPath : (emptyStackPDA M).Reaches
        ⟨(emptyStackPDA M).initial_state, preWord,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q, [], gamma ++ context⟩)
      (continuation : (emptyStackPDA M).Reaches
        ⟨target, postWord, context⟩ ⟨final, [], []⟩) :
      Focused M (PDA_to_CFG.N.list q gamma target) preWord postWord

private theorem terminal_word_eq_of_derives (G : CF_grammar T)
    {u v : List T}
    (h : G.DerivesRightmost (u.map symbol.terminal)
      (v.map symbol.terminal)) :
    u = v := by
  have heq := h.eq_of_map_terminal_source
  exact (List.map_injective_iff.mpr fun _ _ h =>
    symbol.terminal.inj h) heq.symm

private theorem decompose_one_nonterminal
    {N : Type} {A B : N}
    {left right : List (symbol T N)}
    (h : [symbol.nonterminal B] =
      left ++ [symbol.nonterminal A] ++ right) :
    left = [] ∧ A = B ∧ right = [] := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact ⟨rfl, (symbol.nonterminal.inj h.1).symm, h.2.symm⟩
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      have hbad : left ++ symbol.nonterminal A :: right = [] := by
        simpa using h.2.symm
      simp at hbad

private theorem decompose_terminal_nonterminal
    {N : Type} {a : T} {A B : N}
    {left right : List (symbol T N)}
    (h : [symbol.terminal a, symbol.nonterminal B] =
      left ++ [symbol.nonterminal A] ++ right) :
    left = [symbol.terminal a] ∧ A = B ∧ right = [] := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      cases h.1
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨hleft, hA, hright⟩ :=
        decompose_one_nonterminal htail
      subst left
      exact ⟨rfl, hA, hright⟩

private theorem decompose_two_nonterminals
    {N : Type} {A B C : N}
    {left right : List (symbol T N)}
    (h : [symbol.nonterminal B, symbol.nonterminal C] =
      left ++ [symbol.nonterminal A] ++ right) :
    (left = [] ∧ A = B ∧
      right = [symbol.nonterminal C]) ∨
    (left = [symbol.nonterminal B] ∧ A = C ∧ right = []) := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      left
      exact ⟨rfl, (symbol.nonterminal.inj h.1).symm, h.2.symm⟩
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨hleft, hA, hright⟩ :=
        decompose_one_nonterminal htail
      subst left
      right
      exact ⟨rfl, hA, hright⟩

/-- The computation-zipper invariant for an arbitrary focused occurrence.
The strings on both sides may be scheduled to terminals independently; their
terminal yields are exactly the input consumed before the focus and the input
handled by its saved continuation. -/
public theorem focused_of_derivation (M : DPDA Q T S)
    {form p right : List (symbol T (Nonterminal M))}
    {A : Nonterminal M} {preWord postWord : List T}
    (hroot : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial] form)
    (hshape : form = p ++ [symbol.nonterminal A] ++ right)
    (hp : (characteristicGrammar M).DerivesRightmost
      p (preWord.map symbol.terminal))
    (hright : (characteristicGrammar M).DerivesRightmost
      right (postWord.map symbol.terminal)) :
    Focused M A preWord postWord := by
  induction hroot generalizing p A right preWord postWord with
  | refl =>
      rw [characteristicGrammar_initial] at hshape
      cases p with
      | cons X p => simp at hshape
      | nil =>
          simp only [List.nil_append, List.cons_append,
            List.cons.injEq] at hshape
          obtain ⟨hA, hrightNil⟩ := hshape
          have hA : A = PDA_to_CFG.N.start :=
            (symbol.nonterminal.inj hA).symm
          subst A
          have hpNil : preWord = [] := by
            have hp' : (characteristicGrammar M).DerivesRightmost
                (([] : List T).map symbol.terminal)
                (preWord.map symbol.terminal) := by
              simpa using hp
            exact (terminal_word_eq_of_derives
              (characteristicGrammar M) hp').symm
          have hsNil : postWord = [] := by
            rw [← hrightNil] at hright
            have hright' : (characteristicGrammar M).DerivesRightmost
                (([] : List T).map symbol.terminal)
                (postWord.map symbol.terminal) := by
              simpa using hright
            exact (terminal_word_eq_of_derives
              (characteristicGrammar M) hright').symm
          subst preWord
          subst postWord
          exact Focused.start
  | @tail before form hprevious hstep ih =>
      have hstep' : (characteristicGrammar M).ProducesRightmost before
          (p ++ [symbol.nonterminal A] ++ right) := by
        rw [← hshape]
        exact hstep
      rcases hstep'.preimage_nonterminal with hsurvives | hintroduced
      · rcases hsurvives with ⟨right₀, hbefore, hrightStep⟩
        exact ih hbefore hp (hrightStep.single.trans hright)
      · rcases hintroduced with
          ⟨r, hr, p₀, left, beta, trailing, hrhs,
            hpShape, hrightShape, hbefore⟩
        have hp' : (characteristicGrammar M).DerivesRightmost
            (p₀ ++ left) (preWord.map symbol.terminal) := by
          rw [← hpShape]
          exact hp
        obtain ⟨pre₀, leftWord, hpreWord, hp₀, hleft⟩ :=
          CF_grammar.DerivesRightmost.append_to_terminals_split hp'
        have hright' : (characteristicGrammar M).DerivesRightmost
            (beta ++ trailing.map symbol.terminal)
            (postWord.map symbol.terminal) := by
          rw [← hrightShape]
          exact hright
        obtain ⟨betaWord, trailingWord, hpostWord, hbeta, htrailing⟩ :=
          CF_grammar.DerivesRightmost.append_to_terminals_split hright'
        have htrailingWord : trailingWord = trailing :=
          (terminal_word_eq_of_derives _ htrailing).symm
        subst trailingWord
        have hparent : Focused M r.1 pre₀ trailing :=
          ih hbefore hp₀ Relation.ReflTransGen.refl
        rcases characteristicGrammar_rule_shape M hr with
          hbase | hread | hepsilon | hsplit | hstart
        · rcases hbase with ⟨q, rfl⟩
          simp at hrhs
        · rcases hread with
            ⟨q, target, q', a, Z, alpha, htransition, rfl⟩
          obtain ⟨hleftShape, hA, hbetaShape⟩ :=
            decompose_terminal_nonterminal hrhs
          subst A
          rw [hleftShape] at hleft
          have hleftWord : leftWord = [a] :=
            (terminal_word_eq_of_derives _ hleft).symm
          subst leftWord
          rw [hbetaShape] at hbeta
          have hbetaWord : betaWord = [] :=
            (terminal_word_eq_of_derives _ hbeta).symm
          subst betaWord
          rw [hpreWord, hpostWord]
          simp only [List.nil_append]
          cases hparent with
          | single _ _ _ _ _ context final prefixPath continuation =>
              have prefixPath' :=
                (PDA.unconsumed_input [a]).mp prefixPath
              have firstStep : (emptyStackPDA M).Reaches
                  ⟨q, [a], Z :: context⟩
                  ⟨q', [], alpha ++ context⟩ := by
                apply Relation.ReflTransGen.single
                exact Or.inl ⟨q', alpha, htransition, by simp⟩
              apply Focused.list q' target alpha
                (pre₀ ++ [a]) trailing context final
              · simpa [PDA.conf.appendInput] using
                  prefixPath'.trans firstStep
              · exact continuation
        · rcases hepsilon with
            ⟨q, target, q', Z, alpha, htransition, rfl⟩
          obtain ⟨hleftShape, hA, hbetaShape⟩ :=
            decompose_one_nonterminal hrhs
          subst A
          rw [hleftShape] at hleft
          have hleftWord : leftWord = [] :=
            (terminal_word_eq_of_derives _ hleft).symm
          subst leftWord
          rw [hbetaShape] at hbeta
          have hbetaWord : betaWord = [] :=
            (terminal_word_eq_of_derives _ hbeta).symm
          subst betaWord
          rw [hpreWord, hpostWord]
          simp only [List.append_nil, List.nil_append]
          cases hparent with
          | single _ _ _ _ _ context final prefixPath continuation =>
              have firstStep : (emptyStackPDA M).Reaches
                  ⟨q, [], Z :: context⟩
                  ⟨q', [], alpha ++ context⟩ := by
                apply Relation.ReflTransGen.single
                exact ⟨q', alpha, htransition, by simp⟩
              apply Focused.list q' target alpha
                pre₀ trailing context final
              · exact prefixPath.trans firstStep
              · exact continuation
        · rcases hsplit with
            ⟨q, middle, target, Z, alpha, hlength, rfl⟩
          rcases decompose_two_nonterminals hrhs with hfirst | hsecond
          · rcases hfirst with ⟨hleftShape, hA, hbetaShape⟩
            subst A
            rw [hleftShape] at hleft
            have hleftWord : leftWord = [] :=
              (terminal_word_eq_of_derives _ hleft).symm
            subst leftWord
            rw [hbetaShape] at hbeta
            have hlen : alpha.length ≤
                PDA_to_CFG.max_push (emptyStackPDA M) := by
              rw [List.length_cons] at hlength
              apply le_trans
              · exact WithBot.coe_le_coe.mpr (Nat.le_succ alpha.length)
              · exact hlength
            have hrightPath :=
              reaches_of_characteristic_derives_list M hlen hbeta
            rw [hpreWord, hpostWord]
            simp only [List.append_nil]
            cases hparent with
            | list _ _ _ _ _ context final prefixPath continuation =>
                have hrightContext := hrightPath.append_stack context
                have hrightInput :=
                  (PDA.unconsumed_input trailing).mp hrightContext
                apply Focused.single q middle Z pre₀
                  (betaWord ++ trailing) (alpha ++ context) final
                · simpa [List.append_assoc] using prefixPath
                · exact hrightInput.trans continuation
          · rcases hsecond with ⟨hleftShape, hA, hbetaShape⟩
            subst A
            rw [hleftShape] at hleft
            have hleftPath :=
              reaches_of_characteristic_derives_single M hleft
            rw [hbetaShape] at hbeta
            have hbetaWord : betaWord = [] :=
              (terminal_word_eq_of_derives _ hbeta).symm
            subst betaWord
            rw [hpreWord, hpostWord]
            simp only [List.nil_append]
            cases hparent with
            | list _ _ _ _ _ context final prefixPath continuation =>
                have prefixPath' :=
                  (PDA.unconsumed_input leftWord).mp prefixPath
                have hleftContext :=
                  hleftPath.append_stack (alpha ++ context)
                apply Focused.list middle target alpha
                  (pre₀ ++ leftWord) trailing context final
                · simpa [List.append_assoc, PDA.conf.appendInput] using
                    prefixPath'.trans hleftContext
                · exact continuation
        · rcases hstart with ⟨target, rfl⟩
          obtain ⟨hleftShape, hA, hbetaShape⟩ :=
            decompose_one_nonterminal hrhs
          subst A
          rw [hleftShape] at hleft
          have hleftWord : leftWord = [] :=
            (terminal_word_eq_of_derives _ hleft).symm
          subst leftWord
          rw [hbetaShape] at hbeta
          have hbetaWord : betaWord = [] :=
            (terminal_word_eq_of_derives _ hbeta).symm
          subst betaWord
          rw [hpreWord, hpostWord]
          simp only [List.append_nil, List.nil_append]
          cases hparent
          apply Focused.list (emptyStackPDA M).initial_state target
            [(emptyStackPDA M).start_symbol] [] [] [] target
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.refl

/-- Prehandle-specialized form of the computation zipper. -/
public theorem focused_of_prehandle (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T}
    (hroot : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal A] ++ suffix.map symbol.terminal))
    (hp : (characteristicGrammar M).DerivesRightmost
      p (preWord.map symbol.terminal)) :
    Focused M A preWord suffix := by
  exact focused_of_derivation M hroot rfl hp Relation.ReflTransGen.refl

end

end DPDA_to_LR
