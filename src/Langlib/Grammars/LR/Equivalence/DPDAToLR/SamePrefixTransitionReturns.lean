module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CountedRetainedIntervals
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.WrapperReturnNesting

/-!
# Same-prefix transition-generated empty returns

This module isolates the part of concrete empty-return synchronization which
is already forced by a transition-generated edge.  Reading edges synchronize
with every other edge using the existing concrete read theorem.  Consequently
only an epsilon-generated left edge paired with an epsilon or structural split
edge remains.

The counted factorization below strengthens the transition side to an exact
one-step retained return.  This makes the remaining boundary-order question
explicit rather than hiding it behind ordinary reachability.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Constructor-exact view of an epsilon-generated concrete empty edge. -/
@[expose]
public def ConcreteEpsilonEmptyEdge (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (q : State M)
    (suffix : List T) : Prop :=
  ∃ (preWord : List T) (context : List (StackSymbol M))
      (source : State M) (Z : StackSymbol M),
    ConcreteOperationalSpine M p
      (PDA_to_CFG.N.single source Z q) suffix preWord context ∧
    (q, []) ∈ (emptyStackPDA M).transition_fun' source Z ∧
    (PDA_to_CFG.N.single source Z q,
      [symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules

/-- Constructor-exact view of a structural split concrete empty edge. -/
@[expose]
public def ConcreteSplitEmptyEdge (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (q : State M)
    (suffix : List T) : Prop :=
  ∃ (base : List (symbol T (Nonterminal M)))
      (preWord leftWord : List T)
      (context : List (StackSymbol M)) (source : State M)
      (Z : StackSymbol M),
    p = base ++
      [symbol.nonterminal (PDA_to_CFG.N.single source Z q)] ∧
    ConcreteOperationalSpine M base
      (PDA_to_CFG.N.list source [Z] q) suffix preWord context ∧
    [Z].length ≤ PDA_to_CFG.max_push (emptyStackPDA M) ∧
    (PDA_to_CFG.N.list source [Z] q,
      [symbol.nonterminal (PDA_to_CFG.N.single source Z q),
        symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
          (characteristicGrammar M).rules ∧
    (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.single source Z q)]
      (leftWord.map symbol.terminal)

/-- Exact residual after dispatching all same-prefix cases involving a read
edge. -/
@[expose]
public def SamePrefixEpsilonReturnResidual (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (q₁ q₂ : State M)
    (suffix₁ suffix₂ : List T) : Prop :=
  ConcreteEpsilonEmptyEdge M p q₁ suffix₁ ∧
    (ConcreteEpsilonEmptyEdge M p q₂ suffix₂ ∨
      ConcreteSplitEmptyEdge M p q₂ suffix₂)

/-- At a common visible prefix, a transition-generated empty edge either has
the same return state as the other edge, or the pair is exactly one of the two
epsilon residuals. -/
public theorem concreteTransitionEmptyReturn_samePrefix_state_eq_or_residual
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q₁ q₂ : State M}
    {suffix₁ suffix₂ : List T}
    (edge₁ : ConcreteEmptyTransitionEdge M p q₁ suffix₁)
    (edge₂ : ConcreteEmptyEdge M p q₂ suffix₂) :
    q₁ = q₂ ∨
      SamePrefixEpsilonReturnResidual M p q₁ q₂ suffix₁ suffix₂ := by
  cases edge₁ with
  | @read base suffix₁ preWord context source a Z q₁
      parent transition rule =>
      left
      exact concreteReadEmptyReturn_samePrefix_state_eq M
        parent transition rule edge₂
  | @epsilon p suffix₁ preWord₁ context₁ source₁ Z₁ q₁
      parent₁ transition₁ rule₁ =>
      cases edge₂ with
      | @read base suffix₂ preWord₂ context₂ source₂ a Z₂ q₂
          parent₂ transition₂ rule₂ =>
          left
          exact concreteEmptyReturn_read_samePrefix_state_eq M
            (ConcreteEmptyEdge.epsilon parent₁ transition₁ rule₁)
            parent₂ transition₂ rule₂
      | @epsilon p suffix₂ preWord₂ context₂ source₂ Z₂ q₂
          parent₂ transition₂ rule₂ =>
          right
          exact ⟨⟨preWord₁, context₁, source₁, Z₁,
              parent₁, transition₁, rule₁⟩,
            Or.inl ⟨preWord₂, context₂, source₂, Z₂,
              parent₂, transition₂, rule₂⟩⟩
      | @split base suffix₂ preWord₂ leftWord₂ context₂
          source₂ Z₂ q₂ parent₂ length₂ rule₂ left₂ =>
          right
          exact ⟨⟨preWord₁, context₁, source₁, Z₁,
              parent₁, transition₁, rule₁⟩,
            Or.inr ⟨base, preWord₂, leftWord₂, context₂,
              source₂, Z₂, rfl, parent₂, length₂,
              rule₂, left₂⟩⟩

/-- Counted form of a transition-generated return.  Unlike the general
`CountedConcreteEmptyReturnInterval`, the retained return has exactly one
PDA step. -/
@[expose]
public def CountedConcreteEmptyTransitionInterval (M : DPDA Q T S)
    (completion suffix : List T) (q : State M) : Prop :=
  ∃ (beforeWord segmentWord : List T) (source : State M)
      (top : StackSymbol M) (context : List (StackSymbol M))
      (final : State M) (prefixSteps : ℕ),
    completion = beforeWord ++ segmentWord ∧
    (emptyStackPDA M).ReachesIn prefixSteps
      ⟨(emptyStackPDA M).initial_state, beforeWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, [], top :: context⟩ ∧
    PDA.RetainedFrameRun (emptyStackPDA M) context 1
      ⟨source, segmentWord, top :: context⟩
      ⟨q, [], context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨q, suffix, context⟩ ⟨final, [], []⟩

private theorem transition_terminal_completion_singleton
    (M : DPDA Q T S) {a : T} {w : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.terminal a] (w.map symbol.terminal)) :
    w = [a] := by
  have h' : (characteristicGrammar M).DerivesRightmost
      ([a].map (symbol.terminal (N := Nonterminal M)))
      (w.map symbol.terminal) := by simpa using h
  have heq := h'.eq_of_map_terminal_source
  have hmap : w.map (symbol.terminal (N := Nonterminal M)) =
      [a].map symbol.terminal := by simpa using heq
  exact (List.map_injective_iff.mpr fun _ _ hsymbol =>
    symbol.terminal.inj hsymbol) hmap

private theorem transition_oneStep_retained
    {P : PDA Q T S} {source target : Q} {input : List T}
    {top : S} {frame : List S}
    (hstep : P.Reaches₁ ⟨source, input, [top]⟩ ⟨target, [], []⟩) :
    PDA.RetainedFrameRun P frame 1
      ⟨source, input, top :: frame⟩ ⟨target, [], frame⟩ := by
  have hcounted : P.ReachesIn 1
      ⟨source, input, [top]⟩ ⟨target, [], []⟩ := by
    simpa using PDA.ReachesIn.step (PDA.ReachesIn.refl _) hstep
  simpa [PDA.conf.appendStack] using
    (PDA.RetainedFrameRun.ofReachesIn (frame := frame) hcounted)

/-- Exact one-step counted interval supplied by a transition-tagged edge at
any selected completion of its prefix. -/
public theorem ConcreteEmptyTransitionEdge.countedIntervalAtCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix completion : List T}
    (edge : ConcreteEmptyTransitionEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    CountedConcreteEmptyTransitionInterval M completion suffix q := by
  cases edge with
  | @read base suffix oldWord oldContext source a Z q
      parent transition rule =>
      obtain ⟨beforeWord, segmentWord, hcompletion, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hsegmentWord : segmentWord = [a] :=
        transition_terminal_completion_singleton M hsegment
      subst segmentWord
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hbase
      obtain ⟨prefixSteps, hprefix⟩ := hparent.exists_prefixRunIn M
      cases hparent.focusedExact M with
      | single _ _ _ _ _ _ final oldPrefix continuation =>
          have hcore : (emptyStackPDA M).Reaches₁
              ⟨source, [a], [Z]⟩ ⟨q, [], []⟩ := by
            exact Or.inl ⟨q, [], transition, by simp⟩
          exact ⟨beforeWord, [a], source, Z, context, final,
            prefixSteps, hcompletion, hprefix,
            transition_oneStep_retained hcore, continuation⟩
  | @epsilon p suffix oldWord oldContext source Z q
      parent transition rule =>
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hp
      obtain ⟨prefixSteps, hprefix⟩ := hparent.exists_prefixRunIn M
      cases hparent.focusedExact M with
      | single _ _ _ _ _ _ final oldPrefix continuation =>
          have hcore : (emptyStackPDA M).Reaches₁
              ⟨source, [], [Z]⟩ ⟨q, [], []⟩ := by
            exact ⟨q, [], transition, by simp⟩
          exact ⟨completion, [], source, Z, context, final,
            prefixSteps, by simp, hprefix,
            transition_oneStep_retained hcore, continuation⟩

/-- Both exact counted intervals are available at one common completion of a
same-prefix pair.  This is the input expected by the retained-return nesting
theorems; the remaining issue is to relate their boundary counts. -/
public theorem samePrefixTransitionReturn_exists_countedIntervals
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q₁ q₂ : State M}
    {suffix₁ suffix₂ completion : List T}
    (edge₁ : ConcreteEmptyTransitionEdge M p q₁ suffix₁)
    (edge₂ : ConcreteEmptyEdge M p q₂ suffix₂)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    CountedConcreteEmptyTransitionInterval M completion suffix₁ q₁ ∧
      CountedConcreteEmptyReturnInterval M completion suffix₂ q₂ :=
  ⟨edge₁.countedIntervalAtCompletion M hp,
    edge₂.countedReturnIntervalAtCompletion M hp⟩

end

end DPDA_to_LR
