module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ZeroVisibleSpine

/-!
# Semantics and alignment of visible spine anchors

This file is the small, ancestry-preserving interface between normalized
spines and paired synchronization.  It exposes the exact operational cut of
a visible anchor, classifies zero-visible tails according to whether they
contain a genuine epsilon transition, and aligns the last visible event of
two anchors with the same prefix.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Exact-context zipper semantics of a visible anchor. -/
public theorem VisibleSpineAnchor.focusedExact (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : VisibleSpineAnchor M p A suffix preWord context) :
    FocusedExact M A preWord suffix context :=
  (h.concreteOperationalSpine M).focusedExact M

/-- The concrete cut of a visible anchor is reached after exactly its
completed visible-prefix word. -/
public theorem VisibleSpineAnchor.prefixPath (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : VisibleSpineAnchor M p A suffix preWord context) :
    (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, preWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨spineCutState M A, [], spineCutStack M A context⟩ := by
  cases h.focusedExact M with
  | start => exact Relation.ReflTransGen.refl
  | single q target Z preWord postWord context final
      prefixPath continuation =>
      simpa [spineCutState, spineCutStack] using prefixPath
  | list q target gamma preWord postWord context final
      prefixPath continuation =>
      simpa [spineCutState, spineCutStack] using prefixPath

/-- A list-valued visible anchor retains an accepting continuation beginning
at exactly its indexed outer context. -/
public theorem VisibleSpineAnchor.listContinuation (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {q target : State M} {gamma : List (StackSymbol M)}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : VisibleSpineAnchor M p (PDA_to_CFG.N.list q gamma target)
      suffix preWord context) :
    ∃ final : State M,
      (emptyStackPDA M).Reaches
        ⟨target, suffix, context⟩ ⟨final, [], []⟩ := by
  cases h.focusedExact M with
  | list _ _ _ _ _ _ final prefixPath continuation =>
      exact ⟨final, continuation⟩

/-- Combined exact prefix and continuation semantics for a list anchor. -/
public theorem VisibleSpineAnchor.listSemantics (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {q target : State M} {gamma : List (StackSymbol M)}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : VisibleSpineAnchor M p (PDA_to_CFG.N.list q gamma target)
      suffix preWord context) :
    ∃ final : State M,
      (emptyStackPDA M).Reaches
        ⟨(emptyStackPDA M).initial_state, preWord,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q, [], gamma ++ context⟩ ∧
      (emptyStackPDA M).Reaches
        ⟨target, suffix, context⟩ ⟨final, [], []⟩ := by
  cases h.focusedExact M with
  | list _ _ _ _ _ _ final prefixPath continuation =>
      exact ⟨final, prefixPath, continuation⟩

/-! ## Stable physical source cuts before a read -/

private theorem reaches_eq_of_read_enabled
    {Q₀ T₀ S₀ : Type} [Fintype Q₀] [Fintype T₀] [Fintype S₀]
    (A : DPDA Q₀ T₀ S₀)
    {q p next : Q₀} {a : T₀} {Z : S₀}
    {gamma stack delta : List S₀}
    (hread : A.transition q a Z = some (next, gamma))
    (hreach : A.toPDA.Reaches
      ⟨q, [a], Z :: stack⟩ ⟨p, [a], delta⟩) :
    (⟨q, [a], Z :: stack⟩ : PDA.conf A.toPDA) =
      ⟨p, [a], delta⟩ := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hreach with
      heq | hnonempty
  · exact heq.symm
  · obtain ⟨middle, hfirst, hrest⟩ :=
      Relation.TransGen.head'_iff.mp hnonempty
    rcases PDA.reaches₁_push hfirst with hconsume | hepsilon
    · rcases hconsume with
        ⟨b, tail, nextState, replacement, hinput, hmiddle, _⟩
      have hb : b = a ∧ tail = [] := by
        have hb' : a = b ∧ tail = [] := by simpa using hinput
        exact ⟨hb'.1.symm, hb'.2⟩
      rcases hb with ⟨rfl, rfl⟩
      subst middle
      obtain ⟨consumed, hdecrease⟩ := PDA.decreasing_input hrest
      simp at hdecrease
    · rcases hepsilon with
        ⟨nextState, replacement, hmiddle, hepsilon⟩
      have hepsilonNone : A.epsilon_transition q Z = none := by
        by_contra hsome
        have hreadNone := A.no_mixed q Z hsome a
        rw [hread] at hreadNone
        simp at hreadNone
      simp [DPDA.toPDA, hepsilonNone] at hepsilon

/-- A reading transition of the final-state-to-empty-stack machine lies in
the simulation component and is induced by a genuine normalized-DPDA read. -/
private theorem emptyStack_read_simulation_view (M : DPDA Q T S)
    {q next : State M} {a : T} {Z : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (h : (next, gamma) ∈
      (emptyStackPDA M).transition_fun q a Z) :
    ∃ (q₀ next₀ : Q × Bool) (Z₀ : S) (gamma₀ : List S),
      q = Sum.inl q₀ ∧ Z = some Z₀ ∧
      next = Sum.inl next₀ ∧ gamma = gamma₀.map some ∧
      M.firstFinal.transition q₀ a Z₀ = some (next₀, gamma₀) := by
  classical
  cases q with
  | inr i =>
      simp [emptyStackPDA, PDA_FS_to_ES_pda,
        PDA_FS_to_ES_trans] at h
  | inl q₀ =>
      cases Z with
      | none =>
          simp [emptyStackPDA, PDA_FS_to_ES_pda,
            PDA_FS_to_ES_trans] at h
      | some Z₀ =>
          change (next, gamma) ∈
              (fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                M.firstFinal.toPDA.transition_fun q₀ a Z₀ at h
          rcases h with ⟨⟨next₀, gamma₀⟩, htransition, heq⟩
          cases hoption : M.firstFinal.transition q₀ a Z₀ with
          | none => simp [DPDA.toPDA, hoption] at htransition
          | some out =>
              have hout : out = (next₀, gamma₀) := by
                have hout' : (next₀, gamma₀) = out := by
                  simpa [DPDA.toPDA, hoption] using htransition
                exact hout'.symm
              subst out
              rcases heq with ⟨rfl, rfl⟩
              exact ⟨q₀, next₀, Z₀, gamma₀,
                rfl, rfl, rfl, rfl, hoption⟩

private theorem simulation_stack_shape
    {Z : S} {context : List (Option S)} {stack : List S}
    (h : some Z :: context = stack.map some ++ [none]) :
    ∃ rest : List S,
      stack = Z :: rest ∧ context = rest.map some ++ [none] := by
  cases stack with
  | nil => simp at h
  | cons Z' rest =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      have hZ : Z' = Z := (Option.some.inj h.1).symm
      subst Z'
      exact ⟨rest, rfl, h.2⟩

/-- Two concrete single parents at the same visible/completed prefix which
can both read the same next terminal represent the same complete physical
source cut, including their saved outer stack contexts. -/
public theorem concreteSingle_read_source_cuts_eq (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ q₂ target₁ target₂ next₁ next₂ : State M}
    {a : T} {Z₁ Z₂ : StackSymbol M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M p
      (PDA_to_CFG.N.single q₁ Z₁ target₁)
      suffix₁ preWord context₁)
    (parent₂ : ConcreteOperationalSpine M p
      (PDA_to_CFG.N.single q₂ Z₂ target₂)
      suffix₂ preWord context₂)
    (read₁ : (next₁, gamma₁) ∈
      (emptyStackPDA M).transition_fun q₁ a Z₁)
    (read₂ : (next₂, gamma₂) ∈
      (emptyStackPDA M).transition_fun q₂ a Z₂) :
    (⟨q₁, [], Z₁ :: context₁⟩ : PDA.conf (emptyStackPDA M)) =
      ⟨q₂, [], Z₂ :: context₂⟩ := by
  obtain ⟨q₁', next₁', Z₁', gamma₁', rfl, rfl, rfl, rfl, read₁'⟩ :=
    emptyStack_read_simulation_view M read₁
  obtain ⟨q₂', next₂', Z₂', gamma₂', rfl, rfl, rfl, rfl, read₂'⟩ :=
    emptyStack_read_simulation_view M read₂
  have focused₁ := parent₁.focusedExact M
  have focused₂ := parent₂.focusedExact M
  cases focused₁ with
  | single _ _ _ _ _ _ final₁ prefixPath₁ continuation₁ =>
      cases focused₂ with
      | single _ _ _ _ _ _ final₂ prefixPath₂ continuation₂ =>
          obtain ⟨stack₁, hstack₁, normalized₁⟩ :=
            emptyStack_reachable_simulation_shape M prefixPath₁
          obtain ⟨stack₂, hstack₂, normalized₂⟩ :=
            emptyStack_reachable_simulation_shape M prefixPath₂
          obtain ⟨rest₁, hstack₁', hcontext₁⟩ :=
            simulation_stack_shape hstack₁
          obtain ⟨rest₂, hstack₂', hcontext₂⟩ :=
            simulation_stack_shape hstack₂
          subst stack₁
          subst stack₂
          have path₁ : M.firstFinal.toPDA.Reaches
              ⟨M.firstFinal.initial_state, preWord ++ [a],
                [M.firstFinal.start_symbol]⟩
              ⟨q₁', [a], Z₁' :: rest₁⟩ := by
            simpa [PDA.conf.appendInput] using
              (PDA.unconsumed_input [a]).mp normalized₁
          have path₂ : M.firstFinal.toPDA.Reaches
              ⟨M.firstFinal.initial_state, preWord ++ [a],
                [M.firstFinal.start_symbol]⟩
              ⟨q₂', [a], Z₂' :: rest₂⟩ := by
            simpa [PDA.conf.appendInput] using
              (PDA.unconsumed_input [a]).mp normalized₂
          have hnormalized :
              (⟨q₁', [a], Z₁' :: rest₁⟩ :
                  PDA.conf M.firstFinal.toPDA) =
                ⟨q₂', [a], Z₂' :: rest₂⟩ := by
            rcases M.firstFinal.toPDA_reaches_comparable path₁ path₂ with
                h₁₂ | h₂₁
            · exact reaches_eq_of_read_enabled M.firstFinal read₁' h₁₂
            · exact (reaches_eq_of_read_enabled M.firstFinal read₂' h₂₁).symm
          have hstate : q₁' = q₂' :=
            congrArg PDA.conf.state hnormalized
          have hphysical : Z₁' :: rest₁ = Z₂' :: rest₂ :=
            congrArg PDA.conf.stack hnormalized
          have htop : Z₁' = Z₂' := (List.cons.inj hphysical).1
          have hrest : rest₁ = rest₂ := (List.cons.inj hphysical).2
          subst q₂'
          subst Z₂'
          subst rest₂
          rw [hcontext₁, hcontext₂]

/-! ## Epsilon-free and epsilon-bearing zero tails -/

/-- A zero-visible tail built without an epsilon constructor. -/
public inductive EpsilonFreeZeroVisibleTail (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (preWord : List T)
    (anchor : Nonterminal M) (anchorSuffix : List T)
    (anchorContext : List (StackSymbol M)) :
    Nonterminal M → List T → List (StackSymbol M) → Prop
  | refl : EpsilonFreeZeroVisibleTail M p preWord anchor anchorSuffix
      anchorContext anchor anchorSuffix anchorContext
  | start
      {target : State M}
      (previous : EpsilonFreeZeroVisibleTail M p preWord anchor
        anchorSuffix anchorContext PDA_to_CFG.N.start [] [])
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      EpsilonFreeZeroVisibleTail M p preWord anchor anchorSuffix
        anchorContext
        (PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target) [] []
  | splitLeft
      {suffix z : List T} {context : List (StackSymbol M)}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : EpsilonFreeZeroVisibleTail M p preWord anchor
        anchorSuffix anchorContext
        (PDA_to_CFG.N.list q (Z :: gamma) target) suffix context)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      EpsilonFreeZeroVisibleTail M p preWord anchor anchorSuffix
        anchorContext (PDA_to_CFG.N.single q Z middle)
        (z ++ suffix) (gamma ++ context)

/-- A zero-visible tail whose retained history contains an epsilon
constructor. -/
public inductive EpsilonBearingZeroVisibleTail (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (preWord : List T)
    (anchor : Nonterminal M) (anchorSuffix : List T)
    (anchorContext : List (StackSymbol M)) :
    Nonterminal M → List T → List (StackSymbol M) → Prop
  | epsilon
      {suffix : List T} {context : List (StackSymbol M)}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : ZeroVisibleTail M p preWord anchor anchorSuffix
        anchorContext (PDA_to_CFG.N.single q Z target) suffix context)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      EpsilonBearingZeroVisibleTail M p preWord anchor anchorSuffix
        anchorContext (PDA_to_CFG.N.list next gamma target) suffix context
  | start
      {target : State M}
      (previous : EpsilonBearingZeroVisibleTail M p preWord anchor
        anchorSuffix anchorContext PDA_to_CFG.N.start [] [])
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      EpsilonBearingZeroVisibleTail M p preWord anchor anchorSuffix
        anchorContext
        (PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target) [] []
  | splitLeft
      {suffix z : List T} {context : List (StackSymbol M)}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : EpsilonBearingZeroVisibleTail M p preWord anchor
        anchorSuffix anchorContext
        (PDA_to_CFG.N.list q (Z :: gamma) target) suffix context)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      EpsilonBearingZeroVisibleTail M p preWord anchor anchorSuffix
        anchorContext (PDA_to_CFG.N.single q Z middle)
        (z ++ suffix) (gamma ++ context)

/-- An epsilon-free zero tail only changes the grammar view of its physical
cut. -/
public theorem EpsilonFreeZeroVisibleTail.cut_eq (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M} {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : EpsilonFreeZeroVisibleTail M p preWord anchor anchorSuffix
      anchorContext current currentSuffix currentContext) :
    (⟨spineCutState M anchor, [], spineCutStack M anchor anchorContext⟩ :
        PDA.conf (emptyStackPDA M)) =
      ⟨spineCutState M current, [], spineCutStack M current currentContext⟩ := by
  induction h with
  | refl => rfl
  | start previous hrule ih =>
      simpa [spineCutState, spineCutStack] using ih
  | @splitLeft suffix z context q middle target Z gamma previous
      hlength hrule hright ih =>
      simpa [spineCutState, spineCutStack, List.append_assoc] using ih

/-- The epsilon step in an epsilon-bearing tail makes its exact cut path
nonempty. -/
public theorem EpsilonBearingZeroVisibleTail.transGen_cut
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M} {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : EpsilonBearingZeroVisibleTail M p preWord anchor anchorSuffix
      anchorContext current currentSuffix currentContext) :
    Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
      ⟨spineCutState M anchor, [], spineCutStack M anchor anchorContext⟩
      ⟨spineCutState M current, [], spineCutStack M current currentContext⟩ := by
  induction h with
  | @epsilon suffix context q target next Z gamma previous
      htransition hrule =>
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨q, [], Z :: context⟩
          ⟨next, [], gamma ++ context⟩ :=
        ⟨next, gamma, htransition, by simp⟩
      simpa [spineCutState, spineCutStack] using
        Relation.TransGen.tail' (previous.reaches_cut M) hstep
  | start previous hrule ih =>
      simpa [spineCutState, spineCutStack] using ih
  | @splitLeft suffix z context q middle target Z gamma previous
      hlength hrule hright ih =>
      simpa [spineCutState, spineCutStack, List.append_assoc] using ih

/-- Structural classification of a zero-visible tail by the presence of an
epsilon constructor. -/
public theorem ZeroVisibleTail.epsilonFree_or_epsilonBearing
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M} {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext) :
    EpsilonFreeZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        current currentSuffix currentContext ∨
      EpsilonBearingZeroVisibleTail M p preWord anchor anchorSuffix
        anchorContext current currentSuffix currentContext := by
  induction h with
  | refl => exact Or.inl EpsilonFreeZeroVisibleTail.refl
  | start previous hrule ih =>
      rcases ih with hfree | hbearing
      · exact Or.inl (EpsilonFreeZeroVisibleTail.start hfree hrule)
      · exact Or.inr (EpsilonBearingZeroVisibleTail.start hbearing hrule)
  | epsilon previous htransition hrule ih =>
      exact Or.inr
        (EpsilonBearingZeroVisibleTail.epsilon previous htransition hrule)
  | splitLeft previous hlength hrule hright ih =>
      rcases ih with hfree | hbearing
      · exact Or.inl
          (EpsilonFreeZeroVisibleTail.splitLeft hfree hlength hrule hright)
      · exact Or.inr
          (EpsilonBearingZeroVisibleTail.splitLeft
            hbearing hlength hrule hright)

/-- Operational form of the zero-tail dichotomy: either its endpoints are
literally the same physical cut, or a nonempty PDA path connects them. -/
public theorem ZeroVisibleTail.cut_eq_or_transGen (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M} {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext) :
    ((⟨spineCutState M anchor, [], spineCutStack M anchor anchorContext⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨spineCutState M current, [],
          spineCutStack M current currentContext⟩) ∨
      Relation.TransGen
        (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
        ⟨spineCutState M anchor, [], spineCutStack M anchor anchorContext⟩
        ⟨spineCutState M current, [],
          spineCutStack M current currentContext⟩ := by
  rcases h.epsilonFree_or_epsilonBearing M with hfree | hbearing
  · exact Or.inl (hfree.cut_eq M)
  · exact Or.inr (hbearing.transGen_cut M)

/-- A zero-visible tail from a visible anchor can reach a `single` node only
by a final split-left constructor. -/
public theorem ZeroVisibleTail.single_eq_splitLeft (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor : Nonterminal M} {anchorSuffix suffix : List T}
    {anchorContext context : List (StackSymbol M)}
    {q middle : State M} {Z : StackSymbol M}
    (hanchor : VisibleSpineAnchor M p anchor anchorSuffix
      preWord anchorContext)
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      (PDA_to_CFG.N.single q Z middle) suffix context) :
    ∃ (gamma : List (StackSymbol M)) (target : State M)
        (parentSuffix : List T) (outerContext : List (StackSymbol M))
        (z : List T),
      ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.list q (Z :: gamma) target)
        parentSuffix outerContext ∧
      (Z :: gamma).length ≤ PDA_to_CFG.max_push (emptyStackPDA M) ∧
      (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules ∧
      (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal) ∧
      suffix = z ++ parentSuffix ∧ context = gamma ++ outerContext := by
  cases h with
  | refl => cases hanchor
  | splitLeft previous hlength hrule hright =>
      exact ⟨_, _, _, _, _, previous, hlength, hrule, hright, rfl, rfl⟩

/-- A zero-visible tail from a visible anchor to an empty-list node is either
already at that anchor, or ends in the exact split-left/epsilon pair which
performs the empty return. -/
public theorem ZeroVisibleTail.emptyList_eq_or_splitEpsilon
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor : Nonterminal M} {anchorSuffix suffix : List T}
    {anchorContext context : List (StackSymbol M)} {q : State M}
    (hanchor : VisibleSpineAnchor M p anchor anchorSuffix
      preWord anchorContext)
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      (PDA_to_CFG.N.list q [] q) suffix context) :
    (anchor = PDA_to_CFG.N.list q [] q ∧
      anchorSuffix = suffix ∧ anchorContext = context) ∨
    ∃ (source : State M) (Z : StackSymbol M)
        (gamma : List (StackSymbol M)) (target : State M)
        (parentSuffix : List T) (outerContext : List (StackSymbol M))
        (z : List T),
      ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.list source (Z :: gamma) target)
        parentSuffix outerContext ∧
      (Z :: gamma).length ≤ PDA_to_CFG.max_push (emptyStackPDA M) ∧
      (PDA_to_CFG.N.list source (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single source Z q),
            symbol.nonterminal (PDA_to_CFG.N.list q gamma target)]) ∈
        (characteristicGrammar M).rules ∧
      (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list q gamma target)]
        (z.map symbol.terminal) ∧
      (q, []) ∈ (emptyStackPDA M).transition_fun' source Z ∧
      (PDA_to_CFG.N.single source Z q,
          [symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules ∧
      suffix = z ++ parentSuffix ∧ context = gamma ++ outerContext := by
  cases h with
  | refl => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @epsilon suffix context source target next Z gamma previous
      htransition hrule =>
      obtain ⟨saved, outerTarget, parentSuffix, outerContext, z,
        htail, hlength, hsplitRule, hright, hsuffix, hcontext⟩ :=
        previous.single_eq_splitLeft M hanchor
      exact Or.inr ⟨source, Z, saved, outerTarget,
        parentSuffix, outerContext, z, htail, hlength, hsplitRule,
        hright, htransition, hrule, hsuffix, hcontext⟩

/-! ## Pure alignment of the last visible event -/

/-- Two visible anchors with the same visible prefix have the same kind of
last visible event.  Read/read pairs share their predecessor prefix and last
terminal.  Split-right/split-right pairs share their predecessor prefix and
the complete displayed single marker; their hidden replacement tails,
targets, contexts, and left completions remain explicit and may differ. -/
public inductive PairedVisibleAnchors (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → List T →
      Nonterminal M → List T → List (StackSymbol M) →
      Nonterminal M → List T → List (StackSymbol M) → Prop
  | root : PairedVisibleAnchors M [] []
      PDA_to_CFG.N.start [] [] PDA_to_CFG.N.start [] []
  | read
      {base : List (symbol T (Nonterminal M))}
      {beforeWord suffix₁ suffix₂ : List T}
      {context₁ context₂ : List (StackSymbol M)}
      {q₁ target₁ next₁ q₂ target₂ next₂ : State M}
      {a : T} {Z₁ Z₂ : StackSymbol M}
      {gamma₁ gamma₂ : List (StackSymbol M)}
      (parent₁ : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.single q₁ Z₁ target₁)
        suffix₁ beforeWord context₁)
      (transition₁ : (next₁, gamma₁) ∈
        (emptyStackPDA M).transition_fun q₁ a Z₁)
      (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target₁,
          [symbol.terminal a,
            symbol.nonterminal
              (PDA_to_CFG.N.list next₁ gamma₁ target₁)]) ∈
        (characteristicGrammar M).rules)
      (parent₂ : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.single q₂ Z₂ target₂)
        suffix₂ beforeWord context₂)
      (transition₂ : (next₂, gamma₂) ∈
        (emptyStackPDA M).transition_fun q₂ a Z₂)
      (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target₂,
          [symbol.terminal a,
            symbol.nonterminal
              (PDA_to_CFG.N.list next₂ gamma₂ target₂)]) ∈
        (characteristicGrammar M).rules) :
      PairedVisibleAnchors M (base ++ [symbol.terminal a])
        (beforeWord ++ [a])
        (PDA_to_CFG.N.list next₁ gamma₁ target₁)
        suffix₁ context₁
        (PDA_to_CFG.N.list next₂ gamma₂ target₂)
        suffix₂ context₂
  | splitRight
      {base : List (symbol T (Nonterminal M))} {completedWord : List T}
      {beforeWord₁ leftWord₁ beforeWord₂ leftWord₂ : List T}
      {suffix₁ suffix₂ : List T}
      {context₁ context₂ : List (StackSymbol M)}
      {q middle target₁ target₂ : State M} {Z : StackSymbol M}
      {gamma₁ gamma₂ : List (StackSymbol M)}
      (parent₁ : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.list q (Z :: gamma₁) target₁)
        suffix₁ beforeWord₁ context₁)
      (length₁ : (Z :: gamma₁).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (rule₁ : (PDA_to_CFG.N.list q (Z :: gamma₁) target₁,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma₁ target₁)]) ∈
        (characteristicGrammar M).rules)
      (left₁ : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)]
        (leftWord₁.map symbol.terminal))
      (parent₂ : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.list q (Z :: gamma₂) target₂)
        suffix₂ beforeWord₂ context₂)
      (length₂ : (Z :: gamma₂).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (rule₂ : (PDA_to_CFG.N.list q (Z :: gamma₂) target₂,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma₂ target₂)]) ∈
        (characteristicGrammar M).rules)
      (left₂ : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)]
        (leftWord₂.map symbol.terminal))
      (word₁ : completedWord = beforeWord₁ ++ leftWord₁)
      (word₂ : completedWord = beforeWord₂ ++ leftWord₂) :
      PairedVisibleAnchors M
        (base ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)])
        completedWord
        (PDA_to_CFG.N.list middle gamma₁ target₁)
        suffix₁ context₁
        (PDA_to_CFG.N.list middle gamma₂ target₂)
        suffix₂ context₂

/-- Equal visible prefixes align the final visible events of two anchors. -/
public theorem pairedVisibleAnchors_of_same_prefix (M : DPDA Q T S)
    {p₁ p₂ : List (symbol T (Nonterminal M))} {w₁ w₂ : List T}
    {A₁ A₂ : Nonterminal M} {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    (h₁ : VisibleSpineAnchor M p₁ A₁ suffix₁ w₁ context₁)
    (h₂ : VisibleSpineAnchor M p₂ A₂ suffix₂ w₂ context₂)
    (hp : p₁ = p₂) (hw : w₁ = w₂) :
    PairedVisibleAnchors M p₁ w₁ A₁ suffix₁ context₁
      A₂ suffix₂ context₂ := by
  cases h₁ with
  | root =>
      cases h₂ with
      | root => exact PairedVisibleAnchors.root
      | read parent transition rule => simp at hp
      | splitRight parent length rule left => simp at hp
  | @read base₁ suffixOne before₁ contextOne
      q₁ target₁ next₁ a₁ Z₁ gamma₁ parent₁ transition₁ rule₁ =>
      cases h₂ with
      | root => simp at hp
      | @read base₂ suffixTwo before₂ contextTwo
          q₂ target₂ next₂ a₂ Z₂ gamma₂ parent₂ transition₂ rule₂ =>
          have hbase := List.append_inj_left' hp rfl
          have hlast := List.append_inj_right' hp rfl
          have ha : a₁ = a₂ := by simpa using hlast
          subst base₂
          subst a₂
          have hbefore := List.append_inj_left' hw rfl
          subst before₂
          exact PairedVisibleAnchors.read parent₁ transition₁ rule₁
            parent₂ transition₂ rule₂
      | splitRight parent length rule left =>
          have hlast := List.append_inj_right' hp rfl
          cases (List.cons.inj hlast).1
  | @splitRight base₁ suffixOne before₁ leftWord₁ contextOne
      q₁ middle₁ target₁ Z₁ gamma₁ parent₁ length₁ rule₁ left₁ =>
      cases h₂ with
      | root => simp at hp
      | read parent transition rule =>
          have hlast := List.append_inj_right' hp rfl
          cases (List.cons.inj hlast).1
      | @splitRight base₂ suffixTwo before₂ leftWord₂ contextTwo
          q₂ middle₂ target₂ Z₂ gamma₂ parent₂ length₂ rule₂ left₂ =>
          have hbase := List.append_inj_left' hp rfl
          have hlast := List.append_inj_right' hp rfl
          have hmarker :
              (PDA_to_CFG.N.single q₁ Z₁ middle₁ : Nonterminal M) =
                PDA_to_CFG.N.single q₂ Z₂ middle₂ := by
            have hs :
                symbol.nonterminal (T := T)
                    (PDA_to_CFG.N.single q₁ Z₁ middle₁) =
                  symbol.nonterminal
                    (PDA_to_CFG.N.single q₂ Z₂ middle₂) :=
              (List.cons.inj hlast).1
            exact symbol.nonterminal.inj hs
          injection hmarker with hq hZ hmiddle
          subst base₂
          subst q₂
          subst Z₂
          subst middle₂
          exact PairedVisibleAnchors.splitRight
            parent₁ length₁ rule₁ left₁
            parent₂ length₂ rule₂ left₂ rfl hw

end

end DPDA_to_LR
