module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Spine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ActiveHeads

/-!
# Synchronization of active characteristic heads

The hard direction in the characteristic-grammar proof is reverse-edge
uniqueness.  This file isolates the semantic synchronization facts used by
the paired-spine inversion.  Reading heads are the first case: two globally
reachable normalized-DPDA configurations at the same input cut which can
both read the next symbol must coincide.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A deterministic computation cannot move between two configurations with
the same remaining nonempty input if a reading transition is enabled at its
source.  Any first step would either consume that input, which cannot be
undone, or be an epsilon step, which `no_mixed` excludes. -/
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

/-- Reading transitions of the FS-to-empty-stack machine necessarily lie in
the simulation component and expose a genuine transition of the normalized
DPDA. -/
private theorem simulation_read_of_emptyStack_read
    (M : DPDA Q T S) {q next : State M} {a : T}
    {Z : StackSymbol M} {gamma : List (StackSymbol M)}
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
          | none =>
              simp [DPDA.toPDA, hoption] at htransition
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

/-- Completing a shared visible prefix in the same way places two active
simulation-state `single` heads on comparable cuts of the normalized DPDA
run.  The returned stacks include the aligned physical contexts reconstructed
from the FS-to-empty-stack bottom-marker invariant. -/
public theorem activeSingle_simulation_cuts_comparable
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {suffix₁ suffix₂ w : List T}
    {q₁ q₂ : Q × Bool} {Z₁ Z₂ : S}
    {target₁ target₂ : State M}
    (hspine₁ : ActiveSpine M p
      (PDA_to_CFG.N.single (Sum.inl q₁) (some Z₁) target₁) suffix₁)
    (hspine₂ : ActiveSpine M p
      (PDA_to_CFG.N.single (Sum.inl q₂) (some Z₂) target₂) suffix₂)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (w.map symbol.terminal)) :
    ∃ (rest₁ rest₂ : List S),
      M.firstFinal.toPDA.Reaches
          ⟨M.firstFinal.initial_state, w,
            [M.firstFinal.start_symbol]⟩
          ⟨q₁, [], Z₁ :: rest₁⟩ ∧
      M.firstFinal.toPDA.Reaches
          ⟨M.firstFinal.initial_state, w,
            [M.firstFinal.start_symbol]⟩
          ⟨q₂, [], Z₂ :: rest₂⟩ ∧
      (M.firstFinal.toPDA.Reaches
          ⟨q₁, [], Z₁ :: rest₁⟩
          ⟨q₂, [], Z₂ :: rest₂⟩ ∨
       M.firstFinal.toPDA.Reaches
          ⟨q₂, [], Z₂ :: rest₂⟩
          ⟨q₁, [], Z₁ :: rest₁⟩) := by
  have hf₁ := focused_of_prehandle M
    (hspine₁.derivesRightmost M) hp
  have hf₂ := focused_of_prehandle M
    (hspine₂.derivesRightmost M) hp
  cases hf₁ with
  | single _ _ _ _ _ context₁ final₁ prefixPath₁ continuation₁ =>
      cases hf₂ with
      | single _ _ _ _ _ context₂ final₂ prefixPath₂ continuation₂ =>
          obtain ⟨stack₁, hstack₁, hnormalized₁⟩ :=
            emptyStack_reachable_simulation_shape M prefixPath₁
          obtain ⟨stack₂, hstack₂, hnormalized₂⟩ :=
            emptyStack_reachable_simulation_shape M prefixPath₂
          obtain ⟨rest₁, hstack₁', hcontext₁⟩ :=
            simulation_stack_shape hstack₁
          obtain ⟨rest₂, hstack₂', hcontext₂⟩ :=
            simulation_stack_shape hstack₂
          subst stack₁
          subst stack₂
          exact ⟨rest₁, rest₂, hnormalized₁, hnormalized₂,
            M.firstFinal.toPDA_reaches_comparable
              hnormalized₁ hnormalized₂⟩

/-- Two active `single` nodes at the same characteristic prefix which can
both read the same next terminal have the same physical state and exposed
stack symbol.  The terminal suffixes and return targets may differ; neither
is needed for this stable-cut synchronization. -/
public theorem activeSingle_read_heads_unique (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {suffix₁ suffix₂ : List T}
    {q₁ q₂ target₁ target₂ next₁ next₂ : State M}
    {a : T} {Z₁ Z₂ : StackSymbol M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (hspine₁ : ActiveSpine M p
      (PDA_to_CFG.N.single q₁ Z₁ target₁) suffix₁)
    (hspine₂ : ActiveSpine M p
      (PDA_to_CFG.N.single q₂ Z₂ target₂) suffix₂)
    (hread₁ : (next₁, gamma₁) ∈
      (emptyStackPDA M).transition_fun q₁ a Z₁)
    (hread₂ : (next₂, gamma₂) ∈
      (emptyStackPDA M).transition_fun q₂ a Z₂)
    (hrule₁ : (PDA_to_CFG.N.single q₁ Z₁ target₁,
        [symbol.terminal a,
          symbol.nonterminal
            (PDA_to_CFG.N.list next₁ gamma₁ target₁)]) ∈
      (characteristicGrammar M).rules) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  obtain ⟨q₁', next₁', Z₁', gamma₁', rfl, rfl, rfl, rfl,
      hread₁'⟩ := simulation_read_of_emptyStack_read M hread₁
  obtain ⟨q₂', next₂', Z₂', gamma₂', rfl, rfl, rfl, rfl,
      hread₂'⟩ := simulation_read_of_emptyStack_read M hread₂
  obtain ⟨preWord, hp⟩ :=
    prehandle_prefix_completion M
      (r := (PDA_to_CFG.N.single (Sum.inl q₁') (some Z₁') target₁,
        [symbol.terminal a,
          symbol.nonterminal
            (PDA_to_CFG.N.list (Sum.inl next₁')
              (gamma₁'.map some) target₁)]))
      hrule₁ (hspine₁.derivesRightmost M)
  have hf₁ := focused_of_prehandle M
    (hspine₁.derivesRightmost M) hp
  have hf₂ := focused_of_prehandle M
    (hspine₂.derivesRightmost M) hp
  cases hf₁ with
  | single _ _ _ _ _ context₁ final₁ prefixPath₁ continuation₁ =>
      cases hf₂ with
      | single _ _ _ _ _ context₂ final₂ prefixPath₂ continuation₂ =>
          obtain ⟨stack₁, hstack₁, hnormalized₁⟩ :=
            emptyStack_reachable_simulation_shape M prefixPath₁
          obtain ⟨stack₂, hstack₂, hnormalized₂⟩ :=
            emptyStack_reachable_simulation_shape M prefixPath₂
          obtain ⟨rest₁, hstack₁', hcontext₁⟩ :=
            simulation_stack_shape hstack₁
          obtain ⟨rest₂, hstack₂', hcontext₂⟩ :=
            simulation_stack_shape hstack₂
          subst stack₁
          subst stack₂
          have hpath₁ : M.firstFinal.toPDA.Reaches
              ⟨M.firstFinal.initial_state, preWord ++ [a],
                [M.firstFinal.start_symbol]⟩
              ⟨q₁', [a], Z₁' :: rest₁⟩ := by
            simpa [PDA.conf.appendInput] using
              (PDA.unconsumed_input [a]).mp hnormalized₁
          have hpath₂ : M.firstFinal.toPDA.Reaches
              ⟨M.firstFinal.initial_state, preWord ++ [a],
                [M.firstFinal.start_symbol]⟩
              ⟨q₂', [a], Z₂' :: rest₂⟩ := by
            simpa [PDA.conf.appendInput] using
              (PDA.unconsumed_input [a]).mp hnormalized₂
          rcases M.firstFinal.toPDA_reaches_comparable hpath₁ hpath₂ with
              h₁₂ | h₂₁
          · have heq := reaches_eq_of_read_enabled M.firstFinal
              hread₁' h₁₂
            have hstate : q₁' = q₂' :=
              congrArg PDA.conf.state heq
            have hstack : Z₁' :: rest₁ = Z₂' :: rest₂ :=
              congrArg PDA.conf.stack heq
            exact ⟨by rw [hstate], by rw [List.cons.inj hstack |>.1]⟩
          · have heq := reaches_eq_of_read_enabled M.firstFinal
              hread₂' h₂₁
            have hstate : q₂' = q₁' :=
              congrArg PDA.conf.state heq
            have hstack : Z₂' :: rest₂ = Z₁' :: rest₁ :=
              congrArg PDA.conf.stack heq
            exact ⟨by rw [hstate], by rw [List.cons.inj hstack |>.1]⟩

end

end DPDA_to_LR
