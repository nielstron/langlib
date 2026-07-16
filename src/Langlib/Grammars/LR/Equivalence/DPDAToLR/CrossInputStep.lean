module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulDeterminism

/-!
# One useful wrapper step under two input tails

Two productive computations may have different unconsumed tails while still
sharing the next input symbol.  Since a pushdown transition sees only that
symbol, the control state, and the top stack symbol, their next useful moves
have the same control and stack effects.  This file records the corresponding
relation between the two input components as well.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Two steps with corresponding source inputs either both preserve their
respective inputs, or both consume the same leading terminal. -/
@[expose]
public def CorrespondingInputStep
    (before₁ before₂ after₁ after₂ : List T) : Prop :=
  (after₁ = before₁ ∧ after₂ = before₂) ∨
    ∃ (a : T) (rest₁ rest₂ : List T),
      before₁ = a :: rest₁ ∧ before₂ = a :: rest₂ ∧
      after₁ = rest₁ ∧ after₂ = rest₂

/-- Useful one-step computations from equal state/stack cuts and inputs with
the same one-symbol lookahead have equal state and stack effects.  Their input
effects correspond in the sense of `CorrespondingInputStep`.

The two source cuts may be reached from different complete input words. -/
public theorem emptyStack_globally_useful_step_cross_input
    (M : DPDA Q T S)
    {w₁ w₂ sourceInput₁ sourceInput₂ : List T}
    {sourceState : EState M} {sourceStack : List (EStack M)}
    {next₁ next₂ : PDA.conf (emptyStackPDA M)}
    {final₁ final₂ : EState M}
    (hlook : sourceInput₁.take 1 = sourceInput₂.take 1)
    (hglobal₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w₁,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨sourceState, sourceInput₁, sourceStack⟩)
    (hglobal₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w₂,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨sourceState, sourceInput₂, sourceStack⟩)
    (hstep₁ : (emptyStackPDA M).Reaches₁
      ⟨sourceState, sourceInput₁, sourceStack⟩ next₁)
    (hstep₂ : (emptyStackPDA M).Reaches₁
      ⟨sourceState, sourceInput₂, sourceStack⟩ next₂)
    (huseful₁ : (emptyStackPDA M).Reaches
      next₁ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches
      next₂ ⟨final₂, [], []⟩) :
    next₁.state = next₂.state ∧ next₁.stack = next₂.stack ∧
      CorrespondingInputStep sourceInput₁ sourceInput₂
        next₁.input next₂.input := by
  classical
  cases sourceStack with
  | nil => simp [PDA.Reaches₁, PDA.step] at hstep₁
  | cons Z rest =>
      cases sourceInput₁ with
      | nil =>
          have hinput₂ : sourceInput₂ = [] := by
            cases sourceInput₂ with
            | nil => rfl
            | cons a tail => simp at hlook
          subst sourceInput₂
          have hnextInput₁ : next₁.input = [] := by
            rcases PDA.reaches₁_push hstep₁ with hread | hepsilon
            · rcases hread with ⟨a, tail, p, alpha, hnil, rfl, hmem⟩
              simp at hnil
            · rcases hepsilon with ⟨p, alpha, rfl, hmem⟩
              rfl
          have hnext := emptyStack_globally_useful_step_deterministic M
            hglobal₁ hstep₁ hstep₂ huseful₁ huseful₂
          subst next₂
          exact ⟨rfl, rfl, Or.inl ⟨hnextInput₁, hnextInput₁⟩⟩
      | cons a₁ tail₁ =>
          cases sourceInput₂ with
          | nil => simp at hlook
          | cons a₂ tail₂ =>
              have ha : a₁ = a₂ := by simpa using hlook
              subst a₂
              rcases PDA.reaches₁_push hstep₁ with
                  hread₁ | hepsilon₁ <;>
                rcases PDA.reaches₁_push hstep₂ with
                  hread₂ | hepsilon₂
              · rcases hread₁ with
                    ⟨read₁, afterInput₁, p₁, alpha₁,
                      hsourceInput₁, rfl, hmem₁⟩
                rcases hread₂ with
                    ⟨read₂, afterInput₂, p₂, alpha₂,
                      hsourceInput₂, rfl, hmem₂⟩
                have hread₁' : read₁ = a₁ := by
                  simpa using (congrArg List.head? hsourceInput₁).symm
                have hread₂' : read₂ = a₁ := by
                  simpa using (congrArg List.head? hsourceInput₂).symm
                subst read₁
                subst read₂
                have hafter₁ : afterInput₁ = tail₁ := by
                  simpa using (List.cons.inj hsourceInput₁).2.symm
                have hafter₂ : afterInput₂ = tail₂ := by
                  simpa using (List.cons.inj hsourceInput₂).2.symm
                subst afterInput₁
                subst afterInput₂
                have hout := emptyStack_read_output_unique_local M hmem₁ hmem₂
                have hp : p₁ = p₂ := congrArg Prod.fst hout
                have halpha : alpha₁ = alpha₂ := congrArg Prod.snd hout
                subst p₂
                subst alpha₂
                exact ⟨rfl, rfl, Or.inr ⟨a₁, tail₁, tail₂,
                  rfl, rfl, rfl, rfl⟩⟩
              · rcases hread₁ with
                    ⟨read, afterInput, pRead, alphaRead,
                      hsourceInput, rfl, hread⟩
                rcases hepsilon₂ with
                    ⟨pEps, alphaEps, rfl, hepsilon⟩
                have hread' : read = a₁ := by
                  simpa using (congrArg List.head? hsourceInput).symm
                subst read
                exact False.elim <| read_epsilon_not_both_useful M
                  hread hepsilon (by simpa using huseful₂)
              · rcases hepsilon₁ with
                    ⟨pEps, alphaEps, rfl, hepsilon⟩
                rcases hread₂ with
                    ⟨read, afterInput, pRead, alphaRead,
                      hsourceInput, rfl, hread⟩
                have hread' : read = a₁ := by
                  simpa using (congrArg List.head? hsourceInput).symm
                subst read
                exact False.elim <| read_epsilon_not_both_useful M
                  hread hepsilon (by simpa using huseful₁)
              · rcases hepsilon₁ with ⟨p₁, alpha₁, rfl, hmem₁⟩
                rcases hepsilon₂ with ⟨p₂, alpha₂, rfl, hmem₂⟩
                have houtput : (p₁, alpha₁) = (p₂, alpha₂) := by
                  cases sourceState with
                  | inr i =>
                      rcases i with ⟨i, hi⟩
                      have hi' : i = 0 ∨ i = 1 := by omega
                      rcases hi' with rfl | rfl
                      · cases Z with
                        | none =>
                            simp [emptyStackPDA, PDA_FS_to_ES_pda,
                              PDA_FS_to_ES_eps] at hmem₁ hmem₂
                            rcases hmem₁ with ⟨rfl, rfl⟩
                            rcases hmem₂ with ⟨rfl, rfl⟩
                            rfl
                        | some Z =>
                            simp [emptyStackPDA, PDA_FS_to_ES_pda,
                              PDA_FS_to_ES_eps] at hmem₁
                      · simp [emptyStackPDA, PDA_FS_to_ES_pda,
                            PDA_FS_to_ES_eps] at hmem₁ hmem₂
                        rcases hmem₁ with ⟨rfl, rfl⟩
                        rcases hmem₂ with ⟨rfl, rfl⟩
                        rfl
                  | inl q =>
                      cases Z with
                      | none =>
                          change (p₁, alpha₁) ∈
                            (if q ∈ M.firstFinal.toPDA.final_states then
                              {(Sum.inr 1, [])} else ∅) at hmem₁
                          change (p₂, alpha₂) ∈
                            (if q ∈ M.firstFinal.toPDA.final_states then
                              {(Sum.inr 1, [])} else ∅) at hmem₂
                          split_ifs at hmem₁ hmem₂ <;> simp_all
                      | some Z =>
                          change (p₁, alpha₁) ∈
                              ((fun out : (Q × Bool) × List S =>
                                (Sum.inl out.1, out.2.map some)) ''
                                  M.firstFinal.toPDA.transition_fun' q Z ∪
                                if q ∈ M.firstFinal.toPDA.final_states then
                                  {(Sum.inr 1, [])} else ∅) at hmem₁
                          change (p₂, alpha₂) ∈
                              ((fun out : (Q × Bool) × List S =>
                                (Sum.inl out.1, out.2.map some)) ''
                                  M.firstFinal.toPDA.transition_fun' q Z ∪
                                if q ∈ M.firstFinal.toPDA.final_states then
                                  {(Sum.inr 1, [])} else ∅) at hmem₂
                          rcases hmem₁ with hsim₁ | hdrain₁ <;>
                            rcases hmem₂ with hsim₂ | hdrain₂
                          · rcases hsim₁ with ⟨⟨next₁, repl₁⟩, ht₁, heq₁⟩
                            rcases hsim₂ with ⟨⟨next₂, repl₂⟩, ht₂, heq₂⟩
                            have hout := normalized_epsilon_output_unique M ht₁ ht₂
                            cases hout
                            exact heq₁.symm.trans heq₂
                          · rcases hsim₁ with ⟨⟨next, repl⟩, ht, heq⟩
                            split_ifs at hdrain₂ with hfinal
                            · have hdrainEq : (p₂, alpha₂) =
                                  (Sum.inr 1, []) := by simpa using hdrain₂
                              rcases hdrainEq with ⟨rfl, rfl⟩
                              have hsame := drain_reaches_input_eq M huseful₂
                              simp at hsame
                            · simp at hdrain₂
                          · rcases hsim₂ with ⟨⟨next, repl⟩, ht, heq⟩
                            split_ifs at hdrain₁ with hfinal
                            · have hdrainEq : (p₁, alpha₁) =
                                  (Sum.inr 1, []) := by simpa using hdrain₁
                              rcases hdrainEq with ⟨rfl, rfl⟩
                              have hsame := drain_reaches_input_eq M huseful₁
                              simp at hsame
                            · simp at hdrain₁
                          · split_ifs at hdrain₁ hdrain₂ <;> simp_all
                cases houtput
                exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

end

end DPDA_to_LR
