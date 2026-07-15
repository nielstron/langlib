module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Predictive

/-!
# Uniqueness of productive first moves

The empty-stack PDA has one apparent source of nondeterminism: at a normalized
final state it may either keep simulating or enter the drain state.  A drain
move can only complete on empty input.  If a simulated epsilon move could also
complete there, it would give a nonempty epsilon-only path between two
normalized final configurations, contradicting first-final normalization.
Thus one symbol of lookahead determines every productive first move.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem normalized_read_output_unique (M : DPDA Q T S)
    {q p₁ p₂ : Q × Bool} {a : T} {Z : S} {α₁ α₂ : List S}
    (h₁ : (p₁, α₁) ∈ M.firstFinal.toPDA.transition_fun q a Z)
    (h₂ : (p₂, α₂) ∈ M.firstFinal.toPDA.transition_fun q a Z) :
    (p₁, α₁) = (p₂, α₂) := by
  have hs₁ : M.firstFinal.toPDA.Reaches₁
      ⟨q, [a], [Z]⟩ ⟨p₁, [], α₁⟩ := by
    exact Or.inl ⟨p₁, α₁, h₁, by simp⟩
  have hs₂ : M.firstFinal.toPDA.Reaches₁
      ⟨q, [a], [Z]⟩ ⟨p₂, [], α₂⟩ := by
    exact Or.inl ⟨p₂, α₂, h₂, by simp⟩
  have hc := M.firstFinal.toPDA_step_deterministic hs₁ hs₂
  exact Prod.ext (congrArg PDA.conf.state hc) (congrArg PDA.conf.stack hc)

private theorem normalized_epsilon_output_unique (M : DPDA Q T S)
    {q p₁ p₂ : Q × Bool} {Z : S} {α₁ α₂ : List S}
    (h₁ : (p₁, α₁) ∈ M.firstFinal.toPDA.transition_fun' q Z)
    (h₂ : (p₂, α₂) ∈ M.firstFinal.toPDA.transition_fun' q Z) :
    (p₁, α₁) = (p₂, α₂) := by
  have hs₁ : M.firstFinal.toPDA.Reaches₁
      ⟨q, [], [Z]⟩ ⟨p₁, [], α₁⟩ := by
    exact ⟨p₁, α₁, h₁, by simp⟩
  have hs₂ : M.firstFinal.toPDA.Reaches₁
      ⟨q, [], [Z]⟩ ⟨p₂, [], α₂⟩ := by
    exact ⟨p₂, α₂, h₂, by simp⟩
  have hc := M.firstFinal.toPDA_step_deterministic hs₁ hs₂
  exact Prod.ext (congrArg PDA.conf.state hc) (congrArg PDA.conf.stack hc)

/-- Reading transitions of the normalized empty-stack PDA have a unique
output. -/
private theorem emptyStack_read_output_unique (M : DPDA Q T S)
    {q p₁ p₂ : EState M} {a : T} {Z : EStack M}
    {α₁ α₂ : List (EStack M)}
    (h₁ : (p₁, α₁) ∈ (emptyStackPDA M).transition_fun q a Z)
    (h₂ : (p₂, α₂) ∈ (emptyStackPDA M).transition_fun q a Z) :
    (p₁, α₁) = (p₂, α₂) := by
  cases q with
  | inr i => simp [emptyStackPDA, PDA_FS_to_ES_pda,
      PDA_FS_to_ES_trans] at h₁
  | inl q =>
      cases Z with
      | none => simp [emptyStackPDA, PDA_FS_to_ES_pda,
          PDA_FS_to_ES_trans] at h₁
      | some Z =>
          change (p₁, α₁) ∈
              (fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                M.firstFinal.toPDA.transition_fun q a Z at h₁
          change (p₂, α₂) ∈
              (fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                M.firstFinal.toPDA.transition_fun q a Z at h₂
          rcases h₁ with ⟨out₁, hout₁, heq₁⟩
          rcases h₂ with ⟨out₂, hout₂, heq₂⟩
          have hout := normalized_read_output_unique M hout₁ hout₂
          have hout' : out₁ = out₂ := by simpa only [Prod.eta] using hout
          subst out₂
          exact heq₁.symm.trans heq₂

/-- If a read move and an epsilon move are both enabled, the epsilon move is
necessarily the extra drain move. -/
private theorem emptyStack_epsilon_eq_drain_of_read (M : DPDA Q T S)
    {q pRead pEps : EState M} {a : T} {Z : EStack M}
    {αRead αEps : List (EStack M)}
    (hread : (pRead, αRead) ∈
      (emptyStackPDA M).transition_fun q a Z)
    (heps : (pEps, αEps) ∈
      (emptyStackPDA M).transition_fun' q Z) :
    (pEps, αEps) = (Sum.inr 1, []) := by
  classical
  cases q with
  | inr i => simp [emptyStackPDA, PDA_FS_to_ES_pda,
      PDA_FS_to_ES_trans] at hread
  | inl q =>
      cases Z with
      | none => simp [emptyStackPDA, PDA_FS_to_ES_pda,
          PDA_FS_to_ES_trans] at hread
      | some Z =>
          change (pRead, αRead) ∈
              (fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                M.firstFinal.toPDA.transition_fun q a Z at hread
          change (pEps, αEps) ∈
              ((fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                  M.firstFinal.toPDA.transition_fun' q Z ∪
                if q ∈ M.firstFinal.toPDA.final_states then
                  {(Sum.inr 1, [])} else ∅) at heps
          rcases hread with ⟨⟨p, α⟩, hread, _⟩
          rcases heps with hsimulation | hdrain
          · rcases hsimulation with ⟨⟨p', β⟩, heps, _⟩
            have hsRead : M.firstFinal.toPDA.Reaches₁
                ⟨q, [a], [Z]⟩ ⟨p, [], α⟩ := by
              exact Or.inl ⟨p, α, hread, by simp⟩
            have hsEps : M.firstFinal.toPDA.Reaches₁
                ⟨q, [a], [Z]⟩ ⟨p', [a], β⟩ := by
              exact Or.inr ⟨p', β, heps, by simp⟩
            have hsame := M.firstFinal.toPDA_step_deterministic hsRead hsEps
            have hbad := congrArg PDA.conf.input hsame
            simp at hbad
          · split_ifs at hdrain with hfinal
            · simpa using hdrain
            · simp at hdrain

/-- Drain computations stay in the drain state. -/
private theorem drain_reaches_state_eq (M : DPDA Q T S)
    {input : List T} {stack : List (EStack M)}
    {c : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, input, stack⟩ c) :
    c.state = Sum.inr 1 := by
  induction h with
  | refl => rfl
  | @tail c d hreach hstep ih =>
      rcases c with ⟨state, cin, cstack⟩
      simp only at ih
      subst state
      cases cstack with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons Z rest =>
          rcases PDA.reaches₁_push hstep with hread | hepsilon
          · rcases hread with ⟨a, tail, p, α, hinput, hmem⟩
            simp [emptyStackPDA, PDA_FS_to_ES_pda,
              PDA_FS_to_ES_trans] at hmem
          · rcases hepsilon with ⟨p, α, rfl, hmem⟩
            change (p, α) ∈ PDA_FS_to_ES_eps
              M.firstFinal.toPDA (Sum.inr 1) Z at hmem
            simpa [PDA_FS_to_ES_eps] using congrArg Prod.fst hmem

/-- The simulated epsilon branch and the drain branch cannot both be
productive with the same one-symbol lookahead and target. -/
private theorem simulation_drain_not_both_productive (M : DPDA Q T S)
    {q p : Q × Bool} {Z : S} {α : List S}
    {x y : List T} {target : EState M}
    (hq : q ∈ M.firstFinal.final_states)
    (hsimStep : (p, α) ∈ M.firstFinal.toPDA.transition_fun' q Z)
    (hsim : (emptyStackPDA M).Reaches
      ⟨Sum.inl p, x, α.map some⟩ ⟨target, [], []⟩)
    (hdrain : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, y, []⟩ ⟨target, [], []⟩)
    (hlook : x.take 1 = y.take 1) : False := by
  have hy : y = [] := by
    have := drain_reaches_input_eq M hdrain
    simpa using this.symm
  have htarget : target = Sum.inr 1 := by
    simpa using drain_reaches_state_eq M hdrain
  have hx : x = [] := by
    subst y
    cases x with
    | nil => rfl
    | cons a x => simp at hlook
  subst x
  subst y
  subst target
  obtain ⟨final, δ, hfinal, hreach⟩ :=
    simulation_reaches_drain_witness M hsim
  have hfirst : M.firstFinal.toPDA.Reaches₁
      ⟨q, [], [Z]⟩ ⟨p, [], α⟩ :=
    ⟨p, α, hsimStep, by simp⟩
  have hnonempty : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
      ⟨q, [], [Z]⟩ ⟨final, [], δ⟩ :=
    Relation.TransGen.head' hfirst hreach
  exact (M.firstFinal_no_final_to_final_epsilon hq hnonempty) hfinal

/-- One symbol of lookahead uniquely determines a productive first move for a
fixed characteristic-nonterminal target. -/
public theorem productiveFirstMove_unique (M : DPDA Q T S)
    {q target : EState M} {Z : EStack M}
    {x y : List T} {sig₁ sig₂ : FirstMoveSignature M}
    (hlook : x.take 1 = y.take 1)
    (h₁ : ProductiveFirstMove M q Z x target sig₁)
    (h₂ : ProductiveFirstMove M q Z y target sig₂) :
    sig₁ = sig₂ := by
  classical
  rcases h₁ with ⟨hmove₁, hreach₁⟩
  rcases h₂ with ⟨hmove₂, hreach₂⟩
  cases hmove₁ with
  | read a x p₁ α₁ ht₁ =>
      cases hmove₂ with
      | read b y p₂ α₂ ht₂ =>
          have hab : a = b := by
            simpa using congrArg List.head? hlook
          subst b
          have hout := emptyStack_read_output_unique M ht₁ ht₂
          cases hout
          rfl
      | epsilon _ p₂ α₂ ht₂ =>
          have hdrain := emptyStack_epsilon_eq_drain_of_read M ht₁ ht₂
          rcases hdrain with ⟨rfl, rfl⟩
          have hy : y = [] := by
            have := drain_reaches_input_eq M hreach₂
            simpa using this.symm
          subst y
          simp at hlook
  | epsilon x p₁ α₁ ht₁ =>
      cases hmove₂ with
      | read b y p₂ α₂ ht₂ =>
          have hdrain := emptyStack_epsilon_eq_drain_of_read M ht₂ ht₁
          rcases hdrain with ⟨rfl, rfl⟩
          have hx : x = [] := by
            have := drain_reaches_input_eq M hreach₁
            simpa using this.symm
          subst x
          simp at hlook
      | epsilon y p₂ α₂ ht₂ =>
          cases q with
          | inr i =>
              rcases i with ⟨i, hi⟩
              have hi' : i = 0 ∨ i = 1 := by omega
              rcases hi' with rfl | rfl
              · cases Z with
                | none =>
                    simp [emptyStackPDA, PDA_FS_to_ES_pda,
                      PDA_FS_to_ES_eps] at ht₁ ht₂
                    rcases ht₁ with ⟨rfl, rfl⟩
                    rcases ht₂ with ⟨rfl, rfl⟩
                    rfl
                | some Z =>
                    simp [emptyStackPDA, PDA_FS_to_ES_pda,
                      PDA_FS_to_ES_eps] at ht₁
              · simp [emptyStackPDA, PDA_FS_to_ES_pda,
                  PDA_FS_to_ES_eps] at ht₁ ht₂
                rcases ht₁ with ⟨rfl, rfl⟩
                rcases ht₂ with ⟨rfl, rfl⟩
                rfl
          | inl q =>
              cases Z with
              | none =>
                  simp [emptyStackPDA, PDA_FS_to_ES_pda,
                    PDA_FS_to_ES_eps] at ht₁ ht₂
                  rcases ht₁ with ⟨_, rfl, rfl⟩
                  rcases ht₂ with ⟨_, rfl, rfl⟩
                  rfl
              | some Z =>
                  change (p₁, α₁) ∈
                      ((fun out : (Q × Bool) × List S =>
                        (Sum.inl out.1, out.2.map some)) ''
                          M.firstFinal.toPDA.transition_fun' q Z ∪
                        if q ∈ M.firstFinal.toPDA.final_states then
                          {(Sum.inr 1, [])} else ∅) at ht₁
                  change (p₂, α₂) ∈
                      ((fun out : (Q × Bool) × List S =>
                        (Sum.inl out.1, out.2.map some)) ''
                          M.firstFinal.toPDA.transition_fun' q Z ∪
                        if q ∈ M.firstFinal.toPDA.final_states then
                          {(Sum.inr 1, [])} else ∅) at ht₂
                  rcases ht₁ with hsim₁ | hdrain₁ <;>
                    rcases ht₂ with hsim₂ | hdrain₂
                  · rcases hsim₁ with ⟨out₁, hout₁, heq₁⟩
                    rcases hsim₂ with ⟨out₂, hout₂, heq₂⟩
                    have hout := normalized_epsilon_output_unique M hout₁ hout₂
                    have hout' : out₁ = out₂ := by
                      simpa only [Prod.eta] using hout
                    subst out₂
                    have heq := heq₁.symm.trans heq₂
                    cases heq
                    rfl
                  · split_ifs at hdrain₂ with hq
                    · rcases hsim₁ with ⟨⟨p, α⟩, hp, heq⟩
                      rcases heq with ⟨rfl, rfl⟩
                      rcases hdrain₂ with ⟨rfl, rfl⟩
                      exact False.elim <| simulation_drain_not_both_productive M
                        hq hp hreach₁ hreach₂ hlook
                    · simp at hdrain₂
                  · split_ifs at hdrain₁ with hq
                    · rcases hsim₂ with ⟨⟨p, α⟩, hp, heq⟩
                      rcases heq with ⟨rfl, rfl⟩
                      rcases hdrain₁ with ⟨rfl, rfl⟩
                      exact False.elim <| simulation_drain_not_both_productive M
                        hq hp hreach₂ hreach₁ hlook.symm
                    · simp at hdrain₁
                  · split_ifs at hdrain₁ hdrain₂ with hq
                    · rcases hdrain₁ with ⟨rfl, rfl⟩
                      rcases hdrain₂ with ⟨rfl, rfl⟩
                      rfl
                    · simp at hdrain₁

end

end DPDA_to_LR
