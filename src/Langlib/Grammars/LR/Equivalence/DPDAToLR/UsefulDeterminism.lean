module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.AcceptingPaths
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulEpsilonCycles

/-!
# Determinism of useful paths in the normalized empty-stack wrapper

The final-state-to-empty-stack wrapper has one deliberate source of
nondeterminism: a normalized final state may either keep simulating or enter
the fresh drain state.  On a globally reachable computation, two successor
steps which both retain an empty-stack continuation nevertheless agree.  A
simulation step competing with the drain step would give a nonempty path
from a normalized final configuration to a later normalized final
configuration, contrary to first-final normalization.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem emptyStack_read_view (M : DPDA Q T S)
    {q next : EState M} {a : T} {Z : EStack M}
    {gamma : List (EStack M)}
    (h : (next, gamma) ∈
      (emptyStackPDA M).transition_fun q a Z) :
    ∃ (q₀ next₀ : Q × Bool) (Z₀ : S) (gamma₀ : List S),
      q = Sum.inl q₀ ∧ Z = some Z₀ ∧
      next = Sum.inl next₀ ∧ gamma = gamma₀.map some ∧
      (next₀, gamma₀) ∈
        M.firstFinal.toPDA.transition_fun q₀ a Z₀ := by
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
          rcases heq with ⟨rfl, rfl⟩
          exact ⟨q₀, next₀, Z₀, gamma₀,
            rfl, rfl, rfl, rfl, htransition⟩

public theorem normalized_epsilon_output_unique (M : DPDA Q T S)
    {q p₁ p₂ : Q × Bool} {Z : S} {α₁ α₂ : List S}
    (h₁ : (p₁, α₁) ∈ M.firstFinal.toPDA.transition_fun' q Z)
    (h₂ : (p₂, α₂) ∈ M.firstFinal.toPDA.transition_fun' q Z) :
    (p₁, α₁) = (p₂, α₂) := by
  have hs₁ : M.firstFinal.toPDA.Reaches₁
      ⟨q, [], [Z]⟩ ⟨p₁, [], α₁⟩ :=
    ⟨p₁, α₁, h₁, by simp⟩
  have hs₂ : M.firstFinal.toPDA.Reaches₁
      ⟨q, [], [Z]⟩ ⟨p₂, [], α₂⟩ :=
    ⟨p₂, α₂, h₂, by simp⟩
  have hc := M.firstFinal.toPDA_step_deterministic hs₁ hs₂
  exact Prod.ext (congrArg PDA.conf.state hc) (congrArg PDA.conf.stack hc)

public theorem emptyStack_read_output_unique_local (M : DPDA Q T S)
    {q next₁ next₂ : EState M} {a : T} {Z : EStack M}
    {gamma₁ gamma₂ : List (EStack M)}
    (h₁ : (next₁, gamma₁) ∈
      (emptyStackPDA M).transition_fun q a Z)
    (h₂ : (next₂, gamma₂) ∈
      (emptyStackPDA M).transition_fun q a Z) :
    (next₁, gamma₁) = (next₂, gamma₂) := by
  obtain ⟨q₁, p₁, Z₁, alpha₁, hq₁, hZ₁,
      hnext₁, hgamma₁, ht₁⟩ := emptyStack_read_view M h₁
  obtain ⟨q₂, p₂, Z₂, alpha₂, hq₂, hZ₂,
      hnext₂, hgamma₂, ht₂⟩ := emptyStack_read_view M h₂
  have hq : q₁ = q₂ := Sum.inl.inj (hq₁.symm.trans hq₂)
  have hZ : Z₁ = Z₂ := Option.some.inj (hZ₁.symm.trans hZ₂)
  subst q₂
  subst Z₂
  have hs₁ : M.firstFinal.toPDA.Reaches₁
      ⟨q₁, [a], [Z₁]⟩ ⟨p₁, [], alpha₁⟩ :=
    Or.inl ⟨p₁, alpha₁, ht₁, by simp⟩
  have hs₂ : M.firstFinal.toPDA.Reaches₁
      ⟨q₁, [a], [Z₁]⟩ ⟨p₂, [], alpha₂⟩ :=
    Or.inl ⟨p₂, alpha₂, ht₂, by simp⟩
  have hout := M.firstFinal.toPDA_step_deterministic hs₁ hs₂
  have hp : p₁ = p₂ := congrArg PDA.conf.state hout
  have halpha : alpha₁ = alpha₂ := congrArg PDA.conf.stack hout
  subst p₂
  subst alpha₂
  exact Prod.ext (hnext₁.trans hnext₂.symm)
    (hgamma₁.trans hgamma₂.symm)

private theorem mixed_simulation_drain_not_both_useful (M : DPDA Q T S)
    {w input : List T} {q p : Q × Bool} {Z : S}
    {replacement : List S} {rest : List (EStack M)}
    {final : EState M}
    (hq : q ∈ M.firstFinal.final_states)
    (hsimulation : (p, replacement) ∈
      M.firstFinal.toPDA.transition_fun' q Z)
    (hinput : input = [])
    (hglobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q, input, some Z :: rest⟩)
    (huseful : (emptyStackPDA M).Reaches
      ⟨Sum.inl p, input, replacement.map some ++ rest⟩
      ⟨final, [], []⟩) : False := by
  classical
  subst input
  have hmem : (Sum.inl p, replacement.map some) ∈
      (emptyStackPDA M).transition_fun' (Sum.inl q) (some Z) := by
    change (Sum.inl p, replacement.map some) ∈
      ((fun out : (Q × Bool) × List S =>
        (Sum.inl out.1, out.2.map some)) ''
          M.firstFinal.toPDA.transition_fun' q Z ∪
        if q ∈ M.firstFinal.toPDA.final_states then
          {(Sum.inr 1, [])} else ∅)
    exact Or.inl ⟨(p, replacement), hsimulation, rfl⟩
  have hsimStep : (emptyStackPDA M).Reaches₁
      ⟨Sum.inl q, [], some Z :: rest⟩
      ⟨Sum.inl p, [], replacement.map some ++ rest⟩ := by
    exact ⟨Sum.inl p, replacement.map some, hmem,
      by simp⟩
  have hfinal : final = Sum.inr 1 :=
    emptyStack_accepting_state_eq_drain M
      ((hglobal.tail hsimStep).trans huseful)
  subst final
  rcases emptyStack_simulation_reaches_classify M huseful with
      ⟨next, output, result, hend, hproject⟩ |
      ⟨hend, next, output, result, hnextFinal, hproject⟩
  · have hbad := congrArg PDA.conf.state hend
    simp at hbad
  · have hprojectStep := emptyStack_simulation_step_projects M hsimStep
    obtain ⟨consumed, hconsumed⟩ := PDA.decreasing_input hproject
    have houtput : output = [] := by
      simpa using (List.eq_nil_of_append_eq_nil hconsumed.symm).2
    subst output
    have hnonempty : Relation.TransGen
        (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
        ⟨q, [], (some Z :: rest).filterMap id⟩
        ⟨next, [], result⟩ :=
      Relation.TransGen.head' hprojectStep hproject
    exact (M.firstFinal_no_final_to_final_epsilon hq hnonempty) hnextFinal

public theorem read_epsilon_not_both_useful (M : DPDA Q T S)
    {a : T} {tail : List T} {q : EState M} {Z : EStack M}
    {pRead pEps : EState M} {alphaRead alphaEps : List (EStack M)}
    {rest : List (EStack M)} {final : EState M}
    (hread : (pRead, alphaRead) ∈
      (emptyStackPDA M).transition_fun q a Z)
    (hepsilon : (pEps, alphaEps) ∈
      (emptyStackPDA M).transition_fun' q Z)
    (huseful : (emptyStackPDA M).Reaches
      ⟨pEps, a :: tail, alphaEps ++ rest⟩ ⟨final, [], []⟩) :
    False := by
  classical
  obtain ⟨q₀, p₀, Z₀, alpha₀, hq, hZ,
      hpRead, halphaRead, hnormalizedRead⟩ :=
    emptyStack_read_view M hread
  subst q
  subst Z
  subst pRead
  subst alphaRead
  change (pEps, alphaEps) ∈
      ((fun out : (Q × Bool) × List S =>
        (Sum.inl out.1, out.2.map some)) ''
          M.firstFinal.toPDA.transition_fun' q₀ Z₀ ∪
        if q₀ ∈ M.firstFinal.toPDA.final_states then
          {(Sum.inr 1, [])} else ∅) at hepsilon
  rcases hepsilon with hsimulation | hdrain
  · rcases hsimulation with
      ⟨⟨pEps₀, alphaEps₀⟩, hnormalizedEps, heq⟩
    rcases heq with ⟨rfl, rfl⟩
    have hsRead : M.firstFinal.toPDA.Reaches₁
        ⟨q₀, [a], [Z₀]⟩ ⟨p₀, [], alpha₀⟩ := by
      exact Or.inl ⟨p₀, alpha₀, hnormalizedRead, by simp⟩
    have hsEps : M.firstFinal.toPDA.Reaches₁
        ⟨q₀, [a], [Z₀]⟩ ⟨pEps₀, [a], alphaEps₀⟩ := by
      exact Or.inr ⟨pEps₀, alphaEps₀, hnormalizedEps, by simp⟩
    have hsame := M.firstFinal.toPDA_step_deterministic hsRead hsEps
    have hbad := congrArg PDA.conf.input hsame
    simp at hbad
  · split_ifs at hdrain with hfinal
    · have heq : (pEps, alphaEps) = (Sum.inr 1, []) := by
        simpa using hdrain
      rcases heq with ⟨rfl, rfl⟩
      have hsame := drain_reaches_input_eq M huseful
      simp at hsame
    · simp at hdrain

/-- From a globally reachable source, two one-step successors which both
have an empty-stack continuation are equal. -/
public theorem emptyStack_globally_useful_step_deterministic
    (M : DPDA Q T S)
    {w : List T} {source next₁ next₂ : PDA.conf (emptyStackPDA M)}
    {final₁ final₂ : EState M}
    (hglobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩ source)
    (hstep₁ : (emptyStackPDA M).Reaches₁ source next₁)
    (hstep₂ : (emptyStackPDA M).Reaches₁ source next₂)
    (huseful₁ : (emptyStackPDA M).Reaches next₁ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches next₂ ⟨final₂, [], []⟩) :
    next₁ = next₂ := by
  classical
  rcases source with ⟨state, input, stack⟩
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at hstep₁
  | cons Z rest =>
      rcases PDA.reaches₁_push hstep₁ with hread₁ | hepsilon₁ <;>
        rcases PDA.reaches₁_push hstep₂ with hread₂ | hepsilon₂
      · rcases hread₁ with
          ⟨a₁, tail₁, p₁, alpha₁, hinput₁, rfl, hmem₁⟩
        rcases hread₂ with
          ⟨a₂, tail₂, p₂, alpha₂, hinput₂, rfl, hmem₂⟩
        have hinputEq : a₁ :: tail₁ = a₂ :: tail₂ :=
          hinput₁.symm.trans hinput₂
        injection hinputEq with ha htail
        subst a₂
        subst tail₂
        have hout := emptyStack_read_output_unique_local M hmem₁ hmem₂
        cases hout
        rfl
      · rcases hread₁ with
          ⟨a, tail, pRead, alphaRead, hinput, rfl, hread⟩
        rcases hepsilon₂ with ⟨pEps, alphaEps, rfl, hepsilon⟩
        exact False.elim <| read_epsilon_not_both_useful M
          hread hepsilon (by simpa [hinput] using huseful₂)
      · rcases hepsilon₁ with ⟨pEps, alphaEps, rfl, hepsilon⟩
        rcases hread₂ with
          ⟨a, tail, pRead, alphaRead, hinput, rfl, hread⟩
        exact False.elim <| read_epsilon_not_both_useful M
          hread hepsilon (by simpa [hinput] using huseful₁)
      · rcases hepsilon₁ with ⟨p₁, alpha₁, rfl, hmem₁⟩
        rcases hepsilon₂ with ⟨p₂, alpha₂, rfl, hmem₂⟩
        cases state with
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
                  have heqOut : (p₁, alpha₁) = (p₂, alpha₂) :=
                    heq₁.symm.trans heq₂
                  cases heqOut
                  rfl
                · rcases hsim₁ with ⟨⟨next, repl⟩, ht, heq⟩
                  split_ifs at hdrain₂ with hfinal
                  · have hdrainEq : (p₂, alpha₂) = (Sum.inr 1, []) := by
                      simpa using hdrain₂
                    rcases heq with ⟨rfl, rfl⟩
                    rcases hdrainEq with ⟨rfl, rfl⟩
                    exact False.elim <| mixed_simulation_drain_not_both_useful M
                      hfinal ht (by
                        have hsame := drain_reaches_input_eq M huseful₂
                        simpa using hsame.symm)
                      (by simpa using hglobal) huseful₁
                  · simp at hdrain₂
                · rcases hsim₂ with ⟨⟨next, repl⟩, ht, heq⟩
                  split_ifs at hdrain₁ with hfinal
                  · have hdrainEq : (p₁, alpha₁) = (Sum.inr 1, []) := by
                      simpa using hdrain₁
                    rcases hdrainEq with ⟨rfl, rfl⟩
                    rcases heq with ⟨rfl, rfl⟩
                    exact False.elim <| mixed_simulation_drain_not_both_useful M
                      hfinal ht (by
                        have hsame := drain_reaches_input_eq M huseful₁
                        simpa using hsame.symm)
                      (by simpa using hglobal) huseful₂
                  · simp at hdrain₁
                · split_ifs at hdrain₁ hdrain₂ <;> simp_all

/-- Two equal-length paths from the same global initial configuration have
the same endpoint whenever both endpoints still have an empty-stack
continuation. -/
public theorem emptyStack_globally_useful_reachesIn_deterministic
    (M : DPDA Q T S)
    {w : List T} {n : ℕ}
    {c₁ c₂ : PDA.conf (emptyStackPDA M)}
    {final₁ final₂ : EState M}
    (h₁ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩ c₁)
    (h₂ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩ c₂)
    (huseful₁ : (emptyStackPDA M).Reaches c₁ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches c₂ ⟨final₂, [], []⟩) :
    c₁ = c₂ := by
  induction n generalizing c₁ c₂ with
  | zero =>
      exact (PDA.reachesIn_zero h₁).symm.trans (PDA.reachesIn_zero h₂)
  | succ n ih =>
      obtain ⟨before₁, hprefix₁, hlast₁⟩ :=
        PDA.reachesIn_iff_split_last.mpr h₁
      obtain ⟨before₂, hprefix₂, hlast₂⟩ :=
        PDA.reachesIn_iff_split_last.mpr h₂
      have hstep₁ := PDA.reaches₁_iff_reachesIn_one.mpr hlast₁
      have hstep₂ := PDA.reaches₁_iff_reachesIn_one.mpr hlast₂
      have hbeforeUseful₁ : (emptyStackPDA M).Reaches
          before₁ ⟨final₁, [], []⟩ :=
        (Relation.ReflTransGen.single hstep₁).trans huseful₁
      have hbeforeUseful₂ : (emptyStackPDA M).Reaches
          before₂ ⟨final₂, [], []⟩ :=
        (Relation.ReflTransGen.single hstep₂).trans huseful₂
      have hbefore := ih hprefix₁ hprefix₂
        hbeforeUseful₁ hbeforeUseful₂
      subst before₂
      exact emptyStack_globally_useful_step_deterministic M
        (PDA.reaches_of_reachesIn hprefix₁)
        hstep₁ hstep₂ huseful₁ huseful₂

end

end DPDA_to_LR
