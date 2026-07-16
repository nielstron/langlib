module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.AcceptingPaths
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulEpsilonCycles

/-!
# Factoring global paths through the FS-to-ES drain

A global computation which reaches the fresh drain state has a unique
semantic phase boundary: immediately before its first drain transition it is
the lift of a final configuration of the normalized DPDA.  This file retains
both sides of that boundary—the normalized prefix and the literal FS-to-ES
suffix—for later cut-comparison arguments.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Every step from the boot state enters the simulation component. -/
private theorem boot_step_target_simulation (M : DPDA Q T S)
    {input : List T} {stack : List (Option S)}
    {d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches₁
      ⟨Sum.inr 0, input, stack⟩ d) :
    ∃ q : Q × Bool, d.state = Sum.inl q := by
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      rcases PDA.reaches₁_push h with hread | hepsilon
      · rcases hread with
          ⟨a, tail, next, alpha, hinput, htarget, hmem⟩
        simp [emptyStackPDA, PDA_FS_to_ES_pda,
          PDA_FS_to_ES_trans] at hmem
      · rcases hepsilon with ⟨next, alpha, htarget, hmem⟩
        cases Z with
        | some Z =>
            simp [emptyStackPDA, PDA_FS_to_ES_pda,
              PDA_FS_to_ES_eps] at hmem
        | none =>
            simp [emptyStackPDA, PDA_FS_to_ES_pda,
              PDA_FS_to_ES_eps] at hmem
            rcases hmem with ⟨rfl, rfl⟩
            exact ⟨M.firstFinal.toPDA.initial_state, by simp [htarget]⟩

/-- A step out of the drain stays there, preserves input, and pops exactly
one symbol. -/
private theorem drain_step_shape (M : DPDA Q T S)
    {input : List T} {stack : List (Option S)}
    {d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches₁
      ⟨Sum.inr 1, input, stack⟩ d) :
    ∃ Z rest, stack = Z :: rest ∧
      d = ⟨Sum.inr 1, input, rest⟩ := by
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      refine ⟨Z, rest, rfl, ?_⟩
      rcases PDA.reaches₁_push h with hread | hepsilon
      · rcases hread with
          ⟨a, tail, next, alpha, hinput, htarget, hmem⟩
        simp [emptyStackPDA, PDA_FS_to_ES_pda,
          PDA_FS_to_ES_trans] at hmem
      · rcases hepsilon with ⟨next, alpha, rfl, hmem⟩
        change (next, alpha) ∈ PDA_FS_to_ES_eps
          M.firstFinal.toPDA (Sum.inr 1) Z at hmem
        simpa [PDA_FS_to_ES_eps] using hmem

/-- Exact inversion of a simulation-to-drain step. -/
private theorem simulation_step_to_drain_view (M : DPDA Q T S)
    {q : Q × Bool} {input : List T} {stack : List (Option S)}
    {d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches₁
      ⟨Sum.inl q, input, stack⟩ d)
    (hd : d.state = Sum.inr 1) :
    q ∈ M.firstFinal.final_states ∧ d.input = input := by
  classical
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      rcases PDA.reaches₁_push h with hread | hepsilon
      · rcases hread with
          ⟨a, tail, next, alpha, hinput, htarget, hmem⟩
        have hnext : next = Sum.inr 1 := by
          simpa [htarget] using hd
        subst next
        cases Z <;>
          simp [emptyStackPDA, PDA_FS_to_ES_pda,
            PDA_FS_to_ES_trans] at hmem
      · rcases hepsilon with ⟨next, alpha, htarget, hmem⟩
        have hnext : next = Sum.inr 1 := by
          simpa [htarget] using hd
        have hinput : d.input = input := by simp [htarget]
        subst next
        cases Z with
        | none =>
            change (Sum.inr 1, alpha) ∈
              (if q ∈ M.firstFinal.toPDA.final_states then
                {(Sum.inr 1, [])} else ∅) at hmem
            split_ifs at hmem with hfinal
            · exact ⟨hfinal, hinput⟩
            · simp at hmem
        | some Z =>
            change (Sum.inr 1, alpha) ∈
                ((fun out : (Q × Bool) × List S =>
                  (Sum.inl out.1, out.2.map some)) ''
                    M.firstFinal.toPDA.transition_fun' q Z ∪
                  if q ∈ M.firstFinal.toPDA.final_states then
                    {(Sum.inr 1, [])} else ∅) at hmem
            rcases hmem with hsimulation | hdrain
            · rcases hsimulation with ⟨out, _, hout⟩
              have := congrArg (fun pair => pair.1) hout
              simp at this
            · split_ifs at hdrain with hfinal
              · exact ⟨hfinal, hinput⟩
              · simp at hdrain

/-- General form used by tail induction: any globally reachable drain-state
configuration factors at its first drain edge.  The normalized prefix, the
literal entry edge, and the drain-only tail are all retained. -/
private theorem emptyStack_global_drain_factorization_aux
    (M : DPDA Q T S) {w : List T}
    {c : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩ c)
    (hstate : c.state = Sum.inr 1) :
    ∃ (p : Q × Bool) (delta : List S)
        (entryStack : List (Option S)),
      p ∈ M.firstFinal.final_states ∧
      M.firstFinal.toPDA.Reaches
        ⟨M.firstFinal.initial_state, w,
          [M.firstFinal.start_symbol]⟩
        ⟨p, c.input, delta⟩ ∧
      (emptyStackPDA M).Reaches₁
        (liftConf M.firstFinal.toPDA ⟨p, c.input, delta⟩)
        ⟨Sum.inr 1, c.input, entryStack⟩ ∧
      (emptyStackPDA M).Reaches
        ⟨Sum.inr 1, c.input, entryStack⟩ c := by
  induction h with
  | refl =>
      simp [emptyStackPDA, PDA_FS_to_ES_pda] at hstate
  | @tail before after hprefix hstep ih =>
      rcases after with ⟨afterState, afterInput, afterStack⟩
      simp only at hstate
      subst afterState
      rcases before with ⟨state, input, stack⟩
      cases state with
      | inl q =>
          obtain ⟨hfinal, hsameInput⟩ :=
            simulation_step_to_drain_view M hstep rfl
          simp only at hsameInput
          subst afterInput
          obtain ⟨delta, hstack, hnormalized⟩ :=
            emptyStack_reachable_simulation_shape M hprefix
          subst stack
          exact ⟨q, delta, afterStack, hfinal, hnormalized,
            by simpa [emptyStackPDA, liftConf] using hstep,
            Relation.ReflTransGen.refl⟩
      | inr i =>
          rcases i with ⟨i, hi⟩
          have hi' : i = 0 ∨ i = 1 := by omega
          rcases hi' with rfl | rfl
          · obtain ⟨q, htarget⟩ :=
              boot_step_target_simulation M (by simpa using hstep)
            simp at htarget
          · obtain ⟨Z, rest, hstack, hafter⟩ :=
              drain_step_shape M (by simpa using hstep)
            have hafterInput : afterInput = input := by
              simpa using congrArg PDA.conf.input hafter
            subst afterInput
            obtain ⟨p, delta, entryStack, hfinal, hnormalized,
                hentry, hsuffix⟩ := ih rfl
            exact ⟨p, delta, entryStack, hfinal, hnormalized, hentry,
              hsuffix.tail hstep⟩

/-- A global path to an exact drain cut factors at its first drain entry into
a normalized first-final computation and the literal remaining FS-to-ES
path. -/
public theorem emptyStack_global_drain_factorization
    (M : DPDA Q T S) {w input : List T}
    {drainStack : List (Option S)}
    (h : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inr 1, input, drainStack⟩) :
    ∃ (p : Q × Bool) (delta : List S)
        (entryStack : List (Option S)),
      p ∈ M.firstFinal.final_states ∧
      M.firstFinal.toPDA.Reaches
        ⟨M.firstFinal.initial_state, w,
          [M.firstFinal.start_symbol]⟩
        ⟨p, input, delta⟩ ∧
      (emptyStackPDA M).Reaches₁
        (liftConf M.firstFinal.toPDA ⟨p, input, delta⟩)
        ⟨Sum.inr 1, input, entryStack⟩ ∧
      (emptyStackPDA M).Reaches
        ⟨Sum.inr 1, input, entryStack⟩
        ⟨Sum.inr 1, input, drainStack⟩ :=
  emptyStack_global_drain_factorization_aux M h rfl

end

end DPDA_to_LR
