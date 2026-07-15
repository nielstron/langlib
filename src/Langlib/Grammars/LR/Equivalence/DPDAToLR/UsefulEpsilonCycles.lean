module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.PredictiveUniqueness
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulCycles

/-!
# Useful epsilon cycles in the normalized empty-stack PDA

The final-state-to-empty-stack conversion is almost deterministic.  Its only
extra branch enters the fresh drain state from a normalized final state.
First-final normalization makes that branch harmless for useful computations:
a simulation branch which returned to the same cut would be a forbidden
nonempty epsilon path from a normalized final state to itself.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- No transition of the FS-to-empty-stack machine enters its fresh boot
state. -/
private theorem emptyStack_step_target_ne_boot (M : DPDA Q T S)
    {c d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches₁ c d) :
    d.state ≠ Sum.inr 0 := by
  rcases c with ⟨state, input, stack⟩
  rcases d with ⟨next, nextInput, nextStack⟩
  simp only
  intro hboot
  subst next
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      rcases PDA.reaches₁_push h with hread | hepsilon
      · rcases hread with ⟨a, tail, p, alpha, _, heq, hmem⟩
        cases heq
        cases state <;> cases Z <;>
          simp [emptyStackPDA, PDA_FS_to_ES_pda,
            PDA_FS_to_ES_trans] at hmem
      · rcases hepsilon with ⟨p, alpha, heq, hmem⟩
        cases heq
        cases state with
        | inl q =>
            cases Z <;>
              simp [emptyStackPDA, PDA_FS_to_ES_pda,
                PDA_FS_to_ES_eps] at hmem
        | inr i =>
            rcases i with ⟨i, hi⟩
            have hi' : i = 0 ∨ i = 1 := by omega
            rcases hi' with rfl | rfl <;>
              cases Z <;>
              simp [emptyStackPDA, PDA_FS_to_ES_pda,
                PDA_FS_to_ES_eps] at hmem

/-- From the fresh drain state, every step stays in the drain state, keeps
the input fixed, and removes exactly one stack symbol. -/
private theorem drain_step_shape (M : DPDA Q T S)
    {input : List T} {stack : List (EStack M)}
    {d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches₁
      ⟨Sum.inr 1, input, stack⟩ d) :
    ∃ Z rest, stack = Z :: rest ∧ d = ⟨Sum.inr 1, input, rest⟩ := by
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      refine ⟨Z, rest, rfl, ?_⟩
      rcases PDA.reaches₁_push h with hread | hepsilon
      · rcases hread with ⟨a, tail, p, alpha, _, _, hmem⟩
        simp [emptyStackPDA, PDA_FS_to_ES_pda,
          PDA_FS_to_ES_trans] at hmem
      · rcases hepsilon with ⟨p, alpha, rfl, hmem⟩
        change (p, alpha) ∈ PDA_FS_to_ES_eps
          M.firstFinal.toPDA (Sum.inr 1) Z at hmem
        simpa [PDA_FS_to_ES_eps] using hmem

private theorem drain_reaches_stack_length_le (M : DPDA Q T S)
    {input : List T} {stack : List (EStack M)}
    {d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, input, stack⟩ d) :
    d.state = Sum.inr 1 ∧ d.input = input ∧
      d.stack.length ≤ stack.length := by
  induction h with
  | refl => exact ⟨rfl, rfl, le_rfl⟩
  | @tail c d hreach hstep ih =>
      rcases c with ⟨state, cin, cstack⟩
      simp only at ih
      rcases ih with ⟨hstate, hinput, hlength⟩
      subst state
      subst cin
      obtain ⟨Z, rest, hcstack, rfl⟩ := drain_step_shape M hstep
      subst cstack
      exact ⟨rfl, rfl, by simp at hlength ⊢; omega⟩

private theorem no_drain_cycle (M : DPDA Q T S)
    {input : List T} {stack : List (EStack M)}
    (h : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
      ⟨Sum.inr 1, input, stack⟩ ⟨Sum.inr 1, input, stack⟩) :
    False := by
  obtain ⟨d, hfirst, hrest⟩ := Relation.TransGen.head'_iff.mp h
  obtain ⟨Z, rest, hstack, rfl⟩ := drain_step_shape M hfirst
  subst stack
  have hlen := (drain_reaches_stack_length_le M hrest).2.2
  simp at hlen

private theorem no_boot_cycle (M : DPDA Q T S)
    {input : List T} {stack : List (EStack M)}
    (h : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
      ⟨Sum.inr 0, input, stack⟩ ⟨Sum.inr 0, input, stack⟩) :
    False := by
  obtain ⟨d, hfirst, hrest⟩ := Relation.TransGen.head'_iff.mp h
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hrest with heq | htail
  · subst d
    exact emptyStack_step_target_ne_boot M hfirst rfl
  · obtain ⟨before, _, hlast⟩ := Relation.TransGen.tail'_iff.mp htail
    exact emptyStack_step_target_ne_boot M hlast rfl

/-- A simulation-to-simulation FS→ES step projects through arbitrary
`Option` stack context to a step of the normalized DPDA.  `none` symbols in
the untouched context are simply erased by `filterMap`. -/
public theorem emptyStack_simulation_step_projects (M : DPDA Q T S)
    {q p : Q × Bool} {input input' : List T}
    {stack stack' : List (EStack M)}
    (h : (emptyStackPDA M).Reaches₁
      ⟨Sum.inl q, input, stack⟩ ⟨Sum.inl p, input', stack'⟩) :
    M.firstFinal.toPDA.Reaches₁
      ⟨q, input, stack.filterMap id⟩
      ⟨p, input', stack'.filterMap id⟩ := by
  classical
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      rcases PDA.reaches₁_push h with hread | hepsilon
      · rcases hread with
          ⟨a, tail, next, alpha, hinput, htarget, hmem⟩
        cases htarget
        cases Z with
        | none =>
            simp [emptyStackPDA, PDA_FS_to_ES_pda,
              PDA_FS_to_ES_trans] at hmem
        | some Z =>
            change (Sum.inl p, alpha) ∈
                (fun out : (Q × Bool) × List S =>
                  (Sum.inl out.1, out.2.map some)) ''
                  M.firstFinal.toPDA.transition_fun q a Z at hmem
            rcases hmem with ⟨⟨next₀, beta⟩, hbeta, hout⟩
            have hnext : next₀ = p := by
              have := congrArg (fun out => out.1) hout
              simpa using this
            have halpha : alpha = beta.map some := by
              have := congrArg (fun out => out.2) hout
              simpa using this.symm
            subst next₀
            subst alpha
            subst input
            exact Or.inl ⟨p, beta, hbeta, by
              simp [List.filterMap_append]⟩
      · rcases hepsilon with ⟨next, alpha, htarget, hmem⟩
        cases htarget
        cases Z with
        | none =>
            change (Sum.inl p, alpha) ∈
              (if q ∈ M.firstFinal.toPDA.final_states then
                {(Sum.inr 1, [])} else ∅) at hmem
            split_ifs at hmem <;> simp_all
        | some Z =>
            change (Sum.inl p, alpha) ∈
                ((fun out : (Q × Bool) × List S =>
                  (Sum.inl out.1, out.2.map some)) ''
                    M.firstFinal.toPDA.transition_fun' q Z ∪
                  if q ∈ M.firstFinal.toPDA.final_states then
                    {(Sum.inr 1, [])} else ∅) at hmem
            rcases hmem with hsimulation | hdrain
            · rcases hsimulation with ⟨⟨next₀, beta⟩, hbeta, hout⟩
              have hnext : next₀ = p := by
                have := congrArg (fun out => out.1) hout
                simpa using this
              have halpha : alpha = beta.map some := by
                have := congrArg (fun out => out.2) hout
                simpa using this.symm
              subst next₀
              subst alpha
              cases input with
              | nil =>
                  exact ⟨p, beta, hbeta, by
                    simp [List.filterMap_append]⟩
              | cons a tail =>
                  exact Or.inr ⟨p, beta, hbeta, by
                    simp [List.filterMap_append]⟩
            · split_ifs at hdrain <;> simp_all

/-- Entering the fresh drain state from a simulation state is possible only
from a normalized final state. -/
private theorem simulation_step_to_drain_final (M : DPDA Q T S)
    {q : Q × Bool} {input : List T} {stack : List (EStack M)}
    {d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches₁
      ⟨Sum.inl q, input, stack⟩ d)
    (hd : d.state = Sum.inr 1) :
    q ∈ M.firstFinal.final_states := by
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
        subst next
        cases Z with
        | none =>
            change (Sum.inr 1, alpha) ∈
              (if q ∈ M.firstFinal.toPDA.final_states then
                {(Sum.inr 1, [])} else ∅) at hmem
            split_ifs at hmem with hfinal
            · exact hfinal
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
              · exact hfinal
              · simp at hdrain

/-- A run beginning in a simulation state either remains a simulation of the
normalized DPDA, or has entered the drain after reaching a normalized final
configuration.  The statement permits arbitrary `Option` stack context. -/
public theorem emptyStack_simulation_reaches_classify (M : DPDA Q T S)
    {q : Q × Bool} {input : List T} {stack : List (EStack M)}
    {d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches
      ⟨Sum.inl q, input, stack⟩ d) :
    (∃ (p : Q × Bool) (output : List T) (result : List (EStack M)),
      d = ⟨Sum.inl p, output, result⟩ ∧
      M.firstFinal.toPDA.Reaches
        ⟨q, input, stack.filterMap id⟩
        ⟨p, output, result.filterMap id⟩) ∨
    (d.state = Sum.inr 1 ∧
      ∃ (p : Q × Bool) (output : List T) (result : List S),
        p ∈ M.firstFinal.final_states ∧
        M.firstFinal.toPDA.Reaches
          ⟨q, input, stack.filterMap id⟩
          ⟨p, output, result⟩) := by
  classical
  induction h with
  | refl =>
      exact Or.inl ⟨q, input, stack, rfl, Relation.ReflTransGen.refl⟩
  | @tail c d hreach hstep ih =>
      rcases ih with
        ⟨p, output, result, rfl, hsim⟩ |
        ⟨hcstate, p, output, result, hp, hsim⟩
      · rcases d with ⟨state, nextInput, nextStack⟩
        cases state with
        | inl next =>
            exact Or.inl ⟨next, nextInput, nextStack, rfl,
              hsim.tail (emptyStack_simulation_step_projects M hstep)⟩
        | inr i =>
            rcases i with ⟨i, hi⟩
            have hi' : i = 0 ∨ i = 1 := by omega
            rcases hi' with rfl | rfl
            · exact False.elim
                (emptyStack_step_target_ne_boot M hstep rfl)
            · exact Or.inr ⟨rfl, p, output, result.filterMap id,
                simulation_step_to_drain_final M hstep rfl, hsim⟩
      · rcases c with ⟨state, currentInput, currentStack⟩
        simp only at hcstate
        subst state
        obtain ⟨Z, rest, hstack, hd⟩ := drain_step_shape M hstep
        subst currentStack
        subst d
        exact Or.inr ⟨rfl, p, output, result, hp, hsim⟩

/-- Every nonempty simulation-to-simulation FS→ES run projects to a
nonempty run of the normalized DPDA, even when its untouched stack context
contains the FS→ES bottom marker. -/
private theorem simulation_transGen_projects (M : DPDA Q T S)
    {q p : Q × Bool} {input output : List T}
    {stack result : List (EStack M)}
    (h : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
      ⟨Sum.inl q, input, stack⟩
      ⟨Sum.inl p, output, result⟩) :
    Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
      ⟨q, input, stack.filterMap id⟩
      ⟨p, output, result.filterMap id⟩ := by
  obtain ⟨d, hfirst, hrest⟩ := Relation.TransGen.head'_iff.mp h
  rcases d with ⟨state, nextInput, nextStack⟩
  cases state with
  | inl p =>
      have hproject := emptyStack_simulation_step_projects M hfirst
      have hclassify := emptyStack_simulation_reaches_classify M hrest
      rcases hclassify with
        ⟨next, output, result, heq, hprojectRest⟩ |
        ⟨hstate, next, output, result, hfinal, hprojectRest⟩
      · cases heq
        exact Relation.TransGen.head' hproject hprojectRest
      · simp at hstate
  | inr i =>
      rcases i with ⟨i, hi⟩
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · exact False.elim
          (emptyStack_step_target_ne_boot M hfirst rfl)
      · have hstate := (drain_reaches_stack_length_le M hrest).1
        simp at hstate

/-- A nonempty exact cycle in the simulation part projects to a nonempty
exact cycle of the normalized DPDA. -/
private theorem simulation_cycle_projects (M : DPDA Q T S)
    {q : Q × Bool} {input : List T} {stack : List (EStack M)}
    (h : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
      ⟨Sum.inl q, input, stack⟩
      ⟨Sum.inl q, input, stack⟩) :
    Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
      ⟨q, input, stack.filterMap id⟩
      ⟨q, input, stack.filterMap id⟩ :=
  simulation_transGen_projects M h

private theorem reaches₁_append_stack_exact
    {Q₀ T₀ S₀ : Type} [Fintype Q₀] [Fintype T₀] [Fintype S₀]
    {P : PDA Q₀ T₀ S₀} {c d : PDA.conf P}
    (h : P.Reaches₁ c d) (suffix : List S₀) :
    P.Reaches₁ (c.appendStack suffix) (d.appendStack suffix) := by
  rcases c with ⟨q, input, stack⟩
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      rcases PDA.reaches₁_push h with
          ⟨a, tail, next, replacement, rfl, rfl, htransition⟩ |
          ⟨next, replacement, rfl, htransition⟩
      · exact Or.inl ⟨next, replacement, htransition, by
          simp [PDA.conf.appendStack, List.append_assoc]⟩
      · cases input with
        | nil =>
            exact ⟨next, replacement, htransition, by
              simp [PDA.conf.appendStack, List.append_assoc]⟩
        | cons a tail =>
            exact Or.inr ⟨next, replacement, htransition, by
              simp [PDA.conf.appendStack, List.append_assoc]⟩

/-- Stack and unconsumed-input locality preserve nonemptiness of an exact
run, not merely its reflexive-transitive reachability. -/
private theorem transGen_append_stack_input_exact
    {Q₀ T₀ S₀ : Type} [Fintype Q₀] [Fintype T₀] [Fintype S₀]
    {P : PDA Q₀ T₀ S₀} {c d : PDA.conf P}
    (h : Relation.TransGen (@PDA.Reaches₁ _ _ _ _ _ _ P) c d)
    (stackSuffix : List S₀) (inputSuffix : List T₀) :
    Relation.TransGen (@PDA.Reaches₁ _ _ _ _ _ _ P)
      ((c.appendStack stackSuffix).appendInput inputSuffix)
      ((d.appendStack stackSuffix).appendInput inputSuffix) := by
  obtain ⟨next, hfirst, hrest⟩ := Relation.TransGen.head'_iff.mp h
  have hfirstStack := reaches₁_append_stack_exact hfirst stackSuffix
  have hfirstInput : P.Reaches₁
      ((c.appendStack stackSuffix).appendInput inputSuffix)
      ((next.appendStack stackSuffix).appendInput inputSuffix) := by
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    exact (PDA.unconsumed_input_N (pda := P) inputSuffix).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hfirstStack)
  have hrestStack := PDA.Reaches.append_stack hrest stackSuffix
  have hrestInput :=
    (PDA.unconsumed_input inputSuffix).mp hrestStack
  exact Relation.TransGen.head' hfirstInput hrestInput

/-- Transporting an exact cycle forward along a deterministic run leaves an
exact cycle at every later configuration.  In a first-final normalized DPDA
this is impossible once a normalized final state is reached: the transported
cycle would be a nonempty same-input path from that final state to itself. -/
private theorem firstFinal_no_cycle_before_final (M : DPDA Q T S)
    {c : PDA.conf M.firstFinal.toPDA}
    {p : Q × Bool} {input : List T} {stack : List S}
    (hcycle : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA) c c)
    (hreach : M.firstFinal.toPDA.Reaches c ⟨p, input, stack⟩)
    (hfinal : p ∈ M.firstFinal.final_states) : False := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact (M.firstFinal_no_final_to_final_epsilon hfinal hcycle) hfinal
  | @head c middle hstep hrest ih =>
      obtain ⟨cycleNext, hcycleStep, hcycleRest⟩ :=
        Relation.TransGen.head'_iff.mp hcycle
      have hnext : cycleNext = middle :=
        M.firstFinal.toPDA_step_deterministic hcycleStep hstep
      subst cycleNext
      have hcycle' : Relation.TransGen
          (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA) middle middle :=
        Relation.TransGen.tail' hcycleRest hstep
      exact ih hcycle'

/-- The normalized FS→ES machine has no nonempty cycle with a continuation
to empty stack.  Boot cannot be re-entered, drain steps strictly shrink the
stack, and a simulation cycle projects to the deterministic first-final
machine.  A useful simulation continuation either itself reaches empty stack,
or enters drain from a normalized final state; both projected alternatives
contradict determinism and first-final normalization. -/
public theorem emptyStack_no_useful_cycle (M : DPDA Q T S)
    {c : PDA.conf (emptyStackPDA M)} {final : EState M}
    (hcycle : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M)) c c)
    (huseful : (emptyStackPDA M).Reaches c ⟨final, [], []⟩) : False := by
  rcases c with ⟨state, input, stack⟩
  cases state with
  | inl q =>
      have hcycle' := simulation_cycle_projects M hcycle
      rcases emptyStack_simulation_reaches_classify M huseful with
        ⟨p, output, result, heq, hreach⟩ |
        ⟨hstate, p, output, result, hp, hreach⟩
      · cases heq
        exact M.firstFinal.toPDA_no_cycle_before_empty_stack hcycle' hreach
      · exact firstFinal_no_cycle_before_final M hcycle' hreach hp
  | inr i =>
      rcases i with ⟨i, hi⟩
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · exact no_boot_cycle M hcycle
      · exact no_drain_cycle M hcycle

/-- The same exclusion holds for a useful self-embedding stack-growth
segment in the FS→ES machine.  In the simulation component the inserted
`Option` block either projects to a nonempty normalized-DPDA block, where the
counted stack-growth kernels apply, or projects to the empty block, where the
nonempty FS→ES segment becomes an exact normalized-DPDA cycle. -/
public theorem emptyStack_no_useful_stack_growth (M : DPDA Q T S)
    {q final : EState M} {base extra context : List (EStack M)}
    {input : List T}
    (hgrowth : (emptyStackPDA M).Reaches
      ⟨q, [], base⟩ ⟨q, [], base ++ extra⟩)
    (hextra : extra ≠ [])
    (huseful : (emptyStackPDA M).Reaches
      ⟨q, input, base ++ extra ++ context⟩ ⟨final, [], []⟩) :
    False := by
  have hconfigNe :
      (⟨q, [], base ++ extra⟩ : PDA.conf (emptyStackPDA M)) ≠
        ⟨q, [], base⟩ := by
    intro heq
    have hstack := congrArg PDA.conf.stack heq
    have hlength := congrArg List.length hstack
    simp only [List.length_append] at hlength
    have : extra.length = 0 := by omega
    exact hextra (List.length_eq_zero_iff.mp this)
  obtain hgrowthEq | hgrowthTrans :=
    Relation.reflTransGen_iff_eq_or_transGen.mp hgrowth
  · exact hconfigNe hgrowthEq
  · cases q with
    | inr i =>
        rcases i with ⟨i, hi⟩
        have hi' : i = 0 ∨ i = 1 := by omega
        rcases hi' with rfl | rfl
        · obtain ⟨before, _, hlast⟩ :=
            Relation.TransGen.tail'_iff.mp hgrowthTrans
          exact emptyStack_step_target_ne_boot M hlast rfl
        · have hlength :=
            (drain_reaches_stack_length_le M hgrowth).2.2
          simp only [List.length_append] at hlength
          have : extra.length = 0 := by omega
          exact hextra (List.length_eq_zero_iff.mp this)
    | inl source =>
        have hprojectTrans :=
          simulation_transGen_projects M hgrowthTrans
        have hgrowth' : M.firstFinal.toPDA.Reaches
            ⟨source, [], base.filterMap id⟩
            ⟨source, [],
              base.filterMap id ++ extra.filterMap id⟩ := by
          simpa [List.filterMap_append] using
            hprojectTrans.to_reflTransGen
        by_cases hprojectExtra : extra.filterMap id = []
        · have hcycle : Relation.TransGen
              (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
              ⟨source, [], base.filterMap id⟩
              ⟨source, [], base.filterMap id⟩ := by
            simpa [List.filterMap_append, hprojectExtra] using hprojectTrans
          have hcycleUseful : Relation.TransGen
              (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
              ⟨source, input,
                base.filterMap id ++ extra.filterMap id ++
                  context.filterMap id⟩
              ⟨source, input,
                base.filterMap id ++ extra.filterMap id ++
                  context.filterMap id⟩ := by
            have hlift := transGen_append_stack_input_exact hcycle
              (extra.filterMap id ++ context.filterMap id) input
            simpa [PDA.conf.appendStack, PDA.conf.appendInput,
              List.append_assoc] using hlift
          rcases emptyStack_simulation_reaches_classify M huseful with
            ⟨p, output, result, heq, hreach⟩ |
            ⟨hstate, p, output, result, hp, hreach⟩
          · cases heq
            have hreach' : M.firstFinal.toPDA.Reaches
                ⟨source, input,
                  base.filterMap id ++ extra.filterMap id ++
                    context.filterMap id⟩
                ⟨p, [], []⟩ := by
              simpa [List.filterMap_append] using hreach
            exact M.firstFinal.toPDA_no_cycle_before_empty_stack
              hcycleUseful hreach'
          · have hreach' : M.firstFinal.toPDA.Reaches
                ⟨source, input,
                  base.filterMap id ++ extra.filterMap id ++
                    context.filterMap id⟩
                ⟨p, output, result⟩ := by
              simpa [List.filterMap_append] using hreach
            exact firstFinal_no_cycle_before_final M
              hcycleUseful hreach' hp
        · rcases emptyStack_simulation_reaches_classify M huseful with
            ⟨p, output, result, heq, hreach⟩ |
            ⟨hstate, p, output, result, hp, hreach⟩
          · cases heq
            have hreach' : M.firstFinal.toPDA.Reaches
                ⟨source, input,
                  base.filterMap id ++ extra.filterMap id ++
                    context.filterMap id⟩
                ⟨p, [], []⟩ := by
              simpa [List.filterMap_append] using hreach
            exact M.firstFinal.toPDA_no_useful_stack_growth
              hgrowth' hprojectExtra hreach'
          · have hreach' : M.firstFinal.toPDA.Reaches
                ⟨source, input,
                  base.filterMap id ++ extra.filterMap id ++
                    context.filterMap id⟩
                ⟨p, output, result⟩ := by
              simpa [List.filterMap_append] using hreach
            exact M.firstFinal_toPDA_no_stack_growth_before_final
              hgrowth' hprojectExtra hreach' hp

end

end DPDA_to_LR
