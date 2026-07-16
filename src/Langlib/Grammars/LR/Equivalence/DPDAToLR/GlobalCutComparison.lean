module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulEpsilonCycles
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.AcceptingPaths
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.DrainFactorization

/-!
# Comparison of globally reachable FS→ES cuts

The normalized DPDA is deterministic inside the simulation component.  This
module packages that ordering at the concrete FS→ES configuration level and
is the prerequisite for the corresponding drain and mixed-cut comparisons.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-! ## The deterministic drain tail -/

/-- A drain step removes exactly the current top stack symbol. -/
private theorem drain_step_shape (M : DPDA Q T S)
    {input : List T} {stack : List (Option S)}
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

/-- The transition relation is functional once the drain has been entered. -/
private theorem drain_step_deterministic (M : DPDA Q T S)
    {input : List T} {stack : List (Option S)}
    {d₁ d₂ : PDA.conf (emptyStackPDA M)}
    (h₁ : (emptyStackPDA M).Reaches₁
      ⟨Sum.inr 1, input, stack⟩ d₁)
    (h₂ : (emptyStackPDA M).Reaches₁
      ⟨Sum.inr 1, input, stack⟩ d₂) :
    d₁ = d₂ := by
  obtain ⟨Z₁, rest₁, hstack₁, rfl⟩ := drain_step_shape M h₁
  obtain ⟨Z₂, rest₂, hstack₂, rfl⟩ := drain_step_shape M h₂
  have hrest := (List.cons.inj (hstack₁.symm.trans hstack₂)).2
  cases hrest
  rfl

/-- Equal-length computations from a drain configuration have equal
endpoints. -/
private theorem drain_reachesIn_deterministic (M : DPDA Q T S)
    {n : ℕ} {input : List T} {stack : List (Option S)}
    {d₁ d₂ : PDA.conf (emptyStackPDA M)}
    (h₁ : (emptyStackPDA M).ReachesIn n
      ⟨Sum.inr 1, input, stack⟩ d₁)
    (h₂ : (emptyStackPDA M).ReachesIn n
      ⟨Sum.inr 1, input, stack⟩ d₂) :
    d₁ = d₂ := by
  induction n generalizing stack d₁ d₂ with
  | zero =>
      exact (PDA.reachesIn_zero h₁).symm.trans (PDA.reachesIn_zero h₂)
  | succ n ih =>
      obtain ⟨middle₁, hprefix₁, hlast₁⟩ :=
        PDA.reachesIn_iff_split_first.mpr h₁
      obtain ⟨middle₂, hprefix₂, hlast₂⟩ :=
        PDA.reachesIn_iff_split_first.mpr h₂
      have hmiddle : middle₁ = middle₂ := drain_step_deterministic M
        (PDA.reaches₁_iff_reachesIn_one.mpr hprefix₁)
        (PDA.reaches₁_iff_reachesIn_one.mpr hprefix₂)
      subst middle₂
      obtain ⟨Z, rest, hstack, hmiddle⟩ := drain_step_shape M
        (PDA.reaches₁_iff_reachesIn_one.mpr hprefix₁)
      subst middle₁
      exact ih hlast₁ hlast₂

/-- Split a counted computation after a specified prefix length. -/
private theorem reachesIn_split_add
    {P : PDA Q T (Option S)} {n k : ℕ}
    {c d : PDA.conf P}
    (h : P.ReachesIn (n + k) c d) :
    ∃ middle : PDA.conf P,
      P.ReachesIn n c middle ∧ P.ReachesIn k middle d := by
  induction k generalizing d with
  | zero =>
      refine ⟨d, ?_, PDA.ReachesIn.refl d⟩
      simpa using h
  | succ k ih =>
      rw [Nat.add_succ] at h
      obtain ⟨before, hbefore, hlast⟩ :=
        PDA.reachesIn_iff_split_last.mpr h
      obtain ⟨middle, hprefix, hsuffix⟩ := ih hbefore
      exact ⟨middle, hprefix,
        PDA.ReachesIn.step hsuffix
          (PDA.reaches₁_iff_reachesIn_one.mpr hlast)⟩

/-- A shorter drain computation is the unique prefix of a longer one. -/
private theorem drain_reachesIn_prefix_of_le (M : DPDA Q T S)
    {n m : ℕ} {input : List T} {stack : List (Option S)}
    {d₁ d₂ : PDA.conf (emptyStackPDA M)}
    (hnm : n ≤ m)
    (h₁ : (emptyStackPDA M).ReachesIn n
      ⟨Sum.inr 1, input, stack⟩ d₁)
    (h₂ : (emptyStackPDA M).ReachesIn m
      ⟨Sum.inr 1, input, stack⟩ d₂) :
    (emptyStackPDA M).Reaches d₁ d₂ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  obtain ⟨middle, hprefix, hsuffix⟩ := reachesIn_split_add h₂
  have hmiddle : middle = d₁ :=
    drain_reachesIn_deterministic M hprefix h₁
  subst middle
  exact PDA.reaches_of_reachesIn hsuffix

/-- Two computations from the same drain configuration are prefix
comparable. -/
private theorem drain_reaches_comparable (M : DPDA Q T S)
    {input : List T} {stack : List (Option S)}
    {d₁ d₂ : PDA.conf (emptyStackPDA M)}
    (h₁ : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, input, stack⟩ d₁)
    (h₂ : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, input, stack⟩ d₂) :
    (emptyStackPDA M).Reaches d₁ d₂ ∨
      (emptyStackPDA M).Reaches d₂ d₁ := by
  rw [PDA.reaches_iff_reachesIn] at h₁ h₂
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  rcases le_total n m with hnm | hmn
  · exact Or.inl (drain_reachesIn_prefix_of_le M hnm hn hm)
  · exact Or.inr (drain_reachesIn_prefix_of_le M hmn hm hn)

/-- Any transition into the drain pops the current top stack symbol. -/
private theorem step_to_drain_shape (M : DPDA Q T S)
    {c : PDA.conf (emptyStackPDA M)}
    {input : List T} {drainStack : List (Option S)}
    (h : (emptyStackPDA M).Reaches₁ c
      ⟨Sum.inr 1, input, drainStack⟩) :
    ∃ Z rest, c.stack = Z :: rest ∧ drainStack = rest := by
  classical
  rcases c with ⟨state, sourceInput, sourceStack⟩
  cases sourceStack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      refine ⟨Z, rest, rfl, ?_⟩
      rcases PDA.reaches₁_push h with hread | hepsilon
      · rcases hread with
          ⟨a, tail, p, alpha, hinput, htarget, hmem⟩
        have hp : p = Sum.inr 1 := by
          simpa [htarget] using (congrArg PDA.conf.state htarget).symm
        subst p
        cases state <;> cases Z <;>
          simp [emptyStackPDA, PDA_FS_to_ES_pda,
            PDA_FS_to_ES_trans] at hmem
      · rcases hepsilon with ⟨p, alpha, htarget, hmem⟩
        have hp : p = Sum.inr 1 := by
          simpa [htarget] using (congrArg PDA.conf.state htarget).symm
        subst p
        have htargetStack : drainStack = alpha ++ rest := by
          simpa using congrArg PDA.conf.stack htarget
        cases state with
        | inl q =>
            cases Z with
            | none =>
                change (Sum.inr 1, alpha) ∈
                  (if q ∈ M.firstFinal.toPDA.final_states then
                    {(Sum.inr 1, [])} else ∅) at hmem
                split_ifs at hmem <;> simp_all
            | some Z =>
                change (Sum.inr 1, alpha) ∈
                    ((fun out : (Q × Bool) × List S =>
                      (Sum.inl out.1, out.2.map some)) ''
                        M.firstFinal.toPDA.transition_fun' q Z ∪
                      if q ∈ M.firstFinal.toPDA.final_states then
                        {(Sum.inr 1, [])} else ∅) at hmem
                rcases hmem with hsimulation | hdrain
                · rcases hsimulation with ⟨out, _, hout⟩
                  have := congrArg Prod.fst hout
                  simp at this
                · split_ifs at hdrain <;> simp_all
        | inr i =>
            rcases i with ⟨i, hi⟩
            have hi' : i = 0 ∨ i = 1 := by omega
            rcases hi' with rfl | rfl <;>
              cases Z <;>
              simp [emptyStackPDA, PDA_FS_to_ES_pda,
                PDA_FS_to_ES_eps] at hmem <;>
              simp_all

/-- Two one-step entries into the drain from the same configuration have the
same target. -/
private theorem steps_to_drain_eq (M : DPDA Q T S)
    {c : PDA.conf (emptyStackPDA M)}
    {input : List T} {stack₁ stack₂ : List (Option S)}
    (h₁ : (emptyStackPDA M).Reaches₁ c
      ⟨Sum.inr 1, input, stack₁⟩)
    (h₂ : (emptyStackPDA M).Reaches₁ c
      ⟨Sum.inr 1, input, stack₂⟩) :
    stack₁ = stack₂ := by
  obtain ⟨Z₁, rest₁, hsource₁, hstack₁⟩ :=
    step_to_drain_shape M h₁
  obtain ⟨Z₂, rest₂, hsource₂, hstack₂⟩ :=
    step_to_drain_shape M h₂
  have hrest : rest₁ = rest₂ :=
    (List.cons.inj (hsource₁.symm.trans hsource₂)).2
  exact hstack₁.trans (hrest.trans hstack₂.symm)

/-! ## First-final cuts -/

/-- Two normalized final configurations reached from the same normalized
initial configuration, with the same remaining input, coincide. -/
private theorem reachable_normalized_finals_eq (M : DPDA Q T S)
    {w input : List T} {q₁ q₂ : Q × Bool} {stack₁ stack₂ : List S}
    (hq₁ : q₁ ∈ M.firstFinal.final_states)
    (hq₂ : q₂ ∈ M.firstFinal.final_states)
    (h₁ : M.firstFinal.toPDA.Reaches
      ⟨M.firstFinal.initial_state, w, [M.firstFinal.start_symbol]⟩
      ⟨q₁, input, stack₁⟩)
    (h₂ : M.firstFinal.toPDA.Reaches
      ⟨M.firstFinal.initial_state, w, [M.firstFinal.start_symbol]⟩
      ⟨q₂, input, stack₂⟩) :
    (⟨q₁, input, stack₁⟩ : PDA.conf M.firstFinal.toPDA) =
      ⟨q₂, input, stack₂⟩ := by
  rcases M.firstFinal.toPDA_reaches_comparable h₁ h₂ with h₁₂ | h₂₁
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h₁₂ with
        heq | hstrict
    · exact heq.symm
    · exact False.elim
        ((M.firstFinal_no_final_to_final_epsilon hq₁ hstrict) hq₂)
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h₂₁ with
        heq | hstrict
    · exact heq
    · exact False.elim
        ((M.firstFinal_no_final_to_final_epsilon hq₂ hstrict) hq₁)

/-- A globally reachable simulation cut that still has a useful continuation
must occur no later than any globally reachable normalized final cut on the
same empty-input computation.  Otherwise the useful continuation would reach
a second normalized final after a nonempty path from the first one. -/
private theorem useful_simulation_precedes_final (M : DPDA Q T S)
    {w : List T} {q p : Q × Bool}
    {simStack : List (Option S)} {gamma delta : List S}
    (hstack : simStack = gamma.map some ++ [none])
    (hsim : M.firstFinal.toPDA.Reaches
      ⟨M.firstFinal.initial_state, w, [M.firstFinal.start_symbol]⟩
      ⟨q, [], gamma⟩)
    (hp : p ∈ M.firstFinal.final_states)
    (hfinal : M.firstFinal.toPDA.Reaches
      ⟨M.firstFinal.initial_state, w, [M.firstFinal.start_symbol]⟩
      ⟨p, [], delta⟩)
    (huseful : (emptyStackPDA M).Reaches
      ⟨Sum.inl q, [], simStack⟩ ⟨Sum.inr 1, [], []⟩) :
    M.firstFinal.toPDA.Reaches
      ⟨q, [], gamma⟩ ⟨p, [], delta⟩ := by
  classical
  rcases M.firstFinal.toPDA_reaches_comparable hsim hfinal with
      hsimFinal | hfinalSim
  · exact hsimFinal
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hfinalSim with
        heq | hstrict
    · simpa [heq] using
        (Relation.ReflTransGen.refl : M.firstFinal.toPDA.Reaches
          ⟨p, [], delta⟩ ⟨p, [], delta⟩)
    · rcases emptyStack_simulation_reaches_classify M huseful with
          ⟨next, output, result, hend, hproject⟩ |
          ⟨hend, next, output, result, hnextFinal, hproject⟩
      · have hbad := congrArg PDA.conf.state hend
        simp at hbad
      · subst simStack
        have hproject' : M.firstFinal.toPDA.Reaches
            ⟨q, [], gamma⟩ ⟨next, output, result⟩ := by
          simpa [List.filterMap_append] using hproject
        obtain ⟨consumed, hconsumed⟩ := PDA.decreasing_input hproject'
        have houtput : output = [] := by
          simpa using (List.eq_nil_of_append_eq_nil hconsumed.symm).2
        subst output
        have hforbidden : Relation.TransGen
            (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
            ⟨p, [], delta⟩ ⟨next, [], result⟩ :=
          hstrict.trans_left hproject'
        exact False.elim
          ((M.firstFinal_no_final_to_final_epsilon hp hforbidden)
            hnextFinal)

/-- Globally reachable cuts that both remain in the simulation component of
the FS→ES machine are linearly ordered. -/
public theorem emptyStack_global_simulation_cuts_comparable
    (M : DPDA Q T S)
    {w input : List T} {q₁ q₂ : Q × Bool}
    {stack₁ stack₂ : List (Option S)}
    (h₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q₁, input, stack₁⟩)
    (h₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q₂, input, stack₂⟩) :
    (emptyStackPDA M).Reaches
        ⟨Sum.inl q₁, input, stack₁⟩
        ⟨Sum.inl q₂, input, stack₂⟩ ∨
      (emptyStackPDA M).Reaches
        ⟨Sum.inl q₂, input, stack₂⟩
        ⟨Sum.inl q₁, input, stack₁⟩ := by
  obtain ⟨underStack₁, hstack₁, hnormalized₁⟩ :=
    emptyStack_reachable_simulation_shape M h₁
  obtain ⟨underStack₂, hstack₂, hnormalized₂⟩ :=
    emptyStack_reachable_simulation_shape M h₂
  subst stack₁
  subst stack₂
  rcases M.firstFinal.toPDA_reaches_comparable
      hnormalized₁ hnormalized₂ with h₁₂ | h₂₁
  · left
    simpa [emptyStackPDA, liftConf] using
      simulation_reaches M.firstFinal.toPDA _ _ h₁₂
  · right
    simpa [emptyStackPDA, liftConf] using
      simulation_reaches M.firstFinal.toPDA _ _ h₂₁

/-- Globally reachable cuts in the drain component are linearly ordered.
This holds for every shared remaining input, not only for accepting
computations at empty input. -/
public theorem emptyStack_global_drain_cuts_comparable
    (M : DPDA Q T S)
    {w input : List T} {stack₁ stack₂ : List (Option S)}
    (h₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inr 1, input, stack₁⟩)
    (h₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inr 1, input, stack₂⟩) :
    (emptyStackPDA M).Reaches
        ⟨Sum.inr 1, input, stack₁⟩
        ⟨Sum.inr 1, input, stack₂⟩ ∨
      (emptyStackPDA M).Reaches
        ⟨Sum.inr 1, input, stack₂⟩
        ⟨Sum.inr 1, input, stack₁⟩ := by
  obtain ⟨p₁, delta₁, entryStack₁, hp₁, hnormalized₁,
      hentry₁, htail₁⟩ :=
    emptyStack_global_drain_factorization M h₁
  obtain ⟨p₂, delta₂, entryStack₂, hp₂, hnormalized₂,
      hentry₂, htail₂⟩ :=
    emptyStack_global_drain_factorization M h₂
  have hfinal := reachable_normalized_finals_eq M
    hp₁ hp₂ hnormalized₁ hnormalized₂
  cases hfinal
  have hentryStack : entryStack₁ = entryStack₂ :=
    steps_to_drain_eq M hentry₁ hentry₂
  subst entryStack₂
  exact drain_reaches_comparable M htail₁ htail₂

/-- A useful globally reachable simulation cut precedes every useful drain
cut at the same remaining input.  Usefulness of the drain cut first forces
that input to be empty; first-final normalization then rules out the only
possible reverse ordering in the normalized simulation. -/
public theorem emptyStack_global_simulation_drain_useful
    (M : DPDA Q T S)
    {w input : List T} {q : Q × Bool}
    {simStack drainStack : List (Option S)}
    {final₁ final₂ : EState M}
    (hsimGlobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q, input, simStack⟩)
    (hdrainGlobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inr 1, input, drainStack⟩)
    (hsimUseful : (emptyStackPDA M).Reaches
      ⟨Sum.inl q, input, simStack⟩ ⟨final₁, [], []⟩)
    (hdrainUseful : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, input, drainStack⟩ ⟨final₂, [], []⟩) :
    (emptyStackPDA M).Reaches
      ⟨Sum.inl q, input, simStack⟩
      ⟨Sum.inr 1, input, drainStack⟩ := by
  have hinput : input = [] := by
    have hsame := drain_reaches_input_eq M hdrainUseful
    simpa using hsame.symm
  subst input
  have hfinal₁ : final₁ = Sum.inr 1 :=
    emptyStack_accepting_state_eq_drain M
      (hsimGlobal.trans hsimUseful)
  subst final₁
  obtain ⟨gamma, hsimStack, hnormalizedSim⟩ :=
    emptyStack_reachable_simulation_shape M hsimGlobal
  obtain ⟨p, delta, entryStack, hp, hnormalizedFinal,
      hentry, htail⟩ :=
    emptyStack_global_drain_factorization M hdrainGlobal
  have hnormalized := useful_simulation_precedes_final M
    hsimStack hnormalizedSim hp hnormalizedFinal hsimUseful
  have hlift := simulation_reaches M.firstFinal.toPDA _ _ hnormalized
  have hsuffix : (emptyStackPDA M).Reaches
      (liftConf M.firstFinal.toPDA ⟨p, [], delta⟩)
      ⟨Sum.inr 1, [], drainStack⟩ :=
    (Relation.ReflTransGen.single hentry).trans htail
  subst simStack
  simpa [emptyStackPDA, liftConf] using hlift.trans hsuffix

/-- Two useful non-boot cuts reached at the same input position lie on one
ordered computation of the normalized empty-stack machine.  This packages
the simulation/simulation, drain/drain, and mixed phase comparisons behind a
single phase-independent interface. -/
public theorem emptyStack_global_useful_nonboot_cuts_comparable
    (M : DPDA Q T S)
    {w input : List T} {q₁ q₂ final₁ final₂ : EState M}
    {stack₁ stack₂ : List (EStack M)}
    (hglobal₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, input, stack₁⟩)
    (hglobal₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, input, stack₂⟩)
    (huseful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, input, stack₁⟩ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, input, stack₂⟩ ⟨final₂, [], []⟩)
    (hnonboot₁ : q₁ ≠ Sum.inr 0)
    (hnonboot₂ : q₂ ≠ Sum.inr 0) :
    (emptyStackPDA M).Reaches
        ⟨q₁, input, stack₁⟩ ⟨q₂, input, stack₂⟩ ∨
      (emptyStackPDA M).Reaches
        ⟨q₂, input, stack₂⟩ ⟨q₁, input, stack₁⟩ := by
  cases q₁ with
  | inl q₁ =>
      cases q₂ with
      | inl q₂ =>
          exact emptyStack_global_simulation_cuts_comparable M
            hglobal₁ hglobal₂
      | inr i₂ =>
          rcases i₂ with ⟨i₂, hi₂⟩
          have hi₂' : i₂ = 0 ∨ i₂ = 1 := by omega
          rcases hi₂' with rfl | rfl
          · exact False.elim (hnonboot₂ rfl)
          · exact Or.inl <| emptyStack_global_simulation_drain_useful M
              hglobal₁ hglobal₂ huseful₁ huseful₂
  | inr i₁ =>
      rcases i₁ with ⟨i₁, hi₁⟩
      have hi₁' : i₁ = 0 ∨ i₁ = 1 := by omega
      rcases hi₁' with rfl | rfl
      · exact False.elim (hnonboot₁ rfl)
      · cases q₂ with
        | inl q₂ =>
            exact Or.inr <| emptyStack_global_simulation_drain_useful M
              hglobal₂ hglobal₁ huseful₂ huseful₁
        | inr i₂ =>
            rcases i₂ with ⟨i₂, hi₂⟩
            have hi₂' : i₂ = 0 ∨ i₂ = 1 := by omega
            rcases hi₂' with rfl | rfl
            · exact False.elim (hnonboot₂ rfl)
            · exact emptyStack_global_drain_cuts_comparable M
                hglobal₁ hglobal₂

end

end DPDA_to_LR
