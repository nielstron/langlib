module

public import Langlib.Automata.DeterministicPushdown.Definition
public import Mathlib.Data.Fintype.Prod

/-!
# First-final normalization for deterministic pushdown automata

This file equips a DPDA with one extra bit of finite control.  The bit records
whether an accepting state has already been left since the most recent
input-reading transition.  Input transitions clear the bit, while
epsilon-transitions set it when their source state is accepting.  Only an
unmarked copy of an original accepting state is accepting.

Consequently the normalized machine recognizes exactly the same language, but
no nonempty epsilon-only path can run from one accepting configuration to
another.  This is the acceptance normalization used in the classical
DPDA-to-LR(1) characteristic-grammar construction.
-/

@[expose]
public section

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Add a bit recording whether a final state has already been left during the
current epsilon phase.  Reading input starts a fresh phase. -/
public noncomputable def firstFinal (M : DPDA Q T S) : DPDA (Q × Bool) T S := by
  classical
  refine
    { initial_state := (M.initial_state, false)
      start_symbol := M.start_symbol
      final_states := { qb | qb.2 = false ∧ qb.1 ∈ M.final_states }
      transition := fun qb a Z =>
        (M.transition qb.1 a Z).map fun out => ((out.1, false), out.2)
      epsilon_transition := fun qb Z =>
        (M.epsilon_transition qb.1 Z).map fun out =>
          ((out.1, qb.2 || decide (qb.1 ∈ M.final_states)), out.2)
      no_mixed := ?_ }
  intro qb Z hε a
  have hεM : M.epsilon_transition qb.1 Z ≠ none := by
    intro hnone
    simp [hnone] at hε
  have hδM := M.no_mixed qb.1 Z hεM a
  simp [hδM]

/-- Lift an original configuration, choosing the value of the first-final bit. -/
@[expose]
public def firstFinalLift (M : DPDA Q T S) (seen : Bool)
    (c : PDA.conf M.toPDA) : PDA.conf M.firstFinal.toPDA :=
  ⟨(c.state, seen), c.input, c.stack⟩

/-- Forget the first-final bit in a normalized configuration. -/
@[expose]
public def firstFinalErase (M : DPDA Q T S)
    (c : PDA.conf M.firstFinal.toPDA) : PDA.conf M.toPDA :=
  ⟨c.state.1, c.input, c.stack⟩

@[simp]
public theorem firstFinalErase_lift (M : DPDA Q T S) (seen : Bool)
    (c : PDA.conf M.toPDA) :
    M.firstFinalErase (M.firstFinalLift seen c) = c := by
  cases c
  rfl

@[simp]
public theorem firstFinalLift_initial (M : DPDA Q T S) (w : List T) :
    M.firstFinalLift false
        ⟨M.initial_state, w, [M.start_symbol]⟩ =
      ⟨M.firstFinal.initial_state, w, [M.firstFinal.start_symbol]⟩ := by
  rfl

@[simp]
public theorem firstFinal_lift_mem_final_iff (M : DPDA Q T S) (seen : Bool)
    (c : PDA.conf M.toPDA) :
    (M.firstFinalLift seen c).state ∈ M.firstFinal.final_states ↔
      seen = false ∧ c.state ∈ M.final_states := by
  simp [firstFinalLift, firstFinal]

/-! ## One-step simulation -/

/-- Every normalized step projects to the corresponding original step. -/
public theorem firstFinalErase_step (M : DPDA Q T S)
    {c d : PDA.conf M.firstFinal.toPDA}
    (h : @PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA c d) :
    @PDA.Reaches₁ _ _ _ _ _ _ M.toPDA
      (M.firstFinalErase c) (M.firstFinalErase d) := by
  rcases c with ⟨⟨q, seen⟩, input, stack⟩
  rcases d with ⟨⟨p, seen'⟩, input', stack'⟩
  cases input with
  | nil =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at h
      | cons Z rest =>
          simp only [PDA.Reaches₁, PDA.step, DPDA.toPDA, firstFinal,
            Set.mem_setOf_eq, firstFinalErase] at h ⊢
          rcases h with ⟨p', β, hε, hd⟩
          obtain ⟨hstate, rfl, rfl⟩ := PDA.conf.mk.inj hd
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hstate
          cases hM : M.epsilon_transition q Z with
          | none => simp [hM] at hε
          | some out =>
              rcases out with ⟨pM, βM⟩
              simp [hM] at hε
              rcases hε with ⟨rfl, rfl, rfl⟩
              exact ⟨pM, β, by simp, rfl⟩
  | cons a restInput =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at h
      | cons Z restStack =>
          simp only [PDA.Reaches₁, PDA.step, DPDA.toPDA, firstFinal,
            Set.mem_union, Set.mem_setOf_eq, firstFinalErase] at h ⊢
          rcases h with hδ | hε
          · rcases hδ with ⟨p', β, hδ, hd⟩
            obtain ⟨hstate, rfl, rfl⟩ := PDA.conf.mk.inj hd
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hstate
            cases hM : M.transition q a Z with
            | none => simp [hM] at hδ
            | some out =>
                rcases out with ⟨pM, βM⟩
                simp [hM] at hδ
                rcases hδ with ⟨rfl, rfl, rfl⟩
                exact Or.inl ⟨pM, β, by simp, rfl⟩
          · rcases hε with ⟨p', β, hε, hd⟩
            obtain ⟨hstate, rfl, rfl⟩ := PDA.conf.mk.inj hd
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hstate
            cases hM : M.epsilon_transition q Z with
            | none => simp [hM] at hε
            | some out =>
                rcases out with ⟨pM, βM⟩
                simp [hM] at hε
                rcases hε with ⟨rfl, rfl, rfl⟩
                exact Or.inr ⟨pM, β, by simp, rfl⟩

/-- Lift one original step.  The returned equation records exactly when the
new first-final bit is set: epsilon steps preserve/set it, while input steps
clear it. -/
public theorem firstFinalLift_step (M : DPDA Q T S) (seen : Bool)
    {c d : PDA.conf M.toPDA}
    (h : @PDA.Reaches₁ _ _ _ _ _ _ M.toPDA c d) :
    ∃ seen' : Bool,
      @PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA
        (M.firstFinalLift seen c) (M.firstFinalLift seen' d) ∧
      (seen' = true ↔
        c.input = d.input ∧ (seen = true ∨ c.state ∈ M.final_states)) := by
  classical
  rcases c with ⟨q, input, stack⟩
  rcases d with ⟨p, input', stack'⟩
  cases input with
  | nil =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at h
      | cons Z rest =>
          simp only [PDA.Reaches₁, PDA.step, DPDA.toPDA, Set.mem_setOf_eq] at h
          rcases h with ⟨p', β, hε, hd⟩
          obtain ⟨rfl, rfl, rfl⟩ := PDA.conf.mk.inj hd
          cases hM : M.epsilon_transition q Z with
          | none => simp [hM] at hε
          | some out =>
              rcases out with ⟨pM, βM⟩
              simp [hM] at hε
              rcases hε with ⟨rfl, rfl⟩
              refine ⟨seen || decide (q ∈ M.final_states), ?_, ?_⟩
              · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, firstFinal,
                  firstFinalLift, hM]
              · simp [Bool.or_eq_true]
  | cons a restInput =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at h
      | cons Z restStack =>
          simp only [PDA.Reaches₁, PDA.step, DPDA.toPDA, Set.mem_union,
            Set.mem_setOf_eq] at h
          rcases h with hδ | hε
          · rcases hδ with ⟨p', β, hδ, hd⟩
            obtain ⟨rfl, rfl, rfl⟩ := PDA.conf.mk.inj hd
            cases hM : M.transition q a Z with
            | none => simp [hM] at hδ
            | some out =>
                rcases out with ⟨pM, βM⟩
                simp [hM] at hδ
                rcases hδ with ⟨rfl, rfl⟩
                refine ⟨false, ?_, ?_⟩
                · exact Or.inl ⟨(p, false), β, by
                    simp [DPDA.toPDA, firstFinal, hM], rfl⟩
                · simp
          · rcases hε with ⟨p', β, hε, hd⟩
            obtain ⟨rfl, rfl, rfl⟩ := PDA.conf.mk.inj hd
            cases hM : M.epsilon_transition q Z with
            | none => simp [hM] at hε
            | some out =>
                rcases out with ⟨pM, βM⟩
                simp [hM] at hε
                rcases hε with ⟨rfl, rfl⟩
                refine ⟨seen || decide (q ∈ M.final_states), ?_, ?_⟩
                · exact Or.inr ⟨(p, seen || decide (q ∈ M.final_states)), β, by
                    simp [DPDA.toPDA, firstFinal, hM], rfl⟩
                · simp [Bool.or_eq_true]

/-! ## Multi-step simulation and the seen-final trace invariant -/

/-- Every normalized run projects to an original run. -/
public theorem firstFinalErase_reaches (M : DPDA Q T S)
    {c d : PDA.conf M.firstFinal.toPDA}
    (h : @PDA.Reaches _ _ _ _ _ _ M.firstFinal.toPDA c d) :
    @PDA.Reaches _ _ _ _ _ _ M.toPDA
      (M.firstFinalErase c) (M.firstFinalErase d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (M.firstFinalErase_step hstep)

/-- Lift an original run from a clear first-final bit.  If the resulting bit is
set, the lifted run has already visited an unmarked original final state with
the same remaining input as the endpoint.  In particular, no input transition
has occurred since that visit. -/
public theorem firstFinalLift_reaches_from_clear (M : DPDA Q T S)
    {c d : PDA.conf M.toPDA}
    (h : @PDA.Reaches _ _ _ _ _ _ M.toPDA c d) :
    ∃ seen : Bool,
      @PDA.Reaches _ _ _ _ _ _ M.firstFinal.toPDA
        (M.firstFinalLift false c) (M.firstFinalLift seen d) ∧
      (seen = true →
        ∃ e : PDA.conf M.toPDA,
          @PDA.Reaches _ _ _ _ _ _ M.firstFinal.toPDA
            (M.firstFinalLift false c) (M.firstFinalLift false e) ∧
          e.input = d.input ∧ e.state ∈ M.final_states) := by
  induction h with
  | refl =>
      exact ⟨false, Relation.ReflTransGen.refl, by simp⟩
  | @tail d e hreach hstep ih =>
      obtain ⟨seen, hlift, hseen⟩ := ih
      obtain ⟨seen', hliftStep, hseenStep⟩ := M.firstFinalLift_step seen hstep
      refine ⟨seen', Relation.ReflTransGen.tail hlift hliftStep, ?_⟩
      intro htrue
      have hsame : d.input = e.input := (hseenStep.mp htrue).1
      rcases (hseenStep.mp htrue).2 with hprevious | hfinal
      · obtain ⟨witness, hwreach, hwinput, hwfinal⟩ := hseen hprevious
        exact ⟨witness, hwreach, hwinput.trans hsame, hwfinal⟩
      · cases hSeen : seen
        · exact ⟨d, by simpa [hSeen] using hlift, hsame, hfinal⟩
        · obtain ⟨witness, hwreach, hwinput, hwfinal⟩ := hseen hSeen
          exact ⟨witness, hwreach, hwinput.trans hsame, hwfinal⟩

/-! ## Language preservation -/

/-- First-final normalization preserves final-state acceptance exactly. -/
public theorem firstFinal_acceptsByFinalState (M : DPDA Q T S) :
    M.firstFinal.acceptsByFinalState = M.acceptsByFinalState := by
  ext w
  constructor
  · rintro ⟨⟨q, seen⟩, hfinal, γ, hreach⟩
    have hproject := M.firstFinalErase_reaches hreach
    simp only [firstFinalErase] at hproject
    have hq : q ∈ M.final_states := by
      change seen = false ∧ q ∈ M.final_states at hfinal
      exact hfinal.2
    exact ⟨q, hq, γ, hproject⟩
  · rintro ⟨q, hq, γ, hreach⟩
    obtain ⟨seen, hlift, hseen⟩ := M.firstFinalLift_reaches_from_clear hreach
    cases hSeen : seen
    · refine ⟨(q, false), ?_, γ, ?_⟩
      · change false = false ∧ q ∈ M.final_states
        exact ⟨rfl, by simpa [DPDA.toPDA] using hq⟩
      · simpa [hSeen] using hlift
    · obtain ⟨e, hereach, heinput, hefinal⟩ := hseen hSeen
      rcases e with ⟨qe, einput, estack⟩
      simp only at heinput
      subst einput
      refine ⟨(qe, false), ?_, estack, ?_⟩
      · change false = false ∧ qe ∈ M.final_states
        exact ⟨rfl, hefinal⟩
      · simpa [DPDA.toPDA, firstFinalLift, firstFinal] using hereach

/-! ## No repeated final state in an epsilon phase -/

/-- If a run is split at an intermediate configuration and consumes no input
overall, then the intermediate configuration has the same remaining input too. -/
private theorem firstFinal_intermediate_input_eq (M : DPDA Q T S)
    {a b c : PDA.conf M.firstFinal.toPDA}
    (hab : @PDA.Reaches _ _ _ _ _ _ M.firstFinal.toPDA a b)
    (hbc : @PDA.Reaches _ _ _ _ _ _ M.firstFinal.toPDA b c)
    (hac : a.input = c.input) :
    b.input = c.input := by
  obtain ⟨u, hu⟩ := PDA.decreasing_input hab
  obtain ⟨v, hv⟩ := PDA.decreasing_input hbc
  have hlength := congrArg List.length hac
  rw [hu, hv] at hlength
  simp only [List.length_append] at hlength
  have hvzero : v.length = 0 := by omega
  have hvnil : v = [] := List.length_eq_zero_iff.mp hvzero
  simpa [hvnil] using hv

/-- An input-preserving normalized step sets the marker if it starts either
with a set marker or in an original final state. -/
private theorem firstFinal_step_sets_seen_of_same_input (M : DPDA Q T S)
    {c d : PDA.conf M.firstFinal.toPDA}
    (hstep : @PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA c d)
    (hinput : c.input = d.input)
    (hmarked : c.state.2 = true ∨ c.state.1 ∈ M.final_states) :
    d.state.2 = true := by
  classical
  rcases c with ⟨⟨q, seen⟩, input, stack⟩
  rcases d with ⟨⟨p, seen'⟩, input', stack'⟩
  simp only at hinput hmarked ⊢
  subst input'
  have hmark : (seen || decide (q ∈ M.final_states)) = true := by
    rcases hmarked with hseen | hfinal
    · simp [hseen]
    · simp [hfinal]
  cases input with
  | nil =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons Z rest =>
          simp only [PDA.Reaches₁, PDA.step] at hstep
          rcases hstep with ⟨p', β, hε, hd⟩
          cases hM : M.epsilon_transition q Z with
          | none => simp [DPDA.toPDA, firstFinal, hM] at hε
          | some out =>
              rcases out with ⟨pM, βM⟩
              simp [DPDA.toPDA, firstFinal, hM] at hε
              rcases hε with ⟨rfl, rfl⟩
              exact (congrArg (fun e => e.state.2) hd).trans hmark
  | cons a restInput =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons Z restStack =>
          simp only [PDA.Reaches₁, PDA.step, Set.mem_union,
            Set.mem_setOf_eq] at hstep
          rcases hstep with hδ | hε
          · rcases hδ with ⟨p', β, hδ, hd⟩
            have hlength := congrArg (fun e => e.input.length) hd
            simp only [List.length_cons] at hlength
            omega
          · rcases hε with ⟨p', β, hε, hd⟩
            cases hM : M.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, firstFinal, hM] at hε
            | some out =>
                rcases out with ⟨pM, βM⟩
                simp [DPDA.toPDA, firstFinal, hM] at hε
                rcases hε with ⟨rfl, rfl⟩
                exact (congrArg (fun e => e.state.2) hd).trans hmark

/-- Once set, the first-final marker stays set along any run that consumes no
input. -/
private theorem firstFinal_seen_true_of_reaches_same_input (M : DPDA Q T S)
    {c d : PDA.conf M.firstFinal.toPDA}
    (hreach : @PDA.Reaches _ _ _ _ _ _ M.firstFinal.toPDA c d)
    (hinput : c.input = d.input)
    (hseen : c.state.2 = true) :
    d.state.2 = true := by
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a h => a.input = d.input → a.state.2 = true → d.state.2 = true)
    hreach ?_ ?_ hinput hseen
  · intro _ h
    exact h
  · intro a b hab hbd ih had haSeen
    have hbInput := M.firstFinal_intermediate_input_eq
      (Relation.ReflTransGen.single hab) hbd had
    have habInput : a.input = b.input := had.trans hbInput.symm
    have hbSeen := M.firstFinal_step_sets_seen_of_same_input hab habInput (Or.inl haSeen)
    exact ih hbInput hbSeen

/-- No nonempty run starting in a normalized final configuration and consuming
no input can end in another normalized final configuration.  Stating the path
with `Relation.TransGen` excludes the reflexive zero-step path. -/
public theorem firstFinal_no_final_to_final_epsilon (M : DPDA Q T S)
    {q p : Q × Bool} {input : List T} {γ δ : List S}
    (hq : q ∈ M.firstFinal.final_states)
    (hreach : Relation.TransGen
      (@PDA.Reaches₁ _ _ _ _ _ _ M.firstFinal.toPDA)
      ⟨q, input, γ⟩ ⟨p, input, δ⟩) :
    p ∉ M.firstFinal.final_states := by
  intro hp
  change q.2 = false ∧ q.1 ∈ M.final_states at hq
  change p.2 = false ∧ p.1 ∈ M.final_states at hp
  obtain ⟨c, hfirst, hrest⟩ := Relation.TransGen.head'_iff.mp hreach
  have hcInput : c.input = input := M.firstFinal_intermediate_input_eq
    (Relation.ReflTransGen.single hfirst) hrest rfl
  have hfirstInput : (⟨q, input, γ⟩ : PDA.conf M.firstFinal.toPDA).input = c.input := by
    exact hcInput.symm
  have hcSeen := M.firstFinal_step_sets_seen_of_same_input
    hfirst hfirstInput (Or.inr hq.2)
  have hpSeen := M.firstFinal_seen_true_of_reaches_same_input hrest hcInput hcSeen
  have : false = true := hp.1.symm.trans hpSeen
  exact Bool.noConfusion this

end DPDA
