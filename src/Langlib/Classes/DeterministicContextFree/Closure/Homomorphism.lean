module

public import Langlib.Classes.DeterministicContextFree.Closure.Union
public import Langlib.Utilities.ClosurePredicates

/-!
# Deterministic Context-Free Languages Are Not Closed Under Homomorphism

If deterministic context-free languages were closed under arbitrary string
homomorphisms, then erasing the first symbol of a prefix-marked disjoint union
would make them closed under union.
-/

open PDA

namespace DCFHomomorphism

variable {T : Type} [Fintype T]

private inductive MarkState (Q₁ Q₂ : Type) where
  | start
  | left : Q₁ → MarkState Q₁ Q₂
  | right : Q₂ → MarkState Q₁ Q₂
deriving Fintype

private inductive MarkStack (S₁ S₂ : Type) where
  | bottom
  | left : S₁ → MarkStack S₁ S₂
  | right : S₂ → MarkStack S₁ S₂
deriving Fintype

namespace DPDA

variable {Q₁ Q₂ S₁ S₂ : Type}
variable [Fintype Q₁] [Fintype Q₂] [Fintype S₁] [Fintype S₂]

public abbrev LeftQuotientState (Q : Type) :=
  Bool × Q

public def leftQuotientSingleton {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A) : DPDA (LeftQuotientState Q) A S where
  initial_state := (false, M.initial_state)
  start_symbol := M.start_symbol
  final_states := {q | q.1 = true ∧ q.2 ∈ M.final_states}
  transition q x Z :=
    match q with
    | (true, q) => (M.transition q x Z).map fun p => ((true, p.1), p.2)
    | (false, _) => none
  epsilon_transition q Z :=
    match q with
    | (true, q) => (M.epsilon_transition q Z).map fun p => ((true, p.1), p.2)
    | (false, q) =>
        match M.epsilon_transition q Z with
        | some p => some ((false, p.1), p.2)
        | none => (M.transition q a Z).map fun p => ((true, p.1), p.2)
  no_mixed := by
    rintro ⟨mode, q⟩ Z hε x
    cases mode <;> simp [LeftQuotientState] at hε ⊢
    exact M.no_mixed q Z (by simpa using hε) x

private def leftQuotientConf {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A) :
    PDA.conf (leftQuotientSingleton M a).toPDA → PDA.conf M.toPDA
  | ⟨(false, q), input, stack⟩ => ⟨q, a :: input, stack⟩
  | ⟨(true, q), input, stack⟩ => ⟨q, input, stack⟩

private lemma leftQuotient_step_sound {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A)
    {c c' : PDA.conf (leftQuotientSingleton M a).toPDA}
    (hstep : PDA.Reaches₁ c c') :
    PDA.Reaches (leftQuotientConf M a c) (leftQuotientConf M a c') := by
  rcases c with ⟨⟨mode, q⟩, input, stack⟩
  cases stack with
  | nil =>
      simp [PDA.Reaches₁, PDA.step] at hstep
  | cons Z γ =>
      cases mode
      · cases input with
        | nil =>
          simp [PDA.Reaches₁, PDA.step, leftQuotientSingleton, DPDA.toPDA] at hstep
          cases hε : M.epsilon_transition q Z with
          | some eps =>
              rcases hstep with hstep | hbad
              ·
                rcases hstep with ⟨p, β, hp, rfl⟩
                have hp' : ((false, p), β) = ((false, eps.1), eps.2) := by
                  simpa [hε] using hp
                injection hp' with hpq hβ
                cases hpq
                cases hβ
                exact Relation.ReflTransGen.single
                  (Set.mem_union_right _ ⟨eps.1, eps.2, by simpa [DPDA.toPDA, hε], rfl⟩)
              · simp [hε] at hbad
          | none =>
              cases ht : M.transition q a Z with
              | none => simp [hε, ht] at hstep
              | some tr =>
                  simp [hε, ht] at hstep
                  rcases hstep with ⟨β, rfl, rfl⟩
                  exact Relation.ReflTransGen.single
                    (Set.mem_union_left _ ⟨tr.1, tr.2, by simpa [DPDA.toPDA, ht], rfl⟩)
        | cons x xs =>
          simp [PDA.Reaches₁, PDA.step, leftQuotientSingleton, DPDA.toPDA] at hstep
          cases hε : M.epsilon_transition q Z with
          | some eps =>
              rcases hstep with hstep | hbad
              ·
                rcases hstep with ⟨p, β, hp, rfl⟩
                have hp' : ((false, p), β) = ((false, eps.1), eps.2) := by
                  simpa [hε] using hp
                injection hp' with hpq hβ
                cases hpq
                cases hβ
                exact Relation.ReflTransGen.single
                  (Set.mem_union_right _ ⟨eps.1, eps.2, by simpa [DPDA.toPDA, hε], rfl⟩)
              · simp [hε] at hbad
          | none =>
              cases ht : M.transition q a Z with
              | none => simp [hε, ht] at hstep
              | some tr =>
                  simp [hε, ht] at hstep
                  rcases hstep with ⟨β, rfl, rfl⟩
                  exact Relation.ReflTransGen.single
                    (Set.mem_union_left _ ⟨tr.1, tr.2, by simpa [DPDA.toPDA, ht], rfl⟩)
      · cases input with
        | nil =>
            simp [PDA.Reaches₁, PDA.step, leftQuotientSingleton, DPDA.toPDA] at hstep
            cases hε : M.epsilon_transition q Z with
            | none => simp [hε] at hstep
            | some eps =>
                simp [hε] at hstep
                rcases hstep with ⟨β, rfl, rfl⟩
                exact Relation.ReflTransGen.single
                  ⟨eps.1, eps.2, by simpa [DPDA.toPDA, hε], rfl⟩
        | cons x xs =>
            simp [PDA.Reaches₁, PDA.step, leftQuotientSingleton, DPDA.toPDA] at hstep
            rcases hstep with hstep | hstep
            · cases ht : M.transition q x Z with
              | none => simp [ht] at hstep
              | some tr =>
                  simp [ht] at hstep
                  rcases hstep with ⟨β, rfl, rfl⟩
                  exact Relation.ReflTransGen.single
                    (Set.mem_union_left _ ⟨tr.1, tr.2, by simpa [DPDA.toPDA, ht], rfl⟩)
            · cases hε : M.epsilon_transition q Z with
              | none => simp [hε] at hstep
              | some eps =>
                  simp [hε] at hstep
                  rcases hstep with ⟨β, rfl, rfl⟩
                  exact Relation.ReflTransGen.single
                    (Set.mem_union_right _ ⟨eps.1, eps.2, by simpa [DPDA.toPDA, hε], rfl⟩)

private lemma leftQuotient_reaches_sound {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A)
    {c c' : PDA.conf (leftQuotientSingleton M a).toPDA}
    (hreach : PDA.Reaches c c') :
    PDA.Reaches (leftQuotientConf M a c) (leftQuotientConf M a c') := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans ih (leftQuotient_step_sound M a hstep)

private lemma leftQuotient_step_complete {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A)
    {c : PDA.conf (leftQuotientSingleton M a).toPDA} {d' : PDA.conf M.toPDA}
    (hstep : PDA.Reaches₁ (leftQuotientConf M a c) d') :
    ∃ c' : PDA.conf (leftQuotientSingleton M a).toPDA,
      PDA.Reaches c c' ∧ leftQuotientConf M a c' = d' := by
  rcases c with ⟨⟨mode, q⟩, input, stack⟩
  cases stack with
  | nil =>
      cases mode <;> simp [PDA.Reaches₁, PDA.step, leftQuotientConf] at hstep
  | cons Z γ =>
      cases mode
      · cases input with
        | nil =>
            simp [PDA.Reaches₁, PDA.step, leftQuotientConf, DPDA.toPDA] at hstep
            rcases hstep with hstep | hstep
            · rcases hstep with ⟨p, β, hp, rfl⟩
              cases hε : M.epsilon_transition q Z with
              | some eps =>
                  have hnone := M.no_mixed q Z (by simpa [hε]) a
                  simp [hnone] at hp
              | none =>
                  cases ht : M.transition q a Z with
                  | none => simp [DPDA.toPDA, ht] at hp
                  | some pβ =>
                      rcases pβ with ⟨p', β'⟩
                      simp [DPDA.toPDA, ht] at hp
                      rcases hp with ⟨rfl, rfl⟩
                      refine ⟨⟨(true, p), [], β ++ γ⟩, ?_, rfl⟩
                      exact Relation.ReflTransGen.single (by
                        unfold PDA.Reaches₁ PDA.step
                        refine ⟨(true, p), β, ?_, rfl⟩
                        simp [leftQuotientSingleton, DPDA.toPDA, hε, ht])
            · rcases hstep with ⟨p, β, hp, rfl⟩
              cases hε : M.epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  refine ⟨⟨(false, p), [], β ++ γ⟩, ?_, rfl⟩
                  exact Relation.ReflTransGen.single (by
                    unfold PDA.Reaches₁ PDA.step
                    refine ⟨(false, p), β, ?_, rfl⟩
                    simp [leftQuotientSingleton, DPDA.toPDA, hε])
        | cons x xs =>
            simp [PDA.Reaches₁, PDA.step, leftQuotientConf, DPDA.toPDA] at hstep
            rcases hstep with hstep | hstep
            · rcases hstep with ⟨p, β, hp, rfl⟩
              cases hε : M.epsilon_transition q Z with
              | some eps =>
                  have hnone := M.no_mixed q Z (by simpa [hε]) a
                  simp [hnone] at hp
              | none =>
                  cases ht : M.transition q a Z with
                  | none => simp [DPDA.toPDA, ht] at hp
                  | some pβ =>
                      rcases pβ with ⟨p', β'⟩
                      simp [DPDA.toPDA, ht] at hp
                      rcases hp with ⟨rfl, rfl⟩
                      refine ⟨⟨(true, p), x :: xs, β ++ γ⟩, ?_, rfl⟩
                      exact Relation.ReflTransGen.single (by
                        unfold PDA.Reaches₁ PDA.step
                        right
                        refine ⟨(true, p), β, ?_, rfl⟩
                        simp [leftQuotientSingleton, DPDA.toPDA, hε, ht])
            · rcases hstep with ⟨p, β, hp, rfl⟩
              cases hε : M.epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  refine ⟨⟨(false, p), x :: xs, β ++ γ⟩, ?_, rfl⟩
                  exact Relation.ReflTransGen.single (by
                    unfold PDA.Reaches₁ PDA.step
                    right
                    refine ⟨(false, p), β, ?_, rfl⟩
                    simp [leftQuotientSingleton, DPDA.toPDA, hε])
      · cases input with
        | nil =>
            simp [PDA.Reaches₁, PDA.step, leftQuotientConf, DPDA.toPDA] at hstep
            rcases hstep with ⟨p, β, hp, rfl⟩
            cases hε : M.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [DPDA.toPDA, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨(true, p), [], β ++ γ⟩, ?_, rfl⟩
                exact Relation.ReflTransGen.single (by
                  unfold PDA.Reaches₁ PDA.step
                  refine ⟨(true, p), β, ?_, rfl⟩
                  simp [leftQuotientSingleton, DPDA.toPDA, hε])
        | cons x xs =>
            simp [PDA.Reaches₁, PDA.step, leftQuotientConf, DPDA.toPDA] at hstep
            rcases hstep with hstep | hstep
            · rcases hstep with ⟨p, β, hp, rfl⟩
              cases ht : M.transition q x Z with
              | none => simp [DPDA.toPDA, ht] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, ht] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  refine ⟨⟨(true, p), xs, β ++ γ⟩, ?_, rfl⟩
                  exact Relation.ReflTransGen.single (by
                    unfold PDA.Reaches₁ PDA.step
                    left
                    refine ⟨(true, p), β, ?_, rfl⟩
                    simp [leftQuotientSingleton, DPDA.toPDA, ht])
            · rcases hstep with ⟨p, β, hp, rfl⟩
              cases hε : M.epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  refine ⟨⟨(true, p), x :: xs, β ++ γ⟩, ?_, rfl⟩
                  exact Relation.ReflTransGen.single (by
                    unfold PDA.Reaches₁ PDA.step
                    right
                    refine ⟨(true, p), β, ?_, rfl⟩
                    simp [leftQuotientSingleton, DPDA.toPDA, hε])

private lemma leftQuotient_reaches_complete_aux {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A)
    {d d' : PDA.conf M.toPDA} (hreach : PDA.Reaches d d') :
    ∀ c : PDA.conf (leftQuotientSingleton M a).toPDA,
    leftQuotientConf M a c = d →
    ∃ c' : PDA.conf (leftQuotientSingleton M a).toPDA,
      PDA.Reaches c c' ∧ leftQuotientConf M a c' = d' := by
  induction hreach with
  | refl =>
      intro c hsrc
      exact ⟨c, Relation.ReflTransGen.refl, hsrc⟩
  | tail _ hstep ih =>
      intro c hsrc
      rcases ih c hsrc with ⟨cMid, hMid, hmap⟩
      rcases leftQuotient_step_complete M a (c := cMid) (by
        rw [hmap]
        exact hstep) with
        ⟨cEnd, hEnd, hmapEnd⟩
      exact ⟨cEnd, Relation.ReflTransGen.trans hMid hEnd, hmapEnd⟩

private lemma leftQuotient_reaches_complete {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A)
    {c : PDA.conf (leftQuotientSingleton M a).toPDA} {d' : PDA.conf M.toPDA}
    (hreach : PDA.Reaches (leftQuotientConf M a c) d') :
    ∃ c' : PDA.conf (leftQuotientSingleton M a).toPDA,
      PDA.Reaches c c' ∧ leftQuotientConf M a c' = d' :=
  leftQuotient_reaches_complete_aux M a hreach c rfl

public theorem leftQuotientSingleton_accepts {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A) :
    (leftQuotientSingleton M a).acceptsByFinalState =
      [a] \\ M.acceptsByFinalState := by
  ext w
  constructor
  · rintro ⟨q, hq, γ, hreach⟩
    rcases q with ⟨mode, q⟩
    rcases hq with ⟨hmode, hq⟩
    simp at hmode
    subst mode
    change a :: w ∈ M.acceptsByFinalState
    exact ⟨q, hq, γ, leftQuotient_reaches_sound M a hreach⟩
  · intro hw
    change a :: w ∈ M.acceptsByFinalState at hw
    rcases hw with ⟨q, hq, γ, hreach⟩
    rcases leftQuotient_reaches_complete M a
        (c := ⟨(false, M.initial_state), w, [M.start_symbol]⟩)
        (d' := ⟨q, [], γ⟩) hreach with ⟨c, hc, hmap⟩
    rcases c with ⟨⟨mode, q'⟩, input, stack⟩
    cases mode
    · simp [leftQuotientConf] at hmap
    · simp [leftQuotientConf] at hmap
      rcases hmap with ⟨rfl, rfl, rfl⟩
      exact ⟨(true, q'), by
        constructor
        · rfl
        · change q' ∈ M.final_states at hq
          exact hq, stack, hc⟩

public theorem is_DCF_leftQuotient_singleton {Q A S : Type} [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) (a : A) :
    is_DCF ([a] \\ M.acceptsByFinalState) :=
  ⟨_, _, inferInstance, inferInstance, leftQuotientSingleton M a,
    leftQuotientSingleton_accepts M a⟩

private def markTransitionLeft (M : DPDA Q₁ T S₁)
    (q : Q₁) (a : T) (Z : S₁) :
    Option (MarkState Q₁ Q₂ × List (MarkStack S₁ S₂)) :=
  match M.transition q a Z with
  | none => none
  | some (q', γ) => some (MarkState.left q', γ.map MarkStack.left)

private def markTransitionRight (M : DPDA Q₂ T S₂)
    (q : Q₂) (a : T) (Z : S₂) :
    Option (MarkState Q₁ Q₂ × List (MarkStack S₁ S₂)) :=
  match M.transition q a Z with
  | none => none
  | some (q', γ) => some (MarkState.right q', γ.map MarkStack.right)

private def markEpsilonLeft (M : DPDA Q₁ T S₁) (q : Q₁) (Z : S₁) :
    Option (MarkState Q₁ Q₂ × List (MarkStack S₁ S₂)) :=
  match M.epsilon_transition q Z with
  | none => none
  | some (q', γ) => some (MarkState.left q', γ.map MarkStack.left)

private def markEpsilonRight (M : DPDA Q₂ T S₂) (q : Q₂) (Z : S₂) :
    Option (MarkState Q₁ Q₂ × List (MarkStack S₁ S₂)) :=
  match M.epsilon_transition q Z with
  | none => none
  | some (q', γ) => some (MarkState.right q', γ.map MarkStack.right)

private def markedUnion (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    DPDA (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) where
  initial_state := MarkState.start
  start_symbol := MarkStack.bottom
  final_states :=
    {q | (∃ q₁ ∈ M₁.final_states, q = MarkState.left q₁) ∨
      (∃ q₂ ∈ M₂.final_states, q = MarkState.right q₂)}
  transition q a Z :=
    match q, a, Z with
    | MarkState.start, Sum.inl false, MarkStack.bottom =>
        some (MarkState.left M₁.initial_state, [MarkStack.left M₁.start_symbol])
    | MarkState.start, Sum.inl true, MarkStack.bottom =>
        some (MarkState.right M₂.initial_state, [MarkStack.right M₂.start_symbol])
    | MarkState.left q₁, Sum.inr a, MarkStack.left Z₁ =>
        markTransitionLeft (Q₂ := Q₂) (S₂ := S₂) M₁ q₁ a Z₁
    | MarkState.right q₂, Sum.inr a, MarkStack.right Z₂ =>
        markTransitionRight (Q₁ := Q₁) (S₁ := S₁) M₂ q₂ a Z₂
    | _, _, _ => none
  epsilon_transition q Z :=
    match q, Z with
    | MarkState.left q₁, MarkStack.left Z₁ =>
        markEpsilonLeft (Q₂ := Q₂) (S₂ := S₂) M₁ q₁ Z₁
    | MarkState.right q₂, MarkStack.right Z₂ =>
        markEpsilonRight (Q₁ := Q₁) (S₁ := S₁) M₂ q₂ Z₂
    | _, _ => none
  no_mixed := by
    intro q Z hε a
    cases q <;> cases Z <;> cases a <;>
      simp [markEpsilonLeft, markEpsilonRight, markTransitionLeft, markTransitionRight] at hε ⊢
    · rename_i q₁ Z₁ t
      split at hε
      · exact False.elim (hε rfl)
      · rename_i q' γ hε₁
        have hnone := M₁.no_mixed q₁ Z₁ (by simp [hε₁]) t
        simpa [markTransitionLeft, hnone]
    · rename_i q₂ Z₂ t
      split at hε
      · exact False.elim (hε rfl)
      · rename_i q' γ hε₁
        have hnone := M₂.no_mixed q₂ Z₂ (by simp [hε₁]) t
        simpa [markTransitionRight, hnone]

private def leftConf (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    PDA.conf M₁.toPDA → PDA.conf (markedUnion M₁ M₂).toPDA
  | ⟨q, w, γ⟩ => ⟨MarkState.left q, w.map Sum.inr, γ.map MarkStack.left⟩

private def rightConf (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    PDA.conf M₂.toPDA → PDA.conf (markedUnion M₁ M₂).toPDA
  | ⟨q, w, γ⟩ => ⟨MarkState.right q, w.map Sum.inr, γ.map MarkStack.right⟩

private lemma left_reaches₁_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₁.toPDA} :
    PDA.Reaches₁ c c' →
      @PDA.Reaches₁ (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
        (markedUnion M₁ M₂).toPDA (leftConf M₁ M₂ c) (leftConf M₁ M₂ c') := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases c' with ⟨q', w', γ'⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn Q₁ T S₁ _ _ _ M₁.toPDA 1 ⟨q, w, []⟩ ⟨q', w', γ'⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with ⟨p, β, hp, hcfg⟩
          refine ⟨MarkState.left p, β.map MarkStack.left, ?_, ?_⟩
          · cases hε : M₁.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [DPDA.toPDA, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε]
          · simpa [leftConf, List.map_append] using congrArg (leftConf M₁ M₂) hcfg
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            left
            refine ⟨MarkState.left p, β.map MarkStack.left, ?_, ?_⟩
            · cases ht : M₁.transition q a Z with
              | none => simp [DPDA.toPDA, ht] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, ht] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, markedUnion, markTransitionLeft, ht]
            · simpa [leftConf, List.map_append] using congrArg (leftConf M₁ M₂) hcfg
          · rcases h with ⟨p, β, hp, hcfg⟩
            right
            refine ⟨MarkState.left p, β.map MarkStack.left, ?_, ?_⟩
            · cases hε : M₁.epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε]
            · simpa [leftConf, List.map_append] using congrArg (leftConf M₁ M₂) hcfg

private lemma left_reaches_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₁.toPDA} :
    PDA.Reaches c c' →
      @PDA.Reaches (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
        (markedUnion M₁ M₂).toPDA (leftConf M₁ M₂ c) (leftConf M₁ M₂ c') := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (left_reaches₁_map M₁ M₂ hstep)

private lemma right_reaches₁_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₂.toPDA} :
    PDA.Reaches₁ c c' →
      @PDA.Reaches₁ (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
        (markedUnion M₁ M₂).toPDA (rightConf M₁ M₂ c) (rightConf M₁ M₂ c') := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases c' with ⟨q', w', γ'⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn Q₂ T S₂ _ _ _ M₂.toPDA 1 ⟨q, w, []⟩ ⟨q', w', γ'⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with ⟨p, β, hp, hcfg⟩
          refine ⟨MarkState.right p, β.map MarkStack.right, ?_, ?_⟩
          · cases hε : M₂.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [DPDA.toPDA, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε]
          · simpa [rightConf, List.map_append] using congrArg (rightConf M₁ M₂) hcfg
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            left
            refine ⟨MarkState.right p, β.map MarkStack.right, ?_, ?_⟩
            · cases ht : M₂.transition q a Z with
              | none => simp [DPDA.toPDA, ht] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, ht] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, markedUnion, markTransitionRight, ht]
            · simpa [rightConf, List.map_append] using congrArg (rightConf M₁ M₂) hcfg
          · rcases h with ⟨p, β, hp, hcfg⟩
            right
            refine ⟨MarkState.right p, β.map MarkStack.right, ?_, ?_⟩
            · cases hε : M₂.epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε]
            · simpa [rightConf, List.map_append] using congrArg (rightConf M₁ M₂) hcfg

private lemma right_reaches_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₂.toPDA} :
    PDA.Reaches c c' →
      @PDA.Reaches (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
        (markedUnion M₁ M₂).toPDA (rightConf M₁ M₂ c) (rightConf M₁ M₂ c') := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (right_reaches₁_map M₁ M₂ hstep)

private lemma left_reaches₁_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₁.toPDA} {d : PDA.conf (markedUnion M₁ M₂).toPDA} :
    @PDA.Reaches₁ (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
      (markedUnion M₁ M₂).toPDA (leftConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₁.toPDA, d = leftConf M₁ M₂ c' ∧ PDA.Reaches₁ c c' := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases d with ⟨qd, wd, γd⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
          (markedUnion M₁ M₂).toPDA 1 (leftConf M₁ M₂ ⟨q, w, []⟩) ⟨qd, wd, γd⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with ⟨p, β, hp, hcfg⟩
          cases hε : M₁.epsilon_transition q Z with
          | none => simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
          | some pβ =>
              rcases pβ with ⟨p', β'⟩
              simp [leftConf, DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
              rcases hp with ⟨rfl, rfl⟩
              refine ⟨⟨p', [], β' ++ γ⟩, ?_, ?_⟩
              · simpa [leftConf, List.map_append] using hcfg
              · refine ⟨p', β', ?_, rfl⟩
                simp [DPDA.toPDA, hε]
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases ht : M₁.transition q a Z with
            | none => simp [DPDA.toPDA, markedUnion, markTransitionLeft, ht] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [leftConf, DPDA.toPDA, markedUnion, markTransitionLeft, ht] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [leftConf, List.map_append] using hcfg
                · left
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, ht]
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases hε : M₁.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [leftConf, DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', a :: w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [leftConf, List.map_append] using hcfg
                · right
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, hε]

private lemma left_reaches_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₁.toPDA} {d : PDA.conf (markedUnion M₁ M₂).toPDA} :
    @PDA.Reaches (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
      (markedUnion M₁ M₂).toPDA (leftConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₁.toPDA, d = leftConf M₁ M₂ c' ∧ PDA.Reaches c c' := by
  intro h
  induction h with
  | refl => exact ⟨c, rfl, PDA.Reaches.refl _⟩
  | tail _ hstep ih =>
      rcases ih with ⟨c', rfl, hc'⟩
      rcases left_reaches₁_unmap M₁ M₂ hstep with ⟨c'', rfl, hstep'⟩
      exact ⟨c'', rfl, Relation.ReflTransGen.tail hc' hstep'⟩

private lemma right_reaches₁_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₂.toPDA} {d : PDA.conf (markedUnion M₁ M₂).toPDA} :
    @PDA.Reaches₁ (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
      (markedUnion M₁ M₂).toPDA (rightConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₂.toPDA, d = rightConf M₁ M₂ c' ∧ PDA.Reaches₁ c c' := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases d with ⟨qd, wd, γd⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
          (markedUnion M₁ M₂).toPDA 1 (rightConf M₁ M₂ ⟨q, w, []⟩) ⟨qd, wd, γd⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with ⟨p, β, hp, hcfg⟩
          cases hε : M₂.epsilon_transition q Z with
          | none => simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
          | some pβ =>
              rcases pβ with ⟨p', β'⟩
              simp [rightConf, DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
              rcases hp with ⟨rfl, rfl⟩
              refine ⟨⟨p', [], β' ++ γ⟩, ?_, ?_⟩
              · simpa [rightConf, List.map_append] using hcfg
              · refine ⟨p', β', ?_, rfl⟩
                simp [DPDA.toPDA, hε]
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases ht : M₂.transition q a Z with
            | none => simp [DPDA.toPDA, markedUnion, markTransitionRight, ht] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [rightConf, DPDA.toPDA, markedUnion, markTransitionRight, ht] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [rightConf, List.map_append] using hcfg
                · left
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, ht]
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases hε : M₂.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [rightConf, DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', a :: w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [rightConf, List.map_append] using hcfg
                · right
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, hε]

private lemma right_reaches_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₂.toPDA} {d : PDA.conf (markedUnion M₁ M₂).toPDA} :
    @PDA.Reaches (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
      (markedUnion M₁ M₂).toPDA (rightConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₂.toPDA, d = rightConf M₁ M₂ c' ∧ PDA.Reaches c c' := by
  intro h
  induction h with
  | refl => exact ⟨c, rfl, PDA.Reaches.refl _⟩
  | tail _ hstep ih =>
      rcases ih with ⟨c', rfl, hc'⟩
      rcases right_reaches₁_unmap M₁ M₂ hstep with ⟨c'', rfl, hstep'⟩
      exact ⟨c'', rfl, Relation.ReflTransGen.tail hc' hstep'⟩

private lemma left_reachesIn_empty_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    ∀ n {q : Q₁} {sf : MarkState Q₁ Q₂} {x : List (Bool ⊕ T)}
      {γ δ : List (MarkStack S₁ S₂)},
      @PDA.ReachesIn (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
        (markedUnion M₁ M₂).toPDA n
        ⟨MarkState.left q, x, γ⟩ ⟨sf, [], δ⟩ →
      ∃ w : List T, x = w.map Sum.inr
  | 0, q, sf, x, γ, δ, h => by
      have heq := PDA.reachesIn_zero h
      cases heq
      exact ⟨[], rfl⟩
  | n + 1, q, sf, x, γ, δ, h => by
      obtain ⟨c, hstep, hrest⟩ := PDA.reachesIn_iff_split_first.mpr h
      rcases c with ⟨s, y, stack⟩
      have hstep' := PDA.reachesIn_one.mp hstep
      rcases γ with _ | ⟨Z, γ'⟩
      · simp [PDA.step] at hstep'
      · cases Z with
        | bottom =>
            cases x <;> simp [PDA.step, DPDA.toPDA, markedUnion] at hstep'
        | right Z₂ =>
            cases x <;> simp [PDA.step, DPDA.toPDA, markedUnion] at hstep'
        | left Z₁ =>
            cases x with
            | nil =>
                unfold PDA.step at hstep'
                rcases hstep' with ⟨p, β, hp, hcfg⟩
                cases hε : M₁.epsilon_transition q Z₁ with
                | none => simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
                | some pβ =>
                    rcases pβ with ⟨p', β'⟩
                    simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
                    rcases hp with ⟨rfl, rfl⟩
                    cases hcfg
                    exact ⟨[], rfl⟩
            | cons a x' =>
                cases a with
                | inl b =>
                    unfold PDA.step at hstep'
                    rcases hstep' with hstep' | hstep'
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      simp [DPDA.toPDA, markedUnion] at hp
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases hε : M₁.epsilon_transition q Z₁ with
                      | none => simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          obtain ⟨w, hw⟩ :=
                            left_reachesIn_empty_payload M₁ M₂ n hrest
                          cases w <;> simp at hw
                | inr a =>
                    unfold PDA.step at hstep'
                    rcases hstep' with hstep' | hstep'
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases ht : M₁.transition q a Z₁ with
                      | none => simp [DPDA.toPDA, markedUnion, markTransitionLeft, ht] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, markedUnion, markTransitionLeft, ht] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          obtain ⟨w, hw⟩ :=
                            left_reachesIn_empty_payload M₁ M₂ n hrest
                          exact ⟨a :: w, by simp [hw]⟩
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases hε : M₁.epsilon_transition q Z₁ with
                      | none => simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, markedUnion, markEpsilonLeft, hε] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          exact left_reachesIn_empty_payload M₁ M₂ n hrest

private lemma left_reaches_empty_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {q : Q₁} {sf : MarkState Q₁ Q₂} {x : List (Bool ⊕ T)}
    {γ δ : List (MarkStack S₁ S₂)} :
    @PDA.Reaches (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
      (markedUnion M₁ M₂).toPDA
      ⟨MarkState.left q, x, γ⟩ ⟨sf, [], δ⟩ →
    ∃ w : List T, x = w.map Sum.inr := by
  intro h
  obtain ⟨n, hn⟩ := PDA.reaches_iff_reachesIn.mp h
  exact left_reachesIn_empty_payload M₁ M₂ n hn

private lemma right_reachesIn_empty_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    ∀ n {q : Q₂} {sf : MarkState Q₁ Q₂} {x : List (Bool ⊕ T)}
      {γ δ : List (MarkStack S₁ S₂)},
      @PDA.ReachesIn (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
        (markedUnion M₁ M₂).toPDA n
        ⟨MarkState.right q, x, γ⟩ ⟨sf, [], δ⟩ →
      ∃ w : List T, x = w.map Sum.inr
  | 0, q, sf, x, γ, δ, h => by
      have heq := PDA.reachesIn_zero h
      cases heq
      exact ⟨[], rfl⟩
  | n + 1, q, sf, x, γ, δ, h => by
      obtain ⟨c, hstep, hrest⟩ := PDA.reachesIn_iff_split_first.mpr h
      rcases c with ⟨s, y, stack⟩
      have hstep' := PDA.reachesIn_one.mp hstep
      rcases γ with _ | ⟨Z, γ'⟩
      · simp [PDA.step] at hstep'
      · cases Z with
        | bottom =>
            cases x <;> simp [PDA.step, DPDA.toPDA, markedUnion] at hstep'
        | left Z₁ =>
            cases x <;> simp [PDA.step, DPDA.toPDA, markedUnion] at hstep'
        | right Z₂ =>
            cases x with
            | nil =>
                unfold PDA.step at hstep'
                rcases hstep' with ⟨p, β, hp, hcfg⟩
                cases hε : M₂.epsilon_transition q Z₂ with
                | none => simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
                | some pβ =>
                    rcases pβ with ⟨p', β'⟩
                    simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
                    rcases hp with ⟨rfl, rfl⟩
                    cases hcfg
                    exact ⟨[], rfl⟩
            | cons a x' =>
                cases a with
                | inl b =>
                    unfold PDA.step at hstep'
                    rcases hstep' with hstep' | hstep'
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      simp [DPDA.toPDA, markedUnion] at hp
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases hε : M₂.epsilon_transition q Z₂ with
                      | none => simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          obtain ⟨w, hw⟩ :=
                            right_reachesIn_empty_payload M₁ M₂ n hrest
                          cases w <;> simp at hw
                | inr a =>
                    unfold PDA.step at hstep'
                    rcases hstep' with hstep' | hstep'
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases ht : M₂.transition q a Z₂ with
                      | none => simp [DPDA.toPDA, markedUnion, markTransitionRight, ht] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, markedUnion, markTransitionRight, ht] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          obtain ⟨w, hw⟩ :=
                            right_reachesIn_empty_payload M₁ M₂ n hrest
                          exact ⟨a :: w, by simp [hw]⟩
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases hε : M₂.epsilon_transition q Z₂ with
                      | none => simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, markedUnion, markEpsilonRight, hε] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          exact right_reachesIn_empty_payload M₁ M₂ n hrest

private lemma right_reaches_empty_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {q : Q₂} {sf : MarkState Q₁ Q₂} {x : List (Bool ⊕ T)}
    {γ δ : List (MarkStack S₁ S₂)} :
    @PDA.Reaches (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
      (markedUnion M₁ M₂).toPDA
      ⟨MarkState.right q, x, γ⟩ ⟨sf, [], δ⟩ →
    ∃ w : List T, x = w.map Sum.inr := by
  intro h
  obtain ⟨n, hn⟩ := PDA.reaches_iff_reachesIn.mp h
  exact right_reachesIn_empty_payload M₁ M₂ n hn

private lemma markedUnion_accepts_left (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {w : List T} :
    w ∈ M₁.acceptsByFinalState →
      Sum.inl false :: w.map Sum.inr ∈ (markedUnion M₁ M₂).acceptsByFinalState := by
  rintro ⟨q, hq, γ, hreach⟩
  refine ⟨MarkState.left q, ?_, γ.map MarkStack.left, ?_⟩
  · left
    exact ⟨q, hq, rfl⟩
  · let c0 : PDA.conf (markedUnion M₁ M₂).toPDA :=
      leftConf M₁ M₂ ⟨M₁.initial_state, w, [M₁.start_symbol]⟩
    have hfirst :
        @PDA.Reaches₁ (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
          (markedUnion M₁ M₂).toPDA
          ⟨(markedUnion M₁ M₂).initial_state, Sum.inl false :: w.map Sum.inr,
            [(markedUnion M₁ M₂).start_symbol]⟩ c0 := by
      unfold c0 PDA.Reaches₁ PDA.step
      left
      refine ⟨MarkState.left M₁.initial_state, [MarkStack.left M₁.start_symbol], ?_, ?_⟩
      · simp [DPDA.toPDA, markedUnion]
      · simp [leftConf]
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hfirst)
      (left_reaches_map M₁ M₂ hreach)

private lemma markedUnion_accepts_right (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {w : List T} :
    w ∈ M₂.acceptsByFinalState →
      Sum.inl true :: w.map Sum.inr ∈ (markedUnion M₁ M₂).acceptsByFinalState := by
  rintro ⟨q, hq, γ, hreach⟩
  refine ⟨MarkState.right q, ?_, γ.map MarkStack.right, ?_⟩
  · right
    exact ⟨q, hq, rfl⟩
  · let c0 : PDA.conf (markedUnion M₁ M₂).toPDA :=
      rightConf M₁ M₂ ⟨M₂.initial_state, w, [M₂.start_symbol]⟩
    have hfirst :
        @PDA.Reaches₁ (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
          (markedUnion M₁ M₂).toPDA
          ⟨(markedUnion M₁ M₂).initial_state, Sum.inl true :: w.map Sum.inr,
            [(markedUnion M₁ M₂).start_symbol]⟩ c0 := by
      unfold c0 PDA.Reaches₁ PDA.step
      left
      refine ⟨MarkState.right M₂.initial_state, [MarkStack.right M₂.start_symbol], ?_, ?_⟩
      · simp [DPDA.toPDA, markedUnion]
      · simp [rightConf]
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hfirst)
      (right_reaches_map M₁ M₂ hreach)

private lemma markedUnion_accepts_iff (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {x : List (Bool ⊕ T)} :
    x ∈ (markedUnion M₁ M₂).acceptsByFinalState ↔
      (∃ w, x = Sum.inl false :: w.map Sum.inr ∧ w ∈ M₁.acceptsByFinalState) ∨
      (∃ w, x = Sum.inl true :: w.map Sum.inr ∧ w ∈ M₂.acceptsByFinalState) := by
  constructor
  · rintro ⟨qf, hfinal, γ, hreach⟩
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨c, hstep, hrest⟩
    · cases heq
      simp [DPDA.toPDA, markedUnion] at hfinal
    · rcases c with ⟨s, y, stack⟩
      cases x with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at hstep
          simp [DPDA.toPDA, markedUnion] at hstep
      | cons a xs =>
          cases a with
          | inr a =>
              unfold PDA.Reaches₁ PDA.step at hstep
              rcases hstep with hstep | hstep
              · rcases hstep with ⟨p, β, hp, hcfg⟩
                simp [DPDA.toPDA, markedUnion] at hp
              · rcases hstep with ⟨p, β, hp, hcfg⟩
                simp [DPDA.toPDA, markedUnion] at hp
          | inl b =>
              cases b
              · unfold PDA.Reaches₁ PDA.step at hstep
                rcases hstep with hstep | hstep
                · rcases hstep with ⟨p, β, hp, hcfg⟩
                  simp [DPDA.toPDA, markedUnion] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  cases hcfg
                  obtain ⟨w, hxs⟩ := left_reaches_empty_payload M₁ M₂ hrest
                  have hrest' :
                      @PDA.Reaches (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
                        (markedUnion M₁ M₂).toPDA
                        (leftConf M₁ M₂ ⟨M₁.initial_state, w, [M₁.start_symbol]⟩)
                        ⟨qf, [], γ⟩ := by
                    simpa [leftConf, hxs] using hrest
                  rcases left_reaches_unmap M₁ M₂ hrest' with ⟨c', hc', hM⟩
                  rcases c' with ⟨q', w', γ'⟩
                  simp [leftConf] at hc'
                  rcases hc' with ⟨rfl, rfl, rfl⟩
                  have hq' : q' ∈ M₁.final_states := by
                    simpa [DPDA.toPDA, markedUnion] using hfinal
                  left
                  exact ⟨w, by simp [hxs], ⟨q', hq', γ', hM⟩⟩
                · rcases hstep with ⟨p, β, hp, hcfg⟩
                  simp [DPDA.toPDA, markedUnion] at hp
              · unfold PDA.Reaches₁ PDA.step at hstep
                rcases hstep with hstep | hstep
                · rcases hstep with ⟨p, β, hp, hcfg⟩
                  simp [DPDA.toPDA, markedUnion] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  cases hcfg
                  obtain ⟨w, hxs⟩ := right_reaches_empty_payload M₁ M₂ hrest
                  have hrest' :
                      @PDA.Reaches (MarkState Q₁ Q₂) (Bool ⊕ T) (MarkStack S₁ S₂) _ _ _
                        (markedUnion M₁ M₂).toPDA
                        (rightConf M₁ M₂ ⟨M₂.initial_state, w, [M₂.start_symbol]⟩)
                        ⟨qf, [], γ⟩ := by
                    simpa [rightConf, hxs] using hrest
                  rcases right_reaches_unmap M₁ M₂ hrest' with ⟨c', hc', hM⟩
                  rcases c' with ⟨q', w', γ'⟩
                  simp [rightConf] at hc'
                  rcases hc' with ⟨rfl, rfl, rfl⟩
                  have hq' : q' ∈ M₂.final_states := by
                    simpa [DPDA.toPDA, markedUnion] using hfinal
                  right
                  exact ⟨w, by simp [hxs], ⟨q', hq', γ', hM⟩⟩
                · rcases hstep with ⟨p, β, hp, hcfg⟩
                  simp [DPDA.toPDA, markedUnion] at hp
  · rintro (⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩)
    · exact markedUnion_accepts_left M₁ M₂ hw
    · exact markedUnion_accepts_right M₁ M₂ hw

private lemma mem_prod_singletons_iff {α β : Type} (h : α → List β)
    (x : List α) (u : List β) :
    u ∈ (x.map (fun a => ({h a} : Language β))).prod ↔ u = x.flatMap h := by
  induction x generalizing u with
  | nil =>
      exact Set.mem_singleton_iff
  | cons a x ih =>
      rw [List.map_cons, List.prod_cons, Language.mul_def, Set.mem_image2]
      constructor
      · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        rw [Set.mem_singleton_iff] at hu₁
        subst u₁
        rw [(ih u₂).mp hu₂]
        rfl
      · intro hu
        subst hu
        exact ⟨h a, Set.mem_singleton (h a), x.flatMap h, (ih _).mpr rfl, rfl⟩

private lemma mem_homomorphicImage_iff_flatMap {α β : Type} (L : Language α)
    (h : α → List β) (u : List β) :
    u ∈ L.homomorphicImage h ↔ ∃ x ∈ L, u = x.flatMap h := by
  constructor
  · rintro ⟨x, hx, hu⟩
    exact ⟨x, hx, (mem_prod_singletons_iff h x u).mp hu⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (mem_prod_singletons_iff h x (x.flatMap h)).mpr rfl⟩

private def eraseMarker : Bool ⊕ T → List T
  | Sum.inl _ => []
  | Sum.inr a => [a]

omit [Fintype T] in
private lemma flatMap_erase_payload (w : List T) :
    (w.map Sum.inr).flatMap eraseMarker = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [eraseMarker, ih]

private lemma markedUnion_hom_eq_union (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    ((markedUnion M₁ M₂).acceptsByFinalState).homomorphicImage eraseMarker =
      M₁.acceptsByFinalState + M₂.acceptsByFinalState := by
  ext w
  constructor
  · intro hw
    rw [mem_homomorphicImage_iff_flatMap] at hw
    rcases hw with ⟨x, hx, rfl⟩
    rw [markedUnion_accepts_iff M₁ M₂] at hx
    rcases hx with ⟨u, rfl, hu⟩ | ⟨u, rfl, hu⟩
    · simpa [eraseMarker, Language.add_def, flatMap_erase_payload] using Or.inl hu
    · simpa [eraseMarker, Language.add_def, flatMap_erase_payload] using Or.inr hu
  · intro hw
    rw [mem_homomorphicImage_iff_flatMap]
    rw [Language.add_def] at hw
    rcases hw with hw | hw
    · exact ⟨Sum.inl false :: w.map Sum.inr, markedUnion_accepts_left M₁ M₂ hw,
        by simp [eraseMarker, flatMap_erase_payload]⟩
    · exact ⟨Sum.inl true :: w.map Sum.inr, markedUnion_accepts_right M₁ M₂ hw,
        by simp [eraseMarker, flatMap_erase_payload]⟩

private def mergeMarker (marker : T) : Bool ⊕ T → List T
  | Sum.inl _ => [marker]
  | Sum.inr a => [a]

omit [Fintype T] in
private lemma mergeMarker_epsfree (marker : T) :
    IsEpsFreeHomomorphism (mergeMarker marker) := by
  intro a
  cases a <;> simp [mergeMarker]

omit [Fintype T] in
private lemma flatMap_merge_payload (marker : T) (w : List T) :
    (w.map Sum.inr).flatMap (mergeMarker marker) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [mergeMarker, ih]

private lemma markedUnion_merge_leftQuotient_eq_union
    (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) (marker : T) :
    [marker] \\ (((markedUnion M₁ M₂).acceptsByFinalState).homomorphicImage
      (mergeMarker marker)) =
      M₁.acceptsByFinalState + M₂.acceptsByFinalState := by
  ext w
  constructor
  · intro hw
    change marker :: w ∈ ((markedUnion M₁ M₂).acceptsByFinalState).homomorphicImage
      (mergeMarker marker) at hw
    rw [mem_homomorphicImage_iff_flatMap] at hw
    rcases hw with ⟨x, hx, hflat⟩
    rw [markedUnion_accepts_iff M₁ M₂] at hx
    rcases hx with ⟨u, rfl, hu⟩ | ⟨u, rfl, hu⟩
    · simp [mergeMarker, flatMap_merge_payload] at hflat
      subst w
      exact Or.inl hu
    · simp [mergeMarker, flatMap_merge_payload] at hflat
      subst w
      exact Or.inr hu
  · intro hw
    change marker :: w ∈ ((markedUnion M₁ M₂).acceptsByFinalState).homomorphicImage
      (mergeMarker marker)
    rw [mem_homomorphicImage_iff_flatMap]
    rw [Language.add_def] at hw
    rcases hw with hw | hw
    · exact ⟨Sum.inl false :: w.map Sum.inr, markedUnion_accepts_left M₁ M₂ hw,
        by simp [mergeMarker, flatMap_merge_payload]⟩
    · exact ⟨Sum.inl true :: w.map Sum.inr, markedUnion_accepts_right M₁ M₂ hw,
        by simp [mergeMarker, flatMap_merge_payload]⟩

end DPDA

public theorem DCF_leftQuotient_singleton {A : Type} [Fintype A]
    {L : Language A} (a : A) (hL : is_DCF L) :
    is_DCF ([a] \\ L) := by
  rcases hL with ⟨Q, S, hQ, hS, M, hM⟩
  have h := DPDA.is_DCF_leftQuotient_singleton M a
  rw [hM] at h
  exact h

public theorem DCF_leftQuotient_word {A : Type} [Fintype A]
    (x : List A) {L : Language A} (hL : is_DCF L) :
    is_DCF (x \\ L) := by
  induction x generalizing L with
  | nil =>
      simpa using hL
  | cons a x ih =>
      rw [Language.cons_leftQuotient]
      exact ih (DCF_leftQuotient_singleton a hL)

public theorem DCF_notClosedUnderHomomorphism :
    ¬ ClosedUnderHomomorphism is_DCF := by
  intro hhom
  apply DCF_notClosedUnderUnion
  intro L₁ L₂ hL₁ hL₂
  rcases hL₁ with ⟨Q₁, S₁, hQ₁, hS₁, M₁, hM₁⟩
  rcases hL₂ with ⟨Q₂, S₂, hQ₂, hS₂, M₂, hM₂⟩
  let M := DPDA.markedUnion M₁ M₂
  have hMDCF : is_DCF M.acceptsByFinalState := by
    exact ⟨_, _, inferInstance, inferInstance, M, rfl⟩
  have hImage :=
    hhom (α := Bool ⊕ Fin 3) (β := Fin 3) M.acceptsByFinalState DPDA.eraseMarker hMDCF
  simpa [M, DPDA.markedUnion_hom_eq_union, hM₁, hM₂] using hImage

public theorem DCF_notClosedUnderEpsFreeHomomorphism :
    ¬ ClosedUnderEpsFreeHomomorphism is_DCF := by
  intro heps
  apply DCF_notClosedUnderUnion_of_three
    (Sum.inl false : Bool ⊕ Fin 3) (Sum.inl true : Bool ⊕ Fin 3) (Sum.inr 0)
    (by decide) (by decide) (by decide)
  intro L₁ L₂ hL₁ hL₂
  rcases hL₁ with ⟨Q₁, S₁, hQ₁, hS₁, M₁, hM₁⟩
  rcases hL₂ with ⟨Q₂, S₂, hQ₂, hS₂, M₂, hM₂⟩
  let marker : Bool ⊕ Fin 3 := Sum.inl false
  let M := DPDA.markedUnion M₁ M₂
  have hMDCF : is_DCF M.acceptsByFinalState := by
    exact ⟨_, _, inferInstance, inferInstance, M, rfl⟩
  have hImage := heps M.acceptsByFinalState (DPDA.mergeMarker marker)
    (DPDA.mergeMarker_epsfree marker) hMDCF
  rcases hImage with ⟨Q, S, hQ, hS, MImage, hMImage⟩
  have hQuot : is_DCF ([marker] \\ (M.acceptsByFinalState.homomorphicImage
      (DPDA.mergeMarker marker))) := by
    have h := DPDA.is_DCF_leftQuotient_singleton MImage marker
    rw [hMImage] at h
    exact h
  dsimp [M] at hQuot
  change is_DCF ([marker] \\ (((DPDA.markedUnion M₁ M₂).acceptsByFinalState).homomorphicImage
      (DPDA.mergeMarker marker))) at hQuot
  rw [DPDA.markedUnion_merge_leftQuotient_eq_union M₁ M₂ marker, hM₁, hM₂] at hQuot
  exact hQuot

end DCFHomomorphism
