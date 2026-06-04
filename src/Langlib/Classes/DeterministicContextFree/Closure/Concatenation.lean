module

public import Langlib.Classes.DeterministicContextFree.Closure.Bijection
public import Langlib.Classes.DeterministicContextFree.Closure.Homomorphism
public import Langlib.Classes.DeterministicContextFree.Closure.IntersectionRegular
public import Langlib.Classes.DeterministicContextFree.Closure.Union
public import Langlib.Classes.DeterministicContextFree.Examples.AnBmCm
public import Langlib.Classes.Regular.Closure.Concatenation
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Classes.Regular.Closure.Star
public import Langlib.Classes.Regular.Closure.Union
public import Langlib.Classes.Regular.Examples.TopBot
public import Langlib.Classes.Regular.Inclusion.DeterministicContextFree
public import Langlib.Automata.FiniteState.Equivalence.Regular
public import Langlib.Utilities.ClosurePredicates

/-!
# Deterministic Context-Free Languages Are Not Closed Under Concatenation

The reduction uses the standard DCFL union witnesses.  If DCFLs were closed under
concatenation, then prefixing one branch by a fresh marker and concatenating with
the marker star would let an intersection and a left quotient recover the union
of the two witness languages.
-/

open PDA

namespace DCFConcatenation

private inductive OptionalState (Q₁ Q₂ : Type) where
  | start
  | left : Q₁ → OptionalState Q₁ Q₂
  | right : Q₂ → OptionalState Q₁ Q₂
deriving Fintype

private inductive OptionalStack (S₁ S₂ : Type) where
  | bottom
  | left : S₁ → OptionalStack S₁ S₂
  | right : S₂ → OptionalStack S₁ S₂
deriving Fintype

namespace DPDA

variable {T Q₁ Q₂ S₁ S₂ : Type}
variable [Fintype T] [Fintype Q₁] [Fintype Q₂] [Fintype S₁] [Fintype S₂]

private def optTransitionLeft (M : DPDA Q₁ T S₁)
    (q : Q₁) (a : T) (Z : S₁) :
    Option (OptionalState Q₁ Q₂ × List (OptionalStack S₁ S₂)) :=
  match M.transition q a Z with
  | none => none
  | some (q', γ) => some (OptionalState.left q', γ.map OptionalStack.left)

private def optTransitionRight (M : DPDA Q₂ T S₂)
    (q : Q₂) (a : T) (Z : S₂) :
    Option (OptionalState Q₁ Q₂ × List (OptionalStack S₁ S₂)) :=
  match M.transition q a Z with
  | none => none
  | some (q', γ) => some (OptionalState.right q', γ.map OptionalStack.right)

private def optEpsilonLeft (M : DPDA Q₁ T S₁) (q : Q₁) (Z : S₁) :
    Option (OptionalState Q₁ Q₂ × List (OptionalStack S₁ S₂)) :=
  match M.epsilon_transition q Z with
  | none => none
  | some (q', γ) => some (OptionalState.left q', γ.map OptionalStack.left)

private def optEpsilonRight (M : DPDA Q₂ T S₂) (q : Q₂) (Z : S₂) :
    Option (OptionalState Q₁ Q₂ × List (OptionalStack S₁ S₂)) :=
  match M.epsilon_transition q Z with
  | none => none
  | some (q', γ) => some (OptionalState.right q', γ.map OptionalStack.right)

private def optionalMarkedUnion (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    DPDA (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) where
  initial_state := OptionalState.start
  start_symbol := OptionalStack.bottom
  final_states :=
    {q | q = OptionalState.start ∧ M₂.initial_state ∈ M₂.final_states ∨
      (∃ q₁ ∈ M₁.final_states, q = OptionalState.left q₁) ∨
      (∃ q₂ ∈ M₂.final_states, q = OptionalState.right q₂)}
  transition q a Z :=
    match q, a, Z with
    | OptionalState.start, Sum.inl false, OptionalStack.bottom =>
        some (OptionalState.left M₁.initial_state, [OptionalStack.left M₁.start_symbol])
    | OptionalState.start, Sum.inr a, OptionalStack.bottom =>
        optTransitionRight (Q₁ := Q₁) (S₁ := S₁) M₂ M₂.initial_state a M₂.start_symbol
    | OptionalState.left q₁, Sum.inr a, OptionalStack.left Z₁ =>
        optTransitionLeft (Q₂ := Q₂) (S₂ := S₂) M₁ q₁ a Z₁
    | OptionalState.right q₂, Sum.inr a, OptionalStack.right Z₂ =>
        optTransitionRight (Q₁ := Q₁) (S₁ := S₁) M₂ q₂ a Z₂
    | _, _, _ => none
  epsilon_transition q Z :=
    match q, Z with
    | OptionalState.left q₁, OptionalStack.left Z₁ =>
        optEpsilonLeft (Q₂ := Q₂) (S₂ := S₂) M₁ q₁ Z₁
    | OptionalState.right q₂, OptionalStack.right Z₂ =>
        optEpsilonRight (Q₁ := Q₁) (S₁ := S₁) M₂ q₂ Z₂
    | _, _ => none
  no_mixed := by
    intro q Z hε a
    cases q <;> cases Z <;> cases a <;>
      simp [optEpsilonLeft, optEpsilonRight, optTransitionLeft, optTransitionRight] at hε ⊢
    · rename_i q₁ Z₁ t
      split at hε
      · exact False.elim (hε rfl)
      · rename_i q' γ hε₁
        have hnone := M₁.no_mixed q₁ Z₁ (by simp [hε₁]) t
        simpa [optTransitionLeft, hnone]
    · rename_i q₂ Z₂ t
      split at hε
      · exact False.elim (hε rfl)
      · rename_i q' γ hε₂
        have hnone := M₂.no_mixed q₂ Z₂ (by simp [hε₂]) t
        simpa [optTransitionRight, hnone]

private def leftConf (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    PDA.conf M₁.toPDA → PDA.conf (optionalMarkedUnion M₁ M₂).toPDA
  | ⟨q, w, γ⟩ => ⟨OptionalState.left q, w.map Sum.inr, γ.map OptionalStack.left⟩

private def rightConf (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    PDA.conf M₂.toPDA → PDA.conf (optionalMarkedUnion M₁ M₂).toPDA
  | ⟨q, w, γ⟩ => ⟨OptionalState.right q, w.map Sum.inr, γ.map OptionalStack.right⟩

private lemma left_reaches₁_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₁.toPDA} :
    PDA.Reaches₁ c c' →
      @PDA.Reaches₁ (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnion M₁ M₂).toPDA (leftConf M₁ M₂ c) (leftConf M₁ M₂ c') := by
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
          refine ⟨OptionalState.left p, β.map OptionalStack.left, ?_, ?_⟩
          · cases hε : M₁.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [DPDA.toPDA, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε]
          · simpa [leftConf, List.map_append] using congrArg (leftConf M₁ M₂) hcfg
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            left
            refine ⟨OptionalState.left p, β.map OptionalStack.left, ?_, ?_⟩
            · cases ht : M₁.transition q a Z with
              | none => simp [DPDA.toPDA, ht] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, ht] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, optionalMarkedUnion, optTransitionLeft, ht]
            · simpa [leftConf, List.map_append] using congrArg (leftConf M₁ M₂) hcfg
          · rcases h with ⟨p, β, hp, hcfg⟩
            right
            refine ⟨OptionalState.left p, β.map OptionalStack.left, ?_, ?_⟩
            · cases hε : M₁.epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε]
            · simpa [leftConf, List.map_append] using congrArg (leftConf M₁ M₂) hcfg

private lemma left_reaches_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₁.toPDA} :
    PDA.Reaches c c' →
      @PDA.Reaches (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnion M₁ M₂).toPDA (leftConf M₁ M₂ c) (leftConf M₁ M₂ c') := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (left_reaches₁_map M₁ M₂ hstep)

private lemma right_reaches₁_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₂.toPDA} :
    PDA.Reaches₁ c c' →
      @PDA.Reaches₁ (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnion M₁ M₂).toPDA (rightConf M₁ M₂ c) (rightConf M₁ M₂ c') := by
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
          refine ⟨OptionalState.right p, β.map OptionalStack.right, ?_, ?_⟩
          · cases hε : M₂.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [DPDA.toPDA, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε]
          · simpa [rightConf, List.map_append] using congrArg (rightConf M₁ M₂) hcfg
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            left
            refine ⟨OptionalState.right p, β.map OptionalStack.right, ?_, ?_⟩
            · cases ht : M₂.transition q a Z with
              | none => simp [DPDA.toPDA, ht] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, ht] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, optionalMarkedUnion, optTransitionRight, ht]
            · simpa [rightConf, List.map_append] using congrArg (rightConf M₁ M₂) hcfg
          · rcases h with ⟨p, β, hp, hcfg⟩
            right
            refine ⟨OptionalState.right p, β.map OptionalStack.right, ?_, ?_⟩
            · cases hε : M₂.epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε]
            · simpa [rightConf, List.map_append] using congrArg (rightConf M₁ M₂) hcfg

private lemma right_reaches_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₂.toPDA} :
    PDA.Reaches c c' →
      @PDA.Reaches (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnion M₁ M₂).toPDA (rightConf M₁ M₂ c) (rightConf M₁ M₂ c') := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (right_reaches₁_map M₁ M₂ hstep)

private lemma left_reaches₁_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₁.toPDA} {d : PDA.conf (optionalMarkedUnion M₁ M₂).toPDA} :
    @PDA.Reaches₁ (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnion M₁ M₂).toPDA (leftConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₁.toPDA, d = leftConf M₁ M₂ c' ∧ PDA.Reaches₁ c c' := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases d with ⟨qd, wd, γd⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
          (optionalMarkedUnion M₁ M₂).toPDA 1 (leftConf M₁ M₂ ⟨q, w, []⟩) ⟨qd, wd, γd⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with ⟨p, β, hp, hcfg⟩
          cases hε : M₁.epsilon_transition q Z with
          | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
          | some pβ =>
              rcases pβ with ⟨p', β'⟩
              simp [leftConf, DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
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
            | none => simp [DPDA.toPDA, optionalMarkedUnion, optTransitionLeft, ht] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [leftConf, DPDA.toPDA, optionalMarkedUnion, optTransitionLeft, ht] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [leftConf, List.map_append] using hcfg
                · left
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, ht]
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases hε : M₁.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [leftConf, DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', a :: w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [leftConf, List.map_append] using hcfg
                · right
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, hε]

private lemma left_reaches_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₁.toPDA} {d : PDA.conf (optionalMarkedUnion M₁ M₂).toPDA} :
    @PDA.Reaches (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnion M₁ M₂).toPDA (leftConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₁.toPDA, d = leftConf M₁ M₂ c' ∧ PDA.Reaches c c' := by
  intro h
  induction h with
  | refl => exact ⟨c, rfl, PDA.Reaches.refl _⟩
  | tail _ hstep ih =>
      rcases ih with ⟨c', rfl, hc'⟩
      rcases left_reaches₁_unmap M₁ M₂ hstep with ⟨c'', rfl, hstep'⟩
      exact ⟨c'', rfl, Relation.ReflTransGen.tail hc' hstep'⟩

private lemma right_reaches₁_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₂.toPDA} {d : PDA.conf (optionalMarkedUnion M₁ M₂).toPDA} :
    @PDA.Reaches₁ (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnion M₁ M₂).toPDA (rightConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₂.toPDA, d = rightConf M₁ M₂ c' ∧ PDA.Reaches₁ c c' := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases d with ⟨qd, wd, γd⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
          (optionalMarkedUnion M₁ M₂).toPDA 1 (rightConf M₁ M₂ ⟨q, w, []⟩) ⟨qd, wd, γd⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with ⟨p, β, hp, hcfg⟩
          cases hε : M₂.epsilon_transition q Z with
          | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
          | some pβ =>
              rcases pβ with ⟨p', β'⟩
              simp [rightConf, DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
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
            | none => simp [DPDA.toPDA, optionalMarkedUnion, optTransitionRight, ht] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [rightConf, DPDA.toPDA, optionalMarkedUnion, optTransitionRight, ht] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [rightConf, List.map_append] using hcfg
                · left
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, ht]
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases hε : M₂.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [rightConf, DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', a :: w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [rightConf, List.map_append] using hcfg
                · right
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, hε]

private lemma right_reaches_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₂.toPDA} {d : PDA.conf (optionalMarkedUnion M₁ M₂).toPDA} :
    @PDA.Reaches (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnion M₁ M₂).toPDA (rightConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₂.toPDA, d = rightConf M₁ M₂ c' ∧ PDA.Reaches c c' := by
  intro h
  induction h with
  | refl => exact ⟨c, rfl, PDA.Reaches.refl _⟩
  | tail _ hstep ih =>
      rcases ih with ⟨c', rfl, hc'⟩
      rcases right_reaches₁_unmap M₁ M₂ hstep with ⟨c'', rfl, hstep'⟩
      exact ⟨c'', rfl, Relation.ReflTransGen.tail hc' hstep'⟩

private lemma left_reachesIn_empty_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    ∀ n {q : Q₁} {sf : OptionalState Q₁ Q₂} {x : List (Bool ⊕ T)}
      {γ δ : List (OptionalStack S₁ S₂)},
      @PDA.ReachesIn (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnion M₁ M₂).toPDA n
        ⟨OptionalState.left q, x, γ⟩ ⟨sf, [], δ⟩ →
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
            cases x <;> simp [PDA.step, DPDA.toPDA, optionalMarkedUnion] at hstep'
        | right Z₂ =>
            cases x <;> simp [PDA.step, DPDA.toPDA, optionalMarkedUnion] at hstep'
        | left Z₁ =>
            cases x with
            | nil =>
                unfold PDA.step at hstep'
                rcases hstep' with ⟨p, β, hp, hcfg⟩
                cases hε : M₁.epsilon_transition q Z₁ with
                | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
                | some pβ =>
                    rcases pβ with ⟨p', β'⟩
                    simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
                    rcases hp with ⟨rfl, rfl⟩
                    cases hcfg
                    exact ⟨[], rfl⟩
            | cons a x' =>
                cases a with
                | inl b =>
                    unfold PDA.step at hstep'
                    rcases hstep' with hstep' | hstep'
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      simp [DPDA.toPDA, optionalMarkedUnion] at hp
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases hε : M₁.epsilon_transition q Z₁ with
                      | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
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
                      | none => simp [DPDA.toPDA, optionalMarkedUnion, optTransitionLeft, ht] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, optionalMarkedUnion, optTransitionLeft, ht] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          obtain ⟨w, hw⟩ :=
                            left_reachesIn_empty_payload M₁ M₂ n hrest
                          exact ⟨a :: w, by simp [hw]⟩
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases hε : M₁.epsilon_transition q Z₁ with
                      | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonLeft, hε] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          exact left_reachesIn_empty_payload M₁ M₂ n hrest

private lemma left_reaches_empty_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {q : Q₁} {sf : OptionalState Q₁ Q₂} {x : List (Bool ⊕ T)}
    {γ δ : List (OptionalStack S₁ S₂)} :
    @PDA.Reaches (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnion M₁ M₂).toPDA
      ⟨OptionalState.left q, x, γ⟩ ⟨sf, [], δ⟩ →
    ∃ w : List T, x = w.map Sum.inr := by
  intro h
  obtain ⟨n, hn⟩ := PDA.reaches_iff_reachesIn.mp h
  exact left_reachesIn_empty_payload M₁ M₂ n hn

private lemma right_reachesIn_empty_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    ∀ n {q : Q₂} {sf : OptionalState Q₁ Q₂} {x : List (Bool ⊕ T)}
      {γ δ : List (OptionalStack S₁ S₂)},
      @PDA.ReachesIn (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnion M₁ M₂).toPDA n
        ⟨OptionalState.right q, x, γ⟩ ⟨sf, [], δ⟩ →
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
            cases x <;> simp [PDA.step, DPDA.toPDA, optionalMarkedUnion] at hstep'
        | left Z₁ =>
            cases x <;> simp [PDA.step, DPDA.toPDA, optionalMarkedUnion] at hstep'
        | right Z₂ =>
            cases x with
            | nil =>
                unfold PDA.step at hstep'
                rcases hstep' with ⟨p, β, hp, hcfg⟩
                cases hε : M₂.epsilon_transition q Z₂ with
                | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
                | some pβ =>
                    rcases pβ with ⟨p', β'⟩
                    simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
                    rcases hp with ⟨rfl, rfl⟩
                    cases hcfg
                    exact ⟨[], rfl⟩
            | cons a x' =>
                cases a with
                | inl b =>
                    unfold PDA.step at hstep'
                    rcases hstep' with hstep' | hstep'
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      simp [DPDA.toPDA, optionalMarkedUnion] at hp
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases hε : M₂.epsilon_transition q Z₂ with
                      | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
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
                      | none => simp [DPDA.toPDA, optionalMarkedUnion, optTransitionRight, ht] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, optionalMarkedUnion, optTransitionRight, ht] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          obtain ⟨w, hw⟩ :=
                            right_reachesIn_empty_payload M₁ M₂ n hrest
                          exact ⟨a :: w, by simp [hw]⟩
                    · rcases hstep' with ⟨p, β, hp, hcfg⟩
                      cases hε : M₂.epsilon_transition q Z₂ with
                      | none => simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
                      | some pβ =>
                          rcases pβ with ⟨p', β'⟩
                          simp [DPDA.toPDA, optionalMarkedUnion, optEpsilonRight, hε] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hcfg
                          exact right_reachesIn_empty_payload M₁ M₂ n hrest

private lemma right_reaches_empty_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {q : Q₂} {sf : OptionalState Q₁ Q₂} {x : List (Bool ⊕ T)}
    {γ δ : List (OptionalStack S₁ S₂)} :
    @PDA.Reaches (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnion M₁ M₂).toPDA
      ⟨OptionalState.right q, x, γ⟩ ⟨sf, [], δ⟩ →
    ∃ w : List T, x = w.map Sum.inr := by
  intro h
  obtain ⟨n, hn⟩ := PDA.reaches_iff_reachesIn.mp h
  exact right_reachesIn_empty_payload M₁ M₂ n hn

private lemma optional_accepts_left (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {w : List T} :
    w ∈ M₁.acceptsByFinalState →
      Sum.inl false :: w.map Sum.inr ∈ (optionalMarkedUnion M₁ M₂).acceptsByFinalState := by
  rintro ⟨q, hq, γ, hreach⟩
  refine ⟨OptionalState.left q, ?_, γ.map OptionalStack.left, ?_⟩
  · right
    left
    exact ⟨q, hq, rfl⟩
  · let c0 : PDA.conf (optionalMarkedUnion M₁ M₂).toPDA :=
      leftConf M₁ M₂ ⟨M₁.initial_state, w, [M₁.start_symbol]⟩
    have hfirst :
        @PDA.Reaches₁ (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
          (optionalMarkedUnion M₁ M₂).toPDA
          ⟨(optionalMarkedUnion M₁ M₂).initial_state, Sum.inl false :: w.map Sum.inr,
            [(optionalMarkedUnion M₁ M₂).start_symbol]⟩ c0 := by
      unfold c0 PDA.Reaches₁ PDA.step
      left
      refine ⟨OptionalState.left M₁.initial_state, [OptionalStack.left M₁.start_symbol], ?_, ?_⟩
      · simp [DPDA.toPDA, optionalMarkedUnion]
      · simp [leftConf]
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hfirst)
      (left_reaches_map M₁ M₂ hreach)

private lemma optional_accepts_right (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    (hnoε : M₂.epsilon_transition M₂.initial_state M₂.start_symbol = none)
    {w : List T} :
    w ∈ M₂.acceptsByFinalState →
      w.map Sum.inr ∈ (optionalMarkedUnion M₁ M₂).acceptsByFinalState := by
  rintro ⟨q, hq, γ, hreach⟩
  cases w with
  | nil =>
      rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨c, hstep, _⟩
      · cases heq
        exact ⟨OptionalState.start, by
          left
          exact ⟨rfl, hq⟩, [OptionalStack.bottom], Relation.ReflTransGen.refl⟩
      · unfold PDA.Reaches₁ PDA.step at hstep
        simp [DPDA.toPDA, hnoε] at hstep
  | cons a w =>
      rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨c, hstep, hrest⟩
      · cases heq
      · rcases c with ⟨p, input, stack⟩
        unfold PDA.Reaches₁ PDA.step at hstep
        simp [DPDA.toPDA, hnoε] at hstep
        rcases hstep with ⟨hp, hinput⟩
        subst input
        cases ht : M₂.transition M₂.initial_state a M₂.start_symbol with
        | none => simp [DPDA.toPDA, ht] at hp
        | some pβ =>
            rcases pβ with ⟨p0, β0⟩
            simp [DPDA.toPDA, ht] at hp
            rcases hp with ⟨rfl, rfl⟩
            refine ⟨OptionalState.right q, ?_, γ.map OptionalStack.right, ?_⟩
            · right
              right
              exact ⟨q, hq, rfl⟩
            · have hfirst :
                  @PDA.Reaches₁ (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
                    (optionalMarkedUnion M₁ M₂).toPDA
                    ⟨(optionalMarkedUnion M₁ M₂).initial_state,
                      Sum.inr a :: w.map Sum.inr,
                      [(optionalMarkedUnion M₁ M₂).start_symbol]⟩
                    (rightConf M₁ M₂ ⟨p, w, stack⟩) := by
                unfold PDA.Reaches₁ PDA.step
                left
                refine ⟨OptionalState.right p, stack.map OptionalStack.right, ?_, ?_⟩
                · simp [DPDA.toPDA, optionalMarkedUnion, optTransitionRight, ht]
                · simp [rightConf]
              exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hfirst)
                (right_reaches_map M₁ M₂ hrest)

private theorem optional_accepts_iff (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    (hnoε : M₂.epsilon_transition M₂.initial_state M₂.start_symbol = none)
    {x : List (Bool ⊕ T)} :
    x ∈ (optionalMarkedUnion M₁ M₂).acceptsByFinalState ↔
      (∃ w, x = Sum.inl false :: w.map Sum.inr ∧ w ∈ M₁.acceptsByFinalState) ∨
      (∃ w, x = w.map Sum.inr ∧ w ∈ M₂.acceptsByFinalState) := by
  constructor
  · rintro ⟨qf, hfinal, γ, hreach⟩
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨c, hstep, hrest⟩
    · cases heq
      rcases hfinal with ⟨_, hinit⟩ | ⟨⟨_, _, hbad⟩ | ⟨_, _, hbad⟩⟩
      · right
        exact ⟨[], rfl, ⟨M₂.initial_state, hinit, [M₂.start_symbol], Relation.ReflTransGen.refl⟩⟩
      · cases hbad
      · cases hbad
    · rcases c with ⟨s, y, stack⟩
      cases x with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at hstep
          simp [DPDA.toPDA, optionalMarkedUnion] at hstep
      | cons a xs =>
          cases a with
          | inl b =>
              cases b
              · unfold PDA.Reaches₁ PDA.step at hstep
                rcases hstep with hstep | hstep
                · rcases hstep with ⟨p, β, hp, hcfg⟩
                  simp [DPDA.toPDA, optionalMarkedUnion] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  cases hcfg
                  obtain ⟨w, hxs⟩ := left_reaches_empty_payload M₁ M₂ hrest
                  have hrest' :
                      @PDA.Reaches (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
                        (optionalMarkedUnion M₁ M₂).toPDA
                        (leftConf M₁ M₂ ⟨M₁.initial_state, w, [M₁.start_symbol]⟩)
                        ⟨qf, [], γ⟩ := by
                    simpa [leftConf, hxs] using hrest
                  rcases left_reaches_unmap M₁ M₂ hrest' with ⟨c', hc', hM⟩
                  rcases c' with ⟨q', w', γ'⟩
                  simp [leftConf] at hc'
                  rcases hc' with ⟨rfl, rfl, rfl⟩
                  have hq' : q' ∈ M₁.final_states := by
                    rcases hfinal with hstart | hfinal
                    · rcases hstart with ⟨hstart, _⟩
                      simp [optionalMarkedUnion] at hstart
                    · rcases hfinal with hleft | hright
                      · rcases hleft with ⟨q1, hq1, hqeq⟩
                        simp [optionalMarkedUnion] at hqeq
                        rcases hqeq with rfl
                        exact hq1
                      · rcases hright with ⟨q2, _, hqeq⟩
                        simp [optionalMarkedUnion] at hqeq
                  left
                  exact ⟨w, by simp [hxs], ⟨q', hq', γ', hM⟩⟩
                · rcases hstep with ⟨p, β, hp, hcfg⟩
                  simp [DPDA.toPDA, optionalMarkedUnion] at hp
              · unfold PDA.Reaches₁ PDA.step at hstep
                rcases hstep with hstep | hstep
                · rcases hstep with ⟨p, β, hp, hcfg⟩
                  simp [DPDA.toPDA, optionalMarkedUnion] at hp
                · rcases hstep with ⟨p, β, hp, hcfg⟩
                  simp [DPDA.toPDA, optionalMarkedUnion] at hp
          | inr t =>
              unfold PDA.Reaches₁ PDA.step at hstep
              rcases hstep with hstep | hstep
              · rcases hstep with ⟨p, β, hp, hcfg⟩
                cases ht : M₂.transition M₂.initial_state t M₂.start_symbol with
                | none => simp [DPDA.toPDA, optionalMarkedUnion, optTransitionRight, ht] at hp
                | some pβ =>
                    rcases pβ with ⟨p0, β0⟩
                    simp [DPDA.toPDA, optionalMarkedUnion, optTransitionRight, ht] at hp
                    rcases hp with ⟨rfl, rfl⟩
                    cases hcfg
                    obtain ⟨w, hxs⟩ := right_reaches_empty_payload M₁ M₂ hrest
                    have hrest' :
                        @PDA.Reaches (OptionalState Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
                          (optionalMarkedUnion M₁ M₂).toPDA
                          (rightConf M₁ M₂ ⟨p0, w, β0⟩)
                          ⟨qf, [], γ⟩ := by
                      simpa [rightConf, hxs] using hrest
                    rcases right_reaches_unmap M₁ M₂ hrest' with ⟨c', hc', hM⟩
                    rcases c' with ⟨q', w', γ'⟩
                    simp [rightConf] at hc'
                    rcases hc' with ⟨rfl, rfl, rfl⟩
                    have hq' : q' ∈ M₂.final_states := by
                      rcases hfinal with hstart | hfinal
                      · rcases hstart with ⟨hstart, _⟩
                        simp [optionalMarkedUnion] at hstart
                      · rcases hfinal with hleft | hright
                        · rcases hleft with ⟨q1, _, hqeq⟩
                          simp [optionalMarkedUnion] at hqeq
                        · rcases hright with ⟨q2, hq2, hqeq⟩
                          simp [optionalMarkedUnion] at hqeq
                          rcases hqeq with rfl
                          exact hq2
                    right
                    refine ⟨t :: w, ?_, ?_⟩
                    · simp [hxs]
                    · refine ⟨q', hq', γ', ?_⟩
                      exact Relation.ReflTransGen.tail
                        (Relation.ReflTransGen.refl : PDA.Reaches
                          (⟨M₂.initial_state, t :: w, [M₂.start_symbol]⟩ : PDA.conf M₂.toPDA)
                          ⟨M₂.initial_state, t :: w, [M₂.start_symbol]⟩)
                        (by
                          unfold PDA.Reaches₁ PDA.step
                          left
                          refine ⟨p0, β0, ?_, by simp⟩
                          simp [DPDA.toPDA, ht])
                        |>.trans hM
              · rcases hstep with ⟨p, β, hp, hcfg⟩
                simp [DPDA.toPDA, optionalMarkedUnion] at hp
  · rintro (⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩)
    · exact optional_accepts_left M₁ M₂ hw
    · exact optional_accepts_right M₁ M₂ hnoε hw

public theorem is_DCF_optional_marked_union_no_initial_epsilon
    (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    (hnoε : M₂.epsilon_transition M₂.initial_state M₂.start_symbol = none) :
    is_DCF
      ({x | (∃ w, x = Sum.inl false :: w.map Sum.inr ∧ w ∈ M₁.acceptsByFinalState) ∨
        (∃ w, x = w.map Sum.inr ∧ w ∈ M₂.acceptsByFinalState)} :
        Language (Bool ⊕ T)) := by
  refine ⟨OptionalState Q₁ Q₂, OptionalStack S₁ S₂, inferInstance, inferInstance,
    optionalMarkedUnion M₁ M₂, ?_⟩
  ext x
  exact optional_accepts_iff M₁ M₂ hnoε

end DPDA

private inductive OptionalQuotState (T Q₁ Q₂ : Type) where
  | start
  | left : Q₁ → OptionalQuotState T Q₁ Q₂
  | right : T → DCFHomomorphism.DPDA.LeftQuotientState Q₂ → OptionalQuotState T Q₁ Q₂
deriving DecidableEq

private def optionalQuotStateEquiv (T Q₁ Q₂ : Type) :
    OptionalQuotState T Q₁ Q₂ ≃
      Unit ⊕ Q₁ ⊕ T × DCFHomomorphism.DPDA.LeftQuotientState Q₂ where
  toFun
    | OptionalQuotState.start => Sum.inl ()
    | OptionalQuotState.left q => Sum.inr (Sum.inl q)
    | OptionalQuotState.right a q => Sum.inr (Sum.inr (a, q))
  invFun
    | Sum.inl _ => OptionalQuotState.start
    | Sum.inr (Sum.inl q) => OptionalQuotState.left q
    | Sum.inr (Sum.inr (a, q)) => OptionalQuotState.right a q
  left_inv := by
    intro q
    cases q <;> rfl
  right_inv := by
    intro q
    rcases q with (_ | (_ | ⟨a, q⟩)) <;> rfl

private instance optionalQuotStateFintype {T Q₁ Q₂ : Type}
    [Fintype T] [Fintype Q₁] [Fintype Q₂] :
    Fintype (OptionalQuotState T Q₁ Q₂) :=
  Fintype.ofEquiv _ (optionalQuotStateEquiv T Q₁ Q₂).symm

namespace DPDA

variable {T Q₁ Q₂ S₁ S₂ : Type}
variable [Fintype T] [Fintype Q₁] [Fintype Q₂] [Fintype S₁] [Fintype S₂]

private abbrev quotientM (M : DPDA Q₂ T S₂) (a : T) :=
  DCFHomomorphism.DPDA.leftQuotientSingleton M a

private def optQuotTransitionLeft (M : DPDA Q₁ T S₁)
    (q : Q₁) (a : T) (Z : S₁) :
    Option (OptionalQuotState T Q₁ Q₂ × List (OptionalStack S₁ S₂)) :=
  match M.transition q a Z with
  | none => none
  | some (q', γ) => some (OptionalQuotState.left q', γ.map OptionalStack.left)

private def optQuotTransitionRight (M : DPDA Q₂ T S₂)
    (mark : T) (q : DCFHomomorphism.DPDA.LeftQuotientState Q₂) (a : T) (Z : S₂) :
    Option (OptionalQuotState T Q₁ Q₂ × List (OptionalStack S₁ S₂)) :=
  match (quotientM M mark).transition q a Z with
  | none => none
  | some (q', γ) => some (OptionalQuotState.right mark q', γ.map OptionalStack.right)

private def optQuotEpsilonLeft (M : DPDA Q₁ T S₁) (q : Q₁) (Z : S₁) :
    Option (OptionalQuotState T Q₁ Q₂ × List (OptionalStack S₁ S₂)) :=
  match M.epsilon_transition q Z with
  | none => none
  | some (q', γ) => some (OptionalQuotState.left q', γ.map OptionalStack.left)

private def optQuotEpsilonRight (M : DPDA Q₂ T S₂)
    (mark : T) (q : DCFHomomorphism.DPDA.LeftQuotientState Q₂) (Z : S₂) :
    Option (OptionalQuotState T Q₁ Q₂ × List (OptionalStack S₁ S₂)) :=
  match (quotientM M mark).epsilon_transition q Z with
  | none => none
  | some (q', γ) => some (OptionalQuotState.right mark q', γ.map OptionalStack.right)

private def optionalMarkedUnionQuot (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    DPDA (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) where
  initial_state := OptionalQuotState.start
  start_symbol := OptionalStack.bottom
  final_states :=
    {q | q = OptionalQuotState.start ∧ ([] : List T) ∈ M₂.acceptsByFinalState ∨
      (∃ q₁ ∈ M₁.final_states, q = OptionalQuotState.left q₁) ∨
      (∃ mark q₂, q₂ ∈ (quotientM M₂ mark).final_states ∧
        q = OptionalQuotState.right mark q₂)}
  transition q a Z :=
    match q, a, Z with
    | OptionalQuotState.start, Sum.inl false, OptionalStack.bottom =>
        some (OptionalQuotState.left M₁.initial_state, [OptionalStack.left M₁.start_symbol])
    | OptionalQuotState.start, Sum.inr a, OptionalStack.bottom =>
        some (OptionalQuotState.right a (quotientM M₂ a).initial_state,
          [OptionalStack.right (quotientM M₂ a).start_symbol])
    | OptionalQuotState.left q₁, Sum.inr a, OptionalStack.left Z₁ =>
        optQuotTransitionLeft (Q₂ := Q₂) (S₂ := S₂) M₁ q₁ a Z₁
    | OptionalQuotState.right mark q₂, Sum.inr a, OptionalStack.right Z₂ =>
        optQuotTransitionRight (Q₁ := Q₁) (S₁ := S₁) M₂ mark q₂ a Z₂
    | _, _, _ => none
  epsilon_transition q Z :=
    match q, Z with
    | OptionalQuotState.left q₁, OptionalStack.left Z₁ =>
        optQuotEpsilonLeft (Q₂ := Q₂) (S₂ := S₂) M₁ q₁ Z₁
    | OptionalQuotState.right mark q₂, OptionalStack.right Z₂ =>
        optQuotEpsilonRight (Q₁ := Q₁) (S₁ := S₁) M₂ mark q₂ Z₂
    | _, _ => none
  no_mixed := by
    intro q Z hε a
    cases q <;> cases Z <;> cases a <;>
      simp [optQuotEpsilonLeft, optQuotEpsilonRight, optQuotTransitionLeft,
        optQuotTransitionRight] at hε ⊢
    · rename_i q₁ Z₁ t
      split at hε
      · exact False.elim (hε rfl)
      · rename_i q' γ hε₁
        have hnone := M₁.no_mixed q₁ Z₁ (by simp [hε₁]) t
        simpa [optQuotTransitionLeft, hnone]
    · rename_i mark q₂ Z₂ t
      split at hε
      · exact False.elim (hε rfl)
      · rename_i q' γ hε₂
        have hnone := (quotientM M₂ mark).no_mixed q₂ Z₂ (by simp [hε₂]) t
        simpa [optQuotTransitionRight, hnone]

private def quotLeftConf (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    PDA.conf M₁.toPDA → PDA.conf (optionalMarkedUnionQuot M₁ M₂).toPDA
  | ⟨q, w, γ⟩ => ⟨OptionalQuotState.left q, w.map Sum.inr, γ.map OptionalStack.left⟩

private def quotRightConf (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) (mark : T) :
    PDA.conf (quotientM M₂ mark).toPDA → PDA.conf (optionalMarkedUnionQuot M₁ M₂).toPDA
  | ⟨q, w, γ⟩ => ⟨OptionalQuotState.right mark q, w.map Sum.inr, γ.map OptionalStack.right⟩

private lemma quot_left_reaches₁_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₁.toPDA} :
    PDA.Reaches₁ c c' →
      @PDA.Reaches₁ (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnionQuot M₁ M₂).toPDA (quotLeftConf M₁ M₂ c) (quotLeftConf M₁ M₂ c') := by
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
          refine ⟨OptionalQuotState.left p, β.map OptionalStack.left, ?_, ?_⟩
          · cases hε : M₁.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [DPDA.toPDA, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonLeft, hε]
          · simpa [quotLeftConf, List.map_append] using congrArg (quotLeftConf M₁ M₂) hcfg
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            left
            refine ⟨OptionalQuotState.left p, β.map OptionalStack.left, ?_, ?_⟩
            · cases ht : M₁.transition q a Z with
              | none => simp [DPDA.toPDA, ht] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, ht] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotTransitionLeft, ht]
            · simpa [quotLeftConf, List.map_append] using congrArg (quotLeftConf M₁ M₂) hcfg
          · rcases h with ⟨p, β, hp, hcfg⟩
            right
            refine ⟨OptionalQuotState.left p, β.map OptionalStack.left, ?_, ?_⟩
            · cases hε : M₁.epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonLeft, hε]
            · simpa [quotLeftConf, List.map_append] using congrArg (quotLeftConf M₁ M₂) hcfg

private lemma quot_left_reaches_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c c' : PDA.conf M₁.toPDA} :
    PDA.Reaches c c' →
      @PDA.Reaches (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnionQuot M₁ M₂).toPDA (quotLeftConf M₁ M₂ c) (quotLeftConf M₁ M₂ c') := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (quot_left_reaches₁_map M₁ M₂ hstep)

private lemma quot_right_reaches₁_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) (mark : T)
    {c c' : PDA.conf (quotientM M₂ mark).toPDA} :
    PDA.Reaches₁ c c' →
      @PDA.Reaches₁ (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnionQuot M₁ M₂).toPDA
        (quotRightConf M₁ M₂ mark c) (quotRightConf M₁ M₂ mark c') := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases c' with ⟨q', w', γ'⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn (DCFHomomorphism.DPDA.LeftQuotientState Q₂) T S₂ _ _ _
          (quotientM M₂ mark).toPDA 1 ⟨q, w, []⟩ ⟨q', w', γ'⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with ⟨p, β, hp, hcfg⟩
          refine ⟨OptionalQuotState.right mark p, β.map OptionalStack.right, ?_, ?_⟩
          · cases hε : (quotientM M₂ mark).epsilon_transition q Z with
            | none => simp [DPDA.toPDA, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [DPDA.toPDA, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonRight, hε]
          · simpa [quotRightConf, List.map_append] using congrArg (quotRightConf M₁ M₂ mark) hcfg
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            left
            refine ⟨OptionalQuotState.right mark p, β.map OptionalStack.right, ?_, ?_⟩
            · cases ht : (quotientM M₂ mark).transition q a Z with
              | none => simp [DPDA.toPDA, ht] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, ht] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotTransitionRight, ht]
            · simpa [quotRightConf, List.map_append] using congrArg (quotRightConf M₁ M₂ mark) hcfg
          · rcases h with ⟨p, β, hp, hcfg⟩
            right
            refine ⟨OptionalQuotState.right mark p, β.map OptionalStack.right, ?_, ?_⟩
            · cases hε : (quotientM M₂ mark).epsilon_transition q Z with
              | none => simp [DPDA.toPDA, hε] at hp
              | some pβ =>
                  rcases pβ with ⟨p', β'⟩
                  simp [DPDA.toPDA, hε] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonRight, hε]
            · simpa [quotRightConf, List.map_append] using congrArg (quotRightConf M₁ M₂ mark) hcfg

private lemma quot_right_reaches_map (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) (mark : T)
    {c c' : PDA.conf (quotientM M₂ mark).toPDA} :
    PDA.Reaches c c' →
      @PDA.Reaches (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
        (optionalMarkedUnionQuot M₁ M₂).toPDA
        (quotRightConf M₁ M₂ mark c) (quotRightConf M₁ M₂ mark c') := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (quot_right_reaches₁_map M₁ M₂ mark hstep)

private lemma quot_left_reaches₁_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₁.toPDA} {d : PDA.conf (optionalMarkedUnionQuot M₁ M₂).toPDA} :
    @PDA.Reaches₁ (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnionQuot M₁ M₂).toPDA (quotLeftConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₁.toPDA, d = quotLeftConf M₁ M₂ c' ∧ PDA.Reaches₁ c c' := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases d with ⟨qd, wd, γd⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
          (optionalMarkedUnionQuot M₁ M₂).toPDA 1 (quotLeftConf M₁ M₂ ⟨q, w, []⟩) ⟨qd, wd, γd⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with ⟨p, β, hp, hcfg⟩
          cases hε : M₁.epsilon_transition q Z with
          | none => simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonLeft, hε] at hp
          | some pβ =>
              rcases pβ with ⟨p', β'⟩
              simp [quotLeftConf, DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonLeft, hε] at hp
              rcases hp with ⟨rfl, rfl⟩
              refine ⟨⟨p', [], β' ++ γ⟩, ?_, ?_⟩
              · simpa [quotLeftConf, List.map_append] using hcfg
              · refine ⟨p', β', ?_, rfl⟩
                simp [DPDA.toPDA, hε]
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases ht : M₁.transition q a Z with
            | none => simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotTransitionLeft, ht] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [quotLeftConf, DPDA.toPDA, optionalMarkedUnionQuot, optQuotTransitionLeft, ht] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [quotLeftConf, List.map_append] using hcfg
                · left
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, ht]
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases hε : M₁.epsilon_transition q Z with
            | none => simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonLeft, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [quotLeftConf, DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonLeft, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', a :: w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [quotLeftConf, List.map_append] using hcfg
                · right
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, hε]

private lemma quot_left_reaches_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {c : PDA.conf M₁.toPDA} {d : PDA.conf (optionalMarkedUnionQuot M₁ M₂).toPDA} :
    @PDA.Reaches (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnionQuot M₁ M₂).toPDA (quotLeftConf M₁ M₂ c) d →
      ∃ c' : PDA.conf M₁.toPDA, d = quotLeftConf M₁ M₂ c' ∧ PDA.Reaches c c' := by
  intro h
  induction h with
  | refl => exact ⟨c, rfl, PDA.Reaches.refl _⟩
  | tail _ hstep ih =>
      rcases ih with ⟨c', rfl, hc'⟩
      rcases quot_left_reaches₁_unmap M₁ M₂ hstep with ⟨c'', rfl, hstep'⟩
      exact ⟨c'', rfl, Relation.ReflTransGen.tail hc' hstep'⟩

private lemma quot_right_reaches₁_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) (mark : T)
    {c : PDA.conf (quotientM M₂ mark).toPDA}
    {d : PDA.conf (optionalMarkedUnionQuot M₁ M₂).toPDA} :
    @PDA.Reaches₁ (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnionQuot M₁ M₂).toPDA (quotRightConf M₁ M₂ mark c) d →
      ∃ c' : PDA.conf (quotientM M₂ mark).toPDA,
        d = quotRightConf M₁ M₂ mark c' ∧ PDA.Reaches₁ c c' := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases d with ⟨qd, wd, γd⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
          (optionalMarkedUnionQuot M₁ M₂).toPDA 1 (quotRightConf M₁ M₂ mark ⟨q, w, []⟩)
          ⟨qd, wd, γd⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with ⟨p, β, hp, hcfg⟩
          cases hε : (quotientM M₂ mark).epsilon_transition q Z with
          | none => simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonRight, hε] at hp
          | some pβ =>
              rcases pβ with ⟨p', β'⟩
              simp [quotRightConf, DPDA.toPDA, optionalMarkedUnionQuot,
                optQuotEpsilonRight, hε] at hp
              rcases hp with ⟨rfl, rfl⟩
              refine ⟨⟨p', [], β' ++ γ⟩, ?_, ?_⟩
              · simpa [quotRightConf, List.map_append] using hcfg
              · refine ⟨p', β', ?_, rfl⟩
                simp [DPDA.toPDA, hε]
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases ht : (quotientM M₂ mark).transition q a Z with
            | none => simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotTransitionRight, ht] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [quotRightConf, DPDA.toPDA, optionalMarkedUnionQuot,
                  optQuotTransitionRight, ht] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [quotRightConf, List.map_append] using hcfg
                · left
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, ht]
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases hε : (quotientM M₂ mark).epsilon_transition q Z with
            | none => simp [DPDA.toPDA, optionalMarkedUnionQuot, optQuotEpsilonRight, hε] at hp
            | some pβ =>
                rcases pβ with ⟨p', β'⟩
                simp [quotRightConf, DPDA.toPDA, optionalMarkedUnionQuot,
                  optQuotEpsilonRight, hε] at hp
                rcases hp with ⟨rfl, rfl⟩
                refine ⟨⟨p', a :: w, β' ++ γ⟩, ?_, ?_⟩
                · simpa [quotRightConf, List.map_append] using hcfg
                · right
                  refine ⟨p', β', ?_, rfl⟩
                  simp [DPDA.toPDA, hε]

private lemma quot_right_reaches_unmap (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) (mark : T)
    {c : PDA.conf (quotientM M₂ mark).toPDA}
    {d : PDA.conf (optionalMarkedUnionQuot M₁ M₂).toPDA} :
    @PDA.Reaches (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
      (optionalMarkedUnionQuot M₁ M₂).toPDA (quotRightConf M₁ M₂ mark c) d →
      ∃ c' : PDA.conf (quotientM M₂ mark).toPDA,
        d = quotRightConf M₁ M₂ mark c' ∧ PDA.Reaches c c' := by
  intro h
  induction h with
  | refl => exact ⟨c, rfl, PDA.Reaches.refl _⟩
  | tail _ hstep ih =>
      rcases ih with ⟨c', rfl, hc'⟩
      rcases quot_right_reaches₁_unmap M₁ M₂ mark hstep with ⟨c'', rfl, hstep'⟩
      exact ⟨c'', rfl, Relation.ReflTransGen.tail hc' hstep'⟩

private lemma optionalQuot_accepts_left (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {w : List T} :
    w ∈ M₁.acceptsByFinalState →
      Sum.inl false :: w.map Sum.inr ∈ (optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState := by
  rintro ⟨q, hq, γ, hreach⟩
  refine ⟨OptionalQuotState.left q, ?_, γ.map OptionalStack.left, ?_⟩
  · right
    left
    exact ⟨q, hq, rfl⟩
  · let c0 : PDA.conf (optionalMarkedUnionQuot M₁ M₂).toPDA :=
      quotLeftConf M₁ M₂ ⟨M₁.initial_state, w, [M₁.start_symbol]⟩
    have hfirst :
        @PDA.Reaches₁ (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
          (optionalMarkedUnionQuot M₁ M₂).toPDA
          ⟨(optionalMarkedUnionQuot M₁ M₂).initial_state, Sum.inl false :: w.map Sum.inr,
            [(optionalMarkedUnionQuot M₁ M₂).start_symbol]⟩ c0 := by
      unfold c0 PDA.Reaches₁ PDA.step
      left
      refine ⟨OptionalQuotState.left M₁.initial_state, [OptionalStack.left M₁.start_symbol], ?_, ?_⟩
      · simp [DPDA.toPDA, optionalMarkedUnionQuot]
      · simp [quotLeftConf]
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hfirst)
      (quot_left_reaches_map M₁ M₂ hreach)

private lemma optionalQuot_accepts_right (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {w : List T} :
    w ∈ M₂.acceptsByFinalState →
      w.map Sum.inr ∈ (optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState := by
  intro hw
  cases w with
  | nil =>
      exact ⟨OptionalQuotState.start, by
        left
        exact ⟨rfl, hw⟩, [OptionalStack.bottom], Relation.ReflTransGen.refl⟩
  | cons a w =>
      have hquot :
          w ∈ (quotientM M₂ a).acceptsByFinalState := by
        rw [DCFHomomorphism.DPDA.leftQuotientSingleton_accepts]
        change a :: w ∈ M₂.acceptsByFinalState
        exact hw
      rcases hquot with ⟨q, hq, γ, hreach⟩
      refine ⟨OptionalQuotState.right a q, ?_, γ.map OptionalStack.right, ?_⟩
      · right
        right
        exact ⟨a, q, hq, rfl⟩
      · let c0 : PDA.conf (optionalMarkedUnionQuot M₁ M₂).toPDA :=
          quotRightConf M₁ M₂ a ⟨(quotientM M₂ a).initial_state, w,
            [(quotientM M₂ a).start_symbol]⟩
        have hfirst :
            @PDA.Reaches₁ (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
              (optionalMarkedUnionQuot M₁ M₂).toPDA
              ⟨(optionalMarkedUnionQuot M₁ M₂).initial_state,
                Sum.inr a :: w.map Sum.inr,
                [(optionalMarkedUnionQuot M₁ M₂).start_symbol]⟩ c0 := by
          unfold c0 PDA.Reaches₁ PDA.step
          left
          refine ⟨OptionalQuotState.right a (quotientM M₂ a).initial_state,
            [OptionalStack.right (quotientM M₂ a).start_symbol], ?_, ?_⟩
          · simp [DPDA.toPDA, optionalMarkedUnionQuot]
          · simp [quotRightConf]
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hfirst)
          (quot_right_reaches_map M₁ M₂ a hreach)

private lemma optionalQuot_accepts_marker_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {w : List T} :
    Sum.inl false :: w.map Sum.inr ∈ (optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState ↔
      w ∈ M₁.acceptsByFinalState := by
  constructor
  · rintro ⟨qf, hfinal, γ, hreach⟩
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨c, hstep, hrest⟩
    · cases heq
    · rcases c with ⟨s, y, stack⟩
      unfold PDA.Reaches₁ PDA.step at hstep
      rcases hstep with hstep | hstep
      · rcases hstep with ⟨p, β, hp, hcfg⟩
        simp [DPDA.toPDA, optionalMarkedUnionQuot] at hp
        rcases hp with ⟨rfl, rfl⟩
        cases hcfg
        have hrest' :
            @PDA.Reaches (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
              (optionalMarkedUnionQuot M₁ M₂).toPDA
              (quotLeftConf M₁ M₂ ⟨M₁.initial_state, w, [M₁.start_symbol]⟩)
              ⟨qf, [], γ⟩ := by
          simpa [quotLeftConf] using hrest
        rcases quot_left_reaches_unmap M₁ M₂ hrest' with ⟨c', hc', hM⟩
        rcases c' with ⟨q', w', γ'⟩
        simp [quotLeftConf] at hc'
        rcases hc' with ⟨rfl, rfl, rfl⟩
        have hq' : q' ∈ M₁.final_states := by
          rcases hfinal with hstart | hfinal
          · rcases hstart with ⟨hstart, _⟩
            simp [optionalMarkedUnionQuot] at hstart
          · rcases hfinal with hleft | hright
            · rcases hleft with ⟨q1, hq1, hqeq⟩
              simp [optionalMarkedUnionQuot] at hqeq
              rcases hqeq with rfl
              exact hq1
            · rcases hright with ⟨mark, q2, _, hqeq⟩
              simp [optionalMarkedUnionQuot] at hqeq
        exact ⟨q', hq', γ', hM⟩
      · rcases hstep with ⟨p, β, hp, hcfg⟩
        simp [DPDA.toPDA, optionalMarkedUnionQuot] at hp
  · exact optionalQuot_accepts_left M₁ M₂

private lemma optionalQuot_accepts_payload (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂)
    {w : List T} :
    w.map Sum.inr ∈ (optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState ↔
      w ∈ M₂.acceptsByFinalState := by
  constructor
  · intro h
    cases w with
    | nil =>
        rcases h with ⟨qf, hfinal, γ, hreach⟩
        rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨c, hstep, _⟩
        · cases heq
          rcases hfinal with hstart | hfinal
          · exact hstart.2
          · rcases hfinal with hleft | hright
            · rcases hleft with ⟨_, _, hbad⟩
              cases hbad
            · rcases hright with ⟨_, _, _, hbad⟩
              cases hbad
        · unfold PDA.Reaches₁ PDA.step at hstep
          simp [DPDA.toPDA, optionalMarkedUnionQuot] at hstep
    | cons a w =>
        rcases h with ⟨qf, hfinal, γ, hreach⟩
        rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨c, hstep, hrest⟩
        · cases heq
        · rcases c with ⟨s, y, stack⟩
          unfold PDA.Reaches₁ PDA.step at hstep
          rcases hstep with hstep | hstep
          · rcases hstep with ⟨p, β, hp, hcfg⟩
            simp [DPDA.toPDA, optionalMarkedUnionQuot] at hp
            rcases hp with ⟨rfl, rfl⟩
            cases hcfg
            have hrest' :
                @PDA.Reaches (OptionalQuotState T Q₁ Q₂) (Bool ⊕ T) (OptionalStack S₁ S₂) _ _ _
                  (optionalMarkedUnionQuot M₁ M₂).toPDA
                  (quotRightConf M₁ M₂ a ⟨(quotientM M₂ a).initial_state, w,
                    [(quotientM M₂ a).start_symbol]⟩)
                  ⟨qf, [], γ⟩ := by
              simpa [quotRightConf] using hrest
            rcases quot_right_reaches_unmap M₁ M₂ a hrest' with ⟨c', hc', hM⟩
            rcases c' with ⟨q', w', γ'⟩
            simp [quotRightConf] at hc'
            rcases hc' with ⟨rfl, rfl, rfl⟩
            have hq' : q' ∈ (quotientM M₂ a).final_states := by
              rcases hfinal with hstart | hfinal
              · rcases hstart with ⟨hstart, _⟩
                simp [optionalMarkedUnionQuot] at hstart
              · rcases hfinal with hleft | hright
                · rcases hleft with ⟨q1, _, hqeq⟩
                  simp [optionalMarkedUnionQuot] at hqeq
                · rcases hright with ⟨mark, q2, hq2, hqeq⟩
                  simp [optionalMarkedUnionQuot] at hqeq
                  rcases hqeq with ⟨rfl, rfl⟩
                  exact hq2
            have hquot : w ∈ (quotientM M₂ a).acceptsByFinalState :=
              ⟨q', hq', γ', hM⟩
            rw [DCFHomomorphism.DPDA.leftQuotientSingleton_accepts] at hquot
            change a :: w ∈ M₂.acceptsByFinalState at hquot
            exact hquot
          · rcases hstep with ⟨p, β, hp, hcfg⟩
            simp [DPDA.toPDA, optionalMarkedUnionQuot] at hp
  · exact optionalQuot_accepts_right M₁ M₂

private theorem is_DCF_optional_marked_union_machine
    (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    is_DCF (optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState :=
  ⟨OptionalQuotState T Q₁ Q₂, OptionalStack S₁ S₂, inferInstance, inferInstance,
    optionalMarkedUnionQuot M₁ M₂, rfl⟩

end DPDA

private abbrev marker {T : Type} : Bool ⊕ T := Sum.inl false

private abbrev markerStar (T : Type) : Language (Bool ⊕ T) :=
  KStar.kstar ({[marker]} : Language (Bool ⊕ T))

private abbrev payloadOnly (T : Type) : Language (Bool ⊕ T) :=
  Language.map Sum.inr (⊤ : Language T)

private abbrev oneMarkerPayload (T : Type) : Language (Bool ⊕ T) :=
  ({[marker]} : Language (Bool ⊕ T)) * payloadOnly T

private lemma markerStar_nil_mem {T : Type} :
    ([] : List (Bool ⊕ T)) ∈ markerStar T :=
  Language.nil_mem_kstar _

private lemma markerStar_singleton_mem {T : Type} :
    ([marker] : List (Bool ⊕ T)) ∈ markerStar T := by
  rw [markerStar, Language.mem_kstar]
  refine ⟨[[marker]], by simp, ?_⟩
  intro y hy
  simpa using hy

private lemma markerStar_all_marker {T : Type} {p : List (Bool ⊕ T)}
    (hp : p ∈ markerStar T) :
    ∀ a ∈ p, a = marker := by
  rw [markerStar, Language.mem_kstar] at hp
  rcases hp with ⟨blocks, rfl, hblocks⟩
  intro a ha
  rw [List.mem_flatten] at ha
  rcases ha with ⟨block, hblock, ha⟩
  have hblock' := hblocks block hblock
  rw [Set.mem_singleton_iff] at hblock'
  subst block
  simpa using ha

private lemma marker_not_mem_payload {T : Type} (w : List T) :
    (marker : Bool ⊕ T) ∉ w.map Sum.inr := by
  intro h
  rw [List.mem_map] at h
  rcases h with ⟨a, _ha, h⟩
  cases h

private lemma mem_oneMarkerPayload_iff {T : Type} {x : List (Bool ⊕ T)} :
    x ∈ oneMarkerPayload T ↔ ∃ w : List T, x = marker :: w.map Sum.inr := by
  rw [oneMarkerPayload, Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst u
    rcases hv with ⟨w, _hw, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨[marker], Set.mem_singleton _, w.map Sum.inr, ⟨w, trivial, rfl⟩, rfl⟩

private lemma oneMarkerPayload_regular {T : Type} [Fintype T] :
    (oneMarkerPayload T).IsRegular := by
  exact (Language.isRegular_singleton_word ([marker] : List (Bool ⊕ T))).mul'
    (Language.isRegular_top.map Sum.inr)

private lemma payloadOnly_regular {T : Type} [Fintype T] :
    (payloadOnly T).IsRegular :=
  Language.isRegular_top.map Sum.inr

/-- If `L₁` and `L₂` are deterministic context-free, so is the language that contains
either a marked payload from `L₁` or an unmarked payload from `L₂`. -/
public theorem DCF_optional_marked_union
    {T : Type} [Fintype T] {L₁ L₂ : Language T}
    (hL₁ : is_DCF L₁) (hL₂ : is_DCF L₂) :
    is_DCF ({x | (∃ w, x = (Sum.inl false : Bool ⊕ T) :: w.map Sum.inr ∧ w ∈ L₁) ∨
      (∃ w, x = w.map Sum.inr ∧ w ∈ L₂)} : Language (Bool ⊕ T)) := by
  rcases hL₁ with ⟨Q₁, S₁, hQ₁, hS₁, M₁, hM₁⟩
  rcases hL₂ with ⟨Q₂, S₂, hQ₂, hS₂, M₂, hM₂⟩
  let O : Language (Bool ⊕ T) := (DPDA.optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState
  let validShape : Language (Bool ⊕ T) := oneMarkerPayload T + payloadOnly T
  have hO : is_DCF O := DPDA.is_DCF_optional_marked_union_machine M₁ M₂
  have hShape : validShape.IsRegular :=
    (oneMarkerPayload_regular (T := T)).add' (payloadOnly_regular (T := T))
  have hFiltered : is_DCF (O ⊓ validShape) :=
    DCF_inter_regular O validShape hO hShape
  have hEq : O ⊓ validShape =
      ({x | (∃ w, x = (Sum.inl false : Bool ⊕ T) :: w.map Sum.inr ∧ w ∈ L₁) ∨
        (∃ w, x = w.map Sum.inr ∧ w ∈ L₂)} : Language (Bool ⊕ T)) := by
    ext x
    constructor
    · rintro ⟨hOmem, hshape⟩
      change x ∈ oneMarkerPayload T + payloadOnly T at hshape
      rw [Language.add_def] at hshape
      rcases hshape with hmarked | hunmarked
      · rw [mem_oneMarkerPayload_iff] at hmarked
        rcases hmarked with ⟨w, rfl⟩
        left
        refine ⟨w, rfl, ?_⟩
        simpa [hM₁, marker] using (DPDA.optionalQuot_accepts_marker_payload M₁ M₂).mp hOmem
      · rcases hunmarked with ⟨w, _hw, rfl⟩
        right
        refine ⟨w, rfl, ?_⟩
        simpa [hM₂] using (DPDA.optionalQuot_accepts_payload M₁ M₂).mp hOmem
    · rintro (⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩)
      · constructor
        · exact (DPDA.optionalQuot_accepts_marker_payload M₁ M₂).mpr (by simpa [hM₁] using hw)
        · change marker :: w.map Sum.inr ∈ oneMarkerPayload T + payloadOnly T
          rw [Language.add_def]
          left
          rw [mem_oneMarkerPayload_iff]
          exact ⟨w, rfl⟩
      · constructor
        · exact (DPDA.optionalQuot_accepts_payload M₁ M₂).mpr (by simpa [hM₂] using hw)
        · change w.map Sum.inr ∈ oneMarkerPayload T + payloadOnly T
          rw [Language.add_def]
          right
          exact ⟨w, trivial, rfl⟩
  rwa [← hEq]

private lemma markerStar_regular {T : Type} [Fintype T] :
    (markerStar T).IsRegular := by
  exact (Language.isRegular_singleton_word ([marker] : List (Bool ⊕ T))).kstar'

private lemma marker_payload_mem_concat_iff
    {T Q₁ Q₂ S₁ S₂ : Type}
    [Fintype T] [Fintype Q₁] [Fintype Q₂] [Fintype S₁] [Fintype S₂]
    (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) {w : List T} :
    (marker : Bool ⊕ T) :: w.map Sum.inr ∈
        markerStar T * (DPDA.optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState ↔
      w ∈ M₁.acceptsByFinalState ∨ w ∈ M₂.acceptsByFinalState := by
  constructor
  · intro h
    rw [Language.mem_mul] at h
    rcases h with ⟨p, hp, q, hq, hpq⟩
    have hall := markerStar_all_marker hp
    cases p with
    | nil =>
        simp at hpq
        subst q
        exact Or.inl ((DPDA.optionalQuot_accepts_marker_payload M₁ M₂).mp hq)
    | cons a p' =>
        have ha : a = marker := hall a (by simp)
        subst a
        cases p' with
        | nil =>
            simp at hpq
            subst q
            exact Or.inr ((DPDA.optionalQuot_accepts_payload M₁ M₂).mp hq)
        | cons b p'' =>
            have hb : b = marker := hall b (by simp)
            simp at hpq
            have hbmem : b ∈ w.map Sum.inr := by
              rw [← hpq]
              simp
            exact False.elim (marker_not_mem_payload w (by simpa [hb] using hbmem))
  · intro h
    rw [Language.mem_mul]
    rcases h with h | h
    · refine ⟨[], markerStar_nil_mem, marker :: w.map Sum.inr,
        (DPDA.optionalQuot_accepts_marker_payload M₁ M₂).mpr h, ?_⟩
      simp
    · refine ⟨[marker], markerStar_singleton_mem, w.map Sum.inr,
        (DPDA.optionalQuot_accepts_payload M₁ M₂).mpr h, ?_⟩
      simp

private theorem optional_concat_slice_eq_union
    {T Q₁ Q₂ S₁ S₂ : Type}
    [Fintype T] [Fintype Q₁] [Fintype Q₂] [Fintype S₁] [Fintype S₂]
    (M₁ : DPDA Q₁ T S₁) (M₂ : DPDA Q₂ T S₂) :
    [marker] \\ ((markerStar T * (DPDA.optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState) ⊓
        oneMarkerPayload T) =
      Language.map Sum.inr (M₁.acceptsByFinalState + M₂.acceptsByFinalState) := by
  ext x
  constructor
  · intro hx
    change (marker : Bool ⊕ T) :: x ∈
      ((markerStar T * (DPDA.optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState) ⊓
        oneMarkerPayload T) at hx
    rcases hx with ⟨hcat, hone⟩
    rw [mem_oneMarkerPayload_iff] at hone
    rcases hone with ⟨w, hshape⟩
    cases hshape
    rw [marker_payload_mem_concat_iff M₁ M₂] at hcat
    exact ⟨w, by simpa [Language.add_def] using hcat, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    change (marker : Bool ⊕ T) :: w.map Sum.inr ∈
      ((markerStar T * (DPDA.optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState) ⊓
        oneMarkerPayload T)
    constructor
    · rw [marker_payload_mem_concat_iff M₁ M₂]
      simpa [Language.add_def] using hw
    · rw [mem_oneMarkerPayload_iff]
      exact ⟨w, rfl⟩

/-- Deterministic context-free languages over `Bool ⊕ Fin 3` are not closed
under concatenation. -/
public theorem DCF_notClosedUnderConcatenation :
    ¬ ClosedUnderConcatenation (α := Bool ⊕ Fin 3) is_DCF := by
  intro hconcat
  apply DCF_notClosedUnderUnion
  intro L₁ L₂ hL₁ hL₂
  rcases hL₁ with ⟨Q₁, S₁, hQ₁, hS₁, M₁, hM₁⟩
  rcases hL₂ with ⟨Q₂, S₂, hQ₂, hS₂, M₂, hM₂⟩
  let O : Language (Bool ⊕ Fin 3) := (DPDA.optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState
  have hO : is_DCF O := DPDA.is_DCF_optional_marked_union_machine M₁ M₂
  have hStar : is_DCF (markerStar (Fin 3)) :=
    is_DCF_of_is_RG (is_RG_of_isRegular markerStar_regular)
  have hCat : is_DCF (markerStar (Fin 3) * O) :=
    hconcat (markerStar (Fin 3)) O hStar hO
  have hFiltered : is_DCF ((markerStar (Fin 3) * O) ⊓ oneMarkerPayload (Fin 3)) :=
    DCF_inter_regular (markerStar (Fin 3) * O) (oneMarkerPayload (Fin 3)) hCat
      oneMarkerPayload_regular
  have hQuot : is_DCF ([marker] \\ ((markerStar (Fin 3) * O) ⊓ oneMarkerPayload (Fin 3))) :=
    DCFHomomorphism.DCF_leftQuotient_singleton marker hFiltered
  change is_DCF ([marker] \\ ((markerStar (Fin 3) *
    (DPDA.optionalMarkedUnionQuot M₁ M₂).acceptsByFinalState) ⊓
      oneMarkerPayload (Fin 3))) at hQuot
  rw [optional_concat_slice_eq_union M₁ M₂] at hQuot
  have hUnion :=
    DCF_of_map_injective_DCF_rev (f := Sum.inr)
      (by
        intro a b h
        exact Sum.inr.inj h)
      (M₁.acceptsByFinalState + M₂.acceptsByFinalState) hQuot
  simpa [hM₁, hM₂] using hUnion

end DCFConcatenation
