module

public import Langlib.Automata.DeterministicPushdown.Totalization
public import Langlib.Classes.ContextFree.Closure.InverseHomomorphism
public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Utilities.ClosurePredicates

@[expose]
public section

/-!
# Deterministic Context-Free Closure Under Inverse Homomorphism

The construction first totalizes the source DPDA.  Besides preserving its
language, the totalizer keeps a permanent bottom-of-stack marker and records in
its finite control whether the current epsilon phase can accept.

For a homomorphism `h : α → List β`, the inverse-image machine stores one
source letter and a position in `h a` in finite control.  Consuming a source
letter is deliberately performed *before* the simulated epsilon phase.  This
ordering is essential when `h a = []`: prioritizing source-machine epsilon
steps can otherwise starve an erasable source letter forever.
-/

open PDA

noncomputable section

variable {α β : Type} [Fintype α] [Fintype β]
variable {Q S : Type} [Fintype Q] [Fintype S]

/-- A buffered source letter together with the next position of its nonempty image. -/
public abbrev InvHomBuffer (α β : Type) (h : α → List β) :=
  Option (Σ a : α, Fin (h a).length)

/-- The part of a buffered homomorphic image which remains to be simulated. -/
public def invHomBufferRemaining (h : α → List β) : InvHomBuffer α β h → List β
  | none => []
  | some ⟨a, k⟩ => (h a).drop k.val

/-- Extension of a string homomorphism to words. -/
public def invHomWord (h : α → List β) (w : List α) : List β :=
  w.flatMap h

/-- Advance past one simulated symbol in a nonempty buffered image. -/
public def invHomAdvance (h : α → List β) (a : α) (k : Fin (h a).length) :
    InvHomBuffer α β h :=
  if hk : k.val + 1 < (h a).length then
    some ⟨a, ⟨k.val + 1, hk⟩⟩
  else none

omit [Fintype α] [Fintype β] in
@[simp] theorem invHomWord_nil (h : α → List β) : invHomWord h [] = [] := rfl

omit [Fintype α] [Fintype β] in
@[simp] theorem invHomWord_cons (h : α → List β) (a : α) (w : List α) :
    invHomWord h (a :: w) = h a ++ invHomWord h w := by
  simp [invHomWord]

omit [Fintype α] [Fintype β] in
@[simp] theorem invHomBufferRemaining_none (h : α → List β) :
    invHomBufferRemaining h none = [] := rfl

/-- DPDA recognizing the inverse image of `M` under `h`, provided final-state
membership of `M` is invariant along its empty-input epsilon runs.

In the ready state (`buffer = none`) the machine has no epsilon transition: it
first consumes the next source letter.  A nonempty image is then drained through
epsilon transitions, with source-machine epsilon steps taking priority while a
buffer is present. -/
public def DPDA.inverseHomomorphism
    (M : DPDA Q β S) (h : α → List β) :
    DPDA (Q × InvHomBuffer α β h) α S where
  initial_state := (M.initial_state, none)
  start_symbol := M.start_symbol
  final_states := {p | p.1 ∈ M.final_states ∧ p.2 = none}
  transition := fun ⟨q, buffer⟩ a Z =>
    match buffer with
    | none =>
        if hlen : 0 < (h a).length then
          some ((q, some ⟨a, ⟨0, hlen⟩⟩), [Z])
        else
          some ((q, none), [Z])
    | some _ => none
  epsilon_transition := fun ⟨q, buffer⟩ Z =>
    match buffer with
    | none => none
    | some ⟨a, k⟩ =>
        match M.epsilon_transition q Z with
        | some (q', γ) => some ((q', some ⟨a, k⟩), γ)
        | none =>
            match M.transition q ((h a).get k) Z with
            | none => none
            | some (q', γ) => some ((q', invHomAdvance h a k), γ)
  no_mixed := by
    intro ⟨q, buffer⟩ Z hε a
    cases buffer with
    | none => simp at hε
    | some buffer => rfl

omit [Fintype α] [Fintype β] in
private theorem bufferRemaining_cons (h : α → List β)
    (a : α) (k : Fin (h a).length) :
    invHomBufferRemaining h (some ⟨a, k⟩) =
      (h a).get k :: (h a).drop (k.val + 1) := by
  unfold invHomBufferRemaining
  exact List.drop_eq_getElem_cons k.isLt

omit [Fintype α] [Fintype β] in
private theorem bufferRemaining_last (h : α → List β)
    (a : α) (k : Fin (h a).length)
    (hk : ¬ k.val + 1 < (h a).length) :
    invHomBufferRemaining h (some ⟨a, k⟩) = [(h a).get k] := by
  rw [bufferRemaining_cons]
  simp [List.drop_eq_nil_of_le (by omega : (h a).length ≤ k.val + 1)]

omit [Fintype α] [Fintype β] in
private theorem bufferRemaining_advance (h : α → List β)
    (a : α) (k : Fin (h a).length) :
    invHomBufferRemaining h (some ⟨a, k⟩) =
      (h a).get k :: invHomBufferRemaining h (invHomAdvance h a k) := by
  by_cases hk : k.val + 1 < (h a).length
  · rw [bufferRemaining_cons]
    simp [invHomAdvance, hk, invHomBufferRemaining]
  · rw [bufferRemaining_last h a k hk]
    simp [invHomAdvance, hk, invHomBufferRemaining]

private theorem source_epsilon_step
    (M : DPDA Q β S) (q q' : Q) (input : List β)
    (Z : S) (rest γ : List S)
    (hε : M.epsilon_transition q Z = some (q', γ)) :
    @PDA.Reaches₁ _ β S _ _ _ M.toPDA
      ⟨q, input, Z :: rest⟩ ⟨q', input, γ ++ rest⟩ := by
  cases input <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε]

private theorem source_input_step
    (M : DPDA Q β S) (q q' : Q) (b : β) (input : List β)
    (Z : S) (rest γ : List S)
    (hε : M.epsilon_transition q Z = none)
    (hδ : M.transition q b Z = some (q', γ)) :
    @PDA.Reaches₁ _ β S _ _ _ M.toPDA
      ⟨q, b :: input, Z :: rest⟩ ⟨q', input, γ ++ rest⟩ := by
  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε, hδ]

private theorem inverseHomomorphism_ready_step
    (M : DPDA Q β S) (h : α → List β)
    (q : Q) (a : α) (w : List α) (Z : S) (rest : List S) :
    let buffer : InvHomBuffer α β h :=
      if hlen : 0 < (h a).length then some ⟨a, ⟨0, hlen⟩⟩ else none
    @PDA.Reaches₁ _ α S _ _ _ (M.inverseHomomorphism h).toPDA
      ⟨(q, none), a :: w, Z :: rest⟩ ⟨(q, buffer), w, Z :: rest⟩ := by
  dsimp
  by_cases hlen : 0 < (h a).length
  · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, DPDA.inverseHomomorphism, hlen]
  · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, DPDA.inverseHomomorphism, hlen]

private theorem inverseHomomorphism_epsilon_step
    (M : DPDA Q β S) (h : α → List β)
    (q q' : Q) (a : α) (k : Fin (h a).length)
    (w : List α) (Z : S) (rest γ : List S)
    (hε : M.epsilon_transition q Z = some (q', γ)) :
    @PDA.Reaches₁ _ α S _ _ _ (M.inverseHomomorphism h).toPDA
      ⟨(q, some ⟨a, k⟩), w, Z :: rest⟩
      ⟨(q', some ⟨a, k⟩), w, γ ++ rest⟩ := by
  cases w <;>
    simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, DPDA.inverseHomomorphism, hε]

private theorem inverseHomomorphism_drain_step
    (M : DPDA Q β S) (h : α → List β)
    (q q' : Q) (a : α) (k : Fin (h a).length)
    (w : List α) (Z : S) (rest γ : List S)
    (hε : M.epsilon_transition q Z = none)
    (hδ : M.transition q ((h a).get k) Z = some (q', γ)) :
    @PDA.Reaches₁ _ α S _ _ _ (M.inverseHomomorphism h).toPDA
      ⟨(q, some ⟨a, k⟩), w, Z :: rest⟩
      ⟨(q', invHomAdvance h a k), w, γ ++ rest⟩ := by
  have hδ' : M.transition q (h a)[k.val] Z = some (q', γ) := by
    simpa only [List.get_eq_getElem] using hδ
  cases w <;>
    simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, DPDA.inverseHomomorphism, hε, hδ']

/-- Every inverse-machine step either stutters in, or is one step of, the source
machine on the represented virtual input. -/
private theorem inverseHomomorphism_step_projects
    (M : DPDA Q β S) (h : α → List β)
    {c₁ c₂ : @PDA.conf _ α S _ _ _ (M.inverseHomomorphism h).toPDA}
    (hstep : @PDA.Reaches₁ _ α S _ _ _ (M.inverseHomomorphism h).toPDA c₁ c₂) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨c₁.state.1,
        invHomBufferRemaining h c₁.state.2 ++ invHomWord h c₁.input,
        c₁.stack⟩
      ⟨c₂.state.1,
        invHomBufferRemaining h c₂.state.2 ++ invHomWord h c₂.input,
        c₂.stack⟩ := by
  rcases c₁ with ⟨⟨q, buffer⟩, input, stack⟩
  rcases stack with _ | ⟨Z, rest⟩
  · simp [PDA.Reaches₁, PDA.step] at hstep
  cases buffer with
  | none =>
      cases input with
      | nil =>
          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA,
            DPDA.inverseHomomorphism] at hstep
      | cons a w =>
          by_cases hlen : 0 < (h a).length
          · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA,
              DPDA.inverseHomomorphism, hlen] at hstep
            subst c₂
            simp [invHomBufferRemaining, invHomWord]
            exact Relation.ReflTransGen.refl
          · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA,
              DPDA.inverseHomomorphism, hlen] at hstep
            subst c₂
            have ha : h a = [] := List.eq_nil_of_length_eq_zero (by omega)
            simp [invHomBufferRemaining, invHomWord, ha]
            exact Relation.ReflTransGen.refl
  | some payload =>
      rcases payload with ⟨a, k⟩
      cases hε : M.epsilon_transition q Z with
      | some out =>
          rcases out with ⟨q', γ⟩
          cases input <;>
            simp [PDA.Reaches₁, PDA.step, DPDA.toPDA,
              DPDA.inverseHomomorphism, hε] at hstep
          all_goals
            rcases hstep with ⟨rfl, rfl, rfl⟩
            exact Relation.ReflTransGen.single
              (source_epsilon_step M q q'
                (invHomBufferRemaining h (some ⟨a, k⟩) ++ invHomWord h _)
                Z rest γ hε)
      | none =>
          cases hδ : M.transition q ((h a).get k) Z with
          | none =>
              have hδ' : M.transition q (h a)[k.val] Z = none := by
                simpa only [List.get_eq_getElem] using hδ
              cases input <;>
                simp [PDA.Reaches₁, PDA.step, DPDA.toPDA,
                  DPDA.inverseHomomorphism, hε, hδ'] at hstep
          | some out =>
              rcases out with ⟨q', γ⟩
              have hδ' : M.transition q (h a)[k.val] Z = some (q', γ) := by
                simpa only [List.get_eq_getElem] using hδ
              cases input <;>
                simp [PDA.Reaches₁, PDA.step, DPDA.toPDA,
                  DPDA.inverseHomomorphism, hε, hδ'] at hstep
              all_goals
                rcases hstep with ⟨rfl, rfl, rfl⟩
                rw [bufferRemaining_advance]
                exact Relation.ReflTransGen.single
                  (source_input_step M q q' ((h a).get k)
                    (invHomBufferRemaining h (invHomAdvance h a k) ++ invHomWord h _)
                    Z rest γ hε hδ)

/-- Projection extends from one step to finite reachability. -/
private theorem inverseHomomorphism_reaches_projects
    (M : DPDA Q β S) (h : α → List β)
    {c₁ c₂ : @PDA.conf _ α S _ _ _ (M.inverseHomomorphism h).toPDA}
    (hreach : @PDA.Reaches _ α S _ _ _ (M.inverseHomomorphism h).toPDA c₁ c₂) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨c₁.state.1,
        invHomBufferRemaining h c₁.state.2 ++ invHomWord h c₁.input,
        c₁.stack⟩
      ⟨c₂.state.1,
        invHomBufferRemaining h c₂.state.2 ++ invHomWord h c₂.input,
        c₂.stack⟩ := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans ih
        (inverseHomomorphism_step_projects M h hstep)

private theorem source_reachesIn_epsilon_first
    (M : DPDA Q β S) (n : ℕ)
    (q qε qf : Q) (input : List β) (Z : S) (rest γε γf : List S)
    (hε : M.epsilon_transition q Z = some (qε, γε))
    (hreach : @PDA.ReachesIn _ β S _ _ _ M.toPDA (n + 1)
      ⟨q, input, Z :: rest⟩ ⟨qf, [], γf⟩) :
    @PDA.ReachesIn _ β S _ _ _ M.toPDA n
      ⟨qε, input, γε ++ rest⟩ ⟨qf, [], γf⟩ := by
  obtain ⟨c, hone, hrest⟩ := PDA.reachesIn_iff_split_first.mpr hreach
  rw [PDA.reachesIn_one] at hone
  cases input with
  | nil =>
      simp [PDA.step, DPDA.toPDA, hε] at hone
      subst c
      exact hrest
  | cons b input =>
      have hδnone := M.no_mixed q Z (by simp [hε]) b
      simp [PDA.step, DPDA.toPDA, hε, hδnone] at hone
      subst c
      exact hrest

private theorem source_reachesIn_input_first
    (M : DPDA Q β S) (n : ℕ)
    (q qδ qf : Q) (b : β) (input : List β) (Z : S) (rest γδ γf : List S)
    (hε : M.epsilon_transition q Z = none)
    (hδ : M.transition q b Z = some (qδ, γδ))
    (hreach : @PDA.ReachesIn _ β S _ _ _ M.toPDA (n + 1)
      ⟨q, b :: input, Z :: rest⟩ ⟨qf, [], γf⟩) :
    @PDA.ReachesIn _ β S _ _ _ M.toPDA n
      ⟨qδ, input, γδ ++ rest⟩ ⟨qf, [], γf⟩ := by
  obtain ⟨c, hone, hrest⟩ := PDA.reachesIn_iff_split_first.mpr hreach
  rw [PDA.reachesIn_one] at hone
  simp [PDA.step, DPDA.toPDA, hε, hδ] at hone
  subst c
  exact hrest

/-- Completeness of the buffered simulation.  The nonempty-stack hypothesis is
used only to ensure that source letters with empty images can still be consumed.
The empty-input final-state hypothesis permits stopping in the ready state rather
than reproducing a trailing epsilon phase. -/
private theorem inverseHomomorphism_accept_lift
    (M : DPDA Q β S) (h : α → List β)
    (hfinal : ∀ (q q' : Q) (stack stack' : List S),
      @PDA.Reaches _ β S _ _ _ M.toPDA
        ⟨q, [], stack⟩ ⟨q', [], stack'⟩ →
      (q ∈ M.final_states ↔ q' ∈ M.final_states))
    (n : ℕ) (q : Q) (buffer : InvHomBuffer α β h)
    (w : List α) (stack : List S) (qf : Q) (stackf : List S)
    (hqf : qf ∈ M.final_states)
    (hreach : @PDA.ReachesIn _ β S _ _ _ M.toPDA n
      ⟨q, invHomBufferRemaining h buffer ++ invHomWord h w, stack⟩
      ⟨qf, [], stackf⟩)
    (hne : ∀ (c : @PDA.conf _ β S _ _ _ M.toPDA),
      @PDA.Reaches _ β S _ _ _ M.toPDA
        ⟨q, invHomBufferRemaining h buffer ++ invHomWord h w, stack⟩ c →
      c.stack ≠ []) :
    ∃ q' stack', q' ∈ M.final_states ∧
      @PDA.Reaches _ α S _ _ _ (M.inverseHomomorphism h).toPDA
        ⟨(q, buffer), w, stack⟩ ⟨(q', none), [], stack'⟩ := by
  cases buffer with
  | none =>
      cases w with
      | nil =>
          have hsource : @PDA.Reaches _ β S _ _ _ M.toPDA
              ⟨q, [], stack⟩ ⟨qf, [], stackf⟩ := by
            exact PDA.reaches_iff_reachesIn.mpr ⟨n, by simpa using hreach⟩
          have hq : q ∈ M.final_states := (hfinal q qf stack stackf hsource).2 hqf
          exact ⟨q, stack, hq, Relation.ReflTransGen.refl⟩
      | cons a w =>
          have hstack : stack ≠ [] := hne _ Relation.ReflTransGen.refl
          obtain ⟨Z, rest, rfl⟩ := List.exists_cons_of_ne_nil hstack
          by_cases hlen : 0 < (h a).length
          · let nextBuffer : InvHomBuffer α β h := some ⟨a, ⟨0, hlen⟩⟩
            have hready := inverseHomomorphism_ready_step M h q a w Z rest
            have hreach' : @PDA.ReachesIn _ β S _ _ _ M.toPDA n
                ⟨q, invHomBufferRemaining h nextBuffer ++ invHomWord h w, Z :: rest⟩
                ⟨qf, [], stackf⟩ := by
              simpa [nextBuffer, invHomBufferRemaining, invHomWord] using hreach
            have hne' : ∀ (c : @PDA.conf _ β S _ _ _ M.toPDA),
                @PDA.Reaches _ β S _ _ _ M.toPDA
                  ⟨q, invHomBufferRemaining h nextBuffer ++ invHomWord h w, Z :: rest⟩ c →
                c.stack ≠ [] := by
              simpa [nextBuffer, invHomBufferRemaining, invHomWord] using hne
            obtain ⟨q', stack', hq', hlift⟩ :=
              inverseHomomorphism_accept_lift M h hfinal n q nextBuffer w
                (Z :: rest) qf stackf hqf hreach' hne'
            have hready' : @PDA.Reaches₁ _ α S _ _ _ (M.inverseHomomorphism h).toPDA
                ⟨(q, none), a :: w, Z :: rest⟩ ⟨(q, nextBuffer), w, Z :: rest⟩ := by
              simpa [nextBuffer, hlen] using hready
            exact ⟨q', stack', hq', Relation.ReflTransGen.trans
              (Relation.ReflTransGen.single hready') hlift⟩
          · have ha : h a = [] := List.eq_nil_of_length_eq_zero (by omega)
            have hready := inverseHomomorphism_ready_step M h q a w Z rest
            have hreach' : @PDA.ReachesIn _ β S _ _ _ M.toPDA n
                ⟨q, invHomBufferRemaining h none ++ invHomWord h w, Z :: rest⟩
                ⟨qf, [], stackf⟩ := by
              simpa [invHomBufferRemaining, invHomWord, ha] using hreach
            have hne' : ∀ (c : @PDA.conf _ β S _ _ _ M.toPDA),
                @PDA.Reaches _ β S _ _ _ M.toPDA
                  ⟨q, invHomBufferRemaining h none ++ invHomWord h w, Z :: rest⟩ c →
                c.stack ≠ [] := by
              simpa [invHomBufferRemaining, invHomWord, ha] using hne
            obtain ⟨q', stack', hq', hlift⟩ :=
              inverseHomomorphism_accept_lift M h hfinal n q none w
                (Z :: rest) qf stackf hqf hreach' hne'
            have hready' : @PDA.Reaches₁ _ α S _ _ _ (M.inverseHomomorphism h).toPDA
                ⟨(q, none), a :: w, Z :: rest⟩ ⟨(q, none), w, Z :: rest⟩ := by
              simpa [hlen] using hready
            exact ⟨q', stack', hq',
              Relation.ReflTransGen.trans (Relation.ReflTransGen.single hready') hlift⟩
  | some payload =>
      rcases payload with ⟨a, k⟩
      have hstack : stack ≠ [] := hne _ Relation.ReflTransGen.refl
      obtain ⟨Z, rest, rfl⟩ := List.exists_cons_of_ne_nil hstack
      cases n with
      | zero =>
          have heq := PDA.reachesIn_zero hreach
          have hinput := congrArg PDA.conf.input heq
          rw [bufferRemaining_cons] at hinput
          simp at hinput
          exact (Nat.not_le_of_lt k.isLt hinput.1).elim
      | succ n =>
          cases hε : M.epsilon_transition q Z with
          | some out =>
              rcases out with ⟨qε, γε⟩
              have hfirst := source_epsilon_step M q qε
                (invHomBufferRemaining h (some ⟨a, k⟩) ++ invHomWord h w)
                Z rest γε hε
              have hreach' := source_reachesIn_epsilon_first M n q qε qf
                (invHomBufferRemaining h (some ⟨a, k⟩) ++ invHomWord h w)
                Z rest γε stackf hε (by simpa [Nat.succ_eq_add_one] using hreach)
              have hne' : ∀ (c : @PDA.conf _ β S _ _ _ M.toPDA),
                  @PDA.Reaches _ β S _ _ _ M.toPDA
                    ⟨qε, invHomBufferRemaining h (some ⟨a, k⟩) ++ invHomWord h w,
                      γε ++ rest⟩ c →
                  c.stack ≠ [] := by
                intro c hc
                exact hne c (Relation.ReflTransGen.trans
                  (Relation.ReflTransGen.single hfirst) hc)
              obtain ⟨q', stack', hq', hlift⟩ :=
                inverseHomomorphism_accept_lift M h hfinal n qε (some ⟨a, k⟩) w
                  (γε ++ rest) qf stackf hqf hreach' hne'
              have hinv := inverseHomomorphism_epsilon_step M h q qε a k w Z rest γε hε
              exact ⟨q', stack', hq',
                Relation.ReflTransGen.trans (Relation.ReflTransGen.single hinv) hlift⟩
          | none =>
              cases hδ : M.transition q ((h a).get k) Z with
              | none =>
                  have hδ' : M.transition q (h a)[k.val] Z = none := by
                    simpa only [List.get_eq_getElem] using hδ
                  obtain ⟨c, hone, _⟩ := PDA.reachesIn_iff_split_first.mpr
                    (by simpa [Nat.succ_eq_add_one] using hreach)
                  rw [PDA.reachesIn_one] at hone
                  have hinputEq :
                      invHomBufferRemaining h (some ⟨a, k⟩) ++ invHomWord h w =
                        (h a).get k :: ((h a).drop (k.val + 1) ++ invHomWord h w) := by
                    rw [bufferRemaining_cons]
                    rfl
                  rw [hinputEq] at hone
                  simp [PDA.step, DPDA.toPDA, hε, hδ', List.get_eq_getElem] at hone
              | some out =>
                  rcases out with ⟨qδ, γδ⟩
                  have hfirst := source_input_step M q qδ ((h a).get k)
                    (invHomBufferRemaining h (invHomAdvance h a k) ++ invHomWord h w)
                    Z rest γδ hε hδ
                  have hreach' : @PDA.ReachesIn _ β S _ _ _ M.toPDA n
                      ⟨qδ,
                        invHomBufferRemaining h (invHomAdvance h a k) ++ invHomWord h w,
                        γδ ++ rest⟩
                      ⟨qf, [], stackf⟩ := by
                    have hreach0 := hreach
                    rw [bufferRemaining_advance] at hreach0
                    apply source_reachesIn_input_first M n q qδ qf ((h a).get k)
                      (invHomBufferRemaining h (invHomAdvance h a k) ++ invHomWord h w)
                      Z rest γδ stackf hε hδ
                    simpa [Nat.succ_eq_add_one] using hreach0
                  have hne' : ∀ (c : @PDA.conf _ β S _ _ _ M.toPDA),
                      @PDA.Reaches _ β S _ _ _ M.toPDA
                        ⟨qδ,
                          invHomBufferRemaining h (invHomAdvance h a k) ++ invHomWord h w,
                          γδ ++ rest⟩ c →
                      c.stack ≠ [] := by
                    intro c hc
                    apply hne c
                    rw [bufferRemaining_advance]
                    exact Relation.ReflTransGen.trans
                      (Relation.ReflTransGen.single hfirst) hc
                  obtain ⟨q', stack', hq', hlift⟩ :=
                    inverseHomomorphism_accept_lift M h hfinal n qδ
                      (invHomAdvance h a k) w (γδ ++ rest)
                      qf stackf hqf hreach' hne'
                  have hinv := inverseHomomorphism_drain_step M h q qδ a k w
                    Z rest γδ hε hδ
                  exact ⟨q', stack', hq',
                    Relation.ReflTransGen.trans (Relation.ReflTransGen.single hinv) hlift⟩
termination_by n + w.length

/-- Correctness of the repaired inverse-homomorphism construction under the two
normal-form properties supplied by the DPDA totalizer. -/
public theorem DPDA.inverseHomomorphism_correct
    (M : DPDA Q β S) (h : α → List β)
    (hfinal : ∀ (q q' : Q) (stack stack' : List S),
      @PDA.Reaches _ β S _ _ _ M.toPDA
        ⟨q, [], stack⟩ ⟨q', [], stack'⟩ →
      (q ∈ M.final_states ↔ q' ∈ M.final_states))
    (hne : ∀ (w : List β) (c : @PDA.conf _ β S _ _ _ M.toPDA),
      @PDA.Reaches _ β S _ _ _ M.toPDA
        ⟨M.initial_state, w, [M.start_symbol]⟩ c → c.stack ≠ []) :
    (M.inverseHomomorphism h).acceptsByFinalState =
      M.acceptsByFinalState.inverseHomomorphicImage h := by
  ext w
  constructor
  · rintro ⟨⟨q, buffer⟩, ⟨hq, hbuffer⟩, stack, hreach⟩
    change buffer = none at hbuffer
    subst buffer
    have hproject := inverseHomomorphism_reaches_projects M h hreach
    have hsource : @PDA.Reaches _ β S _ _ _ M.toPDA
        ⟨M.initial_state, invHomWord h w, [M.start_symbol]⟩
        ⟨q, [], stack⟩ := by
      simpa [invHomBufferRemaining, invHomWord] using hproject
    change w.flatMap h ∈ M.acceptsByFinalState
    exact ⟨q, hq, stack, by simpa [invHomWord] using hsource⟩
  · intro hw
    change w.flatMap h ∈ M.acceptsByFinalState at hw
    obtain ⟨qf, hqf, stackf, hreach⟩ := hw
    obtain ⟨n, hn⟩ := PDA.reaches_iff_reachesIn.mp hreach
    have hne' : ∀ (c : @PDA.conf _ β S _ _ _ M.toPDA),
        @PDA.Reaches _ β S _ _ _ M.toPDA
          ⟨M.initial_state,
            invHomBufferRemaining h none ++ invHomWord h w,
            [M.start_symbol]⟩ c →
        c.stack ≠ [] := by
      simpa [invHomBufferRemaining, invHomWord] using hne (w.flatMap h)
    have hn' : @PDA.ReachesIn _ β S _ _ _ M.toPDA n
        ⟨M.initial_state,
          invHomBufferRemaining h none ++ invHomWord h w,
          [M.start_symbol]⟩
        ⟨qf, [], stackf⟩ := by
      simpa [invHomBufferRemaining, invHomWord] using hn
    obtain ⟨q', stack', hq', hlift⟩ :=
      inverseHomomorphism_accept_lift M h hfinal n M.initial_state none w
        [M.start_symbol] qf stackf hqf hn' hne'
    exact ⟨(q', none), ⟨hq', rfl⟩, stack', hlift⟩

/-- Deterministic context-free languages are closed under inverse string
homomorphism. -/
public theorem DCF_closed_under_inverse_homomorphism
    (L : Language β) (h : α → List β) (hL : is_DCF L) :
    is_DCF (L.inverseHomomorphicImage h) := by
  obtain ⟨Q, S, _, _, M, hM⟩ := hL
  obtain ⟨A⟩ := DPDA.hasRegularEpsilonAnalysis M
  let M' := DPDA.totalizer A
  have hfinal : ∀ (q q' : DPDA.TotalState Q)
      (stack stack' : List (DPDA.TotalStackSymbol A)),
      @PDA.Reaches _ β (DPDA.TotalStackSymbol A) _ _ _ M'.toPDA
        ⟨q, [], stack⟩ ⟨q', [], stack'⟩ →
      (q ∈ M'.final_states ↔ q' ∈ M'.final_states) := by
    intro q q' stack stack' hr
    exact DPDA.totalizer_empty_reaches_preserves_final (A := A) hr
  have hne : ∀ (w : List β)
      (c : @PDA.conf _ β (DPDA.TotalStackSymbol A) _ _ _ M'.toPDA),
      @PDA.Reaches _ β (DPDA.TotalStackSymbol A) _ _ _ M'.toPDA
        ⟨M'.initial_state, w, [M'.start_symbol]⟩ c → c.stack ≠ [] := by
    intro w c hr hempty
    have hbottom := (DPDA.totalizer_reaches_stack_invariants (A := A) w hr).2
    rw [hempty] at hbottom
    exact hbottom
  refine ⟨DPDA.TotalState Q × InvHomBuffer α β h,
    DPDA.TotalStackSymbol A, inferInstance, inferInstance,
    M'.inverseHomomorphism h, ?_⟩
  rw [DPDA.inverseHomomorphism_correct M' h hfinal hne,
    DPDA.totalizer_acceptsByFinalState_eq_original (A := A), hM]

/-- Predicate-form closure theorem used by the README closure table. -/
public theorem DCF_closedUnderInverseHomomorphism :
    ClosedUnderInverseHomomorphism is_DCF := by
  intro α β _ _ L h hL
  simpa [Language.inverseHomomorphicImage] using
    DCF_closed_under_inverse_homomorphism (L := L) h hL

end
