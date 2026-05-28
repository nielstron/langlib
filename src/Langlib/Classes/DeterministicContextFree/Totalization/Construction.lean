import Langlib.Classes.DeterministicContextFree.Totalization.AnnotatedStack

/-! # Totalization Construction

This file defines the analyzed DPDA totalizer and proves that it is an equivalent
deciding presentation for the original final-state DPDA.  The stack annotation
infrastructure lives in `Totalization.AnnotatedStack`.
-/

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
variable {M : DPDA Q T S} (A : M.RegularEpsilonAnalysis)

noncomputable section

/-- Finite control states of the totalized DPDA.  The boolean in `sim` records
whether the original machine would accept if the input ended at the current stack. -/
inductive TotalState (Q : Type) where
  | init : TotalState Q
  | sim : Q → Bool → TotalState Q
  | drain : TotalState Q
deriving DecidableEq, Fintype

/-- Replacement block for an original stack update above a known suffix summary. -/
def annotatedReplacement (below : AnalysisSummary A) (β : List S) : List (TotalStackSymbol A) :=
  annotateAbove A below β

/-- Initial stack expansion: install the original start symbol above the permanent bottom. -/
def initialReplacement : List (TotalStackSymbol A) :=
  annotateAbove A (AnalysisSummary.id A) [M.start_symbol] ++ [none]

theorem erase_annotatedReplacement (below : AnalysisSummary A) (β : List S) :
    eraseAnnotatedStack (A := A) (annotatedReplacement A below β) = β :=
  erase_annotateAbove A below β

theorem erase_annotatedReplacement_append (below : AnalysisSummary A) (β : List S)
    (rest : List (TotalStackSymbol A)) :
    eraseAnnotatedStack (A := A) (annotatedReplacement A below β ++ rest) =
      β ++ eraseAnnotatedStack (A := A) rest := by
  rw [eraseAnnotatedStack_append, erase_annotatedReplacement]

theorem erase_initialReplacement :
    eraseAnnotatedStack (A := A) (initialReplacement A) = [M.start_symbol] := by
  simp [initialReplacement, eraseAnnotatedStack]

theorem stackWellAnnotated_initialReplacement :
    StackWellAnnotated (A := A) (initialReplacement A) := by
  simpa [initialReplacement] using
    stackWellAnnotated_annotateAbove_bottom (A := A) [M.start_symbol]

theorem stackHasBottom_initialReplacement :
    StackHasBottom (A := A) (initialReplacement A) := by
  simpa [initialReplacement] using
    stackHasBottom_annotateAbove_bottom (A := A) [M.start_symbol]

theorem stackWellAnnotated_annotatedReplacement_append {below : AnalysisSummary A}
    {rest : List (TotalStackSymbol A)} (β : List S)
    (hbelow : SummaryRepresents A below (eraseAnnotatedStack (A := A) rest))
    (hrest : StackWellAnnotated (A := A) rest) :
    StackWellAnnotated (A := A) (annotatedReplacement A below β ++ rest) :=
  stackWellAnnotated_annotateAbove_append (A := A) hbelow hrest β

theorem stackHasBottom_annotatedReplacement_append {below : AnalysisSummary A}
    {rest : List (TotalStackSymbol A)} (β : List S)
    (hrest : StackHasBottom (A := A) rest) :
    StackHasBottom (A := A) (annotatedReplacement A below β ++ rest) :=
  stackHasBottom_annotateAbove_append (A := A) hrest β

theorem summaryRepresents_replacement {below : AnalysisSummary A}
    {rest : List (TotalStackSymbol A)} (β : List S)
    (hbelow : SummaryRepresents A below (eraseAnnotatedStack (A := A) rest)) :
    SummaryRepresents A (below.above A β)
      (eraseAnnotatedStack (A := A) (annotatedReplacement A below β ++ rest)) := by
  rw [erase_annotatedReplacement_append]
  exact hbelow.above (A := A) β

theorem replacement_preserves_annotations {Z : S} {below : AnalysisSummary A}
    {rest : List (TotalStackSymbol A)} (β : List S)
    (hstack : StackWellAnnotated (A := A) (some (Z, below) :: rest)) :
    StackWellAnnotated (A := A) (annotatedReplacement A below β ++ rest) ∧
      SummaryRepresents A (below.above A β)
        (eraseAnnotatedStack (A := A) (annotatedReplacement A below β ++ rest)) := by
  exact
    ⟨stackWellAnnotated_annotatedReplacement_append (A := A) β hstack.1 hstack.2,
      summaryRepresents_replacement (A := A) β hstack.1⟩

theorem replacement_preserves_bottom {Z : S} {below : AnalysisSummary A}
    {rest : List (TotalStackSymbol A)} (β : List S)
    (hbottom : StackHasBottom (A := A) (some (Z, below) :: rest)) :
    StackHasBottom (A := A) (annotatedReplacement A below β ++ rest) :=
  stackHasBottom_annotatedReplacement_append (A := A) β hbottom

theorem initialSummaryRepresents :
    SummaryRepresents A ((AnalysisSummary.id A).above A [M.start_symbol]) [M.start_symbol] :=
  (summaryRepresents_id A).cons (A := A) M.start_symbol

def initialSummary : AnalysisSummary A :=
  (AnalysisSummary.id A).above A [M.start_symbol]

def initialAcceptBit : Bool :=
  acceptBit A M.initial_state (initialSummary A)

theorem initial_configuration_annotations :
    StackWellAnnotated (A := A) (initialReplacement A) ∧
      StackHasBottom (A := A) (initialReplacement A) ∧
      SummaryRepresents A (initialSummary A)
        (eraseAnnotatedStack (A := A) (initialReplacement A)) := by
  rw [erase_initialReplacement]
  exact
    ⟨stackWellAnnotated_initialReplacement A, stackHasBottom_initialReplacement A,
      initialSummaryRepresents A⟩

/-- The finite-control state corresponding to an original state and a resulting stack summary. -/
def simState (q : Q) (summary : AnalysisSummary A) : TotalState Q :=
  TotalState.sim q (acceptBit A q summary)

/-- The analyzed totalizer.  It follows terminating epsilon phases of `M`, treats
divergent epsilon phases as stable decision points, and drains any remaining input
to a rejecting state when the original computation cannot consume the next symbol. -/
def totalizer : DPDA (TotalState Q) T (TotalStackSymbol A) := by
  classical
  refine
    { initial_state := TotalState.init
      start_symbol := none
      final_states := { st |
        (st = TotalState.init ∧ initialAcceptBit A = true) ∨
          ∃ q, st = TotalState.sim q true }
      transition := ?transition
      epsilon_transition := ?epsilon
      no_mixed := ?no_mixed }
  · intro st a top
    exact
      match st with
      | TotalState.init => none
      | TotalState.drain => some (TotalState.drain, [top])
      | TotalState.sim q _ =>
          match top with
          | none => some (TotalState.drain, [none])
          | some (Z, below) =>
              match M.epsilon_transition q Z with
              | some _ =>
                  if stopsFromSummary A q (fullSummaryOfTop A top) then
                    none
                  else
                    some (TotalState.drain, [top])
              | none =>
                  match M.transition q a Z with
                  | some (p, β) =>
                      some (simState A p (below.above A β), annotatedReplacement A below β)
                  | none => some (TotalState.drain, [top])
  · intro st top
    exact
      match st with
      | TotalState.init =>
          match top with
          | none =>
              some (simState A M.initial_state ((AnalysisSummary.id A).above A [M.start_symbol]),
                initialReplacement A)
          | some _ => none
      | TotalState.drain => none
      | TotalState.sim q b =>
          match top with
          | none => none
          | some (Z, below) =>
              match M.epsilon_transition q Z with
              | some (p, β) =>
                  if stopsFromSummary A q (fullSummaryOfTop A top) then
                    some (TotalState.sim p b, annotatedReplacement A below β)
                  else
                    none
              | none => none
  · intro st top hε a
    cases st with
    | init =>
        cases top <;> simp at hε ⊢
    | drain =>
        simp at hε
    | sim q b =>
        cases top with
        | none => simp at hε
        | some payload =>
            rcases payload with ⟨Z, below⟩
            cases hMε : M.epsilon_transition q Z with
            | none => simp [hMε] at hε
            | some out =>
                by_cases hstop : stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                · simp [hMε, hstop]
                · simp [hMε, hstop] at hε

theorem simState_mem_final_iff (q : Q) (summary : AnalysisSummary A) :
    simState A q summary ∈ (totalizer A).final_states ↔ acceptsFromSummary A q summary := by
  classical
  simp [totalizer, simState, acceptBit_eq_true_iff]

theorem sim_mem_final_iff (q : Q) (b : Bool) :
    TotalState.sim q b ∈ (totalizer A).final_states ↔ b = true := by
  cases b <;> simp [totalizer]

theorem simState_mem_final_iff_semantic {q : Q} {summary : AnalysisSummary A} {γ : List S}
    (hsummary : SummaryRepresents A summary γ) :
    simState A q summary ∈ (totalizer A).final_states ↔
      ∃ q' γ', M.EpsilonReaches (q, γ) (q', γ') ∧ q' ∈ M.final_states := by
  rw [simState_mem_final_iff]
  exact acceptsFromSummary_correct A hsummary q

theorem init_mem_final_iff :
    TotalState.init ∈ (totalizer A).final_states ↔ initialAcceptBit A = true := by
  simp [totalizer]

theorem drain_not_mem_final :
    TotalState.drain ∉ (totalizer A).final_states := by
  simp [totalizer]

theorem totalizer_empty_step_preserves_final
    {st₁ st₂ : TotalState Q} {stack₁ stack₂ : List (TotalStackSymbol A)}
    (hstep : @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA ⟨st₁, [], stack₁⟩ ⟨st₂, [], stack₂⟩) :
    st₁ ∈ (totalizer A).final_states ↔ st₂ ∈ (totalizer A).final_states := by
  cases st₁ with
  | init =>
      cases stack₁ with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons top rest =>
          cases top with
          | none =>
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, initialAcceptBit] at hstep ⊢
              rcases hstep with ⟨rfl, _⟩
              simp [initialSummary, simState]
          | some payload =>
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
  | drain =>
      cases stack₁ with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons top rest =>
          cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
  | sim q b =>
      cases stack₁ with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons top rest =>
          cases top with
          | none =>
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
          | some payload =>
              rcases payload with ⟨Z, below⟩
              cases hε : M.epsilon_transition q Z with
              | none =>
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε] at hstep
              | some out =>
                  by_cases hstops : stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                  · rcases out with ⟨p, β⟩
                    simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep ⊢
                    rcases hstep with ⟨rfl, _⟩
                    cases b <;> simp
                  · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep

theorem totalizer_empty_reaches_preserves_final_aux
    {st₁ : TotalState Q} {stack₁ : List (TotalStackSymbol A)}
    {c₂ : @PDA.conf (TotalState Q) T (TotalStackSymbol A) _ _ _ (totalizer A).toPDA}
    (hreach : @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA ⟨st₁, [], stack₁⟩ c₂) :
    st₁ ∈ (totalizer A).final_states ↔ c₂.state ∈ (totalizer A).final_states := by
  induction hreach with
  | refl => rfl
  | @tail c₁ c₂ hprefix hstep ih =>
      have hc₁_input : c₁.input = [] := by
        obtain ⟨u, hu⟩ := PDA.decreasing_input hprefix
        simp at hu
        exact hu.2
      have hc₂_input : c₂.input = [] := by
        obtain ⟨u, hu⟩ := PDA.decreasing_input_one (PDA.reaches₁_iff_reachesIn_one.mp hstep)
        simp [hc₁_input] at hu
        exact hu.2
      cases c₁ with
      | mk stMid inputMid stackMid =>
          simp at hc₁_input
          subst inputMid
          cases c₂ with
          | mk st₂ input₂ stack₂ =>
              simp at hc₂_input
              subst input₂
              exact Iff.trans ih (totalizer_empty_step_preserves_final (A := A) hstep)

theorem totalizer_empty_reaches_preserves_final
    {st₁ st₂ : TotalState Q} {stack₁ stack₂ : List (TotalStackSymbol A)}
    (hreach : @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA ⟨st₁, [], stack₁⟩ ⟨st₂, [], stack₂⟩) :
    st₁ ∈ (totalizer A).final_states ↔ st₂ ∈ (totalizer A).final_states :=
  totalizer_empty_reaches_preserves_final_aux (A := A) hreach

theorem totalizer_step_deterministic
    {c c₁ c₂ : @PDA.conf (TotalState Q) T (TotalStackSymbol A) _ _ _ (totalizer A).toPDA}
    (h₁ : @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA c c₁)
    (h₂ : @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA c c₂) :
    c₁ = c₂ := by
  have close :
      ∀ {st₁ st₂ st : TotalState Q}
        {input₁ input₂ input : List T}
        {stack₁ stack₂ stack : List (TotalStackSymbol A)},
        st₁ = st ∧ input₁ = input ∧ stack₁ = stack →
        st₂ = st ∧ input₂ = input ∧ stack₂ = stack →
        st₁ = st₂ ∧ input₁ = input₂ ∧ stack₁ = stack₂ := by
    intro st₁ st₂ st input₁ input₂ input stack₁ stack₂ stack h₁ h₂
    rcases h₁ with ⟨rfl, rfl, rfl⟩
    rcases h₂ with ⟨rfl, rfl, rfl⟩
    simp
  rcases c with ⟨st, input, stack⟩
  rcases c₁ with ⟨st₁, input₁, stack₁⟩
  rcases c₂ with ⟨st₂, input₂, stack₂⟩
  cases input with
  | nil =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at h₁
      | cons top rest =>
          cases st with
          | init =>
              cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at h₁ h₂ ⊢;
                exact close h₁ h₂
          | drain =>
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at h₁
          | sim q b =>
              cases top with
              | none =>
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at h₁
              | some payload =>
                  rcases payload with ⟨Z, below⟩
                  cases hε : M.epsilon_transition q Z with
                  | none =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε] at h₁
                  | some out =>
                      by_cases hstops : stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                      · rcases out with ⟨p, β⟩
                        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at h₁ h₂ ⊢
                        exact close h₁ h₂
                      · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at h₁
  | cons a inputTail =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at h₁
      | cons top rest =>
          cases st with
          | init =>
              cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at h₁ h₂ ⊢;
                exact close h₁ h₂
          | drain =>
              cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at h₁ h₂ ⊢ <;>
                exact close h₁ h₂
          | sim q b =>
              cases top with
              | none =>
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at h₁ h₂ ⊢
                  exact close h₁ h₂
              | some payload =>
                  rcases payload with ⟨Z, below⟩
                  cases hε : M.epsilon_transition q Z with
                  | none =>
                      cases hδ : M.transition q a Z with
                      | none =>
                          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hδ] at h₁ h₂ ⊢
                          exact close h₁ h₂
                      | some out =>
                          rcases out with ⟨p, β⟩
                          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hδ] at h₁ h₂ ⊢
                          exact close h₁ h₂
                  | some out =>
                      rcases out with ⟨p, β⟩
                      by_cases hstops : stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                      · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at h₁ h₂ ⊢
                        exact close h₁ h₂
                      · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at h₁ h₂ ⊢
                        exact close h₁ h₂

theorem totalizer_reachesIn_deterministic
    {n : ℕ}
    {c c₁ c₂ : @PDA.conf (TotalState Q) T (TotalStackSymbol A) _ _ _ (totalizer A).toPDA}
    (h₁ : @PDA.ReachesIn (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA n c c₁)
    (h₂ : @PDA.ReachesIn (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA n c c₂) :
    c₁ = c₂ := by
  induction n generalizing c₁ c₂ with
  | zero =>
      have h₁eq := PDA.reachesIn_zero h₁
      have h₂eq := PDA.reachesIn_zero h₂
      exact h₁eq.symm.trans h₂eq
  | succ n ih =>
      obtain ⟨d₁, hd₁, hstep₁⟩ := PDA.reachesIn_iff_split_last.mpr h₁
      obtain ⟨d₂, hd₂, hstep₂⟩ := PDA.reachesIn_iff_split_last.mpr h₂
      have hd : d₁ = d₂ := ih hd₁ hd₂
      subst d₂
      exact totalizer_step_deterministic (A := A)
        (PDA.reaches₁_iff_reachesIn_one.mpr hstep₁)
        (PDA.reaches₁_iff_reachesIn_one.mpr hstep₂)

theorem totalizer_reachesIn_prefix_of_le
    {n m : ℕ}
    {c c₁ c₂ : @PDA.conf (TotalState Q) T (TotalStackSymbol A) _ _ _ (totalizer A).toPDA}
    (hle : n ≤ m)
    (h₁ : @PDA.ReachesIn (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA n c c₁)
    (h₂ : @PDA.ReachesIn (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA m c c₂) :
    @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA c₁ c₂ := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  subst m
  induction k generalizing c₂ with
  | zero =>
      have heq := totalizer_reachesIn_deterministic (A := A) h₁ (by simpa using h₂)
      subst c₂
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      obtain ⟨d, hd, hstep⟩ :=
        PDA.reachesIn_iff_split_last.mpr (by
          simpa [Nat.add_assoc] using h₂)
      exact Relation.ReflTransGen.tail (ih (Nat.le_add_right n k) hd)
        (PDA.reaches₁_iff_reachesIn_one.mpr hstep)

theorem totalizer_sim_step_to_original {q p : Q} {b b' : Bool}
    {input input' : List T} {stack stack' : List (TotalStackSymbol A)}
    (hstep : @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, input, stack⟩
      ⟨TotalState.sim p b', input', stack'⟩) :
    @PDA.Reaches₁ Q T S _ _ _ M.toPDA
      ⟨q, input, eraseAnnotatedStack (A := A) stack⟩
      ⟨p, input', eraseAnnotatedStack (A := A) stack'⟩ := by
  cases input with
  | nil =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons top rest =>
          cases top with
          | none =>
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
          | some payload =>
              rcases payload with ⟨Z, below⟩
              cases hε : M.epsilon_transition q Z with
              | none =>
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε] at hstep
              | some out =>
                  rcases out with ⟨r, β⟩
                  by_cases hstops :
                      stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                  · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                    rcases hstep with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
                    have hOrig :
                        ⟨p, [], β ++ eraseAnnotatedStack (A := A) rest⟩ ∈
                        PDA.step (pda := M.toPDA)
                          ⟨q, [], Z :: eraseAnnotatedStack (A := A) rest⟩ :=
                      ⟨p, β, by simp [DPDA.toPDA, hε], rfl⟩
                    simpa [PDA.Reaches₁, eraseAnnotatedStack, erase_annotatedReplacement_append] using hOrig
                  · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
  | cons a inputTail =>
      cases stack with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons top rest =>
          cases top with
          | none =>
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
          | some payload =>
              rcases payload with ⟨Z, below⟩
              cases hε : M.epsilon_transition q Z with
              | none =>
                  cases hδ : M.transition q a Z with
                  | none =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hδ] at hstep
                  | some out =>
                      rcases out with ⟨r, β⟩
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, simState, hε, hδ] at hstep
                      rcases hstep with ⟨⟨rfl, _⟩, ⟨rfl, rfl⟩⟩
                      have hOrig :
                          ⟨p, input', β ++ eraseAnnotatedStack (A := A) rest⟩ ∈
                          PDA.step (pda := M.toPDA)
                            ⟨q, a :: input', Z :: eraseAnnotatedStack (A := A) rest⟩ :=
                        Set.mem_union_left _
                          ⟨p, β, by simp [DPDA.toPDA, hδ], rfl⟩
                      simpa [PDA.Reaches₁, eraseAnnotatedStack, erase_annotatedReplacement_append] using hOrig
              | some out =>
                  rcases out with ⟨r, β⟩
                  by_cases hstops :
                      stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                  · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                    rcases hstep with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
                    have hOrig :
                        ⟨p, a :: inputTail, β ++ eraseAnnotatedStack (A := A) rest⟩ ∈
                        PDA.step (pda := M.toPDA)
                          ⟨q, a :: inputTail, Z :: eraseAnnotatedStack (A := A) rest⟩ :=
                      Set.mem_union_right _
                        ⟨p, β, by simp [DPDA.toPDA, hε], rfl⟩
                    simpa [PDA.Reaches₁, eraseAnnotatedStack, erase_annotatedReplacement_append] using hOrig
                  · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep

theorem totalizer_no_step_to_init
    {c : @PDA.conf (TotalState Q) T (TotalStackSymbol A) _ _ _ (totalizer A).toPDA}
    {input : List T} {stack : List (TotalStackSymbol A)}
    (hstep : @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA c ⟨TotalState.init, input, stack⟩) :
    False := by
  rcases c with ⟨st, input₀, stack₀⟩
  cases input₀ with
  | nil =>
      cases stack₀ with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons top rest =>
          cases st with
          | init =>
              cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, simState] at hstep
          | drain =>
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
          | sim q b =>
              cases top with
              | none =>
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
              | some payload =>
                  rcases payload with ⟨Z, below⟩
                  cases hε : M.epsilon_transition q Z with
                  | none =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε] at hstep
                  | some out =>
                      by_cases hstops :
                          stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                      · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                      · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
  | cons a inputTail =>
      cases stack₀ with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep
      | cons top rest =>
          cases st with
          | init =>
              cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, simState] at hstep
          | drain =>
              cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
          | sim q b =>
              cases top with
              | none =>
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
              | some payload =>
                  rcases payload with ⟨Z, below⟩
                  cases hε : M.epsilon_transition q Z with
                  | none =>
                      cases hδ : M.transition q a Z with
                      | none =>
                          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hδ] at hstep
                      | some out =>
                          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, simState, hε, hδ] at hstep
                  | some out =>
                      by_cases hstops :
                          stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                      · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                      · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep

theorem totalizer_reaches_original_rep (w : List T)
    {c : @PDA.conf (TotalState Q) T (TotalStackSymbol A) _ _ _ (totalizer A).toPDA}
    (hreach : @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.init, w, [none]⟩ c) :
    (c.state = TotalState.init → c.input = w ∧ c.stack = [none]) ∧
      (∀ q b, c.state = TotalState.sim q b →
        @PDA.Reaches Q T S _ _ _ M.toPDA
          ⟨M.initial_state, w, [M.start_symbol]⟩
          ⟨q, c.input, eraseAnnotatedStack (A := A) c.stack⟩) := by
  induction hreach with
  | refl =>
      constructor
      · intro _; simp
      · intro q b hsim
        simp at hsim
  | @tail cMid cEnd hprefix hstep ih =>
      constructor
      · intro hinit
        rcases cEnd with ⟨stEnd, inputEnd, stackEnd⟩
        simp at hinit
        subst stEnd
        exact (totalizer_no_step_to_init (A := A) hstep).elim
      · intro q b hsim
        rcases cEnd with ⟨stEnd, inputEnd, stackEnd⟩
        simp at hsim
        subst stEnd
        rcases cMid with ⟨stMid, inputMid, stackMid⟩
        cases stMid with
        | init =>
            have hmid := ih.1 rfl
            have hinputMid : inputMid = w := hmid.1
            have hstackMid : stackMid = [none] := hmid.2
            subst inputMid
            subst stackMid
            cases w with
            | nil =>
                simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, simState] at hstep
                rcases hstep with ⟨⟨rfl, _⟩, ⟨rfl, rfl⟩⟩
                exact Relation.ReflTransGen.refl
            | cons a wtail =>
                simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, simState] at hstep
                rcases hstep with ⟨⟨rfl, _⟩, ⟨rfl, rfl⟩⟩
                exact Relation.ReflTransGen.refl
        | drain =>
            cases inputMid with
            | nil =>
                cases stackMid with
                | nil => simp [PDA.Reaches₁, PDA.step] at hstep
                | cons top rest =>
                    simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
            | cons a inputTail =>
                cases stackMid with
                | nil => simp [PDA.Reaches₁, PDA.step] at hstep
                | cons top rest =>
                    cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
        | sim r bmid =>
            have hOrigPrefix := ih.2 r bmid rfl
            exact Relation.ReflTransGen.tail hOrigPrefix
              (totalizer_sim_step_to_original (A := A) hstep)

theorem totalizer_reaches_sim_to_original (w : List T) {q : Q} {b : Bool}
    {input : List T} {stack : List (TotalStackSymbol A)}
    (hreach : @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.init, w, [none]⟩
      ⟨TotalState.sim q b, input, stack⟩) :
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩
      ⟨q, input, eraseAnnotatedStack (A := A) stack⟩ :=
  (totalizer_reaches_original_rep (A := A) w hreach).2 q b rfl

theorem totalizer_reaches_stack_invariants (w : List T)
    {c : @PDA.conf (TotalState Q) T (TotalStackSymbol A) _ _ _ (totalizer A).toPDA}
    (hreach : @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.init, w, [none]⟩ c) :
    StackWellAnnotated (A := A) c.stack ∧ StackHasBottom (A := A) c.stack := by
  induction hreach with
  | refl =>
      exact ⟨stackWellAnnotated_none (A := A), stackHasBottom_none (A := A)⟩
  | @tail cMid cEnd hprefix hstep ih =>
      rcases cMid with ⟨stMid, inputMid, stackMid⟩
      rcases cEnd with ⟨stEnd, inputEnd, stackEnd⟩
      dsimp at ih ⊢
      cases inputMid with
      | nil =>
          cases stackMid with
          | nil => simp [PDA.Reaches₁, PDA.step] at hstep
          | cons top rest =>
              cases stMid with
              | init =>
                  cases top with
                  | none =>
                      simp [StackWellAnnotated] at ih
                      have hrest : rest = [] := ih.1
                      subst rest
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                      rcases hstep with ⟨rfl, rfl, rfl⟩
                      exact
                        ⟨stackWellAnnotated_initialReplacement A,
                          stackHasBottom_initialReplacement A⟩
                  | some payload =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
              | drain =>
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
              | sim q b =>
                  cases top with
                  | none =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                  | some payload =>
                      rcases payload with ⟨Z, below⟩
                      cases hε : M.epsilon_transition q Z with
                      | none =>
                          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε] at hstep
                      | some out =>
                          rcases out with ⟨p, β⟩
                          by_cases hstops :
                              stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                          · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                            rcases hstep with ⟨rfl, rfl, rfl⟩
                            exact
                              ⟨(replacement_preserves_annotations (A := A) β ih.1).1,
                                replacement_preserves_bottom (A := A) β ih.2⟩
                          · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
      | cons a inputTail =>
          cases stackMid with
          | nil => simp [PDA.Reaches₁, PDA.step] at hstep
          | cons top rest =>
              cases stMid with
              | init =>
                  cases top with
                  | none =>
                      simp [StackWellAnnotated] at ih
                      have hrest : rest = [] := ih.1
                      subst rest
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                      rcases hstep with ⟨rfl, rfl, rfl⟩
                      exact
                        ⟨stackWellAnnotated_initialReplacement A,
                          stackHasBottom_initialReplacement A⟩
                  | some payload =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
              | drain =>
                  cases top with
                  | none =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                      rcases hstep with ⟨rfl, rfl, rfl⟩
                      exact ih
                  | some payload =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                      rcases hstep with ⟨rfl, rfl, rfl⟩
                      exact ih
              | sim q b =>
                  cases top with
                  | none =>
                      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                      rcases hstep with ⟨rfl, rfl, rfl⟩
                      exact ih
                  | some payload =>
                      rcases payload with ⟨Z, below⟩
                      cases hε : M.epsilon_transition q Z with
                      | none =>
                          cases hδ : M.transition q a Z with
                          | none =>
                              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hδ] at hstep
                              rcases hstep with ⟨rfl, rfl, rfl⟩
                              exact ih
                          | some out =>
                              rcases out with ⟨p, β⟩
                              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hδ] at hstep
                              rcases hstep with ⟨rfl, rfl, rfl⟩
                              exact
                                ⟨(replacement_preserves_annotations (A := A) β ih.1).1,
                                  replacement_preserves_bottom (A := A) β ih.2⟩
                      | some out =>
                          rcases out with ⟨p, β⟩
                          by_cases hstops :
                              stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                          · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                            rcases hstep with ⟨rfl, rfl, rfl⟩
                            exact
                              ⟨(replacement_preserves_annotations (A := A) β ih.1).1,
                                replacement_preserves_bottom (A := A) β ih.2⟩
                          · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                            rcases hstep with ⟨rfl, rfl, rfl⟩
                            exact ih

theorem totalizer_empty_final_to_original_accept (w : List T)
    {c : @PDA.conf (TotalState Q) T (TotalStackSymbol A) _ _ _ (totalizer A).toPDA}
    (hreach : @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.init, w, [none]⟩ c)
    (hinput : c.input = [])
    (hfinal : c.state ∈ (totalizer A).final_states) :
    w ∈ M.acceptsByFinalState := by
  induction hreach with
  | refl =>
      simp at hinput
      subst w
      have hbit : initialAcceptBit A = true := (init_mem_final_iff (A := A)).1 hfinal
      have haccept : acceptsFromSummary A M.initial_state (initialSummary A) :=
        (acceptBit_eq_true_iff (A := A) M.initial_state (initialSummary A)).1 hbit
      obtain ⟨qf, γf, hε, hqf⟩ :=
        (acceptsFromSummary_correct A (initialSummaryRepresents A) M.initial_state).1 haccept
      exact ⟨qf, hqf, γf, epsilonReaches_toPDA (w := ([] : List T)) hε⟩
  | @tail cMid cEnd hprefix hstep ih =>
      rcases cMid with ⟨stMid, inputMid, stackMid⟩
      rcases cEnd with ⟨stEnd, inputEnd, stackEnd⟩
      dsimp at hinput hfinal
      subst inputEnd
      by_cases hmid_empty : inputMid = []
      · subst inputMid
        have hmid_final :
            stMid ∈ (totalizer A).final_states := by
          exact (totalizer_empty_step_preserves_final (A := A) hstep).2 hfinal
        exact ih rfl hmid_final
      · cases inputMid with
        | nil => exact (hmid_empty rfl).elim
        | cons a inputTail =>
            cases stackMid with
            | nil => simp [PDA.Reaches₁, PDA.step] at hstep
            | cons top rest =>
                cases stMid with
                | init =>
                    cases top with
                    | none =>
                        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, simState] at hstep
                    | some payload =>
                        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                | drain =>
                    cases top <;> simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                    · rcases hstep with ⟨rfl, rfl, rfl⟩
                      exact (drain_not_mem_final (A := A) hfinal).elim
                    · rcases hstep with ⟨rfl, rfl, rfl⟩
                      exact (drain_not_mem_final (A := A) hfinal).elim
                | sim q b =>
                    cases top with
                    | none =>
                        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer] at hstep
                        rcases hstep with ⟨rfl, rfl, rfl⟩
                        exact (drain_not_mem_final (A := A) hfinal).elim
                    | some payload =>
                        rcases payload with ⟨Z, below⟩
                        cases hε : M.epsilon_transition q Z with
                        | none =>
                            cases hδ : M.transition q a Z with
                            | none =>
                                simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hδ] at hstep
                                rcases hstep with ⟨rfl, rfl, rfl⟩
                                exact (drain_not_mem_final (A := A) hfinal).elim
                            | some out =>
                                rcases out with ⟨p, β⟩
                                have hstepOrig := hstep
                                simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, simState, hε, hδ] at hstep
                                rcases hstep with ⟨rfl, htail, rfl⟩
                                subst inputTail
                                have hreachEnd :
                                    @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
                                      (totalizer A).toPDA
                                      ⟨TotalState.init, w, [none]⟩
                                      ⟨simState A p (below.above A β), [], annotatedReplacement A below β ++ rest⟩ := by
                                  exact Relation.ReflTransGen.tail hprefix hstepOrig
                                have hOrigPrefix :
                                    @PDA.Reaches Q T S _ _ _ M.toPDA
                                      ⟨M.initial_state, w, [M.start_symbol]⟩
                                      ⟨p, [], eraseAnnotatedStack (A := A)
                                        (annotatedReplacement A below β ++ rest)⟩ :=
                                  totalizer_reaches_sim_to_original (A := A) w hreachEnd
                                have hmidInv :=
                                  totalizer_reaches_stack_invariants (A := A) w hprefix
                                have hsummary :
                                    SummaryRepresents A (below.above A β)
                                      (eraseAnnotatedStack (A := A)
                                        (annotatedReplacement A below β ++ rest)) :=
                                  (replacement_preserves_annotations (A := A) β hmidInv.1).2
                                have hsem :=
                                  (simState_mem_final_iff_semantic (A := A)
                                    (q := p) (summary := below.above A β) hsummary).1 hfinal
                                obtain ⟨qf, γf, hεreach, hqf⟩ := hsem
                                exact ⟨qf, hqf, γf,
                                  Relation.ReflTransGen.trans hOrigPrefix
                                    (epsilonReaches_toPDA (w := ([] : List T)) hεreach)⟩
                        | some out =>
                            rcases out with ⟨p, β⟩
                            by_cases hstops :
                                stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))
                            · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                            · simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, totalizer, hε, hstops] at hstep
                              rcases hstep with ⟨rfl, rfl, rfl⟩
                              exact (drain_not_mem_final (A := A) hfinal).elim

theorem totalizer_acceptsByFinalState_subset_original :
    (totalizer A).acceptsByFinalState ≤ M.acceptsByFinalState := by
  intro w hw
  unfold DPDA.acceptsByFinalState PDA.acceptsByFinalState at hw ⊢
  obtain ⟨st, hfinal, stack, hreach⟩ := hw
  exact totalizer_empty_final_to_original_accept (A := A) w hreach rfl hfinal

theorem totalizer_initial_step (w : List T) :
    @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.init, w, [none]⟩
      ⟨simState A M.initial_state ((AnalysisSummary.id A).above A [M.start_symbol]),
        w, initialReplacement A⟩ := by
  cases w with
  | nil =>
      change
        ⟨simState A M.initial_state ((AnalysisSummary.id A).above A [M.start_symbol]),
          [], initialReplacement A⟩ ∈
          PDA.step (pda := (totalizer A).toPDA) ⟨TotalState.init, [], [none]⟩
      exact
        ⟨simState A M.initial_state ((AnalysisSummary.id A).above A [M.start_symbol]),
          initialReplacement A, by simp [DPDA.toPDA, totalizer], rfl⟩
  | cons a w =>
      change
        ⟨simState A M.initial_state ((AnalysisSummary.id A).above A [M.start_symbol]),
          a :: w, initialReplacement A⟩ ∈
          PDA.step (pda := (totalizer A).toPDA) ⟨TotalState.init, a :: w, [none]⟩
      exact Set.mem_union_right _
        ⟨simState A M.initial_state ((AnalysisSummary.id A).above A [M.start_symbol]),
          initialReplacement A, by simp [DPDA.toPDA, totalizer], rfl⟩

theorem totalizer_initial_reaches (w : List T) :
    @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.init, w, [none]⟩
      ⟨simState A M.initial_state ((AnalysisSummary.id A).above A [M.start_symbol]),
        w, initialReplacement A⟩ :=
  Relation.ReflTransGen.single (totalizer_initial_step A w)

theorem totalizer_accepts_nil_of_original_accept
    (h : ([] : List T) ∈ M.acceptsByFinalState) :
    ([] : List T) ∈ (totalizer A).acceptsByFinalState := by
  unfold DPDA.acceptsByFinalState PDA.acceptsByFinalState at h ⊢
  obtain ⟨qf, hqf, γf, hreach⟩ := h
  have hε :
      M.EpsilonReaches (M.initial_state, [M.start_symbol]) (qf, γf) :=
    epsilonReaches_of_toPDA_empty_reaches hreach
  have haccept : acceptsFromSummary A M.initial_state (initialSummary A) :=
    (acceptsFromSummary_correct A (initialSummaryRepresents A) M.initial_state).2
      ⟨qf, γf, hε, hqf⟩
  have hfinal :
      simState A M.initial_state (initialSummary A) ∈ (totalizer A).final_states :=
    (simState_mem_final_iff (A := A) M.initial_state (initialSummary A)).2 haccept
  refine ⟨simState A M.initial_state (initialSummary A), hfinal, initialReplacement A, ?_⟩
  simpa [initialSummary] using totalizer_initial_reaches A ([] : List T)

theorem totalizer_input_step_of_transition {q p : Q} {b : Bool} {a : T} {Z : S}
    {below : AnalysisSummary A} {β : List S} {rest : List (TotalStackSymbol A)}
    {w : List T}
    (hε : M.epsilon_transition q Z = none)
    (hδ : M.transition q a Z = some (p, β)) :
    @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
      ⟨simState A p (below.above A β), w, annotatedReplacement A below β ++ rest⟩ := by
  change
    ⟨simState A p (below.above A β), w, annotatedReplacement A below β ++ rest⟩ ∈
      PDA.step (pda := (totalizer A).toPDA)
        ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
  exact Set.mem_union_left _
    ⟨simState A p (below.above A β), annotatedReplacement A below β,
      by simp [DPDA.toPDA, totalizer, simState, hε, hδ], rfl⟩

theorem totalizer_input_step_preserves_annotations {q p : Q} {b : Bool} {a : T} {Z : S}
    {below : AnalysisSummary A} {β : List S} {rest : List (TotalStackSymbol A)}
    {w : List T}
    (hε : M.epsilon_transition q Z = none)
    (hδ : M.transition q a Z = some (p, β))
    (hstack : StackWellAnnotated (A := A) (some (Z, below) :: rest))
    (hbottom : StackHasBottom (A := A) (some (Z, below) :: rest)) :
    ∃ stack' summary',
      @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
        ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
        ⟨simState A p summary', w, stack'⟩ ∧
      StackWellAnnotated (A := A) stack' ∧
      StackHasBottom (A := A) stack' ∧
      SummaryRepresents A summary' (eraseAnnotatedStack (A := A) stack') ∧
      eraseAnnotatedStack (A := A) stack' = β ++ eraseAnnotatedStack (A := A) rest := by
  refine ⟨annotatedReplacement A below β ++ rest, below.above A β, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using
      totalizer_input_step_of_transition (A := A) (w := w) hε hδ
  · exact (replacement_preserves_annotations (A := A) β hstack).1
  · exact replacement_preserves_bottom (A := A) β hbottom
  · exact (replacement_preserves_annotations (A := A) β hstack).2
  · exact erase_annotatedReplacement_append A below β rest

theorem totalizer_epsilon_step_of_transition {q p : Q} {b : Bool} {Z : S}
    {below : AnalysisSummary A} {β : List S} {rest : List (TotalStackSymbol A)}
    {w : List T}
    (hε : M.epsilon_transition q Z = some (p, β))
    (hstop : stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))) :
    @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, w, some (Z, below) :: rest⟩
      ⟨TotalState.sim p b, w, annotatedReplacement A below β ++ rest⟩ := by
  cases w with
  | nil =>
      change
        ⟨TotalState.sim p b, [], annotatedReplacement A below β ++ rest⟩ ∈
          PDA.step (pda := (totalizer A).toPDA)
            ⟨TotalState.sim q b, [], some (Z, below) :: rest⟩
      exact
        ⟨TotalState.sim p b, annotatedReplacement A below β,
          by simp [DPDA.toPDA, totalizer, simState, hε, hstop], rfl⟩
  | cons a w =>
      change
        ⟨TotalState.sim p b, a :: w, annotatedReplacement A below β ++ rest⟩ ∈
          PDA.step (pda := (totalizer A).toPDA)
            ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
      exact Set.mem_union_right _
        ⟨TotalState.sim p b, annotatedReplacement A below β,
          by simp [DPDA.toPDA, totalizer, simState, hε, hstop], rfl⟩

theorem totalizer_epsilon_step_of_epsilonStep {q p : Q} {b : Bool} {γ' : List S}
    {top : TotalStackSymbol A} {rest : List (TotalStackSymbol A)} {w : List T}
    (hstack : StackWellAnnotated (A := A) (top :: rest))
    (hbottom : StackHasBottom (A := A) (top :: rest))
    (hstep : M.EpsilonStep
      (q, eraseAnnotatedStack (A := A) (top :: rest)) (p, γ'))
    (hstop : ∃ c', M.EpsilonStopsAt
      (q, eraseAnnotatedStack (A := A) (top :: rest)) c') :
    ∃ stack' summary',
      @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
      ⟨TotalState.sim q b, w, top :: rest⟩
      ⟨TotalState.sim p b, w, stack'⟩ ∧
      StackWellAnnotated (A := A) stack' ∧
      StackHasBottom (A := A) stack' ∧
      SummaryRepresents A summary' γ' ∧
      eraseAnnotatedStack (A := A) stack' = γ' := by
  cases top with
  | none =>
      simp [StackWellAnnotated] at hstack
      subst rest
      simp [EpsilonStep, eraseAnnotatedStack] at hstep
  | some payload =>
      rcases payload with ⟨Z, below⟩
      simp [EpsilonStep, eraseAnnotatedStack] at hstep
      obtain ⟨β, hβ, rfl⟩ := hstep
      have htopStops : topStops A q (some (Z, below)) :=
        (topStops_semantic_of_stackWellAnnotated (A := A) hstack q).2 hstop
      have hstopsFromSummary :
          stopsFromSummary A q (fullSummaryOfTop A (some (Z, below))) :=
        (topStops_eq_stopsFromSummary (A := A) q (some (Z, below))).1 htopStops
      refine
        ⟨annotatedReplacement A below β ++ rest, below.above A β, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using
          totalizer_epsilon_step_of_transition (A := A) (w := w) hβ hstopsFromSummary
      · exact (replacement_preserves_annotations (A := A) β hstack).1
      · exact replacement_preserves_bottom (A := A) β hbottom
      · simpa [erase_annotatedReplacement_append] using
          (replacement_preserves_annotations (A := A) β hstack).2
      · exact erase_annotatedReplacement_append A below β rest

theorem totalizer_epsilonReaches_of_epsilonReaches {q : Q} {b : Bool} {c' : EpsilonConf Q S}
    {top : TotalStackSymbol A} {rest : List (TotalStackSymbol A)} {w : List T}
    (hstack : StackWellAnnotated (A := A) (top :: rest))
    (hbottom : StackHasBottom (A := A) (top :: rest))
    (hreach : M.EpsilonReaches
      (q, eraseAnnotatedStack (A := A) (top :: rest)) c')
    (hstop : ∃ cfinal,
      M.EpsilonStopsAt (q, eraseAnnotatedStack (A := A) (top :: rest)) cfinal) :
    ∃ stack' summary',
      @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
      ⟨TotalState.sim q b, w, top :: rest⟩
      ⟨TotalState.sim c'.1 b, w, stack'⟩ ∧
      StackWellAnnotated (A := A) stack' ∧
      StackHasBottom (A := A) stack' ∧
      SummaryRepresents A summary' c'.2 ∧
      eraseAnnotatedStack (A := A) stack' = c'.2 := by
  induction hreach with
  | refl =>
      refine
        ⟨top :: rest, fullSummaryOfTop A top, Relation.ReflTransGen.refl, hstack,
          hbottom, stackWellAnnotated_fullSummaryOfTop (A := A) hstack, rfl⟩
  | @tail mid nxt hprev hstep ih =>
      obtain ⟨stackMid, summaryMid, hreachT, hstackMid, hbottomMid, hsummaryMid, heraseMid⟩ := ih
      rcases mid with ⟨r, γmid⟩
      cases stackMid with
      | nil =>
          simp [eraseAnnotatedStack] at heraseMid
          subst γmid
          simp [EpsilonStep] at hstep
      | cons topMid restMid =>
          have hsummaryTop :
              SummaryRepresents A (fullSummaryOfTop A topMid)
                (eraseAnnotatedStack (A := A) (topMid :: restMid)) :=
            stackWellAnnotated_fullSummaryOfTop (A := A) hstackMid
          have hsummaryMidErase :
              SummaryRepresents A summaryMid
                (eraseAnnotatedStack (A := A) (topMid :: restMid)) := by
            simpa [heraseMid] using hsummaryMid
          have hsummaryEq : summaryMid = fullSummaryOfTop A topMid :=
            SummaryRepresents.eq (A := A) hsummaryMidErase hsummaryTop
          subst summaryMid
          obtain ⟨cfinal, hstops⟩ := hstop
          have hstopMid : ∃ cfinal,
              M.EpsilonStopsAt
                (r, eraseAnnotatedStack (A := A) (topMid :: restMid)) cfinal := by
            refine ⟨cfinal, ?_⟩
            simpa [heraseMid] using epsilonReaches_suffix_of_stops hprev hstops
          have hstepErase :
              M.EpsilonStep
                (r, eraseAnnotatedStack (A := A) (topMid :: restMid)) nxt := by
            simpa [heraseMid] using hstep
          obtain ⟨stackNext, summaryNext, hstepT, hstackNext, hbottomNext, hsummaryNext, heraseNext⟩ :=
            totalizer_epsilon_step_of_epsilonStep (A := A) (w := w)
              hstackMid hbottomMid hstepErase hstopMid
          refine ⟨stackNext, summaryNext, ?_, hstackNext, hbottomNext, hsummaryNext, heraseNext⟩
          exact Relation.ReflTransGen.trans hreachT (Relation.ReflTransGen.single hstepT)

theorem totalizer_epsilonStopsAt_of_epsilonStopsAt {q : Q} {b : Bool} {cstable : EpsilonConf Q S}
    {top : TotalStackSymbol A} {rest : List (TotalStackSymbol A)} {w : List T}
    (hstack : StackWellAnnotated (A := A) (top :: rest))
    (hbottom : StackHasBottom (A := A) (top :: rest))
    (hstops : M.EpsilonStopsAt
      (q, eraseAnnotatedStack (A := A) (top :: rest)) cstable) :
    ∃ stack' summary',
      @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
      ⟨TotalState.sim q b, w, top :: rest⟩
      ⟨TotalState.sim cstable.1 b, w, stack'⟩ ∧
      StackWellAnnotated (A := A) stack' ∧
      StackHasBottom (A := A) stack' ∧
      SummaryRepresents A summary' cstable.2 ∧
      eraseAnnotatedStack (A := A) stack' = cstable.2 ∧
      M.EpsilonStable cstable := by
  obtain ⟨hreach, hstable⟩ := hstops
  obtain ⟨stack', summary', hreachT, hstack', hbottom', hsummary', herase'⟩ :=
    totalizer_epsilonReaches_of_epsilonReaches (A := A) (w := w)
      hstack hbottom hreach ⟨cstable, hreach, hstable⟩
  exact ⟨stack', summary', hreachT, hstack', hbottom', hsummary', herase', hstable⟩

theorem totalizer_input_step_to_drain_of_no_transition {q : Q} {b : Bool} {a : T} {Z : S}
    {below : AnalysisSummary A} {rest : List (TotalStackSymbol A)} {w : List T}
    (hε : M.epsilon_transition q Z = none)
    (hδ : M.transition q a Z = none) :
    @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
      ⟨TotalState.drain, w, some (Z, below) :: rest⟩ := by
  change
    ⟨TotalState.drain, w, some (Z, below) :: rest⟩ ∈
      PDA.step (pda := (totalizer A).toPDA)
        ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
  exact Set.mem_union_left _
    ⟨TotalState.drain, [some (Z, below)],
      by simp [DPDA.toPDA, totalizer, simState, hε, hδ], rfl⟩

theorem totalizer_input_step_to_drain_of_unstopping_epsilon {q p : Q} {b : Bool} {a : T} {Z : S}
    {below : AnalysisSummary A} {β : List S} {rest : List (TotalStackSymbol A)}
    {w : List T}
    (hε : M.epsilon_transition q Z = some (p, β))
    (hstop : ¬ stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))) :
    @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
      ⟨TotalState.drain, w, some (Z, below) :: rest⟩ := by
  change
    ⟨TotalState.drain, w, some (Z, below) :: rest⟩ ∈
      PDA.step (pda := (totalizer A).toPDA)
        ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
  exact Set.mem_union_left _
    ⟨TotalState.drain, [some (Z, below)],
      by simp [DPDA.toPDA, totalizer, simState, hε, hstop], rfl⟩

theorem totalizer_input_step_to_drain_of_empty_stack {q : Q} {b : Bool} {a : T}
    {rest : List (TotalStackSymbol A)} {w : List T} :
    @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, a :: w, none :: rest⟩
      ⟨TotalState.drain, w, none :: rest⟩ := by
  change
    ⟨TotalState.drain, w, none :: rest⟩ ∈
      PDA.step (pda := (totalizer A).toPDA)
        ⟨TotalState.sim q b, a :: w, none :: rest⟩
  exact Set.mem_union_left _
    ⟨TotalState.drain, [none], by simp [DPDA.toPDA, totalizer, simState], rfl⟩

theorem totalizer_drain_input_step (a : T) (w : List T)
    (top : TotalStackSymbol A) (rest : List (TotalStackSymbol A)) :
    @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.drain, a :: w, top :: rest⟩
      ⟨TotalState.drain, w, top :: rest⟩ := by
  change
    ⟨TotalState.drain, w, top :: rest⟩ ∈
      PDA.step (pda := (totalizer A).toPDA) ⟨TotalState.drain, a :: w, top :: rest⟩
  exact Set.mem_union_left _
    ⟨TotalState.drain, [top], by simp [DPDA.toPDA, totalizer], rfl⟩

theorem totalizer_drain_reaches_empty_input (w : List T)
    (top : TotalStackSymbol A) (rest : List (TotalStackSymbol A)) :
    @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.drain, w, top :: rest⟩
      ⟨TotalState.drain, [], top :: rest⟩ := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons a w ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (totalizer_drain_input_step A a w top rest)) ih

theorem totalizer_no_transition_reaches_empty_drain {q : Q} {b : Bool} {a : T} {Z : S}
    {below : AnalysisSummary A} {rest : List (TotalStackSymbol A)} {w : List T}
    (hε : M.epsilon_transition q Z = none)
    (hδ : M.transition q a Z = none) :
    @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
      ⟨TotalState.drain, [], some (Z, below) :: rest⟩ :=
  Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (totalizer_input_step_to_drain_of_no_transition (A := A) (w := w) hε hδ))
    (totalizer_drain_reaches_empty_input A w (some (Z, below)) rest)

theorem totalizer_stable_input_step_preserves_annotations {q p : Q} {b : Bool} {a : T} {Z : S}
    {below : AnalysisSummary A} {β : List S} {rest : List (TotalStackSymbol A)}
    {w : List T}
    (hstack : StackWellAnnotated (A := A) (some (Z, below) :: rest))
    (hbottom : StackHasBottom (A := A) (some (Z, below) :: rest))
    (hstable : M.EpsilonStable
      (q, eraseAnnotatedStack (A := A) (some (Z, below) :: rest)))
    (hδ : M.transition q a Z = some (p, β)) :
    ∃ stack' summary',
      @PDA.Reaches₁ (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
        ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
        ⟨simState A p summary', w, stack'⟩ ∧
      StackWellAnnotated (A := A) stack' ∧
      StackHasBottom (A := A) stack' ∧
      SummaryRepresents A summary' (eraseAnnotatedStack (A := A) stack') ∧
      eraseAnnotatedStack (A := A) stack' = β ++ eraseAnnotatedStack (A := A) rest := by
  have hε : M.epsilon_transition q Z = none := by
    simpa [EpsilonStable, eraseAnnotatedStack] using hstable
  exact totalizer_input_step_preserves_annotations (A := A) (w := w) hε hδ hstack hbottom

theorem totalizer_stable_no_transition_reaches_empty_drain {q : Q} {b : Bool} {a : T} {Z : S}
    {below : AnalysisSummary A} {rest : List (TotalStackSymbol A)} {w : List T}
    (hstable : M.EpsilonStable
      (q, eraseAnnotatedStack (A := A) (some (Z, below) :: rest)))
    (hδ : M.transition q a Z = none) :
    @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
      ⟨TotalState.drain, [], some (Z, below) :: rest⟩ := by
  have hε : M.epsilon_transition q Z = none := by
    simpa [EpsilonStable, eraseAnnotatedStack] using hstable
  simpa using
    totalizer_no_transition_reaches_empty_drain (A := A) (w := w) hε hδ

theorem totalizer_unstopping_epsilon_reaches_empty_drain {q p : Q} {b : Bool} {a : T} {Z : S}
    {below : AnalysisSummary A} {β : List S} {rest : List (TotalStackSymbol A)}
    {w : List T}
    (hε : M.epsilon_transition q Z = some (p, β))
    (hstop : ¬ stopsFromSummary A q (fullSummaryOfTop A (some (Z, below)))) :
    @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, a :: w, some (Z, below) :: rest⟩
      ⟨TotalState.drain, [], some (Z, below) :: rest⟩ :=
  Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (totalizer_input_step_to_drain_of_unstopping_epsilon (A := A) (w := w) hε hstop))
    (totalizer_drain_reaches_empty_input A w (some (Z, below)) rest)

theorem totalizer_empty_original_stack_reaches_empty_drain {q : Q} {b : Bool} {a : T}
    {rest : List (TotalStackSymbol A)} {w : List T} :
    @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨TotalState.sim q b, a :: w, none :: rest⟩
      ⟨TotalState.drain, [], none :: rest⟩ :=
  Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (totalizer_input_step_to_drain_of_empty_stack (A := A) (w := w)))
    (totalizer_drain_reaches_empty_input A w none rest)

theorem totalizer_reaches_empty_from_sim (q : Q) (b : Bool) (w : List T)
    (top : TotalStackSymbol A) (rest : List (TotalStackSymbol A))
    (hstack : StackWellAnnotated (A := A) (top :: rest))
    (hbottom : StackHasBottom (A := A) (top :: rest)) :
    ∃ st stack,
      @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
        ⟨TotalState.sim q b, w, top :: rest⟩
        ⟨st, [], stack⟩ := by
  induction w generalizing q b top rest with
  | nil =>
      exact ⟨TotalState.sim q b, top :: rest, Relation.ReflTransGen.refl⟩
  | cons a w ih =>
      cases top with
      | none =>
          exact
            ⟨TotalState.drain, none :: rest,
              totalizer_empty_original_stack_reaches_empty_drain (A := A)
                (q := q) (b := b) (a := a) (w := w) (rest := rest)⟩
      | some payload =>
          rcases payload with ⟨Z, below⟩
          by_cases hstops : ∃ cstable,
              M.EpsilonStopsAt
                (q, eraseAnnotatedStack (A := A) (some (Z, below) :: rest)) cstable
          · obtain ⟨⟨qstable, γstable⟩, hstopAt⟩ := hstops
            obtain ⟨stackMid, summaryMid, hphase, hstackMid, hbottomMid,
              hsummaryMid, heraseMid, hstable⟩ :=
                totalizer_epsilonStopsAt_of_epsilonStopsAt (A := A) (b := b) (w := a :: w)
                  hstack hbottom hstopAt
            obtain ⟨topMid, restMid, hmid_eq⟩ :=
              stackHasBottom_nonempty (A := A) hbottomMid
            subst stackMid
            cases topMid with
            | none =>
                refine ⟨TotalState.drain, none :: restMid, ?_⟩
                exact Relation.ReflTransGen.trans hphase
                  (totalizer_empty_original_stack_reaches_empty_drain (A := A)
                    (q := qstable) (b := b) (a := a) (w := w) (rest := restMid))
            | some payloadMid =>
                rcases payloadMid with ⟨Zmid, belowMid⟩
                have hstableMid :
                    M.EpsilonStable
                      (qstable,
                        eraseAnnotatedStack (A := A) (some (Zmid, belowMid) :: restMid)) := by
                  simpa [heraseMid] using hstable
                cases hδ : M.transition qstable a Zmid with
                | none =>
                    refine ⟨TotalState.drain, some (Zmid, belowMid) :: restMid, ?_⟩
                    exact Relation.ReflTransGen.trans hphase
                      (totalizer_stable_no_transition_reaches_empty_drain (A := A)
                        (q := qstable) (b := b) (a := a) (Z := Zmid) (below := belowMid)
                        (rest := restMid) (w := w) hstableMid hδ)
                | some out =>
                    rcases out with ⟨p, β⟩
                    obtain ⟨stackNext, summaryNext, hinput, hstackNext, hbottomNext,
                      _hsummaryNext, _heraseNext⟩ :=
                        totalizer_stable_input_step_preserves_annotations (A := A)
                          (q := qstable) (p := p) (b := b) (a := a) (Z := Zmid)
                          (below := belowMid) (β := β) (rest := restMid) (w := w)
                          hstackMid hbottomMid hstableMid hδ
                    obtain ⟨topNext, restNext, hnext_eq⟩ :=
                      stackHasBottom_nonempty (A := A) hbottomNext
                    subst stackNext
                    obtain ⟨st, stackFinal, hrec⟩ :=
                      ih p (acceptBit A p summaryNext) topNext restNext hstackNext hbottomNext
                    refine ⟨st, stackFinal, ?_⟩
                    exact Relation.ReflTransGen.trans hphase
                      (Relation.ReflTransGen.trans
                        (Relation.ReflTransGen.single hinput)
                        (by simpa [simState] using hrec))
          · cases hε : M.epsilon_transition q Z with
            | none =>
                have hstable :
                    M.EpsilonStable
                      (q, eraseAnnotatedStack (A := A) (some (Z, below) :: rest)) := by
                  simp [EpsilonStable, eraseAnnotatedStack, hε]
                exact (hstops ⟨(q, eraseAnnotatedStack (A := A) (some (Z, below) :: rest)),
                  Relation.ReflTransGen.refl, hstable⟩).elim
            | some out =>
                rcases out with ⟨p, β⟩
                have hnotStopsFromSummary :
                    ¬ stopsFromSummary A q (fullSummaryOfTop A (some (Z, below))) := by
                  intro hs
                  have htop : topStops A q (some (Z, below)) :=
                    (topStops_eq_stopsFromSummary (A := A) q (some (Z, below))).2 hs
                  exact hstops ((topStops_semantic_of_stackWellAnnotated (A := A) hstack q).1 htop)
                exact
                  ⟨TotalState.drain, some (Z, below) :: rest,
                    totalizer_unstopping_epsilon_reaches_empty_drain (A := A)
                      (q := q) (p := p) (b := b) (a := a) (Z := Z) (below := below)
                      (β := β) (rest := rest) (w := w) hε hnotStopsFromSummary⟩

theorem totalizer_accepting_reaches_from_simState (q : Q) (w : List T)
    (top : TotalStackSymbol A) (rest : List (TotalStackSymbol A))
    (hstack : StackWellAnnotated (A := A) (top :: rest))
    (hbottom : StackHasBottom (A := A) (top :: rest))
    {qf : Q} {γf : List S}
    (hreach : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨q, w, eraseAnnotatedStack (A := A) (top :: rest)⟩ ⟨qf, [], γf⟩)
    (hqf : qf ∈ M.final_states) :
    ∃ st stack,
      @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
        ⟨simState A q (fullSummaryOfTop A top), w, top :: rest⟩
        ⟨st, [], stack⟩ ∧
      st ∈ (totalizer A).final_states := by
  induction w generalizing q top rest with
  | nil =>
      have hε :
          M.EpsilonReaches
            (q, eraseAnnotatedStack (A := A) (top :: rest)) (qf, γf) :=
        epsilonReaches_of_toPDA_empty_reaches hreach
      have hsummary :
          SummaryRepresents A (fullSummaryOfTop A top)
            (eraseAnnotatedStack (A := A) (top :: rest)) :=
        stackWellAnnotated_fullSummaryOfTop (A := A) hstack
      have hfinal :
          simState A q (fullSummaryOfTop A top) ∈ (totalizer A).final_states :=
        (simState_mem_final_iff_semantic (A := A)
          (q := q) (summary := fullSummaryOfTop A top) hsummary).2
          ⟨qf, γf, hε, hqf⟩
      exact
        ⟨simState A q (fullSummaryOfTop A top), top :: rest,
          Relation.ReflTransGen.refl, hfinal⟩
  | cons a w ih =>
      cases top with
      | none =>
          simp [StackWellAnnotated] at hstack
          subst rest
          have hreachEmpty :
              @PDA.Reaches Q T S _ _ _ M.toPDA
                ⟨q, a :: w, []⟩ ⟨qf, [], γf⟩ := by
            simpa [eraseAnnotatedStack] using hreach
          have hsameInput := (PDA.reaches_on_empty_stack (pda := M.toPDA) hreachEmpty).1
          cases hsameInput
      | some payload =>
          rcases payload with ⟨Z, below⟩
          obtain ⟨cstable, hstopAt⟩ :=
            DPDA.epsilonStopsAt_of_toPDA_reaches_nonempty (M := M) hreach
          obtain ⟨stackMid, summaryMid, hphase, hstackMid, hbottomMid,
            hsummaryMid, heraseMid, hstable⟩ :=
              totalizer_epsilonStopsAt_of_epsilonStopsAt (A := A)
                (q := q)
                (b := acceptBit A q (fullSummaryOfTop A (some (Z, below))))
                (top := some (Z, below)) (rest := rest) (w := a :: w)
                hstack hbottom hstopAt
          have hreachStable :
              @PDA.Reaches Q T S _ _ _ M.toPDA
                ⟨cstable.1, a :: w, cstable.2⟩ ⟨qf, [], γf⟩ :=
            DPDA.toPDA_reaches_suffix_of_epsilonReaches_nonempty hstopAt.1 hreach
          obtain ⟨topMid, restMid, hmid_eq⟩ :=
            stackHasBottom_nonempty (A := A) hbottomMid
          subst stackMid
          have hreachMid :
              @PDA.Reaches Q T S _ _ _ M.toPDA
                ⟨cstable.1, a :: w,
                  eraseAnnotatedStack (A := A) (topMid :: restMid)⟩
                ⟨qf, [], γf⟩ := by
            simpa [heraseMid] using hreachStable
          cases topMid with
          | none =>
              simp [StackWellAnnotated] at hstackMid
              subst restMid
              have hreachEmpty :
                  @PDA.Reaches Q T S _ _ _ M.toPDA
                    ⟨cstable.1, a :: w, []⟩ ⟨qf, [], γf⟩ := by
                simpa [eraseAnnotatedStack] using hreachMid
              have hsameInput := (PDA.reaches_on_empty_stack (pda := M.toPDA) hreachEmpty).1
              cases hsameInput
          | some payloadMid =>
              rcases payloadMid with ⟨Zmid, belowMid⟩
              have hstableMid :
                  M.EpsilonStable
                    (cstable.1,
                      eraseAnnotatedStack (A := A) (some (Zmid, belowMid) :: restMid)) := by
                simpa [heraseMid] using hstable
              have hstableTop : M.epsilon_transition cstable.1 Zmid = none := by
                simpa [EpsilonStable, eraseAnnotatedStack] using hstableMid
              obtain ⟨p, β, hδ, hreachNextOriginal⟩ :=
                stable_reaches_nonempty_decompose (M := M)
                  (q := cstable.1) (qf := qf) (a := a) (w := w)
                  (Z := Zmid) (γ := eraseAnnotatedStack (A := A) restMid)
                  (γf := γf) hstableTop (by
                    simpa [eraseAnnotatedStack] using hreachMid)
              obtain ⟨stackNext, summaryNext, hinput, hstackNext, hbottomNext,
                hsummaryNext, heraseNext⟩ :=
                  totalizer_stable_input_step_preserves_annotations (A := A)
                    (q := cstable.1) (p := p)
                    (b := acceptBit A q (fullSummaryOfTop A (some (Z, below))))
                    (a := a) (Z := Zmid) (below := belowMid) (β := β)
                    (rest := restMid) (w := w)
                    hstackMid hbottomMid hstableMid hδ
              obtain ⟨topNext, restNext, hnext_eq⟩ :=
                stackHasBottom_nonempty (A := A) hbottomNext
              subst stackNext
              have hsummaryTopNext :
                  SummaryRepresents A (fullSummaryOfTop A topNext)
                    (eraseAnnotatedStack (A := A) (topNext :: restNext)) :=
                stackWellAnnotated_fullSummaryOfTop (A := A) hstackNext
              have hsummaryEq :
                  summaryNext = fullSummaryOfTop A topNext :=
                SummaryRepresents.eq (A := A) hsummaryNext hsummaryTopNext
              subst summaryNext
              have hreachNext :
                  @PDA.Reaches Q T S _ _ _ M.toPDA
                    ⟨p, w, eraseAnnotatedStack (A := A) (topNext :: restNext)⟩
                    ⟨qf, [], γf⟩ := by
                simpa [heraseNext] using hreachNextOriginal
              obtain ⟨st, stackFinal, hrec, hfinal⟩ :=
                ih p topNext restNext hstackNext hbottomNext hreachNext
              refine ⟨st, stackFinal, ?_, hfinal⟩
              exact Relation.ReflTransGen.trans (by simpa [simState] using hphase)
                (Relation.ReflTransGen.trans
                  (Relation.ReflTransGen.single hinput)
                  hrec)

theorem totalizer_reaches_empty (w : List T) :
    ∃ st stack,
      @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
        ⟨(totalizer A).initial_state, w, [(totalizer A).start_symbol]⟩
        ⟨st, [], stack⟩ := by
  obtain ⟨top, rest, hinitStack⟩ :=
    stackHasBottom_nonempty (A := A) (stackHasBottom_initialReplacement A)
  have hstack : StackWellAnnotated (A := A) (top :: rest) := by
    simpa [← hinitStack] using stackWellAnnotated_initialReplacement A
  have hbottom : StackHasBottom (A := A) (top :: rest) := by
    simpa [← hinitStack] using stackHasBottom_initialReplacement A
  obtain ⟨st, stack, hreachSim⟩ :=
    totalizer_reaches_empty_from_sim (A := A)
      M.initial_state (initialAcceptBit A) w top rest hstack hbottom
  refine ⟨st, stack, ?_⟩
  exact Relation.ReflTransGen.trans (totalizer_initial_reaches A w) (by
    simpa [totalizer, initialAcceptBit, initialSummary, simState, hinitStack] using hreachSim)

theorem original_accept_subset_totalizer_acceptsByFinalState :
    M.acceptsByFinalState ≤ (totalizer A).acceptsByFinalState := by
  intro w hw
  unfold DPDA.acceptsByFinalState PDA.acceptsByFinalState at hw ⊢
  obtain ⟨qf, hqf, γf, hreach⟩ := hw
  obtain ⟨top, rest, hinitStack⟩ :=
    stackHasBottom_nonempty (A := A) (stackHasBottom_initialReplacement A)
  have hstack : StackWellAnnotated (A := A) (top :: rest) := by
    simpa [← hinitStack] using stackWellAnnotated_initialReplacement A
  have hbottom : StackHasBottom (A := A) (top :: rest) := by
    simpa [← hinitStack] using stackHasBottom_initialReplacement A
  have hreachInit :
      @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨M.initial_state, w, eraseAnnotatedStack (A := A) (top :: rest)⟩
        ⟨qf, [], γf⟩ := by
    simpa [← hinitStack, erase_initialReplacement] using hreach
  have hsummaryTop :
      SummaryRepresents A (fullSummaryOfTop A top) [M.start_symbol] := by
    have h :=
      stackWellAnnotated_fullSummaryOfTop (A := A) (top := top) (rest := rest) hstack
    simpa [← hinitStack, erase_initialReplacement] using h
  have hsummaryEq : fullSummaryOfTop A top = initialSummary A :=
    SummaryRepresents.eq (A := A) hsummaryTop (initialSummaryRepresents A)
  obtain ⟨st, stack, hreachSim, hfinal⟩ :=
    totalizer_accepting_reaches_from_simState (A := A)
      M.initial_state w top rest hstack hbottom hreachInit hqf
  refine ⟨st, hfinal, stack, ?_⟩
  exact Relation.ReflTransGen.trans (totalizer_initial_reaches A w) (by
    simpa [totalizer, initialSummary, hinitStack, hsummaryEq] using hreachSim)

theorem totalizer_acceptsByFinalState_eq_original :
    (totalizer A).acceptsByFinalState = M.acceptsByFinalState :=
  le_antisymm (totalizer_acceptsByFinalState_subset_original (A := A))
    (original_accept_subset_totalizer_acceptsByFinalState (A := A))

theorem totalizer_total :
    ∀ w : List T, ∃ st stack,
      @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
        (totalizer A).toPDA
        ⟨(totalizer A).initial_state, w, [(totalizer A).start_symbol]⟩
        ⟨st, [], stack⟩ :=
  totalizer_reaches_empty A

theorem totalizer_final_consistent (w : List T) (st₁ st₂ : TotalState Q)
    (stack₁ stack₂ : List (TotalStackSymbol A))
    (h₁ : @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨(totalizer A).initial_state, w, [(totalizer A).start_symbol]⟩
      ⟨st₁, [], stack₁⟩)
    (h₂ : @PDA.Reaches (TotalState Q) T (TotalStackSymbol A) _ _ _
      (totalizer A).toPDA
      ⟨(totalizer A).initial_state, w, [(totalizer A).start_symbol]⟩
      ⟨st₂, [], stack₂⟩) :
    st₁ ∈ (totalizer A).final_states ↔ st₂ ∈ (totalizer A).final_states := by
  obtain ⟨n₁, hn₁⟩ := PDA.reaches_iff_reachesIn.mp h₁
  obtain ⟨n₂, hn₂⟩ := PDA.reaches_iff_reachesIn.mp h₂
  by_cases hle : n₁ ≤ n₂
  · exact totalizer_empty_reaches_preserves_final (A := A)
      (totalizer_reachesIn_prefix_of_le (A := A) hle hn₁ hn₂)
  · have hle' : n₂ ≤ n₁ := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    exact (totalizer_empty_reaches_preserves_final (A := A)
      (totalizer_reachesIn_prefix_of_le (A := A) hle' hn₂ hn₁)).symm

theorem totalizer_decides :
    (totalizer A).DecidesEveryInput := by
  constructor
  · exact totalizer_total A
  · intro w st₁ st₂ stack₁ stack₂ h₁ h₂
    exact totalizer_final_consistent (A := A) w st₁ st₂ stack₁ stack₂ h₁ h₂

end

end DPDA
