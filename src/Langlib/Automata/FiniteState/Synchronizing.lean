module

public import Langlib.Automata.FiniteState.Definition

@[expose]
public section

/-!
# Synchronizing deterministic finite automata

This file adds the reset-word vocabulary used in synchronization theory to
Langlib's `DFA`, which is Mathlib's deterministic finite-automaton type.
Acceptance data are irrelevant to synchronization: a word is reset when it
sends every possible starting state to one common state.
-/

namespace DFA

universe u v

variable {Alpha : Type u} {State : Type v}

/-- A word is a reset word when it sends every state to one common state. -/
def IsResetWord (M : DFA Alpha State) (word : List Alpha) : Prop :=
  ∃ target, ∀ state, M.evalFrom state word = target

/-- A DFA is synchronizing when it has at least one reset word. -/
def Synchronizing (M : DFA Alpha State) : Prop :=
  ∃ word, M.IsResetWord word

/-- The DFA has a reset word whose length is at most `bound`. -/
def HasResetWordOfLengthAtMost
    (M : DFA Alpha State) (bound : ℕ) : Prop :=
  ∃ word, M.IsResetWord word ∧ word.length ≤ bound

/-- The numerical Černý bound for the state type of `M`. -/
def cernyBound (_M : DFA Alpha State) [Fintype State] : ℕ :=
  (Fintype.card State - 1) ^ 2

/-- The automaton satisfies the conclusion of the Černý conjecture. -/
def SatisfiesCerny (M : DFA Alpha State) [Fintype State] : Prop :=
  M.HasResetWordOfLengthAtMost M.cernyBound

/-- Evaluate a list of word chunks without first constructing their
flattening.  This is extensionally `evalFrom` on `chunks.flatten`, but it is
also useful for kernel computation because the evaluator's recursion depth
is bounded by the largest chunk rather than the total word length. -/
def evalChunks (M : DFA Alpha State) (state : State) :
    List (List Alpha) → State
  | [] => state
  | chunk :: chunks => M.evalChunks (M.evalFrom state chunk) chunks

theorem evalFrom_flatten (M : DFA Alpha State) (state : State)
    (chunks : List (List Alpha)) :
    M.evalFrom state chunks.flatten = M.evalChunks state chunks := by
  induction chunks generalizing state with
  | nil => rfl
  | cons chunk chunks ih =>
      simp only [List.flatten_cons, M.evalFrom_of_append, evalChunks]
      exact ih _

instance (M : DFA Alpha State) (word : List Alpha)
    [Fintype State] [DecidableEq State] :
    Decidable (M.IsResetWord word) := by
  unfold IsResetWord
  infer_instance

theorem isResetWord_iff_pairwise (M : DFA Alpha State)
    (word : List Alpha) :
    M.IsResetWord word ↔
      ∀ left right, M.evalFrom left word = M.evalFrom right word := by
  constructor
  · rintro ⟨target, htarget⟩ left right
    rw [htarget left, htarget right]
  · intro hpair
    exact ⟨M.evalFrom M.start word, fun state => hpair state M.start⟩

theorem isResetWord_iff_eq_start (M : DFA Alpha State)
    (word : List Alpha) :
    M.IsResetWord word ↔
      ∀ state, M.evalFrom state word = M.evalFrom M.start word := by
  rw [isResetWord_iff_pairwise]
  constructor
  · exact fun h state => h state M.start
  · intro h left right
    rw [h left, h right]

theorem IsResetWord.appendRight {M : DFA Alpha State}
    {word suffix : List Alpha} (hword : M.IsResetWord word) :
    M.IsResetWord (word ++ suffix) := by
  obtain ⟨target, htarget⟩ := hword
  refine ⟨M.evalFrom target suffix, ?_⟩
  intro state
  rw [M.evalFrom_of_append, htarget state]

theorem IsResetWord.appendLeft {M : DFA Alpha State}
    {pre word : List Alpha} (hword : M.IsResetWord word) :
    M.IsResetWord (pre ++ word) := by
  obtain ⟨target, htarget⟩ := hword
  refine ⟨target, ?_⟩
  intro state
  rw [M.evalFrom_of_append, htarget]

theorem IsResetWord.synchronizing {M : DFA Alpha State}
    {word : List Alpha} (hword : M.IsResetWord word) :
    M.Synchronizing :=
  ⟨word, hword⟩

theorem satisfiesCerny_of_resetWord (M : DFA Alpha State)
    [Fintype State] {word : List Alpha}
    (hword : M.IsResetWord word)
    (hlength : word.length ≤ M.cernyBound) :
    M.SatisfiesCerny :=
  ⟨word, hword, hlength⟩

theorem SatisfiesCerny.synchronizing (M : DFA Alpha State)
    [Fintype State] (hM : M.SatisfiesCerny) :
    M.Synchronizing := by
  obtain ⟨word, hword, _⟩ := hM
  exact hword.synchronizing

end DFA
