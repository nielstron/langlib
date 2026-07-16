module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TraceApproximants

@[expose]
public section

/-!
# Shortest distinguishing words

The soundness half of the finite-basis calculus follows a shortest word on
which two deterministic transition trees disagree.  This file records the
generic deterministic facts about such words, independently of the later
limit-subterm rule.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A finite label word is enabled from exactly one of two terms. -/
@[expose] public def DistinguishingWord
    (g : EncodedFirstOrderGrammar Action)
    (left right : RegularTerm) (word : List (Label Action)) : Prop :=
  g.IsTrace left word ≠ g.IsTrace right word

/-- An offending word is a shortest distinguishing word.  Minimality is by
length, so all words shorter than it agree, not merely its proper prefixes. -/
@[expose] public def OffendingWord
    (g : EncodedFirstOrderGrammar Action)
    (left right : RegularTerm) (word : List (Label Action)) : Prop :=
  g.DistinguishingWord left right word ∧
    ∀ shorter, shorter.length < word.length →
      ¬g.DistinguishingWord left right shorter

public theorem distinguishingWord_iff_isSome_ne
    (g : EncodedFirstOrderGrammar Action)
    (left right : RegularTerm) (word : List (Label Action)) :
    g.DistinguishingWord left right word ↔
      (g.run? word left).isSome ≠ (g.run? word right).isSome := by
  simp [DistinguishingWord, IsTrace]

public theorem not_traceEquivalent_iff_exists_distinguishingWord
    (g : EncodedFirstOrderGrammar Action) (left right : RegularTerm) :
    ¬g.TraceEquivalent left right ↔
      ∃ word, g.DistinguishingWord left right word := by
  change (fun word => g.IsTrace left word) ≠
      (fun word => g.IsTrace right word) ↔ _
  rw [Function.ne_iff]
  rfl

/-- Every inequivalent pair has a shortest distinguishing word. -/
public theorem exists_offendingWord_of_not_traceEquivalent
    (g : EncodedFirstOrderGrammar Action) {left right : RegularTerm}
    (hne : ¬g.TraceEquivalent left right) :
    ∃ word, g.OffendingWord left right word := by
  classical
  obtain ⟨witness, hwitness⟩ :=
    (g.not_traceEquivalent_iff_exists_distinguishingWord left right).mp hne
  let leastLength := Nat.find
    (show ∃ n, ∃ word, word.length = n ∧
        g.DistinguishingWord left right word from
      ⟨witness.length, witness, rfl, hwitness⟩)
  obtain ⟨word, hlength, hword⟩ := Nat.find_spec
    (show ∃ n, ∃ word, word.length = n ∧
        g.DistinguishingWord left right word from
      ⟨witness.length, witness, rfl, hwitness⟩)
  refine ⟨word, hword, ?_⟩
  intro shorter hshorter hdistinguishes
  have hexists : ∃ candidate, candidate.length = shorter.length ∧
      g.DistinguishingWord left right candidate :=
    ⟨shorter, rfl, hdistinguishes⟩
  have hleast : leastLength ≤ shorter.length := Nat.find_min' _ hexists
  dsimp only [leastLength] at hleast
  omega

@[simp] public theorem not_distinguishingWord_nil
    (g : EncodedFirstOrderGrammar Action) (left right : RegularTerm) :
    ¬g.DistinguishingWord left right [] := by
  simp [DistinguishingWord, IsTrace]

public theorem OffendingWord.ne_nil
    {g : EncodedFirstOrderGrammar Action} {left right : RegularTerm}
    {word : List (Label Action)} (hword : g.OffendingWord left right word) :
    word ≠ [] := by
  intro hnil
  subst word
  exact g.not_distinguishingWord_nil left right hword.1

@[symm] public theorem OffendingWord.symm
    {g : EncodedFirstOrderGrammar Action} {left right : RegularTerm}
    {word : List (Label Action)} (hword : g.OffendingWord left right word) :
    g.OffendingWord right left word := by
  refine ⟨ne_comm.mp hword.1, ?_⟩
  intro shorter hshorter hdistinguishes
  exact hword.2 shorter hshorter (ne_comm.mp hdistinguishes)

/-- Before the final symbol of a shortest distinguishing word, the two trace
trees agree at every smaller depth. -/
public theorem OffendingWord.traceApprox_pred
    {g : EncodedFirstOrderGrammar Action} {left right : RegularTerm}
    {word : List (Label Action)} (hword : g.OffendingWord left right word) :
    g.TraceApprox (word.length - 1) left right := by
  classical
  apply (g.traceApprox_iff_sameTracesThrough
    (word.length - 1) left right).mpr
  intro candidate hlength
  have hwordLength : 0 < word.length := by
    cases word with
    | nil => exact (hword.ne_nil rfl).elim
    | cons head tail => simp
  have hshorter : candidate.length < word.length := by omega
  have hagree := hword.2 candidate hshorter
  unfold DistinguishingWord at hagree
  exact iff_of_eq (not_ne_iff.mp hagree)

/-- Finite trace agreement transports whether a supplied word distinguishes a
pair, provided the comparison depth reaches that word. -/
public theorem distinguishingWord_congr_left_of_traceApprox
    {g : EncodedFirstOrderGrammar Action}
    {left replacement right : RegularTerm} {depth : ℕ}
    (happrox : g.TraceApprox depth left replacement)
    {word : List (Label Action)} (hlength : word.length ≤ depth) :
    g.DistinguishingWord left right word ↔
      g.DistinguishingWord replacement right word := by
  have hsame := (g.traceApprox_iff_sameTracesThrough
    depth left replacement).mp happrox word hlength
  unfold DistinguishingWord
  rw [propext hsame]

/-- Replacing the left term by one agreeing through the full offending depth
preserves the same shortest counterexample. -/
public theorem OffendingWord.replaceLeft
    {g : EncodedFirstOrderGrammar Action}
    {left replacement right : RegularTerm} {word : List (Label Action)}
    (hword : g.OffendingWord left right word)
    (happrox : g.TraceApprox word.length left replacement) :
    g.OffendingWord replacement right word := by
  refine ⟨(g.distinguishingWord_congr_left_of_traceApprox happrox
    (Nat.le_refl _)).mp hword.1, ?_⟩
  intro shorter hshorter hdistinguishes
  apply hword.2 shorter hshorter
  exact (g.distinguishingWord_congr_left_of_traceApprox happrox
    (Nat.le_of_lt hshorter)).mpr hdistinguishes

/-- Symmetric form of `OffendingWord.replaceLeft`. -/
public theorem OffendingWord.replaceRight
    {g : EncodedFirstOrderGrammar Action}
    {left right replacement : RegularTerm} {word : List (Label Action)}
    (hword : g.OffendingWord left right word)
    (happrox : g.TraceApprox word.length right replacement) :
    g.OffendingWord left replacement word := by
  have hsym : g.OffendingWord right left word := by
    exact hword.symm
  have hreplaced := hsym.replaceLeft happrox
  refine ⟨ne_comm.mp hreplaced.1, ?_⟩
  intro shorter hshorter hdistinguishes
  exact hreplaced.2 shorter hshorter (ne_comm.mp hdistinguishes)

/-- Reaching two targets through the same prefix transports trace disagreement
between the initial and residual pairs. -/
public theorem distinguishingWord_append_iff
    (g : EncodedFirstOrderGrammar Action)
    {left right left' right' : RegularTerm}
    {pre suffix : List (Label Action)}
    (hleft : g.run? pre left = some left')
    (hright : g.run? pre right = some right') :
    g.DistinguishingWord left right (pre ++ suffix) ↔
      g.DistinguishingWord left' right' suffix := by
  rw [g.distinguishingWord_iff_isSome_ne,
    g.distinguishingWord_iff_isSome_ne,
    g.run?_append pre suffix left,
    g.run?_append pre suffix right, hleft, hright]
  simp

/-- Removing a commonly executable prefix from a shortest distinguishing word
leaves a shortest distinguishing word for the reached residual pair. -/
public theorem OffendingWord.of_append
    {g : EncodedFirstOrderGrammar Action}
    {left right left' right' : RegularTerm}
    {pre suffix : List (Label Action)}
    (hword : g.OffendingWord left right (pre ++ suffix))
    (hleft : g.run? pre left = some left')
    (hright : g.run? pre right = some right') :
    g.OffendingWord left' right' suffix := by
  refine ⟨(g.distinguishingWord_append_iff hleft hright).mp hword.1, ?_⟩
  intro shorter hshorter hdistinguishes
  apply hword.2 (pre ++ shorter)
  · simp only [List.length_append]
    omega
  · exact (g.distinguishingWord_append_iff hleft hright).mpr hdistinguishes

/-- A nonempty offending word has matching first transitions: disagreement
cannot occur before its final label. -/
public theorem OffendingWord.exists_step_of_cons
    {g : EncodedFirstOrderGrammar Action}
    {left right : RegularTerm} {label : Label Action}
    {suffix : List (Label Action)}
    (hword : g.OffendingWord left right (label :: suffix))
    (hsuffix : suffix ≠ []) :
    ∃ left' right', g.step? label left = some left' ∧
      g.step? label right = some right' := by
  have hone : ¬g.DistinguishingWord left right [label] := by
    apply hword.2
    have hsuffixLength : 0 < suffix.length := by
      cases suffix with
      | nil => exact (hsuffix rfl).elim
      | cons head tail => simp
    simp [hsuffixLength]
  have hdistinguishes := hword.1
  unfold DistinguishingWord IsTrace at hone hdistinguishes
  simp only [run?_cons, run?_nil] at hone
  cases hleft : g.step? label left with
  | none =>
      cases hright : g.step? label right with
      | none =>
          simp [hleft, hright] at hdistinguishes
      | some right' =>
          exact (hone (by simp [hleft, hright])).elim
  | some left' =>
      cases hright : g.step? label right with
      | none =>
          exact (hone (by simp [hleft, hright])).elim
      | some right' =>
          exact ⟨left', right', rfl, rfl⟩

/-- After the common first transition, the tail of a shortest distinguishing
word is shortest for the successor pair. -/
public theorem OffendingWord.tail
    {g : EncodedFirstOrderGrammar Action}
    {left right left' right' : RegularTerm} {label : Label Action}
    {suffix : List (Label Action)}
    (hword : g.OffendingWord left right (label :: suffix))
    (hleft : g.step? label left = some left')
    (hright : g.step? label right = some right') :
    g.OffendingWord left' right' suffix := by
  have hprefixLeft : g.run? [label] left = some left' := by
    simp [hleft]
  have hprefixRight : g.run? [label] right = some right' := by
    simp [hright]
  have happend : label :: suffix = [label] ++ suffix := by rfl
  rw [happend] at hword
  exact OffendingWord.of_append hword hprefixLeft hprefixRight

end EncodedFirstOrderGrammar

end DCFEquivalence
