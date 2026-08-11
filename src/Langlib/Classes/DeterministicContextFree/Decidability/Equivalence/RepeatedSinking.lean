module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedSemanticReachability

@[expose]
public section

/-!
# Repeated sinking and accumulated exposure depth

The M₂ argument repeatedly advances to an immediate unfolding subterm until a
pivot is encountered.  Each sinking block consumes a nonempty prefix.  After
`depth` such blocks, the concatenated word exposes an occurrence at depth
`depth` of the original source.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One exact, progress-making sinking step with its reached representative
made explicit. -/
public structure SinkingStep
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action))
    (target : RegularTerm) where
  subterm : RegularTerm
  word_nonempty : word ≠ []
  subterm_at : source.SubtermAtDepth 1 subterm
  run : g.run? word source = some target
  target_matches : target.UnfoldingEquivalent subterm

/-- An exact sinking step is, in particular, a `SinksBy` witness. -/
public theorem SinkingStep.sinksBy
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {word : List (Label Action)}
    (step : SinkingStep g source word target) :
    g.SinksBy source word := by
  refine ⟨word, [], by simp, step.word_nonempty, ?_⟩
  exact ⟨step.subterm, target, step.subterm_at,
    step.run, step.target_matches⟩

/-- Every sinking witness selects an exact nonempty sinking prefix. -/
public theorem SinksBy.exists_sinkingStep_prefix
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    (hsinks : g.SinksBy source word) :
    ∃ stem suffix target,
      word = stem ++ suffix ∧
        Nonempty (SinkingStep g source stem target) := by
  obtain ⟨stem, suffix, hword, hnonempty,
      subterm, target, hsubterm, hrun, htarget⟩ := hsinks
  exact ⟨stem, suffix, target, hword, ⟨
    { subterm := subterm
      word_nonempty := hnonempty
      subterm_at := hsubterm
      run := hrun
      target_matches := htarget }⟩⟩

/-- `depth` consecutive exact sinking prefixes can be consumed from `word`.
The unused suffix after the final sinking step is retained. -/
@[expose] public def RepeatedlySinksBy
    (g : EncodedFirstOrderGrammar Action) :
    RegularTerm → List (Label Action) → ℕ → Prop
  | _source, _word, 0 => True
  | source, word, depth + 1 =>
      ∃ stem suffix target,
        word = stem ++ suffix ∧
          Nonempty (SinkingStep g source stem target) ∧
          g.RepeatedlySinksBy target suffix depth

@[simp] public theorem repeatedlySinksBy_zero
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action)) :
    g.RepeatedlySinksBy source word 0 := trivial

/-- One repeated sinking step is exactly ordinary sinking. -/
public theorem repeatedlySinksBy_one_iff
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action)) :
    g.RepeatedlySinksBy source word 1 ↔
      g.SinksBy source word := by
  constructor
  · rintro ⟨stem, suffix, target, hword, ⟨step⟩, _hrest⟩
    rw [hword]
    exact step.sinksBy.append suffix
  · intro hsinks
    obtain ⟨stem, suffix, target, hword, hstep⟩ :=
      hsinks.exists_sinkingStep_prefix
    exact ⟨stem, suffix, target, hword, hstep, trivial⟩

/-- Appending unused input preserves a repeated-sinking witness. -/
public theorem RepeatedlySinksBy.append
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.RepeatedlySinksBy source word depth)
    (suffix : List (Label Action)) :
    g.RepeatedlySinksBy source (word ++ suffix) depth := by
  induction depth generalizing source word with
  | zero => trivial
  | succ depth ih =>
      obtain ⟨stem, remainder, target, hword, hstep, hrest⟩ :=
        hsinks
      refine ⟨stem, remainder ++ suffix, target, ?_, hstep, ?_⟩
      · rw [hword, List.append_assoc]
      · exact ih hrest

/-- Truncating a repeated-sinking chain preserves its initial part. -/
public theorem RepeatedlySinksBy.mono
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {small large : ℕ}
    (hsinks : g.RepeatedlySinksBy source word large)
    (hle : small ≤ large) :
    g.RepeatedlySinksBy source word small := by
  induction small generalizing source word large with
  | zero => trivial
  | succ small ih =>
      cases large with
      | zero => omega
      | succ large =>
          obtain ⟨stem, suffix, target, hword, hstep, hrest⟩ :=
            hsinks
          exact ⟨stem, suffix, target, hword, hstep,
            ih hrest (by omega)⟩

/-- Every sinking block consumes at least one label, so `depth` repeated
blocks require a word of length at least `depth`. -/
public theorem RepeatedlySinksBy.depth_le_length
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.RepeatedlySinksBy source word depth) :
    depth ≤ word.length := by
  induction depth generalizing source word with
  | zero => omega
  | succ depth ih =>
      obtain ⟨stem, suffix, target, hword, ⟨step⟩, hrest⟩ :=
        hsinks
      have hstem : 1 ≤ stem.length :=
        List.length_pos_iff.mpr step.word_nonempty
      have htail := ih hrest
      rw [hword, List.length_append]
      omega

/-- Repeated sinking accumulates exact unfolding depth in the original
source. -/
public theorem RepeatedlySinksBy.exposesBy
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.RepeatedlySinksBy source word depth) :
    g.ExposesBy source word depth := by
  induction depth generalizing source word with
  | zero => exact g.exposesBy_zero source word
  | succ depth ih =>
      obtain ⟨stem, suffix, target, hword, ⟨step⟩, hrest⟩ :=
        hsinks
      obtain ⟨initialSegment, remainder, hsuffix, hexposes⟩ :=
        ih hrest
      refine ⟨stem ++ initialSegment, remainder, ?_, ?_⟩
      · rw [hword, hsuffix, List.append_assoc]
      · simpa [Nat.add_comm] using
          (ExposesAtDepth.append_of_run step.subterm_at step.run
            step.target_matches hexposes)

end EncodedFirstOrderGrammar

end DCFEquivalence
