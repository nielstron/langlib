module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RegularStairBases

@[expose]
public section

/-!
# Reindexing and enlarging stair bounds

Tail elimination discards a fixed initial segment of a stair and adds a fixed
presentation overhead.  These elementary closure lemmas isolate that book-
keeping from the semantic replacement argument.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private theorem strictMono_nat_id_le
    {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) :
    n ≤ f n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep : f n < f n.succ := by
        simpa [Nat.succ_eq_add_one] using hf (Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (ih.trans_lt hstep)

private theorem strictMono_nat_add_le
    {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) :
    f 0 + n ≤ f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : f n < f (n + 1) := by
        simpa [Nat.succ_eq_add_one] using hf (Nat.lt_succ_self n)
      omega

/-- An open-sound coverage remains bounded when its numerical bound grows. -/
public def BoundedOpenSoundCoverage.mono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {bound bound' : ℕ} {word}
    (coverage : BoundedOpenSoundCoverage g initialLeft initialRight bound word)
    (hbound : bound ≤ bound') :
    BoundedOpenSoundCoverage g initialLeft initialRight bound' word :=
  { coverage with
    arity_le := coverage.arity_le.trans hbound
    left_size_le := coverage.left_size_le.trans hbound
    right_size_le := coverage.right_size_le.trans hbound }

/-- Eventual bounded open-soundness is monotone in the bound. -/
public theorem EventuallyBoundedOpenSound.mono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {bound bound' : ℕ}
    {path : TracePath g initialLeft initialRight}
    (hcoverage : g.EventuallyBoundedOpenSound initialLeft initialRight
      bound path)
    (hbound : bound ≤ bound') :
    g.EventuallyBoundedOpenSound initialLeft initialRight bound' path := by
  obtain ⟨n, ⟨coverage⟩⟩ := hcoverage
  exact ⟨n, ⟨coverage.mono hbound⟩⟩

/-- A supported regular presentation remains bounded when its numerical bound
grows. -/
public def BoundedActiveSchemaCoverage.mono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound bound' width : ℕ} {arguments word}
    (coverage : BoundedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments word)
    (hbound : bound ≤ bound') :
    BoundedActiveSchemaCoverage g initialLeft initialRight
      bound' width arguments word :=
  { coverage with
    arity_le := coverage.arity_le.trans hbound
    left_size_le := coverage.left_size_le.trans hbound
    right_size_le := coverage.right_size_le.trans hbound }

/-- Pointwise enlargement of the growth function preserves a regular stair
sequence. -/
public def RegularActiveStairSequence.rebound
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width : ℕ}
    {growth growth' : ℕ → ℕ}
    {path : TracePath g initialLeft initialRight}
    (sequence : RegularActiveStairSequence g initialLeft initialRight
      width growth path)
    (hbound : ∀ j, growth j ≤ growth' j) :
    RegularActiveStairSequence g initialLeft initialRight
      width growth' path :=
  { arguments := sequence.arguments
    levels := sequence.levels
    levels_strictMono := sequence.levels_strictMono
    covered := fun j => by
      obtain ⟨coverage⟩ := sequence.covered j
      exact ⟨coverage.mono (hbound j)⟩ }

/-- Discarding a fixed number of selected prefixes produces a stair with the
shifted growth function. -/
public def RegularActiveStairSequence.dropLevels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width : ℕ}
    {growth : ℕ → ℕ} {path : TracePath g initialLeft initialRight}
    (sequence : RegularActiveStairSequence g initialLeft initialRight
      width growth path)
    (offset : ℕ) :
    RegularActiveStairSequence g initialLeft initialRight width
      (fun j => growth (offset + j)) path :=
  { arguments := sequence.arguments
    levels := fun j => sequence.levels (offset + j)
    levels_strictMono := by
      intro i j hij
      exact sequence.levels_strictMono (Nat.add_lt_add_left hij offset)
    covered := fun j => sequence.covered (offset + j) }

/-- Dropping levels and then adding a fixed presentation overhead gives the
exact growth transformation used in the tail-elimination proof. -/
public def RegularActiveStairSequence.dropLevelsAndAdd
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width : ℕ}
    {growth : ℕ → ℕ} {path : TracePath g initialLeft initialRight}
    (sequence : RegularActiveStairSequence g initialLeft initialRight
      width growth path)
    (offset overhead : ℕ) :
    RegularActiveStairSequence g initialLeft initialRight width
      (fun j => growth (offset + j) + overhead) path := by
  apply (sequence.dropLevels offset).rebound
  intro j
  exact Nat.le_add_right _ _

/-- Dropping `shorterWord.length + 1` selected levels guarantees that every
remaining path word is strictly longer than `shorterWord`, independently of
where the strictly increasing level selector started. -/
public theorem RegularActiveStairSequence.shorterWord_lt_after_drop
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width : ℕ}
    {growth : ℕ → ℕ} {path : TracePath g initialLeft initialRight}
    (sequence : RegularActiveStairSequence g initialLeft initialRight
      width growth path)
    (shorterWord : List (Label Action)) (j : ℕ) :
    shorterWord.length <
      (path.word
        (sequence.levels (shorterWord.length + 1 + j))).length := by
  rw [path.word_length]
  have hlevels := strictMono_nat_id_le sequence.levels_strictMono
    (shorterWord.length + 1 + j)
  omega

/-- If the shorter certificate extends the selected level-zero stem by
`suffix`, dropping only `suffix.length + 1` selected levels is enough.  Unlike
the absolute bound above, this offset is independent of the path's initial
selected level. -/
public theorem RegularActiveStairSequence.appendedWord_lt_after_drop
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width : ℕ}
    {growth : ℕ → ℕ} {path : TracePath g initialLeft initialRight}
    (sequence : RegularActiveStairSequence g initialLeft initialRight
      width growth path)
    (suffix : List (Label Action)) (j : ℕ) :
    (path.word (sequence.levels 0) ++ suffix).length <
      (path.word
        (sequence.levels (suffix.length + 1 + j))).length := by
  simp only [List.length_append, path.word_length]
  have hlevels := strictMono_nat_add_le sequence.levels_strictMono
    (suffix.length + 1 + j)
  omega

end EncodedFirstOrderGrammar

end DCFEquivalence
