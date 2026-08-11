module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisSoundness

@[expose]
public section

/-!
# Reducing sufficient-basis completeness to path coverage

This file isolates the compactness part of the positive equivalence proof.  If
every infinite path of derived pair labels eventually becomes an instance of a
bounded sound schema, then the concrete bounded basis derives `NOP` at the
root.  The proof is constructive at the level of derivations: from a missing
root `NOP` it repeatedly chooses an enabled child which also lacks `NOP`,
producing an infinite uncovered path.

The later stair/balancing theorem has exactly one job: establish
`EveryDerivationPathCovered` for some grammar-dependent bound.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private def PairRebaseInvariant
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) :
    CertificateJudgment Action → Prop
  | .pair word left right => ∀ basis',
      CertificateDerivable g initialLeft initialRight basis'
        (.pair word left right)
  | .nop _ => True
  | .fail => True

private theorem pairRebaseInvariant_of_derivable
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment) :
    PairRebaseInvariant g initialLeft initialRight judgment := by
  induction h with
  | «axiom» hground =>
      intro basis'
      exact .axiom hground
  | transition hpair happrox hleft hright hground ih =>
      intro basis'
      exact .transition (ih basis') happrox hleft hright hground
  | limit houter hshorter houterContext hreplacementContext hfocus
      hnontrivial hlength houterMatch hshorterLeft hshorterRight hground
      ihOuter ihShorter =>
      intro basis'
      exact .limit (ihOuter basis') (ihShorter basis') houterContext
        hreplacementContext hfocus hnontrivial hlength houterMatch
        hshorterLeft hshorterRight hground
  | symmetry hpair ih =>
      intro basis'
      exact .symmetry (ih basis')
  | basis => trivial
  | progression => trivial
  | rejection => trivial

/-- Pair-label derivations use no basis rule, so they can be replayed under
any replacement basis. -/
public theorem CertificateDerivable.rebasePair
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis basis' : List BasisPair}
    {word : List (Label Action)} {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right)) :
    CertificateDerivable g initialLeft initialRight basis'
      (.pair word left right) :=
  pairRebaseInvariant_of_derivable h basis'

/-- One-step rewriting preserves runtime groundness.  This follows from
well-formedness of the grammar; keeping it explicit here makes the compactness
argument independent of graph-substitution details. -/
@[expose] public def PreservesGroundSteps
    (g : EncodedFirstOrderGrammar Action) : Prop :=
  ∀ {label : Label Action} {source target : RegularTerm},
    source.Ground g.ranks → g.step? label source = some target →
      target.Ground g.ranks

/-- A derived pair is covered by a bounded sound basis instance. -/
public structure SoundMatch
    (g : EncodedFirstOrderGrammar Action)
    (word : List (Label Action)) (left right : RegularTerm) where
  schema : BasisPair
  arguments : List RegularTerm
  word_nonempty : word ≠ []
  sound : g.SoundBasisPair schema
  argument_count : arguments.length = schema.arity
  arguments_ground : g.groundArgumentsCode arguments = true
  left_matches : RegularTerm.unfoldingEquivalentCode left
    (schema.left.instantiate arguments) = true
  right_matches : RegularTerm.unfoldingEquivalentCode right
    (schema.right.instantiate arguments) = true

/-- A single natural number bounding the arity and both finite graph
presentations in a sound match. -/
@[expose] public def SoundMatch.bound
    {g : EncodedFirstOrderGrammar Action}
    {word : List (Label Action)} {left right : RegularTerm}
    (matchData : SoundMatch g word left right) : ℕ :=
  max matchData.schema.arity
    (max matchData.schema.left.nodes.length
      matchData.schema.right.nodes.length)

/-- A sound match is bounded by its explicit finite presentation size. -/
public structure BoundedSoundMatch
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ)
    (word : List (Label Action)) (left right : RegularTerm) where
  schema : BasisPair
  arguments : List RegularTerm
  word_nonempty : word ≠ []
  sound : g.SoundBasisPair schema
  arity_le : schema.arity ≤ bound
  left_size_le : schema.left.nodes.length ≤ bound
  right_size_le : schema.right.nodes.length ≤ bound
  argument_count : arguments.length = schema.arity
  arguments_ground : g.groundArgumentsCode arguments = true
  left_matches : RegularTerm.unfoldingEquivalentCode left
    (schema.left.instantiate arguments) = true
  right_matches : RegularTerm.unfoldingEquivalentCode right
    (schema.right.instantiate arguments) = true

public def SoundMatch.toBounded
    {g : EncodedFirstOrderGrammar Action}
    {word : List (Label Action)} {left right : RegularTerm}
    (matchData : SoundMatch g word left right)
    {bound : ℕ} (hbound : matchData.bound ≤ bound) :
    BoundedSoundMatch g bound word left right :=
  { schema := matchData.schema
    arguments := matchData.arguments
    word_nonempty := matchData.word_nonempty
    sound := matchData.sound
    arity_le := le_trans (Nat.le_max_left _ _) hbound
    left_size_le := le_trans
      (le_trans (Nat.le_max_left _ _)
        (Nat.le_max_right matchData.schema.arity _)) hbound
    right_size_le := le_trans
      (le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right matchData.schema.arity _)) hbound
    argument_count := matchData.argument_count
    arguments_ground := matchData.arguments_ground
    left_matches := matchData.left_matches
    right_matches := matchData.right_matches }

/-- A word is covered when some pair derivable at that same word (possibly
after limit-subterm replacements) matches a bounded sound schema. -/
public structure BoundedSoundCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound : ℕ)
    (word : List (Label Action)) where
  left : RegularTerm
  right : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight
    (g.boundedSoundBasis bound)
    (CertificateJudgment.pair word left right)
  match_data : BoundedSoundMatch g bound word left right

/-- Basis-independent coverage of one word by a sound schema.  Pair-label
derivations are stored under the empty basis and can later be rebased. -/
public structure SoundCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (word : List (Label Action)) where
  left : RegularTerm
  right : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight []
    (CertificateJudgment.pair word left right)
  match_data : SoundMatch g word left right

@[expose] public def SoundCoverage.bound
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {word : List (Label Action)}
    (coverage : SoundCoverage g initialLeft initialRight word) : ℕ :=
  coverage.match_data.bound

public def SoundCoverage.toBounded
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {word : List (Label Action)}
    (coverage : SoundCoverage g initialLeft initialRight word)
    {bound : ℕ} (hbound : coverage.bound ≤ bound) :
    BoundedSoundCoverage g initialLeft initialRight bound word :=
  { left := coverage.left
    right := coverage.right
    derivation := coverage.derivation.rebasePair
    match_data := coverage.match_data.toBounded hbound }

/-- An infinite common transition path from one initial pair.  Determinism
fixes both residual terms once the successive labels have been chosen. -/
public structure TracePath
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) where
  word : ℕ → List (Label Action)
  left : ℕ → RegularTerm
  right : ℕ → RegularTerm
  starts_word : word 0 = []
  starts_left : left 0 = initialLeft
  starts_right : right 0 = initialRight
  step : ∀ n, ∃ label,
    word (n + 1) = word n ++ [label] ∧
    g.step? label (left n) = some (left (n + 1)) ∧
    g.step? label (right n) = some (right (n + 1))

/-- The index of a trace path is exactly the length of its accumulated word. -/
public theorem TracePath.word_length
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (n : ℕ) :
    (path.word n).length = n := by
  induction n with
  | zero => simp [path.starts_word]
  | succ n ih =>
      obtain ⟨label, hword, _hleft, _hright⟩ := path.step n
      rw [show n + 1 = n.succ by omega, hword,
        List.length_append, ih]
      simp

/-- Pointwise form of the deep balancing statement: every infinite common
trace eventually reaches a word at which some derived pair is an instance of a
sound finite schema.  No uniform presentation bound is required here. -/
@[expose] public def EveryTracePathEventuallySound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) : Prop :=
  ∀ path : TracePath g initialLeft initialRight,
    ∃ n, Nonempty (SoundCoverage g initialLeft initialRight (path.word n))

/-- Every infinite derived path eventually meets a bounded sound schema. -/
@[expose] public def EveryDerivationPathCovered
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound : ℕ) : Prop :=
  ∀ path : TracePath g initialLeft initialRight,
    ∃ n, Nonempty (BoundedSoundCoverage g initialLeft initialRight
      bound (path.word n))

private structure OpenPair
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound : ℕ) where
  word : List (Label Action)
  left : RegularTerm
  right : RegularTerm
  pair : CertificateDerivable g initialLeft initialRight
    (g.boundedSoundBasis bound) (.pair word left right)
  not_nop : ¬CertificateDerivable g initialLeft initialRight
    (g.boundedSoundBasis bound) (.nop word)

private def OpenSuccessor
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {bound : ℕ}
    (current next : OpenPair g initialLeft initialRight bound) : Prop :=
  ∃ label,
    next.word = current.word ++ [label] ∧
    g.step? label current.left = some next.left ∧
    g.step? label current.right = some next.right

private theorem exists_openSuccessor
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {bound : ℕ}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (current : OpenPair g initialLeft initialRight bound) :
    ∃ next, OpenSuccessor current next := by
  classical
  have hcurrentEquivalent : g.TraceEquivalent current.left current.right :=
    current.pair.pair_traceEquivalent_of_initial laws hinitialEquivalent
  have happroxProp : g.TraceApprox 1 current.left current.right :=
    (g.traceEquivalent_iff_forall_traceApprox current.left current.right).mp
      hcurrentEquivalent 1
  have happroxCode : g.traceApproxCode 1 current.left current.right = true :=
    (g.traceApproxCode_eq_true_iff 1 current.left current.right).mpr happroxProp
  have hexistsLabel : ∃ label ∈ g.enabledLabels current.left,
      ¬CertificateDerivable g initialLeft initialRight
        (g.boundedSoundBasis bound) (.nop (current.word ++ [label])) := by
    by_contra hnone
    push_neg at hnone
    apply current.not_nop
    exact .progression current.pair happroxCode hnone
  obtain ⟨label, henabled, hnotNop⟩ := hexistsLabel
  have hleftSome := (g.mem_enabledLabels_iff current.left label).mp henabled
  cases hleft : g.step? label current.left with
  | none => simp [hleft] at hleftSome
  | some nextLeft =>
      have hrel := happroxProp label
      rw [hleft] at hrel
      cases hright : g.step? label current.right with
      | none =>
          rw [hright] at hrel
          cases hrel
      | some nextRight =>
          have hcurrentGround := groundPairCode_of_pair_derivable current.pair
          unfold groundPairCode at hcurrentGround
          rw [Bool.and_eq_true] at hcurrentGround
          have hleftGround : current.left.Ground g.ranks :=
            (RegularTerm.groundCode_eq_true_iff g.ranks current.left).mp
              hcurrentGround.1
          have hrightGround : current.right.Ground g.ranks :=
            (RegularTerm.groundCode_eq_true_iff g.ranks current.right).mp
              hcurrentGround.2
          have hnextLeftGround := hgroundSteps hleftGround hleft
          have hnextRightGround := hgroundSteps hrightGround hright
          have hnextGround : g.groundPairCode nextLeft nextRight = true := by
            unfold groundPairCode
            rw [Bool.and_eq_true]
            exact ⟨(RegularTerm.groundCode_eq_true_iff g.ranks nextLeft).mpr
                hnextLeftGround,
              (RegularTerm.groundCode_eq_true_iff g.ranks nextRight).mpr
                hnextRightGround⟩
          let nextPair : OpenPair g initialLeft initialRight bound :=
            { word := current.word ++ [label]
              left := nextLeft
              right := nextRight
              pair := .transition current.pair happroxCode hleft hright hnextGround
              not_nop := hnotNop }
          refine ⟨nextPair, label, rfl, ?_, ?_⟩
          · exact hleft
          · exact hright

private noncomputable def nextOpenPair
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {bound : ℕ}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (current : OpenPair g initialLeft initialRight bound) :
    OpenPair g initialLeft initialRight bound :=
  Classical.choose
    (exists_openSuccessor laws hgroundSteps hinitialEquivalent current)

private theorem nextOpenPair_isSuccessor
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {bound : ℕ}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (current : OpenPair g initialLeft initialRight bound) :
    OpenSuccessor current
      (nextOpenPair laws hgroundSteps hinitialEquivalent current) :=
  Classical.choose_spec
    (exists_openSuccessor laws hgroundSteps hinitialEquivalent current)

private noncomputable def openPairSequence
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {bound : ℕ}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (initial : OpenPair g initialLeft initialRight bound) :
    ℕ → OpenPair g initialLeft initialRight bound
  | 0 => initial
  | n + 1 => nextOpenPair laws hgroundSteps hinitialEquivalent
      (openPairSequence laws hgroundSteps hinitialEquivalent initial n)

/-- Path coverage by bounded sound instances yields an actual finite
derivation of root `NOP`. -/
public theorem derivable_nop_of_everyDerivationPathCovered
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {bound : ℕ}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hequivalent : g.TraceEquivalent initialLeft initialRight)
    (hcovered : g.EveryDerivationPathCovered
      initialLeft initialRight bound) :
    CertificateDerivable g initialLeft initialRight
      (g.boundedSoundBasis bound) (.nop []) := by
  classical
  by_contra hnotRoot
  let initial : OpenPair g initialLeft initialRight bound :=
    { word := []
      left := initialLeft
      right := initialRight
      pair := .axiom hground
      not_nop := hnotRoot }
  let sequence := openPairSequence laws hgroundSteps hequivalent initial
  let path : TracePath g initialLeft initialRight :=
    { word := fun n => (sequence n).word
      left := fun n => (sequence n).left
      right := fun n => (sequence n).right
      starts_word := rfl
      starts_left := rfl
      starts_right := rfl
      step := fun n => by
        change OpenSuccessor (sequence n) (sequence (n + 1))
        change OpenSuccessor (sequence n)
          (nextOpenPair laws hgroundSteps hequivalent (sequence n))
        exact nextOpenPair_isSuccessor laws hgroundSteps
          hequivalent (sequence n) }
  obtain ⟨n, ⟨hcoverage⟩⟩ := hcovered path
  change BoundedSoundCoverage g initialLeft initialRight bound
    (sequence n).word at hcoverage
  apply (sequence n).not_nop
  exact hcoverage.derivation.nop_of_boundedSoundInstance g bound
    hcoverage.match_data.word_nonempty hcoverage.match_data.sound
    hcoverage.match_data.arity_le hcoverage.match_data.left_size_le
    hcoverage.match_data.right_size_le hcoverage.match_data.argument_count
    hcoverage.match_data.arguments_ground hcoverage.match_data.left_matches
    hcoverage.match_data.right_matches

end EncodedFirstOrderGrammar

end DCFEquivalence
