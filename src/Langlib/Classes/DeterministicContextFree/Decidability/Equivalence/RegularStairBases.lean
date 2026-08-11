module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveSchemaSupport

@[expose]
public section

/-!
# Stair bases closed under regular tail elimination

This is the stair interface used after the first balancing construction.
Unlike `ActiveStairSequence`, its heads are arbitrary regular schemas equipped
with `SupportedByPrefix`; hence tying a unary context during tail elimination
stays inside the interface.  All levels retain one common padded argument
tuple, while `width` records only its semantically active prefix.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A bounded regular active-schema presentation using one externally fixed
argument tuple. -/
public structure BoundedActiveSchemaCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (bound width : ℕ)
    (arguments : List RegularTerm) (word : List (Label Action)) where
  coverage : ActiveSchemaCoverage g initialLeft initialRight width word
  arguments_eq : coverage.arguments = arguments
  arity_le : coverage.schema.arity ≤ bound
  left_size_le : coverage.schema.left.nodes.length ≤ bound
  right_size_le : coverage.schema.right.nodes.length ≤ bound

/-- A stair sequence of arbitrary regular schemas.  The argument tuple is
fixed globally along the path; only its first `width` positions are active. -/
public structure RegularActiveStairSequence
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (width : ℕ) (growth : ℕ → ℕ)
    (path : TracePath g initialLeft initialRight) where
  arguments : List RegularTerm
  levels : ℕ → ℕ
  levels_strictMono : StrictMono levels
  covered : ∀ j, Nonempty
    (BoundedActiveSchemaCoverage g initialLeft initialRight
      (growth j) width arguments (path.word (levels j)))

/-- The regular active stair-base property, closed under unary-limit tail
elimination. -/
@[expose] public def HasRegularActiveStairBase
    (g : EncodedFirstOrderGrammar Action) (width : ℕ) : Prop :=
  ∃ growth : ℕ → ℕ,
    ∀ initialLeft initialRight,
      g.groundPairCode initialLeft initialRight = true →
      g.TraceEquivalent initialLeft initialRight →
      ∀ path : TracePath g initialLeft initialRight,
        g.EventuallyBoundedOpenSound initialLeft initialRight
          (growth 0) path ∨
        Nonempty (RegularActiveStairSequence g initialLeft initialRight
          width growth path)

/-- A finite-head bounded presentation is, in particular, a supported regular
schema presentation with the same bounds. -/
public def BoundedActiveHeadCoverage.toBoundedActiveSchemaCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight tails filler word bound}
    (coverage : BoundedActiveHeadCoverage g initialLeft initialRight
      bound tails filler word) :
    BoundedActiveSchemaCoverage g initialLeft initialRight bound tails.length
      coverage.arguments word :=
  { coverage := coverage.toActiveHeadCoverage.toActiveSchemaCoverage
    arguments_eq := rfl
    arity_le := coverage.arity_le
    left_size_le := coverage.left_size_le
    right_size_le := coverage.right_size_le }

/-- Every finite-head stair sequence embeds into the regular interface. -/
public def ActiveStairSequence.toRegular
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight width growth path}
    (sequence : ActiveStairSequence g initialLeft initialRight
      width growth path) :
    RegularActiveStairSequence g initialLeft initialRight width growth path := by
  let arguments := g.activePaddedArguments sequence.tails sequence.filler
  refine
    { arguments := arguments
      levels := sequence.levels
      levels_strictMono := sequence.levels_strictMono
      covered := ?_ }
  intro j
  obtain ⟨coverage⟩ := sequence.covered j
  have hwidth : sequence.tails.length = width := sequence.active_width
  let source : BoundedActiveSchemaCoverage g initialLeft initialRight
      (growth j) sequence.tails.length arguments
      (path.word (sequence.levels j)) :=
    coverage.toBoundedActiveSchemaCoverage
  have htype :
      BoundedActiveSchemaCoverage g initialLeft initialRight
          (growth j) sequence.tails.length arguments
            (path.word (sequence.levels j)) =
        BoundedActiveSchemaCoverage g initialLeft initialRight
          (growth j) width arguments (path.word (sequence.levels j)) :=
    congrArg (fun activeWidth =>
      BoundedActiveSchemaCoverage g initialLeft initialRight
        (growth j) activeWidth arguments (path.word (sequence.levels j)))
      hwidth
  exact ⟨htype.mp source⟩

/-- A finite-head active stair base supplies a regular active stair base of the
same width and growth function. -/
public theorem HasActiveStairBase.toRegular
    {g : EncodedFirstOrderGrammar Action} {width : ℕ}
    (hstair : g.HasActiveStairBase width) :
    g.HasRegularActiveStairBase width := by
  obtain ⟨growth, hstair⟩ := hstair
  refine ⟨growth, ?_⟩
  intro initialLeft initialRight hground hequivalent path
  rcases hstair initialLeft initialRight hground hequivalent path with
    hbounded | hsequence
  · exact Or.inl hbounded
  · obtain ⟨sequence⟩ := hsequence
    exact Or.inr ⟨sequence.toRegular⟩

/-- Width zero in the regular interface reaches the fixed bounded basis of
open-sound schemas on every path. -/
public theorem everyPathCoveredBy_of_regularActiveStairBase_zero
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {growth : ℕ → ℕ}
    (hstair :
      ∀ initialLeft initialRight,
        g.groundPairCode initialLeft initialRight = true →
        g.TraceEquivalent initialLeft initialRight →
        ∀ path : TracePath g initialLeft initialRight,
          g.EventuallyBoundedOpenSound initialLeft initialRight
            (growth 0) path ∨
          Nonempty (RegularActiveStairSequence g initialLeft initialRight
            0 growth path))
    {initialLeft initialRight : RegularTerm}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hequivalent : g.TraceEquivalent initialLeft initialRight) :
    g.EveryPathCoveredBy initialLeft initialRight
      (g.boundedOpenSoundBasis (growth 0)) := by
  intro path
  rcases hstair initialLeft initialRight hground hequivalent path with
    hbounded | hsequence
  · obtain ⟨n, ⟨coverage⟩⟩ := hbounded
    exact ⟨n, ⟨coverage.toBasisCoverage⟩⟩
  · obtain ⟨sequence⟩ := hsequence
    obtain ⟨bounded⟩ := sequence.covered 0
    let coverage := bounded.coverage
    have hopen : g.OpenSoundBasisPair coverage.schema :=
      coverage.openSoundPair_of_width_zero laws hequivalent
    have hmem : coverage.schema ∈
        g.boundedOpenSoundBasis (growth 0) := by
      apply (g.mem_boundedOpenSoundBasis_iff
        (growth 0) coverage.schema).mpr
      exact ⟨bounded.arity_le, bounded.left_size_le,
        bounded.right_size_le, hopen⟩
    refine ⟨sequence.levels 0, ⟨?_⟩⟩
    exact
      { left := coverage.left
        right := coverage.right
        derivation := coverage.derivation.rebasePair
        schema := coverage.schema
        schema_mem := hmem
        arguments := coverage.arguments
        word_nonempty := coverage.word_nonempty
        schema_wellFormed := coverage.schema_wellFormed
        argument_count := coverage.argument_count
        arguments_ground := coverage.arguments_ground
        left_matches := coverage.left_matches
        right_matches := coverage.right_matches }

/-- A zero-width regular active stair base yields direct root certificates over
one fixed original open-sound basis. -/
public theorem derivable_nop_of_regularActiveStairBase_zero
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    (hstair : g.HasRegularActiveStairBase 0) :
    ∃ bound,
      ∀ initialLeft initialRight,
        g.groundPairCode initialLeft initialRight = true →
        g.TraceEquivalent initialLeft initialRight →
        CertificateDerivable g initialLeft initialRight
          (g.boundedOpenSoundBasis bound) (.nop []) := by
  obtain ⟨growth, hstair⟩ := hstair
  refine ⟨growth 0, ?_⟩
  intro initialLeft initialRight hground hequivalent
  apply g.derivable_nop_of_everyPathCoveredBy laws hgroundSteps
    hground hequivalent
  exact everyPathCoveredBy_of_regularActiveStairBase_zero laws hstair
    hground hequivalent

end EncodedFirstOrderGrammar

end DCFEquivalence
