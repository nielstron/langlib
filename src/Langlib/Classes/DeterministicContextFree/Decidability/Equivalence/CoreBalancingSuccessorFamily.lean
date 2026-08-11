module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingSuccessorFamily

@[expose]
public section

/-!
# Exposable-core successor rows for balancing

The global exposing-normal-form hypothesis is stronger than Proposition 45
needs at the one-row level.  A row only needs its own exposing witness, and
the grammar-wide `coreExposureBound` bounds the selected witness at every such
position.

The partial family below is indexed only by exposable positions belonging to
the active root.  It deliberately does not manufacture rows for unexposable
children; those positions require the semantic independence argument before
the existing full-prefix certificate replacement can be reused.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The shorter Proposition-45 row at one position of the exposable core. -/
public theorem BalancingSegment.exists_coreExposedSuccessorResult
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} (hexposureBound : g.coreExposureBound ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    {filler : RegularTerm} (hfiller : filler.Ground g.ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    (position : g.ExposablePosition)
    {children : List ℕ} {child : ℕ}
    (hroot :
      active.rootApplication? = some (position.1.1.val, children))
    (hchild : children[position.1.2.val]? = some child) :
    Nonempty (BalancingSegment.ExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      segment stem filler child) := by
  let word := g.coreExposingWord position.1
  have hwordExposure : g.ExposesSuccessor position.1 word :=
    g.coreExposingWord_exposes position
  have hwordLength : word.length < bound :=
    lt_of_lt_of_le
      (g.coreExposingWord_length_lt_coreExposureBound position)
      hexposureBound
  obtain ⟨activeTarget, pivotTarget, hactiveRun,
      hactiveMatches, hpivotRun⟩ :=
    segment.exists_pivotTarget_for_exposedSuccessor
      hg hactive position.1 hwordExposure hwordLength hroot hchild
  have hderivation :
      CertificateDerivable g initialLeft initialRight []
        (.pair (stem ++ word.map Sum.inl) activeTarget pivotTarget) :=
    houter.follow_runActions
      (preservesGroundSteps_of_wellFormed hg) hequivalent
      hactiveRun hpivotRun
  obtain ⟨pivotResidual, hpivotSymbolic, hpivotInstance,
      hpivotSupported, hpivotArity, hpivotSize⟩ :=
    exists_depthPrefix_supported_residual hg hpivot hfiller
      bound (Nat.le_of_lt hwordLength) hpivotRun
  exact ⟨
    { word := word
      word_exposes := ⟨position.1, hwordExposure⟩
      word_length_lt := hwordLength
      activeTarget := activeTarget
      pivotTarget := pivotTarget
      active_run := hactiveRun
      active_matches := hactiveMatches
      pivot_run := hpivotRun
      shorter_derivation := hderivation
      pivotResidual := pivotResidual
      pivot_symbolic_run := hpivotSymbolic
      pivot_instance_matches := hpivotInstance
      pivot_supported := hpivotSupported
      pivot_arity_le := hpivotArity
      pivot_size_le := hpivotSize }⟩

/-- The canonical formal successor belonging to one concrete child of a
ranked root symbol. -/
@[expose] public def rootSuccessorPosition
    (g : EncodedFirstOrderGrammar Action)
    (symbol : Fin g.ranks.length) (children : List ℕ)
    (hrank : g.ranks.get symbol = children.length)
    (index : Fin children.length) : g.SuccessorPosition :=
  ⟨symbol, ⟨index.val, by
    rw [hrank]
    exact index.isLt⟩⟩

/-- Concrete root-child indices whose canonical formal successor belongs to
the exposable core. -/
public def RootExposableIndex
    (g : EncodedFirstOrderGrammar Action)
    (symbol : Fin g.ranks.length) (children : List ℕ)
    (hrank : g.ranks.get symbol = children.length) :=
  { index : Fin children.length //
    ∃ word, g.ExposesSuccessor
      (g.rootSuccessorPosition symbol children hrank index) word }

/-- The exposable-position package selected by a core root index. -/
@[expose] public def RootExposableIndex.position
    {g : EncodedFirstOrderGrammar Action}
    {symbol : Fin g.ranks.length} {children : List ℕ}
    {hrank : g.ranks.get symbol = children.length}
    (index : RootExposableIndex g symbol children hrank) :
    g.ExposablePosition :=
  ⟨g.rootSuccessorPosition symbol children hrank index.1, index.2⟩

/-- The concrete child selected by a core root index. -/
@[expose] public def RootExposableIndex.child
    {g : EncodedFirstOrderGrammar Action}
    {symbol : Fin g.ranks.length} {children : List ℕ}
    {hrank : g.ranks.get symbol = children.length}
    (index : RootExposableIndex g symbol children hrank) : ℕ :=
  children[index.1.val]

/-- One shorter row for every exposable successor of the concrete active
root, with no field at unexposable successors. -/
public structure BalancingSegment.CoreExposedSuccessorFamily
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {initialLeft initialRight : RegularTerm}
    (stem : List (Label Action)) (filler : RegularTerm)
    (symbol : Fin g.ranks.length) (children : List ℕ)
    (hrank : g.ranks.get symbol = children.length) where
  row : ∀ index : RootExposableIndex g symbol children hrank,
    BalancingSegment.ExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      segment stem filler index.child

/-- Select the complete partial family of core rows at the active root. -/
public theorem BalancingSegment.exists_coreExposedSuccessorFamily
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} (hexposureBound : g.coreExposureBound ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    {filler : RegularTerm} (hfiller : filler.Ground g.ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    {symbol : Fin g.ranks.length} {children : List ℕ}
    (hrank : g.ranks.get symbol = children.length)
    (hroot : active.rootApplication? = some (symbol.val, children)) :
    Nonempty (segment.CoreExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler symbol children hrank) := by
  classical
  have hexists :
      ∀ index : RootExposableIndex g symbol children hrank,
        Nonempty (BalancingSegment.ExposedSuccessorResult
          (initialLeft := initialLeft) (initialRight := initialRight)
          segment stem filler index.child) := by
    intro index
    apply segment.exists_coreExposedSuccessorResult hg hexposureBound
      hactive hpivot hfiller houter hequivalent index.position
    · exact hroot
    · simp [RootExposableIndex.position, RootExposableIndex.child,
        rootSuccessorPosition]
  exact ⟨
    { row := fun index => Classical.choice (hexists index) }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
