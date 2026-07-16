module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedCompactedSchemaStair
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerWindowedTrajectoryInvariants
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerNormalForm
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerUniformBounds

@[expose]
public section

/-!
# A single quantitative premise for the marker-stable stair base

All qualitative branches of the critical-marker construction are already
available: a certificate-derived repeat gives a terminal original identity
schema, and an endpoint containing a fresh marker action gives a terminal
marker schema.  On the remaining marker-free, nonrepeating branch, the
canonical windowed pivot trajectory only needs pointwise compact guarded
schemas.

The canonical marker-free package already supplies the operational rebase,
guarded fixed-tail presentation, endpoint dichotomy, and initial `M₂` bound.
`HasUniformMarkerStableGuardedCompactionBound` is therefore the exact
remaining Proposition-49 contract: one pointwise compact guarded schema
family, with a depth recurrence independent of the marker count.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A certificate-derived repeat in a marker extension is already a terminal
marker-stable row over the original identity schema. -/
public theorem TracePath.eventuallyMarkerStableOpenSound_of_hasDerivedRepeat
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    (hrepeat : path.HasDerivedRepeat) :
    EventuallyMarkerStableOpenSound g count initialLeft initialRight
      g.criticalMarkerTerminalBound path := by
  let extended := g.withCriticalMarkers count
  obtain ⟨i, j, earlier, later, hij, hleft, hright⟩ := hrepeat
  have hlaterGround :=
    groundPairCode_of_pair_derivable later.derivation
  unfold groundPairCode at hlaterGround
  rw [Bool.and_eq_true] at hlaterGround
  have hleftGround : later.left.Ground extended.ranks :=
    (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
      hlaterGround.1
  have hrightGround : later.right.Ground extended.ranks :=
    (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
      hlaterGround.2
  have hvariableWellFormed :
      (RegularTerm.variableTerm 0).WellFormed extended.ranks 1 :=
    RegularTerm.variableTerm_wellFormed (by omega)
  have hleftInstance :
      ((RegularTerm.variableTerm 0).instantiate [later.left])
        |>.UnfoldingEquivalent later.left := by
    exact RegularTerm.instantiate_unfoldingEquivalent_argument
      (by simpa [RegularTerm.rootNode?] using
        RegularTerm.variableTerm_rootNode? 0)
      (by simp)
      (RegularTerm.referenceClosed_of_ground hleftGround)
  have hrightInstance :
      ((RegularTerm.variableTerm 0).instantiate [later.right])
        |>.UnfoldingEquivalent later.right := by
    exact RegularTerm.instantiate_unfoldingEquivalent_argument
      (by simpa [RegularTerm.rootNode?] using
        RegularTerm.variableTerm_rootNode? 0)
      (by simp)
      (RegularTerm.referenceClosed_of_ground hrightGround)
  obtain ⟨result, hresultDerivable, hresultMatch⟩ :=
    later.derivation.subtermReplacement earlier.derivation
      hvariableWellFormed hleftGround hrightGround
      (by simpa [path.word_length] using hij)
      hleftInstance.symm hleft hright
  let tails : List RegularTerm := [later.right]
  let filler := later.right
  let head : FiniteHead := .var 0
  let arguments := extended.activePaddedArguments tails filler
  have hargumentAt :
      arguments[0]? = some later.right := by
    simp [arguments, activePaddedArguments, tails]
  have hinstance :
      (head.toRegularTerm.instantiate arguments)
        |>.UnfoldingEquivalent later.right := by
    apply RegularTerm.instantiate_unfoldingEquivalent_argument
      (x := 0)
    · simpa [head, FiniteHead.toRegularTerm,
        RegularTerm.rootNode?] using
        RegularTerm.variableTerm_rootNode? 0
    · exact hargumentAt
    · exact RegularTerm.referenceClosed_of_ground hrightGround
  have hwordNonempty : path.word j ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    rw [path.word_length] at hlength
    simp at hlength
    omega
  let active : ActiveHeadCoverage extended
      initialLeft initialRight tails filler (path.word j) :=
    { leftHead := head
      rightHead := head
      left := result
      right := later.right
      derivation := hresultDerivable
      word_nonempty := hwordNonempty
      left_active := by simp [head, tails, FiniteHead.VariablesBelow]
      right_active := by simp [head, tails, FiniteHead.VariablesBelow]
      left_ranked := by simp [head, FiniteHead.RankedBy]
      right_ranked := by simp [head, FiniteHead.RankedBy]
      tails_ground := by
        intro tail htail
        have htailEq : tail = later.right := by
          simpa [tails] using htail
        subst tail
        exact hrightGround
      filler_ground := hrightGround
      left_matches := by
        apply (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        exact hresultMatch.trans
          (hrightInstance.trans hinstance.symm)
      right_matches := by
        apply (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        exact hinstance.symm }
  have harity :
      active.schema.arity = g.criticalMarkerTerminalBound := by
    change max tails.length (extended.ranks.foldr max 0) =
      max 1 (g.ranks.foldr max 0)
    rw [show extended.ranks.foldr max 0 =
        g.ranks.foldr max 0 by
      simpa [extended] using withCriticalMarkers_rankMax g count]
    simp [tails]
  let bounded : BoundedActiveHeadCoverage extended
      initialLeft initialRight g.criticalMarkerTerminalBound
      tails filler (path.word j) :=
    { active with
      arity_le := by rw [harity]
      left_size_le := by
        calc
          active.schema.left.nodes.length = 1 := by
            simp [active, ActiveHeadCoverage.schema, activeHeadPair,
              BasisPair.left, FiniteHead.toRegularTerm_nodes_length,
              head, FiniteHead.compiledNodeCount]
          _ ≤ g.criticalMarkerTerminalBound := Nat.le_max_left _ _
      right_size_le := by
        calc
          active.schema.right.nodes.length = 1 := by
            simp [active, ActiveHeadCoverage.schema, activeHeadPair,
              BasisPair.right, FiniteHead.toRegularTerm_nodes_length,
              head, FiniteHead.compiledNodeCount]
          _ ≤ g.criticalMarkerTerminalBound := Nat.le_max_left _ _ }
  let witnessed :=
    bounded.toBoundedWitnessedActiveSchemaCoverage
  have hschemaArity :
      witnessed.witnessed.coverage.schema.arity =
        g.criticalMarkerTerminalBound := by
    simpa [witnessed] using harity
  have hschemaLeft :
      witnessed.witnessed.coverage.schema.left =
        RegularTerm.variableTerm 0 := by
    simp [witnessed,
      BoundedActiveHeadCoverage.toBoundedWitnessedActiveSchemaCoverage,
      ActiveHeadCoverage.toWitnessedActiveSchemaCoverage,
      ActiveHeadCoverage.toActiveSchemaCoverage,
      ActiveHeadCoverage.schema, activeHeadPair, BasisPair.left,
      bounded, active, head, FiniteHead.toRegularTerm]
  have hschemaRight :
      witnessed.witnessed.coverage.schema.right =
        RegularTerm.variableTerm 0 := by
    simp [witnessed,
      BoundedActiveHeadCoverage.toBoundedWitnessedActiveSchemaCoverage,
      ActiveHeadCoverage.toWitnessedActiveSchemaCoverage,
      ActiveHeadCoverage.toActiveSchemaCoverage,
      ActiveHeadCoverage.schema, activeHeadPair, BasisPair.right,
      bounded, active, head, FiniteHead.toRegularTerm]
  have horiginalSchema :
      g.basisPairWellFormedCode
        witnessed.witnessed.coverage.schema = true := by
    have hpositive : 0 < g.criticalMarkerTerminalBound := by
      simp [criticalMarkerTerminalBound]
    unfold basisPairWellFormedCode
    rw [Bool.and_eq_true]
    constructor
    · rw [hschemaArity, hschemaLeft]
      exact RegularTerm.variableTerm_wellFormed hpositive
    · rw [hschemaArity, hschemaRight]
      exact RegularTerm.variableTerm_wellFormed hpositive
  let terminal :
      TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage
        g count initialLeft initialRight
        g.criticalMarkerTerminalBound tails.length arguments
          (path.word j) :=
    { bounded := witnessed
      original_schema_wellFormed := horiginalSchema }
  refine ⟨j, tails.length, arguments, terminal, ?_⟩
  change g.TraceEquivalent
    witnessed.witnessed.coverage.schema.left
    witnessed.witnessed.coverage.schema.right
  rw [hschemaLeft, hschemaRight]

/-- Exact count-independent quantitative output still required from
Proposition 49 on the marker-free branch.  All operational data is supplied
by `MarkerFreeGuardedProgressPresentation`; the premise asks only for the
pointwise compact guarded schemas. -/
@[expose] public def HasUniformMarkerStableGuardedCompactionBound
    (g : EncodedFirstOrderGrammar Action)
    (bound : ℕ) (schemaDepth : ℕ → ℕ) : Prop :=
  ∀ (hg : g.WellFormed)
    (count : ℕ)
    (initialLeft initialRight : RegularTerm)
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (_hnoRepeat : ¬path.HasDerivedRepeat)
    (initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound)
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (package :
      TracePath.StructuredPivotChain.MarkerFreeGuardedProgressPresentation
        (hg := hg) (filler := initialLeft) chain),
    ∀ j,
      Nonempty (GuardedFiniteSchemaCompaction g.ranks
        package.presentation.arity package.presentation.width
        package.presentation.depth (schemaDepth j)
        (g.CriticalBoundaryGuard count
          (g.criticalDepthPrefix package.presentation.depth
            package.rebase.base))
        (package.presentation.schema j))

/-- The guarded compacted recurrence supplies one uniform marker-stable stair
base.  Repeat and fresh-marker branches are terminal; the remaining branch is
assembled from the compact schemas and widened to original-grammar bounds. -/
public theorem
    hasUniformMarkerStableWitnessedRegularActiveStairBase_of_guardedCompactionBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (schemaDepth : ℕ → ℕ)
    (hm2 : g.HasUniformMarkerStableGuardedCompactionBound
      bound schemaDepth) :
    g.HasUniformMarkerStableWitnessedRegularActiveStairBase
      (g.criticalDepthPrefixTailBound bound) := by
  let targetWidth := g.criticalDepthPrefixTailBound bound
  let targetArity := max targetWidth (g.ranks.foldr max 0)
  let rowBound : ℕ → ℕ := fun j =>
    g.criticalMarkerFixedBalancingPresentationBound
      bound targetArity
      (RegularTerm.finiteSchemaNodeBound
        g.ranks (schemaDepth j))
  let growth : ℕ → ℕ := fun j =>
    max g.criticalMarkerTerminalBound (rowBound j)
  refine ⟨growth, ?_⟩
  intro count initialLeft initialRight hground hinitial path
  let extended := g.withCriticalMarkers count
  let hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  let hnormalExtended : extended.ExposingNormalForm :=
    g.withCriticalMarkers_exposingNormalForm hnormal count
  have hexposureExtended :
      extended.exposureBound hnormalExtended ≤ bound :=
    (g.withCriticalMarkers_exposureBound_le hnormal count).trans
      hexposureBound
  by_cases hrepeat : path.HasDerivedRepeat
  · exact Or.inl
      ((path.eventuallyMarkerStableOpenSound_of_hasDerivedRepeat hrepeat)
        |>.mono (by
          dsimp [growth]
          exact Nat.le_max_left _ _))
  · let source : path.DerivedPairAt 0 :=
      { left := initialLeft
        right := initialRight
        derivation := by
          simpa [path.starts_word] using
            (CertificateDerivable.axiom
              (basis := ([] : List BasisPair)) hground) }
    obtain ⟨initial⟩ :=
      source.exists_initialStructuredBalancingState
        hgExtended hnormalExtended hground hinitial hrepeat
        hexposureExtended
    obtain ⟨chain⟩ :=
      path.exists_structuredPivotChain_of_noDerivedRepeat
        hnormalExtended hrepeat hexposureExtended initial
    let windowed := chain.toWindowedPivotTrajectory
    have hleftGround : initialLeft.Ground extended.ranks := by
      unfold groundPairCode at hground
      rw [Bool.and_eq_true] at hground
      exact
        (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
          hground.1
    rcases
        chain
          |>.eventuallyMarkerStableOpenSound_or_exists_markerFreeGuardedProgressPresentation
            hg hnormalExtended hground hinitial hexposureExtended
            hrepeat hleftGround with
      heventually | hpackage
    · exact Or.inl (heventually.mono (by
        dsimp [growth]
        exact Nat.le_max_left _ _))
    · obtain ⟨package⟩ := hpackage
      have compactions :=
        hm2 hg count initialLeft initialRight path
          hground hinitial hrepeat initial chain package
      let presentation := package.presentation
      let rebase := package.rebase
      have hpresentationDepth :
          presentation.depth = bound := by
        exact package.depth_eq
      have hpresentationDepthLe :
          bound ≤ presentation.depth := by
        omega
      have hwidth :
          presentation.width ≤ targetWidth := by
        dsimp [targetWidth]
        simpa [hpresentationDepth] using
          presentation.width_le_criticalDepthPrefixTailBound
      have harity :
          presentation.arity ≤ targetArity := by
        dsimp [targetArity, targetWidth]
        simpa [hpresentationDepth] using
          presentation.arity_le_uniform
      have htargetWidth : targetWidth ≤ targetArity := by
        dsimp [targetArity]
        exact Nat.le_max_left _ _
      let stair :=
        chain
          |>.toMarkerStableWitnessedRegularActiveStairSequence_of_guardedProgressCompactedSchemas_widened
            hg hnormalExtended hground hinitial
            hexposureExtended windowed.toPivotTrajectory rebase
            presentation hpresentationDepthLe schemaDepth
            (fun j => Classical.choice (compactions j))
            (fun j =>
              package.endpoint_noMarkerActions (rebase.start + j))
            hwidth harity htargetWidth
      refine Or.inr ⟨
        { arguments := stair.arguments
          levels := stair.levels
          levels_strictMono := stair.levels_strictMono
          covered := ?_ }⟩
      intro j
      obtain ⟨coverage⟩ := stair.covered j
      refine ⟨coverage.mono ?_⟩
      have hlocal :
          (extended.fixedBalancingPresentationBound
              bound presentation.arity
              (RegularTerm.finiteSchemaNodeBound
                g.ranks (schemaDepth j))) ≤
            rowBound j := by
        apply
          (g.withCriticalMarkers_fixedBalancingPresentationBound_le
            count bound presentation.arity
              (RegularTerm.finiteSchemaNodeBound
                g.ranks (schemaDepth j))).trans
        exact
          g.criticalMarkerFixedBalancingPresentationBound_mono_arity
            bound
            (RegularTerm.finiteSchemaNodeBound
              g.ranks (schemaDepth j))
            harity
      have hwidened :
          max targetArity
              (extended.fixedBalancingPresentationBound
                bound presentation.arity
                (RegularTerm.finiteSchemaNodeBound
                  g.ranks (schemaDepth j))) ≤
            rowBound j := by
        apply max_le
        · unfold rowBound
          unfold criticalMarkerFixedBalancingPresentationBound
          exact Nat.le_max_left _ _
        · exact hlocal
      exact hwidened.trans (Nat.le_max_right _ _)

end EncodedFirstOrderGrammar

end DCFEquivalence
