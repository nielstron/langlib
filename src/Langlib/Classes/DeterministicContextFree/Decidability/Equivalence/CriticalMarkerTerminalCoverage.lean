module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerStructuredPivotInvariants

@[expose]
public section

/-!
# Terminal coverage after a critical marker

Terminal coverage may use a path word containing fresh marker actions.  Once a
marker action occurs, both sides of a common ground trace step become the same
fresh nullary marker.  They can therefore be represented by the single
original schema variable `x₀`, instantiated with that marker.  The resulting
presentation bound depends only on the original maximum rank, not on the
marker index or extension count.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A successful fresh-marker step from a ground term necessarily uses an
installed marker and produces that exact nullary marker. -/
public theorem withCriticalMarkers_markerStep_target
    (g : EncodedFirstOrderGrammar Action)
    (count marker : ℕ) {source target : RegularTerm}
    (hsource : source.Ground (g.withCriticalMarkers count).ranks)
    (hstep : (g.withCriticalMarkers count).step?
      (.inl (.inr marker)) source = some target) :
    marker < count ∧ target = g.criticalMarker marker := by
  let extended := g.withCriticalMarkers count
  obtain ⟨X, children, hroot⟩ := hsource.exists_rootApplication
  have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
  have hshape := hsource.1
  unfold RegularTerm.ShapeWellFormed
    RegularTerm.shapeWellFormedCode at hshape
  rw [Bool.and_eq_true] at hshape
  have hnodeMem :
      (.inr (X, children) : RawNode) ∈ source.nodes :=
    List.mem_of_getElem? hrootNode
  have hnodeWell :=
    (List.all_eq_true.mp hshape.2) _ hnodeMem
  unfold RegularTerm.nodeShapeWellFormedCode at hnodeWell
  cases hrank : extended.ranks[X]? with
  | none =>
      change (match extended.ranks[X]? with
        | none => false
        | some rank =>
            decide (children.length = rank) &&
              children.all fun child =>
                decide (child < source.nodes.length)) = true at hnodeWell
      rw [hrank] at hnodeWell
      contradiction
  | some rank =>
      have hXextended : X < extended.ranks.length :=
        (List.getElem?_eq_some_iff.mp hrank).1
      have hchildrenLength : children.length = rank := by
        change (match extended.ranks[X]? with
          | none => false
          | some rank =>
              decide (children.length = rank) &&
                children.all fun child =>
                  decide (child < source.nodes.length)) = true at hnodeWell
        rw [hrank] at hnodeWell
        rw [Bool.and_eq_true] at hnodeWell
        exact of_decide_eq_true hnodeWell.1
      change extended.rootRewrite? (.inr marker) source =
          some target at hstep
      unfold rootRewrite? at hstep
      rw [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ :=
        Option.map_eq_some_iff.mp hstep
      by_cases hXoriginal : X < g.ranks.length
      · rw [withCriticalMarkers_ruleLookup_markerAction_originalSymbol
          g count marker X hXoriginal] at hrule
        contradiction
      · let i := X - g.ranks.length
        have hi : i < count := by
          have hlength :
              extended.ranks.length = g.ranks.length + count := by
            simp [extended, withCriticalMarkers_ranks]
          rw [hlength] at hXextended
          dsimp [i]
          omega
        have hX : X = g.criticalMarkerSymbol i := by
          unfold criticalMarkerSymbol
          dsimp [i]
          omega
        rw [hX, withCriticalMarkers_ruleLookup_fresh] at hrule
        have hvalid : i = marker ∧ i < count := by
          by_contra hnot
          rw [if_neg hnot] at hrule
          contradiction
        rw [if_pos hvalid] at hrule
        have hrhs : rhs = g.criticalMarker i :=
          Option.some.inj hrule.symm
        subst rhs
        have hmarkerRank :
            extended.ranks[g.criticalMarkerSymbol i]? = some 0 := by
          change (g.ranks ++ List.replicate count 0)[
              g.ranks.length + i]? = some 0
          rw [List.getElem?_append_right (by omega)]
          simp [hi]
        have hrankZero : rank = 0 := by
          rw [hX, hmarkerRank] at hrank
          exact Option.some.inj hrank.symm
        have hchildren : children = [] := by
          apply List.length_eq_zero_iff.mp
          omega
        subst children
        constructor
        · simpa [← hvalid.1] using hi
        · rw [← hvalid.1]
          simpa using htarget.symm

/-- Uniform presentation bound for the terminal schema `x₀ = x₀`. -/
@[expose] public def criticalMarkerTerminalBound
    (g : EncodedFirstOrderGrammar Action) : ℕ :=
  max 1 (g.ranks.foldr max 0)

/-- One common marker step yields terminal original-schema coverage.  The
schema is `x₀ = x₀`, instantiated with the reached marker; hence its bound is
independent of both the marker index and extension count. -/
public theorem TracePath.eventuallyMarkerStableOpenSound_of_markerStep
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (n marker : ℕ)
    (hleft : (g.withCriticalMarkers count).step?
      (.inl (.inr marker)) (path.left n) =
        some (path.left (n + 1)))
    (hright : (g.withCriticalMarkers count).step?
      (.inl (.inr marker)) (path.right n) =
        some (path.right (n + 1))) :
    EventuallyMarkerStableOpenSound g count
      initialLeft initialRight g.criticalMarkerTerminalBound path := by
  let extended := g.withCriticalMarkers count
  let hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  let hgroundSteps : extended.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hgExtended
  have hpairGround :=
    path.residual_ground hgroundSteps hground n
  unfold groundPairCode at hpairGround
  rw [Bool.and_eq_true] at hpairGround
  have hleftGround : (path.left n).Ground extended.ranks :=
    (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
      hpairGround.1
  have hrightGround : (path.right n).Ground extended.ranks :=
    (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
      hpairGround.2
  obtain ⟨hmarkerCount, hleftTarget⟩ :=
    g.withCriticalMarkers_markerStep_target
      count marker hleftGround hleft
  obtain ⟨_hmarkerCountRight, hrightTarget⟩ :=
    g.withCriticalMarkers_markerStep_target
      count marker hrightGround hright
  let tails : List RegularTerm := [g.criticalMarker marker]
  let filler := initialLeft
  let head : FiniteHead := .var 0
  let arguments := extended.activePaddedArguments tails filler
  have hfiller : filler.Ground extended.ranks := by
    unfold groundPairCode at hground
    rw [Bool.and_eq_true] at hground
    exact (RegularTerm.groundCode_eq_true_iff extended.ranks _).mp
      hground.1
  have hmarkerGround :
      (g.criticalMarker marker).Ground extended.ranks :=
    g.criticalMarker_ground hmarkerCount
  have hargumentAt :
      arguments[0]? = some (g.criticalMarker marker) := by
    simp [arguments, activePaddedArguments, tails]
  have hinstance :
      (head.toRegularTerm.instantiate arguments)
        |>.UnfoldingEquivalent (g.criticalMarker marker) := by
    apply RegularTerm.instantiate_unfoldingEquivalent_argument
      (x := 0)
    · simpa [head, FiniteHead.toRegularTerm,
        RegularTerm.rootNode?] using
        RegularTerm.variableTerm_rootNode? 0
    · exact hargumentAt
    · exact RegularTerm.referenceClosed_of_ground hmarkerGround
  have hwordNonempty : path.word (n + 1) ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    rw [path.word_length] at hlength
    simp at hlength
  let active : ActiveHeadCoverage extended
      initialLeft initialRight tails filler (path.word (n + 1)) :=
    { leftHead := head
      rightHead := head
      left := path.left (n + 1)
      right := path.right (n + 1)
      derivation := path.pair_derivable hgroundSteps
        hground hinitial (n + 1)
      word_nonempty := hwordNonempty
      left_active := by simp [head, tails, FiniteHead.VariablesBelow]
      right_active := by simp [head, tails, FiniteHead.VariablesBelow]
      left_ranked := by simp [head, FiniteHead.RankedBy]
      right_ranked := by simp [head, FiniteHead.RankedBy]
      tails_ground := by
        intro tail htail
        have htailEq : tail = g.criticalMarker marker := by
          simpa [tails] using htail
        subst tail
        exact hmarkerGround
      filler_ground := hfiller
      left_matches := by
        apply (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        rw [hleftTarget]
        exact hinstance.symm
      right_matches := by
        apply (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        rw [hrightTarget]
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
      tails filler (path.word (n + 1)) :=
    { active with
      arity_le := by rw [harity]
      left_size_le := by
        calc
          active.schema.left.nodes.length = 1 := by
            simp [active, ActiveHeadCoverage.schema, activeHeadPair,
              BasisPair.left,
              FiniteHead.toRegularTerm_nodes_length, head,
              FiniteHead.compiledNodeCount]
          _ ≤ g.criticalMarkerTerminalBound := by
            exact Nat.le_max_left _ _
      right_size_le := by
        calc
          active.schema.right.nodes.length = 1 := by
            simp [active, ActiveHeadCoverage.schema, activeHeadPair,
              BasisPair.right,
              FiniteHead.toRegularTerm_nodes_length, head,
              FiniteHead.compiledNodeCount]
          _ ≤ g.criticalMarkerTerminalBound := by
            exact Nat.le_max_left _ _ }
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
          (path.word (n + 1)) :=
    { bounded := witnessed
      original_schema_wellFormed := horiginalSchema }
  refine ⟨n + 1, tails.length, arguments, terminal, ?_⟩
  change g.TraceEquivalent
    witnessed.witnessed.coverage.schema.left
    witnessed.witnessed.coverage.schema.right
  rw [hschemaLeft, hschemaRight]

/-- A marker action in an accumulated trace word occurred at an exact earlier
common step of the trace path. -/
public theorem TracePath.exists_markerStep_of_mem_word
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    {n marker : ℕ}
    (hmem :
      (.inl (.inr marker) : Label (Action ⊕ ℕ)) ∈ path.word n) :
    ∃ k < n,
      (g.withCriticalMarkers count).step?
          (.inl (.inr marker)) (path.left k) =
        some (path.left (k + 1)) ∧
      (g.withCriticalMarkers count).step?
          (.inl (.inr marker)) (path.right k) =
        some (path.right (k + 1)) := by
  induction n with
  | zero =>
      rw [path.starts_word] at hmem
      simp at hmem
  | succ n ih =>
      obtain ⟨label, hword, hleft, hright⟩ := path.step n
      have hsplit :
          (.inl (.inr marker) : Label (Action ⊕ ℕ)) ∈ path.word n ∨
            (.inl (.inr marker) : Label (Action ⊕ ℕ)) = label := by
        rw [hword] at hmem
        simpa using hmem
      rcases hsplit with hprior | hcurrent
      · obtain ⟨k, hk, hkleft, hkright⟩ := ih hprior
        exact ⟨k, hk.trans (Nat.lt_succ_self n), hkleft, hkright⟩
      · subst label
        exact ⟨n, Nat.lt_succ_self n, hleft, hright⟩

/-- Once any fresh marker action appears in a trace prefix, that prefix has
already reached the uniform terminal original-schema alternative. -/
public theorem TracePath.eventuallyMarkerStableOpenSound_of_markerAction_mem
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    {n marker : ℕ}
    (hmem :
      (.inl (.inr marker) : Label (Action ⊕ ℕ)) ∈ path.word n) :
    EventuallyMarkerStableOpenSound g count
      initialLeft initialRight g.criticalMarkerTerminalBound path := by
  obtain ⟨k, _hk, hleft, hright⟩ :=
    path.exists_markerStep_of_mem_word hmem
  exact path.eventuallyMarkerStableOpenSound_of_markerStep
    hg hground hinitial k marker hleft hright

/-- The marker endpoint remains available under any larger global bound. -/
public theorem TracePath.eventuallyMarkerStableOpenSound_of_markerAction_mem_mono
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    {n marker bound : ℕ}
    (hmem :
      (.inl (.inr marker) : Label (Action ⊕ ℕ)) ∈ path.word n)
    (hbound : g.criticalMarkerTerminalBound ≤ bound) :
    EventuallyMarkerStableOpenSound g count
      initialLeft initialRight bound path :=
  (path.eventuallyMarkerStableOpenSound_of_markerAction_mem
    hg hground hinitial hmem).mono hbound

namespace TracePath.StructuredPivotChain

/-- On a structured suffix, a fresh marker action closes the terminal branch;
otherwise endpoint marker-freeness supplies every marker-stable premise except
the explicitly retained fixed-base symbol invariant. -/
public theorem eventuallyMarkerStableOpenSound_or_markerFreeSuffix
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count) hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (trajectory : chain.PivotTrajectory)
    (rebase : trajectory.MaximalExposureRebase)
    {filler : RegularTerm}
    (presentation : FixedTailPivotPresentation
      (g.withCriticalMarkers count)
      rebase.base filler rebase.labels
      (fun j => trajectory.representatives (rebase.start + j)))
    (hpositive : 0 < bound)
    (hbase :
      (rebase.base.depthPrefix presentation.depth).head.SymbolsBelow
        g.ranks.length)
    {globalBound : ℕ}
    (hterminal :
      g.criticalMarkerTerminalBound ≤ globalBound) :
    EventuallyMarkerStableOpenSound g count
        initialLeft initialRight globalBound path ∨
      MarkerFreeStructuredPivotSuffix
        (hg := hg) chain trajectory rebase presentation := by
  rcases chain.endpointMarkerActionDichotomy
      (hg := hg) rebase.start with
      hnoMarker | ⟨j, marker, hmarker⟩
  · exact Or.inr
      (MarkerFreeStructuredPivotSuffix.of_endpointNoMarkerActions
        hpositive hbase hnoMarker)
  · exact Or.inl
      (path.eventuallyMarkerStableOpenSound_of_markerAction_mem_mono
        (n := chain.levels (rebase.start + j))
        (marker := marker) (bound := globalBound)
        hg hground hinitial hmarker hterminal)

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
