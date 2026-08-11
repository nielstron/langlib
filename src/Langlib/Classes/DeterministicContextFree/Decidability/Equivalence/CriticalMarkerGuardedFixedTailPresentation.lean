module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaNoVariableReflection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OperationalFixedTailPresentation

@[expose]
public section

/-!
# Marker-aware fixed-tail presentations

This is the critical-marker analogue of `FixedTailPivotPresentation`.
Fresh-marker roots are cut into the fixed argument tuple, so the common
source schema and every symbolic residual remain well formed over the
original rank table.  The residual also carries the guarded-depth invariant:
variables above the cutoff can only denote fresh marker arguments.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One marker-aware residual over the common critical-prefix argument
tuple. -/
public structure CriticalGuardedFixedTailResidual
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (term filler : RegularTerm) (depth : ℕ)
    (word : List (Action ⊕ ℕ)) (target : RegularTerm) where
  residual : RegularTerm
  symbolic_run :
    (g.withCriticalMarkers count).runActions? word
      (g.criticalDepthPrefix depth term).head.toRegularTerm =
        some residual
  noVariableBefore :
    (g.withCriticalMarkers count).NoVariableBefore
      (g.criticalDepthPrefix depth term).head.toRegularTerm word
  instance_matches :
    (residual.instantiate
      ((g.criticalDepthPrefix depth term)
        |>.paddedArguments g.ranks filler))
      |>.UnfoldingEquivalent target
  supported :
    RegularTerm.SupportedByPrefix
      (g.withCriticalMarkers count).ranks
      ((g.criticalDepthPrefix depth term).schemaArity g.ranks)
      (g.criticalDepthPrefix depth term).tails.length residual
  hasPrefixWitness :
    residual.HasPrefixWitness
      (g.criticalDepthPrefix depth term).tails.length
  guarded :
    residual.GuardedApplicationDepth
      (g.CriticalBoundaryGuard count
        (g.criticalDepthPrefix depth term))
      depth
  wellFormed_original :
    residual.WellFormed g.ranks
      ((g.criticalDepthPrefix depth term).schemaArity g.ranks)
  size_le :
    residual.nodes.length ≤
      (g.withCriticalMarkers count).residualNodeBound word.length
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) depth)

/-- A lifted-original, fixed-base non-sinking run has a marker-aware
guarded residual. -/
public theorem exists_criticalGuardedFixedTailResidual
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {term filler target : RegularTerm}
    (hterm : term.Ground (g.withCriticalMarkers count).ranks)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) (hdepth : 0 < depth)
    (originalActions : List Action)
    (hrun :
      (g.withCriticalMarkers count).runActions?
        (originalActions.map Sum.inl) term = some target)
    (hnever :
      (g.withCriticalMarkers count).NeverSinksFromBase term
        (originalActions.map Sum.inl)) :
    Nonempty (CriticalGuardedFixedTailResidual
      g count term filler depth
      (originalActions.map Sum.inl) target) := by
  let extended := g.withCriticalMarkers count
  let decomposition := g.criticalDepthPrefix depth term
  let schema := decomposition.head.toRegularTerm
  let arguments :=
    decomposition.paddedArguments g.ranks filler
  have hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have hvalid : decomposition.Valid :=
    g.criticalDepthPrefix_valid term depth
  have hrankedOriginal : decomposition.head.RankedBy g.ranks :=
    g.criticalDepthPrefix_head_rankedBy_original hterm depth
  have hrankedExtended :
      decomposition.head.RankedBy extended.ranks := by
    simpa [extended, withCriticalMarkers_ranks] using
      hrankedOriginal.appendRanks
  have hschemaSupported :
      RegularTerm.SupportedByPrefix extended.ranks
        (decomposition.schemaArity g.ranks)
        decomposition.tails.length schema := by
    have hsource :=
      FiniteHead.toRegularTerm_supportedByPrefix
        hvalid hrankedExtended
    have hrankMax :
        extended.ranks.foldr max 0 =
          g.ranks.foldr max 0 := by
      simpa [extended] using
        g.withCriticalMarkers_rankMax count
    rw [hrankMax] at hsource
    simpa [schema, DepthPrefix.schemaArity] using hsource
  have hpaddingExtended :
      extended.ranks.foldr max 0 ≤
        decomposition.schemaArity g.ranks := by
    rw [show extended.ranks.foldr max 0 =
        g.ranks.foldr max 0 by
      simpa [extended] using
        g.withCriticalMarkers_rankMax count]
    simp [DepthPrefix.schemaArity]
  have hpaddingOriginal :
      g.ranks.foldr max 0 ≤
        decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  have hargumentsGround :
      ∀ argument ∈ arguments,
        argument.Ground extended.ranks :=
    g.criticalDepthPrefix_paddedArguments_ground
      hterm hfiller depth
  have hargumentsClosed :
      ∀ argument ∈ arguments,
        argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent term :=
    g.criticalDepthPrefix_compiled_unfoldingEquivalent
      hterm hfiller depth
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed
        hschemaSupported.1)
      hargumentsClosed
  obtain ⟨instanceTarget, hinstanceRun,
      hinstanceTargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hgExtended
      hinstanceEquivalent hinstanceClosed
      (RegularTerm.referenceClosed_of_ground hterm) hrun
  have hnoVariable :
      extended.NoVariableBefore schema
        (originalActions.map Sum.inl) := by
    simpa [schema, decomposition, extended] using
      g.criticalDepthPrefix_noVariableBefore_of_neverSinksFromBase
        hg hterm hfiller depth hdepth originalActions rfl hrun hnever
  obtain ⟨residual, hsymbolic, hresidualInstance⟩ :=
    extended.runActions?_reflects_instantiation_of_noVariableBefore
      hgExtended (originalActions.map Sum.inl)
      ⟨_, hschemaSupported.1⟩ hargumentsClosed
      hinstanceRun hnoVariable
  have hresidualSupported :=
    hschemaSupported.residual hgExtended
      hpaddingExtended hsymbolic
  have hsourceWitness :
      schema.HasPrefixWitness decomposition.tails.length :=
    FiniteHead.toRegularTerm_hasPrefixWitness hvalid
  have hresidualWitness :=
    hsourceWitness.runActions hgExtended
      hpaddingExtended hschemaSupported.1 hsymbolic
  have hguarded :
      residual.GuardedApplicationDepth
        (g.CriticalBoundaryGuard count decomposition) depth := by
    simpa [schema, decomposition, extended] using
      g.criticalDepthPrefix_residual_guardedApplicationDepth_of_neverSinksFromBase
        hg hterm depth hsymbolic hnever
  have hsourceOriginal :
      schema.WellFormed g.ranks
        (decomposition.schemaArity g.ranks) := by
    simpa [schema, decomposition] using
      g.criticalDepthPrefix_head_wellFormed_original
        hterm depth
  have hresidualOriginal :
      residual.WellFormed g.ranks
        (decomposition.schemaArity g.ranks) :=
    runActions?_preserves_wellFormed_original
      hg hsourceOriginal hpaddingOriginal hsymbolic
  have hinitialSize :
      schema.nodes.length ≤
        FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) depth := by
    simpa [schema, decomposition] using
      g.criticalDepthPrefix_schema_nodes_length_le
        hterm depth
  have hsize :=
    extended.runActions?_nodes_length_le hgExtended
      ⟨decomposition.schemaArity g.ranks,
        hschemaSupported.1⟩
      hinitialSize hsymbolic
  exact ⟨
    { residual := residual
      symbolic_run := by
        simpa [schema, decomposition, extended] using hsymbolic
      noVariableBefore := by
        simpa [schema, decomposition, extended] using hnoVariable
      instance_matches := by
        simpa [arguments, decomposition] using
          hresidualInstance.trans hinstanceTargetEquivalent
      supported := by
        simpa [decomposition, extended] using hresidualSupported
      hasPrefixWitness := by
        simpa [schema, decomposition] using hresidualWitness
      guarded := by
        simpa [decomposition] using hguarded
      wellFormed_original := by
        simpa [decomposition] using hresidualOriginal
      size_le := by
        simpa [decomposition, extended] using hsize }⟩

/-- An infinite family of marker-aware residual schemas over one fixed
argument tuple. -/
public structure CriticalGuardedFixedTailPivotPresentation
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (base filler : RegularTerm)
    (labels : ℕ → List (Label (Action ⊕ ℕ)))
    (pivots : ℕ → RegularTerm) where
  depth : ℕ
  depth_positive : 0 < depth
  base_ground : base.Ground (g.withCriticalMarkers count).ranks
  filler_ground : filler.Ground (g.withCriticalMarkers count).ranks
  originalActions : ℕ → List Action
  labels_eq : ∀ j,
    labels j =
      ((originalActions j).map Sum.inl).map Sum.inl
  neverSinks : ∀ j,
    (g.withCriticalMarkers count).NeverSinksFromBase base
      ((originalActions j).map Sum.inl)
  residual : ∀ j,
    CriticalGuardedFixedTailResidual g count base filler depth
      ((originalActions j).map Sum.inl) (pivots j)

namespace CriticalGuardedFixedTailPivotPresentation

variable {g : EncodedFirstOrderGrammar Action} {count : ℕ}
  {base filler : RegularTerm}
  {labels : ℕ → List (Label (Action ⊕ ℕ))}
  {pivots : ℕ → RegularTerm}

@[expose] public def width
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) : ℕ :=
  (g.criticalDepthPrefix presentation.depth base).tails.length

@[expose] public def arity
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) : ℕ :=
  (g.criticalDepthPrefix presentation.depth base).schemaArity g.ranks

@[expose] public def arguments
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) :
    List RegularTerm :=
  (g.criticalDepthPrefix presentation.depth base)
    |>.paddedArguments g.ranks filler

@[expose] public def actions
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) : List (Action ⊕ ℕ) :=
  (presentation.originalActions j).map Sum.inl

@[expose] public def schema
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) : RegularTerm :=
  (presentation.residual j).residual

@[simp] public theorem arguments_length
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) :
    presentation.arguments.length = presentation.arity := by
  simp [arguments, arity]

public theorem arguments_ground
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) :
    ∀ argument ∈ presentation.arguments,
      argument.Ground (g.withCriticalMarkers count).ranks :=
  g.criticalDepthPrefix_paddedArguments_ground
    presentation.base_ground presentation.filler_ground
    presentation.depth

public theorem labels_eq_actions
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) :
    labels j = (presentation.actions j).map Sum.inl :=
  presentation.labels_eq j

public theorem actions_eq_original
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) :
    presentation.actions j =
      (presentation.originalActions j).map Sum.inl := rfl

public theorem schema_instance_matches
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) :
    ((presentation.schema j).instantiate presentation.arguments)
      |>.UnfoldingEquivalent (pivots j) :=
  (presentation.residual j).instance_matches

public theorem schema_supported
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) :
    RegularTerm.SupportedByPrefix
      (g.withCriticalMarkers count).ranks
      presentation.arity presentation.width
      (presentation.schema j) :=
  (presentation.residual j).supported

public theorem schema_hasPrefixWitness
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) :
    (presentation.schema j).HasPrefixWitness presentation.width :=
  (presentation.residual j).hasPrefixWitness

public theorem schema_guarded
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) :
    (presentation.schema j).GuardedApplicationDepth
      (g.CriticalBoundaryGuard count
        (g.criticalDepthPrefix presentation.depth base))
      presentation.depth :=
  (presentation.residual j).guarded

public theorem schema_wellFormed_original
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) :
    (presentation.schema j).WellFormed g.ranks presentation.arity :=
  (presentation.residual j).wellFormed_original

public theorem rankMax_le_arity
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) :
    (g.withCriticalMarkers count).ranks.foldr max 0 ≤
      presentation.arity := by
  rw [g.withCriticalMarkers_rankMax count]
  simp [arity, DepthPrefix.schemaArity]

public theorem width_le_arity
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) :
    presentation.width ≤ presentation.arity := by
  simp [width, arity, DepthPrefix.schemaArity]

public theorem width_le_criticalDepthPrefixTailBound
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) :
    presentation.width ≤
      g.criticalDepthPrefixTailBound presentation.depth :=
  g.criticalDepthPrefix_tails_length_le
    presentation.base_ground presentation.depth

public theorem arity_le_uniform
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots) :
    presentation.arity ≤
      max (g.criticalDepthPrefixTailBound presentation.depth)
        (g.ranks.foldr max 0) :=
  g.criticalDepthPrefix_schemaArity_le
    presentation.base_ground presentation.depth

public theorem schema_size_le
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    (j : ℕ) :
    (presentation.schema j).nodes.length ≤
      (g.withCriticalMarkers count).residualNodeBound
        (presentation.actions j).length
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) presentation.depth) :=
  (presentation.residual j).size_le

end CriticalGuardedFixedTailPivotPresentation

/-- Generic family construction from lifted-original non-sinking words. -/
public theorem
    exists_criticalGuardedFixedTailPivotPresentation_atDepth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {base filler : RegularTerm}
    {labels : ℕ → List (Label (Action ⊕ ℕ))}
    {pivots : ℕ → RegularTerm}
    (hbase : base.Ground (g.withCriticalMarkers count).ranks)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) (hdepth : 0 < depth)
    (hruns : ∀ j,
      (g.withCriticalMarkers count).run? (labels j) base =
        some (pivots j))
    (horiginal : ∀ j, ∃ originalActions : List Action,
      labels j =
        (originalActions.map Sum.inl).map Sum.inl)
    (hnever : ∀ j (originalActions : List Action),
      labels j =
          (originalActions.map Sum.inl).map Sum.inl →
        (g.withCriticalMarkers count).NeverSinksFromBase base
          (originalActions.map Sum.inl)) :
    ∃ presentation : CriticalGuardedFixedTailPivotPresentation
        g count base filler labels pivots,
      presentation.depth = depth := by
  classical
  choose originalActions hlabels using horiginal
  have hresidual : ∀ j,
      CriticalGuardedFixedTailResidual g count base filler depth
        ((originalActions j).map Sum.inl) (pivots j) := by
    intro j
    have hrunActions :
        (g.withCriticalMarkers count).runActions?
          ((originalActions j).map Sum.inl) base =
            some (pivots j) := by
      simpa [runActions?, ← hlabels j] using hruns j
    exact Classical.choice
      (exists_criticalGuardedFixedTailResidual
        hg hbase hfiller depth hdepth (originalActions j)
        hrunActions (hnever j (originalActions j) (hlabels j)))
  let presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots :=
    { depth := depth
      depth_positive := hdepth
      base_ground := hbase
      filler_ground := hfiller
      originalActions := originalActions
      labels_eq := hlabels
      neverSinks := fun j =>
        hnever j (originalActions j) (hlabels j)
      residual := hresidual }
  exact ⟨presentation, rfl⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
