module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotPrefixResidual
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationSupport

@[expose]
public section

/-!
# Pivot residuals over an already fixed argument tuple

The first balancing result compiles a concrete pivot through its own depth
prefix.  Along the later pivot path, however, every pivot is already presented
as a schema over one fixed tuple of boundary tails.  If that schema has enough
protected application depth, the concrete pivot run reflects to a symbolic
run of the schema and retains the same prefix-support invariant.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A concrete run from an instance of a sufficiently deep prefix-supported
schema reflects to a supported symbolic residual over the same arguments. -/
public theorem exists_supportedSchemaResidual
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema concrete target : RegularTerm}
    {arguments : List RegularTerm} {arity width : ℕ}
    {word : List Action}
    (hsupported : RegularTerm.SupportedByPrefix g.ranks
      arity width schema)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hdepth : schema.ApplicationDepth word.length)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hinstance : (schema.instantiate arguments).UnfoldingEquivalent
      concrete)
    (hconcreteClosed : concrete.ReferenceClosed)
    (hrun : g.runActions? word concrete = some target) :
    ∃ residual,
      g.runActions? word schema = some residual ∧
      (residual.instantiate arguments).UnfoldingEquivalent target ∧
      arguments.length = arity ∧
      RegularTerm.SupportedByPrefix g.ranks arity width residual ∧
      residual.nodes.length ≤
        g.residualNodeBound word.length schema.nodes.length := by
  have hschemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hsupported.1
  have hinstanceClosed := RegularTerm.instantiate_referenceClosed
    hschemaClosed hargumentsClosed
  obtain ⟨instanceTarget, hinstanceRun, htargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hg hinstance
      hinstanceClosed hconcreteClosed hrun
  obtain ⟨residual, hsymbolic, hresidualInstance⟩ :=
    g.runActions?_reflects_instantiation_equivalent hg
      word ⟨arity, hsupported.1⟩ hdepth
      hargumentsClosed hinstanceRun
  have hresidualSupported :=
    hsupported.residual hg hpadding hsymbolic
  have hsize : residual.nodes.length ≤
      g.residualNodeBound word.length schema.nodes.length := by
    exact g.runActions?_nodes_length_le hg
      ⟨arity, hsupported.1⟩ (le_refl _) hsymbolic
  exact ⟨residual, hsymbolic,
    hresidualInstance.trans htargetEquivalent,
    hargumentsLength, hresidualSupported, hsize⟩

/-- The symbolic pivot residual obtained from a pre-existing deep schema over
fixed arguments. -/
public structure BalancingSegment.SchemaPivotResidual
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {filler : RegularTerm}
    (activeResult : segment.ActivePrefixResidual filler)
    (pivotSchema : RegularTerm) (arguments : List RegularTerm)
    (arity width : ℕ) where
  residual : RegularTerm
  symbolic_run :
    g.runActions? activeResult.actions pivotSchema = some residual
  instance_matches :
    (residual.instantiate arguments).UnfoldingEquivalent
      segment.pivotTarget
  argument_count : arguments.length = arity
  supported :
    RegularTerm.SupportedByPrefix g.ranks arity width residual
  hasPrefixWitness : residual.HasPrefixWitness width
  size_le :
    residual.nodes.length ≤
      g.residualNodeBound activeResult.actions.length
        pivotSchema.nodes.length

/-- A sufficiently deep, prefix-supported presentation of the concrete pivot
can be followed symbolically under the balancing word while retaining the
same fixed arguments. -/
public theorem BalancingSegment.exists_schemaPivotResidual
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {active pivot : RegularTerm}
    {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {filler : RegularTerm}
    (activeResult : segment.ActivePrefixResidual filler)
    {pivotSchema : RegularTerm} {arguments : List RegularTerm}
    {arity width : ℕ}
    (hsupported : RegularTerm.SupportedByPrefix g.ranks
      arity width pivotSchema)
    (hpivotWitness : pivotSchema.HasPrefixWitness width)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hdepth : pivotSchema.ApplicationDepth
      activeResult.actions.length)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hinstance : (pivotSchema.instantiate arguments).UnfoldingEquivalent
      pivot)
    (hpivotClosed : pivot.ReferenceClosed) :
    Nonempty (segment.SchemaPivotResidual activeResult
      pivotSchema arguments arity width) := by
  have hpivotRun :
      g.runActions? activeResult.actions pivot =
        some segment.pivotTarget := by
    simpa [runActions?, activeResult.labels_eq] using segment.pivot_run
  obtain ⟨residual, hsymbolic, hresidualInstance,
      hargumentCount, hresidualSupported, hsize⟩ :=
    exists_supportedSchemaResidual hg hsupported hpadding hdepth
      hargumentsLength hargumentsClosed hinstance hpivotClosed hpivotRun
  have hresidualWitness : residual.HasPrefixWitness width :=
    hpivotWitness.runActions hg hpadding hsupported.1 hsymbolic
  exact ⟨
    { residual := residual
      symbolic_run := hsymbolic
      instance_matches := hresidualInstance
      argument_count := hargumentCount
      supported := hresidualSupported
      hasPrefixWitness := hresidualWitness
      size_le := hsize }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
