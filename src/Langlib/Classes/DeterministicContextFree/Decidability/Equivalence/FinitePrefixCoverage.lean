module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FinitePrefixExecution
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveExposure

@[expose]
public section

/-!
# Bounded finite-prefix residuals

This file packages Observation 20 in the form needed by the balancing
construction.  A concrete run of length at most `depth` is represented by a
symbolic residual of the compiled depth prefix.  The residual remains
supported by the genuine boundary tuple, and both its arity and raw graph size
have grammar-uniform bounds.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A bounded concrete run factors through a bounded residual schema supported
by the genuine tails of the source depth prefix. -/
public theorem exists_depthPrefix_supported_residual
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler target : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) {word : List Action}
    (hlength : word.length ≤ depth)
    (hrun : g.runActions? word term = some target) :
    ∃ residual,
      g.runActions? word
          (term.depthPrefix depth).head.toRegularTerm = some residual ∧
      RegularTerm.UnfoldingEquivalent
        (residual.instantiate
          ((term.depthPrefix depth).paddedArguments g.ranks filler)) target ∧
      RegularTerm.SupportedByPrefix g.ranks
        ((term.depthPrefix depth).schemaArity g.ranks)
        (term.depthPrefix depth).tails.length residual ∧
      (term.depthPrefix depth).schemaArity g.ranks ≤
        max (RegularTerm.depthPrefixTailBound g.ranks depth)
          (g.ranks.foldr max 0) ∧
      residual.nodes.length ≤
        g.residualNodeBound word.length
          (FiniteHead.compiledDepthBound
            (g.ranks.foldr max 0) depth) := by
  obtain ⟨residual, hsymbolic, hinstance⟩ :=
    exists_depthPrefix_residual hg hterm hfiller depth hlength hrun
  let decomposition := term.depthPrefix depth
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid term depth
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hterm depth
  have hinitialSupported :
      RegularTerm.SupportedByPrefix g.ranks
        (decomposition.schemaArity g.ranks) decomposition.tails.length
        decomposition.head.toRegularTerm := by
    simpa [decomposition, DepthPrefix.schemaArity] using
      (FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked)
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  have hresidualSupported :
      RegularTerm.SupportedByPrefix g.ranks
        (decomposition.schemaArity g.ranks) decomposition.tails.length
        residual :=
    hinitialSupported.residual hg hpadding hsymbolic
  have harity :
      decomposition.schemaArity g.ranks ≤
        max (RegularTerm.depthPrefixTailBound g.ranks depth)
          (g.ranks.foldr max 0) := by
    simpa [decomposition] using
      RegularTerm.depthPrefix_schemaArity_le hterm depth
  have hinitialSize :
      decomposition.head.toRegularTerm.nodes.length ≤
        FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) depth := by
    simpa [decomposition] using
      RegularTerm.depthPrefix_schema_nodes_length_le hterm depth
  have hresidualSize :
      residual.nodes.length ≤
        g.residualNodeBound word.length
          (FiniteHead.compiledDepthBound
            (g.ranks.foldr max 0) depth) := by
    apply g.runActions?_nodes_length_le hg
      ⟨decomposition.schemaArity g.ranks, hinitialSupported.1⟩
      hinitialSize hsymbolic
  refine ⟨residual, hsymbolic, hinstance, ?_, ?_, hresidualSize⟩
  · simpa [decomposition] using hresidualSupported
  · simpa [decomposition] using harity

end EncodedFirstOrderGrammar

end DCFEquivalence
