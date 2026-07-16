module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailBalancingStairAssembly

@[expose]
public section

/-!
# Grammar-uniform envelopes for fixed-tail presentations

Once Proposition 49 has rebased its pivot path and chosen the fixed depth
`M₀`, the number of genuine tails and the padded arity are bounded solely by
the grammar.  If the word reaching the `j`th retained pivot also has a uniform
length bound, the step-monotone residual envelope supplies the corresponding
uniform graph-size bound.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Grammar-wide upper bound for the active width at one chosen prefix depth. -/
@[expose] public def fixedTailWidthBound
    (g : EncodedFirstOrderGrammar Action) (depth : ℕ) : ℕ :=
  RegularTerm.depthPrefixTailBound g.ranks depth

/-- Grammar-wide upper bound for the padded arity at one chosen prefix depth. -/
@[expose] public def fixedTailArityBound
    (g : EncodedFirstOrderGrammar Action) (depth : ℕ) : ℕ :=
  max (g.fixedTailWidthBound depth) (g.ranks.foldr max 0)

/-- Uniform schema-size envelope for a fixed-tail residual reached within the
supplied action budget. -/
@[expose] public def fixedTailSchemaBound
    (g : EncodedFirstOrderGrammar Action)
    (depth actionBound : ℕ) : ℕ :=
  g.residualNodeEnvelope actionBound
    (FiniteHead.compiledDepthBound
      (g.ranks.foldr max 0) depth)

namespace FixedTailPivotPresentation

public theorem width_le_fixedTailWidthBound
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation : FixedTailPivotPresentation
      g base filler labels pivots) :
    presentation.width ≤ g.fixedTailWidthBound presentation.depth := by
  exact RegularTerm.depthPrefix_tails_length_le
    presentation.base_ground presentation.depth

public theorem arity_le_fixedTailArityBound
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation : FixedTailPivotPresentation
      g base filler labels pivots) :
    presentation.arity ≤ g.fixedTailArityBound presentation.depth := by
  exact RegularTerm.depthPrefix_schemaArity_le
    presentation.base_ground presentation.depth

/-- A pointwise action-length estimate turns the path-local residual bound into
one grammar-uniform envelope. -/
public theorem schema_nodes_length_le_fixedTailSchemaBound
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation : FixedTailPivotPresentation
      g base filler labels pivots)
    (j actionBound : ℕ)
    (hactions : (presentation.actions j).length ≤ actionBound) :
    (presentation.schema j).nodes.length ≤
      g.fixedTailSchemaBound presentation.depth actionBound := by
  exact (presentation.schema_size_le j).trans
    (g.residualNodeBound_le_residualNodeEnvelope_of_le
      hactions (le_refl _))

end FixedTailPivotPresentation

end EncodedFirstOrderGrammar

end DCFEquivalence
