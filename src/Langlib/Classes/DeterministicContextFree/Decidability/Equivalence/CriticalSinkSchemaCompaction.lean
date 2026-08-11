module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerCancellation
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteSchemaCompaction

@[expose]
public section

/-!
# Compacting the protected endpoint of a critical sink branch

The `M₂` sink branch naturally produces two open schemas:

* the actual fixed-tail residual, which retains the full protected
  application depth and the active-prefix witness; and
* an auxiliary descended schema, whose unfolding depth has the desired
  quantitative upper bound.

Their arbitrary ground instances cannot be cancelled.  The critical-marker
tuple is faithful, so equivalence of the two critical instances identifies
the open schemas.  The auxiliary upper bound can then be transferred to the
actual schema, after which finite-schema compaction discards unreachable
graph garbage without losing the actual schema's protected structure.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A finite compaction which also retains the full protected application
depth required by the balancing construction. -/
public structure ProtectedFiniteSchemaCompaction
    (ranks : List ℕ) (arity width guardDepth depth : ℕ)
    (schema : RegularTerm)
    extends RegularTerm.FiniteSchemaCompaction
      ranks arity width depth schema where
  applicationDepth : compact.ApplicationDepth guardDepth

/-- Critical-instance cancellation combines the actual schema's protected
lower-depth invariant with the auxiliary schema's quantitative upper-depth
invariant, and then compacts the result to a grammar-uniform raw graph bound. -/
public theorem exists_protectedFiniteSchemaCompaction_of_criticalInstances
    {g : EncodedFirstOrderGrammar Action}
    {arity width guardDepth depth : ℕ}
    {actual auxiliary : RegularTerm}
    (hactual : actual.WellFormed g.ranks arity)
    (hauxiliary : auxiliary.WellFormed g.ranks arity)
    (hwitness : actual.HasPrefixWitness width)
    (hwidth : width ≤ arity)
    (hrankMax : g.ranks.foldr max 0 ≤ arity)
    (hprotected : actual.ApplicationDepth guardDepth)
    (hauxiliaryDepth :
      auxiliary.UnfoldingDepthAtMost depth)
    (hcritical :
      (actual.instantiate (g.criticalArguments arity))
        |>.UnfoldingEquivalent
          (auxiliary.instantiate (g.criticalArguments arity))) :
    Nonempty (ProtectedFiniteSchemaCompaction g.ranks
      arity width guardDepth depth actual) := by
  have hopen : actual.UnfoldingEquivalent auxiliary :=
    g.unfoldingEquivalent_of_criticalInstantiation
      hactual hauxiliary hcritical
  have hactualDepth : actual.UnfoldingDepthAtMost depth :=
    hopen.symm.unfoldingDepthAtMost hauxiliaryDepth
  obtain ⟨compaction⟩ :=
    RegularTerm.exists_finiteSchemaCompaction
      hactual hwitness hwidth hrankMax hactualDepth
  exact ⟨
    { toFiniteSchemaCompaction := compaction
      applicationDepth :=
        compaction.equivalent.symm.applicationDepth hprotected }⟩

/-- Convenience form when the auxiliary branch carries executable finiteness
and a raw node bound rather than an explicit semantic unfolding-depth bound. -/
public theorem
    exists_protectedFiniteSchemaCompaction_of_criticalInstances_of_nodes
    {g : EncodedFirstOrderGrammar Action}
    {arity width guardDepth depth : ℕ}
    {actual auxiliary : RegularTerm}
    (hactual : actual.WellFormed g.ranks arity)
    (hauxiliary : auxiliary.WellFormed g.ranks arity)
    (hwitness : actual.HasPrefixWitness width)
    (hwidth : width ≤ arity)
    (hrankMax : g.ranks.foldr max 0 ≤ arity)
    (hprotected : actual.ApplicationDepth guardDepth)
    (hauxiliaryFinite : auxiliary.UnfoldsFinite)
    (hauxiliarySize : auxiliary.nodes.length ≤ depth)
    (hcritical :
      (actual.instantiate (g.criticalArguments arity))
        |>.UnfoldingEquivalent
          (auxiliary.instantiate (g.criticalArguments arity))) :
    Nonempty (ProtectedFiniteSchemaCompaction g.ranks
      arity width guardDepth depth actual) := by
  apply g.exists_protectedFiniteSchemaCompaction_of_criticalInstances
    hactual hauxiliary hwitness hwidth hrankMax hprotected
  · exact RegularTerm.UnfoldingDepthAtMost.mono
      hauxiliaryFinite.unfoldingDepthAtMost_nodes hauxiliarySize
  · exact hcritical

end EncodedFirstOrderGrammar

end DCFEquivalence
