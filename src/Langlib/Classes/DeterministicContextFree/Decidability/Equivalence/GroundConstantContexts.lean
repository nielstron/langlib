module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TracePathRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.UnaryFixedPointUniqueness

@[expose]
public section

/-!
# Ground terms as constant unary contexts

The ordinary subterm-replacement case of the certificate limit rule treats a
ground replacement term as a unary context which ignores its parameter.
Runtime graphs may retain unreachable variables with arbitrary indices, so we
first sanitize that garbage to the sole unary variable.  Ground reachability
then guarantees that the sanitized root is an application, and tying its
unreachable parameter leaves the denoted ground term unchanged.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Sanitizing a ground term produces a syntactically nontrivial unary
context. -/
public theorem Ground.sanitizeUnary_nontrivial
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) :
    term.sanitizeUnary.nontrivialUnaryCode = true := by
  obtain ⟨support, _hsupport, hwitness⟩ := hground.2
  obtain ⟨X, children, hroot, _hchildren⟩ :=
    hwitness.2 term.root hwitness.1
  unfold nontrivialUnaryCode rootNode?
  rw [sanitizeUnary_root, sanitizeUnary_nodeAt?, hroot]
  rfl

/-- A sanitized ground term remains semantically constant when instantiated
at its unary parameter. -/
public theorem Ground.sanitizeUnary_instantiate_unfoldingEquivalent
    {ranks : List ℕ} {term argument : RegularTerm}
    (hground : term.Ground ranks)
    (hargument : argument.ReferenceClosed) :
    (term.sanitizeUnary.instantiate [argument]).UnfoldingEquivalent term :=
  (hground.hasUnaryWitness.sanitizeUnary_instantiate_unfoldingEquivalent
    hargument).trans (hground.instantiate_unfoldingEquivalent [argument])

/-- Closing the unary parameter of a sanitized ground term preserves its
denoted regular tree. -/
public theorem Ground.sanitizeUnary_unaryLimit_unfoldingEquivalent
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) :
    term.sanitizeUnary.unaryLimit.UnfoldingEquivalent term := by
  apply unaryLimit_unfoldingEquivalent_of_fixedPoint
    (sanitizeUnary_wellFormed_of_shape hground.1)
    hground.sanitizeUnary_nontrivial
    (referenceClosed_of_ground hground)
  exact hground.sanitizeUnary_instantiate_unfoldingEquivalent
    (referenceClosed_of_ground hground)

end RegularTerm

end DCFEquivalence
