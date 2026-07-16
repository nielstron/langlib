module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SubtermReplacement
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.UnarySpecialization

@[expose]
public section

/-!
# Replacing one argument inside a derived schema instance

The ordinary subterm-replacement certificate acts on a unary context.  Unary
specialization turns an arbitrary open schema into just such a context by
freezing every argument except the selected slot.  This file packages the two
constructions into the positional replacement rule used by balancing-result
composition.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Replace one argument of a derived schema instance using a strictly shorter
derived pair. -/
public theorem CertificateDerivable.replaceArgument
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word shorterWord : List (Label Action)}
    {outerLeft outerRight shorterLeft shorterRight : RegularTerm}
    {schema replacement : RegularTerm} {arguments : List RegularTerm}
    {x : ℕ}
    (houter : CertificateDerivable g initialLeft initialRight basis
      (.pair word outerLeft outerRight))
    (hshorter : CertificateDerivable g initialLeft initialRight basis
      (.pair shorterWord shorterLeft shorterRight))
    (hschema : schema.WellFormed g.ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (hx : x < arguments.length)
    (hreplacement : replacement.Ground g.ranks)
    (hlength : shorterWord.length < word.length)
    (houterLeft : outerLeft.UnfoldingEquivalent
      (schema.instantiate arguments))
    (hshorterLeft : shorterLeft.UnfoldingEquivalent arguments[x])
    (hshorterRight : shorterRight.UnfoldingEquivalent replacement) :
    ∃ result,
      CertificateDerivable g initialLeft initialRight basis
        (.pair word result outerRight) ∧
      result.UnfoldingEquivalent
        (schema.instantiate
          (RegularTerm.replaceArgument arguments x replacement)) := by
  have hfocusGround : arguments[x].Ground g.ranks :=
    harguments arguments[x] (List.getElem_mem hx)
  have hspecialized :
      (RegularTerm.unarySpecialization schema arguments x).WellFormed
        g.ranks 1 :=
    RegularTerm.unarySpecialization_wellFormed hschema harguments
  have houterMatch : outerLeft.UnfoldingEquivalent
      ((RegularTerm.unarySpecialization schema arguments x).instantiate
        [arguments[x]]) :=
    houterLeft.trans
      (RegularTerm.unarySpecialization_instantiate_unfoldingEquivalent
        hschema hx harguments).symm
  obtain ⟨result, hresult, hresultEquivalent⟩ :=
    houter.subtermReplacement hshorter hspecialized hfocusGround
      hreplacement hlength houterMatch hshorterLeft hshorterRight
  refine ⟨result, hresult, hresultEquivalent.trans ?_⟩
  exact RegularTerm.unarySpecialization_instantiate_focus
    hschema hx harguments
      (RegularTerm.referenceClosed_of_ground hreplacement)

end EncodedFirstOrderGrammar

end DCFEquivalence
