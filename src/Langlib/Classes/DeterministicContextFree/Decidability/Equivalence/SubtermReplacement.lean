module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GroundConstantContexts

@[expose]
public section

/-!
# Ordinary subterm replacement as a limit-rule instance

The certificate calculus stores only the general limit-subterm replacement
rule.  Its ordinary replacement special case uses the replacement term as a
constant unary context.  `sanitizeUnary` makes that context structurally
well-formed without changing its reachable ground unfolding.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Replace one focused ground subterm using a strictly earlier derived pair.
The concrete conclusion contains the sanitized constant context's unary-limit
graph; the second conjunct identifies it with the expected direct
replacement up to equality of unfoldings. -/
public theorem CertificateDerivable.subtermReplacement
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word shorterWord : List (Label Action)}
    {outerLeft outerRight shorterLeft shorterRight : RegularTerm}
    {outerContext focus replacement : RegularTerm}
    (houter : CertificateDerivable g initialLeft initialRight basis
      (.pair word outerLeft outerRight))
    (hshorter : CertificateDerivable g initialLeft initialRight basis
      (.pair shorterWord shorterLeft shorterRight))
    (houterContext : outerContext.WellFormed g.ranks 1)
    (hfocus : focus.Ground g.ranks)
    (hreplacement : replacement.Ground g.ranks)
    (hlength : shorterWord.length < word.length)
    (houterMatch : outerLeft.UnfoldingEquivalent
      (outerContext.instantiate [focus]))
    (hshorterLeft : shorterLeft.UnfoldingEquivalent focus)
    (hshorterRight : shorterRight.UnfoldingEquivalent replacement) :
    ∃ result,
      CertificateDerivable g initialLeft initialRight basis
        (.pair word result outerRight) ∧
      result.UnfoldingEquivalent
        (outerContext.instantiate [replacement]) := by
  let replacementContext := replacement.sanitizeUnary
  let replacementLimit := replacementContext.unaryLimit
  let result := outerContext.instantiate [replacementLimit]
  have hreplacementContext : replacementContext.WellFormed g.ranks 1 :=
    RegularTerm.sanitizeUnary_wellFormed_of_shape hreplacement.1
  have hnontrivial : replacementContext.nontrivialUnaryCode = true :=
    hreplacement.sanitizeUnary_nontrivial
  have hlimitGround : replacementLimit.Ground g.ranks :=
    RegularTerm.unaryLimit_ground hreplacementContext hnontrivial
  have hresultGround : result.Ground g.ranks :=
    RegularTerm.instantiate_singleton_ground houterContext hlimitGround
  have houterGround := groundPairCode_of_pair_derivable houter
  have houterRightGround : outerRight.Ground g.ranks := by
    unfold groundPairCode at houterGround
    rw [Bool.and_eq_true] at houterGround
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp houterGround.2
  have hgroundResult : g.groundPairCode result outerRight = true := by
    unfold groundPairCode
    rw [Bool.and_eq_true]
    exact ⟨(RegularTerm.groundCode_eq_true_iff g.ranks _).mpr hresultGround,
      (RegularTerm.groundCode_eq_true_iff g.ranks _).mpr houterRightGround⟩
  have hreplacementInstance :
      (replacementContext.instantiate [focus]).UnfoldingEquivalent
        replacement :=
    hreplacement.sanitizeUnary_instantiate_unfoldingEquivalent
      (RegularTerm.referenceClosed_of_ground hfocus)
  have hderivation : CertificateDerivable g initialLeft initialRight basis
      (.pair word result outerRight) := by
    apply CertificateDerivable.limit houter hshorter
      houterContext hreplacementContext
      ((RegularTerm.groundCode_eq_true_iff g.ranks focus).mpr hfocus)
      hnontrivial hlength
    · exact (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        houterMatch
    · exact (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        hshorterLeft
    · exact (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        (hshorterRight.trans hreplacementInstance.symm)
    · exact hgroundResult
  have hlimitEquivalent : replacementLimit.UnfoldingEquivalent replacement :=
    hreplacement.sanitizeUnary_unaryLimit_unfoldingEquivalent
  have hresultEquivalent : result.UnfoldingEquivalent
      (outerContext.instantiate [replacement]) := by
    apply RegularTerm.instantiate_unfoldingEquivalent
      (RegularTerm.referenceClosed_of_wellFormed houterContext)
    · exact .cons hlimitEquivalent .nil
    · intro argument hargument
      simp only [List.mem_singleton] at hargument
      subst argument
      exact RegularTerm.referenceClosed_of_ground hlimitGround
    · intro argument hargument
      simp only [List.mem_singleton] at hargument
      subst argument
      exact RegularTerm.referenceClosed_of_ground hreplacement
  exact ⟨result, hderivation, hresultEquivalent⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
