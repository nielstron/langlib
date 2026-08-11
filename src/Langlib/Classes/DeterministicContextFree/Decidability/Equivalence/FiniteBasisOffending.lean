module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OffendingWords
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisSemantics

@[expose]
public section

/-!
# Offending-word invariant for the finite-basis calculus

This is the shortest-counterexample half of Proposition 31 in
arXiv:1010.4760v4.  If a pair is derived at a prefix `u` of a shortest
distinguishing word, the remaining suffix is still a shortest distinguishing
word for that derived pair.  The limit-subterm case is the essential one: the
strictly shorter premise supplies enough finite trace agreement to tie the
replacement context into its regular limit without changing the counterexample.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private def OffendingInvariant
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) :
    CertificateJudgment Action → Prop
  | .pair word left right =>
      ∀ {suffix : List (Label Action)},
        g.OffendingWord initialLeft initialRight (word ++ suffix) →
          g.OffendingWord left right suffix
  | .nop _ => True
  | .fail => True

private theorem offendingInvariant_of_derivable
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment) :
    OffendingInvariant g initialLeft initialRight judgment := by
  induction h with
  | «axiom» hground =>
      intro suffix hinitial
      simpa using hinitial
  | @transition sourceWord sourceLeft sourceRight targetLeft targetRight
      label hsource happrox hleft hright hground ih =>
      intro suffix hinitial
      have hsourceOffending : g.OffendingWord sourceLeft sourceRight
          (label :: suffix) := by
        apply ih
        simpa [List.append_assoc]
          using hinitial
      exact hsourceOffending.tail hleft hright
  | @limit sourceWord shorterWord outerLeft outerRight shorterLeft
      shorterRight outerContext replacementContext focus houter hshorter
      houterContextCode hreplacementContextCode hfocusCode hnontrivial
      hlength houterMatchCode hshorterLeftCode hshorterRightCode hground
      ihOuter ihShorter =>
      intro suffix hinitial
      have houterOffending :
          g.OffendingWord outerLeft outerRight suffix :=
        ihOuter hinitial

      have hinitialApprox : g.TraceApprox
          (shorterWord.length + suffix.length) initialLeft initialRight := by
        apply g.traceApprox_anti (h := hinitial.traceApprox_pred)
        simp only [List.length_append]
        omega
      have hshorterApprox :
          g.TraceApprox suffix.length shorterLeft shorterRight :=
        hshorter.pairApproxInvariant laws suffix.length hinitialApprox

      have houterGround := groundPairCode_of_pair_derivable houter
      have hshorterGround := groundPairCode_of_pair_derivable hshorter
      have houterLeftClosed :=
        referenceClosed_of_groundPairCode_left g houterGround
      have hshorterLeftClosed :=
        referenceClosed_of_groundPairCode_left g hshorterGround
      have hshorterRightClosed :=
        referenceClosed_of_groundPairCode_right g hshorterGround
      have houterContext : outerContext.ReferenceClosed :=
        RegularTerm.referenceClosed_of_wellFormed houterContextCode
      have hreplacementContext : replacementContext.ReferenceClosed :=
        RegularTerm.referenceClosed_of_wellFormed hreplacementContextCode
      have hfocus : focus.ReferenceClosed :=
        RegularTerm.referenceClosed_of_ground
          ((RegularTerm.groundCode_eq_true_iff g.ranks focus).mp hfocusCode)
      have hreplacementFocus :
          (replacementContext.instantiate [focus]).ReferenceClosed :=
        RegularTerm.instantiate_singleton_referenceClosed
          hreplacementContext hfocus
      have houterFocus :
          (outerContext.instantiate [focus]).ReferenceClosed :=
        RegularTerm.instantiate_singleton_referenceClosed houterContext hfocus

      have houterMatch : g.TraceApprox suffix.length outerLeft
          (outerContext.instantiate [focus]) :=
        laws.traceApprox_of_unfoldingEquivalentCode suffix.length
          houterLeftClosed houterFocus houterMatchCode
      have hshorterLeft : g.TraceApprox suffix.length shorterLeft focus :=
        laws.traceApprox_of_unfoldingEquivalentCode suffix.length
          hshorterLeftClosed hfocus hshorterLeftCode
      have hshorterRight : g.TraceApprox suffix.length shorterRight
          (replacementContext.instantiate [focus]) :=
        laws.traceApprox_of_unfoldingEquivalentCode suffix.length
          hshorterRightClosed hreplacementFocus hshorterRightCode
      have hfocusUnfolding : g.TraceApprox suffix.length focus
          (replacementContext.instantiate [focus]) :=
        hshorterLeft.symm.trans (hshorterApprox.trans hshorterRight)
      have hfocusLimit :
          g.TraceApprox suffix.length focus replacementContext.unaryLimit :=
        laws.traceApprox_unaryLimit hreplacementContextCode hnontrivial hfocus
          suffix.length hfocusUnfolding
      have hcontexts : g.TraceApprox suffix.length
          (outerContext.instantiate [focus])
          (outerContext.instantiate [replacementContext.unaryLimit]) :=
        laws.congruent suffix.length outerContext focus
          replacementContext.unaryLimit houterContextCode hfocus
          (RegularTerm.unaryLimit_referenceClosed hreplacementContext)
          hfocusLimit
      exact houterOffending.replaceLeft (houterMatch.trans hcontexts)
  | @symmetry sourceWord sourceLeft sourceRight hsource ih =>
      intro suffix hinitial
      exact (ih hinitial).symm
  | basis => trivial
  | progression => trivial
  | rejection => trivial

/-- Every pair label produced by the finite-basis calculus preserves the exact
residual of a shortest distinguishing word. -/
public theorem CertificateDerivable.offendingResidual
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word : List (Label Action)} {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right)) :
    ∀ {suffix : List (Label Action)},
      g.OffendingWord initialLeft initialRight (word ++ suffix) →
        g.OffendingWord left right suffix :=
  offendingInvariant_of_derivable laws h

end EncodedFirstOrderGrammar

end DCFEquivalence
