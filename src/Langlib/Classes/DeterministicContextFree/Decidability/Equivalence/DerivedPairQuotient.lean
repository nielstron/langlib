module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisSemantics
public import Langlib.Utilities.LanguageOperations

@[expose]
public section

/-!
# Trace quotients of certificate-derived pairs

Jančar's Proposition 31(3) says that, from an equivalent initial pair, every
pair derived at a word `u` has exactly the `u`-left quotient of the initial
trace language on both sides.  This is stronger than merely knowing that the
two derived components are trace equivalent: it lets a fixed continuation of
the original trace be resumed after limit-subterm replacement and balancing.

The result below is stated for an arbitrary basis.  Pair judgments are
generated only by the primary rules, so the basis cannot affect this
invariant.  The empty-basis specialization used by the balancing path is an
immediate instance.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Deterministic execution identifies the target trace language with the
left quotient of the source trace language by the executed word. -/
public theorem traceLanguage_eq_leftQuotient_of_run
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm}
    {word : List (Label Action)}
    (hrun : g.run? word source = some target) :
    g.traceLanguage target = word \\ g.traceLanguage source := by
  ext suffix
  change g.IsTrace target suffix ↔
    g.IsTrace source (word ++ suffix)
  unfold IsTrace
  rw [g.run?_append, hrun]
  rfl

private def PairQuotientProperty
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft : RegularTerm) :
    CertificateJudgment Action → Prop
  | .pair word left right =>
      g.traceLanguage left =
          word \\ g.traceLanguage initialLeft ∧
        g.traceLanguage right =
          word \\ g.traceLanguage initialLeft
  | .nop _ => True
  | .fail => True

private theorem pairQuotientProperty_of_derivable
    {g : EncodedFirstOrderGrammar Action}
    (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm}
    {basis : List BasisPair}
    {judgment : CertificateJudgment Action}
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (h : CertificateDerivable g initialLeft initialRight basis judgment) :
    PairQuotientProperty g initialLeft judgment := by
  induction h with
  | «axiom» =>
      simp only [PairQuotientProperty, Language.nil_leftQuotient]
      exact ⟨trivial, hinitial.symm⟩
  | @transition word left right left' right' label hpair _happrox
      hleft hright _hground ih =>
      simp only [PairQuotientProperty] at ih ⊢
      have hleftRun : g.run? [label] left = some left' := by
        simp [hleft]
      have hrightRun : g.run? [label] right = some right' := by
        simp [hright]
      constructor
      · calc
          g.traceLanguage left' =
              [label] \\ g.traceLanguage left :=
            traceLanguage_eq_leftQuotient_of_run hleftRun
          _ = [label] \\
              (word \\ g.traceLanguage initialLeft) := by
            rw [ih.1]
          _ = (word ++ [label]) \\
              g.traceLanguage initialLeft := by
            rw [Language.append_leftQuotient]
      · calc
          g.traceLanguage right' =
              [label] \\ g.traceLanguage right :=
            traceLanguage_eq_leftQuotient_of_run hrightRun
          _ = [label] \\
              (word \\ g.traceLanguage initialLeft) := by
            rw [ih.2]
          _ = (word ++ [label]) \\
              g.traceLanguage initialLeft := by
            rw [Language.append_leftQuotient]
  | @limit word shorterWord outerLeft outerRight shorterLeft shorterRight
      outerContext replacementContext focus houter hshorter
      houterContext hreplacementContext hfocus hnontrivial hlength
      houterMatch hshorterLeft hshorterRight hground ihOuter _ihShorter =>
      simp only [PairQuotientProperty] at ihOuter ⊢
      let hresult : CertificateDerivable g initialLeft initialRight basis
          (.pair word
            (outerContext.instantiate [replacementContext.unaryLimit])
            outerRight) :=
        .limit houter hshorter houterContext hreplacementContext
          hfocus hnontrivial hlength houterMatch
          hshorterLeft hshorterRight hground
      have hequivalent :
          g.TraceEquivalent
            (outerContext.instantiate [replacementContext.unaryLimit])
            outerRight :=
        hresult.pair_traceEquivalent_of_initial laws hinitial
      exact ⟨Eq.trans hequivalent ihOuter.2, ihOuter.2⟩
  | @symmetry word left right hpair ih =>
      simp only [PairQuotientProperty] at ih ⊢
      exact ⟨ih.2, ih.1⟩
  | basis => trivial
  | progression => trivial
  | rejection => trivial

/-- Proposition 31(3): both components of a derived pair have exactly the
left quotient of the equivalent initial pair's left trace language. -/
public theorem CertificateDerivable.pair_traceLanguages_eq_leftQuotient
    {g : EncodedFirstOrderGrammar Action}
    (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm}
    {basis : List BasisPair}
    {word : List (Label Action)}
    {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right))
    (hinitial : g.TraceEquivalent initialLeft initialRight) :
    g.traceLanguage left =
        word \\ g.traceLanguage initialLeft ∧
      g.traceLanguage right =
        word \\ g.traceLanguage initialLeft :=
  pairQuotientProperty_of_derivable laws hinitial h

/-- Symmetric form of Proposition 31(3), recording equality with the
quotient of either initial component. -/
public theorem CertificateDerivable.pair_traceLanguages_eq_both_leftQuotients
    {g : EncodedFirstOrderGrammar Action}
    (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm}
    {basis : List BasisPair}
    {word : List (Label Action)}
    {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right))
    (hinitial : g.TraceEquivalent initialLeft initialRight) :
    g.traceLanguage left =
        word \\ g.traceLanguage initialLeft ∧
      g.traceLanguage right =
        word \\ g.traceLanguage initialLeft ∧
      g.traceLanguage left =
        word \\ g.traceLanguage initialRight ∧
      g.traceLanguage right =
        word \\ g.traceLanguage initialRight := by
  obtain ⟨hleft, hright⟩ :=
    h.pair_traceLanguages_eq_leftQuotient laws hinitial
  have hquotients :
      word \\ g.traceLanguage initialLeft =
        word \\ g.traceLanguage initialRight := by
    exact congrArg (fun language => word \\ language) hinitial
  exact ⟨hleft, hright,
    hleft.trans hquotients,
    hright.trans hquotients⟩

/-- Membership form used to continue a fixed trace after a derived
balancing row: a suffix is enabled from either derived component exactly
when the original prefix followed by that suffix is enabled initially. -/
public theorem CertificateDerivable.pair_isTrace_iff_append
    {g : EncodedFirstOrderGrammar Action}
    (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm}
    {basis : List BasisPair}
    {word suffix : List (Label Action)}
    {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right))
    (hinitial : g.TraceEquivalent initialLeft initialRight) :
    (g.IsTrace left suffix ↔
        g.IsTrace initialLeft (word ++ suffix)) ∧
      (g.IsTrace right suffix ↔
        g.IsTrace initialLeft (word ++ suffix)) := by
  obtain ⟨hleft, hright⟩ :=
    h.pair_traceLanguages_eq_leftQuotient laws hinitial
  constructor
  · have hmem := Set.ext_iff.mp hleft suffix
    exact hmem
  · have hmem := Set.ext_iff.mp hright suffix
    exact hmem

/-- Operational continuation form: every initial trace extending the derived
word has concrete suffix runs from both derived components. -/
public theorem CertificateDerivable.exists_pair_runs_of_append_trace
    {g : EncodedFirstOrderGrammar Action}
    (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm}
    {basis : List BasisPair}
    {word suffix : List (Label Action)}
    {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right))
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (htrace : g.IsTrace initialLeft (word ++ suffix)) :
    ∃ leftTarget rightTarget,
      g.run? suffix left = some leftTarget ∧
        g.run? suffix right = some rightTarget := by
  have hderived :=
    h.pair_isTrace_iff_append laws (suffix := suffix) hinitial
  obtain ⟨leftTarget, hleftRun⟩ :=
    (g.isTrace_iff_exists_executes).mp
      (hderived.1.mpr htrace)
  obtain ⟨rightTarget, hrightRun⟩ :=
    (g.isTrace_iff_exists_executes).mp
      (hderived.2.mpr htrace)
  exact ⟨leftTarget, rightTarget, hleftRun, hrightRun⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
