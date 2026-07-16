module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StairBoundMonotonicity

@[expose]
public section

/-!
# Following ordinary runs inside the certificate calculus

An exposed equation is stated using an ordinary action run of open schemas.
The width-reduction proof needs the corresponding concrete ground run appended
to an already derived pair judgment.  Determinism, trace equivalence, and
ground-step preservation discharge every local transition side condition.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A finite run can be transported across equality of regular unfoldings. -/
public theorem exists_run_of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {left right rightTarget : RegularTerm} {word : List (Label Action)}
    (hequivalent : left.UnfoldingEquivalent right)
    (hleftClosed : left.ReferenceClosed)
    (hrightClosed : right.ReferenceClosed)
    (hrun : g.run? word right = some rightTarget) :
    ∃ leftTarget,
      g.run? word left = some leftTarget ∧
      leftTarget.UnfoldingEquivalent rightTarget := by
  induction word generalizing left right with
  | nil =>
      simp at hrun
      subst rightTarget
      exact ⟨left, rfl, hequivalent⟩
  | cons label word ih =>
      simp only [run?_cons] at hrun
      cases hrightStep : g.step? label right with
      | none => simp [hrightStep] at hrun
      | some rightNext =>
          simp only [hrightStep, Option.bind_some] at hrun
          have hrel := step?_respects_unfoldingEquivalent
            (g := g) (label := label) hequivalent hleftClosed hrightClosed
            (fun X action rhs hrule => selected_rhs_referenceClosed hg hrule)
          rw [hrightStep] at hrel
          cases hleftStep : g.step? label left with
          | none =>
              rw [hleftStep] at hrel
              cases hrel
          | some leftNext =>
              rw [hleftStep] at hrel
              cases hrel with
              | some hnextEquivalent =>
                  have hleftNextClosed :=
                    step?_preserves_referenceClosed hg hleftClosed hleftStep
                  have hrightNextClosed :=
                    step?_preserves_referenceClosed hg hrightClosed hrightStep
                  obtain ⟨leftTarget, hleftRun, htargetEquivalent⟩ :=
                    ih hnextEquivalent hleftNextClosed hrightNextClosed hrun
                  refine ⟨leftTarget, ?_, htargetEquivalent⟩
                  simp [run?_cons, hleftStep, hleftRun]

/-- Ordinary-action specialization of run transport. -/
public theorem exists_runActions_of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {left right rightTarget : RegularTerm} {word : List Action}
    (hequivalent : left.UnfoldingEquivalent right)
    (hleftClosed : left.ReferenceClosed)
    (hrightClosed : right.ReferenceClosed)
    (hrun : g.runActions? word right = some rightTarget) :
    ∃ leftTarget,
      g.runActions? word left = some leftTarget ∧
      leftTarget.UnfoldingEquivalent rightTarget := by
  exact exists_run_of_unfoldingEquivalent hg hequivalent
    hleftClosed hrightClosed hrun

/-- Extend a derived equivalent ground pair along a common ordinary action
run. -/
public theorem CertificateDerivable.follow_runActions
    {g : EncodedFirstOrderGrammar Action}
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {stem : List (Label Action)} {left right : RegularTerm}
    (hpair : CertificateDerivable g initialLeft initialRight basis
      (.pair stem left right))
    (hequivalent : g.TraceEquivalent left right)
    {actions : List Action} {leftTarget rightTarget : RegularTerm}
    (hleftRun : g.runActions? actions left = some leftTarget)
    (hrightRun : g.runActions? actions right = some rightTarget) :
    CertificateDerivable g initialLeft initialRight basis
      (.pair (stem ++ actions.map Sum.inl) leftTarget rightTarget) := by
  induction actions generalizing stem left right with
  | nil =>
      simp [runActions?] at hleftRun hrightRun
      subst leftTarget
      subst rightTarget
      simpa using hpair
  | cons action actions ih =>
      unfold runActions? at hleftRun hrightRun
      simp only [List.map_cons, run?_cons] at hleftRun hrightRun
      cases hleftStep : g.step? (.inl action) left with
      | none => simp [hleftStep] at hleftRun
      | some leftNext =>
          simp only [hleftStep, Option.bind_some] at hleftRun
          cases hrightStep : g.step? (.inl action) right with
          | none => simp [hrightStep] at hrightRun
          | some rightNext =>
              simp only [hrightStep, Option.bind_some] at hrightRun
              have happrox : g.traceApproxCode 1 left right = true := by
                apply (g.traceApproxCode_eq_true_iff 1 left right).mpr
                exact (g.traceEquivalent_iff_forall_traceApprox left right).mp
                  hequivalent 1
              have hcurrentGround := groundPairCode_of_pair_derivable hpair
              unfold groundPairCode at hcurrentGround
              rw [Bool.and_eq_true] at hcurrentGround
              have hleftGround :=
                (RegularTerm.groundCode_eq_true_iff g.ranks left).mp
                  hcurrentGround.1
              have hrightGround :=
                (RegularTerm.groundCode_eq_true_iff g.ranks right).mp
                  hcurrentGround.2
              have hleftNextGround := hgroundSteps hleftGround hleftStep
              have hrightNextGround := hgroundSteps hrightGround hrightStep
              have hnextGround : g.groundPairCode leftNext rightNext = true := by
                unfold groundPairCode
                rw [Bool.and_eq_true]
                exact ⟨(RegularTerm.groundCode_eq_true_iff
                    g.ranks leftNext).mpr hleftNextGround,
                  (RegularTerm.groundCode_eq_true_iff
                    g.ranks rightNext).mpr hrightNextGround⟩
              have hnextPair : CertificateDerivable g initialLeft initialRight
                  basis (.pair (stem ++ [.inl action])
                    leftNext rightNext) :=
                .transition hpair happrox hleftStep hrightStep hnextGround
              have hleftSingleton : g.run? [.inl action] left =
                  some leftNext := by simp [hleftStep]
              have hrightSingleton : g.run? [.inl action] right =
                  some rightNext := by simp [hrightStep]
              have hnextEquivalent := hequivalent.residual
                hleftSingleton hrightSingleton
              have hresult := ih hnextPair hnextEquivalent
                (hleftRun := by
                  simpa [runActions?] using hleftRun)
                (hrightRun := by
                  simpa [runActions?] using hrightRun)
              simpa [List.map_cons, List.append_assoc] using hresult

/-- The semantic equivalence premise can be recovered from an equivalent
initial query and the existing pair derivation. -/
public theorem CertificateDerivable.follow_runActions_of_initial
    {g : EncodedFirstOrderGrammar Action}
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {stem : List (Label Action)} {left right : RegularTerm}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (hpair : CertificateDerivable g initialLeft initialRight basis
      (.pair stem left right))
    {actions : List Action} {leftTarget rightTarget : RegularTerm}
    (hleftRun : g.runActions? actions left = some leftTarget)
    (hrightRun : g.runActions? actions right = some rightTarget) :
    CertificateDerivable g initialLeft initialRight basis
      (.pair (stem ++ actions.map Sum.inl) leftTarget rightTarget) :=
  hpair.follow_runActions hgroundSteps
    (hpair.pair_traceEquivalent_of_initial laws hinitialEquivalent)
    hleftRun hrightRun

/-- Apply the limit rule to both components of one derived pair, using the
same shorter fixed-point equation.  The second application is obtained by
symmetry, so this packages the two-sided tail replacement used at every later
stair level. -/
public theorem CertificateDerivable.limit_both
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word shorterWord : List (Label Action)}
    {left right shorterLeft shorterRight : RegularTerm}
    {leftContext rightContext replacementContext focus : RegularTerm}
    (houter : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right))
    (hshorter : CertificateDerivable g initialLeft initialRight basis
      (.pair shorterWord shorterLeft shorterRight))
    (hleftContext : leftContext.wellFormedCode g.ranks 1 = true)
    (hrightContext : rightContext.wellFormedCode g.ranks 1 = true)
    (hreplacementContext :
      replacementContext.wellFormedCode g.ranks 1 = true)
    (hfocus : focus.groundCode g.ranks = true)
    (hnontrivial : replacementContext.nontrivialUnaryCode = true)
    (hlength : shorterWord.length < word.length)
    (hleftMatch : RegularTerm.unfoldingEquivalentCode left
      (leftContext.instantiate [focus]) = true)
    (hrightMatch : RegularTerm.unfoldingEquivalentCode right
      (rightContext.instantiate [focus]) = true)
    (hshorterLeft :
      RegularTerm.unfoldingEquivalentCode shorterLeft focus = true)
    (hshorterRight : RegularTerm.unfoldingEquivalentCode shorterRight
      (replacementContext.instantiate [focus]) = true)
    (hleftGround : g.groundPairCode
      (leftContext.instantiate [replacementContext.unaryLimit])
      right = true)
    (hrightGround : g.groundPairCode
      (rightContext.instantiate [replacementContext.unaryLimit])
      (leftContext.instantiate [replacementContext.unaryLimit]) = true) :
    CertificateDerivable g initialLeft initialRight basis
      (.pair word
        (leftContext.instantiate [replacementContext.unaryLimit])
        (rightContext.instantiate [replacementContext.unaryLimit])) := by
  have hleftReplaced : CertificateDerivable g initialLeft initialRight basis
      (.pair word
        (leftContext.instantiate [replacementContext.unaryLimit]) right) :=
    .limit houter hshorter hleftContext hreplacementContext hfocus
      hnontrivial hlength hleftMatch hshorterLeft hshorterRight hleftGround
  have hrightReplaced : CertificateDerivable g initialLeft initialRight basis
      (.pair word
        (rightContext.instantiate [replacementContext.unaryLimit])
        (leftContext.instantiate [replacementContext.unaryLimit])) :=
    .limit (.symmetry hleftReplaced) hshorter hrightContext
      hreplacementContext hfocus hnontrivial hlength hrightMatch
        hshorterLeft hshorterRight hrightGround
  exact .symmetry hrightReplaced

end EncodedFirstOrderGrammar

end DCFEquivalence
