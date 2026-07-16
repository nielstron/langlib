module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisCalculus

@[expose]
public section

/-!
# Realizing finite-basis derivations as executable certificates

`CertificateDerivable` is the convenient inductive presentation of the
finite-basis calculus, whereas `checkCertificateRows` is the executable object
which can be enumerated by the positive semidecision.  This file proves the
missing converse to checker soundness: every finite inductive derivation can be
laid out as a bottom-up row list accepted by the checker.

The proof is insensitive to an already checked prefix.  This stronger extension
form is what makes independently realized premise trees composable while
retaining the checker's backward-reference convention.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

omit [DecidableEq Action] in
/-- Every judgment occurring in the prior list has a backward reference. -/
private theorem exists_lookupPrior_eq_some_of_mem
    {prior : List (CertificateJudgment Action)}
    {judgment : CertificateJudgment Action}
    (hmem : judgment ∈ prior) :
    ∃ back, lookupPrior prior back = some judgment := by
  rw [← List.mem_reverse, List.mem_iff_getElem?] at hmem
  exact hmem

omit [DecidableEq Action] in
/-- A finite list of judgments already present in the prior list can be named
simultaneously by a list of backward references. -/
private theorem exists_lookupPrior_refs
    (prior judgments : List (CertificateJudgment Action))
    (hmem : ∀ judgment ∈ judgments, judgment ∈ prior) :
    ∃ refs : List ℕ, refs.mapM (lookupPrior prior) = some judgments := by
  induction judgments with
  | nil => exact ⟨[], rfl⟩
  | cons judgment judgments ih =>
      obtain ⟨back, hback⟩ :=
        exists_lookupPrior_eq_some_of_mem (hmem judgment (by simp))
      obtain ⟨refs, hrefs⟩ := ih fun tail htail =>
        hmem tail (by simp [htail])
      exact ⟨back :: refs, by simp [hback, hrefs]⟩

/-- Checking row lists composes by list append. -/
private theorem checkCertificateRows_append
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (first second : List (CertificateRow Action)) :
    g.checkCertificateRows initialLeft initialRight basis prior
        (first ++ second) =
      (g.checkCertificateRows initialLeft initialRight basis prior first).bind
        (fun middle =>
          g.checkCertificateRows initialLeft initialRight basis middle second) := by
  induction first generalizing prior with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.cons_append, checkCertificateRows]
      cases hrow : g.checkCertificateRow initialLeft initialRight basis prior row with
      | none => simp
      | some result => simp [ih]

/-- Append one successfully checked row to an already checked row list. -/
private theorem checkCertificateRows_append_singleton
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (rows : List (CertificateRow Action))
    (middle : List (CertificateJudgment Action))
    (row : CertificateRow Action) (result : CertificateJudgment Action)
    (hrows : g.checkCertificateRows initialLeft initialRight basis prior rows =
      some middle)
    (hrow : g.checkCertificateRow initialLeft initialRight basis middle row =
      some result) :
    g.checkCertificateRows initialLeft initialRight basis prior
        (rows ++ [row]) = some (middle ++ [result]) := by
  rw [checkCertificateRows_append, hrows]
  simp [checkCertificateRows, hrow]

/-- Strong executable realization of the finite-basis calculus.  Starting
after any already checked `prior`, a derivation can be compiled to rows whose
result list ends in the derived judgment; the old prior remains a prefix of the
new result prefix. -/
public theorem CertificateDerivable.exists_checked_extension
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment) :
    ∀ prior, ∃ rows stem,
      g.checkCertificateRows initialLeft initialRight basis prior rows =
        some (stem ++ [judgment]) ∧
      prior <+: stem := by
  induction h with
  | «axiom» hground =>
      intro prior
      refine ⟨[.axiom], prior, ?_, List.prefix_rfl⟩
      simp [checkCertificateRows, checkCertificateRow, checkCondition, hground]
  | @transition word left right left' right' label hpair happrox hleft hright
      hground ih =>
      intro prior
      obtain ⟨rows, stem, hrows, hprefix⟩ := ih prior
      let middle := stem ++ [.pair word left right]
      obtain ⟨pairRef, hpairRef⟩ :=
        exists_lookupPrior_eq_some_of_mem
          (prior := middle) (judgment := .pair word left right) (by
            simp [middle])
      let row : CertificateRow Action := .transition pairRef label
      have hrow : g.checkCertificateRow initialLeft initialRight basis middle row =
          some (.pair (word ++ [label]) left' right') := by
        simp [row, checkCertificateRow, hpairRef, checkCondition, happrox,
          hleft, hright, hground]
      refine ⟨rows ++ [row], middle, ?_, ?_⟩
      · exact checkCertificateRows_append_singleton g initialLeft initialRight
          basis prior rows middle row _ (by simpa [middle] using hrows) hrow
      · exact hprefix.trans (List.prefix_append _ _)
  | @limit word shorterWord outerLeft outerRight shorterLeft shorterRight
      outerContext replacementContext focus houter hshorter houterContext
      hreplacementContext hfocus hnontrivial hlength houterMatch hshorterLeft
      hshorterRight hground ihOuter ihShorter =>
      intro prior
      obtain ⟨outerRows, outerPrefix, houterRows, hpriorOuter⟩ := ihOuter prior
      let afterOuter := outerPrefix ++ [.pair word outerLeft outerRight]
      obtain ⟨shorterRows, shorterPrefix, hshorterRows, houterShorter⟩ :=
        ihShorter afterOuter
      let middle := shorterPrefix ++
        [.pair shorterWord shorterLeft shorterRight]
      have houterMem : (.pair word outerLeft outerRight :
          CertificateJudgment Action) ∈ middle := by
        apply List.mem_append_left
        exact houterShorter.subset (by simp [afterOuter])
      obtain ⟨outerRef, houterRef⟩ :=
        exists_lookupPrior_eq_some_of_mem houterMem
      obtain ⟨shorterRef, hshorterRef⟩ :=
        exists_lookupPrior_eq_some_of_mem
          (prior := middle)
          (judgment := .pair shorterWord shorterLeft shorterRight) (by
            simp [middle])
      let row : CertificateRow Action :=
        .limit outerRef shorterRef outerContext replacementContext focus
      have hconditions : g.limitRowConditionsCode word shorterWord
          outerLeft outerRight shorterLeft shorterRight outerContext
          replacementContext focus = true :=
        (limitRowConditionsCode_eq_true_iff g word shorterWord outerLeft
          outerRight shorterLeft shorterRight outerContext replacementContext
          focus).2 ⟨houterContext, hreplacementContext, hfocus, hnontrivial,
            hlength, houterMatch, hshorterLeft, hshorterRight, hground⟩
      have hrow : g.checkCertificateRow initialLeft initialRight basis middle row =
          some (.pair word
            (outerContext.instantiate [replacementContext.unaryLimit])
            outerRight) := by
        simp [row, checkCertificateRow, houterRef, hshorterRef, checkCondition,
          hconditions]
      let allRows := outerRows ++ shorterRows
      have hallRows : g.checkCertificateRows initialLeft initialRight basis prior
          allRows = some middle := by
        dsimp [allRows]
        rw [checkCertificateRows_append, houterRows]
        simpa [afterOuter, middle] using hshorterRows
      refine ⟨allRows ++ [row], middle, ?_, ?_⟩
      · exact checkCertificateRows_append_singleton g initialLeft initialRight
          basis prior allRows middle row _ hallRows hrow
      · exact hpriorOuter.trans (List.prefix_append _ _)
          |>.trans houterShorter
          |>.trans (List.prefix_append _ _)
  | @symmetry word left right hpair ih =>
      intro prior
      obtain ⟨rows, stem, hrows, hprefix⟩ := ih prior
      let middle := stem ++ [.pair word left right]
      obtain ⟨pairRef, hpairRef⟩ :=
        exists_lookupPrior_eq_some_of_mem
          (prior := middle) (judgment := .pair word left right) (by
            simp [middle])
      let row : CertificateRow Action := .symmetry pairRef
      have hrow : g.checkCertificateRow initialLeft initialRight basis middle row =
          some (.pair word right left) := by
        simp [row, checkCertificateRow, hpairRef]
      refine ⟨rows ++ [row], middle, ?_, ?_⟩
      · exact checkCertificateRows_append_singleton g initialLeft initialRight
          basis prior rows middle row _ (by simpa [middle] using hrows) hrow
      · exact hprefix.trans (List.prefix_append _ _)
  | @basis word left right pairRef schema arguments hpair hschema hnonempty
      hschemaWellFormed hargumentCount harguments hleft hright ih =>
      intro prior
      obtain ⟨rows, stem, hrows, hprefix⟩ := ih prior
      let middle := stem ++ [.pair word left right]
      obtain ⟨sourceRef, hsourceRef⟩ :=
        exists_lookupPrior_eq_some_of_mem
          (prior := middle) (judgment := .pair word left right) (by
            simp [middle])
      let row : CertificateRow Action := .basis sourceRef pairRef arguments
      have hconditions : g.basisRowConditionsCode word left right schema
          arguments = true :=
        (basisRowConditionsCode_eq_true_iff g word left right schema
          arguments).2 ⟨hnonempty, hschemaWellFormed, hargumentCount,
            harguments, hleft, hright⟩
      have hrow : g.checkCertificateRow initialLeft initialRight basis middle row =
          some (.nop word) := by
        simp [row, checkCertificateRow, hsourceRef, hschema, checkCondition,
          hconditions]
      refine ⟨rows ++ [row], middle, ?_, ?_⟩
      · exact checkCertificateRows_append_singleton g initialLeft initialRight
          basis prior rows middle row _ (by simpa [middle] using hrows) hrow
      · exact hprefix.trans (List.prefix_append _ _)
  | @progression word left right hpair happrox hchildren ihPair ihChildren =>
      intro prior
      obtain ⟨pairRows, pairPrefix, hpairRows, hpriorPair⟩ := ihPair prior
      let afterPair := pairPrefix ++ [.pair word left right]
      let targets : List (CertificateJudgment Action) :=
        (g.enabledLabels left).map fun label => .nop (word ++ [label])
      have realizeLabels : ∀ labels : List (Label Action),
          (∀ label ∈ labels, label ∈ g.enabledLabels left) →
          ∀ current, ∃ rows final,
            g.checkCertificateRows initialLeft initialRight basis current rows =
              some final ∧
            current <+: final ∧
            ∀ label ∈ labels,
              (.nop (word ++ [label]) : CertificateJudgment Action) ∈ final := by
        intro labels
        induction labels with
        | nil =>
            intro _ current
            refine ⟨[], current, rfl, List.prefix_rfl, ?_⟩
            simp
        | cons label labels ih =>
            intro hsubset current
            have hlabel : label ∈ g.enabledLabels left :=
              hsubset label (by simp)
            obtain ⟨headRows, headPrefix, hheadRows, hcurrentHead⟩ :=
              ihChildren label hlabel current
            let afterHead := headPrefix ++ [.nop (word ++ [label])]
            obtain ⟨tailRows, final, htailRows, hheadFinal, htailMem⟩ :=
              ih (fun tail htail => hsubset tail (by simp [htail])) afterHead
            refine ⟨headRows ++ tailRows, final, ?_, ?_, ?_⟩
            · rw [checkCertificateRows_append, hheadRows]
              simpa [afterHead] using htailRows
            · exact hcurrentHead.trans (List.prefix_append _ _)
                |>.trans hheadFinal
            · intro target htarget
              simp only [List.mem_cons] at htarget
              rcases htarget with rfl | htarget
              · exact hheadFinal.subset (by simp [afterHead])
              · exact htailMem target htarget
      obtain ⟨childRows, middle, hchildRows, hpairChildren, hlabelTargets⟩ :=
        realizeLabels (g.enabledLabels left) (by simp) afterPair
      have htargets : ∀ target ∈ targets, target ∈ middle := by
        intro target htarget
        change target ∈ (g.enabledLabels left).map
          (fun label => (.nop (word ++ [label]) :
            CertificateJudgment Action)) at htarget
        obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp htarget
        exact hlabelTargets label hlabel
      obtain ⟨childRefs, hchildRefs⟩ :=
        exists_lookupPrior_refs middle targets htargets
      obtain ⟨sourceRef, hsourceRef⟩ :=
        exists_lookupPrior_eq_some_of_mem
          (prior := middle) (judgment := .pair word left right)
          (hpairChildren.subset (by simp [afterPair]))
      let row : CertificateRow Action := .progression sourceRef childRefs
      have hprogression : g.progressionChildrenCode middle word left childRefs =
          true := (progressionChildrenCode_eq_true_iff g middle word left
            childRefs).2 (by simpa [targets] using hchildRefs)
      have hrow : g.checkCertificateRow initialLeft initialRight basis middle row =
          some (.nop word) := by
        simp [row, checkCertificateRow, hsourceRef, checkCondition, happrox,
          hprogression]
      let allRows := pairRows ++ childRows
      have hallRows : g.checkCertificateRows initialLeft initialRight basis prior
          allRows = some middle := by
        dsimp [allRows]
        rw [checkCertificateRows_append, hpairRows]
        simpa [afterPair] using hchildRows
      refine ⟨allRows ++ [row], middle, ?_, ?_⟩
      · exact checkCertificateRows_append_singleton g initialLeft initialRight
          basis prior allRows middle row _ hallRows hrow
      · exact hpriorPair.trans (List.prefix_append _ _)
          |>.trans hpairChildren
  | @rejection word left right hpair hreject ih =>
      intro prior
      obtain ⟨rows, stem, hrows, hprefix⟩ := ih prior
      let middle := stem ++ [.pair word left right]
      obtain ⟨pairRef, hpairRef⟩ :=
        exists_lookupPrior_eq_some_of_mem
          (prior := middle) (judgment := .pair word left right) (by
            simp [middle])
      let row : CertificateRow Action := .rejection pairRef
      have hrow : g.checkCertificateRow initialLeft initialRight basis middle row =
          some .fail := by
        simp [row, checkCertificateRow, hpairRef, checkCondition, hreject]
      refine ⟨rows ++ [row], middle, ?_, ?_⟩
      · exact checkCertificateRows_append_singleton g initialLeft initialRight
          basis prior rows middle row _ (by simpa [middle] using hrows) hrow
      · exact hprefix.trans (List.prefix_append _ _)

/-- Every inductive proof of `ε ⊨ NOP` has a concrete row certificate accepted
by the executable checker. -/
public theorem exists_acceptingCertificate_of_derivable_nop
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (h : CertificateDerivable g initialLeft initialRight basis (.nop [])) :
    ∃ rows, g.acceptsEquivalenceCertificateCode initialLeft initialRight basis
      rows = true := by
  obtain ⟨rows, stem, hrows, _⟩ := h.exists_checked_extension []
  refine ⟨rows, ?_⟩
  rw [acceptsEquivalenceCertificateCode_eq_true_iff]
  simp [checkCertificate, hrows]

/-- Executable positive certificates and finite inductive derivations are
extensionally equivalent. -/
public theorem exists_acceptingCertificate_iff_derivable_nop
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair) :
    (∃ rows, g.acceptsEquivalenceCertificateCode initialLeft initialRight basis
      rows = true) ↔
      CertificateDerivable g initialLeft initialRight basis (.nop []) := by
  constructor
  · rintro ⟨rows, hrows⟩
    exact g.derivable_nop_of_acceptsEquivalenceCertificate initialLeft
      initialRight basis rows hrows
  · exact exists_acceptingCertificate_of_derivable_nop

end EncodedFirstOrderGrammar

end DCFEquivalence
