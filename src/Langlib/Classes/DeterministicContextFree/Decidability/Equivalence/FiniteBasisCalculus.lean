module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TraceApproximants
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GroundComputability

@[expose]
public section

/-!
# The finite-basis deduction calculus

This file formalizes the finite proof objects used on the positive side of
deterministic first-order-grammar trace equivalence.  It is the executable
counterpart of the word-labelling predicate in Figure 1 of Jančar's
arXiv:1010.4760v4.

A certificate is a bottom-up list of rows.  References are distances backwards
from the current row (`0` names the immediately preceding result).  This makes
separately constructed proof fragments stable under concatenation and will be
useful when certificates are enumerated.

The checker deliberately compares regular terms by `UnfoldingEquivalent`, not
by equality of their finite graph presentations.  In particular, neither a
basis instance nor a repeated/limit term can be certified merely by choosing a
convenient graph layout.

This file establishes only the finite local calculus and its executable
checker.  Its semantic soundness and the sufficient-basis completeness theorem
are separate proof boundaries; no decidability claim is made here.
-/

namespace DCFEquivalence

/-! ## Closing a unary regular context by its limit -/

namespace RegularTerm

/-- Redirect a reference to the distinguished unary variable back to the root
of its context.  On a well-formed unary context this ties precisely the open
recursive calls. -/
@[expose] public def closeUnaryReference (context : RegularTerm) (i : ℕ) : ℕ :=
  match context.nodeAt? i with
  | some (.inl 0) => context.root
  | _ => i

/-- Redirect the children of one application node while closing a unary
context.  Variable nodes are retained but become unreachable from the closed
root whenever the context is nontrivial. -/
@[expose] public def closeUnaryNode (context : RegularTerm) : RawNode → RawNode
  | .inl x => .inl x
  | .inr (X, children) =>
      .inr (X, children.map context.closeUnaryReference)

/-- The regular solution `Fᵒᵐᵐ¹` of `x = F(x)`, represented by tying every
reference to the unary variable back to the root of `F`'s finite graph. -/
@[expose] public def unaryLimit (context : RegularTerm) : RegularTerm :=
  (context.nodes.map context.closeUnaryNode,
    context.closeUnaryReference context.root)

/-- A unary context is nontrivial when its root is not the open variable.  For
a well-formed term with variable bound one this is exactly the side condition
`F ≠ x₁` in the limit-subterm rule. -/
@[expose] public def nontrivialUnaryCode (context : RegularTerm) : Bool :=
  match context.rootNode? with
  | some (.inl 0) => false
  | _ => true

end RegularTerm

/-! ## Finite basis and certificate syntax -/

/-- A basis row stores its variable bound and the two regular term schemas. -/
public abbrev BasisPair := ℕ × RegularTerm × RegularTerm

namespace BasisPair

@[expose] public def arity (pair : BasisPair) : ℕ := pair.1

@[expose] public def left (pair : BasisPair) : RegularTerm := pair.2.1

@[expose] public def right (pair : BasisPair) : RegularTerm := pair.2.2

end BasisPair

/-- The three forms of judgment in the word-labelling calculus. -/
public inductive CertificateJudgment (Action : Type) where
  | pair (word : List (Label Action)) (left right : RegularTerm)
  | nop (word : List (Label Action))
  | fail
  deriving DecidableEq

/-- One locally checkable deduction row.

`limit outer shorter E F T` implements limit-subterm replacement.  The checker
requires `outer` to label `(E(T), U)`, `shorter` to label `(T, F(T))`, and the
second word to be strictly shorter.  Its conclusion labels
`(E(Fᵒᵐᵐ¹), U)`.
-/
public inductive CertificateRow (Action : Type) where
  | axiom
  | transition (pairRef : ℕ) (label : Label Action)
  | limit (outerRef shorterRef : ℕ)
      (outerContext replacementContext focus : RegularTerm)
  | symmetry (pairRef : ℕ)
  | basis (pairRef basisRef : ℕ) (arguments : List RegularTerm)
  | progression (pairRef : ℕ) (childRefs : List ℕ)
  | rejection (pairRef : ℕ)
  deriving DecidableEq

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Structurally valid ground arguments for a basis instance. -/
@[expose] public def groundArgumentsCode
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm) : Bool :=
  arguments.all fun argument => argument.groundCode g.ranks

/-- Structural validity of one finite basis schema. -/
@[expose] public def basisPairWellFormedCode
    (g : EncodedFirstOrderGrammar Action) (pair : BasisPair) : Bool :=
  pair.left.wellFormedCode g.ranks pair.arity &&
    pair.right.wellFormedCode g.ranks pair.arity

/-- Structural validity of a pair of ground terms. -/
@[expose] public def groundPairCode
    (g : EncodedFirstOrderGrammar Action)
    (left right : RegularTerm) : Bool :=
  left.groundCode g.ranks && right.groundCode g.ranks

/-- The finite list of labels enabled at a term.  Duplicates in the grammar's
raw action list are removed before certificates assign one child to each
enabled action. -/
@[expose] public def enabledLabels
    (g : EncodedFirstOrderGrammar Action)
    (term : RegularTerm) : List (Label Action) :=
  (g.candidateLabels term).dedup.filter fun label =>
    (g.step? label term).isSome

/-- Backward reference lookup: zero denotes the newest prior judgment. -/
@[expose] public def lookupPrior
    (prior : List (CertificateJudgment Action)) (back : ℕ) :
    Option (CertificateJudgment Action) :=
  prior.reverse[back]?

/-- The finite enabled-label list is extensionally exact. -/
public theorem mem_enabledLabels_iff
    (g : EncodedFirstOrderGrammar Action) (term : RegularTerm)
    (label : Label Action) :
    label ∈ g.enabledLabels term ↔ (g.step? label term).isSome = true := by
  simp only [enabledLabels, List.mem_filter, List.mem_dedup]
  constructor
  · exact fun h => h.2
  · intro hstep
    refine ⟨?_, hstep⟩
    cases h : g.step? label term with
    | none => simp [h] at hstep
    | some target =>
        exact mem_candidateLabels_of_step?_eq_some h

omit [DecidableEq Action] in
/-- A successful backward lookup names an actual earlier judgment. -/
public theorem mem_of_lookupPrior_eq_some
    {prior : List (CertificateJudgment Action)} {back : ℕ}
    {judgment : CertificateJudgment Action}
    (h : lookupPrior prior back = some judgment) : judgment ∈ prior := by
  have hreverse : judgment ∈ prior.reverse := List.mem_of_getElem? h
  simpa using hreverse

omit [DecidableEq Action] in
/-- Every result returned by a batch of backward lookups occurs among the prior
verified judgments. -/
public theorem mem_prior_of_mapM_lookupPrior_eq_some
    {prior : List (CertificateJudgment Action)} {refs : List ℕ}
    {judgments : List (CertificateJudgment Action)}
    (h : refs.mapM (lookupPrior prior) = some judgments) :
    ∀ judgment ∈ judgments, judgment ∈ prior := by
  induction refs generalizing judgments with
  | nil =>
      simp at h
      subst judgments
      simp
  | cons ref refs ih =>
      cases hhead : lookupPrior prior ref with
      | none => simp [hhead] at h
      | some head =>
          cases htail : refs.mapM (lookupPrior prior) with
          | none => simp [hhead, htail] at h
          | some tail =>
              simp [hhead, htail] at h
              subst judgments
              intro judgment hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact mem_of_lookupPrior_eq_some hhead
              · exact ih htail judgment hmem

@[expose] public def checkCondition (condition : Bool) : Option Unit :=
  if condition then some () else none

@[simp] private theorem checkCondition_bind_eq_some_iff
    {Result : Type} (condition : Bool) (next : Unit → Option Result)
    (result : Result) :
    (checkCondition condition >>= next) = some result ↔
      condition = true ∧ next () = some result := by
  cases condition <;> simp [checkCondition]

/-- All finite side conditions of one limit-subterm replacement row. -/
@[expose] public def limitRowConditionsCode
    (g : EncodedFirstOrderGrammar Action)
    (word shorterWord : List (Label Action))
    (outerLeft outerRight shorterLeft shorterRight : RegularTerm)
    (outerContext replacementContext focus : RegularTerm) : Bool :=
  outerContext.wellFormedCode g.ranks 1 &&
  replacementContext.wellFormedCode g.ranks 1 &&
  focus.groundCode g.ranks &&
  replacementContext.nontrivialUnaryCode &&
  decide (shorterWord.length < word.length) &&
  RegularTerm.unfoldingEquivalentCode outerLeft
    (outerContext.instantiate [focus]) &&
  RegularTerm.unfoldingEquivalentCode shorterLeft focus &&
  RegularTerm.unfoldingEquivalentCode shorterRight
    (replacementContext.instantiate [focus]) &&
  g.groundPairCode
    (outerContext.instantiate [replacementContext.unaryLimit]) outerRight

/-- All finite side conditions of one basis row. -/
@[expose] public def basisRowConditionsCode
    (g : EncodedFirstOrderGrammar Action)
    (word : List (Label Action)) (left right : RegularTerm)
    (schema : BasisPair) (arguments : List RegularTerm) : Bool :=
  decide (word ≠ []) &&
  g.basisPairWellFormedCode schema &&
  decide (arguments.length = schema.arity) &&
  g.groundArgumentsCode arguments &&
  RegularTerm.unfoldingEquivalentCode left
    (schema.left.instantiate arguments) &&
  RegularTerm.unfoldingEquivalentCode right
    (schema.right.instantiate arguments)

/-- Exact finite child-reference condition for bottom-up progression. -/
@[expose] public def progressionChildrenCode
    (g : EncodedFirstOrderGrammar Action)
    (prior : List (CertificateJudgment Action))
    (word : List (Label Action)) (left : RegularTerm)
    (childRefs : List ℕ) : Bool :=
  decide (childRefs.mapM (lookupPrior prior) = some
    ((g.enabledLabels left).map fun label => .nop (word ++ [label])))

omit [DecidableEq Action] in
public theorem limitRowConditionsCode_eq_true_iff
    (g : EncodedFirstOrderGrammar Action)
    (word shorterWord : List (Label Action))
    (outerLeft outerRight shorterLeft shorterRight : RegularTerm)
    (outerContext replacementContext focus : RegularTerm) :
    g.limitRowConditionsCode word shorterWord
      outerLeft outerRight shorterLeft shorterRight
      outerContext replacementContext focus = true ↔
      outerContext.wellFormedCode g.ranks 1 = true ∧
      replacementContext.wellFormedCode g.ranks 1 = true ∧
      focus.groundCode g.ranks = true ∧
      replacementContext.nontrivialUnaryCode = true ∧
      shorterWord.length < word.length ∧
      RegularTerm.unfoldingEquivalentCode outerLeft
        (outerContext.instantiate [focus]) = true ∧
      RegularTerm.unfoldingEquivalentCode shorterLeft focus = true ∧
      RegularTerm.unfoldingEquivalentCode shorterRight
        (replacementContext.instantiate [focus]) = true ∧
      g.groundPairCode
        (outerContext.instantiate [replacementContext.unaryLimit])
        outerRight = true := by
  simp [limitRowConditionsCode]
  tauto

omit [DecidableEq Action] in
public theorem basisRowConditionsCode_eq_true_iff
    (g : EncodedFirstOrderGrammar Action)
    (word : List (Label Action)) (left right : RegularTerm)
    (schema : BasisPair) (arguments : List RegularTerm) :
    g.basisRowConditionsCode word left right schema arguments = true ↔
      word ≠ [] ∧
      g.basisPairWellFormedCode schema = true ∧
      arguments.length = schema.arity ∧
      g.groundArgumentsCode arguments = true ∧
      RegularTerm.unfoldingEquivalentCode left
        (schema.left.instantiate arguments) = true ∧
      RegularTerm.unfoldingEquivalentCode right
        (schema.right.instantiate arguments) = true := by
  simp [basisRowConditionsCode]
  tauto

public theorem progressionChildrenCode_eq_true_iff
    (g : EncodedFirstOrderGrammar Action)
    (prior : List (CertificateJudgment Action))
    (word : List (Label Action)) (left : RegularTerm)
    (childRefs : List ℕ) :
    g.progressionChildrenCode prior word left childRefs = true ↔
      childRefs.mapM (lookupPrior prior) = some
        ((g.enabledLabels left).map fun label => .nop (word ++ [label])) := by
  simp [progressionChildrenCode]

/-- Check one deduction row against already verified earlier rows. -/
@[expose] public def checkCertificateRow
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair)
    (prior : List (CertificateJudgment Action)) :
    CertificateRow Action → Option (CertificateJudgment Action)
  | .axiom => do
      checkCondition (g.groundPairCode initialLeft initialRight)
      pure (.pair [] initialLeft initialRight)
  | .transition pairRef label => do
      let .pair word left right ← lookupPrior prior pairRef | none
      checkCondition (g.traceApproxCode 1 left right)
      let left' ← g.step? label left
      let right' ← g.step? label right
      checkCondition (g.groundPairCode left' right')
      pure (.pair (word ++ [label]) left' right')
  | .limit outerRef shorterRef outerContext replacementContext focus => do
      let .pair word outerLeft outerRight ←
        lookupPrior prior outerRef | none
      let .pair shorterWord shorterLeft shorterRight ←
        lookupPrior prior shorterRef | none
      checkCondition (g.limitRowConditionsCode word shorterWord
        outerLeft outerRight shorterLeft shorterRight
        outerContext replacementContext focus)
      let replacement := replacementContext.unaryLimit
      let result := outerContext.instantiate [replacement]
      pure (.pair word result outerRight)
  | .symmetry pairRef => do
      let .pair word left right ← lookupPrior prior pairRef | none
      pure (.pair word right left)
  | .basis pairRef basisRef arguments => do
      let .pair word left right ← lookupPrior prior pairRef | none
      let schema ← basis[basisRef]?
      checkCondition (g.basisRowConditionsCode word left right schema arguments)
      pure (.nop word)
  | .progression pairRef childRefs => do
      let .pair word left right ← lookupPrior prior pairRef | none
      checkCondition (g.traceApproxCode 1 left right)
      checkCondition (g.progressionChildrenCode prior word left childRefs)
      pure (.nop word)
  | .rejection pairRef => do
      let .pair _word left right ← lookupPrior prior pairRef | none
      checkCondition (!g.traceApproxCode 1 left right)
      pure .fail

/-- Check a bottom-up list of rows and return every verified judgment. -/
@[expose] public def checkCertificateRows
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair) :
    List (CertificateJudgment Action) → List (CertificateRow Action) →
      Option (List (CertificateJudgment Action))
  | prior, [] => some prior
  | prior, row :: rows => do
      let result ← g.checkCertificateRow initialLeft initialRight basis prior row
      g.checkCertificateRows initialLeft initialRight basis
        (prior ++ [result]) rows

/-- Verify a complete certificate and return its final judgment. -/
@[expose] public def checkCertificate
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair)
    (rows : List (CertificateRow Action)) :
    Option (CertificateJudgment Action) := do
  let results ←
    g.checkCertificateRows initialLeft initialRight basis [] rows
  results.getLast?

/-- Executable acceptance of a positive certificate for the initial pair. -/
@[expose] public def acceptsEquivalenceCertificateCode
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair)
    (rows : List (CertificateRow Action)) : Bool :=
  decide (g.checkCertificate initialLeft initialRight basis rows =
    some (.nop []))

/-! ## Relational presentation of the same rows -/

/-- Inductive word-labelling derivability.  The Boolean side conditions are
retained verbatim here so the executable checker can be related to the calculus
without hiding a semantic oracle. -/
public inductive CertificateDerivable
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair) : CertificateJudgment Action → Prop
  | axiom
      (hground : g.groundPairCode initialLeft initialRight = true) :
      CertificateDerivable g initialLeft initialRight basis
        (.pair [] initialLeft initialRight)
  | transition {word left right left' right' label}
      (hpair : CertificateDerivable g initialLeft initialRight basis
        (.pair word left right))
      (happrox : g.traceApproxCode 1 left right = true)
      (hleft : g.step? label left = some left')
      (hright : g.step? label right = some right')
      (hground : g.groundPairCode left' right' = true) :
      CertificateDerivable g initialLeft initialRight basis
        (.pair (word ++ [label]) left' right')
  | limit {word shorterWord : List (Label Action)}
      {outerLeft outerRight shorterLeft shorterRight : RegularTerm}
      {outerContext replacementContext focus : RegularTerm}
      (houter : CertificateDerivable g initialLeft initialRight basis
        (.pair word outerLeft outerRight))
      (hshorter : CertificateDerivable g initialLeft initialRight basis
        (.pair shorterWord shorterLeft shorterRight))
      (houterContext :
        outerContext.wellFormedCode g.ranks 1 = true)
      (hreplacementContext :
        replacementContext.wellFormedCode g.ranks 1 = true)
      (hfocus : focus.groundCode g.ranks = true)
      (hnontrivial : replacementContext.nontrivialUnaryCode = true)
      (hlength : shorterWord.length < word.length)
      (houterMatch : RegularTerm.unfoldingEquivalentCode outerLeft
        (outerContext.instantiate [focus]) = true)
      (hshorterLeft : RegularTerm.unfoldingEquivalentCode shorterLeft focus = true)
      (hshorterRight : RegularTerm.unfoldingEquivalentCode shorterRight
        (replacementContext.instantiate [focus]) = true)
      (hground : g.groundPairCode
        (outerContext.instantiate [replacementContext.unaryLimit])
        outerRight = true) :
      CertificateDerivable g initialLeft initialRight basis
        (.pair word
          (outerContext.instantiate [replacementContext.unaryLimit])
          outerRight)
  | symmetry {word : List (Label Action)} {left right : RegularTerm}
      (hpair : CertificateDerivable g initialLeft initialRight basis
        (.pair word left right)) :
      CertificateDerivable g initialLeft initialRight basis
        (.pair word right left)
  | basis {word : List (Label Action)} {left right : RegularTerm}
      {pairRef : ℕ} {schema : BasisPair} {arguments : List RegularTerm}
      (hpair : CertificateDerivable g initialLeft initialRight basis
        (.pair word left right))
      (hschema : basis[pairRef]? = some schema)
      (hnonempty : word ≠ [])
      (hschemaWellFormed : g.basisPairWellFormedCode schema = true)
      (hargumentCount : arguments.length = schema.arity)
      (harguments : g.groundArgumentsCode arguments = true)
      (hleft : RegularTerm.unfoldingEquivalentCode left
        (schema.left.instantiate arguments) = true)
      (hright : RegularTerm.unfoldingEquivalentCode right
        (schema.right.instantiate arguments) = true) :
      CertificateDerivable g initialLeft initialRight basis (.nop word)
  | progression {word : List (Label Action)} {left right : RegularTerm}
      (hpair : CertificateDerivable g initialLeft initialRight basis
        (.pair word left right))
      (happrox : g.traceApproxCode 1 left right = true)
      (hchildren : ∀ label ∈ g.enabledLabels left,
        CertificateDerivable g initialLeft initialRight basis
          (.nop (word ++ [label]))) :
      CertificateDerivable g initialLeft initialRight basis (.nop word)
  | rejection {word : List (Label Action)} {left right : RegularTerm}
      (hpair : CertificateDerivable g initialLeft initialRight basis
        (.pair word left right))
      (hreject : g.traceApproxCode 1 left right = false) :
      CertificateDerivable g initialLeft initialRight basis .fail

private theorem checkCertificateRow_axiom_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    {result : CertificateJudgment Action}
    (hcheck : g.checkCertificateRow initialLeft initialRight basis prior
      .axiom = some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  cases hground : g.groundPairCode initialLeft initialRight with
  | false => simp [checkCertificateRow, checkCondition, hground] at hcheck
  | true =>
      have hresult : result = .pair [] initialLeft initialRight := by
        simpa [checkCertificateRow, checkCondition, hground] using hcheck.symm
      subst result
      exact .axiom hground

private theorem checkCertificateRow_transition_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (hprior : ∀ judgment ∈ prior,
      CertificateDerivable g initialLeft initialRight basis judgment)
    (pairRef : ℕ) (label : Label Action)
    {result : CertificateJudgment Action}
    (hcheck : g.checkCertificateRow initialLeft initialRight basis prior
      (.transition pairRef label) = some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  cases hlookup : lookupPrior prior pairRef with
  | none => simp [checkCertificateRow, hlookup] at hcheck
  | some judgment =>
      cases judgment with
      | nop word => simp [checkCertificateRow, hlookup] at hcheck
      | fail => simp [checkCertificateRow, hlookup] at hcheck
      | pair word left right =>
          have hpair := hprior _ (mem_of_lookupPrior_eq_some hlookup)
          cases happrox : g.traceApproxCode 1 left right with
          | false =>
              simp [checkCertificateRow, hlookup, checkCondition, happrox]
                at hcheck
          | true =>
              cases hleft : g.step? label left with
              | none =>
                  simp [checkCertificateRow, hlookup, checkCondition, happrox,
                    hleft] at hcheck
              | some left' =>
                  cases hright : g.step? label right with
                  | none =>
                      simp [checkCertificateRow, hlookup, checkCondition,
                        happrox, hleft, hright] at hcheck
                  | some right' =>
                      cases hground : g.groundPairCode left' right' with
                      | false =>
                          simp [checkCertificateRow, hlookup, checkCondition,
                            happrox, hleft, hright, hground] at hcheck
                      | true =>
                          have hresult : result =
                              .pair (word ++ [label]) left' right' := by
                            simpa [checkCertificateRow, hlookup, checkCondition,
                              happrox, hleft, hright, hground] using hcheck.symm
                          subst result
                          exact .transition hpair happrox hleft hright hground

private theorem checkCertificateRow_limit_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (hprior : ∀ judgment ∈ prior,
      CertificateDerivable g initialLeft initialRight basis judgment)
    (outerRef shorterRef : ℕ)
    (outerContext replacementContext focus : RegularTerm)
    {result : CertificateJudgment Action}
    (hcheck : g.checkCertificateRow initialLeft initialRight basis prior
      (.limit outerRef shorterRef outerContext replacementContext focus) =
        some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  cases houterLookup : lookupPrior prior outerRef with
  | none => simp [checkCertificateRow, houterLookup] at hcheck
  | some outerJudgment =>
      cases outerJudgment with
      | nop word => simp [checkCertificateRow, houterLookup] at hcheck
      | fail => simp [checkCertificateRow, houterLookup] at hcheck
      | pair word outerLeft outerRight =>
          have houter := hprior _
            (mem_of_lookupPrior_eq_some houterLookup)
          cases hshorterLookup : lookupPrior prior shorterRef with
          | none =>
              simp [checkCertificateRow, houterLookup, hshorterLookup] at hcheck
          | some shorterJudgment =>
              cases shorterJudgment with
              | nop shorterWord =>
                  simp [checkCertificateRow, houterLookup, hshorterLookup]
                    at hcheck
              | fail =>
                  simp [checkCertificateRow, houterLookup, hshorterLookup]
                    at hcheck
              | pair shorterWord shorterLeft shorterRight =>
                  have hshorter := hprior _
                    (mem_of_lookupPrior_eq_some hshorterLookup)
                  let conditions := g.limitRowConditionsCode word shorterWord
                    outerLeft outerRight shorterLeft shorterRight
                    outerContext replacementContext focus
                  cases hconditions : conditions with
                  | false =>
                      simp [checkCertificateRow, houterLookup, hshorterLookup,
                        conditions, hconditions, checkCondition] at hcheck
                  | true =>
                      have hspec := (limitRowConditionsCode_eq_true_iff g
                        word shorterWord outerLeft outerRight shorterLeft
                        shorterRight outerContext replacementContext focus).mp
                        (by simpa [conditions] using hconditions)
                      rcases hspec with
                        ⟨houterContext, hreplacementContext, hfocus,
                          hnontrivial, hlength, houterMatch, hshorterLeft,
                          hshorterRight, hground⟩
                      have hresult : result = .pair word
                          (outerContext.instantiate
                            [replacementContext.unaryLimit]) outerRight := by
                        simpa [checkCertificateRow, houterLookup,
                          hshorterLookup, conditions, hconditions,
                          checkCondition] using hcheck.symm
                      subst result
                      exact .limit houter hshorter houterContext
                        hreplacementContext hfocus hnontrivial hlength
                        houterMatch hshorterLeft hshorterRight hground

private theorem checkCertificateRow_symmetry_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (hprior : ∀ judgment ∈ prior,
      CertificateDerivable g initialLeft initialRight basis judgment)
    (pairRef : ℕ) {result : CertificateJudgment Action}
    (hcheck : g.checkCertificateRow initialLeft initialRight basis prior
      (.symmetry pairRef) = some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  cases hlookup : lookupPrior prior pairRef with
  | none => simp [checkCertificateRow, hlookup] at hcheck
  | some judgment =>
      cases judgment with
      | nop word => simp [checkCertificateRow, hlookup] at hcheck
      | fail => simp [checkCertificateRow, hlookup] at hcheck
      | pair word left right =>
          have hresult : result = .pair word right left := by
            simpa [checkCertificateRow, hlookup] using hcheck.symm
          subst result
          exact .symmetry (hprior _ (mem_of_lookupPrior_eq_some hlookup))

private theorem checkCertificateRow_basis_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (hprior : ∀ judgment ∈ prior,
      CertificateDerivable g initialLeft initialRight basis judgment)
    (pairRef basisRef : ℕ) (arguments : List RegularTerm)
    {result : CertificateJudgment Action}
    (hcheck : g.checkCertificateRow initialLeft initialRight basis prior
      (.basis pairRef basisRef arguments) = some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  cases hlookup : lookupPrior prior pairRef with
  | none => simp [checkCertificateRow, hlookup] at hcheck
  | some judgment =>
      cases judgment with
      | nop word => simp [checkCertificateRow, hlookup] at hcheck
      | fail => simp [checkCertificateRow, hlookup] at hcheck
      | pair word left right =>
          have hpair := hprior _ (mem_of_lookupPrior_eq_some hlookup)
          cases hschema : basis[basisRef]? with
          | none => simp [checkCertificateRow, hlookup, hschema] at hcheck
          | some schema =>
              let conditions :=
                g.basisRowConditionsCode word left right schema arguments
              cases hconditions : conditions with
              | false =>
                  simp [checkCertificateRow, hlookup, hschema, conditions,
                    hconditions, checkCondition] at hcheck
              | true =>
                  have hspec := (basisRowConditionsCode_eq_true_iff g
                    word left right schema arguments).mp
                    (by simpa [conditions] using hconditions)
                  rcases hspec with
                    ⟨hnonempty, hschemaWellFormed, hargumentCount,
                      harguments, hleft, hright⟩
                  have hresult : result = .nop word := by
                    simpa [checkCertificateRow, hlookup, hschema, conditions,
                      hconditions, checkCondition] using hcheck.symm
                  subst result
                  exact .basis hpair hschema hnonempty hschemaWellFormed
                    hargumentCount harguments hleft hright

private theorem checkCertificateRow_progression_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (hprior : ∀ judgment ∈ prior,
      CertificateDerivable g initialLeft initialRight basis judgment)
    (pairRef : ℕ) (childRefs : List ℕ)
    {result : CertificateJudgment Action}
    (hcheck : g.checkCertificateRow initialLeft initialRight basis prior
      (.progression pairRef childRefs) = some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  cases hlookup : lookupPrior prior pairRef with
  | none => simp [checkCertificateRow, hlookup] at hcheck
  | some judgment =>
      cases judgment with
      | nop word => simp [checkCertificateRow, hlookup] at hcheck
      | fail => simp [checkCertificateRow, hlookup] at hcheck
      | pair word left right =>
          have hpair := hprior _ (mem_of_lookupPrior_eq_some hlookup)
          cases happrox : g.traceApproxCode 1 left right with
          | false =>
              simp [checkCertificateRow, hlookup, happrox, checkCondition]
                at hcheck
          | true =>
              let conditions :=
                g.progressionChildrenCode prior word left childRefs
              cases hconditions : conditions with
              | false =>
                  simp [checkCertificateRow, hlookup, happrox, conditions,
                    hconditions, checkCondition] at hcheck
              | true =>
                  have hchildrenLookup :=
                    (progressionChildrenCode_eq_true_iff g prior word left
                      childRefs).mp (by simpa [conditions] using hconditions)
                  have hresult : result = .nop word := by
                    simpa [checkCertificateRow, hlookup, happrox, conditions,
                      hconditions, checkCondition] using hcheck.symm
                  subst result
                  apply CertificateDerivable.progression hpair happrox
                  intro label hlabel
                  apply hprior
                  apply mem_prior_of_mapM_lookupPrior_eq_some hchildrenLookup
                  exact List.mem_map.mpr ⟨label, hlabel, rfl⟩

private theorem checkCertificateRow_rejection_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (hprior : ∀ judgment ∈ prior,
      CertificateDerivable g initialLeft initialRight basis judgment)
    (pairRef : ℕ) {result : CertificateJudgment Action}
    (hcheck : g.checkCertificateRow initialLeft initialRight basis prior
      (.rejection pairRef) = some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  cases hlookup : lookupPrior prior pairRef with
  | none => simp [checkCertificateRow, hlookup] at hcheck
  | some judgment =>
      cases judgment with
      | nop word => simp [checkCertificateRow, hlookup] at hcheck
      | fail => simp [checkCertificateRow, hlookup] at hcheck
      | pair word left right =>
          have hpair := hprior _ (mem_of_lookupPrior_eq_some hlookup)
          cases happrox : g.traceApproxCode 1 left right with
          | true =>
              simp [checkCertificateRow, hlookup, happrox, checkCondition]
                at hcheck
          | false =>
              have hresult : result = .fail := by
                simpa [checkCertificateRow, hlookup, happrox, checkCondition]
                  using hcheck.symm
              subst result
              exact .rejection hpair happrox

/-- Every successfully checked local row is an instance of the corresponding
inductive deduction rule, assuming all of its backward references have already
been derived. -/
public theorem checkCertificateRow_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (prior : List (CertificateJudgment Action))
    (hprior : ∀ judgment ∈ prior,
      CertificateDerivable g initialLeft initialRight basis judgment)
    (row : CertificateRow Action) {result : CertificateJudgment Action}
    (hcheck : g.checkCertificateRow initialLeft initialRight basis prior row =
      some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  cases row with
  | «axiom» =>
      exact checkCertificateRow_axiom_sound g initialLeft initialRight basis
        prior hcheck
  | transition pairRef label =>
      exact checkCertificateRow_transition_sound g initialLeft initialRight
        basis prior hprior pairRef label hcheck
  | limit outerRef shorterRef outerContext replacementContext focus =>
      exact checkCertificateRow_limit_sound g initialLeft initialRight basis
        prior hprior outerRef shorterRef outerContext replacementContext focus
        hcheck
  | symmetry pairRef =>
      exact checkCertificateRow_symmetry_sound g initialLeft initialRight basis
        prior hprior pairRef hcheck
  | basis pairRef basisRef arguments =>
      exact checkCertificateRow_basis_sound g initialLeft initialRight basis
        prior hprior pairRef basisRef arguments hcheck
  | progression pairRef childRefs =>
      exact checkCertificateRow_progression_sound g initialLeft initialRight
        basis prior hprior pairRef childRefs hcheck
  | rejection pairRef =>
      exact checkCertificateRow_rejection_sound g initialLeft initialRight basis
        prior hprior pairRef hcheck

/-- Replaying a successfully checked row list derives every returned judgment. -/
public theorem checkCertificateRows_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    {prior : List (CertificateJudgment Action)}
    {rows : List (CertificateRow Action)}
    {results : List (CertificateJudgment Action)}
    (hprior : ∀ judgment ∈ prior,
      CertificateDerivable g initialLeft initialRight basis judgment)
    (hcheck : g.checkCertificateRows initialLeft initialRight basis prior rows =
      some results) :
    ∀ judgment ∈ results,
      CertificateDerivable g initialLeft initialRight basis judgment := by
  induction rows generalizing prior results with
  | nil =>
      simp [checkCertificateRows] at hcheck
      subst results
      exact hprior
  | cons row rows ih =>
      cases hrow : g.checkCertificateRow initialLeft initialRight basis prior row with
      | none => simp [checkCertificateRows, hrow] at hcheck
      | some rowResult =>
          have hrowDerivable := g.checkCertificateRow_sound initialLeft
            initialRight basis prior hprior row hrow
          have htail : g.checkCertificateRows initialLeft initialRight basis
              (prior ++ [rowResult]) rows = some results := by
            simpa [checkCertificateRows, hrow] using hcheck
          apply ih (prior := prior ++ [rowResult])
          intro judgment hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | rfl
          · exact hprior judgment hmem
          · exact hrowDerivable
          exact htail

/-- Exact local soundness of the complete executable checker. -/
public theorem checkCertificate_sound
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    {rows : List (CertificateRow Action)}
    {result : CertificateJudgment Action}
    (hcheck : g.checkCertificate initialLeft initialRight basis rows =
      some result) :
    CertificateDerivable g initialLeft initialRight basis result := by
  unfold checkCertificate at hcheck
  cases hrows : g.checkCertificateRows initialLeft initialRight basis [] rows with
  | none => simp [hrows] at hcheck
  | some results =>
      have hlast : results.getLast? = some result := by
        simpa [hrows] using hcheck
      have hall := g.checkCertificateRows_sound initialLeft initialRight basis
        (prior := []) (rows := rows) (results := results) (by simp) hrows
      exact hall result (List.mem_of_getLast? hlast)

public theorem acceptsEquivalenceCertificateCode_eq_true_iff
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (rows : List (CertificateRow Action)) :
    g.acceptsEquivalenceCertificateCode initialLeft initialRight basis rows = true
      ↔ g.checkCertificate initialLeft initialRight basis rows =
        some (.nop []) := by
  simp [acceptsEquivalenceCertificateCode]

/-- A positively accepted finite certificate really derives `ε ⊨ NOP` in the
finite-basis calculus. -/
public theorem derivable_nop_of_acceptsEquivalenceCertificate
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) (basis : List BasisPair)
    (rows : List (CertificateRow Action))
    (haccept : g.acceptsEquivalenceCertificateCode initialLeft initialRight
      basis rows = true) :
    CertificateDerivable g initialLeft initialRight basis (.nop []) := by
  apply g.checkCertificate_sound initialLeft initialRight basis
  exact (acceptsEquivalenceCertificateCode_eq_true_iff g initialLeft
    initialRight basis rows).mp haccept

end EncodedFirstOrderGrammar

end DCFEquivalence
