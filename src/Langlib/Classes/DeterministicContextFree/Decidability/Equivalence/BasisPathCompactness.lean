module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OpenSoundBasis

@[expose]
public section

/-!
# Path compactness for an arbitrary finite basis

The existing bounded-sound compactness theorem specializes the basis in its
statement.  Critical-marker completeness instead fixes one original open-sound
basis and reuses it in an extension.  The argument below is the same infinite
uncovered-path construction, parameterized by an arbitrary basis; semantic
soundness is deliberately not needed for the derivability direction.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A derived nonempty pair which is directly dischargeable by a row of the
fixed basis. -/
public structure BasisCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair) (word : List (Label Action)) where
  left : RegularTerm
  right : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight basis
    (.pair word left right)
  schema : BasisPair
  schema_mem : schema ∈ basis
  arguments : List RegularTerm
  word_nonempty : word ≠ []
  schema_wellFormed : g.basisPairWellFormedCode schema = true
  argument_count : arguments.length = schema.arity
  arguments_ground : g.groundArgumentsCode arguments = true
  left_matches : RegularTerm.unfoldingEquivalentCode left
    (schema.left.instantiate arguments) = true
  right_matches : RegularTerm.unfoldingEquivalentCode right
    (schema.right.instantiate arguments) = true

/-- Every infinite common transition path eventually reaches a basis row. -/
@[expose] public def EveryPathCoveredBy
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair) : Prop :=
  ∀ path : TracePath g initialLeft initialRight,
    ∃ n, Nonempty (BasisCoverage g initialLeft initialRight basis
      (path.word n))

private structure OpenPairWithBasis
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair) where
  word : List (Label Action)
  left : RegularTerm
  right : RegularTerm
  pair : CertificateDerivable g initialLeft initialRight basis
    (.pair word left right)
  not_nop : ¬CertificateDerivable g initialLeft initialRight basis
    (.nop word)

private def OpenSuccessorWithBasis
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (current next : OpenPairWithBasis g initialLeft initialRight basis) : Prop :=
  ∃ label,
    next.word = current.word ++ [label] ∧
    g.step? label current.left = some next.left ∧
    g.step? label current.right = some next.right

private theorem exists_openSuccessorWithBasis
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (current : OpenPairWithBasis g initialLeft initialRight basis) :
    ∃ next, OpenSuccessorWithBasis current next := by
  classical
  have hcurrentEquivalent : g.TraceEquivalent current.left current.right :=
    current.pair.pair_traceEquivalent_of_initial laws hinitialEquivalent
  have happroxProp : g.TraceApprox 1 current.left current.right :=
    (g.traceEquivalent_iff_forall_traceApprox current.left current.right).mp
      hcurrentEquivalent 1
  have happroxCode : g.traceApproxCode 1 current.left current.right = true :=
    (g.traceApproxCode_eq_true_iff 1 current.left current.right).mpr happroxProp
  have hexistsLabel : ∃ label ∈ g.enabledLabels current.left,
      ¬CertificateDerivable g initialLeft initialRight basis
        (.nop (current.word ++ [label])) := by
    by_contra hnone
    push_neg at hnone
    apply current.not_nop
    exact .progression current.pair happroxCode hnone
  obtain ⟨label, henabled, hnotNop⟩ := hexistsLabel
  have hleftSome := (g.mem_enabledLabels_iff current.left label).mp henabled
  cases hleft : g.step? label current.left with
  | none => simp [hleft] at hleftSome
  | some nextLeft =>
      have hrel := happroxProp label
      rw [hleft] at hrel
      cases hright : g.step? label current.right with
      | none =>
          rw [hright] at hrel
          cases hrel
      | some nextRight =>
          have hcurrentGround := groundPairCode_of_pair_derivable current.pair
          unfold groundPairCode at hcurrentGround
          rw [Bool.and_eq_true] at hcurrentGround
          have hleftGround : current.left.Ground g.ranks :=
            (RegularTerm.groundCode_eq_true_iff g.ranks current.left).mp
              hcurrentGround.1
          have hrightGround : current.right.Ground g.ranks :=
            (RegularTerm.groundCode_eq_true_iff g.ranks current.right).mp
              hcurrentGround.2
          have hnextLeftGround := hgroundSteps hleftGround hleft
          have hnextRightGround := hgroundSteps hrightGround hright
          have hnextGround : g.groundPairCode nextLeft nextRight = true := by
            unfold groundPairCode
            rw [Bool.and_eq_true]
            exact ⟨(RegularTerm.groundCode_eq_true_iff g.ranks _).mpr
                hnextLeftGround,
              (RegularTerm.groundCode_eq_true_iff g.ranks _).mpr
                hnextRightGround⟩
          let next : OpenPairWithBasis g initialLeft initialRight basis :=
            { word := current.word ++ [label]
              left := nextLeft
              right := nextRight
              pair := .transition current.pair happroxCode hleft hright
                hnextGround
              not_nop := hnotNop }
          exact ⟨next, label, rfl, hleft, hright⟩

private noncomputable def nextOpenPairWithBasis
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (current : OpenPairWithBasis g initialLeft initialRight basis) :
    OpenPairWithBasis g initialLeft initialRight basis :=
  Classical.choose
    (exists_openSuccessorWithBasis laws hgroundSteps hinitialEquivalent current)

private theorem nextOpenPairWithBasis_isSuccessor
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (current : OpenPairWithBasis g initialLeft initialRight basis) :
    OpenSuccessorWithBasis current
      (nextOpenPairWithBasis laws hgroundSteps hinitialEquivalent current) :=
  Classical.choose_spec
    (exists_openSuccessorWithBasis laws hgroundSteps hinitialEquivalent current)

private noncomputable def openPairWithBasisSequence
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (initial : OpenPairWithBasis g initialLeft initialRight basis) :
    ℕ → OpenPairWithBasis g initialLeft initialRight basis
  | 0 => initial
  | n + 1 => nextOpenPairWithBasis laws hgroundSteps hinitialEquivalent
      (openPairWithBasisSequence laws hgroundSteps hinitialEquivalent initial n)

/-- Coverage of every infinite path by the fixed basis yields a root `NOP`
derivation under that same basis. -/
public theorem derivable_nop_of_everyPathCoveredBy
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hequivalent : g.TraceEquivalent initialLeft initialRight)
    (hcovered : g.EveryPathCoveredBy initialLeft initialRight basis) :
    CertificateDerivable g initialLeft initialRight basis (.nop []) := by
  classical
  by_contra hnotRoot
  let initial : OpenPairWithBasis g initialLeft initialRight basis :=
    { word := []
      left := initialLeft
      right := initialRight
      pair := .axiom hground
      not_nop := hnotRoot }
  let sequence := openPairWithBasisSequence laws hgroundSteps
    hequivalent initial
  let path : TracePath g initialLeft initialRight :=
    { word := fun n => (sequence n).word
      left := fun n => (sequence n).left
      right := fun n => (sequence n).right
      starts_word := rfl
      starts_left := rfl
      starts_right := rfl
      step := fun n => by
        change OpenSuccessorWithBasis (sequence n) (sequence (n + 1))
        change OpenSuccessorWithBasis (sequence n)
          (nextOpenPairWithBasis laws hgroundSteps hequivalent (sequence n))
        exact nextOpenPairWithBasis_isSuccessor laws hgroundSteps
          hequivalent (sequence n) }
  obtain ⟨n, ⟨coverage⟩⟩ := hcovered path
  change BasisCoverage g initialLeft initialRight basis
    (sequence n).word at coverage
  apply (sequence n).not_nop
  obtain ⟨pairRef, hpairRef, hschema⟩ :=
    List.mem_iff_getElem.mp coverage.schema_mem
  apply CertificateDerivable.basis coverage.derivation
    (pairRef := pairRef) (schema := coverage.schema)
    (arguments := coverage.arguments)
  · exact List.getElem?_eq_some_iff.mpr ⟨hpairRef, hschema⟩
  · exact coverage.word_nonempty
  · exact coverage.schema_wellFormed
  · exact coverage.argument_count
  · exact coverage.arguments_ground
  · exact coverage.left_matches
  · exact coverage.right_matches

end EncodedFirstOrderGrammar

end DCFEquivalence
