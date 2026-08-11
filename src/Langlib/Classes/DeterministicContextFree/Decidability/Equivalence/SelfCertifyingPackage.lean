module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CertificateComputability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalWorstInstance
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisRealization

@[expose]
public section

/-!
# Uniform self-certifying equivalence packages

A raw positive witness contains one finite basis, a marker bound, one checked
root certificate for the query, and one checked root certificate for every
critical basis instance.  Unlike `HasEquivalenceCertificate`, acceptance of
this complete package is semantic evidence: the critical-instance theorem
rules out a circularly unsound use of the proposed basis.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The raw instance whose equivalence is to be semidecided. -/
public abbrev SelfCertifyingInstance (Action : Type) :=
  EncodedFirstOrderGrammar Action × (RegularTerm × RegularTerm)

/-- A marker count, a proposed basis, query rows, and one row list per basis
row.  Nested products give this raw witness an automatic primitive encoding. -/
public abbrev SelfCertifyingWitness (Action : Type) :=
  ℕ × (List BasisPair ×
    (List (CertificateRow (Action ⊕ ℕ)) ×
      List (List (CertificateRow (Action ⊕ ℕ)))))

@[expose] public def acceptsCriticalRowsCode
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (basis : List BasisPair) (schema : BasisPair)
    (rows : List (CertificateRow (Action ⊕ ℕ))) : Bool :=
  (g.withCriticalMarkers count).acceptsEquivalenceCertificateCode
    (schema.left.instantiate (g.criticalArguments schema.arity))
    (schema.right.instantiate (g.criticalArguments schema.arity))
    basis rows

/-- Total Boolean validation of a complete self-certifying package. -/
@[expose] public def acceptsSelfCertifyingPackagePayloadCode
    (input : SelfCertifyingInstance Action)
    (witness : SelfCertifyingWitness Action) : Bool :=
  let g := input.1
  let left := input.2.1
  let right := input.2.2
  let count := witness.1
  let basis := witness.2.1
  let queryRows := witness.2.2.1
  let criticalRows := witness.2.2.2
  basis.all (fun schema =>
      g.basisPairWellFormedCode schema && decide (schema.arity ≤ count)) &&
    (g.withCriticalMarkers count).acceptsEquivalenceCertificateCode
      left right basis queryRows &&
    List.all₂ (acceptsCriticalRowsCode g count basis) basis criticalRows

/-- Total Boolean validation of the certificate payload.  Structural validity
of the grammar is the explicit promise of the eventual semidecision merge. -/
@[expose] public def acceptsSelfCertifyingPackageCode
    (input : SelfCertifyingInstance Action)
    (witness : SelfCertifyingWitness Action) : Bool :=
  acceptsSelfCertifyingPackagePayloadCode input witness

private theorem all₂_forall_left
    {Left Right : Type} {test : Left → Right → Bool}
    {left : List Left} {right : List Right}
    (h : List.all₂ test left right = true) :
    ∀ value ∈ left, ∃ partner, test value partner = true := by
  induction left generalizing right with
  | nil => simp
  | cons head tail ih =>
      cases right with
      | nil => simp [List.all₂] at h
      | cons rightHead rightTail =>
          have hparts : test head rightHead = true ∧
              List.all₂ test tail rightTail = true := by
            simpa [List.all₂, Bool.and_eq_true] using h
          intro value hvalue
          rw [List.mem_cons] at hvalue
          rcases hvalue with rfl | htail
          · exact ⟨rightHead, hparts.1⟩
          · exact ih hparts.2 value htail

/-- Acceptance of the complete package implies equivalence in the marker
extension and therefore equivalence in the original grammar. -/
public theorem traceEquivalent_of_acceptsSelfCertifyingPackage
    {input : SelfCertifyingInstance Action}
    {witness : SelfCertifyingWitness Action}
    (hg : input.1.WellFormed)
    (haccept : acceptsSelfCertifyingPackageCode input witness = true) :
    input.1.TraceEquivalent input.2.1 input.2.2 := by
  let g := input.1
  let left := input.2.1
  let right := input.2.2
  let count := witness.1
  let basis := witness.2.1
  let queryRows := witness.2.2.1
  let criticalRows := witness.2.2.2
  change g.TraceEquivalent left right
  unfold acceptsSelfCertifyingPackageCode
    acceptsSelfCertifyingPackagePayloadCode at haccept
  dsimp only at haccept
  have hparts :
      (basis.all (fun schema =>
        g.basisPairWellFormedCode schema &&
          decide (schema.arity ≤ count)) = true ∧
      (g.withCriticalMarkers count).acceptsEquivalenceCertificateCode
        left right basis queryRows = true) ∧
      List.all₂ (acceptsCriticalRowsCode g count basis)
        basis criticalRows = true := by
    simpa only [Bool.and_eq_true] using haccept
  have hbasisCode := hparts.1.1
  have hquery := hparts.1.2
  have hcriticalCode := hparts.2
  have hbasis : ∀ schema ∈ basis,
      schema.left.WellFormed g.ranks schema.arity ∧
        schema.right.WellFormed g.ranks schema.arity := by
    intro schema hschema
    have hrow := (List.all_eq_true.mp hbasisCode) schema hschema
    rw [Bool.and_eq_true] at hrow
    unfold basisPairWellFormedCode at hrow
    rw [Bool.and_eq_true] at hrow
    exact hrow.1
  have hcount : ∀ schema ∈ basis, schema.arity ≤ count := by
    intro schema hschema
    have hrow := (List.all_eq_true.mp hbasisCode) schema hschema
    rw [Bool.and_eq_true] at hrow
    exact of_decide_eq_true hrow.2
  have hg' : g.WellFormed := by simpa [g] using hg
  let family := criticalInstanceFamily_of_originalBasis
    g hg' basis count hbasis hcount
  have hinitial : CertificateDerivable (g.withCriticalMarkers count)
      left right basis (.nop []) :=
    (g.withCriticalMarkers count).derivable_nop_of_acceptsEquivalenceCertificate
      left right basis queryRows hquery
  have hcritical : ∀ schema ∈ basis,
      CertificateDerivable (g.withCriticalMarkers count)
        (family.left schema) (family.right schema) basis (.nop []) := by
    intro schema hschema
    obtain ⟨rows, hrows⟩ := all₂_forall_left hcriticalCode schema hschema
    have hderivable :=
      (g.withCriticalMarkers count).derivable_nop_of_acceptsEquivalenceCertificate
        (schema.left.instantiate (g.criticalArguments schema.arity))
        (schema.right.instantiate (g.criticalArguments schema.arity))
        basis rows hrows
    simpa [family, CriticalInstanceFamily.left,
      CriticalInstanceFamily.right,
      criticalInstanceFamily_of_originalBasis] using hderivable
  have hextended := traceEquivalent_of_criticalCertificates
    (guardedContextLaws_of_wellFormed
      (g.withCriticalMarkers_wellFormed hg' count))
    family hinitial hcritical
  exact g.traceEquivalent_of_withCriticalMarkers count hextended

private theorem all₂_map_right_eq_true
    {Left Right : Type} {test : Left → Right → Bool}
    {items : List Left} {partner : Left → Right}
    (h : ∀ value ∈ items, test value (partner value) = true) :
    List.all₂ test items (items.map partner) = true := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.all₂]
      rw [h head (by simp), ih (by
        intro value hvalue
        exact h value (by simp [hvalue]))]
      simp

/-- Assemble a raw accepted package from one derivation of the query and one
derivation of every canonical critical basis instance. -/
public theorem exists_acceptedSelfCertifyingWitness_of_derivations
    {input : SelfCertifyingInstance Action}
    (count : ℕ) (basis : List BasisPair)
    (hbasis : ∀ schema ∈ basis,
      schema.left.WellFormed input.1.ranks schema.arity ∧
        schema.right.WellFormed input.1.ranks schema.arity)
    (hcount : ∀ schema ∈ basis, schema.arity ≤ count)
    (hquery : CertificateDerivable (input.1.withCriticalMarkers count)
      input.2.1 input.2.2 basis (.nop []))
    (hcritical : ∀ schema ∈ basis,
      CertificateDerivable (input.1.withCriticalMarkers count)
        (schema.left.instantiate
          (input.1.criticalArguments schema.arity))
        (schema.right.instantiate
          (input.1.criticalArguments schema.arity))
        basis (.nop [])) :
    ∃ witness : SelfCertifyingWitness Action,
      acceptsSelfCertifyingPackageCode input witness = true := by
  classical
  obtain ⟨queryRows, hqueryRows⟩ :=
    exists_acceptingCertificate_of_derivable_nop hquery
  have hcriticalRows : ∀ schema ∈ basis,
      ∃ rows : List (CertificateRow (Action ⊕ ℕ)),
        acceptsCriticalRowsCode input.1 count basis schema rows = true := by
    intro schema hschema
    exact exists_acceptingCertificate_of_derivable_nop
      (hcritical schema hschema)
  let rowsFor : BasisPair → List (CertificateRow (Action ⊕ ℕ)) :=
    fun schema => if hschema : schema ∈ basis then
      Classical.choose (hcriticalRows schema hschema) else []
  have hrowsFor : ∀ schema ∈ basis,
      acceptsCriticalRowsCode input.1 count basis schema
        (rowsFor schema) = true := by
    intro schema hschema
    simp only [rowsFor, dif_pos hschema]
    exact Classical.choose_spec (hcriticalRows schema hschema)
  have hbasisCode : basis.all (fun schema =>
      input.1.basisPairWellFormedCode schema &&
        decide (schema.arity ≤ count)) = true := by
    apply List.all_eq_true.mpr
    intro schema hschema
    rw [Bool.and_eq_true]
    refine ⟨?_, by simpa using hcount schema hschema⟩
    unfold basisPairWellFormedCode
    rw [Bool.and_eq_true]
    exact hbasis schema hschema
  have hcriticalCode : List.all₂
      (acceptsCriticalRowsCode input.1 count basis)
      basis (basis.map rowsFor) = true :=
    all₂_map_right_eq_true hrowsFor
  refine ⟨(count, (basis, (queryRows, basis.map rowsFor))), ?_⟩
  unfold acceptsSelfCertifyingPackageCode
    acceptsSelfCertifyingPackagePayloadCode
  dsimp only
  rw [hbasisCode, hqueryRows, hcriticalCode]
  rfl

/-! ## Primitive-recursive package checking -/

section Computability

variable [Primcodable Action]

private theorem replicateZero_primrec :
    Primrec (fun count : ℕ => List.replicate count 0) := by
  refine (Primrec.list_map Primrec.list_range
    (Primrec.const 0).to₂).of_eq ?_
  intro count
  simp

public theorem criticalMarker_primrec :
    Primrec fun input : EncodedFirstOrderGrammar Action × ℕ =>
      input.1.criticalMarker input.2 := by
  have hsymbol : Primrec fun input :
      EncodedFirstOrderGrammar Action × ℕ =>
      input.1.ranks.length + input.2 :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
      Primrec.snd
  have hnode : Primrec fun input :
      EncodedFirstOrderGrammar Action × ℕ =>
      (.inr (input.1.ranks.length + input.2, []) : RawNode) :=
    Primrec.sumInr.comp
      (Primrec.pair hsymbol (Primrec.const []))
  exact (Primrec.pair
    (Primrec.list_cons.comp hnode (Primrec.const []))
    (Primrec.const 0)).of_eq fun input => by
      rfl

private theorem liftCriticalRule_primrec :
    Primrec (liftCriticalRule : RawRule Action → RawRule (Action ⊕ ℕ)) := by
  exact (Primrec.pair Primrec.fst
    (Primrec.pair
      (Primrec.sumInl.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

public theorem criticalMarkerRule_primrec :
    Primrec fun input : EncodedFirstOrderGrammar Action × ℕ =>
      input.1.criticalMarkerRule input.2 := by
  have hsymbol : Primrec fun input :
      EncodedFirstOrderGrammar Action × ℕ =>
      input.1.ranks.length + input.2 :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
      Primrec.snd
  exact (Primrec.pair hsymbol
    (Primrec.pair (Primrec.sumInr.comp Primrec.snd)
      criticalMarker_primrec)).of_eq fun _ => rfl

/-- Adding a finite marker block is primitive recursive in the raw grammar and
the requested block size. -/
public theorem withCriticalMarkers_primrec :
    Primrec fun input : EncodedFirstOrderGrammar Action × ℕ =>
      input.1.withCriticalMarkers input.2 := by
  let Input := EncodedFirstOrderGrammar Action × ℕ
  have hranks : Primrec fun input : Input =>
      input.1.ranks ++ List.replicate input.2 0 :=
    Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (replicateZero_primrec.comp Primrec.snd)
  have hlifted : Primrec fun input : Input =>
      input.1.rawRules.map liftCriticalRule := by
    apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
    apply Primrec₂.mk
    exact liftCriticalRule_primrec.comp Primrec.snd
  have hmarkers : Primrec fun input : Input =>
      (List.range input.2).map input.1.criticalMarkerRule := by
    apply Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    apply Primrec₂.mk
    exact criticalMarkerRule_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (Primrec.pair hranks
    (Primrec.list_append.comp hlifted hmarkers)).of_eq fun _ => rfl

/-- The arity-indexed canonical marker tuple is primitive recursive. -/
public theorem criticalArguments_primrec :
    Primrec fun input : EncodedFirstOrderGrammar Action × ℕ =>
      input.1.criticalArguments input.2 := by
  apply Primrec.list_map (Primrec.list_range.comp Primrec.snd)
  apply Primrec₂.mk
  exact criticalMarker_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)

public abbrev CriticalRowsCheckInput (Action : Type) :=
  EncodedFirstOrderGrammar Action ×
    ℕ × List BasisPair × BasisPair ×
      List (CertificateRow (Action ⊕ ℕ))

/-- Checking one aligned critical basis row is primitive recursive. -/
public theorem acceptsCriticalRowsCode_primrec :
    Primrec fun input : CriticalRowsCheckInput Action =>
      acceptsCriticalRowsCode input.1 input.2.1 input.2.2.1
        input.2.2.2.1 input.2.2.2.2 := by
  let Input := CriticalRowsCheckInput Action
  have hg : Primrec fun input : Input => input.1 := Primrec.fst
  have hcount : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hbasis : Primrec fun input : Input => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hschema : Primrec fun input : Input => input.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrows : Primrec fun input : Input => input.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hextended : Primrec fun input : Input =>
      input.1.withCriticalMarkers input.2.1 :=
    withCriticalMarkers_primrec.comp (Primrec.pair hg hcount)
  have harity : Primrec fun input : Input => input.2.2.2.1.arity :=
    Primrec.fst.comp hschema
  have harguments : Primrec fun input : Input =>
      input.1.criticalArguments input.2.2.2.1.arity :=
    criticalArguments_primrec.comp (Primrec.pair hg harity)
  have hleft : Primrec fun input : Input =>
      input.2.2.2.1.left.instantiate
        (input.1.criticalArguments input.2.2.2.1.arity) :=
    instantiate_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp hschema)) harguments
  have hright : Primrec fun input : Input =>
      input.2.2.2.1.right.instantiate
        (input.1.criticalArguments input.2.2.2.1.arity) :=
    instantiate_primrec.comp
      (Primrec.snd.comp (Primrec.snd.comp hschema)) harguments
  have hbase : Primrec fun input : Input =>
      (input.1.withCriticalMarkers input.2.1,
        ((input.2.2.2.1.left.instantiate
            (input.1.criticalArguments input.2.2.2.1.arity),
          input.2.2.2.1.right.instantiate
            (input.1.criticalArguments input.2.2.2.1.arity)),
        input.2.2.1)) :=
    Primrec.pair hextended
      (Primrec.pair (Primrec.pair hleft hright) hbasis)
  exact (acceptsEquivalenceCertificateCode_primrec.comp
    (Primrec.pair hbase hrows)).of_eq fun _ => rfl

/-- The complete certificate payload checker is primitive recursive.  Grammar
well-formedness is deliberately separated because it is the validity promise
of the eventual DPDA-to-grammar reduction. -/
public theorem acceptsSelfCertifyingPackagePayloadCode_primrec :
    Primrec fun input : SelfCertifyingInstance Action ×
        SelfCertifyingWitness Action =>
      acceptsSelfCertifyingPackagePayloadCode input.1 input.2 := by
  let Input := SelfCertifyingInstance Action × SelfCertifyingWitness Action
  have hg : Primrec fun input : Input => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hleft : Primrec fun input : Input => input.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hright : Primrec fun input : Input => input.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hcount : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hbasis : Primrec fun input : Input => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hqueryRows : Primrec fun input : Input => input.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hcriticalRows : Primrec fun input : Input => input.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hextended : Primrec fun input : Input =>
      input.1.1.withCriticalMarkers input.2.1 :=
    withCriticalMarkers_primrec.comp (Primrec.pair hg hcount)
  have hbasisRows : Primrec fun input : Input =>
      input.2.2.1.all fun schema =>
        input.1.1.basisPairWellFormedCode schema &&
          decide (schema.arity ≤ input.2.1) := by
    apply list_all_primrec hbasis
    apply Primrec₂.mk
    let TestInput := Input × BasisPair
    have hwell : Primrec fun input : TestInput =>
        input.1.1.1.basisPairWellFormedCode input.2 :=
      basisPairWellFormedCode_primrec.comp
        (hg.comp Primrec.fst) Primrec.snd
    have hle : Primrec fun input : TestInput =>
        decide (input.2.arity ≤ input.1.2.1) :=
      (PrimrecRel.decide Primrec.nat_le).comp
        (Primrec.fst.comp Primrec.snd)
        (hcount.comp Primrec.fst)
    exact Primrec.and.comp hwell hle
  have hqueryBase : Primrec fun input : Input =>
      (input.1.1.withCriticalMarkers input.2.1,
        ((input.1.2.1, input.1.2.2), input.2.2.1)) :=
    Primrec.pair hextended
      (Primrec.pair (Primrec.pair hleft hright) hbasis)
  have hquery : Primrec fun input : Input =>
      acceptsEquivalenceCertificateCode
        (input.1.1.withCriticalMarkers input.2.1)
        input.1.2.1 input.1.2.2 input.2.2.1 input.2.2.2.1 :=
    acceptsEquivalenceCertificateCode_primrec.comp
      (Primrec.pair hqueryBase hqueryRows)
  have hcritical : Primrec fun input : Input =>
      List.all₂ (acceptsCriticalRowsCode input.1.1 input.2.1 input.2.2.1)
        input.2.2.1 input.2.2.2.2 := by
    apply list_all₂_primrec hbasis hcriticalRows
    let TestInput := (Input × BasisPair) ×
      List (CertificateRow (Action ⊕ ℕ))
    let pack : TestInput → CriticalRowsCheckInput Action := fun input =>
        (input.1.1.1.1,
          (input.1.1.2.1,
            (input.1.1.2.2.1, (input.1.2, input.2))))
    have hcriticalInput : Primrec pack :=
      Primrec.pair (hg.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair
          (hcount.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair
            (hbasis.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))
    have hpacked : Primrec fun input : TestInput =>
        acceptsCriticalRowsCode (pack input).1 (pack input).2.1
          (pack input).2.2.1 (pack input).2.2.2.1
          (pack input).2.2.2.2 :=
      acceptsCriticalRowsCode_primrec.comp hcriticalInput
    exact hpacked.of_eq fun _ => rfl
  exact (Primrec.and.comp
    (Primrec.and.comp hbasisRows hquery) hcritical).of_eq fun _ => rfl

public theorem acceptsSelfCertifyingPackageCode_primrec :
    Primrec fun input : SelfCertifyingInstance Action ×
        SelfCertifyingWitness Action =>
      acceptsSelfCertifyingPackageCode input.1 input.2 :=
  acceptsSelfCertifyingPackagePayloadCode_primrec.of_eq fun _ => rfl

private theorem acceptsSelfCertifyingPackageCode_primrec₂ :
    Primrec₂ fun (input : SelfCertifyingInstance Action)
      (witness : SelfCertifyingWitness Action) =>
      acceptsSelfCertifyingPackageCode input witness :=
  acceptsSelfCertifyingPackageCode_primrec

/-! ## Unbounded enumeration of complete packages -/

/-- A raw instance has a positive package when some finite proposed witness
passes the total checker. -/
@[expose] public def HasSelfCertifyingPackage
    (input : SelfCertifyingInstance Action) : Prop :=
  ∃ witness, acceptsSelfCertifyingPackageCode input witness = true

/-- Decode the `k`th raw package and run the total checker. -/
@[expose] public def acceptingSelfCertifyingPackageIndexTest
    (input : SelfCertifyingInstance Action) (k : ℕ) : Bool :=
  ((Encodable.decode (α := SelfCertifyingWitness Action) k).map fun witness =>
    acceptsSelfCertifyingPackageCode input witness).getD false

/-- Search for the first encoded accepted package. -/
@[expose] public def findAcceptingSelfCertifyingPackageIndex
    (input : SelfCertifyingInstance Action) : Part ℕ :=
  Nat.rfind fun k =>
    Part.some (acceptingSelfCertifyingPackageIndexTest input k)

private theorem acceptingSelfCertifyingPackageIndexTest_computable₂ :
    Computable₂
      (acceptingSelfCertifyingPackageIndexTest (Action := Action)) := by
  have hmap : Computable fun input : SelfCertifyingInstance Action × ℕ =>
      (Encodable.decode (α := SelfCertifyingWitness Action) input.2).map
        fun witness => acceptsSelfCertifyingPackageCode input.1 witness := by
    exact Computable.option_map
      (Computable.decode.comp Computable.snd)
      (Computable₂.mk
        (acceptsSelfCertifyingPackageCode_primrec₂.to_comp.comp
          (Computable.fst.comp Computable.fst) Computable.snd))
  apply Computable₂.mk
  exact (Computable.option_getD hmap
    (Computable.const false)).of_eq fun _ => rfl

public theorem findAcceptingSelfCertifyingPackageIndex_partrec :
    Partrec
      (findAcceptingSelfCertifyingPackageIndex (Action := Action)) := by
  exact Partrec.rfind
    acceptingSelfCertifyingPackageIndexTest_computable₂.partrec₂

public theorem findAcceptingSelfCertifyingPackageIndex_dom_iff
    (input : SelfCertifyingInstance Action) :
    (findAcceptingSelfCertifyingPackageIndex input).Dom ↔
      HasSelfCertifyingPackage input := by
  simp only [findAcceptingSelfCertifyingPackageIndex,
    Nat.rfind_dom, Part.some_dom]
  constructor
  · rintro ⟨k, hk⟩
    cases hdecode : Encodable.decode
        (α := SelfCertifyingWitness Action) k with
    | none =>
        simp [acceptingSelfCertifyingPackageIndexTest, hdecode] at hk
    | some witness =>
        exact ⟨witness, by
          simpa [acceptingSelfCertifyingPackageIndexTest, hdecode] using hk⟩
  · rintro ⟨witness, hwitness⟩
    refine ⟨Encodable.encode witness, ?_⟩
    simpa [acceptingSelfCertifyingPackageIndexTest] using hwitness

/-- Existence of an accepted finite self-certifying package is recursively
enumerable uniformly in the raw grammar and endpoint graphs. -/
public theorem hasSelfCertifyingPackage_re :
    REPred (HasSelfCertifyingPackage (Action := Action)) := by
  exact findAcceptingSelfCertifyingPackageIndex_partrec.dom_re.of_eq fun input =>
    findAcceptingSelfCertifyingPackageIndex_dom_iff input

/-- On the explicit grammar-validity promise, the positive package predicate
is sound for trace equivalence. -/
public theorem traceEquivalent_of_hasSelfCertifyingPackage
    {input : SelfCertifyingInstance Action} (hg : input.1.WellFormed)
    (hpackage : HasSelfCertifyingPackage input) :
    input.1.TraceEquivalent input.2.1 input.2.2 := by
  obtain ⟨witness, hwitness⟩ := hpackage
  exact traceEquivalent_of_acceptsSelfCertifyingPackage hg hwitness

end Computability

end EncodedFirstOrderGrammar

end DCFEquivalence
