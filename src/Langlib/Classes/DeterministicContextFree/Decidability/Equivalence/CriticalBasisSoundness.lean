module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisSoundness

@[expose]
public section

/-!
# Soundness from finitely certified critical instances

An arbitrary proposed finite basis cannot be trusted: its own basis rule would
otherwise make a circular certificate immediate.  The standard finite-basis
algorithm breaks that circle by checking, for every schema, one *critical*
ground instance whose finite approximation level is no greater than that of
any other ground instance.

This file isolates the global minimal-counterexample argument.  It deliberately
does not construct the critical arguments; that is an operational theorem about
the private-variable semantics.  Given their exact worst-instance property,
root `NOP` certificates for the queried pair and all critical instances imply
both basis soundness and equivalence of the query, without assuming either.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A finite basis equipped with one ground critical substitution per schema.

`worst` is the useful direction of the critical-instance lemma: agreement of
the critical instance through depth `n` forces agreement of every structurally
valid ground instance through the same depth. -/
public structure CriticalInstanceFamily
    (g : EncodedFirstOrderGrammar Action) (basis : List BasisPair) where
  arguments : BasisPair → List RegularTerm
  schema_wellformed : ∀ schema ∈ basis,
    g.basisPairWellFormedCode schema = true
  argument_count : ∀ schema, schema ∈ basis →
    (arguments schema).length = schema.arity
  arguments_ground : ∀ schema, schema ∈ basis →
    g.groundArgumentsCode (arguments schema) = true
  critical_ground : ∀ schema ∈ basis,
    g.groundPairCode
      (schema.left.instantiate (arguments schema))
      (schema.right.instantiate (arguments schema)) = true
  worst : ∀ {schema : BasisPair}, schema ∈ basis →
    ∀ {other : List RegularTerm},
      other.length = schema.arity →
      g.groundArgumentsCode other = true →
      ∀ depth,
        g.TraceApprox depth
            (schema.left.instantiate (arguments schema))
            (schema.right.instantiate (arguments schema)) →
          g.TraceApprox depth
            (schema.left.instantiate other)
            (schema.right.instantiate other)

@[expose] public def CriticalInstanceFamily.left
    {g : EncodedFirstOrderGrammar Action} {basis : List BasisPair}
    (family : CriticalInstanceFamily g basis) (schema : BasisPair) :
    RegularTerm :=
  schema.left.instantiate (family.arguments schema)

@[expose] public def CriticalInstanceFamily.right
    {g : EncodedFirstOrderGrammar Action} {basis : List BasisPair}
    (family : CriticalInstanceFamily g basis) (schema : BasisPair) :
    RegularTerm :=
  schema.right.instantiate (family.arguments schema)

/-- The finitely many pairs for which a self-certifying package contains a
root certificate: the query followed by one critical instance per basis row. -/
@[expose] public def certifiedPairs
    {g : EncodedFirstOrderGrammar Action} {basis : List BasisPair}
    (family : CriticalInstanceFamily g basis)
    (initialLeft initialRight : RegularTerm) :
    List (RegularTerm × RegularTerm) :=
  (initialLeft, initialRight) ::
    basis.map fun schema => (family.left schema, family.right schema)

private theorem offendingWord_length_unique
    {g : EncodedFirstOrderGrammar Action}
    {left right : RegularTerm} {first second : List (Label Action)}
    (hfirst : g.OffendingWord left right first)
    (hsecond : g.OffendingWord left right second) :
    first.length = second.length := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hsecond.2 first hlt hfirst.1
  · exact hfirst.2 second hgt hsecond.1

/-- Semantic equality of two reference-closed graph presentations follows from
the executable unfolding-equivalence check. -/
public theorem GuardedContextLaws.traceEquivalent_of_unfoldingEquivalentCode
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {left right : RegularTerm}
    (hleft : left.ReferenceClosed) (hright : right.ReferenceClosed)
    (hequivalent :
      RegularTerm.unfoldingEquivalentCode left right = true) :
    g.TraceEquivalent left right := by
  apply (g.traceEquivalent_iff_forall_traceApprox left right).mpr
  intro depth
  exact laws.traceApprox_of_unfoldingEquivalentCode depth
    hleft hright hequivalent

omit [DecidableEq Action] in
private theorem referenceClosed_of_groundArgumentsCode
    (g : EncodedFirstOrderGrammar Action) {arguments : List RegularTerm}
    (harguments : g.groundArgumentsCode arguments = true) :
    ∀ argument ∈ arguments, argument.ReferenceClosed := by
  unfold groundArgumentsCode at harguments
  have hall := List.all_eq_true.mp harguments
  intro argument hargument
  apply RegularTerm.referenceClosed_of_ground
  exact (RegularTerm.groundCode_eq_true_iff g.ranks argument).mp
    (hall argument hargument)

private theorem distinguishing_instance_of_matches
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {schema : BasisPair} {arguments : List RegularTerm}
    (hschema : g.basisPairWellFormedCode schema = true)
    (harguments : g.groundArgumentsCode arguments = true)
    {left right : RegularTerm}
    (hground : g.groundPairCode left right = true)
    (hleft : RegularTerm.unfoldingEquivalentCode left
      (schema.left.instantiate arguments) = true)
    (hright : RegularTerm.unfoldingEquivalentCode right
      (schema.right.instantiate arguments) = true)
    {word : List (Label Action)}
    (hdistinguishing : g.DistinguishingWord left right word) :
    g.DistinguishingWord
      (schema.left.instantiate arguments)
      (schema.right.instantiate arguments) word := by
  unfold basisPairWellFormedCode at hschema
  rw [Bool.and_eq_true] at hschema
  have hargumentsClosed :=
    referenceClosed_of_groundArgumentsCode g harguments
  have hleftSchemaClosed : schema.left.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschema.1
  have hrightSchemaClosed : schema.right.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschema.2
  have hleftInstanceClosed :
      (schema.left.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed hleftSchemaClosed
      hargumentsClosed
  have hrightInstanceClosed :
      (schema.right.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed hrightSchemaClosed
      hargumentsClosed
  have hleftClosed := referenceClosed_of_groundPairCode_left g hground
  have hrightClosed := referenceClosed_of_groundPairCode_right g hground
  have hleftEquivalent : g.TraceEquivalent left
      (schema.left.instantiate arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode hleftClosed
      hleftInstanceClosed hleft
  have hrightEquivalent : g.TraceEquivalent right
      (schema.right.instantiate arguments) :=
    laws.traceEquivalent_of_unfoldingEquivalentCode hrightClosed
      hrightInstanceClosed hright
  intro hsame
  apply hdistinguishing
  have hleftSame : g.IsTrace left word =
      g.IsTrace (schema.left.instantiate arguments) word := by
    apply propext
    change word ∈ g.traceLanguage left ↔
      word ∈ g.traceLanguage (schema.left.instantiate arguments)
    rw [hleftEquivalent]
  have hrightSame : g.IsTrace right word =
      g.IsTrace (schema.right.instantiate arguments) word := by
    apply propext
    change word ∈ g.traceLanguage right ↔
      word ∈ g.traceLanguage (schema.right.instantiate arguments)
    rw [hrightEquivalent]
  exact hleftSame.trans (hsame.trans hrightSame.symm)

private theorem offendingWord_length_le_of_distinguishing
    {g : EncodedFirstOrderGrammar Action}
    {left right : RegularTerm} {offending candidate : List (Label Action)}
    (hoffending : g.OffendingWord left right offending)
    (hcandidate : g.DistinguishingWord left right candidate) :
    offending.length ≤ candidate.length := by
  by_contra hnot
  exact hoffending.2 candidate (Nat.lt_of_not_ge hnot) hcandidate

private theorem exists_short_distinguishing_of_not_traceApprox
    {g : EncodedFirstOrderGrammar Action} {depth : ℕ}
    {left right : RegularTerm}
    (hfailed : ¬g.TraceApprox depth left right) :
    ∃ word, word.length ≤ depth ∧
      g.DistinguishingWord left right word := by
  have hsame : ¬g.SameTracesThrough depth left right := by
    intro hsame
    exact hfailed
      ((g.traceApprox_iff_sameTracesThrough depth left right).mpr hsame)
  unfold SameTracesThrough at hsame
  push_neg at hsame
  obtain ⟨word, hlength, hnotIff⟩ := hsame
  refine ⟨word, hlength, ?_⟩
  unfold DistinguishingWord
  intro heq
  rcases hnotIff with hleft | hright
  · exact hleft.2 (heq ▸ hleft.1)
  · exact hright.1 (heq.symm ▸ hright.2)

private theorem exists_critical_offending_le
    {g : EncodedFirstOrderGrammar Action} {basis : List BasisPair}
    (family : CriticalInstanceFamily g basis)
    {schema : BasisPair} (hschemaMem : schema ∈ basis)
    {arguments : List RegularTerm}
    (hargumentCount : arguments.length = schema.arity)
    (harguments : g.groundArgumentsCode arguments = true)
    {instanceWord : List (Label Action)}
    (hinstance : g.OffendingWord
      (schema.left.instantiate arguments)
      (schema.right.instantiate arguments) instanceWord) :
    ∃ criticalWord,
      g.OffendingWord (family.left schema) (family.right schema)
        criticalWord ∧
      criticalWord.length ≤ instanceWord.length := by
  classical
  have hinstanceFailed : ¬g.TraceApprox instanceWord.length
      (schema.left.instantiate arguments)
      (schema.right.instantiate arguments) := by
    intro happrox
    have hsame := (g.traceApprox_iff_sameTracesThrough
      instanceWord.length _ _).mp happrox instanceWord (by simp)
    exact hinstance.1 (propext hsame)
  have hcriticalFailed : ¬g.TraceApprox instanceWord.length
      (family.left schema) (family.right schema) := by
    intro hcritical
    exact hinstanceFailed
      (family.worst hschemaMem hargumentCount harguments
        instanceWord.length hcritical)
  obtain ⟨candidate, hcandidateLength, hcandidate⟩ :=
    exists_short_distinguishing_of_not_traceApprox hcriticalFailed
  have hcriticalNe :
      ¬g.TraceEquivalent (family.left schema) (family.right schema) :=
    (g.not_traceEquivalent_iff_exists_distinguishingWord _ _).mpr
      ⟨candidate, hcandidate⟩
  obtain ⟨criticalWord, hcriticalWord⟩ :=
    g.exists_offendingWord_of_not_traceEquivalent hcriticalNe
  refine ⟨criticalWord, hcriticalWord, ?_⟩
  exact (offendingWord_length_le_of_distinguishing hcriticalWord
    hcandidate).trans hcandidateLength

private def MinimalNopInvariant
    (g : EncodedFirstOrderGrammar Action)
    (basis : List BasisPair) (family : CriticalInstanceFamily g basis)
    (initialLeft initialRight : RegularTerm)
    (selectedWord : List (Label Action)) :
    CertificateJudgment Action → Prop
  | .pair _ _ _ => True
  | .nop word =>
      (∀ schema ∈ basis, ∀ criticalWord,
        g.OffendingWord (family.left schema) (family.right schema)
          criticalWord →
        selectedWord.length ≤ criticalWord.length) →
      ∀ {suffix : List (Label Action)},
        g.OffendingWord initialLeft initialRight (word ++ suffix) → False
  | .fail => True

private theorem minimalNopInvariant_of_derivable
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {basis : List BasisPair} (family : CriticalInstanceFamily g basis)
    {initialLeft initialRight : RegularTerm}
    {selectedWord : List (Label Action)}
    (hselected : g.OffendingWord initialLeft initialRight selectedWord)
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment) :
    MinimalNopInvariant g basis family initialLeft initialRight
      selectedWord judgment := by
  induction h with
  | «axiom» => trivial
  | transition => trivial
  | limit => trivial
  | symmetry => trivial
  | @basis word left right pairRef schema arguments hpair hschema hnonempty
      hschemaWellFormed hargumentCount harguments hleft hright ih =>
      intro hminimal suffix hinitial
      have hresidual : g.OffendingWord left right suffix :=
        hpair.offendingResidual laws hinitial
      have hground := groundPairCode_of_pair_derivable hpair
      have hinstanceDistinguishes : g.DistinguishingWord
          (schema.left.instantiate arguments)
          (schema.right.instantiate arguments) suffix :=
        distinguishing_instance_of_matches laws hschemaWellFormed
          harguments hground hleft hright hresidual.1
      have hinstanceNe : ¬g.TraceEquivalent
          (schema.left.instantiate arguments)
          (schema.right.instantiate arguments) :=
        (g.not_traceEquivalent_iff_exists_distinguishingWord _ _).mpr
          ⟨suffix, hinstanceDistinguishes⟩
      obtain ⟨instanceWord, hinstanceWord⟩ :=
        g.exists_offendingWord_of_not_traceEquivalent hinstanceNe
      have hinstanceLength : instanceWord.length ≤ suffix.length :=
        offendingWord_length_le_of_distinguishing hinstanceWord
          hinstanceDistinguishes
      have hschemaMem : schema ∈ basis := List.mem_of_getElem? hschema
      obtain ⟨criticalWord, hcriticalWord, hcriticalLength⟩ :=
        exists_critical_offending_le family hschemaMem hargumentCount
          harguments hinstanceWord
      have hlower := hminimal schema hschemaMem criticalWord hcriticalWord
      have hselectedLength : selectedWord.length =
          (word ++ suffix).length :=
        offendingWord_length_unique hselected hinitial
      have hwordPositive : 0 < word.length :=
        Nat.pos_of_ne_zero fun hzero =>
          hnonempty (List.length_eq_zero_iff.mp hzero)
      simp only [List.length_append] at hselectedLength
      omega
  | @progression word left right hpair happrox hchildren ihPair ihChildren =>
      intro hminimal suffix hinitial
      have hresidual : g.OffendingWord left right suffix :=
        hpair.offendingResidual laws hinitial
      cases suffix with
      | nil =>
          exact g.not_distinguishingWord_nil left right hresidual.1
      | cons label tail =>
          cases tail with
          | nil =>
              have honeApprox : g.TraceApprox 1 left right :=
                (g.traceApproxCode_eq_true_iff 1 left right).mp happrox
              have hsame := (g.traceApprox_iff_sameTracesThrough
                1 left right).mp honeApprox [label] (by simp)
              exact hresidual.1 (propext hsame)
          | cons next rest =>
              obtain ⟨left', right', hleftStep, hrightStep⟩ :=
                hresidual.exists_step_of_cons (by simp)
              have henabled : label ∈ g.enabledLabels left :=
                (g.mem_enabledLabels_iff left label).mpr (by
                  simp [hleftStep])
              apply ihChildren label henabled hminimal
              simpa [List.append_assoc] using hinitial
  | rejection => trivial

private theorem false_of_minimal_nop
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {basis : List BasisPair} (family : CriticalInstanceFamily g basis)
    {initialLeft initialRight : RegularTerm}
    {selectedWord : List (Label Action)}
    (hselected : g.OffendingWord initialLeft initialRight selectedWord)
    (hminimal : ∀ schema ∈ basis, ∀ criticalWord,
      g.OffendingWord (family.left schema) (family.right schema)
        criticalWord →
      selectedWord.length ≤ criticalWord.length)
    (hnop : CertificateDerivable g initialLeft initialRight basis (.nop [])) :
    False := by
  have hinvariant := minimalNopInvariant_of_derivable laws family
    hselected hnop
  exact hinvariant hminimal (by simpa using hselected)

private theorem nop_of_mem_certifiedPairs
    {g : EncodedFirstOrderGrammar Action} {basis : List BasisPair}
    (family : CriticalInstanceFamily g basis)
    {initialLeft initialRight : RegularTerm}
    (hinitial : CertificateDerivable g initialLeft initialRight basis (.nop []))
    (hcritical : ∀ schema ∈ basis,
      CertificateDerivable g (family.left schema) (family.right schema)
        basis (.nop []))
    {pair : RegularTerm × RegularTerm}
    (hpair : pair ∈ certifiedPairs family initialLeft initialRight) :
    CertificateDerivable g pair.1 pair.2 basis (.nop []) := by
  simp only [certifiedPairs, List.mem_cons, List.mem_map] at hpair
  rcases hpair with hquery | hbasis
  · subst pair
    exact hinitial
  · obtain ⟨schema, hschema, hpair⟩ := hbasis
    subst pair
    exact hcritical schema hschema

/-- **Finite critical-instance soundness.**  If the query and every critical
instance have root `NOP` derivations under the same proposed finite basis, then
the query is trace equivalent.  The basis is not assumed sound: a globally
shortest false certified pair would force a still shorter false critical pair
whenever its proof used the basis rule. -/
public theorem traceEquivalent_of_criticalCertificates
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {basis : List BasisPair} (family : CriticalInstanceFamily g basis)
    {initialLeft initialRight : RegularTerm}
    (hinitial : CertificateDerivable g initialLeft initialRight basis (.nop []))
    (hcritical : ∀ schema ∈ basis,
      CertificateDerivable g (family.left schema) (family.right schema)
        basis (.nop [])) :
    g.TraceEquivalent initialLeft initialRight := by
  classical
  by_contra hne
  obtain ⟨queryWord, hqueryWord⟩ :=
    g.exists_offendingWord_of_not_traceEquivalent hne
  let pairs := certifiedPairs family initialLeft initialRight
  have hexists : ∃ n, ∃ pair ∈ pairs, ∃ word,
      word.length = n ∧ g.OffendingWord pair.1 pair.2 word :=
    ⟨queryWord.length, (initialLeft, initialRight), by
      simp [pairs, certifiedPairs], queryWord, rfl, hqueryWord⟩
  let leastLength := Nat.find hexists
  obtain ⟨selected, hselectedMem, selectedWord, hselectedLength,
      hselectedWord⟩ := Nat.find_spec hexists
  have hminimal : ∀ {pair : RegularTerm × RegularTerm}, pair ∈ pairs →
      ∀ {word}, g.OffendingWord pair.1 pair.2 word →
        leastLength ≤ word.length := by
    intro pair hpair word hword
    exact Nat.find_min' hexists ⟨pair, hpair, word, rfl, hword⟩
  have hselectedNop : CertificateDerivable g selected.1 selected.2
      basis (.nop []) :=
    nop_of_mem_certifiedPairs family hinitial hcritical hselectedMem
  apply false_of_minimal_nop laws family hselectedWord
  · intro schema hschema criticalWord hcriticalWord
    have hcriticalMem : (family.left schema, family.right schema) ∈ pairs := by
      unfold pairs certifiedPairs
      simp only [List.mem_cons, List.mem_map]
      right
      exact ⟨schema, hschema, rfl⟩
    have hlower := hminimal hcriticalMem hcriticalWord
    simpa [leastLength, hselectedLength] using hlower
  · exact hselectedNop

/-- Critical certificates also establish semantic soundness of the entire
proposed basis.  First apply the global minimal-counterexample theorem to each
critical pair itself; its equivalence then transfers to every ground instance
through `worst`. -/
public theorem soundBasis_of_criticalCertificates
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {basis : List BasisPair} (family : CriticalInstanceFamily g basis)
    (hcritical : ∀ schema ∈ basis,
      CertificateDerivable g (family.left schema) (family.right schema)
        basis (.nop [])) :
    g.SoundBasis basis := by
  intro schema hschema
  refine ⟨family.schema_wellformed schema hschema, ?_⟩
  intro arguments hcount hground
  have hcriticalEquivalent : g.TraceEquivalent
      (family.left schema) (family.right schema) :=
    traceEquivalent_of_criticalCertificates laws family
      (hcritical schema hschema) hcritical
  apply (g.traceEquivalent_iff_forall_traceApprox _ _).mpr
  intro depth
  exact family.worst hschema hcount hground depth
    ((g.traceEquivalent_iff_forall_traceApprox _ _).mp
      hcriticalEquivalent depth)

/-- A complete self-certifying package proves both claims needed by the
positive semidecider: the proposed basis is sound, and the queried pair is
equivalent. -/
public theorem soundBasis_and_traceEquivalent_of_criticalCertificates
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {basis : List BasisPair} (family : CriticalInstanceFamily g basis)
    {initialLeft initialRight : RegularTerm}
    (hinitial : CertificateDerivable g initialLeft initialRight basis (.nop []))
    (hcritical : ∀ schema ∈ basis,
      CertificateDerivable g (family.left schema) (family.right schema)
        basis (.nop [])) :
    g.SoundBasis basis ∧ g.TraceEquivalent initialLeft initialRight :=
  ⟨soundBasis_of_criticalCertificates laws family hcritical,
    traceEquivalent_of_criticalCertificates laws family hinitial hcritical⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
