module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedBasis
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisOffending

@[expose]
public section

/-!
# Semantic soundness of finite-basis certificates

This file proves the positive checker's semantic direction.  A basis is sound
when every structurally valid ground instance of every listed schema has equal
trace language.  Under that assumption, deriving `NOP` at a word rules out a
shortest counterexample below that word; in particular, an accepted root
certificate proves trace equivalence.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Every schema listed in the finite basis is semantically sound. -/
@[expose] public def SoundBasis
    (g : EncodedFirstOrderGrammar Action) (basis : List BasisPair) : Prop :=
  ∀ pair ∈ basis, g.SoundBasisPair pair

/-- The selected bounded basis is sound by construction. -/
public theorem boundedSoundBasis_sound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) :
    g.SoundBasis (g.boundedSoundBasis bound) := by
  intro pair hpair
  exact g.soundBasisPair_of_mem_boundedSoundBasis bound hpair

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

/-- A matched ground instance of a sound schema is itself trace equivalent,
even when its two finite graph presentations differ by unfolding equivalence. -/
public theorem SoundBasisPair.traceEquivalent_of_matches
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {schema : BasisPair} (hsound : g.SoundBasisPair schema)
    {arguments : List RegularTerm}
    (hargumentCount : arguments.length = schema.arity)
    (harguments : g.groundArgumentsCode arguments = true)
    {left right : RegularTerm}
    (hground : g.groundPairCode left right = true)
    (hleft : RegularTerm.unfoldingEquivalentCode left
      (schema.left.instantiate arguments) = true)
    (hright : RegularTerm.unfoldingEquivalentCode right
      (schema.right.instantiate arguments) = true) :
    g.TraceEquivalent left right := by
  have hschemaWellFormed := hsound.1
  unfold basisPairWellFormedCode at hschemaWellFormed
  rw [Bool.and_eq_true] at hschemaWellFormed
  have hargumentsClosed :=
    referenceClosed_of_groundArgumentsCode g harguments
  have hleftSchemaClosed : schema.left.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschemaWellFormed.1
  have hrightSchemaClosed : schema.right.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschemaWellFormed.2
  have hleftInstanceClosed :
      (schema.left.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed hleftSchemaClosed hargumentsClosed
  have hrightInstanceClosed :
      (schema.right.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed hrightSchemaClosed hargumentsClosed
  have hleftClosed := referenceClosed_of_groundPairCode_left g hground
  have hrightClosed := referenceClosed_of_groundPairCode_right g hground
  have hinstanceEquivalent := hsound.2 arguments hargumentCount harguments
  apply (g.traceEquivalent_iff_forall_traceApprox left right).mpr
  intro depth
  have hleftApprox : g.TraceApprox depth left
      (schema.left.instantiate arguments) :=
    laws.traceApprox_of_unfoldingEquivalentCode depth hleftClosed
      hleftInstanceClosed hleft
  have hrightApprox : g.TraceApprox depth right
      (schema.right.instantiate arguments) :=
    laws.traceApprox_of_unfoldingEquivalentCode depth hrightClosed
      hrightInstanceClosed hright
  have hinstanceApprox : g.TraceApprox depth
      (schema.left.instantiate arguments)
      (schema.right.instantiate arguments) :=
    (g.traceEquivalent_iff_forall_traceApprox _ _).mp
      hinstanceEquivalent depth
  exact hleftApprox.trans (hinstanceApprox.trans hrightApprox.symm)

private def NopSoundInvariant
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) :
    CertificateJudgment Action → Prop
  | .pair _ _ _ => True
  | .nop word => ∀ {suffix : List (Label Action)},
      g.OffendingWord initialLeft initialRight (word ++ suffix) → False
  | .fail => True

private theorem nopSoundInvariant_of_derivable
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hsound : g.SoundBasis basis)
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment) :
    NopSoundInvariant g initialLeft initialRight judgment := by
  induction h with
  | «axiom» => trivial
  | transition => trivial
  | limit => trivial
  | symmetry => trivial
  | @basis word left right pairRef schema arguments hpair hschema hnonempty
      hschemaWellFormed hargumentCount harguments hleft hright ih =>
      intro suffix hinitial
      have hresidual : g.OffendingWord left right suffix :=
        hpair.offendingResidual laws hinitial
      have hground := groundPairCode_of_pair_derivable hpair
      have hschemaSound : g.SoundBasisPair schema :=
        hsound schema (List.mem_of_getElem? hschema)
      have hequivalent : g.TraceEquivalent left right :=
        hschemaSound.traceEquivalent_of_matches laws hargumentCount
          harguments hground hleft hright
      have hsame : g.IsTrace left suffix ↔ g.IsTrace right suffix := by
        change suffix ∈ g.traceLanguage left ↔
          suffix ∈ g.traceLanguage right
        rw [hequivalent]
      exact hresidual.1 (propext hsame)
  | @progression word left right hpair happrox hchildren ihPair ihChildren =>
      intro suffix hinitial
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
              apply ihChildren label henabled
              simpa [List.append_assoc]
                using hinitial
  | rejection => trivial

/-- A derived `NOP` label excludes every shortest distinguishing continuation
below that word. -/
public theorem CertificateDerivable.no_offendingContinuation_of_nop
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hsound : g.SoundBasis basis) {word : List (Label Action)}
    (h : CertificateDerivable g initialLeft initialRight basis (.nop word)) :
    ∀ {suffix : List (Label Action)},
      g.OffendingWord initialLeft initialRight (word ++ suffix) → False :=
  nopSoundInvariant_of_derivable laws hsound h

/-- Root `NOP` is semantically sound for a sound basis. -/
public theorem CertificateDerivable.traceEquivalent_of_nop
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hsound : g.SoundBasis basis)
    (h : CertificateDerivable g initialLeft initialRight basis (.nop [])) :
    g.TraceEquivalent initialLeft initialRight := by
  by_contra hne
  obtain ⟨word, hword⟩ :=
    g.exists_offendingWord_of_not_traceEquivalent hne
  exact h.no_offendingContinuation_of_nop laws hsound (by simpa using hword)

/-- The executable positive certificate checker cannot accept a false pair
when supplied with a sound finite basis. -/
public theorem traceEquivalent_of_acceptsEquivalenceCertificate
    {g : EncodedFirstOrderGrammar Action} (laws : g.GuardedContextLaws)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    (hsound : g.SoundBasis basis) (rows : List (CertificateRow Action))
    (haccept : g.acceptsEquivalenceCertificateCode initialLeft initialRight
      basis rows = true) :
    g.TraceEquivalent initialLeft initialRight := by
  apply CertificateDerivable.traceEquivalent_of_nop laws hsound
  exact g.derivable_nop_of_acceptsEquivalenceCertificate
    initialLeft initialRight basis rows haccept

end EncodedFirstOrderGrammar

end DCFEquivalence
