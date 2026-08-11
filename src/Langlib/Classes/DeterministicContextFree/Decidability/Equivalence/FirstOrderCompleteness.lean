module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalPathCompleteness
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FirstOrderDecision

@[expose]
public section

/-!
# Complete bounded bases for first-order trace equivalence

This file is the final semantic assembly boundary.  A complete bound supplies
ordinary root certificates for all equivalent ground queries and stable path
coverage for the canonical critical instances of the very same original
open-sound basis.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Valid ground trace pairs whose grammar additionally satisfies the
exposing-successor normal form used by the balancing construction. -/
@[expose] public def ValidExposingTracePair
    (input : TracePair Action) : Prop :=
  ValidTracePair input ∧ input.1.ExposingNormalForm

/-- One fixed original open-sound basis is complete both for ordinary queries
and for its canonical critical instances in the marker extension. -/
@[expose] public def CompleteOpenSoundBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  (∀ initialLeft initialRight,
      g.groundPairCode initialLeft initialRight = true →
      g.TraceEquivalent initialLeft initialRight →
      CertificateDerivable g initialLeft initialRight
        (g.boundedOpenSoundBasis bound) (.nop [])) ∧
    g.CriticalInstancesEveryPathCoveredAt bound

/-- A grammar admits some complete bounded original open-sound basis. -/
@[expose] public def HasCompleteOpenSoundBound
    (g : EncodedFirstOrderGrammar Action) : Prop :=
  ∃ bound, g.CompleteOpenSoundBound bound

/-- A complete bound gives the exact positive package required for every
valid equivalent trace pair over the grammar. -/
public theorem hasSelfCertifyingPackage_of_completeOpenSoundBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} (hcomplete : g.CompleteOpenSoundBound bound)
    {initialLeft initialRight : RegularTerm}
    (hleftGround : initialLeft.Ground g.ranks)
    (hrightGround : initialRight.Ground g.ranks)
    (hequivalent : g.TraceEquivalent initialLeft initialRight) :
    HasSelfCertifyingPackage (g, (initialLeft, initialRight)) := by
  have hground : g.groundPairCode initialLeft initialRight = true := by
    unfold groundPairCode
    rw [Bool.and_eq_true]
    exact ⟨(RegularTerm.groundCode_eq_true_iff _ _).mpr hleftGround,
      (RegularTerm.groundCode_eq_true_iff _ _).mpr hrightGround⟩
  have hquery := hcomplete.1 initialLeft initialRight hground hequivalent
  have hcritical := criticalInstancesDerivableAt_of_everyPathCovered
    hg hcomplete.2
  exact hasSelfCertifyingPackage_of_boundedOpenSound_derivations
    bound hquery hcritical

section Computability

variable [Primcodable Action]

/-- Complete bounded bases only need to be supplied on the stronger exposing
normal-form promise. -/
public theorem
    traceEquivalence_computablePredOnPromise_of_completeOpenSoundBoundsOnExposing
    (hcomplete : ∀ g : EncodedFirstOrderGrammar Action,
      g.WellFormed → g.ExposingNormalForm →
        g.HasCompleteOpenSoundBound) :
    ComputablePredOnPromise (ValidExposingTracePair (Action := Action))
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) := by
  apply
    traceEquivalence_computablePredOnPromise_of_package_complete_under
      (fun input hpromise => hpromise.1)
  intro input hpromise hequivalent
  obtain ⟨bound, hbound⟩ :=
    hcomplete input.1 hpromise.1.1 hpromise.2
  exact hasSelfCertifyingPackage_of_completeOpenSoundBound
    hpromise.1.1 hbound hpromise.1.2.2.1 hpromise.1.2.2.2
      hequivalent

/-- If every well-formed deterministic first-order grammar has a complete
bounded basis, trace equivalence is decidable on the explicit validity
promise. -/
public theorem traceEquivalence_computablePredOnPromise_of_completeOpenSoundBounds
    (hcomplete : ∀ g : EncodedFirstOrderGrammar Action,
      g.WellFormed → g.HasCompleteOpenSoundBound) :
    ComputablePredOnPromise (ValidTracePair (Action := Action))
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) := by
  apply traceEquivalence_computablePredOnPromise_of_package_complete
  intro input hvalid hequivalent
  obtain ⟨bound, hbound⟩ := hcomplete input.1 hvalid.1
  exact hasSelfCertifyingPackage_of_completeOpenSoundBound
    hvalid.1 hbound hvalid.2.2.1 hvalid.2.2.2 hequivalent

end Computability

end EncodedFirstOrderGrammar

end DCFEquivalence
