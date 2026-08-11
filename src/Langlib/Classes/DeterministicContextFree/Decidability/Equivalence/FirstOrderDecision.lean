module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SelfCertifyingPackage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SemidecisionMerge
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TraceInequivalence

@[expose]
public section

/-!
# Deciding trace equivalence from complete positive packages

The negative search enumerates finite distinguishing words.  The positive
search enumerates finite self-certifying packages.  Once completeness of those
packages has been established for valid ground instances, the two searches
cover exactly the promised inputs and can be dovetailed into one decision
procedure.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [Primcodable Action] [DecidableEq Action]

/-- The positive/negative semidecision merge works on any promise which
implies ordinary trace-pair validity.  This is the form used by translations
which additionally promise a semantic grammar normal form. -/
public theorem
    traceEquivalence_computablePredOnPromise_of_package_complete_under
    {Promise : TracePair Action → Prop}
    (hvalid : ∀ input : TracePair Action,
      Promise input → ValidTracePair input)
    (hcomplete : ∀ input : TracePair Action,
      Promise input →
      input.1.TraceEquivalent input.2.1 input.2.2 →
      HasSelfCertifyingPackage input) :
    ComputablePredOnPromise Promise
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) := by
  let positive : TracePair Action → Prop :=
    HasSelfCertifyingPackage
  let negative : TracePair Action → Prop := fun input =>
    ¬ input.1.TraceEquivalent input.2.1 input.2.2
  have hpositive : REPred positive :=
    hasSelfCertifyingPackage_re
  have hnegative : REPred negative :=
    traceInequivalence_re
  have hdisjoint : ∀ input : TracePair Action,
      Promise input → positive input → negative input → False := by
    intro input hpromise hpackage hinequivalent
    exact hinequivalent
      (traceEquivalent_of_hasSelfCertifyingPackage
        (hvalid input hpromise).1 hpackage)
  have hcover : ∀ input : TracePair Action,
      Promise input → positive input ∨ negative input := by
    intro input hpromise
    by_cases hequivalent :
        input.1.TraceEquivalent input.2.1 input.2.2
    · exact Or.inl (hcomplete input hpromise hequivalent)
    · exact Or.inr hequivalent
  have hdecidePositive := computablePredOnPromise_of_re_cover
    hpositive hnegative hdisjoint hcover
  apply hdecidePositive.congr
  intro input hpromise
  constructor
  · exact traceEquivalent_of_hasSelfCertifyingPackage
      (hvalid input hpromise).1
  · exact hcomplete input hpromise

/-- The computability wrapper around the mathematical sufficient-basis
theorem.  Its sole semantic input is completeness of the finite positive
packages on valid ground trace pairs. -/
public theorem traceEquivalence_computablePredOnPromise_of_package_complete
    (hcomplete : ∀ input : TracePair Action,
      ValidTracePair input →
      input.1.TraceEquivalent input.2.1 input.2.2 →
      HasSelfCertifyingPackage input) :
    ComputablePredOnPromise (ValidTracePair (Action := Action))
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) :=
  traceEquivalence_computablePredOnPromise_of_package_complete_under
    (fun _ hvalid => hvalid) hcomplete

end EncodedFirstOrderGrammar

end DCFEquivalence
