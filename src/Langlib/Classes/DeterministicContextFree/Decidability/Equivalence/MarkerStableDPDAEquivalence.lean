module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.MarkerStableUnifiedCompleteness

@[expose]
public section

/-!
# Encoded-DPDA equivalence from one marker-stable stair theorem

Unified marker-stable completeness removes the formerly separate ordinary
query stair premise.  The compressed exposing compiler therefore reduces
encoded deterministic pushdown language equivalence to one remaining
first-order statement: every well-formed exposing grammar admits a uniform
marker-stable witnessed regular active stair base.
-/

open DCFEquivalence

namespace DCFEncodedDPDA

namespace EncodedDPDA

variable {Action : Type} [Fintype Action] [Primcodable Action]
  [DecidableEq Action]

/-- Pull the unified marker-stable trace-equivalence theorem back along any
computable compiler into exposing first-order trace pairs. -/
public theorem
    dcf_computableEquivalence_of_exposingTraceCompiler_of_uniformMarkerStableStairBases
    {TraceAction : Type} [Primcodable TraceAction] [DecidableEq TraceAction]
    (compile : EquivalenceInput Action →
      EncodedFirstOrderGrammar.TracePair TraceAction)
    (compileComputable : Computable compile)
    (compileValid : ∀ input, input.Valid →
      EncodedFirstOrderGrammar.ValidExposingTracePair (compile input))
    (compileCorrect : ∀ input, input.Valid →
      ((compile input).1.TraceEquivalent
          (compile input).2.1 (compile input).2.2 ↔
        input.LanguageEquivalent))
    (hstair : ∀ g : EncodedFirstOrderGrammar TraceAction,
      g.WellFormed → g.ExposingNormalForm →
      ∃ width,
        g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ComputableEquivalence DCF
      (language : EncodedDPDA Action → Language Action)
      (valid := Valid) := by
  apply dcf_computableEquivalence_of_traceCompiler
    compile compileComputable compileValid compileCorrect
  exact
    DCFEquivalence.EncodedFirstOrderGrammar.traceEquivalence_computablePredOnPromise_of_uniformMarkerStableStairBasesOnExposing
      hstair

/-- Final concrete encoded-DPDA endpoint.  All compiler, validity,
computability, and semantic-translation obligations are discharged; only the
uniform marker-stable stair theorem on exposing grammars remains. -/
public theorem
    dcf_computableEquivalence_of_uniformMarkerStableStairBasesOnExposing
    (hstair : ∀ g : EncodedFirstOrderGrammar (Option Action),
      g.WellFormed → g.ExposingNormalForm →
      ∃ width,
        g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ComputableEquivalence DCF
      (language : EncodedDPDA Action → Language Action)
      (valid := Valid) :=
  dcf_computableEquivalence_of_exposingTraceCompiler_of_uniformMarkerStableStairBases
    (equivalenceExposingTracePair (Action := Action))
    (equivalenceExposingTracePair_computable (Action := Action))
    equivalenceExposingTracePair_valid
    equivalenceExposingTracePair_traceEquivalent_iff
    hstair

end EncodedDPDA

end DCFEncodedDPDA
