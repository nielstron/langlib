module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PairReduction
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAToExposingFirstOrder
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FirstOrderCompleteness

@[expose]
public section

/-!
# Semantic compressed pair reduction for deterministic pushdown automata

Paired normalization first puts both source automata into one popping-complete
machine.  The compressed translation then produces an exposing-normal-form
first-order grammar while retaining exactly the observable return
continuations needed for trace equivalence.
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDANormalization

variable {Action : Type} [Fintype Action] [DecidableEq Action]

/-- The compressed exposing trace pair encoded by proof-free paired
normalization data. -/
@[expose] public def PairNormalizationData.exposingTracePair
    (data : PairNormalizationData Action) :
    EncodedFirstOrderGrammar.TracePair (Option Action) :=
  (DPDAToExposingFirstOrder.grammar data.machine,
    DPDAToExposingFirstOrder.configurationTerm data.machine
      data.leftInitial.1 data.leftInitial.2,
    DPDAToExposingFirstOrder.configurationTerm data.machine
      data.rightInitial.1 data.rightInitial.2)

/-- The total proof-free compressed trace-pair compiler before the source
validity promise is used. -/
@[expose] public def pairExposingTraceData
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    EncodedFirstOrderGrammar.TracePair (Option Action) :=
  (pairNormalizationData left right alphabet).exposingTracePair

/-- The compressed exposing trace pair carried by a proof-bearing normalized
pair. -/
@[expose] public def PairNormalizationResult.exposingTracePair
    {left right : EncodedDPDA Action}
    (result : PairNormalizationResult left right) :
    EncodedFirstOrderGrammar.TracePair (Option Action) :=
  (DPDAToExposingFirstOrder.grammar result.machine,
    DPDAToExposingFirstOrder.configurationTerm result.machine
      result.leftInitial.1 result.leftInitial.2,
    DPDAToExposingFirstOrder.configurationTerm result.machine
      result.rightInitial.1 result.rightInitial.2)

@[simp] public theorem
    pairNormalizationResult_exposingTracePair_eq_pairExposingTraceData
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (leftValid : EncodedDPDA.Valid left)
    (rightValid : EncodedDPDA.Valid right)
    (alphabetNodup : alphabet.Nodup)
    (exhaustive : ∀ action, action ∈ alphabet) :
    (pairNormalizationResult left right alphabet leftValid rightValid
      alphabetNodup exhaustive).exposingTracePair =
      pairExposingTraceData left right alphabet := rfl

/-- Normalization followed by the compressed translation produces a valid
exposing first-order trace pair. -/
public theorem PairNormalizationResult.exposingTracePair_valid
    {left right : EncodedDPDA Action}
    (result : PairNormalizationResult left right) :
    EncodedFirstOrderGrammar.ValidExposingTracePair
      result.exposingTracePair := by
  obtain ⟨hwellFormed, hdeterministic, hleftGround,
      hrightGround, hexposing⟩ :=
    DPDAToExposingFirstOrder.configurationTracePair_valid
      result.machine result.normal result.leftState_lt
      result.leftStack_lt result.rightState_lt result.rightStack_lt
  exact ⟨⟨hwellFormed, hdeterministic, hleftGround,
    hrightGround⟩, hexposing⟩

/-- Correctness of the compressed pair reduction: trace equivalence is
exactly equality of the two original final-state languages. -/
public theorem
    PairNormalizationResult.exposingTraceEquivalent_iff_language_eq
    {left right : EncodedDPDA Action}
    (result : PairNormalizationResult left right) :
    result.exposingTracePair.1.TraceEquivalent
        result.exposingTracePair.2.1 result.exposingTracePair.2.2 ↔
      EncodedDPDA.language left = EncodedDPDA.language right := by
  change (DPDAToExposingFirstOrder.grammar result.machine).TraceEquivalent
      (DPDAToExposingFirstOrder.configurationTerm result.machine
        result.leftInitial.1 result.leftInitial.2)
      (DPDAToExposingFirstOrder.configurationTerm result.machine
        result.rightInitial.1 result.rightInitial.2) ↔
    EncodedDPDA.language left = EncodedDPDA.language right
  rw [DPDAToExposingFirstOrder.configurationTerm_traceEquivalent_iff_emptyStackLanguage_eq
    result.normal none result.leftState_lt result.leftStack_lt
    result.rightState_lt result.rightStack_lt]
  rw [result.leftLanguage, result.rightLanguage]
  exact endmarkedLanguage_eq_iff

/-- Valid source automata and an exhaustive duplicate-free alphabet compile
to a valid exposing trace pair. -/
public theorem pairExposingTraceData_valid
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (leftValid : EncodedDPDA.Valid left)
    (rightValid : EncodedDPDA.Valid right)
    (alphabetNodup : alphabet.Nodup)
    (exhaustive : ∀ action, action ∈ alphabet) :
    EncodedFirstOrderGrammar.ValidExposingTracePair
      (pairExposingTraceData left right alphabet) := by
  let result := pairNormalizationResult left right alphabet leftValid
    rightValid alphabetNodup exhaustive
  simpa [result] using result.exposingTracePair_valid

/-- Semantic correctness of the proof-free compressed pair compiler on valid
source automata. -/
public theorem pairExposingTraceData_traceEquivalent_iff_language_eq
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (leftValid : EncodedDPDA.Valid left)
    (rightValid : EncodedDPDA.Valid right)
    (alphabetNodup : alphabet.Nodup)
    (exhaustive : ∀ action, action ∈ alphabet) :
    (pairExposingTraceData left right alphabet).1.TraceEquivalent
        (pairExposingTraceData left right alphabet).2.1
        (pairExposingTraceData left right alphabet).2.2 ↔
      EncodedDPDA.language left = EncodedDPDA.language right := by
  let result := pairNormalizationResult left right alphabet leftValid
    rightValid alphabetNodup exhaustive
  simpa [result] using
    result.exposingTraceEquivalent_iff_language_eq

end DPDANormalization

end DCFEquivalence
