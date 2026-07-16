module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDANormalization
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.EndmarkedLanguage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TraceInequivalence

@[expose]
public section

/-!
# Semantic pair reduction for deterministic pushdown automata

Once two encoded DPDAs have been normalized into one popping-complete machine,
their two initial configurations translate to a valid pair of ground terms in
one deterministic first-order grammar.  Trace equivalence of that pair is
exactly equality of the two original final-state languages.
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDANormalization

variable {Action : Type} [Fintype Action] [DecidableEq Action]

/-- The first-order trace pair encoded by the proof-free output of paired
normalization. -/
@[expose] public def PairNormalizationData.tracePair
    (data : PairNormalizationData Action) :
    EncodedFirstOrderGrammar.TracePair (Option Action) :=
  (DPDAToFirstOrder.grammar data.machine,
    DPDAToFirstOrder.configurationTerm data.machine
      data.leftInitial.1 data.leftInitial.2,
    DPDAToFirstOrder.configurationTerm data.machine
      data.rightInitial.1 data.rightInitial.2)

/-- The computable, proof-free trace-pair compiler before its source validity
promise is used. -/
@[expose] public def pairTraceData
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    EncodedFirstOrderGrammar.TracePair (Option Action) :=
  (pairNormalizationData left right alphabet).tracePair

/-- The first-order trace-equivalence instance carried by a normalized pair of
encoded DPDAs. -/
@[expose] public def PairNormalizationResult.tracePair
    {left right : EncodedDPDA Action}
    (result : PairNormalizationResult left right) :
    EncodedFirstOrderGrammar.TracePair (Option Action) :=
  (DPDAToFirstOrder.grammar result.machine,
    DPDAToFirstOrder.configurationTerm result.machine
      result.leftInitial.1 result.leftInitial.2,
    DPDAToFirstOrder.configurationTerm result.machine
      result.rightInitial.1 result.rightInitial.2)

@[simp] public theorem pairNormalizationResult_tracePair_eq_pairTraceData
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (leftValid : EncodedDPDA.Valid left)
    (rightValid : EncodedDPDA.Valid right)
    (alphabetNodup : alphabet.Nodup)
    (exhaustive : ∀ action, action ∈ alphabet) :
    (pairNormalizationResult left right alphabet leftValid rightValid
      alphabetNodup exhaustive).tracePair =
      pairTraceData left right alphabet := rfl

/-- Normalization produces a syntactically valid deterministic first-order
grammar instance with two ground terms. -/
public theorem PairNormalizationResult.tracePair_valid
    {left right : EncodedDPDA Action}
    (result : PairNormalizationResult left right) :
    EncodedFirstOrderGrammar.ValidTracePair result.tracePair := by
  refine ⟨DPDAToFirstOrder.grammar_wellFormed result.machine,
    DPDAToFirstOrder.grammar_actionDeterministicCode result.machine,
    ?_, ?_⟩
  · exact DPDAToFirstOrder.configurationTerm_ground result.machine
      result.leftState_lt result.leftStack_lt
  · exact DPDAToFirstOrder.configurationTerm_ground result.machine
      result.rightState_lt result.rightStack_lt

/-- Correctness of the pair reduction: first-order trace equivalence is
equivalent to equality of the two source DPDA languages. -/
public theorem PairNormalizationResult.traceEquivalent_iff_language_eq
    {left right : EncodedDPDA Action}
    (result : PairNormalizationResult left right) :
    result.tracePair.1.TraceEquivalent
        result.tracePair.2.1 result.tracePair.2.2 ↔
      EncodedDPDA.language left = EncodedDPDA.language right := by
  change (DPDAToFirstOrder.grammar result.machine).TraceEquivalent
      (DPDAToFirstOrder.configurationTerm result.machine
        result.leftInitial.1 result.leftInitial.2)
      (DPDAToFirstOrder.configurationTerm result.machine
        result.rightInitial.1 result.rightInitial.2) ↔
    EncodedDPDA.language left = EncodedDPDA.language right
  rw [DPDAToFirstOrder.configurationTerm_traceEquivalent_iff_emptyStackLanguage_eq
    result.normal none result.leftState_lt result.leftStack_lt
    result.rightState_lt result.rightStack_lt]
  rw [result.leftLanguage, result.rightLanguage]
  exact endmarkedLanguage_eq_iff

/-- On valid source automata and an exhaustive duplicate-free alphabet, the
proof-free compiler produces a valid first-order trace-equivalence instance. -/
public theorem pairTraceData_valid
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (leftValid : EncodedDPDA.Valid left)
    (rightValid : EncodedDPDA.Valid right)
    (alphabetNodup : alphabet.Nodup)
    (exhaustive : ∀ action, action ∈ alphabet) :
    EncodedFirstOrderGrammar.ValidTracePair
      (pairTraceData left right alphabet) := by
  let result := pairNormalizationResult left right alphabet leftValid
    rightValid alphabetNodup exhaustive
  simpa [result] using result.tracePair_valid

/-- Semantic correctness of the proof-free paired compiler on valid source
automata. -/
public theorem pairTraceData_traceEquivalent_iff_language_eq
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (leftValid : EncodedDPDA.Valid left)
    (rightValid : EncodedDPDA.Valid right)
    (alphabetNodup : alphabet.Nodup)
    (exhaustive : ∀ action, action ∈ alphabet) :
    (pairTraceData left right alphabet).1.TraceEquivalent
        (pairTraceData left right alphabet).2.1
        (pairTraceData left right alphabet).2.2 ↔
      EncodedDPDA.language left = EncodedDPDA.language right := by
  let result := pairNormalizationResult left right alphabet leftValid
    rightValid alphabetNodup exhaustive
  simpa [result] using result.traceEquivalent_iff_language_eq

end DPDANormalization

end DCFEquivalence
