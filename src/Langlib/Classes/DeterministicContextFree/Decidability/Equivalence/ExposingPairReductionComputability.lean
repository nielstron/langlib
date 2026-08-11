module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ExposingPairReduction
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDANormalizationComputability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAToExposingFirstOrderComputability

@[expose]
public section

/-!
# Effectivity of the compressed DPDA pair reduction

This file composes effective paired normalization with the compressed
exposing-normal-form grammar and configuration-term compilers.
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDANormalization

variable {Action : Type} [Fintype Action] [Primcodable Action]
  [DecidableEq Action]

private theorem pairNormalizationData_machine_computable :
    Computable (fun data : PairNormalizationData Action => data.machine) :=
  ((Primrec.fst.comp
    (Primrec.of_equiv (e := pairNormalizationDataEquiv Action))).to_comp)

private theorem pairNormalizationData_leftInitial_computable :
    Computable (fun data : PairNormalizationData Action =>
      data.leftInitial) :=
  (((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := pairNormalizationDataEquiv Action))).to_comp)

private theorem pairNormalizationData_rightInitial_computable :
    Computable (fun data : PairNormalizationData Action =>
      data.rightInitial) :=
  (((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := pairNormalizationDataEquiv Action))).to_comp)

private theorem pairNormalizationData_exposingGrammar_computable :
    Computable (fun data : PairNormalizationData Action =>
      DPDAToExposingFirstOrder.grammar data.machine) :=
  (DPDAToExposingFirstOrder.grammar_computable
    (Action := Option Action)).comp
      (pairNormalizationData_machine_computable (Action := Action))

private theorem pairNormalizationData_leftExposingTerm_computable :
    Computable (fun data : PairNormalizationData Action =>
      DPDAToExposingFirstOrder.configurationTerm data.machine
        data.leftInitial.1 data.leftInitial.2) :=
  (DPDAToExposingFirstOrder.configurationTerm_computable₂
    (Action := Option Action)).comp
      (pairNormalizationData_machine_computable (Action := Action))
      (pairNormalizationData_leftInitial_computable (Action := Action))

private theorem pairNormalizationData_rightExposingTerm_computable :
    Computable (fun data : PairNormalizationData Action =>
      DPDAToExposingFirstOrder.configurationTerm data.machine
        data.rightInitial.1 data.rightInitial.2) :=
  (DPDAToExposingFirstOrder.configurationTerm_computable₂
    (Action := Option Action)).comp
      (pairNormalizationData_machine_computable (Action := Action))
      (pairNormalizationData_rightInitial_computable (Action := Action))

private theorem pairNormalizationData_exposingTracePair_computable :
    Computable (fun data : PairNormalizationData Action =>
      data.exposingTracePair) := by
  have htrace : Computable (fun data : PairNormalizationData Action =>
      ((DPDAToExposingFirstOrder.grammar data.machine,
        DPDAToExposingFirstOrder.configurationTerm data.machine
          data.leftInitial.1 data.leftInitial.2,
        DPDAToExposingFirstOrder.configurationTerm data.machine
          data.rightInitial.1 data.rightInitial.2) :
        EncodedFirstOrderGrammar.TracePair (Option Action))) :=
    Computable.pair
      (pairNormalizationData_exposingGrammar_computable (Action := Action))
      (Computable.pair
        (pairNormalizationData_leftExposingTerm_computable (Action := Action))
        (pairNormalizationData_rightExposingTerm_computable (Action := Action)))
  apply htrace.of_eq
  intro data
  rfl

/-- Paired normalization followed by the compressed exposing translation is
a total computable transformation of the two raw automata and their explicit
finite action alphabet. -/
public theorem pairExposingTraceData_computable :
    Computable (fun input :
      EncodedDPDA Action × EncodedDPDA Action × List Action =>
      pairExposingTraceData input.1 input.2.1 input.2.2) := by
  apply ((pairNormalizationData_exposingTracePair_computable
    (Action := Action)).comp
      (pairNormalizationData_computable (Action := Action))).of_eq
  intro input
  rfl

end DPDANormalization

end DCFEquivalence
