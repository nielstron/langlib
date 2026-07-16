module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ActiveHeadAssembly
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ConcreteReturnClassifier
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.EmptyReturns
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.NoEpsilonCycleConsequences

/-!
# LR(1) assembly from productive anchor synchronization

Both semantic obligations for the productive characteristic grammar reduce
to one boundary-sensitive fact about paired last-visible anchors.  This file
keeps that dependency explicit: the same synchronization theorem determines
epsilon-bearing introducing heads and classifies productive empty returns.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Boundary-sensitive synchronization of productive paired anchors is the
single semantic input needed for the characteristic grammar's LR(1) proof. -/
public theorem characteristicGrammar_isLR1_of_productivePositions
    (M : DPDA Q T S)
    (hpositions : ProductivePairedVisibleAnchorPositionsEqual M) :
    (characteristicGrammar M).IsLRk 1 :=
  characteristicGrammar_isLR1_of_edgeSemantics M
    (introducingEdgesUnique_of_activeHeadUnique M
      (activeHeadUnique_of_epsilonIntroducingHeadsUnique M
        (epsilonIntroducingHeadsUnique_of_productivePositions M
          hpositions)))
    (emptyReturnEdgesUnique_of_concretePairsClassified M
      (concreteEmptyReturnPairsClassified_of_productivePositions M
        hpositions))

end

end DPDA_to_LR

