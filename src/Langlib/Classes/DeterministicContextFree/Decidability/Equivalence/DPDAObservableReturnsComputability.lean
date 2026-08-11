module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAObservableReturns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAToFirstOrderComputability
public import Langlib.Utilities.PrimrecHelpers

@[expose]
public section

/-!
# Computability of arbitrary-input head returns

The semantic file defines the return mask through the already executable least
summary relation.  This file records primitive-recursive evaluators for the
target query machine, individual mask bits, and the retained target list used
as a compressed grammar rank.
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDAObservableReturns

variable {Action : Type} [Fintype Action] [Primcodable Action]
  [DecidableEq Action]

private theorem primrec_list_filterBool_local
    {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) := by
  have hguard : Primrec₂ (fun a b =>
      bif p a b then some b else none) := by
    show Primrec (fun q : A × B =>
      bif p q.1 q.2 then some q.2 else none)
    exact Primrec.cond
      (hp.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)
  have hfilterMap := Primrec.listFilterMap hf hguard
  apply Primrec.of_eq hfilterMap
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih =>
      cases h : p a b <;> simp [List.filter, h, ih]

omit [Fintype Action] [DecidableEq Action] in
private theorem numStates_primrec :
    Primrec (EncodedDPDA.numStates : EncodedDPDA Action → ℕ) := by
  unfold EncodedDPDA.numStates EncodedDPDA
  exact Primrec.succ.comp Primrec.fst

omit [Fintype Action] [DecidableEq Action] in
private theorem numStackSymbols_primrec :
    Primrec (EncodedDPDA.numStackSymbols : EncodedDPDA Action → ℕ) := by
  unfold EncodedDPDA.numStackSymbols EncodedDPDA
  exact Primrec.succ.comp (Primrec.fst.comp Primrec.snd)

omit [Fintype Action] [DecidableEq Action] in
private theorem inputRows_primrec :
    Primrec (EncodedDPDA.inputRows :
      EncodedDPDA Action → List (InputRow Action)) := by
  unfold EncodedDPDA.inputRows EncodedDPDA
  exact Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))

omit [Fintype Action] [DecidableEq Action] in
private theorem epsilonRows_primrec :
    Primrec (EncodedDPDA.epsilonRows :
      EncodedDPDA Action → List EpsilonRow) := by
  unfold EncodedDPDA.epsilonRows EncodedDPDA
  exact Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))

private abbrev TargetInput (Action : Type) :=
  EncodedDPDA Action × ℕ

private def targetFinalCode
    (input : TargetInput Action × ℕ) : Bool :=
  decide (input.2 = input.1.2 % input.1.1.numStates)

omit [Fintype Action] [DecidableEq Action] in
private theorem targetFinalCode_primrec :
    Primrec (targetFinalCode (Action := Action)) := by
  have htarget : Primrec (fun input : TargetInput Action × ℕ =>
      input.1.2 % input.1.1.numStates) :=
    Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst)
      (numStates_primrec.comp (Primrec.fst.comp Primrec.fst))
  unfold targetFinalCode
  exact Primrec.eq.decide.comp Primrec.snd htarget

private def targetFinalCandidate
    (input : TargetInput Action × ℕ) : Option ℕ :=
  bif targetFinalCode input then none else some input.2

omit [Fintype Action] [DecidableEq Action] in
private theorem targetFinalCandidate_primrec :
    Primrec (targetFinalCandidate (Action := Action)) := by
  unfold targetFinalCandidate
  exact Primrec.cond targetFinalCode_primrec
    (Primrec.const none)
    (Primrec.option_some.comp Primrec.snd)

private def targetFinals (input : TargetInput Action) : List ℕ :=
  (List.range input.1.numStates).filterMap fun state =>
    targetFinalCandidate (input, state)

omit [Fintype Action] [DecidableEq Action] in
private theorem targetFinals_primrec :
    Primrec (targetFinals (Action := Action)) := by
  unfold targetFinals
  exact Primrec.listFilterMap
    (Primrec.list_range.comp (numStates_primrec.comp Primrec.fst))
    targetFinalCandidate_primrec.to₂

omit [Fintype Action] [Primcodable Action] [DecidableEq Action] in
private theorem targetFinals_eq (input : TargetInput Action) :
    targetFinals input =
      (List.range input.1.numStates).filter fun state =>
        decide (state ≠ input.2 % input.1.numStates) := by
  unfold targetFinals
  induction List.range input.1.numStates with
  | nil => rfl
  | cons state rest ih =>
      by_cases hstate : state = input.2 % input.1.numStates
      · rw [List.filterMap_cons, List.filter_cons, ih]
        simp [targetFinalCandidate, targetFinalCode, hstate]
      · rw [List.filterMap_cons, List.filter_cons, ih]
        simp [targetFinalCandidate, targetFinalCode, hstate]

private def codedTargetMachine
    (input : TargetInput Action) : EncodedDPDA Action :=
  (input.1.numStates - 1,
    input.1.numStackSymbols - 1,
    0,
    0,
    targetFinals input,
    input.1.inputRows,
    input.1.epsilonRows)

omit [Fintype Action] [DecidableEq Action] in
private theorem codedTargetMachine_primrec :
    Primrec (codedTargetMachine (Action := Action)) := by
  have hstates : Primrec (fun input : TargetInput Action =>
      input.1.numStates) := numStates_primrec.comp Primrec.fst
  have hstack : Primrec (fun input : TargetInput Action =>
      input.1.numStackSymbols) :=
    numStackSymbols_primrec.comp Primrec.fst
  unfold codedTargetMachine
  exact Primrec.pair
    (Primrec.nat_sub.comp hstates (Primrec.const 1))
    (Primrec.pair
      (Primrec.nat_sub.comp hstack (Primrec.const 1))
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair targetFinals_primrec
            (Primrec.pair
              (inputRows_primrec.comp Primrec.fst)
              (epsilonRows_primrec.comp Primrec.fst))))))

omit [Fintype Action] [Primcodable Action] [DecidableEq Action] in
private theorem codedTargetMachine_eq (input : TargetInput Action) :
    codedTargetMachine input = targetMachine input.1 input.2 := by
  unfold codedTargetMachine targetMachine
  rw [targetFinals_eq]

private abbrev HeadReturnInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × ℕ × ℕ)

private def returnQuery
    (input : HeadReturnInput Action) : EncodedDPDA.SummaryTriple :=
  (input.2.1 % input.1.numStates,
    input.2.2.1 % input.1.numStackSymbols,
    input.2.2.2 % input.1.numStates)

omit [Fintype Action] [DecidableEq Action] in
private theorem returnQuery_primrec :
    Primrec (returnQuery (Action := Action)) := by
  have hstates : Primrec (fun input : HeadReturnInput Action =>
      input.1.numStates) := numStates_primrec.comp Primrec.fst
  have hstack : Primrec (fun input : HeadReturnInput Action =>
      input.1.numStackSymbols) :=
    numStackSymbols_primrec.comp Primrec.fst
  unfold returnQuery
  exact Primrec.pair
    (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) hstates)
    (Primrec.pair
      (Primrec.nat_mod.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hstack)
      (Primrec.nat_mod.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hstates))

private def returnTargetMachine
    (input : HeadReturnInput Action) : EncodedDPDA Action :=
  codedTargetMachine (input.1, input.2.2.2)

omit [Fintype Action] [DecidableEq Action] in
private theorem returnTargetMachine_primrec :
    Primrec (returnTargetMachine (Action := Action)) := by
  unfold returnTargetMachine
  exact codedTargetMachine_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private def codedHeadReturnsCode
    (input : HeadReturnInput Action) : Bool :=
  (returnTargetMachine input).leastSummaryRelation.any fun candidate =>
    decide (candidate = returnQuery input)

private theorem codedHeadReturnsCode_primrec :
    Primrec (codedHeadReturnsCode (Action := Action)) := by
  unfold codedHeadReturnsCode
  have hrelation : Primrec (fun input : HeadReturnInput Action =>
      (returnTargetMachine input).leastSummaryRelation) :=
    EncodedDPDA.leastSummaryRelation_primrec.comp
      returnTargetMachine_primrec
  have hpredicate : Primrec₂ (fun (input : HeadReturnInput Action)
      (candidate : EncodedDPDA.SummaryTriple) =>
      decide (candidate = returnQuery input)) := by
    apply Primrec₂.mk
    exact Primrec.eq.decide.comp Primrec.snd
      (returnQuery_primrec.comp Primrec.fst)
  exact primrec_list_any hrelation hpredicate

omit [Fintype Action] [Primcodable Action] in
private theorem codedHeadReturnsCode_eq
    (input : HeadReturnInput Action) :
    codedHeadReturnsCode input =
      headReturnsCode input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  unfold codedHeadReturnsCode headReturnsCode returnTargetMachine returnQuery
  rw [codedTargetMachine_eq]
  induction (targetMachine input.1 input.2.2.2).leastSummaryRelation with
  | nil => rfl
  | cons triple relation ih =>
      simp [ih, eq_comm]

/-- The exact arbitrary-input head-return bit is primitive recursive. -/
public theorem headReturnsCode_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × ℕ × ℕ) =>
      headReturnsCode input.1 input.2.1 input.2.2.1 input.2.2.2) := by
  apply codedHeadReturnsCode_primrec.of_eq
  exact codedHeadReturnsCode_eq

private abbrev HeadInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × ℕ)

private def codedReturnTargets (input : HeadInput Action) : List ℕ :=
  (List.range input.1.numStates).filter fun target =>
    codedHeadReturnsCode
      (input.1, input.2.1, input.2.2, target)

private theorem codedReturnTargets_primrec :
    Primrec (codedReturnTargets (Action := Action)) := by
  unfold codedReturnTargets
  have hitems : Primrec (fun input : HeadInput Action =>
      List.range input.1.numStates) :=
    Primrec.list_range.comp (numStates_primrec.comp Primrec.fst)
  have htest : Primrec₂ (fun (input : HeadInput Action) (target : ℕ) =>
      codedHeadReturnsCode
        (input.1, input.2.1, input.2.2, target)) := by
    apply Primrec₂.mk
    exact codedHeadReturnsCode_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)))
  exact primrec_list_filterBool_local hitems htest

omit [Fintype Action] [Primcodable Action] in
private theorem codedReturnTargets_eq (input : HeadInput Action) :
    codedReturnTargets input =
      returnTargets input.1 input.2.1 input.2.2 := by
  simp [codedReturnTargets, returnTargets, codedHeadReturnsCode_eq]

/-- The ordered list of arbitrary-input return targets is primitive
recursive. -/
public theorem returnTargets_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      returnTargets input.1 input.2.1 input.2.2) := by
  apply codedReturnTargets_primrec.of_eq
  exact codedReturnTargets_eq

private def codedExposedTargets (input : HeadInput Action) : List ℕ :=
  bif (DPDAToFirstOrder.Machine.epsilonStep?
      input.1 input.2.1 input.2.2).isSome then
    []
  else
    codedReturnTargets input

private theorem codedExposedTargets_primrec :
    Primrec (codedExposedTargets (Action := Action)) := by
  unfold codedExposedTargets
  have hepsilon : Primrec (fun input : HeadInput Action =>
      DPDAToFirstOrder.Machine.epsilonStep?
        input.1 input.2.1 input.2.2) :=
    DPDAToFirstOrder.epsilonStep?_primrec
  have hsome : Primrec (fun input : HeadInput Action =>
      (DPDAToFirstOrder.Machine.epsilonStep?
        input.1 input.2.1 input.2.2).isSome) :=
    Primrec.option_isSome.comp hepsilon
  exact Primrec.cond hsome (Primrec.const []) codedReturnTargets_primrec

omit [Fintype Action] [Primcodable Action] in
private theorem codedExposedTargets_eq (input : HeadInput Action) :
    codedExposedTargets input =
      exposedTargets input.1 input.2.1 input.2.2 := by
  cases hstep : DPDAToFirstOrder.Machine.epsilonStep?
      input.1 input.2.1 input.2.2 <;>
    simp [codedExposedTargets, exposedTargets, hstep,
      codedReturnTargets_eq]

/-- The stable-head retained target list, hence the compressed translated
rank, is primitive recursive. -/
public theorem exposedTargets_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      exposedTargets input.1 input.2.1 input.2.2) := by
  apply codedExposedTargets_primrec.of_eq
  exact codedExposedTargets_eq

end DPDAObservableReturns

end DCFEquivalence
