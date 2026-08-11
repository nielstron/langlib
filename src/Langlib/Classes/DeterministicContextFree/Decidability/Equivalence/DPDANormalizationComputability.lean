module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDANormalization
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAToFirstOrderComputability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PairReduction
public import Langlib.Utilities.PrimrecHelpers

@[expose]
public section

/-!
# Computability of DPDA pair normalization

The semantic normalization is intentionally kept in `DPDANormalization`.
This file supplies a compact, fixed-alphabet evaluator proof for its data
projection and then composes it with the first-order grammar compiler.
-/
open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDANormalization

variable {Action : Type} [Primcodable Action] [DecidableEq Action]

private theorem numStates_primrec {T : Type} [Primcodable T] :
    Primrec (EncodedDPDA.numStates : EncodedDPDA T → ℕ) := by
  unfold EncodedDPDA.numStates EncodedDPDA
  exact Primrec.succ.comp Primrec.fst

private theorem numStackSymbols_primrec {T : Type} [Primcodable T] :
    Primrec (EncodedDPDA.numStackSymbols : EncodedDPDA T → ℕ) := by
  unfold EncodedDPDA.numStackSymbols EncodedDPDA
  exact Primrec.succ.comp (Primrec.fst.comp Primrec.snd)

private theorem initialIndex_primrec {T : Type} [Primcodable T] :
    Primrec (EncodedDPDA.initialIndex : EncodedDPDA T → ℕ) := by
  unfold EncodedDPDA.initialIndex EncodedDPDA
  exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem startIndex_primrec {T : Type} [Primcodable T] :
    Primrec (EncodedDPDA.startIndex : EncodedDPDA T → ℕ) := by
  unfold EncodedDPDA.startIndex EncodedDPDA
  exact Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem finalIndices_primrec {T : Type} [Primcodable T] :
    Primrec (EncodedDPDA.finalIndices : EncodedDPDA T → List ℕ) := by
  unfold EncodedDPDA.finalIndices EncodedDPDA
  exact Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd)))

private theorem epsilonRows_primrec {T : Type} [Primcodable T] :
    Primrec (EncodedDPDA.epsilonRows : EncodedDPDA T → List EpsilonRow) := by
  unfold EncodedDPDA.epsilonRows EncodedDPDA
  exact Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))

private theorem list_memBool_primrec {T : Type}
    [Primcodable T] [DecidableEq T] :
    Primrec₂ (fun (items : List T) (value : T) =>
      decide (value ∈ items)) := by
  apply Primrec₂.mk
  have htest : Primrec₂ (fun (input : List T × T) (candidate : T) =>
      decide (candidate = input.2)) := by
    apply Primrec₂.mk
    exact Primrec.eq.decide.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  have hany : Primrec (fun input : List T × T =>
      input.1.any fun candidate => decide (candidate = input.2)) :=
    primrec_list_any Primrec.fst htest
  apply hany.of_eq
  rintro ⟨items, value⟩
  induction items with
  | nil => simp
  | cons head tail ih =>
      have ih' : (tail.any fun candidate => decide (value = candidate)) =
          decide (value ∈ tail) := by
        simpa [eq_comm] using ih
      simp [ih', eq_comm]

private theorem computable_fixedList_map
    {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    (items : List B) {f : A → B → C} (hf : Computable₂ f) :
    Computable fun a => items.map (f a) := by
  induction items with
  | nil => exact Computable.const []
  | cons item items ih =>
      exact Computable.list_cons.comp
        (hf.comp Computable.id (Computable.const item)) ih

private theorem computable_fixedList_flatMap
    {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    (items : List B) {f : A → B → List C} (hf : Computable₂ f) :
    Computable fun a => items.flatMap (f a) := by
  have hmapped := computable_fixedList_map items hf
  apply (Primrec.list_flatten.to_comp.comp hmapped).of_eq
  intro a
  rfl

private theorem computable_range_map
    {A C : Type} [Primcodable A] [Primcodable C]
    {bound : A → ℕ} {f : A → ℕ → C}
    (hbound : Computable bound) (hf : Computable₂ f) :
    Computable fun a => (List.range (bound a)).map (f a) := by
  have hstep : Computable₂ (fun (a : A) (state : ℕ × List C) =>
      state.2 ++ [f a state.1]) := by
    apply Computable₂.mk
    exact Computable.list_concat.comp
      (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
  have hrec := Computable.nat_rec hbound (Computable.const ([] : List C)) hstep
  apply hrec.of_eq
  intro a
  induction bound a with
  | zero => rfl
  | succ n ih => simp [ih, List.range_succ]

private theorem computable_range_filterMap
    {A C : Type} [Primcodable A] [Primcodable C]
    {bound : A → ℕ} {f : A → ℕ → Option C}
    (hbound : Computable bound) (hf : Computable₂ f) :
    Computable fun a => (List.range (bound a)).filterMap (f a) := by
  have hmapped := computable_range_map hbound hf
  have hfilter : Computable
      (fun items : List (Option C) => items.filterMap id) :=
    (Primrec.listFilterMap Primrec.id Primrec.snd.to₂).to_comp
  apply (hfilter.comp hmapped).of_eq
  intro a
  induction List.range (bound a) with
  | nil => rfl
  | cons n rest ih =>
      cases h : f a n <;> simp [h, ih]

private theorem computable_range_flatMap
    {A C : Type} [Primcodable A] [Primcodable C]
    {bound : A → ℕ} {f : A → ℕ → List C}
    (hbound : Computable bound) (hf : Computable₂ f) :
    Computable fun a => (List.range (bound a)).flatMap (f a) := by
  have hmapped := computable_range_map hbound hf
  apply (Primrec.list_flatten.to_comp.comp hmapped).of_eq
  intro a
  rfl

private theorem numStates_computable {T : Type} [Primcodable T] :
    Computable (EncodedDPDA.numStates : EncodedDPDA T → ℕ) := by
  exact numStates_primrec.to_comp

private theorem numStackSymbols_computable {T : Type} [Primcodable T] :
    Computable (EncodedDPDA.numStackSymbols : EncodedDPDA T → ℕ) := by
  exact numStackSymbols_primrec.to_comp

private theorem initialIndex_computable {T : Type} [Primcodable T] :
    Computable (EncodedDPDA.initialIndex : EncodedDPDA T → ℕ) := by
  exact initialIndex_primrec.to_comp

private theorem startIndex_computable {T : Type} [Primcodable T] :
    Computable (EncodedDPDA.startIndex : EncodedDPDA T → ℕ) := by
  exact startIndex_primrec.to_comp

private theorem finalIndices_computable {T : Type} [Primcodable T] :
    Computable (EncodedDPDA.finalIndices : EncodedDPDA T → List ℕ) := by
  exact finalIndices_primrec.to_comp

private theorem epsilonRows_computable {T : Type} [Primcodable T] :
    Computable (EncodedDPDA.epsilonRows : EncodedDPDA T → List EpsilonRow) := by
  exact epsilonRows_primrec.to_comp

private theorem selectedEpsilon?_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      selectedEpsilon? input.1 input.2.1 input.2.2) := by
  apply DPDAToFirstOrder.epsilonStep?_primrec.of_eq
  intro input
  exact (selectedEpsilon?_eq_epsilonStep?
    input.1 input.2.1 input.2.2).symm

private theorem selectedEpsilon?_computable :
    Computable (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      selectedEpsilon? input.1 input.2.1 input.2.2) :=
  selectedEpsilon?_primrec.to_comp

private theorem selectedInput?_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × Action × ℕ) =>
      selectedInput? input.1 input.2.1 input.2.2.1 input.2.2.2) := by
  apply DPDAToFirstOrder.deterministicInputStep?_primrec.of_eq
  intro input
  exact (selectedInput?_eq_inputStep?
    input.1 input.2.1 input.2.2.1 input.2.2.2).symm

private theorem selectedInput?_computable :
    Computable (fun input : EncodedDPDA Action × (ℕ × Action × ℕ) =>
      selectedInput? input.1 input.2.1 input.2.2.1 input.2.2.2) :=
  selectedInput?_primrec.to_comp

private abbrev PairInput (Action : Type) :=
  EncodedDPDA Action × EncodedDPDA Action × List Action

private theorem indexOf_primrec :
    Primrec (fun input : List Action × Action =>
      Endmarked.indexOf input.2 input.1) := by
  have hpredicate : Primrec₂ (fun (input : List Action × Action)
      (candidate : Action) => decide (candidate = input.2)) := by
    apply Primrec₂.mk
    exact Primrec.eq.decide.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  have hfind : Primrec (fun input : List Action × Action =>
      input.1.findIdx fun candidate => decide (candidate = input.2)) :=
    Primrec.list_findIdx Primrec.fst hpredicate
  exact hfind

private theorem normalizedFinalIndices_primrec :
    Primrec (normalizedFinalIndices : EncodedDPDA Action → List ℕ) := by
  have hmod : Primrec₂ (fun (machine : EncodedDPDA Action) (q : ℕ) =>
      q % machine.numStates) := by
    apply Primrec₂.mk
    exact Primrec.nat_mod.comp Primrec.snd
      (numStates_primrec.comp Primrec.fst)
  exact Primrec.list_map finalIndices_primrec hmod

private theorem isFinalIndex_primrec :
    Primrec (fun input : EncodedDPDA Action × ℕ =>
      Endmarked.isFinalIndex input.1 input.2) := by
  have hitems : Primrec (fun input : EncodedDPDA Action × ℕ =>
      normalizedFinalIndices input.1) :=
    normalizedFinalIndices_primrec.comp Primrec.fst
  have hvalue : Primrec (fun input : EncodedDPDA Action × ℕ =>
      input.2 % input.1.numStates) :=
    Primrec.nat_mod.comp Primrec.snd
      (numStates_primrec.comp Primrec.fst)
  apply (list_memBool_primrec.comp hitems hvalue).of_eq
  intro input
  rfl

private theorem endmarkedAlphabet_primrec :
    Primrec (endmarkedAlphabet : List Action → List (Option Action)) := by
  have hmapped : Primrec (fun alphabet : List Action =>
      alphabet.map some) :=
    Primrec.list_map Primrec.id
      (Primrec.option_some.comp Primrec.snd)
  exact Primrec.list_cons.comp (Primrec.const none) hmapped

/-! The endmarker construction mentions two raw machines simultaneously.  Its
fully expanded product encoding is large enough to make instance synthesis
dominate elaboration.  Internally we therefore pass their natural-number
codes, decode once at each projection, and compose with `encode` only at the
public boundary. -/

private abbrev CodedPairInput (Action : Type) :=
  ℕ × ℕ × List Action

private def defaultEncodedDPDA : EncodedDPDA Action :=
  (0, 0, 0, 0, [], [], [])

private def machineOfCode (code : ℕ) : EncodedDPDA Action :=
  (Encodable.decode code).getD defaultEncodedDPDA

private theorem machineOfCode_primrec :
    Primrec (machineOfCode (Action := Action)) := by
  exact Primrec.option_getD.comp Primrec.decode
    (Primrec.const (defaultEncodedDPDA (Action := Action)))

@[simp] private theorem machineOfCode_encode
    (machine : EncodedDPDA Action) :
    machineOfCode (Encodable.encode machine) = machine := by
  simp [machineOfCode]

private theorem codedLeft_primrec :
    Primrec (fun input : CodedPairInput Action =>
      machineOfCode (Action := Action) input.1) :=
  machineOfCode_primrec.comp Primrec.fst

private theorem codedRight_primrec :
    Primrec (fun input : CodedPairInput Action =>
      machineOfCode (Action := Action) input.2.1) :=
  machineOfCode_primrec.comp (Primrec.fst.comp Primrec.snd)

private theorem codedAlphabet_primrec :
    Primrec (fun input : CodedPairInput Action => input.2.2) :=
  Primrec.snd.comp Primrec.snd

private def codedRightPendingBase (input : CodedPairInput Action) : ℕ :=
  Endmarked.rightPendingBase
    (machineOfCode (Action := Action) input.1) input.2.2

private theorem codedRightPendingBase_primrec :
    Primrec (codedRightPendingBase (Action := Action)) := by
  unfold codedRightPendingBase Endmarked.rightPendingBase
    Endmarked.leftPendingBase
  exact Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.nat_mul.comp
      (numStates_primrec.comp (codedLeft_primrec (Action := Action)))
      (Primrec.list_length.comp (codedAlphabet_primrec (Action := Action))))

private def codedAcceptState (input : CodedPairInput Action) : ℕ :=
  codedRightPendingBase (Action := Action) input +
    (machineOfCode (Action := Action) input.2.1).numStates * input.2.2.length

private theorem codedAcceptState_primrec :
    Primrec (codedAcceptState (Action := Action)) := by
  unfold codedAcceptState
  exact Primrec.nat_add.comp (codedRightPendingBase_primrec (Action := Action))
    (Primrec.nat_mul.comp
      (numStates_primrec.comp (codedRight_primrec (Action := Action)))
      (Primrec.list_length.comp (codedAlphabet_primrec (Action := Action))))

private def codedRejectState (input : CodedPairInput Action) : ℕ :=
  codedAcceptState (Action := Action) input + 1

private theorem codedRejectState_primrec :
    Primrec (codedRejectState (Action := Action)) := by
  unfold codedRejectState
  exact Primrec.succ.comp (codedAcceptState_primrec (Action := Action))

private def codedStateCount (input : CodedPairInput Action) : ℕ :=
  codedRejectState (Action := Action) input + 1

private theorem codedStateCount_primrec :
    Primrec (codedStateCount (Action := Action)) := by
  unfold codedStateCount
  exact Primrec.succ.comp (codedRejectState_primrec (Action := Action))

private theorem codedStackCount_primrec :
    Primrec (fun input : CodedPairInput Action =>
      Endmarked.stackCount (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1)) := by
  unfold Endmarked.stackCount
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.const 1)
      (numStackSymbols_primrec.comp (codedLeft_primrec (Action := Action))))
    (numStackSymbols_primrec.comp (codedRight_primrec (Action := Action)))

private abbrev CodedPendingInput (Action : Type) :=
  CodedPairInput Action × (ℕ × Action)

private def codedLeftPending (input : CodedPendingInput Action) : ℕ :=
  Endmarked.leftPending (machineOfCode (Action := Action) input.1.1)
    input.1.2.2 input.2.1 input.2.2

private theorem codedLeftPending_primrec :
    Primrec (codedLeftPending (Action := Action)) := by
  have hstates : Primrec (fun input : CodedPendingInput Action =>
      (machineOfCode (Action := Action) input.1.1).numStates) :=
    numStates_primrec.comp ((codedLeft_primrec (Action := Action)).comp Primrec.fst)
  have hq : Primrec (fun input : CodedPendingInput Action =>
      input.2.1 % (machineOfCode (Action := Action) input.1.1).numStates) :=
    Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) hstates
  have hlength : Primrec (fun input : CodedPendingInput Action =>
      input.1.2.2.length) :=
    Primrec.list_length.comp ((codedAlphabet_primrec (Action := Action)).comp Primrec.fst)
  have hindex : Primrec (fun input : CodedPendingInput Action =>
      Endmarked.indexOf input.2.2 input.1.2.2) :=
    indexOf_primrec.comp
      (Primrec.pair ((codedAlphabet_primrec (Action := Action)).comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  unfold codedLeftPending Endmarked.leftPending Endmarked.pendingIndex
    Endmarked.leftPendingBase
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.const 2)
      (Primrec.nat_mul.comp hq hlength)) hindex

private def codedRightPending (input : CodedPendingInput Action) : ℕ :=
  Endmarked.rightPending (machineOfCode (Action := Action) input.1.1)
    (machineOfCode (Action := Action) input.1.2.1) input.1.2.2
    input.2.1 input.2.2

private theorem codedRightPending_primrec :
    Primrec (codedRightPending (Action := Action)) := by
  have hstates : Primrec (fun input : CodedPendingInput Action =>
      (machineOfCode (Action := Action) input.1.2.1).numStates) :=
    numStates_primrec.comp ((codedRight_primrec (Action := Action)).comp Primrec.fst)
  have hq : Primrec (fun input : CodedPendingInput Action =>
      input.2.1 % (machineOfCode (Action := Action) input.1.2.1).numStates) :=
    Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) hstates
  have hlength : Primrec (fun input : CodedPendingInput Action =>
      input.1.2.2.length) :=
    Primrec.list_length.comp ((codedAlphabet_primrec (Action := Action)).comp Primrec.fst)
  have hindex : Primrec (fun input : CodedPendingInput Action =>
      Endmarked.indexOf input.2.2 input.1.2.2) :=
    indexOf_primrec.comp
      (Primrec.pair ((codedAlphabet_primrec (Action := Action)).comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  unfold codedRightPending Endmarked.rightPending Endmarked.pendingIndex
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp
      ((codedRightPendingBase_primrec (Action := Action)).comp Primrec.fst)
      (Primrec.nat_mul.comp hq hlength)) hindex

private def codedLeftStack (input : CodedPairInput Action × ℕ) : ℕ :=
  Endmarked.leftStack (machineOfCode (Action := Action) input.1.1) input.2

private theorem codedLeftStack_primrec :
    Primrec (codedLeftStack (Action := Action)) := by
  unfold codedLeftStack Endmarked.leftStack
  have hstack : Primrec (fun input : CodedPairInput Action × ℕ =>
      (machineOfCode (Action := Action) input.1.1).numStackSymbols) :=
    numStackSymbols_primrec.comp
      ((codedLeft_primrec (Action := Action)).comp Primrec.fst)
  apply (Primrec.succ.comp
    (Primrec.nat_mod.comp Primrec.snd hstack)).of_eq
  intro input
  omega

private def codedRightStack (input : CodedPairInput Action × ℕ) : ℕ :=
  Endmarked.rightStack (machineOfCode (Action := Action) input.1.1)
    (machineOfCode (Action := Action) input.1.2.1) input.2

private theorem codedRightStack_primrec :
    Primrec (codedRightStack (Action := Action)) := by
  unfold codedRightStack Endmarked.rightStack
  have hleftStack : Primrec (fun input : CodedPairInput Action × ℕ =>
      (machineOfCode (Action := Action) input.1.1).numStackSymbols) :=
    numStackSymbols_primrec.comp
      ((codedLeft_primrec (Action := Action)).comp Primrec.fst)
  have hrightStack : Primrec (fun input : CodedPairInput Action × ℕ =>
      (machineOfCode (Action := Action) input.1.2.1).numStackSymbols) :=
    numStackSymbols_primrec.comp
      ((codedRight_primrec (Action := Action)).comp Primrec.fst)
  apply (Primrec.nat_add.comp
    (Primrec.succ.comp hleftStack)
    (Primrec.nat_mod.comp Primrec.snd hrightStack)).of_eq
  intro input
  omega

private def codedMapLeftReplacement
    (input : CodedPairInput Action × List ℕ) : List ℕ :=
  input.2.map fun Z => codedLeftStack (Action := Action) (input.1, Z)

private theorem codedMapLeftReplacement_primrec :
    Primrec (codedMapLeftReplacement (Action := Action)) := by
  unfold codedMapLeftReplacement
  have hstep : Primrec₂ (fun (input : CodedPairInput Action × List ℕ)
      (Z : ℕ) => codedLeftStack (Action := Action) (input.1, Z)) := by
    apply Primrec₂.mk
    exact (codedLeftStack_primrec (Action := Action)).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_map Primrec.snd hstep

private def codedMapRightReplacement
    (input : CodedPairInput Action × List ℕ) : List ℕ :=
  input.2.map fun Z => codedRightStack (Action := Action) (input.1, Z)

private theorem codedMapRightReplacement_primrec :
    Primrec (codedMapRightReplacement (Action := Action)) := by
  unfold codedMapRightReplacement
  have hstep : Primrec₂ (fun (input : CodedPairInput Action × List ℕ)
      (Z : ℕ) => codedRightStack (Action := Action) (input.1, Z)) := by
    apply Primrec₂.mk
    exact (codedRightStack_primrec (Action := Action)).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_map Primrec.snd hstep

private def codedLeftIsFinalIndex
    (input : CodedPairInput Action × ℕ) : Bool :=
  let machine := machineOfCode (Action := Action) input.1.1
  decide (input.2 % machine.numStates ∈
    machine.finalIndices.map fun q => q % machine.numStates)

private theorem codedLeftIsFinalIndex_primrec :
    Primrec (codedLeftIsFinalIndex (Action := Action)) := by
  unfold codedLeftIsFinalIndex
  have hmachine : Primrec (fun input : CodedPairInput Action × ℕ =>
      machineOfCode (Action := Action) input.1.1) :=
    (codedLeft_primrec (Action := Action)).comp Primrec.fst
  have hstates := numStates_primrec.comp hmachine
  have hfinals := finalIndices_primrec.comp hmachine
  have hnormalize : Primrec₂ (fun (input : CodedPairInput Action × ℕ)
      (q : ℕ) =>
      q % (machineOfCode (Action := Action) input.1.1).numStates) := by
    apply Primrec₂.mk
    exact Primrec.nat_mod.comp Primrec.snd
      (numStates_primrec.comp
        ((codedLeft_primrec (Action := Action)).comp
          (Primrec.fst.comp Primrec.fst)))
  exact list_memBool_primrec.comp
    (Primrec.list_map hfinals hnormalize)
    (Primrec.nat_mod.comp Primrec.snd hstates)

private def codedRightIsFinalIndex
    (input : CodedPairInput Action × ℕ) : Bool :=
  let machine := machineOfCode (Action := Action) input.1.2.1
  decide (input.2 % machine.numStates ∈
    machine.finalIndices.map fun q => q % machine.numStates)

private theorem codedRightIsFinalIndex_primrec :
    Primrec (codedRightIsFinalIndex (Action := Action)) := by
  unfold codedRightIsFinalIndex
  have hmachine : Primrec (fun input : CodedPairInput Action × ℕ =>
      machineOfCode (Action := Action) input.1.2.1) :=
    (codedRight_primrec (Action := Action)).comp Primrec.fst
  have hstates := numStates_primrec.comp hmachine
  have hfinals := finalIndices_primrec.comp hmachine
  have hnormalize : Primrec₂ (fun (input : CodedPairInput Action × ℕ)
      (q : ℕ) =>
      q % (machineOfCode (Action := Action) input.1.2.1).numStates) := by
    apply Primrec₂.mk
    exact Primrec.nat_mod.comp Primrec.snd
      (numStates_primrec.comp
        ((codedRight_primrec (Action := Action)).comp
          (Primrec.fst.comp Primrec.fst)))
  exact list_memBool_primrec.comp
    (Primrec.list_map hfinals hnormalize)
    (Primrec.nat_mod.comp Primrec.snd hstates)

private def codedIsFinalIndex
    (input : CodedPairInput Action × (Bool × ℕ)) : Bool :=
  bif input.2.1 then
    codedRightIsFinalIndex (Action := Action) (input.1, input.2.2)
  else codedLeftIsFinalIndex (Action := Action) (input.1, input.2.2)

private theorem codedIsFinalIndex_primrec :
    Primrec (codedIsFinalIndex (Action := Action)) := by
  unfold codedIsFinalIndex
  have hpayload : Primrec (fun input :
      CodedPairInput Action × (Bool × ℕ) => (input.1, input.2.2)) :=
    Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.cond (Primrec.fst.comp Primrec.snd)
    ((codedRightIsFinalIndex_primrec (Action := Action)).comp hpayload)
    ((codedLeftIsFinalIndex_primrec (Action := Action)).comp hpayload)

private def codedLeftStartRow
    (input : CodedPairInput Action × Action) : InputRow (Option Action) :=
  (Endmarked.leftStart, some input.2, Endmarked.bottom,
    codedLeftPending (Action := Action)
      (input.1, (machineOfCode (Action := Action) input.1.1).initialIndex,
        input.2),
    [codedLeftStack (Action := Action)
      (input.1, (machineOfCode (Action := Action) input.1.1).startIndex),
      Endmarked.bottom])

private theorem codedLeftStartRow_primrec :
    Primrec (codedLeftStartRow (Action := Action)) := by
  unfold codedLeftStartRow
  have hpending : Primrec (fun input : CodedPairInput Action × Action =>
      codedLeftPending (Action := Action)
        (input.1, (machineOfCode (Action := Action) input.1.1).initialIndex,
          input.2)) :=
    (codedLeftPending_primrec (Action := Action)).comp
    (Primrec.pair Primrec.fst
      (Primrec.pair
        (initialIndex_primrec.comp
          ((codedLeft_primrec (Action := Action)).comp Primrec.fst))
        Primrec.snd))
  have hstack : Primrec (fun input : CodedPairInput Action × Action =>
      codedLeftStack (Action := Action)
        (input.1, (machineOfCode (Action := Action) input.1.1).startIndex)) :=
    (codedLeftStack_primrec (Action := Action)).comp
    (Primrec.pair Primrec.fst
      (startIndex_primrec.comp
        ((codedLeft_primrec (Action := Action)).comp Primrec.fst)))
  exact Primrec.pair (Primrec.const Endmarked.leftStart)
    (Primrec.pair (Primrec.option_some.comp Primrec.snd)
      (Primrec.pair (Primrec.const Endmarked.bottom)
        (Primrec.pair hpending
          (Primrec.list_cons.comp hstack
            (Primrec.const [Endmarked.bottom])))))

private def codedRightStartRow
    (input : CodedPairInput Action × Action) : InputRow (Option Action) :=
  (Endmarked.rightStart, some input.2, Endmarked.bottom,
    codedRightPending (Action := Action)
      (input.1, (machineOfCode (Action := Action) input.1.2.1).initialIndex,
        input.2),
    [codedRightStack (Action := Action)
      (input.1, (machineOfCode (Action := Action) input.1.2.1).startIndex),
      Endmarked.bottom])

private theorem codedRightStartRow_primrec :
    Primrec (codedRightStartRow (Action := Action)) := by
  unfold codedRightStartRow
  have hpending : Primrec (fun input : CodedPairInput Action × Action =>
      codedRightPending (Action := Action)
        (input.1,
          (machineOfCode (Action := Action) input.1.2.1).initialIndex,
          input.2)) :=
    (codedRightPending_primrec (Action := Action)).comp
    (Primrec.pair Primrec.fst
      (Primrec.pair
        (initialIndex_primrec.comp
          ((codedRight_primrec (Action := Action)).comp Primrec.fst))
        Primrec.snd))
  have hstack : Primrec (fun input : CodedPairInput Action × Action =>
      codedRightStack (Action := Action)
        (input.1, (machineOfCode (Action := Action) input.1.2.1).startIndex)) :=
    (codedRightStack_primrec (Action := Action)).comp
    (Primrec.pair Primrec.fst
      (startIndex_primrec.comp
        ((codedRight_primrec (Action := Action)).comp Primrec.fst)))
  exact Primrec.pair (Primrec.const Endmarked.rightStart)
    (Primrec.pair (Primrec.option_some.comp Primrec.snd)
      (Primrec.pair (Primrec.const Endmarked.bottom)
        (Primrec.pair hpending
          (Primrec.list_cons.comp hstack
            (Primrec.const [Endmarked.bottom])))))

private def codedLeftInitialIsFinal (input : CodedPairInput Action) : Bool :=
  codedLeftIsFinalIndex (Action := Action)
    (input, (machineOfCode (Action := Action) input.1).initialIndex)

private theorem codedLeftInitialIsFinal_primrec :
    Primrec (codedLeftInitialIsFinal (Action := Action)) := by
  unfold codedLeftInitialIsFinal
  exact (codedLeftIsFinalIndex_primrec (Action := Action)).comp
    (Primrec.pair Primrec.id
      (initialIndex_primrec.comp (codedLeft_primrec (Action := Action))))

private def codedRightInitialIsFinal (input : CodedPairInput Action) : Bool :=
  codedRightIsFinalIndex (Action := Action)
    (input, (machineOfCode (Action := Action) input.2.1).initialIndex)

private theorem codedRightInitialIsFinal_primrec :
    Primrec (codedRightInitialIsFinal (Action := Action)) := by
  unfold codedRightInitialIsFinal
  exact (codedRightIsFinalIndex_primrec (Action := Action)).comp
    (Primrec.pair Primrec.id
      (initialIndex_primrec.comp (codedRight_primrec (Action := Action))))

private def codedLeftEndTarget (input : CodedPairInput Action) : ℕ :=
  bif codedLeftInitialIsFinal (Action := Action) input then
    codedAcceptState (Action := Action) input
  else codedRejectState (Action := Action) input

private theorem codedLeftEndTarget_primrec :
    Primrec (codedLeftEndTarget (Action := Action)) := by
  unfold codedLeftEndTarget
  exact Primrec.cond (codedLeftInitialIsFinal_primrec (Action := Action))
    (codedAcceptState_primrec (Action := Action))
    (codedRejectState_primrec (Action := Action))

private def codedRightEndTarget (input : CodedPairInput Action) : ℕ :=
  bif codedRightInitialIsFinal (Action := Action) input then
    codedAcceptState (Action := Action) input
  else codedRejectState (Action := Action) input

private theorem codedRightEndTarget_primrec :
    Primrec (codedRightEndTarget (Action := Action)) := by
  unfold codedRightEndTarget
  exact Primrec.cond (codedRightInitialIsFinal_primrec (Action := Action))
    (codedAcceptState_primrec (Action := Action))
    (codedRejectState_primrec (Action := Action))

private def codedLeftEndRow
    (input : CodedPairInput Action) : InputRow (Option Action) :=
  (Endmarked.leftStart, none, Endmarked.bottom,
    codedLeftEndTarget (Action := Action) input, [Endmarked.bottom])

private theorem codedLeftEndRow_primrec :
    Primrec (codedLeftEndRow (Action := Action)) := by
  unfold codedLeftEndRow
  exact Primrec.pair (Primrec.const Endmarked.leftStart)
    (Primrec.pair (Primrec.const none)
      (Primrec.pair (Primrec.const Endmarked.bottom)
        (Primrec.pair (codedLeftEndTarget_primrec (Action := Action))
          (Primrec.const [Endmarked.bottom]))))

private def codedRightEndRow
    (input : CodedPairInput Action) : InputRow (Option Action) :=
  (Endmarked.rightStart, none, Endmarked.bottom,
    codedRightEndTarget (Action := Action) input, [Endmarked.bottom])

private theorem codedRightEndRow_primrec :
    Primrec (codedRightEndRow (Action := Action)) := by
  unfold codedRightEndRow
  exact Primrec.pair (Primrec.const Endmarked.rightStart)
    (Primrec.pair (Primrec.const none)
      (Primrec.pair (Primrec.const Endmarked.bottom)
        (Primrec.pair (codedRightEndTarget_primrec (Action := Action))
          (Primrec.const [Endmarked.bottom]))))

private def codedStartRows
    (input : CodedPairInput Action) : List (InputRow (Option Action)) :=
  ((input.2.2.map fun action =>
      codedLeftStartRow (Action := Action) (input, action))
    ++ [codedLeftEndRow (Action := Action) input])
    ++ ((input.2.2.map fun action =>
      codedRightStartRow (Action := Action) (input, action))
    ++ [codedRightEndRow (Action := Action) input])

private theorem codedStartRows_primrec :
    Primrec (codedStartRows (Action := Action)) := by
  unfold codedStartRows
  have hleft : Primrec (fun input : CodedPairInput Action =>
      input.2.2.map fun action =>
        codedLeftStartRow (Action := Action) (input, action)) := by
    have hstep : Primrec₂ (fun (input : CodedPairInput Action)
        (action : Action) =>
        codedLeftStartRow (Action := Action) (input, action)) := by
      apply Primrec₂.mk
      exact codedLeftStartRow_primrec (Action := Action)
    exact Primrec.list_map (codedAlphabet_primrec (Action := Action)) hstep
  have hright : Primrec (fun input : CodedPairInput Action =>
      input.2.2.map fun action =>
        codedRightStartRow (Action := Action) (input, action)) := by
    have hstep : Primrec₂ (fun (input : CodedPairInput Action)
        (action : Action) =>
        codedRightStartRow (Action := Action) (input, action)) := by
      apply Primrec₂.mk
      exact codedRightStartRow_primrec (Action := Action)
    exact Primrec.list_map (codedAlphabet_primrec (Action := Action)) hstep
  exact Primrec.list_append.comp
    (Primrec.list_append.comp hleft
      (Primrec.list_cons.comp (codedLeftEndRow_primrec (Action := Action))
        (Primrec.const [])))
    (Primrec.list_append.comp hright
      (Primrec.list_cons.comp (codedRightEndRow_primrec (Action := Action))
        (Primrec.const [])))

private abbrev CodedSideInput (Action : Type) :=
  CodedPairInput Action × Bool

private def codedSidePending
    (input : CodedSideInput Action × (ℕ × Action)) : ℕ :=
  bif input.1.2 then
    codedRightPending (Action := Action) (input.1.1, input.2)
  else codedLeftPending (Action := Action) (input.1.1, input.2)

private theorem codedSidePending_primrec :
    Primrec (codedSidePending (Action := Action)) := by
  unfold codedSidePending
  have hpair : Primrec (fun input : CodedSideInput Action × (ℕ × Action) =>
      input.1.1) := Primrec.fst.comp Primrec.fst
  have hpendingInput : Primrec (fun input :
      CodedSideInput Action × (ℕ × Action) => (input.1.1, input.2)) :=
    Primrec.pair hpair Primrec.snd
  exact Primrec.cond (Primrec.snd.comp Primrec.fst)
    ((codedRightPending_primrec (Action := Action)).comp hpendingInput)
    ((codedLeftPending_primrec (Action := Action)).comp hpendingInput)

private def codedSideStack (input : CodedSideInput Action × ℕ) : ℕ :=
  bif input.1.2 then codedRightStack (Action := Action) (input.1.1, input.2)
  else codedLeftStack (Action := Action) (input.1.1, input.2)

private theorem codedSideStack_primrec :
    Primrec (codedSideStack (Action := Action)) := by
  unfold codedSideStack
  have hstackInput : Primrec (fun input : CodedSideInput Action × ℕ =>
      (input.1.1, input.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.cond (Primrec.snd.comp Primrec.fst)
    ((codedRightStack_primrec (Action := Action)).comp hstackInput)
    ((codedLeftStack_primrec (Action := Action)).comp hstackInput)

private def codedSideIsFinal (input : CodedSideInput Action × ℕ) : Bool :=
  codedIsFinalIndex (Action := Action) (input.1.1, input.1.2, input.2)

private theorem codedSideIsFinal_primrec :
    Primrec (codedSideIsFinal (Action := Action)) := by
  unfold codedSideIsFinal
  exact (codedIsFinalIndex_primrec (Action := Action)).comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))

private def codedFinishState (input : CodedSideInput Action × ℕ) : ℕ :=
  bif codedSideIsFinal (Action := Action) input then
    codedAcceptState (Action := Action) input.1.1
  else codedRejectState (Action := Action) input.1.1

private theorem codedFinishState_primrec :
    Primrec (codedFinishState (Action := Action)) := by
  unfold codedFinishState
  exact Primrec.cond (codedSideIsFinal_primrec (Action := Action))
    ((codedAcceptState_primrec (Action := Action)).comp
      (Primrec.fst.comp Primrec.fst))
    ((codedRejectState_primrec (Action := Action)).comp
      (Primrec.fst.comp Primrec.fst))

noncomputable section

private noncomputable def epsilonStepEvaluator :
    (EncodedDPDA Action × (ℕ × ℕ)) → Option (ℕ × List ℕ) :=
  Classical.choose
    (DPDAToFirstOrder.epsilonStepEvaluator_exists (Action := Action))

private theorem epsilonStepEvaluator_primrec :
    Primrec (epsilonStepEvaluator (Action := Action)) :=
  (Classical.choose_spec
    (DPDAToFirstOrder.epsilonStepEvaluator_exists (Action := Action))).1

private theorem epsilonStepEvaluator_eq
    (input : EncodedDPDA Action × (ℕ × ℕ)) :
    epsilonStepEvaluator (Action := Action) input =
      DPDAToFirstOrder.Machine.epsilonStep?
        input.1 input.2.1 input.2.2 :=
  (Classical.choose_spec
    (DPDAToFirstOrder.epsilonStepEvaluator_exists (Action := Action))).2 input

private abbrev CodedEpsilonQuery := ℕ × (ℕ × ℕ)

private def selectedEpsilonOfCode
    (input : CodedEpsilonQuery) : Option (ℕ × List ℕ) :=
  epsilonStepEvaluator (Action := Action)
    (machineOfCode (Action := Action) input.1, input.2)

private theorem selectedEpsilonOfCode_primrec :
    Primrec (selectedEpsilonOfCode (Action := Action)) := by
  unfold selectedEpsilonOfCode
  exact epsilonStepEvaluator_primrec.comp
    (Primrec.pair
      ((machineOfCode_primrec (Action := Action)).comp Primrec.fst)
      Primrec.snd)

private abbrev CodedSideHeadInput (Action : Type) :=
  CodedSideInput Action × (Action × ℕ × ℕ)

private def codedLeftSelectedEpsilon?
    (input : CodedSideHeadInput Action) : Option (ℕ × List ℕ) :=
  selectedEpsilonOfCode (Action := Action)
    (input.1.1.1, input.2.2.1, input.2.2.2)

private theorem codedLeftSelectedEpsilon?_primrec :
    Primrec (codedLeftSelectedEpsilon? (Action := Action)) := by
  apply ((selectedEpsilonOfCode_primrec (Action := Action)).comp
    (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp
          (Primrec.snd.comp Primrec.snd))))).of_eq
  intro input
  rfl

private def codedRightSelectedEpsilon?
    (input : CodedSideHeadInput Action) : Option (ℕ × List ℕ) :=
  selectedEpsilonOfCode (Action := Action)
    (input.1.1.2.1, input.2.2.1, input.2.2.2)

private theorem codedRightSelectedEpsilon?_primrec :
    Primrec (codedRightSelectedEpsilon? (Action := Action)) := by
  apply ((selectedEpsilonOfCode_primrec (Action := Action)).comp
    (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp
          (Primrec.snd.comp Primrec.snd))))).of_eq
  intro input
  rfl

private def codedSelectedEpsilon?
    (input : CodedSideHeadInput Action) : Option (ℕ × List ℕ) :=
  bif input.1.2 then codedRightSelectedEpsilon? (Action := Action) input
  else codedLeftSelectedEpsilon? (Action := Action) input

private theorem codedSelectedEpsilon?_primrec :
    Primrec (codedSelectedEpsilon? (Action := Action)) := by
  unfold codedSelectedEpsilon?
  exact Primrec.cond (Primrec.snd.comp Primrec.fst)
    (codedRightSelectedEpsilon?_primrec (Action := Action))
    (codedLeftSelectedEpsilon?_primrec (Action := Action))

private def codedEmbeddedEpsilonRow?
    (input : CodedSideHeadInput Action) : Option EpsilonRow :=
  (codedSelectedEpsilon? (Action := Action) input).map fun output =>
    (codedSidePending (Action := Action)
        (input.1, input.2.2.1, input.2.1),
      codedSideStack (Action := Action) (input.1, input.2.2.2),
      codedSidePending (Action := Action)
        (input.1, output.1, input.2.1),
      output.2.map fun Z =>
        codedSideStack (Action := Action) (input.1, Z))

private theorem codedEmbeddedEpsilonRow?_primrec :
    Primrec (codedEmbeddedEpsilonRow? (Action := Action)) := by
  have hselected : Primrec (codedSelectedEpsilon? (Action := Action)) :=
    codedSelectedEpsilon?_primrec (Action := Action)
  have hrow : Primrec₂ (fun (input : CodedSideHeadInput Action)
      (output : ℕ × List ℕ) =>
        (codedSidePending (Action := Action)
            (input.1, input.2.2.1, input.2.1),
          codedSideStack (Action := Action) (input.1, input.2.2.2),
          codedSidePending (Action := Action)
            (input.1, output.1, input.2.1),
          output.2.map fun Z =>
            codedSideStack (Action := Action) (input.1, Z))) := by
    apply Primrec₂.mk
    have hside : Primrec (fun input :
        CodedSideHeadInput Action × (ℕ × List ℕ) => input.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hpending : Primrec (fun input :
        CodedSideHeadInput Action × (ℕ × List ℕ) => input.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hq : Primrec (fun input :
        CodedSideHeadInput Action × (ℕ × List ℕ) => input.1.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst))
    have hZ : Primrec (fun input :
        CodedSideHeadInput Action × (ℕ × List ℕ) => input.1.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst))
    have hsourcePending : Primrec (fun input :
        CodedSideHeadInput Action × (ℕ × List ℕ) =>
        codedSidePending (Action := Action)
          (input.1.1, input.1.2.2.1, input.1.2.1)) :=
      (codedSidePending_primrec (Action := Action)).comp
      (Primrec.pair hside (Primrec.pair hq hpending))
    have hsourceTop : Primrec (fun input :
        CodedSideHeadInput Action × (ℕ × List ℕ) =>
        codedSideStack (Action := Action)
          (input.1.1, input.1.2.2.2)) :=
      (codedSideStack_primrec (Action := Action)).comp
      (Primrec.pair hside hZ)
    have htargetPending : Primrec (fun input :
        CodedSideHeadInput Action × (ℕ × List ℕ) =>
        codedSidePending (Action := Action)
          (input.1.1, input.2.1, input.1.2.1)) :=
      (codedSidePending_primrec (Action := Action)).comp
      (Primrec.pair hside
        (Primrec.pair (Primrec.fst.comp Primrec.snd) hpending))
    have hreplacement : Primrec (fun input :
        CodedSideHeadInput Action × (ℕ × List ℕ) =>
        input.2.2.map fun Z =>
          codedSideStack (Action := Action) (input.1.1, Z)) := by
      have hmap : Primrec₂ (fun (input :
          CodedSideHeadInput Action × (ℕ × List ℕ)) (Z : ℕ) =>
          codedSideStack (Action := Action) (input.1.1, Z)) := by
        apply Primrec₂.mk
        exact (codedSideStack_primrec (Action := Action)).comp
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            Primrec.snd)
      exact Primrec.list_map (Primrec.snd.comp Primrec.snd) hmap
    exact Primrec.pair hsourcePending
      (Primrec.pair hsourceTop
        (Primrec.pair htargetPending hreplacement))
  exact Primrec.option_map hselected hrow

private def codedSideNumStates (input : CodedSideInput Action) : ℕ :=
  bif input.2 then (machineOfCode (Action := Action) input.1.2.1).numStates
  else (machineOfCode (Action := Action) input.1.1).numStates

private theorem codedSideNumStates_primrec :
    Primrec (codedSideNumStates (Action := Action)) := by
  unfold codedSideNumStates
  exact Primrec.cond Primrec.snd
    (numStates_primrec.comp
      ((codedRight_primrec (Action := Action)).comp Primrec.fst))
    (numStates_primrec.comp
      ((codedLeft_primrec (Action := Action)).comp Primrec.fst))

private def codedSideNumStackSymbols (input : CodedSideInput Action) : ℕ :=
  bif input.2 then
    (machineOfCode (Action := Action) input.1.2.1).numStackSymbols
  else (machineOfCode (Action := Action) input.1.1).numStackSymbols

private theorem codedSideNumStackSymbols_primrec :
    Primrec (codedSideNumStackSymbols (Action := Action)) := by
  unfold codedSideNumStackSymbols
  exact Primrec.cond Primrec.snd
    (numStackSymbols_primrec.comp
      ((codedRight_primrec (Action := Action)).comp Primrec.fst))
    (numStackSymbols_primrec.comp
      ((codedLeft_primrec (Action := Action)).comp Primrec.fst))

private def codedEpsilonRowsAtState
    (input : (CodedSideInput Action × Action) × ℕ) : List EpsilonRow :=
  (List.range
    (codedSideNumStackSymbols (Action := Action) input.1.1)).filterMap fun Z =>
    codedEmbeddedEpsilonRow? (Action := Action)
      (input.1.1, input.1.2, input.2, Z)

private theorem codedEpsilonRowsAtState_primrec :
    Primrec (codedEpsilonRowsAtState (Action := Action)) := by
  unfold codedEpsilonRowsAtState
  have hstack : Primrec (fun input :
      (CodedSideInput Action × Action) × ℕ =>
      codedSideNumStackSymbols (Action := Action) input.1.1) :=
    (codedSideNumStackSymbols_primrec (Action := Action)).comp
      (Primrec.fst.comp Primrec.fst)
  have hrow : Primrec₂ (fun (input :
      (CodedSideInput Action × Action) × ℕ) (Z : ℕ) =>
      codedEmbeddedEpsilonRow? (Action := Action)
        (input.1.1, input.1.2, input.2, Z)) := by
    apply Primrec₂.mk
    exact (codedEmbeddedEpsilonRow?_primrec (Action := Action)).comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp Primrec.fst)
            Primrec.snd)))
  exact Primrec.listFilterMap (Primrec.list_range.comp hstack) hrow

private def codedEpsilonRowsAtPending
    (input : CodedSideInput Action × Action) : List EpsilonRow :=
  (List.range (codedSideNumStates (Action := Action) input.1)).flatMap fun q =>
    codedEpsilonRowsAtState (Action := Action) (input, q)

private theorem codedEpsilonRowsAtPending_primrec :
    Primrec (codedEpsilonRowsAtPending (Action := Action)) := by
  unfold codedEpsilonRowsAtPending
  have hstates : Primrec (fun input : CodedSideInput Action × Action =>
      codedSideNumStates (Action := Action) input.1) :=
    (codedSideNumStates_primrec (Action := Action)).comp Primrec.fst
  have hstep : Primrec₂ (fun (input : CodedSideInput Action × Action)
      (q : ℕ) => codedEpsilonRowsAtState (Action := Action) (input, q)) := by
    apply Primrec₂.mk
    exact codedEpsilonRowsAtState_primrec (Action := Action)
  exact Primrec.list_flatMap (Primrec.list_range.comp hstates) hstep

private def codedEmbeddedEpsilonRows
    (input : CodedSideInput Action) : List EpsilonRow :=
  input.1.2.2.flatMap fun pending =>
    codedEpsilonRowsAtPending (Action := Action) (input, pending)

private theorem codedEmbeddedEpsilonRows_primrec :
    Primrec (codedEmbeddedEpsilonRows (Action := Action)) := by
  unfold codedEmbeddedEpsilonRows
  have hstep : Primrec₂ (fun (input : CodedSideInput Action)
      (pending : Action) =>
      codedEpsilonRowsAtPending (Action := Action) (input, pending)) := by
    apply Primrec₂.mk
    exact codedEpsilonRowsAtPending_primrec (Action := Action)
  exact Primrec.list_flatMap
    ((codedAlphabet_primrec (Action := Action)).comp Primrec.fst) hstep

private def codedLeftEpsilonRows
    (input : CodedPairInput Action) : List EpsilonRow :=
  codedEmbeddedEpsilonRows (Action := Action) (input, false)

private theorem codedLeftEpsilonRows_primrec :
    Primrec (codedLeftEpsilonRows (Action := Action)) := by
  unfold codedLeftEpsilonRows
  exact (codedEmbeddedEpsilonRows_primrec (Action := Action)).comp
    (Primrec.pair Primrec.id (Primrec.const false))

private def codedRightEpsilonRows
    (input : CodedPairInput Action) : List EpsilonRow :=
  codedEmbeddedEpsilonRows (Action := Action) (input, true)

private theorem codedRightEpsilonRows_primrec :
    Primrec (codedRightEpsilonRows (Action := Action)) := by
  unfold codedRightEpsilonRows
  exact (codedEmbeddedEpsilonRows_primrec (Action := Action)).comp
    (Primrec.pair Primrec.id (Primrec.const true))

private noncomputable def deterministicInputStepEvaluator :
    (EncodedDPDA Action × (ℕ × Action × ℕ)) → Option (ℕ × List ℕ) :=
  Classical.choose
    (DPDAToFirstOrder.deterministicInputStepEvaluator_exists (Action := Action))

private theorem deterministicInputStepEvaluator_primrec :
    Primrec (deterministicInputStepEvaluator (Action := Action)) :=
  (Classical.choose_spec
    (DPDAToFirstOrder.deterministicInputStepEvaluator_exists
      (Action := Action))).1

private theorem deterministicInputStepEvaluator_eq
    (input : EncodedDPDA Action × (ℕ × Action × ℕ)) :
    deterministicInputStepEvaluator (Action := Action) input =
      if (DPDAToFirstOrder.Machine.epsilonStep?
          input.1 input.2.1 input.2.2.2).isSome then none
      else DPDAToFirstOrder.Machine.inputStep?
        input.1 input.2.1 input.2.2.1 input.2.2.2 :=
  (Classical.choose_spec
    (DPDAToFirstOrder.deterministicInputStepEvaluator_exists
      (Action := Action))).2 input

private abbrev CodedInputQuery (Action : Type) :=
  ℕ × (ℕ × Action × ℕ)

private def selectedInputOfCode
    (input : CodedInputQuery Action) : Option (ℕ × List ℕ) :=
  deterministicInputStepEvaluator (Action := Action)
    (machineOfCode (Action := Action) input.1, input.2)

private theorem selectedInputOfCode_primrec :
    Primrec (selectedInputOfCode (Action := Action)) := by
  unfold selectedInputOfCode
  exact deterministicInputStepEvaluator_primrec.comp
    (Primrec.pair
      ((machineOfCode_primrec (Action := Action)).comp Primrec.fst)
      Primrec.snd)

private def codedLeftSelectedInput?
    (input : CodedSideHeadInput Action) : Option (ℕ × List ℕ) :=
  selectedInputOfCode (Action := Action)
    (input.1.1.1, input.2.2.1, input.2.1, input.2.2.2)

private theorem codedLeftSelectedInput?_primrec :
    Primrec (codedLeftSelectedInput? (Action := Action)) := by
  unfold codedLeftSelectedInput?
  exact (selectedInputOfCode_primrec (Action := Action)).comp
    (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

private def codedRightSelectedInput?
    (input : CodedSideHeadInput Action) : Option (ℕ × List ℕ) :=
  selectedInputOfCode (Action := Action)
    (input.1.1.2.1, input.2.2.1, input.2.1, input.2.2.2)

private theorem codedRightSelectedInput?_primrec :
    Primrec (codedRightSelectedInput? (Action := Action)) := by
  unfold codedRightSelectedInput?
  exact (selectedInputOfCode_primrec (Action := Action)).comp
    (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

private def codedSelectedInput?
    (input : CodedSideHeadInput Action) : Option (ℕ × List ℕ) :=
  bif input.1.2 then codedRightSelectedInput? (Action := Action) input
  else codedLeftSelectedInput? (Action := Action) input

private theorem codedSelectedInput?_primrec :
    Primrec (codedSelectedInput? (Action := Action)) := by
  unfold codedSelectedInput?
  exact Primrec.cond (Primrec.snd.comp Primrec.fst)
    (codedRightSelectedInput?_primrec (Action := Action))
    (codedLeftSelectedInput?_primrec (Action := Action))

private abbrev CodedInputTargetInput (Action : Type) :=
  CodedSideInput Action × (ℕ × Option Action)

private def codedInputTargetNone
    (input : CodedInputTargetInput Action) : ℕ :=
  codedFinishState (Action := Action) (input.1, input.2.1)

private theorem codedInputTargetNone_primrec :
    Primrec (codedInputTargetNone (Action := Action)) := by
  unfold codedInputTargetNone
  exact (codedFinishState_primrec (Action := Action)).comp
    (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))

private def codedInputTargetSome
    (input : CodedInputTargetInput Action × Action) : ℕ :=
  codedSidePending (Action := Action)
    (input.1.1, input.1.2.1, input.2)

private theorem codedInputTargetSome_primrec :
    Primrec (codedInputTargetSome (Action := Action)) := by
  unfold codedInputTargetSome
  exact (codedSidePending_primrec (Action := Action)).comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))

private def codedInputTarget
    (input : CodedInputTargetInput Action) : ℕ :=
  match input.2.2 with
  | some action => codedInputTargetSome (Action := Action) (input, action)
  | none => codedInputTargetNone (Action := Action) input

private theorem codedInputTarget_primrec :
    Primrec (codedInputTarget (Action := Action)) := by
  have hnone : Primrec (fun input : CodedInputTargetInput Action =>
      codedInputTargetNone (Action := Action) input) :=
    codedInputTargetNone_primrec (Action := Action)
  have hsome : Primrec₂ (fun (input : CodedInputTargetInput Action)
      (action : Action) =>
      codedInputTargetSome (Action := Action) (input, action)) := by
    apply Primrec₂.mk
    exact codedInputTargetSome_primrec (Action := Action)
  apply (Primrec.option_casesOn
    (Primrec.snd.comp Primrec.snd) hnone hsome).of_eq
  rintro ⟨side, target, next⟩
  cases next <;> rfl

private def codedSideReplacement
    (input : CodedSideInput Action × List ℕ) : List ℕ :=
  input.2.map fun Y => codedSideStack (Action := Action) (input.1, Y)

private theorem codedSideReplacement_primrec :
    Primrec (codedSideReplacement (Action := Action)) := by
  unfold codedSideReplacement
  have hstep : Primrec₂ (fun (input : CodedSideInput Action × List ℕ)
      (Y : ℕ) => codedSideStack (Action := Action) (input.1, Y)) := by
    apply Primrec₂.mk
    exact (codedSideStack_primrec (Action := Action)).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_map Primrec.snd hstep

private abbrev CodedInputOutput (Action : Type) :=
  CodedSideHeadInput Action × (ℕ × List ℕ)

private def codedInputSourcePending
    (input : CodedInputOutput Action) : ℕ :=
  codedSidePending (Action := Action)
    (input.1.1, input.1.2.2.1, input.1.2.1)

private theorem codedInputSourcePending_primrec :
    Primrec (codedInputSourcePending (Action := Action)) := by
  unfold codedInputSourcePending
  exact (codedSidePending_primrec (Action := Action)).comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))

private def codedInputSourceTop
    (input : CodedInputOutput Action) : ℕ :=
  codedSideStack (Action := Action) (input.1.1, input.1.2.2.2)

private theorem codedInputSourceTop_primrec :
    Primrec (codedInputSourceTop (Action := Action)) := by
  unfold codedInputSourceTop
  exact (codedSideStack_primrec (Action := Action)).comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))

private def codedInputOutputReplacement
    (input : CodedInputOutput Action) : List ℕ :=
  codedSideReplacement (Action := Action) (input.1.1, input.2.2)

private theorem codedInputOutputReplacement_primrec :
    Primrec (codedInputOutputReplacement (Action := Action)) := by
  unfold codedInputOutputReplacement
  exact (codedSideReplacement_primrec (Action := Action)).comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

private def codedInputNextTarget
    (input : CodedInputOutput Action × Option Action) : ℕ :=
  codedInputTarget (Action := Action)
    (input.1.1.1, input.1.2.1, input.2)

private theorem codedInputNextTarget_primrec :
    Primrec (codedInputNextTarget (Action := Action)) := by
  unfold codedInputNextTarget
  exact (codedInputTarget_primrec (Action := Action)).comp
    (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))

private def codedInputRowForNext
    (input : CodedInputOutput Action × Option Action) :
    InputRow (Option Action) :=
  (codedInputSourcePending (Action := Action) input.1,
    input.2,
    codedInputSourceTop (Action := Action) input.1,
    codedInputNextTarget (Action := Action) input,
    codedInputOutputReplacement (Action := Action) input.1)

private theorem codedInputRowForNext_primrec :
    Primrec (codedInputRowForNext (Action := Action)) := by
  unfold codedInputRowForNext
  exact Primrec.pair
    ((codedInputSourcePending_primrec (Action := Action)).comp Primrec.fst)
    (Primrec.pair Primrec.snd
      (Primrec.pair
        ((codedInputSourceTop_primrec (Action := Action)).comp Primrec.fst)
        (Primrec.pair
          (codedInputNextTarget_primrec (Action := Action))
          ((codedInputOutputReplacement_primrec (Action := Action)).comp
            Primrec.fst))))

private def codedInputRowsForOutput
    (input : CodedInputOutput Action) : List (InputRow (Option Action)) :=
  (endmarkedAlphabet input.1.1.1.2.2).map fun next =>
    codedInputRowForNext (Action := Action) (input, next)

private theorem codedInputRowsForOutput_primrec :
    Primrec (codedInputRowsForOutput (Action := Action)) := by
  unfold codedInputRowsForOutput
  have halphabet : Primrec (fun input : CodedInputOutput Action =>
      endmarkedAlphabet input.1.1.1.2.2) :=
    endmarkedAlphabet_primrec.comp
      ((codedAlphabet_primrec (Action := Action)).comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hstep : Primrec₂ (fun (input : CodedInputOutput Action)
      (next : Option Action) =>
      codedInputRowForNext (Action := Action) (input, next)) := by
    apply Primrec₂.mk
    exact codedInputRowForNext_primrec (Action := Action)
  exact Primrec.list_map halphabet hstep

private def codedEmbeddedInputRowsAtHead
    (input : CodedSideHeadInput Action) : List (InputRow (Option Action)) :=
  match codedSelectedInput? (Action := Action) input with
  | none => []
  | some output => codedInputRowsForOutput (Action := Action) (input, output)

private theorem codedEmbeddedInputRowsAtHead_primrec :
    Primrec (codedEmbeddedInputRowsAtHead (Action := Action)) := by
  have hsome : Primrec₂ (fun (input : CodedSideHeadInput Action)
      (output : ℕ × List ℕ) =>
      codedInputRowsForOutput (Action := Action) (input, output)) := by
    apply Primrec₂.mk
    exact codedInputRowsForOutput_primrec (Action := Action)
  apply (Primrec.option_casesOn
    (codedSelectedInput?_primrec (Action := Action))
    (Primrec.const []) hsome).of_eq
  intro input
  cases h : codedSelectedInput? (Action := Action) input <;>
    simp [codedEmbeddedInputRowsAtHead, h]

private def codedInputRowsAtState
    (input : (CodedSideInput Action × Action) × ℕ) :
    List (InputRow (Option Action)) :=
  (List.range
    (codedSideNumStackSymbols (Action := Action) input.1.1)).flatMap fun Z =>
    codedEmbeddedInputRowsAtHead (Action := Action)
      (input.1.1, input.1.2, input.2, Z)

private theorem codedInputRowsAtState_primrec :
    Primrec (codedInputRowsAtState (Action := Action)) := by
  unfold codedInputRowsAtState
  have hstack : Primrec (fun input :
      (CodedSideInput Action × Action) × ℕ =>
      codedSideNumStackSymbols (Action := Action) input.1.1) :=
    (codedSideNumStackSymbols_primrec (Action := Action)).comp
      (Primrec.fst.comp Primrec.fst)
  have hrows : Primrec₂ (fun (input :
      (CodedSideInput Action × Action) × ℕ) (Z : ℕ) =>
      codedEmbeddedInputRowsAtHead (Action := Action)
        (input.1.1, input.1.2, input.2, Z)) := by
    apply Primrec₂.mk
    exact (codedEmbeddedInputRowsAtHead_primrec (Action := Action)).comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))
  exact Primrec.list_flatMap (Primrec.list_range.comp hstack) hrows

private def codedInputRowsAtPending
    (input : CodedSideInput Action × Action) :
    List (InputRow (Option Action)) :=
  (List.range (codedSideNumStates (Action := Action) input.1)).flatMap fun q =>
    codedInputRowsAtState (Action := Action) (input, q)

private theorem codedInputRowsAtPending_primrec :
    Primrec (codedInputRowsAtPending (Action := Action)) := by
  unfold codedInputRowsAtPending
  have hstates : Primrec (fun input : CodedSideInput Action × Action =>
      codedSideNumStates (Action := Action) input.1) :=
    (codedSideNumStates_primrec (Action := Action)).comp Primrec.fst
  have hstep : Primrec₂ (fun (input : CodedSideInput Action × Action)
      (q : ℕ) => codedInputRowsAtState (Action := Action) (input, q)) := by
    apply Primrec₂.mk
    exact codedInputRowsAtState_primrec (Action := Action)
  exact Primrec.list_flatMap (Primrec.list_range.comp hstates) hstep

private def codedEmbeddedInputRows
    (input : CodedSideInput Action) : List (InputRow (Option Action)) :=
  input.1.2.2.flatMap fun pending =>
    codedInputRowsAtPending (Action := Action) (input, pending)

private theorem codedEmbeddedInputRows_primrec_new :
    Primrec (codedEmbeddedInputRows (Action := Action)) := by
  unfold codedEmbeddedInputRows
  have hstep : Primrec₂ (fun (input : CodedSideInput Action)
      (pending : Action) =>
      codedInputRowsAtPending (Action := Action) (input, pending)) := by
    apply Primrec₂.mk
    exact codedInputRowsAtPending_primrec (Action := Action)
  exact Primrec.list_flatMap
    ((codedAlphabet_primrec (Action := Action)).comp Primrec.fst) hstep


private def codedLeftInputRows
    (input : CodedPairInput Action) : List (InputRow (Option Action)) :=
  codedEmbeddedInputRows (Action := Action) (input, false)

private theorem codedLeftInputRows_primrec :
    Primrec (codedLeftInputRows (Action := Action)) := by
  unfold codedLeftInputRows
  exact (codedEmbeddedInputRows_primrec_new (Action := Action)).comp
    (Primrec.pair Primrec.id (Primrec.const false))

private def codedRightInputRows
    (input : CodedPairInput Action) : List (InputRow (Option Action)) :=
  codedEmbeddedInputRows (Action := Action) (input, true)

private theorem codedRightInputRows_primrec :
    Primrec (codedRightInputRows (Action := Action)) := by
  unfold codedRightInputRows
  exact (codedEmbeddedInputRows_primrec_new (Action := Action)).comp
    (Primrec.pair Primrec.id (Primrec.const true))

private def codedDrainRows (input : CodedPairInput Action) : List EpsilonRow :=
  (List.range (Endmarked.stackCount
    (machineOfCode (Action := Action) input.1)
    (machineOfCode (Action := Action) input.2.1))).map fun Z =>
      (codedAcceptState (Action := Action) input, Z,
        codedAcceptState (Action := Action) input, [])

private theorem codedDrainRows_primrec :
    Primrec (codedDrainRows (Action := Action)) := by
  unfold codedDrainRows
  have hrow : Primrec₂ (fun (input : CodedPairInput Action) (Z : ℕ) =>
      ((codedAcceptState (Action := Action) input, Z,
        codedAcceptState (Action := Action) input, []) : EpsilonRow)) := by
    apply Primrec₂.mk
    exact Primrec.pair ((codedAcceptState_primrec (Action := Action)).comp Primrec.fst)
      (Primrec.pair Primrec.snd
        (Primrec.pair ((codedAcceptState_primrec (Action := Action)).comp Primrec.fst)
          (Primrec.const [])))
  exact Primrec.list_map
    (Primrec.list_range.comp (codedStackCount_primrec (Action := Action))) hrow

private def codedEndmarkedPairMachine
    (input : CodedPairInput Action) : EncodedDPDA (Option Action) :=
  (codedStateCount (Action := Action) input - 1,
    Endmarked.stackCount (machineOfCode (Action := Action) input.1)
      (machineOfCode (Action := Action) input.2.1) - 1,
    Endmarked.leftStart,
    Endmarked.bottom,
    [],
    (codedStartRows (Action := Action) input ++
      codedLeftInputRows (Action := Action) input) ++
      codedRightInputRows (Action := Action) input,
    (codedLeftEpsilonRows (Action := Action) input ++
      codedRightEpsilonRows (Action := Action) input) ++
      codedDrainRows (Action := Action) input)

private theorem codedEndmarkedPairMachine_primrec :
    Primrec (codedEndmarkedPairMachine (Action := Action)) := by
  unfold codedEndmarkedPairMachine
  have hstateField : Primrec (fun input : CodedPairInput Action =>
      codedStateCount (Action := Action) input - 1) :=
    Primrec.nat_sub.comp (codedStateCount_primrec (Action := Action)) (Primrec.const 1)
  have hstackField : Primrec (fun input : CodedPairInput Action =>
      Endmarked.stackCount (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) - 1) :=
    Primrec.nat_sub.comp (codedStackCount_primrec (Action := Action)) (Primrec.const 1)
  have hinputRows : Primrec (fun input : CodedPairInput Action =>
      (codedStartRows (Action := Action) input ++
        codedLeftInputRows (Action := Action) input) ++
        codedRightInputRows (Action := Action) input) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp (codedStartRows_primrec (Action := Action))
        (codedLeftInputRows_primrec (Action := Action)))
      (codedRightInputRows_primrec (Action := Action))
  have hepsilonRows : Primrec (fun input : CodedPairInput Action =>
      (codedLeftEpsilonRows (Action := Action) input ++
        codedRightEpsilonRows (Action := Action) input) ++
        codedDrainRows (Action := Action) input) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp (codedLeftEpsilonRows_primrec (Action := Action))
        (codedRightEpsilonRows_primrec (Action := Action)))
      (codedDrainRows_primrec (Action := Action))
  exact Primrec.pair hstateField
    (Primrec.pair hstackField
      (Primrec.pair (Primrec.const Endmarked.leftStart)
        (Primrec.pair (Primrec.const Endmarked.bottom)
          (Primrec.pair (Primrec.const [])
            (Primrec.pair hinputRows hepsilonRows)))))

private theorem codedEndmarkedPairMachine_computable :
    Computable (codedEndmarkedPairMachine (Action := Action)) :=
  (codedEndmarkedPairMachine_primrec (Action := Action)).to_comp

/-! ## Popping/complete normalization -/

private theorem local_primrec_list_find?
    {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  have hguard : Primrec₂ (fun a b =>
      bif p a b then some b else none) := by
    show Primrec (fun q : A × B =>
      bif p q.1 q.2 then some q.2 else none)
    exact Primrec.cond (hp.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  have hhead := Primrec.list_head?.comp
    (Primrec.listFilterMap hf hguard)
  apply hhead.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons head tail ih =>
      cases h : p a head <;> simp [h, ih]

private abbrev EpsilonOnlyInput (Action : Type) :=
  EncodedDPDA Action × ℕ

private def codedTargetFinalCode
    (input : EpsilonOnlyInput Action × ℕ) : Bool :=
  decide (input.2 = input.1.2 % input.1.1.numStates)

private theorem codedTargetFinalCode_primrec :
    Primrec (codedTargetFinalCode (Action := Action)) := by
  have htarget : Primrec (fun input : EpsilonOnlyInput Action × ℕ =>
      input.1.2 % input.1.1.numStates) :=
    Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst)
      (numStates_primrec.comp (Primrec.fst.comp Primrec.fst))
  unfold codedTargetFinalCode
  exact Primrec.eq.decide.comp Primrec.snd htarget

private def codedTargetFinalCandidate
    (input : EpsilonOnlyInput Action × ℕ) : Option ℕ :=
  bif codedTargetFinalCode input then none else some input.2

private theorem codedTargetFinalCandidate_primrec :
    Primrec (codedTargetFinalCandidate (Action := Action)) := by
  unfold codedTargetFinalCandidate
  exact Primrec.cond codedTargetFinalCode_primrec (Primrec.const none)
    (Primrec.option_some.comp Primrec.snd)

private def codedTargetFinals (input : EpsilonOnlyInput Action) : List ℕ :=
  (List.range input.1.numStates).filterMap fun state =>
    codedTargetFinalCandidate (input, state)

private theorem codedTargetFinals_primrec :
    Primrec (codedTargetFinals (Action := Action)) := by
  unfold codedTargetFinals
  exact Primrec.listFilterMap
    (Primrec.list_range.comp (numStates_primrec.comp Primrec.fst))
    codedTargetFinalCandidate_primrec.to₂

private theorem codedTargetFinals_eq (input : EpsilonOnlyInput Action) :
    codedTargetFinals input =
      (List.range input.1.numStates).filter fun state =>
        decide (state ≠ input.2 % input.1.numStates) := by
  unfold codedTargetFinals
  induction List.range input.1.numStates with
  | nil => rfl
  | cons state rest ih =>
      by_cases hstate : state = input.2 % input.1.numStates
      · rw [List.filterMap_cons, List.filter_cons, ih]
        simp [codedTargetFinalCandidate, codedTargetFinalCode, hstate]
      · rw [List.filterMap_cons, List.filter_cons, ih]
        simp [codedTargetFinalCandidate, codedTargetFinalCode, hstate]

private def codedEpsilonOnlyTargetMachine
    (input : EpsilonOnlyInput Action) : EncodedDPDA Unit :=
  (input.1.numStates - 1,
    input.1.numStackSymbols - 1,
    0,
    0,
    codedTargetFinals input,
    [],
    input.1.epsilonRows)

private theorem codedEpsilonOnlyTargetMachine_primrec :
    Primrec (codedEpsilonOnlyTargetMachine (Action := Action)) := by
  have hstates : Primrec (fun input : EpsilonOnlyInput Action =>
      input.1.numStates) := numStates_primrec.comp Primrec.fst
  have hstack : Primrec (fun input : EpsilonOnlyInput Action =>
      input.1.numStackSymbols) :=
    numStackSymbols_primrec.comp Primrec.fst
  unfold codedEpsilonOnlyTargetMachine
  exact Primrec.pair
    (Primrec.nat_sub.comp hstates (Primrec.const 1))
    (Primrec.pair
      (Primrec.nat_sub.comp hstack (Primrec.const 1))
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair codedTargetFinals_primrec
            (Primrec.pair (Primrec.const [])
              (epsilonRows_primrec.comp Primrec.fst))))))

private theorem codedEpsilonOnlyTargetMachine_eq
    (input : EpsilonOnlyInput Action) :
    codedEpsilonOnlyTargetMachine input =
      Popping.epsilonOnlyTargetMachine input.1 input.2 := by
  unfold codedEpsilonOnlyTargetMachine Popping.epsilonOnlyTargetMachine
  rw [codedTargetFinals_eq]

private abbrev HeadReturnInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × ℕ × ℕ)

private def codedHeadReturnQuery
    (input : HeadReturnInput Action) : ℕ × ℕ × ℕ :=
  (input.2.1 % input.1.numStates,
    input.2.2.1 % input.1.numStackSymbols,
    input.2.2.2 % input.1.numStates)

private theorem codedHeadReturnQuery_primrec :
    Primrec (codedHeadReturnQuery (Action := Action)) := by
  have hstates : Primrec (fun input : HeadReturnInput Action =>
      input.1.numStates) := numStates_primrec.comp Primrec.fst
  have hstack : Primrec (fun input : HeadReturnInput Action =>
      input.1.numStackSymbols) :=
    numStackSymbols_primrec.comp Primrec.fst
  unfold codedHeadReturnQuery
  exact Primrec.pair
    (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) hstates)
    (Primrec.pair
      (Primrec.nat_mod.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hstack)
      (Primrec.nat_mod.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hstates))

private def codedHeadTargetMachine
    (input : HeadReturnInput Action) : EncodedDPDA Unit :=
  codedEpsilonOnlyTargetMachine (input.1, input.2.2.2)

private theorem codedHeadTargetMachine_primrec :
    Primrec (codedHeadTargetMachine (Action := Action)) := by
  unfold codedHeadTargetMachine
  exact codedEpsilonOnlyTargetMachine_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem leastSummaryEvaluator_exists :
    ∃ evaluator : EncodedDPDA Unit → List EncodedDPDA.SummaryTriple,
      Primrec evaluator ∧
        ∀ machine, evaluator machine = machine.leastSummaryRelation :=
  ⟨EncodedDPDA.leastSummaryRelation,
    EncodedDPDA.leastSummaryRelation_primrec, fun _ => rfl⟩

private noncomputable def leastSummaryEvaluator :
    EncodedDPDA Unit → List EncodedDPDA.SummaryTriple :=
  Classical.choose leastSummaryEvaluator_exists

private theorem leastSummaryEvaluator_primrec :
    Primrec leastSummaryEvaluator :=
  (Classical.choose_spec leastSummaryEvaluator_exists).1

private theorem leastSummaryEvaluator_eq (machine : EncodedDPDA Unit) :
    leastSummaryEvaluator machine = machine.leastSummaryRelation :=
  (Classical.choose_spec leastSummaryEvaluator_exists).2 machine

private def codedHeadReturnsCode (input : HeadReturnInput Action) : Bool :=
  (leastSummaryEvaluator (codedHeadTargetMachine input)).any fun candidate =>
    decide (candidate = codedHeadReturnQuery input)

private theorem codedHeadReturnsCode_primrec :
    Primrec (codedHeadReturnsCode (Action := Action)) := by
  unfold codedHeadReturnsCode
  have hrelation : Primrec (fun input : HeadReturnInput Action =>
      leastSummaryEvaluator (codedHeadTargetMachine input)) :=
    leastSummaryEvaluator_primrec.comp
      (codedHeadTargetMachine_primrec (Action := Action))
  have hpredicate : Primrec₂ (fun (input : HeadReturnInput Action)
      (candidate : EncodedDPDA.SummaryTriple) =>
      decide (candidate = codedHeadReturnQuery input)) := by
    apply Primrec₂.mk
    exact Primrec.eq.decide.comp Primrec.snd
      ((codedHeadReturnQuery_primrec (Action := Action)).comp Primrec.fst)
  exact primrec_list_any hrelation hpredicate

private theorem codedHeadReturnsCode_eq (input : HeadReturnInput Action) :
    codedHeadReturnsCode input =
      Popping.headReturnsCode input.1 input.2.1
        input.2.2.1 input.2.2.2 := by
  unfold codedHeadReturnsCode codedHeadReturnQuery codedHeadTargetMachine
  unfold Popping.headReturnsCode
  rw [leastSummaryEvaluator_eq]
  rw [codedEpsilonOnlyTargetMachine_eq]
  induction (Popping.epsilonOnlyTargetMachine input.1
      input.2.2.2).leastSummaryRelation with
  | nil => rfl
  | cons triple relation ih =>
      simp [ih, eq_comm]

private abbrev ReturnEntryInput (Action : Type) :=
  EncodedDPDA Action × ℕ

private def codedReturnPredicate
    (input : ReturnEntryInput Action × ℕ) : Bool :=
  codedHeadReturnsCode
    (input.1.1,
      input.1.2 / input.1.1.numStackSymbols,
      input.1.2 % input.1.1.numStackSymbols,
      input.2)

private theorem codedReturnPredicate_primrec :
    Primrec (codedReturnPredicate (Action := Action)) := by
  have hstack : Primrec (fun input : ReturnEntryInput Action × ℕ =>
      input.1.1.numStackSymbols) :=
    numStackSymbols_primrec.comp (Primrec.fst.comp Primrec.fst)
  unfold codedReturnPredicate
  exact codedHeadReturnsCode_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst) hstack)
        (Primrec.pair
          (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst) hstack)
          Primrec.snd)))

private def codedReturnEntry (input : ReturnEntryInput Action) : Option ℕ :=
  (List.range input.1.numStates).find? fun target =>
    codedReturnPredicate (input, target)

private theorem codedReturnEntry_primrec :
    Primrec (codedReturnEntry (Action := Action)) := by
  unfold codedReturnEntry
  exact local_primrec_list_find?
    (Primrec.list_range.comp (numStates_primrec.comp Primrec.fst))
    codedReturnPredicate_primrec.to₂

private def codedReturnTable (machine : EncodedDPDA Action) :
    Popping.ReturnTable :=
  (List.range (machine.numStates * machine.numStackSymbols)).map fun head =>
    codedReturnEntry (machine, head)

private theorem codedReturnTable_primrec :
    Primrec (codedReturnTable (Action := Action)) := by
  unfold codedReturnTable
  exact Primrec.list_map
    (Primrec.list_range.comp
      (Primrec.nat_mul.comp numStates_primrec numStackSymbols_primrec))
    codedReturnEntry_primrec.to₂

private theorem codedReturnTable_eq (machine : EncodedDPDA Action) :
    codedReturnTable machine = Popping.returnTable machine := by
  simp only [codedReturnTable, Popping.returnTable, codedReturnEntry,
    codedReturnPredicate, codedHeadReturnsCode_eq]

private abbrev HeadIndexInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × ℕ)

private def codedHeadIndex (input : HeadIndexInput Action) : ℕ :=
  (input.2.1 % input.1.numStates) * input.1.numStackSymbols +
    input.2.2 % input.1.numStackSymbols

private theorem codedHeadIndex_primrec :
    Primrec (codedHeadIndex (Action := Action)) := by
  have hstates : Primrec (fun input : HeadIndexInput Action =>
      input.1.numStates) := numStates_primrec.comp Primrec.fst
  have hstack : Primrec (fun input : HeadIndexInput Action =>
      input.1.numStackSymbols) :=
    numStackSymbols_primrec.comp Primrec.fst
  unfold codedHeadIndex
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) hstates)
      hstack)
    (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) hstack)

private abbrev ReturnAtInput (Action : Type) :=
  EncodedDPDA Action × (Popping.ReturnTable × ℕ × ℕ)

private def codedReturnAt (input : ReturnAtInput Action) : Option ℕ :=
  input.2.1[codedHeadIndex (input.1, input.2.2.1, input.2.2.2)]?.join

private theorem codedReturnAt_primrec :
    Primrec (codedReturnAt (Action := Action)) := by
  have hindex : Primrec (fun input : ReturnAtInput Action =>
      codedHeadIndex (input.1, input.2.2.1, input.2.2.2)) :=
    codedHeadIndex_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hlookup : Primrec (fun input : ReturnAtInput Action =>
      input.2.1[codedHeadIndex
        (input.1, input.2.2.1, input.2.2.2)]?) :=
    Primrec.list_getElem?.comp
      (Primrec.fst.comp Primrec.snd) hindex
  unfold codedReturnAt
  exact Primrec.option_bind hlookup Primrec.snd.to₂

private theorem codedReturnAt_eq (input : ReturnAtInput Action) :
    codedReturnAt input =
      Popping.returnAt input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  rfl

private def codedReturnAtReturnTable
    (input : HeadIndexInput Action) : Option ℕ :=
  codedReturnAt
    (input.1, codedReturnTable input.1, input.2.1, input.2.2)

private theorem codedReturnAtReturnTable_primrec :
    Primrec (codedReturnAtReturnTable (Action := Action)) := by
  unfold codedReturnAtReturnTable
  exact codedReturnAt_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (codedReturnTable_primrec.comp Primrec.fst)
        Primrec.snd))

private theorem codedReturnAtReturnTable_eq
    (input : HeadIndexInput Action) :
    codedReturnAtReturnTable input =
      Popping.returnAt input.1 (Popping.returnTable input.1)
        input.2.1 input.2.2 := by
  unfold codedReturnAtReturnTable
  rw [codedReturnAt_eq, codedReturnTable_eq]

private def codedNormalizeStack
    (input : EncodedDPDA Action × List ℕ) : List ℕ :=
  input.2.map fun Z => Z % input.1.numStackSymbols

private theorem codedNormalizeStack_primrec :
    Primrec (codedNormalizeStack (Action := Action)) := by
  have hmap : Primrec₂ (fun (input : EncodedDPDA Action × List ℕ)
      (Z : ℕ) => Z % input.1.numStackSymbols) := by
    apply Primrec₂.mk
    exact Primrec.nat_mod.comp Primrec.snd
      (numStackSymbols_primrec.comp
        (Primrec.fst.comp Primrec.fst))
  unfold codedNormalizeStack
  exact Primrec.list_map Primrec.snd hmap

private theorem codedNormalizeStack_eq
    (input : EncodedDPDA Action × List ℕ) :
    codedNormalizeStack input = Popping.normalizeStack input.1 input.2 := by
  rfl

private abbrev SkipResultCode :=
  ℕ ⊕ (ℕ × ℕ × List ℕ)

private def skipResultEquiv :
    Popping.SkipResult ≃ SkipResultCode where
  toFun
    | .returned state => .inl state
    | .blocked state symbol suffix => .inr (state, symbol, suffix)
  invFun
    | .inl state => .returned state
    | .inr blocked => .blocked blocked.1 blocked.2.1 blocked.2.2
  left_inv result := by cases result <;> rfl
  right_inv code := by cases code <;> rfl

private local instance skipResultPrimcodable :
    Primcodable Popping.SkipResult :=
  Primcodable.ofEquiv SkipResultCode skipResultEquiv

private abbrev SkipInput (Action : Type) :=
  EncodedDPDA Action × (Popping.ReturnTable × ℕ × List ℕ)

private abbrev SkipFoldCode :=
  Bool × (ℕ × ℕ × List ℕ)

private abbrev SkipStepInput (Action : Type) :=
  SkipInput Action × (SkipFoldCode × ℕ)

private def codedSkipStepMachine
    (input : SkipStepInput Action) : EncodedDPDA Action :=
  input.1.1

private theorem codedSkipStepMachine_primrec :
    Primrec (codedSkipStepMachine (Action := Action)) :=
  Primrec.fst.comp Primrec.fst

private def codedSkipStepTable
    (input : SkipStepInput Action) : Popping.ReturnTable :=
  input.1.2.1

private theorem codedSkipStepTable_primrec :
    Primrec (codedSkipStepTable (Action := Action)) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.fst)

private def codedSkipStepState
    (input : SkipStepInput Action) : SkipFoldCode :=
  input.2.1

private theorem codedSkipStepState_primrec :
    Primrec (codedSkipStepState (Action := Action)) :=
  Primrec.fst.comp Primrec.snd

private def codedSkipStepSymbol
    (input : SkipStepInput Action) : ℕ :=
  input.2.2

private theorem codedSkipStepSymbol_primrec :
    Primrec (codedSkipStepSymbol (Action := Action)) :=
  Primrec.snd.comp Primrec.snd

private def codedSkipStepReturn
    (input : SkipStepInput Action) : Option ℕ :=
  codedReturnAt
    (codedSkipStepMachine input,
      codedSkipStepTable input,
      (codedSkipStepState input).2.1,
      codedSkipStepSymbol input)

private theorem codedSkipStepReturn_primrec :
    Primrec (codedSkipStepReturn (Action := Action)) := by
  unfold codedSkipStepReturn
  exact codedReturnAt_primrec.comp
    (Primrec.pair codedSkipStepMachine_primrec
      (Primrec.pair codedSkipStepTable_primrec
        (Primrec.pair
          (Primrec.fst.comp
            (Primrec.snd.comp codedSkipStepState_primrec))
          codedSkipStepSymbol_primrec)))

private def codedSkipActiveCode
    (input : SkipStepInput Action) : SkipFoldCode :=
  bif (codedSkipStepReturn input).isSome then
    (false,
      (codedSkipStepReturn input).getD 0 %
        (codedSkipStepMachine input).numStates,
      0,
      [])
  else
    (true,
      (codedSkipStepState input).2.1 %
        (codedSkipStepMachine input).numStates,
      codedSkipStepSymbol input %
        (codedSkipStepMachine input).numStackSymbols,
      [])

private theorem codedSkipActiveCode_primrec :
    Primrec (codedSkipActiveCode (Action := Action)) := by
  have hmachineStates : Primrec (fun input : SkipStepInput Action =>
      (codedSkipStepMachine input).numStates) :=
    numStates_primrec.comp codedSkipStepMachine_primrec
  have hmachineStack : Primrec (fun input : SkipStepInput Action =>
      (codedSkipStepMachine input).numStackSymbols) :=
    numStackSymbols_primrec.comp codedSkipStepMachine_primrec
  have hreturn := codedSkipStepReturn_primrec (Action := Action)
  have hisSome : Primrec (fun input : SkipStepInput Action =>
      (codedSkipStepReturn input).isSome) :=
    Primrec.option_isSome.comp hreturn
  have htarget : Primrec (fun input : SkipStepInput Action =>
      (codedSkipStepReturn input).getD 0) :=
    Primrec.option_getD.comp hreturn (Primrec.const 0)
  have hsome : Primrec (fun input : SkipStepInput Action =>
      ((false,
        (codedSkipStepReturn input).getD 0 %
          (codedSkipStepMachine input).numStates,
        0,
        []) : SkipFoldCode)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.pair
        (Primrec.nat_mod.comp htarget hmachineStates)
        (Primrec.pair (Primrec.const 0) (Primrec.const [])))
  have hnone : Primrec (fun input : SkipStepInput Action =>
      ((true,
        (codedSkipStepState input).2.1 %
          (codedSkipStepMachine input).numStates,
        codedSkipStepSymbol input %
          (codedSkipStepMachine input).numStackSymbols,
        []) : SkipFoldCode)) :=
    Primrec.pair (Primrec.const true)
      (Primrec.pair
        (Primrec.nat_mod.comp
          (Primrec.fst.comp
            (Primrec.snd.comp codedSkipStepState_primrec))
          hmachineStates)
        (Primrec.pair
          (Primrec.nat_mod.comp codedSkipStepSymbol_primrec hmachineStack)
          (Primrec.const [])))
  unfold codedSkipActiveCode
  exact Primrec.cond hisSome hsome hnone

private def codedSkipBlockedCode
    (input : SkipStepInput Action) : SkipFoldCode :=
  (true,
    (codedSkipStepState input).2.1,
    (codedSkipStepState input).2.2.1,
    (codedSkipStepState input).2.2.2 ++
      [codedSkipStepSymbol input %
        (codedSkipStepMachine input).numStackSymbols])

private theorem codedSkipBlockedCode_primrec :
    Primrec (codedSkipBlockedCode (Action := Action)) := by
  have hnormalized : Primrec (fun input : SkipStepInput Action =>
      codedSkipStepSymbol input %
        (codedSkipStepMachine input).numStackSymbols) :=
    Primrec.nat_mod.comp codedSkipStepSymbol_primrec
      (numStackSymbols_primrec.comp codedSkipStepMachine_primrec)
  unfold codedSkipBlockedCode
  exact Primrec.pair (Primrec.const true)
    (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp codedSkipStepState_primrec))
      (Primrec.pair
        (Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp codedSkipStepState_primrec)))
        (Primrec.list_concat.comp
          (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp
              codedSkipStepState_primrec)))
          hnormalized)))

private def codedSkipFoldStep
    (input : SkipStepInput Action) : SkipFoldCode :=
  bif (codedSkipStepState input).1 then
    codedSkipBlockedCode input
  else codedSkipActiveCode input

private theorem codedSkipFoldStep_primrec :
    Primrec (codedSkipFoldStep (Action := Action)) := by
  unfold codedSkipFoldStep
  exact Primrec.cond
    (Primrec.fst.comp codedSkipStepState_primrec)
    codedSkipBlockedCode_primrec codedSkipActiveCode_primrec

private def rawSkipFold (input : SkipInput Action) : SkipFoldCode :=
  input.2.2.2.foldl
    (fun state Z => codedSkipFoldStep (input, state, Z))
      (false, input.2.2.1 % input.1.numStates, 0, [])

private def defaultSkipFoldCode : SkipFoldCode :=
  (false, 0, 0, [])

private def skipFoldCodeOfNat (code : ℕ) : SkipFoldCode :=
  (Encodable.decode code).getD defaultSkipFoldCode

private theorem skipFoldCodeOfNat_primrec :
    Primrec skipFoldCodeOfNat := by
  unfold skipFoldCodeOfNat
  exact Primrec.option_getD.comp Primrec.decode
    (Primrec.const defaultSkipFoldCode)

@[simp] private theorem skipFoldCodeOfNat_encode
    (state : SkipFoldCode) :
    skipFoldCodeOfNat (Encodable.encode state) = state := by
  simp [skipFoldCodeOfNat]

private abbrev SkipNatStepInput (Action : Type) :=
  SkipInput Action × (ℕ × ℕ)

private def codedSkipNatStep
    (input : SkipNatStepInput Action) : ℕ :=
  Encodable.encode (codedSkipFoldStep
    (input.1, skipFoldCodeOfNat input.2.1, input.2.2))

private theorem codedSkipNatStep_primrec :
    Primrec (codedSkipNatStep (Action := Action)) := by
  have hstepInput : Primrec (fun input : SkipNatStepInput Action =>
      (input.1, skipFoldCodeOfNat input.2.1, input.2.2)) :=
    Primrec.pair Primrec.fst
      (Primrec.pair
        (skipFoldCodeOfNat_primrec.comp
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  unfold codedSkipNatStep
  exact Primrec.encode.comp
    ((codedSkipFoldStep_primrec (Action := Action)).comp hstepInput)

private def defaultSkipInput : SkipInput Action :=
  (defaultEncodedDPDA, [], 0, [])

private def skipInputOfCode (code : ℕ) : SkipInput Action :=
  (Encodable.decode code).getD defaultSkipInput

private theorem skipInputOfCode_primrec :
    Primrec (skipInputOfCode (Action := Action)) := by
  unfold skipInputOfCode
  exact Primrec.option_getD.comp Primrec.decode
    (Primrec.const (defaultSkipInput (Action := Action)))

@[simp] private theorem skipInputOfCode_encode
    (input : SkipInput Action) :
    skipInputOfCode (Encodable.encode input) = input := by
  simp [skipInputOfCode]

private abbrev CodedSkipNatStepInput :=
  ℕ × (ℕ × ℕ)

private def codedSkipNatStepOfCode
    (input : CodedSkipNatStepInput) : ℕ :=
  codedSkipNatStep
    (skipInputOfCode (Action := Action) input.1, input.2)

private theorem codedSkipNatStepOfCode_primrec :
    Primrec (codedSkipNatStepOfCode (Action := Action)) := by
  unfold codedSkipNatStepOfCode
  exact (codedSkipNatStep_primrec (Action := Action)).comp
    (Primrec.pair
      ((skipInputOfCode_primrec (Action := Action)).comp Primrec.fst)
      Primrec.snd)

private theorem skipNatStepEvaluator_exists :
    ∃ evaluator : CodedSkipNatStepInput → ℕ,
      Primrec evaluator ∧
        ∀ input, evaluator input =
          codedSkipNatStepOfCode (Action := Action) input :=
  ⟨codedSkipNatStepOfCode (Action := Action),
    codedSkipNatStepOfCode_primrec (Action := Action), fun _ => rfl⟩

private noncomputable def skipNatStepEvaluator :
    CodedSkipNatStepInput → ℕ :=
  Classical.choose (skipNatStepEvaluator_exists (Action := Action))

private theorem skipNatStepEvaluator_primrec :
    Primrec (skipNatStepEvaluator (Action := Action)) :=
  (Classical.choose_spec
    (skipNatStepEvaluator_exists (Action := Action))).1

private theorem skipNatStepEvaluator_eq (input : CodedSkipNatStepInput) :
    skipNatStepEvaluator (Action := Action) input =
      codedSkipNatStepOfCode (Action := Action) input :=
  (Classical.choose_spec
    (skipNatStepEvaluator_exists (Action := Action))).2 input

@[simp] private theorem skipNatStepEvaluator_encode
    (input : SkipInput Action) (state Z : ℕ) :
    skipNatStepEvaluator (Action := Action)
        (Encodable.encode input, state, Z) =
      codedSkipNatStep (input, state, Z) := by
  rw [skipNatStepEvaluator_eq]
  simp [codedSkipNatStepOfCode]

private def codedSkipStack (code : ℕ) : List ℕ :=
  (skipInputOfCode (Action := Action) code).2.2.2

private theorem codedSkipStack_primrec :
    Primrec (codedSkipStack (Action := Action)) := by
  unfold codedSkipStack
  exact (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp
    (skipInputOfCode_primrec (Action := Action))

@[simp] private theorem codedSkipStack_encode (input : SkipInput Action) :
    codedSkipStack (Action := Action) (Encodable.encode input) =
      input.2.2.2 := by
  simp [codedSkipStack]

private def codedSkipInitial (code : ℕ) : ℕ :=
  let input := skipInputOfCode (Action := Action) code
  Encodable.encode
    ((false, input.2.2.1 % input.1.numStates, 0, []) :
      SkipFoldCode)

private theorem codedSkipInitial_primrec :
    Primrec (codedSkipInitial (Action := Action)) := by
  have hinput := skipInputOfCode_primrec (Action := Action)
  have hinitialCode : Primrec (fun code : ℕ =>
      ((false,
        (skipInputOfCode (Action := Action) code).2.2.1 %
          (skipInputOfCode (Action := Action) code).1.numStates,
        0, []) : SkipFoldCode)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.pair
        (Primrec.nat_mod.comp
          ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp hinput)
          (numStates_primrec.comp (Primrec.fst.comp hinput)))
        (Primrec.pair (Primrec.const 0) (Primrec.const [])))
  unfold codedSkipInitial
  exact Primrec.encode.comp hinitialCode

@[simp] private theorem codedSkipInitial_encode (input : SkipInput Action) :
    codedSkipInitial (Action := Action) (Encodable.encode input) =
      Encodable.encode
        ((false, input.2.2.1 % input.1.numStates, 0, []) :
          SkipFoldCode) := by
  simp [codedSkipInitial]

private def rawSkipNatFoldOfCode (code : ℕ) : ℕ :=
  (codedSkipStack (Action := Action) code).foldl
    (fun state Z => skipNatStepEvaluator (Action := Action)
      (code, state, Z))
    (codedSkipInitial (Action := Action) code)

private theorem rawSkipNatFoldEvaluator_exists :
    ∃ evaluator : ℕ → ℕ,
      Primrec evaluator ∧
        ∀ code, evaluator code =
          rawSkipNatFoldOfCode (Action := Action) code := by
  let evaluator := fun code : ℕ =>
    (codedSkipStack (Action := Action) code).foldl
      (fun state Z => skipNatStepEvaluator (Action := Action)
        (code, state, Z))
      (codedSkipInitial (Action := Action) code)
  refine ⟨evaluator, ?_, ?_⟩
  · exact @primrec_nat_list_foldl
      (codedSkipStack (Action := Action))
      (codedSkipInitial (Action := Action))
      (fun code step =>
        skipNatStepEvaluator (Action := Action) (code, step))
      (codedSkipStack_primrec (Action := Action))
      (codedSkipInitial_primrec (Action := Action))
      (skipNatStepEvaluator_primrec (Action := Action)).to₂
  · intro code
    rfl

private noncomputable def rawSkipNatFoldEvaluator : ℕ → ℕ :=
  Classical.choose (rawSkipNatFoldEvaluator_exists (Action := Action))

private theorem rawSkipNatFoldEvaluator_primrec :
    Primrec (rawSkipNatFoldEvaluator (Action := Action)) :=
  (Classical.choose_spec
    (rawSkipNatFoldEvaluator_exists (Action := Action))).1

private theorem rawSkipNatFoldEvaluator_eq (code : ℕ) :
    rawSkipNatFoldEvaluator (Action := Action) code =
      rawSkipNatFoldOfCode (Action := Action) code :=
  (Classical.choose_spec
    (rawSkipNatFoldEvaluator_exists (Action := Action))).2 code

private def skipFoldEvaluator (input : SkipInput Action) : SkipFoldCode :=
  skipFoldCodeOfNat
    (rawSkipNatFoldEvaluator (Action := Action) (Encodable.encode input))

private theorem skipFoldEvaluator_primrec :
    Primrec (skipFoldEvaluator (Action := Action)) := by
  unfold skipFoldEvaluator
  exact skipFoldCodeOfNat_primrec.comp
    ((rawSkipNatFoldEvaluator_primrec (Action := Action)).comp Primrec.encode)

private theorem skipFoldNatLoop_eq (input : SkipInput Action) :
    ∀ (stack : List ℕ) (state : SkipFoldCode),
      skipFoldCodeOfNat
          (stack.foldl
            (fun code Z => codedSkipNatStep (input, code, Z))
            (Encodable.encode state)) =
        stack.foldl
          (fun current Z => codedSkipFoldStep (input, current, Z))
          state := by
  intro stack
  induction stack with
  | nil =>
      intro state
      simp
  | cons Z stack ih =>
      intro state
      simp only [List.foldl_cons]
      have hstep : codedSkipNatStep
          (input, Encodable.encode state, Z) =
          Encodable.encode (codedSkipFoldStep (input, state, Z)) := by
        simp [codedSkipNatStep]
      rw [hstep]
      exact ih (codedSkipFoldStep (input, state, Z))

private theorem skipFoldEvaluator_eq (input : SkipInput Action) :
    skipFoldEvaluator input = rawSkipFold input := by
  unfold skipFoldEvaluator
  rw [rawSkipNatFoldEvaluator_eq]
  unfold rawSkipNatFoldOfCode rawSkipFold
  rw [codedSkipStack_encode, codedSkipInitial_encode]
  simp only [skipNatStepEvaluator_encode]
  exact skipFoldNatLoop_eq input input.2.2.2
    (false, input.2.2.1 % input.1.numStates, 0, [])

private def codedSkipResultCode (input : SkipInput Action) : SkipResultCode :=
  bif (skipFoldEvaluator input).1 then
    .inr ((skipFoldEvaluator input).2.1,
      (skipFoldEvaluator input).2.2.1,
      (skipFoldEvaluator input).2.2.2)
  else .inl (skipFoldEvaluator input).2.1

private def rawSkipReturnable (input : SkipInput Action) :
    Popping.SkipResult :=
  skipResultEquiv.symm (codedSkipResultCode input)

private theorem codedSkipResultCode_primrec :
    Primrec (codedSkipResultCode (Action := Action)) := by
  have hfold := skipFoldEvaluator_primrec (Action := Action)
  have hblocked : Primrec (fun input : SkipInput Action =>
      (skipFoldEvaluator input).1) := Primrec.fst.comp hfold
  have hinr : Primrec (fun input : SkipInput Action =>
      (Sum.inr ((skipFoldEvaluator input).2.1,
        (skipFoldEvaluator input).2.2.1,
        (skipFoldEvaluator input).2.2.2) : SkipResultCode)) :=
    Primrec.sumInr.comp (Primrec.snd.comp hfold)
  have hinl : Primrec (fun input : SkipInput Action =>
      (Sum.inl (skipFoldEvaluator input).2.1 : SkipResultCode)) :=
    Primrec.sumInl.comp (Primrec.fst.comp (Primrec.snd.comp hfold))
  unfold codedSkipResultCode
  exact Primrec.cond hblocked hinr hinl

private theorem rawSkipReturnable_primrec :
    Primrec (rawSkipReturnable (Action := Action)) := by
  unfold rawSkipReturnable
  exact Primrec.of_equiv_symm.comp
    (codedSkipResultCode_primrec (Action := Action))

private def skipCodeResult (code : SkipFoldCode) : Popping.SkipResult :=
  bif code.1 then
    .blocked code.2.1 code.2.2.1 code.2.2.2
  else .returned code.2.1

private theorem rawSkipReturnable_code (input : SkipInput Action) :
    rawSkipReturnable input = skipCodeResult (rawSkipFold input) := by
  unfold rawSkipReturnable codedSkipResultCode skipCodeResult
  rw [skipFoldEvaluator_eq]
  cases hblocked : (rawSkipFold input).1 <;>
    simp [hblocked, skipResultEquiv]

private theorem codedSkipFoldStep_active_some
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (storedState q₀ Z : ℕ) (storedStack : List ℕ)
    (target : ℕ)
    (hreturn : Popping.returnAt machine table storedState Z = some target) :
    codedSkipFoldStep
        ((machine, table, q₀, storedStack),
          (false, storedState, 0, []), Z) =
      (false, target % machine.numStates, 0, []) := by
  simp [codedSkipFoldStep, codedSkipStepState, codedSkipActiveCode,
    codedSkipStepReturn, codedSkipStepMachine, codedSkipStepTable,
    codedSkipStepSymbol, codedReturnAt_eq, hreturn]

private theorem codedSkipFoldStep_active_none
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (storedState q₀ Z : ℕ) (storedStack : List ℕ)
    (hreturn : Popping.returnAt machine table storedState Z = none) :
    codedSkipFoldStep
        ((machine, table, q₀, storedStack),
          (false, storedState, 0, []), Z) =
      (true, storedState % machine.numStates,
        Z % machine.numStackSymbols, []) := by
  simp [codedSkipFoldStep, codedSkipStepState, codedSkipActiveCode,
    codedSkipStepReturn, codedSkipStepMachine, codedSkipStepTable,
    codedSkipStepSymbol, codedReturnAt_eq, hreturn]

private theorem codedSkipFoldStep_blocked
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q₀ Z state top : ℕ) (storedStack suffix : List ℕ) :
    codedSkipFoldStep
        ((machine, table, q₀, storedStack),
          (true, state, top, suffix), Z) =
      (true, state, top,
        suffix ++ [Z % machine.numStackSymbols]) := by
  rfl

private theorem codedSkipFoldStep_blocked_fold
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q₀ state top : ℕ) (storedStack suffix stack : List ℕ) :
    stack.foldl
        (fun current Z => codedSkipFoldStep
          ((machine, table, q₀, storedStack), current, Z))
        (true, state, top, suffix) =
      (true, state, top,
        suffix ++ Popping.normalizeStack machine stack) := by
  induction stack generalizing suffix with
  | nil => simp [Popping.normalizeStack]
  | cons Z stack ih =>
      simp only [List.foldl_cons]
      rw [codedSkipFoldStep_blocked]
      rw [ih]
      simp [Popping.normalizeStack, List.append_assoc]

private theorem codedSkipFoldStep_input_irrel
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q₁ q₂ : ℕ) (stack₁ stack₂ : List ℕ)
    (state : SkipFoldCode) (Z : ℕ) :
    codedSkipFoldStep ((machine, table, q₁, stack₁), state, Z) =
      codedSkipFoldStep ((machine, table, q₂, stack₂), state, Z) := by
  rfl

private theorem codedSkipFold_input_irrel
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q₁ q₂ : ℕ) (stack₁ stack₂ stack : List ℕ)
    (state : SkipFoldCode) :
    stack.foldl
        (fun current Z => codedSkipFoldStep
          ((machine, table, q₁, stack₁), current, Z)) state =
      stack.foldl
        (fun current Z => codedSkipFoldStep
          ((machine, table, q₂, stack₂), current, Z)) state := by
  induction stack generalizing state with
  | nil => rfl
  | cons Z stack ih =>
      simp only [List.foldl_cons]
      rw [codedSkipFoldStep_input_irrel]
      exact ih _

private theorem returnAt_normalizedState
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q Z : ℕ) :
    Popping.returnAt machine table (q % machine.numStates) Z =
      Popping.returnAt machine table q Z := by
  simp [Popping.returnAt, Popping.headIndex, Nat.mod_mod]

private theorem skipCodeResult_rawSkipFold_eq
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable) :
    ∀ (q : ℕ) (stack : List ℕ),
      skipCodeResult (rawSkipFold (machine, table, q, stack)) =
        Popping.skipReturnable machine table q stack := by
  intro q stack
  induction stack generalizing q with
  | nil =>
      simp [rawSkipFold, skipCodeResult, Popping.skipReturnable]
  | cons Z stack ih =>
      cases hreturn : Popping.returnAt machine table q Z with
      | some target =>
          have hnormalized :
              Popping.returnAt machine table (q % machine.numStates) Z =
                some target := by
            simpa [returnAt_normalizedState] using hreturn
          unfold rawSkipFold
          simp only [List.foldl_cons]
          rw [codedSkipFoldStep_active_some machine table
            (q % machine.numStates) q Z (Z :: stack) target hnormalized]
          rw [codedSkipFold_input_irrel machine table q target
            (Z :: stack) stack stack]
          simpa [rawSkipFold, Popping.skipReturnable, hreturn] using ih target
      | none =>
          have hnormalized :
              Popping.returnAt machine table (q % machine.numStates) Z =
                none := by
            simpa [returnAt_normalizedState] using hreturn
          unfold rawSkipFold
          simp only [List.foldl_cons]
          rw [codedSkipFoldStep_active_none machine table
            (q % machine.numStates) q Z (Z :: stack) hnormalized]
          simp only [Nat.mod_mod]
          rw [codedSkipFoldStep_blocked_fold machine table q
            (q % machine.numStates) (Z % machine.numStackSymbols)
            (Z :: stack) [] stack]
          simp [skipCodeResult, Popping.skipReturnable, hreturn,
            Popping.normalizeStack]

private theorem rawSkipReturnable_eq
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q : ℕ) (stack : List ℕ) :
    rawSkipReturnable (machine, table, q, stack) =
      Popping.skipReturnable machine table q stack := by
  rw [rawSkipReturnable_code]
  exact skipCodeResult_rawSkipFold_eq machine table q stack

private abbrev SkipStackInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × List ℕ)

private def codedSkipReturnableReturnTable
    (input : SkipStackInput Action) : Popping.SkipResult :=
  rawSkipReturnable
    (input.1, codedReturnTable input.1, input.2.1, input.2.2)

private theorem codedSkipReturnableReturnTable_primrec :
    Primrec (codedSkipReturnableReturnTable (Action := Action)) := by
  unfold codedSkipReturnableReturnTable
  exact rawSkipReturnable_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (codedReturnTable_primrec.comp Primrec.fst)
        Primrec.snd))

private theorem codedSkipReturnableReturnTable_eq
    (input : SkipStackInput Action) :
    codedSkipReturnableReturnTable input =
      Popping.skipReturnable input.1 (Popping.returnTable input.1)
        input.2.1 input.2.2 := by
  unfold codedSkipReturnableReturnTable
  rw [rawSkipReturnable_eq, codedReturnTable_eq]

private def selectedEpsilonEvaluator
    (input : EncodedDPDA Action × (ℕ × ℕ)) :
    Option (ℕ × List ℕ) :=
  epsilonStepEvaluator (Action := Action) input

private theorem selectedEpsilonEvaluator_primrec :
    Primrec (selectedEpsilonEvaluator (Action := Action)) := by
  unfold selectedEpsilonEvaluator
  exact epsilonStepEvaluator_primrec (Action := Action)

private theorem selectedEpsilonEvaluator_eq
    (input : EncodedDPDA Action × (ℕ × ℕ)) :
    selectedEpsilonEvaluator input =
      selectedEpsilon? input.1 input.2.1 input.2.2 := by
  unfold selectedEpsilonEvaluator
  rw [epsilonStepEvaluator_eq]
  exact (selectedEpsilon?_eq_epsilonStep?
    input.1 input.2.1 input.2.2).symm

private abbrev ExposeFoldCode :=
  Bool × (Option Popping.ExposedHead × Popping.ExposedHead)

private def defaultExposedHead : Popping.ExposedHead :=
  (0, 0, [])

private abbrev ExposeStepInput (Action : Type) :=
  (EncodedDPDA Action × Popping.ReturnTable) × ExposeFoldCode

private def codedExposeMachine
    (input : ExposeStepInput Action) : EncodedDPDA Action :=
  input.1.1

private theorem codedExposeMachine_primrec :
    Primrec (codedExposeMachine (Action := Action)) :=
  Primrec.fst.comp Primrec.fst

private def codedExposeTable
    (input : ExposeStepInput Action) : Popping.ReturnTable :=
  input.1.2

private theorem codedExposeTable_primrec :
    Primrec (codedExposeTable (Action := Action)) :=
  Primrec.snd.comp Primrec.fst

private def codedExposeCode
    (input : ExposeStepInput Action) : ExposeFoldCode :=
  input.2

private theorem codedExposeCode_primrec :
    Primrec (codedExposeCode (Action := Action)) :=
  Primrec.snd

private def codedExposeHead
    (input : ExposeStepInput Action) : Popping.ExposedHead :=
  (codedExposeCode input).2.2

private theorem codedExposeHead_primrec :
    Primrec (codedExposeHead (Action := Action)) := by
  unfold codedExposeHead
  exact Primrec.snd.comp (Primrec.snd.comp codedExposeCode_primrec)

private def codedExposeEpsilon
    (input : ExposeStepInput Action) : Option (ℕ × List ℕ) :=
  selectedEpsilonEvaluator
    (codedExposeMachine input,
      (codedExposeHead input).1,
      (codedExposeHead input).2.1)

private theorem codedExposeEpsilon_primrec :
    Primrec (codedExposeEpsilon (Action := Action)) := by
  unfold codedExposeEpsilon
  exact selectedEpsilonEvaluator_primrec.comp
    (Primrec.pair codedExposeMachine_primrec
      (Primrec.pair
        (Primrec.fst.comp codedExposeHead_primrec)
        (Primrec.fst.comp (Primrec.snd.comp codedExposeHead_primrec))))

private def codedExposeNoEpsilon
    (input : ExposeStepInput Action) : ExposeFoldCode :=
  (true,
    some
      ((codedExposeHead input).1 % (codedExposeMachine input).numStates,
        (codedExposeHead input).2.1 %
          (codedExposeMachine input).numStackSymbols,
        codedNormalizeStack
          (codedExposeMachine input, (codedExposeHead input).2.2)),
    defaultExposedHead)

private theorem codedExposeNoEpsilon_primrec :
    Primrec (codedExposeNoEpsilon (Action := Action)) := by
  have hstates : Primrec (fun input : ExposeStepInput Action =>
      (codedExposeMachine input).numStates) :=
    numStates_primrec.comp codedExposeMachine_primrec
  have hstack : Primrec (fun input : ExposeStepInput Action =>
      (codedExposeMachine input).numStackSymbols) :=
    numStackSymbols_primrec.comp codedExposeMachine_primrec
  have hnormalized : Primrec (fun input : ExposeStepInput Action =>
      codedNormalizeStack
        (codedExposeMachine input, (codedExposeHead input).2.2)) :=
    codedNormalizeStack_primrec.comp
      (Primrec.pair codedExposeMachine_primrec
        (Primrec.snd.comp (Primrec.snd.comp codedExposeHead_primrec)))
  unfold codedExposeNoEpsilon
  exact Primrec.pair (Primrec.const true)
    (Primrec.pair
      (Primrec.option_some.comp
        (Primrec.pair
          (Primrec.nat_mod.comp
            (Primrec.fst.comp codedExposeHead_primrec) hstates)
          (Primrec.pair
            (Primrec.nat_mod.comp
              (Primrec.fst.comp (Primrec.snd.comp codedExposeHead_primrec))
              hstack)
            hnormalized)))
      (Primrec.const defaultExposedHead))

private abbrev ExposeAfterSkipInput (Action : Type) :=
  ExposeStepInput Action × (ℕ × List ℕ)

private def codedExposeSkip
    (input : ExposeAfterSkipInput Action) : Popping.SkipResult :=
  rawSkipReturnable
    (codedExposeMachine input.1, codedExposeTable input.1,
      input.2.1, input.2.2)

private theorem codedExposeSkip_primrec :
    Primrec (codedExposeSkip (Action := Action)) := by
  unfold codedExposeSkip
  exact rawSkipReturnable_primrec.comp
    (Primrec.pair
      (codedExposeMachine_primrec.comp Primrec.fst)
      (Primrec.pair
        (codedExposeTable_primrec.comp Primrec.fst)
        Primrec.snd))

private def codedExposeSkipFold
    (input : ExposeAfterSkipInput Action) : SkipFoldCode :=
  skipFoldEvaluator
    (codedExposeMachine input.1, codedExposeTable input.1,
      input.2.1, input.2.2)

private theorem codedExposeSkipFold_primrec :
    Primrec (codedExposeSkipFold (Action := Action)) := by
  unfold codedExposeSkipFold
  exact skipFoldEvaluator_primrec.comp
    (Primrec.pair
      (codedExposeMachine_primrec.comp Primrec.fst)
      (Primrec.pair
        (codedExposeTable_primrec.comp Primrec.fst)
        Primrec.snd))

private theorem codedExposeSkipFold_eq
    (input : ExposeAfterSkipInput Action) :
    skipCodeResult (codedExposeSkipFold input) =
      Popping.skipReturnable (codedExposeMachine input.1)
        (codedExposeTable input.1) input.2.1 input.2.2 := by
  unfold codedExposeSkipFold
  rw [skipFoldEvaluator_eq]
  exact skipCodeResult_rawSkipFold_eq _ _ _ _

private def codedExposeAfterSkip
    (input : ExposeAfterSkipInput Action) : ExposeFoldCode :=
  bif (codedExposeSkipFold input).1 then
    (false, none,
      ((codedExposeSkipFold input).2.1,
        (codedExposeSkipFold input).2.2.1,
        (codedExposeSkipFold input).2.2.2 ++
          (codedExposeHead input.1).2.2))
  else
    (true, none, defaultExposedHead)

private theorem codedExposeAfterSkip_primrec :
    Primrec (codedExposeAfterSkip (Action := Action)) := by
  have hskip := codedExposeSkipFold_primrec (Action := Action)
  have hblocked : Primrec (fun input : ExposeAfterSkipInput Action =>
      (codedExposeSkipFold input).1) :=
    Primrec.fst.comp hskip
  have hactive : Primrec (fun input : ExposeAfterSkipInput Action =>
      ((false, none,
        ((codedExposeSkipFold input).2.1,
          (codedExposeSkipFold input).2.2.1,
          (codedExposeSkipFold input).2.2.2 ++
            (codedExposeHead input.1).2.2)) :
        ExposeFoldCode)) := by
    exact Primrec.pair (Primrec.const false)
      (Primrec.pair (Primrec.const none)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hskip))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp
              (Primrec.snd.comp hskip)))
            (Primrec.list_append.comp
              (Primrec.snd.comp (Primrec.snd.comp
                (Primrec.snd.comp hskip)))
              (Primrec.snd.comp (Primrec.snd.comp
                ((codedExposeHead_primrec (Action := Action)).comp
                  Primrec.fst)))))))
  have hreturned : Primrec (fun (_ : ExposeAfterSkipInput Action) =>
      ((true, none, defaultExposedHead) : ExposeFoldCode)) :=
    Primrec.const (true, none, defaultExposedHead)
  unfold codedExposeAfterSkip
  exact Primrec.cond hblocked hactive hreturned

private def codedExposeHasEpsilon
    (input : ExposeStepInput Action) : Bool :=
  (codedExposeEpsilon input).isSome

private theorem codedExposeHasEpsilon_primrec :
    Primrec (codedExposeHasEpsilon (Action := Action)) := by
  unfold codedExposeHasEpsilon
  exact Primrec.option_isSome.comp codedExposeEpsilon_primrec

private def codedExposeEpsilonOutput
    (input : ExposeStepInput Action) : ℕ × List ℕ :=
  (codedExposeEpsilon input).getD (0, [])

private theorem codedExposeEpsilonOutput_primrec :
    Primrec (codedExposeEpsilonOutput (Action := Action)) := by
  unfold codedExposeEpsilonOutput
  exact Primrec.option_getD.comp codedExposeEpsilon_primrec
    (Primrec.const (0, []))

private def codedExposeActive
    (input : ExposeStepInput Action) : ExposeFoldCode :=
  bif codedExposeHasEpsilon input then
    codedExposeAfterSkip (input, codedExposeEpsilonOutput input)
  else
    codedExposeNoEpsilon input

private theorem codedExposeActive_primrec :
    Primrec (codedExposeActive (Action := Action)) := by
  have hsome : Primrec (fun input : ExposeStepInput Action =>
      codedExposeAfterSkip (input, codedExposeEpsilonOutput input)) :=
    codedExposeAfterSkip_primrec.comp
      (Primrec.pair Primrec.id codedExposeEpsilonOutput_primrec)
  unfold codedExposeActive
  exact Primrec.cond codedExposeHasEpsilon_primrec hsome
    codedExposeNoEpsilon_primrec

private def codedExposeFoldStep
    (input : ExposeStepInput Action) : ExposeFoldCode :=
  bif (codedExposeCode input).1 then codedExposeCode input
  else codedExposeActive input

private theorem codedExposeFoldStep_primrec :
    Primrec (codedExposeFoldStep (Action := Action)) := by
  unfold codedExposeFoldStep
  exact Primrec.cond
    (Primrec.fst.comp codedExposeCode_primrec)
    codedExposeCode_primrec codedExposeActive_primrec

private abbrev ExposeAuxInput (Action : Type) :=
  EncodedDPDA Action ×
    (Popping.ReturnTable × ℕ × Popping.ExposedHead)

private def rawExposeHeadAux (input : ExposeAuxInput Action) :
    Option Popping.ExposedHead :=
  let final :=
    (fun code => codedExposeFoldStep ((input.1, input.2.1), code))^[input.2.2.1]
      ((false, none, input.2.2.2) : ExposeFoldCode)
  bif final.1 then final.2.1 else none

private theorem rawExposeHeadAux_primrec :
    Primrec (rawExposeHeadAux (Action := Action)) := by
  have hstep : Primrec₂ (fun (input : ExposeAuxInput Action)
      (code : ExposeFoldCode) =>
      codedExposeFoldStep ((input.1, input.2.1), code)) := by
    apply Primrec₂.mk
    exact codedExposeFoldStep_primrec.comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        Primrec.snd)
  have hinitial : Primrec (fun input : ExposeAuxInput Action =>
      ((false, none, input.2.2.2) : ExposeFoldCode)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.pair (Primrec.const none)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hiterate : Primrec (fun input : ExposeAuxInput Action =>
      (fun code => codedExposeFoldStep ((input.1, input.2.1), code))^[input.2.2.1]
        ((false, none, input.2.2.2) : ExposeFoldCode)) :=
    Primrec.nat_iterate
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      hinitial hstep
  have hflag : Primrec (fun input : ExposeAuxInput Action =>
      ((fun code => codedExposeFoldStep ((input.1, input.2.1), code))^[input.2.2.1]
        ((false, none, input.2.2.2) : ExposeFoldCode)).1) :=
    Primrec.fst.comp hiterate
  have hresult : Primrec (fun input : ExposeAuxInput Action =>
      ((fun code => codedExposeFoldStep ((input.1, input.2.1), code))^[input.2.2.1]
        ((false, none, input.2.2.2) : ExposeFoldCode)).2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hiterate)
  unfold rawExposeHeadAux
  exact Primrec.cond hflag hresult (Primrec.const none)

private theorem skipCodeResult_returned_flag
    (code : SkipFoldCode) (state : ℕ)
    (hresult : skipCodeResult code = .returned state) :
    code.1 = false := by
  cases code with
  | mk flag data =>
      cases flag <;> simp [skipCodeResult] at hresult ⊢

private theorem skipCodeResult_blocked_code
    (code : SkipFoldCode) (state top : ℕ) (replacement : List ℕ)
    (hresult : skipCodeResult code =
      .blocked state top replacement) :
    code = (true, state, top, replacement) := by
  rcases code with ⟨flag, state', top', replacement'⟩
  cases flag
  · simp [skipCodeResult] at hresult
  · simp [skipCodeResult] at hresult
    rcases hresult with ⟨rfl, rfl, rfl⟩
    rfl

private theorem codedExposeFoldStep_none
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q Z : ℕ) (suffix : List ℕ)
    (hepsilon : selectedEpsilon? machine q Z = none) :
    codedExposeFoldStep
        ((machine, table),
          ((false, none, (q, Z, suffix)) : ExposeFoldCode)) =
      (true,
        some (q % machine.numStates, Z % machine.numStackSymbols,
          Popping.normalizeStack machine suffix),
        defaultExposedHead) := by
  simp [codedExposeFoldStep, codedExposeActive,
    codedExposeHasEpsilon, codedExposeEpsilonOutput,
    codedExposeEpsilon, codedExposeNoEpsilon,
    codedExposeCode, codedExposeHead, codedExposeMachine,
    selectedEpsilonEvaluator_eq, hepsilon, codedNormalizeStack_eq]

private theorem codedExposeFoldStep_returned
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q Z : ℕ) (suffix : List ℕ) (output : ℕ × List ℕ)
    (state : ℕ)
    (hepsilon : selectedEpsilon? machine q Z = some output)
    (hskip : Popping.skipReturnable machine table
      output.1 output.2 = .returned state) :
    codedExposeFoldStep
        ((machine, table),
          ((false, none, (q, Z, suffix)) : ExposeFoldCode)) =
      (true, none, defaultExposedHead) := by
  let input : ExposeAfterSkipInput Action :=
    (((machine, table),
      ((false, none, (q, Z, suffix)) : ExposeFoldCode)), output)
  have hresult := codedExposeSkipFold_eq (input := input)
  change skipCodeResult (codedExposeSkipFold input) =
    Popping.skipReturnable machine table output.1 output.2 at hresult
  rw [hskip] at hresult
  have hflag := skipCodeResult_returned_flag
    (codedExposeSkipFold input) state hresult
  simp [codedExposeFoldStep, codedExposeActive,
    codedExposeHasEpsilon, codedExposeEpsilonOutput,
    codedExposeEpsilon, codedExposeAfterSkip,
    codedExposeCode, codedExposeHead, codedExposeMachine,
    selectedEpsilonEvaluator_eq, hepsilon, input, hflag]

private theorem codedExposeFoldStep_blocked
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (q Z : ℕ) (suffix : List ℕ) (output : ℕ × List ℕ)
    (target top : ℕ) (replacement : List ℕ)
    (hepsilon : selectedEpsilon? machine q Z = some output)
    (hskip : Popping.skipReturnable machine table output.1 output.2 =
      .blocked target top replacement) :
    codedExposeFoldStep
        ((machine, table),
          ((false, none, (q, Z, suffix)) : ExposeFoldCode)) =
      (false, none, (target, top, replacement ++ suffix)) := by
  let input : ExposeAfterSkipInput Action :=
    (((machine, table),
      ((false, none, (q, Z, suffix)) : ExposeFoldCode)), output)
  have hresult := codedExposeSkipFold_eq (input := input)
  change skipCodeResult (codedExposeSkipFold input) =
    Popping.skipReturnable machine table output.1 output.2 at hresult
  rw [hskip] at hresult
  have hcode := skipCodeResult_blocked_code
    (codedExposeSkipFold input) target top replacement hresult
  simp [codedExposeFoldStep, codedExposeActive,
    codedExposeHasEpsilon, codedExposeEpsilonOutput,
    codedExposeEpsilon, codedExposeAfterSkip,
    codedExposeCode, codedExposeHead, codedExposeMachine,
    selectedEpsilonEvaluator_eq, hepsilon, input, hcode]

private theorem exposeFoldStep_terminal_iterate
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable)
    (fuel : ℕ) (result : Option Popping.ExposedHead)
    (head : Popping.ExposedHead) :
    (fun code => codedExposeFoldStep ((machine, table), code))^[fuel]
        ((true, result, head) : ExposeFoldCode) =
      (true, result, head) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply]
      change
        (fun code => codedExposeFoldStep ((machine, table), code))^[fuel]
            (codedExposeFoldStep
              ((machine, table),
                ((true, result, head) : ExposeFoldCode))) =
          (true, result, head)
      rw [show codedExposeFoldStep
          ((machine, table),
            ((true, result, head) : ExposeFoldCode)) =
          (true, result, head) by rfl]
      exact ih

private theorem rawExposeHeadAux_eq
    (machine : EncodedDPDA Action) (table : Popping.ReturnTable) :
    ∀ (fuel : ℕ) (head : Popping.ExposedHead),
      rawExposeHeadAux (machine, table, fuel, head) =
        Popping.exposeHeadAux machine table fuel head := by
  intro fuel
  induction fuel with
  | zero =>
      intro head
      rfl
  | succ fuel ih =>
      intro head
      rcases head with ⟨q, Z, suffix⟩
      cases hepsilon : selectedEpsilon? machine q Z with
      | none =>
          simp only [Popping.exposeHeadAux, hepsilon]
          unfold rawExposeHeadAux
          rw [Function.iterate_succ_apply]
          rw [codedExposeFoldStep_none machine table q Z suffix hepsilon]
          rw [exposeFoldStep_terminal_iterate]
          rfl
      | some output =>
          cases hskip : Popping.skipReturnable machine table
              output.1 output.2 with
          | returned state =>
              simp only [Popping.exposeHeadAux, hepsilon, hskip]
              unfold rawExposeHeadAux
              rw [Function.iterate_succ_apply]
              rw [codedExposeFoldStep_returned machine table q Z suffix
                output state hepsilon hskip]
              rw [exposeFoldStep_terminal_iterate]
              rfl
          | blocked target top replacement =>
              simp only [Popping.exposeHeadAux, hepsilon, hskip]
              unfold rawExposeHeadAux
              rw [Function.iterate_succ_apply]
              rw [codedExposeFoldStep_blocked machine table q Z suffix
                output target top replacement hepsilon hskip]
              exact ih (target, top, replacement ++ suffix)

private theorem exposeHeadAux_primrec :
    Primrec (fun input : ExposeAuxInput Action =>
      Popping.exposeHeadAux input.1 input.2.1
        input.2.2.1 input.2.2.2) := by
  apply rawExposeHeadAux_primrec.of_eq
  intro input
  exact rawExposeHeadAux_eq input.1 input.2.1
    input.2.2.1 input.2.2.2

private def rawExposeHead
    (input : EncodedDPDA Action × (ℕ × ℕ)) :
    Option Popping.ExposedHead :=
  rawExposeHeadAux
    (input.1, codedReturnTable input.1,
      input.1.numStates * input.1.numStackSymbols,
      (input.2.1 % input.1.numStates,
        input.2.2 % input.1.numStackSymbols, []))

private theorem rawExposeHead_primrec :
    Primrec (rawExposeHead (Action := Action)) := by
  unfold rawExposeHead
  exact rawExposeHeadAux_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (codedReturnTable_primrec.comp Primrec.fst)
        (Primrec.pair
          (Primrec.nat_mul.comp
            (numStates_primrec.comp Primrec.fst)
            (numStackSymbols_primrec.comp Primrec.fst))
          (Primrec.pair
            (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
              (numStates_primrec.comp Primrec.fst))
            (Primrec.pair
              (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd)
                (numStackSymbols_primrec.comp Primrec.fst))
              (Primrec.const []))))))

private theorem rawExposeHead_eq
    (input : EncodedDPDA Action × (ℕ × ℕ)) :
    rawExposeHead input =
      Popping.exposeHead input.1 input.2.1 input.2.2 := by
  unfold rawExposeHead Popping.exposeHead
  rw [rawExposeHeadAux_eq, codedReturnTable_eq]

private theorem exposeHead_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      Popping.exposeHead input.1 input.2.1 input.2.2) := by
  apply (rawExposeHead_primrec (Action := Action)).of_eq
  intro input
  exact rawExposeHead_eq input

private abbrev NormalizedRowInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × ℕ × Action)

private def selectedInputEvaluator
    (input : EncodedDPDA Action × (ℕ × Action × ℕ)) :
    Option (ℕ × List ℕ) :=
  deterministicInputStepEvaluator (Action := Action) input

private theorem selectedInputEvaluator_primrec :
    Primrec (selectedInputEvaluator (Action := Action)) := by
  unfold selectedInputEvaluator
  exact deterministicInputStepEvaluator_primrec (Action := Action)

private theorem selectedInputEvaluator_eq
    (input : EncodedDPDA Action × (ℕ × Action × ℕ)) :
    selectedInputEvaluator input =
      selectedInput? input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  unfold selectedInputEvaluator
  rw [deterministicInputStepEvaluator_eq]
  exact (selectedInput?_eq_inputStep?
    input.1 input.2.1 input.2.2.1 input.2.2.2).symm

private def rawNormalizedExposed
    (input : NormalizedRowInput Action) : Option Popping.ExposedHead :=
  rawExposeHead (input.1, input.2.1, input.2.2.1)

private theorem rawNormalizedExposed_primrec :
    Primrec (rawNormalizedExposed (Action := Action)) := by
  unfold rawNormalizedExposed
  exact rawExposeHead_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))

private def rawNormalizedStable
    (input : NormalizedRowInput Action) : Popping.ExposedHead :=
  (rawNormalizedExposed input).getD defaultExposedHead

private theorem rawNormalizedStable_primrec :
    Primrec (rawNormalizedStable (Action := Action)) := by
  unfold rawNormalizedStable
  exact Primrec.option_getD.comp rawNormalizedExposed_primrec
    (Primrec.const defaultExposedHead)

private def rawNormalizedSelected
    (input : NormalizedRowInput Action) : Option (ℕ × List ℕ) :=
  selectedInputEvaluator
    (input.1, (rawNormalizedStable input).1,
      input.2.2.2, (rawNormalizedStable input).2.1)

private theorem rawNormalizedSelected_primrec :
    Primrec (rawNormalizedSelected (Action := Action)) := by
  unfold rawNormalizedSelected
  exact selectedInputEvaluator_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair
        (Primrec.fst.comp rawNormalizedStable_primrec)
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp
            (Primrec.snd.comp rawNormalizedStable_primrec)))))

private def rawNormalizedOutput
    (input : NormalizedRowInput Action) : ℕ × List ℕ :=
  (rawNormalizedSelected input).getD (0, [])

private theorem rawNormalizedOutput_primrec :
    Primrec (rawNormalizedOutput (Action := Action)) := by
  unfold rawNormalizedOutput
  exact Primrec.option_getD.comp rawNormalizedSelected_primrec
    (Primrec.const (0, []))

private def rawNormalizedDead
    (input : NormalizedRowInput Action) : InputRow Action :=
  (input.2.1, input.2.2.2, input.2.2.1,
    Popping.deadState input.1, [input.2.2.1])

private theorem rawNormalizedDead_primrec :
    Primrec (rawNormalizedDead (Action := Action)) := by
  unfold rawNormalizedDead
  unfold Popping.deadState
  exact Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair (numStates_primrec.comp Primrec.fst)
          (Primrec.list_cons.comp
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.const [])))))

private def rawNormalizedSuccess
    (input : NormalizedRowInput Action) : InputRow Action :=
  (input.2.1, input.2.2.2, input.2.2.1,
    (rawNormalizedOutput input).1,
    (rawNormalizedOutput input).2 ++ (rawNormalizedStable input).2.2)

private theorem rawNormalizedSuccess_primrec :
    Primrec (rawNormalizedSuccess (Action := Action)) := by
  unfold rawNormalizedSuccess
  exact Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair
          (Primrec.fst.comp rawNormalizedOutput_primrec)
          (Primrec.list_append.comp
            (Primrec.snd.comp rawNormalizedOutput_primrec)
            (Primrec.snd.comp
              (Primrec.snd.comp rawNormalizedStable_primrec))))))

private def rawNormalizedRow
    (input : NormalizedRowInput Action) : InputRow Action :=
  bif (rawNormalizedExposed input).isSome then
    bif (rawNormalizedSelected input).isSome then
      rawNormalizedSuccess input
    else
      rawNormalizedDead input
  else
    rawNormalizedDead input

private theorem rawNormalizedRow_primrec :
    Primrec (rawNormalizedRow (Action := Action)) := by
  have hexposed : Primrec (fun input : NormalizedRowInput Action =>
      (rawNormalizedExposed input).isSome) :=
    Primrec.option_isSome.comp rawNormalizedExposed_primrec
  have hselected : Primrec (fun input : NormalizedRowInput Action =>
      (rawNormalizedSelected input).isSome) :=
    Primrec.option_isSome.comp rawNormalizedSelected_primrec
  have hstable : Primrec (fun input : NormalizedRowInput Action =>
      bif (rawNormalizedSelected input).isSome then
        rawNormalizedSuccess input
      else
        rawNormalizedDead input) :=
    Primrec.cond hselected rawNormalizedSuccess_primrec
      rawNormalizedDead_primrec
  unfold rawNormalizedRow
  exact Primrec.cond hexposed hstable rawNormalizedDead_primrec


private theorem rawNormalizedRow_eq
    (input : NormalizedRowInput Action) :
    rawNormalizedRow input =
      Popping.normalizedRow input.1 input.2.1
        input.2.2.1 input.2.2.2 := by
  unfold rawNormalizedRow Popping.normalizedRow
  cases hexposed : Popping.exposeHead input.1 input.2.1 input.2.2.1 with
  | none =>
      simp [rawNormalizedExposed, rawExposeHead_eq, hexposed,
        rawNormalizedDead]
  | some stable =>
      cases hselected : selectedInput? input.1 stable.1
          input.2.2.2 stable.2.1 with
      | none =>
          simp [rawNormalizedExposed, rawExposeHead_eq, hexposed,
            rawNormalizedStable, rawNormalizedSelected,
            selectedInputEvaluator_eq, hselected, rawNormalizedDead]
      | some output =>
          simp [rawNormalizedExposed, rawExposeHead_eq, hexposed,
            rawNormalizedStable, rawNormalizedSelected,
            selectedInputEvaluator_eq, hselected, rawNormalizedOutput,
            rawNormalizedSuccess]

private theorem normalizedRow_primrec :
    Primrec (fun input : NormalizedRowInput Action =>
      Popping.normalizedRow input.1 input.2.1
        input.2.2.1 input.2.2.2) := by
  apply (rawNormalizedRow_primrec (Action := Action)).of_eq
  intro input
  exact rawNormalizedRow_eq input

private def rawPoppingRows
    (machine : EncodedDPDA Action) : List EpsilonRow :=
  (List.range machine.numStates).flatMap fun q =>
    (List.range machine.numStackSymbols).filterMap fun Z =>
      (codedReturnAtReturnTable (machine, q, Z)).map fun target =>
        ((q, Z, target, []) : EpsilonRow)

private theorem rawPoppingRows_primrec :
    Primrec (rawPoppingRows :
      EncodedDPDA Action → List EpsilonRow) := by
  have hstates : Primrec (fun machine : EncodedDPDA Action =>
      List.range machine.numStates) :=
    Primrec.list_range.comp numStates_primrec
  have hqRows : Primrec₂ (fun (machine : EncodedDPDA Action) (q : ℕ) =>
      (List.range machine.numStackSymbols).filterMap fun Z =>
        (codedReturnAtReturnTable (machine, q, Z)).map
          fun target => ((q, Z, target, []) : EpsilonRow)) := by
    apply Primrec₂.mk
    have hstack : Primrec (fun input : EncodedDPDA Action × ℕ =>
        List.range input.1.numStackSymbols) :=
      Primrec.list_range.comp
        (numStackSymbols_primrec.comp Primrec.fst)
    have hrow : Primrec₂ (fun (input : EncodedDPDA Action × ℕ)
        (Z : ℕ) =>
        (codedReturnAtReturnTable (input.1, input.2, Z)).map fun target =>
            ((input.2, Z, target, []) : EpsilonRow)) := by
      apply Primrec₂.mk
      have hreturn : Primrec (fun input :
          (EncodedDPDA Action × ℕ) × ℕ =>
          codedReturnAtReturnTable
            (input.1.1, input.1.2, input.2)) :=
        codedReturnAtReturnTable_primrec.comp
          (Primrec.pair (Primrec.fst.comp Primrec.fst)
            (Primrec.pair (Primrec.snd.comp Primrec.fst)
              Primrec.snd))
      have hsome : Primrec₂ (fun (input :
          (EncodedDPDA Action × ℕ) × ℕ) (target : ℕ) =>
          ((input.1.2, input.2, target, []) : EpsilonRow)) := by
        apply Primrec₂.mk
        exact Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp Primrec.fst)
            (Primrec.pair Primrec.snd (Primrec.const [])))
      exact Primrec.option_map hreturn hsome
    exact Primrec.listFilterMap hstack hrow
  unfold rawPoppingRows
  exact Primrec.list_flatMap hstates hqRows

private theorem rawPoppingRows_eq (machine : EncodedDPDA Action) :
    rawPoppingRows machine = Popping.poppingRows machine := by
  unfold rawPoppingRows Popping.poppingRows
  simp only [codedReturnAtReturnTable_eq]

private abbrev MachineAlphabetInput (Action : Type) :=
  EncodedDPDA Action × List Action

private def rawNormalizedInputRows
    (input : MachineAlphabetInput Action) : List (InputRow Action) :=
  (List.range input.1.numStates).flatMap fun q =>
    (List.range input.1.numStackSymbols).flatMap fun Z =>
      bif (codedReturnAtReturnTable (input.1, q, Z)).isSome then
        []
      else
        input.2.map fun action =>
          rawNormalizedRow (input.1, q, Z, action)

private theorem rawNormalizedInputRows_primrec :
    Primrec (rawNormalizedInputRows (Action := Action)) := by
  have hstates : Primrec (fun input : MachineAlphabetInput Action =>
      List.range input.1.numStates) :=
    Primrec.list_range.comp (numStates_primrec.comp Primrec.fst)
  have hqRows : Primrec₂ (fun (input : MachineAlphabetInput Action)
      (q : ℕ) =>
      (List.range input.1.numStackSymbols).flatMap fun Z =>
        bif (codedReturnAtReturnTable (input.1, q, Z)).isSome then
          []
        else
          input.2.map fun action =>
            rawNormalizedRow (input.1, q, Z, action)) := by
    apply Primrec₂.mk
    have hstack : Primrec (fun input : MachineAlphabetInput Action × ℕ =>
        List.range input.1.1.numStackSymbols) :=
      Primrec.list_range.comp
        (numStackSymbols_primrec.comp
          (Primrec.fst.comp Primrec.fst))
    have hZRows : Primrec₂ (fun (input : MachineAlphabetInput Action × ℕ)
        (Z : ℕ) =>
        bif (codedReturnAtReturnTable
            (input.1.1, input.2, Z)).isSome then
          []
        else
          input.1.2.map fun action =>
            rawNormalizedRow (input.1.1, input.2, Z, action)) := by
      apply Primrec₂.mk
      have hreturn : Primrec (fun input :
          (MachineAlphabetInput Action × ℕ) × ℕ =>
          codedReturnAtReturnTable
            (input.1.1.1, input.1.2, input.2)) :=
        codedReturnAtReturnTable_primrec.comp
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.pair (Primrec.snd.comp Primrec.fst)
              Primrec.snd))
      have hflag : Primrec (fun input :
          (MachineAlphabetInput Action × ℕ) × ℕ =>
          (codedReturnAtReturnTable
            (input.1.1.1, input.1.2, input.2)).isSome) :=
        Primrec.option_isSome.comp hreturn
      have hnone : Primrec (fun input :
          (MachineAlphabetInput Action × ℕ) × ℕ =>
          input.1.1.2.map
            (fun action => rawNormalizedRow
              (input.1.1.1, input.1.2, input.2, action))) := by
        have hrow : Primrec₂ (fun (input :
            (MachineAlphabetInput Action × ℕ) × ℕ)
            (action : Action) =>
            rawNormalizedRow
              (input.1.1.1, input.1.2, input.2, action)) := by
          apply Primrec₂.mk
          exact rawNormalizedRow_primrec.comp
            (Primrec.pair
              (Primrec.fst.comp (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst)))
              (Primrec.pair
                (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
                (Primrec.pair (Primrec.snd.comp Primrec.fst)
                  Primrec.snd)))
        exact Primrec.list_map
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) hrow
      have hsome : Primrec₂ (fun (_ :
          (MachineAlphabetInput Action × ℕ) × ℕ) (_ : ℕ) =>
          ([] : List (InputRow Action))) := Primrec₂.const []
      have hempty : Primrec (fun (_ :
          (MachineAlphabetInput Action × ℕ) × ℕ) =>
          ([] : List (InputRow Action))) := Primrec.const []
      exact Primrec.cond hflag hempty hnone
    exact Primrec.list_flatMap hstack hZRows
  unfold rawNormalizedInputRows
  exact Primrec.list_flatMap hstates hqRows

private theorem rawNormalizedInputRows_eq
    (input : MachineAlphabetInput Action) :
    rawNormalizedInputRows input =
      Popping.normalizedInputRows input.1 input.2 := by
  unfold rawNormalizedInputRows Popping.normalizedInputRows
  simp only [codedReturnAtReturnTable_eq]
  congr 1
  funext q
  congr 1
  funext Z
  cases hreturn : Popping.returnAt input.1
      (Popping.returnTable input.1) q Z with
  | none =>
      simp [hreturn, rawNormalizedRow_eq]
  | some target =>
      simp [hreturn]

private theorem deadRows_primrec :
    Primrec (fun input : MachineAlphabetInput Action =>
      Popping.deadRows input.1 input.2) := by
  have hstack : Primrec (fun input : MachineAlphabetInput Action =>
      List.range input.1.numStackSymbols) :=
    Primrec.list_range.comp
      (numStackSymbols_primrec.comp Primrec.fst)
  have hZRows : Primrec₂ (fun (input : MachineAlphabetInput Action)
      (Z : ℕ) =>
      input.2.map fun action =>
        ((Popping.deadState input.1, action, Z,
          Popping.deadState input.1, [Z]) : InputRow Action)) := by
    apply Primrec₂.mk
    have hrow : Primrec₂ (fun (input :
        MachineAlphabetInput Action × ℕ) (action : Action) =>
        ((Popping.deadState input.1.1, action, input.2,
          Popping.deadState input.1.1, [input.2]) : InputRow Action)) := by
      apply Primrec₂.mk
      exact Primrec.pair
        (numStates_primrec.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair Primrec.snd
          (Primrec.pair (Primrec.snd.comp Primrec.fst)
            (Primrec.pair
              (numStates_primrec.comp
                (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
              (Primrec.list_cons.comp
                (Primrec.snd.comp Primrec.fst) (Primrec.const [])))))
    exact Primrec.list_map
      (Primrec.snd.comp Primrec.fst) hrow
  unfold Popping.deadRows
  exact Primrec.list_flatMap hstack hZRows

private def rawPoppingCompleteMachine
    (input : MachineAlphabetInput Action) : EncodedDPDA Action :=
  (input.1.numStates,
    input.1.numStackSymbols - 1,
    input.1.initialIndex % input.1.numStates,
    input.1.startIndex % input.1.numStackSymbols,
    [],
    rawNormalizedInputRows input ++ Popping.deadRows input.1 input.2,
    rawPoppingRows input.1)

private theorem rawPoppingCompleteMachine_primrec :
    Primrec (rawPoppingCompleteMachine (Action := Action)) := by
  have hstates : Primrec (fun input : MachineAlphabetInput Action =>
      input.1.numStates) := numStates_primrec.comp Primrec.fst
  have hstack : Primrec (fun input : MachineAlphabetInput Action =>
      input.1.numStackSymbols) :=
    numStackSymbols_primrec.comp Primrec.fst
  have hinitial : Primrec (fun input : MachineAlphabetInput Action =>
      input.1.initialIndex % input.1.numStates) :=
    Primrec.nat_mod.comp (initialIndex_primrec.comp Primrec.fst) hstates
  have hstart : Primrec (fun input : MachineAlphabetInput Action =>
      input.1.startIndex % input.1.numStackSymbols) :=
    Primrec.nat_mod.comp (startIndex_primrec.comp Primrec.fst) hstack
  have hinputRows : Primrec (fun input : MachineAlphabetInput Action =>
      rawNormalizedInputRows input ++
        Popping.deadRows input.1 input.2) :=
    Primrec.list_append.comp rawNormalizedInputRows_primrec deadRows_primrec
  unfold rawPoppingCompleteMachine
  exact Primrec.pair hstates
    (Primrec.pair
      (Primrec.nat_sub.comp hstack (Primrec.const 1))
      (Primrec.pair hinitial
        (Primrec.pair hstart
          (Primrec.pair (Primrec.const [])
            (Primrec.pair hinputRows
              (rawPoppingRows_primrec.comp Primrec.fst))))))

private theorem rawPoppingCompleteMachine_eq
    (input : MachineAlphabetInput Action) :
    rawPoppingCompleteMachine input =
      poppingCompleteMachine input.1 input.2 := by
  unfold rawPoppingCompleteMachine poppingCompleteMachine
  rw [rawNormalizedInputRows_eq, rawPoppingRows_eq]

private theorem poppingCompleteMachine_primrec :
    Primrec (fun input : MachineAlphabetInput Action =>
      poppingCompleteMachine input.1 input.2) := by
  apply (rawPoppingCompleteMachine_primrec (Action := Action)).of_eq
  intro input
  exact rawPoppingCompleteMachine_eq input

private theorem poppingCompleteMachine_computable :
    Computable (fun input : MachineAlphabetInput Action =>
      poppingCompleteMachine input.1 input.2) :=
  poppingCompleteMachine_primrec.to_comp

private theorem epsilonEvaluator_selected_eq
    (machine : EncodedDPDA Action) (q Z : ℕ) :
    epsilonStepEvaluator (Action := Action) (machine, q, Z) =
      selectedEpsilon? machine q Z := by
  exact selectedEpsilonEvaluator_eq (Action := Action) (machine, q, Z)

private theorem inputEvaluator_selected_eq
    (machine : EncodedDPDA Action) (q : ℕ) (action : Action) (Z : ℕ) :
    deterministicInputStepEvaluator (Action := Action)
        (machine, q, action, Z) =
      selectedInput? machine q action Z := by
  exact selectedInputEvaluator_eq (Action := Action)
    (machine, q, action, Z)

private theorem selectedEpsilonOfCode_eq
    (input : CodedEpsilonQuery) :
    selectedEpsilonOfCode (Action := Action) input =
      selectedEpsilon? (machineOfCode (Action := Action) input.1)
        input.2.1 input.2.2 := by
  unfold selectedEpsilonOfCode
  exact epsilonEvaluator_selected_eq (Action := Action)
    (machineOfCode (Action := Action) input.1) input.2.1 input.2.2

private theorem selectedInputOfCode_eq
    (input : CodedInputQuery Action) :
    selectedInputOfCode (Action := Action) input =
      selectedInput? (machineOfCode (Action := Action) input.1)
        input.2.1 input.2.2.1 input.2.2.2 := by
  unfold selectedInputOfCode
  exact inputEvaluator_selected_eq (Action := Action)
    (machineOfCode (Action := Action) input.1)
    input.2.1 input.2.2.1 input.2.2.2

private theorem codedStartRows_eq (input : CodedPairInput Action) :
    codedStartRows (Action := Action) input =
      Endmarked.startRows
        (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2 := by
  simp [codedStartRows, codedLeftStartRow, codedRightStartRow,
    codedLeftEndRow, codedRightEndRow, codedLeftEndTarget,
    codedRightEndTarget, codedLeftInitialIsFinal,
    codedRightInitialIsFinal, codedLeftIsFinalIndex,
    codedRightIsFinalIndex, codedLeftPending, codedRightPending,
    codedLeftStack, codedRightStack, codedAcceptState,
    codedRejectState, codedRightPendingBase, Endmarked.startRows,
    Endmarked.isFinalIndex, Endmarked.acceptState,
    Endmarked.rejectState, normalizedFinalIndices]

private theorem codedDrainRows_eq (input : CodedPairInput Action) :
    codedDrainRows (Action := Action) input =
      Endmarked.drainRows
        (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2 := by
  rfl

private theorem codedLeftEpsilonRows_eq
    (input : CodedPairInput Action) :
    codedLeftEpsilonRows (Action := Action) input =
      Endmarked.leftEpsilonRows
        (machineOfCode (Action := Action) input.1) input.2.2 := by
  simp [codedLeftEpsilonRows, codedEmbeddedEpsilonRows,
    codedEpsilonRowsAtPending, codedEpsilonRowsAtState,
    codedEmbeddedEpsilonRow?, codedSelectedEpsilon?,
    codedLeftSelectedEpsilon?, selectedEpsilonOfCode_eq,
    codedSideNumStates, codedSideNumStackSymbols,
    codedSidePending, codedSideStack, codedLeftPending,
    codedLeftStack, Endmarked.leftEpsilonRows,
    Endmarked.embeddedEpsilonRows]

private theorem codedRightEpsilonRows_eq
    (input : CodedPairInput Action) :
    codedRightEpsilonRows (Action := Action) input =
      Endmarked.rightEpsilonRows
        (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2 := by
  simp [codedRightEpsilonRows, codedEmbeddedEpsilonRows,
    codedEpsilonRowsAtPending, codedEpsilonRowsAtState,
    codedEmbeddedEpsilonRow?, codedSelectedEpsilon?,
    codedRightSelectedEpsilon?, selectedEpsilonOfCode_eq,
    codedSideNumStates, codedSideNumStackSymbols,
    codedSidePending, codedSideStack, codedRightPending,
    codedRightStack, Endmarked.rightEpsilonRows,
    Endmarked.embeddedEpsilonRows]

private theorem bif_decide_eq_ite
    (p : Prop) [Decidable p] {T : Type} (ifTrue ifFalse : T) :
    (bif decide p then ifTrue else ifFalse) =
      if p then ifTrue else ifFalse := by
  by_cases hp : p <;> simp [hp]

private theorem list_map_eta {A B : Type} (f : A → B) (items : List A) :
    List.map (fun item => f item) items = List.map f items := rfl

private theorem codedLeftInputRows_eq
    (input : CodedPairInput Action) :
    codedLeftInputRows (Action := Action) input =
      Endmarked.leftInputRows
        (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2 := by
  simp [codedLeftInputRows, codedEmbeddedInputRows,
    codedInputRowsAtPending, codedInputRowsAtState,
    codedEmbeddedInputRowsAtHead, codedSelectedInput?,
    codedLeftSelectedInput?, selectedInputOfCode_eq,
    codedInputRowsForOutput, codedInputRowForNext,
    codedInputSourcePending, codedInputSourceTop,
    codedInputNextTarget, codedInputTarget, codedInputTargetSome,
    codedInputTargetNone, codedFinishState, codedSideIsFinal,
    codedIsFinalIndex, codedLeftIsFinalIndex,
    codedInputOutputReplacement, codedSideReplacement,
    codedSidePending, codedSideStack,
    codedSideNumStates, codedSideNumStackSymbols,
    codedLeftPending, codedLeftStack, codedAcceptState,
    codedRejectState, codedRightPendingBase,
    Endmarked.leftInputRows, Endmarked.embeddedInputRows,
    Endmarked.isFinalIndex, Endmarked.acceptState,
    Endmarked.rejectState, normalizedFinalIndices,
    bif_decide_eq_ite, list_map_eta]
  apply congrArg (fun f => List.flatMap f input.2.2)
  funext pending
  apply congrArg (fun f =>
    List.flatMap f (List.range
      (machineOfCode (Action := Action) input.1).numStates))
  funext q
  apply congrArg (fun f =>
    List.flatMap f (List.range
      (machineOfCode (Action := Action) input.1).numStackSymbols))
  funext Z
  cases hstep : selectedInput?
      (machineOfCode (Action := Action) input.1) q pending Z with
  | none => simp
  | some output =>
      simp only
      apply congrArg (fun f => List.map f (endmarkedAlphabet input.2.2))
      funext next
      cases next with
      | some action => rfl
      | none =>
          by_cases hfinal : ∃ a ∈
              (machineOfCode (Action := Action) input.1).finalIndices,
              a % (machineOfCode (Action := Action) input.1).numStates =
                output.1 % (machineOfCode (Action := Action) input.1).numStates
          · simp [hfinal]
          · simp [hfinal]

private theorem codedRightInputRows_eq
    (input : CodedPairInput Action) :
    codedRightInputRows (Action := Action) input =
      Endmarked.rightInputRows
        (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2 := by
  simp [codedRightInputRows, codedEmbeddedInputRows,
    codedInputRowsAtPending, codedInputRowsAtState,
    codedEmbeddedInputRowsAtHead, codedSelectedInput?,
    codedRightSelectedInput?, selectedInputOfCode_eq,
    codedInputRowsForOutput, codedInputRowForNext,
    codedInputSourcePending, codedInputSourceTop,
    codedInputNextTarget, codedInputTarget, codedInputTargetSome,
    codedInputTargetNone, codedFinishState, codedSideIsFinal,
    codedIsFinalIndex, codedRightIsFinalIndex,
    codedInputOutputReplacement, codedSideReplacement,
    codedSidePending, codedSideStack,
    codedSideNumStates, codedSideNumStackSymbols,
    codedRightPending, codedRightStack, codedAcceptState,
    codedRejectState, codedRightPendingBase,
    Endmarked.rightInputRows, Endmarked.embeddedInputRows,
    Endmarked.isFinalIndex, Endmarked.acceptState,
    Endmarked.rejectState, normalizedFinalIndices,
    bif_decide_eq_ite, list_map_eta]
  apply congrArg (fun f => List.flatMap f input.2.2)
  funext pending
  apply congrArg (fun f =>
    List.flatMap f (List.range
      (machineOfCode (Action := Action) input.2.1).numStates))
  funext q
  apply congrArg (fun f =>
    List.flatMap f (List.range
      (machineOfCode (Action := Action) input.2.1).numStackSymbols))
  funext Z
  cases hstep : selectedInput?
      (machineOfCode (Action := Action) input.2.1) q pending Z with
  | none => simp
  | some output =>
      simp only
      apply congrArg (fun f => List.map f (endmarkedAlphabet input.2.2))
      funext next
      cases next with
      | some action => rfl
      | none =>
          by_cases hfinal : ∃ a ∈
              (machineOfCode (Action := Action) input.2.1).finalIndices,
              a % (machineOfCode (Action := Action) input.2.1).numStates =
                output.1 %
                  (machineOfCode (Action := Action) input.2.1).numStates
          · simp [hfinal]
          · simp [hfinal]

private theorem codedEndmarkedPairMachine_eq
    (input : CodedPairInput Action) :
    codedEndmarkedPairMachine (Action := Action) input =
      endmarkedPairMachine
        (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2 := by
  unfold codedEndmarkedPairMachine endmarkedPairMachine
  rw [codedStartRows_eq, codedLeftInputRows_eq, codedRightInputRows_eq,
    codedLeftEpsilonRows_eq, codedRightEpsilonRows_eq, codedDrainRows_eq]
  simp [codedStateCount, codedRejectState, codedAcceptState,
    codedRightPendingBase, Endmarked.stateCount, Endmarked.rejectState,
    Endmarked.acceptState]

private theorem codedPairNormalizationData_primrec :
    Primrec (fun input : CodedPairInput Action =>
      pairNormalizationData (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2) := by
  have hendmarked : Primrec (fun input : CodedPairInput Action =>
      endmarkedPairMachine (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2) :=
    (codedEndmarkedPairMachine_primrec (Action := Action)).of_eq
      (codedEndmarkedPairMachine_eq (Action := Action))
  have halphabet : Primrec (fun input : CodedPairInput Action =>
      endmarkedAlphabet input.2.2) :=
    endmarkedAlphabet_primrec.comp (codedAlphabet_primrec (Action := Action))
  have hmachine : Primrec (fun input : CodedPairInput Action =>
      poppingCompleteMachine
        (endmarkedPairMachine (machineOfCode (Action := Action) input.1)
          (machineOfCode (Action := Action) input.2.1) input.2.2)
        (endmarkedAlphabet input.2.2)) :=
    poppingCompleteMachine_primrec.comp
      (Primrec.pair hendmarked halphabet)
  have hcode : Primrec (fun input : CodedPairInput Action =>
      ((poppingCompleteMachine
          (endmarkedPairMachine (machineOfCode (Action := Action) input.1)
            (machineOfCode (Action := Action) input.2.1) input.2.2)
          (endmarkedAlphabet input.2.2),
        endmarkedAlphabet input.2.2,
        (Endmarked.leftStart, [Endmarked.bottom]),
        (Endmarked.rightStart, [Endmarked.bottom])) :
        PairNormalizationDataCode Action)) := by
    exact Primrec.pair hmachine
      (Primrec.pair halphabet
        (Primrec.pair
          (Primrec.const
            (Endmarked.leftStart, [Endmarked.bottom]))
          (Primrec.const
            (Endmarked.rightStart, [Endmarked.bottom]))))
  have hdata := (Primrec.of_equiv_symm
    (e := pairNormalizationDataEquiv Action)).comp hcode
  apply hdata.of_eq
  intro input
  rfl

private theorem codedPairNormalizationData_computable :
    Computable (fun input : CodedPairInput Action =>
      pairNormalizationData (machineOfCode (Action := Action) input.1)
        (machineOfCode (Action := Action) input.2.1) input.2.2) :=
  (codedPairNormalizationData_primrec (Action := Action)).to_comp

/-- Pair normalization is a total computable transformation of the two raw
encoded DPDAs and the explicit finite action alphabet. -/
public theorem pairNormalizationData_computable :
    Computable (fun input :
      EncodedDPDA Action × EncodedDPDA Action × List Action =>
      pairNormalizationData input.1 input.2.1 input.2.2) := by
  have hcodes : Primrec (fun input :
      EncodedDPDA Action × EncodedDPDA Action × List Action =>
      (Encodable.encode input.1,
        Encodable.encode input.2.1, input.2.2)) :=
    Primrec.pair (Primrec.encode.comp Primrec.fst)
      (Primrec.pair
        (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  apply (codedPairNormalizationData_computable.comp hcodes.to_comp).of_eq
  intro input
  simp

private theorem pairNormalizationData_tracePair_computable :
    Computable (fun data : PairNormalizationData Action => data.tracePair) := by
  have hcode : Primrec (pairNormalizationDataEquiv Action) :=
    Primrec.of_equiv
  have hmachine : Computable (fun data : PairNormalizationData Action =>
      data.machine) :=
    (Primrec.fst.comp hcode).to_comp
  have hleft : Computable (fun data : PairNormalizationData Action =>
      data.leftInitial) :=
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp hcode).to_comp
  have hright : Computable (fun data : PairNormalizationData Action =>
      data.rightInitial) :=
    ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp hcode).to_comp
  have hgrammar : Computable (fun data : PairNormalizationData Action =>
      DPDAToFirstOrder.grammar data.machine) :=
    (DPDAToFirstOrder.grammar_computable (Action := Option Action)).comp
      hmachine
  have hleftTerm : Computable (fun data : PairNormalizationData Action =>
      DPDAToFirstOrder.configurationTerm data.machine
        data.leftInitial.1 data.leftInitial.2) :=
    (DPDAToFirstOrder.configurationTerm_computable₂
      (Action := Option Action)).comp hmachine hleft
  have hrightTerm : Computable (fun data : PairNormalizationData Action =>
      DPDAToFirstOrder.configurationTerm data.machine
        data.rightInitial.1 data.rightInitial.2) :=
    (DPDAToFirstOrder.configurationTerm_computable₂
      (Action := Option Action)).comp hmachine hright
  have htrace : Computable (fun data : PairNormalizationData Action =>
      ((DPDAToFirstOrder.grammar data.machine,
        DPDAToFirstOrder.configurationTerm data.machine
          data.leftInitial.1 data.leftInitial.2,
        DPDAToFirstOrder.configurationTerm data.machine
          data.rightInitial.1 data.rightInitial.2) :
        EncodedFirstOrderGrammar.TracePair (Option Action))) := by
    exact Computable.pair hgrammar (Computable.pair hleftTerm hrightTerm)
  apply htrace.of_eq
  intro data
  rfl

/-- Paired DPDA normalization followed by the first-order trace translation is
a total computable transformation of the two raw automata and their explicit
finite action alphabet. -/
public theorem pairTraceData_computable :
    Computable (fun input :
      EncodedDPDA Action × EncodedDPDA Action × List Action =>
      pairTraceData input.1 input.2.1 input.2.2) := by
  apply ((pairNormalizationData_tracePair_computable (Action := Action)).comp
    (pairNormalizationData_computable (Action := Action))).of_eq
  intro input
  rfl
end
end DPDANormalization

end DCFEquivalence
