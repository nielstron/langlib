module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAToFirstOrderComputability
public import Langlib.Classes.DeterministicContextFree.Decidability.Universality
public import Mathlib.Computability.Primrec.List

@[expose]
public section

/-!
# Effective DPDA preprocessing for language equivalence

This file supplies the preprocessing boundary deliberately left open in
`DPDAToFirstOrder`.  There are two independent finite transformations.

* `endmarkedPairMachine` puts two final-state encoded DPDAs into one machine.
  Input is delayed by one letter, so the fresh right endmarker is consumed at
  the same time as the last original transition.  Consequently a divergent
  epsilon phase after the original input has been exhausted causes no problem:
  the validity promise already makes the target state's finality the answer.
* `poppingCompleteMachine` computes the finite return summary of every
  control/stack head.  A returnable head becomes one epsilon pop; a
  nonreturnable head is unfolded to its first stable head, and divergent heads
  are redirected to a permanent dead state.  Missing stable transitions are
  filled by the same dead state.

The fresh marker changes the action alphabet from `Action` to `Option Action`.
This is why the result below cannot inhabit the older
`DPDAToFirstOrder.NormalizationResult source`, whose source and target action
types are definitionally the same.
-/

open PDA
open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDANormalization

variable {Action : Type}

/-! ## Small raw-code utilities -/

@[expose] public def normalizedFinalIndices
    (machine : EncodedDPDA Action) : List ℕ :=
  machine.finalIndices.map fun q => q % machine.numStates

@[expose] public def selectedEpsilon? (machine : EncodedDPDA Action)
    (q Z : ℕ) : Option (ℕ × List ℕ) :=
  (machine.epsilonRows.find? fun row => decide
      (row.1 % machine.numStates = q % machine.numStates ∧
        row.2.1 % machine.numStackSymbols = Z % machine.numStackSymbols)).map
    fun row =>
      (row.2.2.1 % machine.numStates,
        row.2.2.2.map fun Y => Y % machine.numStackSymbols)

@[expose] public def selectedInput? [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) (action : Action) (Z : ℕ) :
    Option (ℕ × List ℕ) :=
  if (selectedEpsilon? machine q Z).isSome then none
  else
    (machine.inputRows.find? fun row => decide
        (row.1 % machine.numStates = q % machine.numStates ∧
          row.2.1 = action ∧
          row.2.2.1 % machine.numStackSymbols = Z % machine.numStackSymbols)).map
      fun row =>
        (row.2.2.2.1 % machine.numStates,
          row.2.2.2.2.map fun Y => Y % machine.numStackSymbols)

public theorem selectedEpsilon?_eq_epsilonStep? [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z : ℕ) :
    selectedEpsilon? machine q Z =
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z := by
  unfold selectedEpsilon? DPDAToFirstOrder.Machine.epsilonStep?
    EncodedDPDA.epsilonLookup EncodedDPDA.state EncodedDPDA.stackSymbol
    EncodedDPDA.replacement
  simp only [Option.map_map, Function.comp_def]
  congr 1
  · funext row
    simp [EncodedDPDA.stackSymbol]

public theorem selectedEpsilon?_normalized
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (replacement : List ℕ)
    (hstep : selectedEpsilon? machine q Z = some (target, replacement)) :
    target % machine.numStates = target ∧
      replacement.map (fun Y => Y % machine.numStackSymbols) = replacement := by
  unfold selectedEpsilon? at hstep
  obtain ⟨row, _, hout⟩ := Option.map_eq_some_iff.mp hstep
  have htarget := congrArg Prod.fst hout
  have hreplacement := congrArg Prod.snd hout
  constructor
  · calc
      target % machine.numStates =
          (row.2.2.1 % machine.numStates) % machine.numStates := by
            exact congrArg (fun x => x % machine.numStates) htarget.symm
      _ = row.2.2.1 % machine.numStates := Nat.mod_mod _ _
      _ = target := htarget
  · calc
      replacement.map (fun Y => Y % machine.numStackSymbols) =
          (row.2.2.2.map fun Y => Y % machine.numStackSymbols).map
            (fun Y => Y % machine.numStackSymbols) := by
              exact congrArg (List.map fun Y => Y % machine.numStackSymbols)
                hreplacement.symm
      _ = row.2.2.2.map (fun Y => Y % machine.numStackSymbols) := by
        simp [List.map_map, Function.comp_def, Nat.mod_mod]
      _ = replacement := hreplacement

public theorem selectedEpsilon?_normalized_key
    (machine : EncodedDPDA Action) (q Z : ℕ) :
    selectedEpsilon? machine (q % machine.numStates)
        (Z % machine.numStackSymbols) =
      selectedEpsilon? machine q Z := by
  unfold selectedEpsilon?
  simp [Nat.mod_mod]

public theorem selectedInput?_eq_inputStep? [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) (action : Action) (Z : ℕ) :
    selectedInput? machine q action Z =
      if (DPDAToFirstOrder.Machine.epsilonStep? machine q Z).isSome then none
      else DPDAToFirstOrder.Machine.inputStep? machine q action Z := by
  rw [← selectedEpsilon?_eq_epsilonStep?]
  unfold selectedInput? DPDAToFirstOrder.Machine.inputStep?
    EncodedDPDA.inputLookup EncodedDPDA.state EncodedDPDA.stackSymbol
    EncodedDPDA.replacement
  split <;> rename_i h
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Option.map_map,
      Function.comp_def]
    congr 1
    · funext row
      simp [EncodedDPDA.stackSymbol]

public theorem selectedInput?_normalized [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) (action : Action) (Z target : ℕ)
    (replacement : List ℕ)
    (hstep : selectedInput? machine q action Z = some (target, replacement)) :
    target % machine.numStates = target ∧
      replacement.map (fun Y => Y % machine.numStackSymbols) = replacement := by
  unfold selectedInput? at hstep
  split at hstep
  · simp at hstep
  · obtain ⟨row, _, hout⟩ := Option.map_eq_some_iff.mp hstep
    have htarget := congrArg Prod.fst hout
    have hreplacement := congrArg Prod.snd hout
    constructor
    · calc
        target % machine.numStates =
            (row.2.2.2.1 % machine.numStates) % machine.numStates := by
              exact congrArg (fun x => x % machine.numStates) htarget.symm
        _ = row.2.2.2.1 % machine.numStates := Nat.mod_mod _ _
        _ = target := htarget
    · calc
        replacement.map (fun Y => Y % machine.numStackSymbols) =
            (row.2.2.2.2.map fun Y => Y % machine.numStackSymbols).map
              (fun Y => Y % machine.numStackSymbols) := by
                exact congrArg (List.map fun Y => Y % machine.numStackSymbols)
                  hreplacement.symm
        _ = row.2.2.2.2.map (fun Y => Y % machine.numStackSymbols) := by
          simp [List.map_map, Function.comp_def, Nat.mod_mod]
        _ = replacement := hreplacement

public theorem selectedInput?_normalized_key [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) (action : Action) (Z : ℕ) :
    selectedInput? machine (q % machine.numStates) action
        (Z % machine.numStackSymbols) =
      selectedInput? machine q action Z := by
  unfold selectedInput?
  rw [selectedEpsilon?_normalized_key]
  simp [Nat.mod_mod]

private theorem state_initial_mod [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    machine.state (machine.initialIndex % machine.numStates) =
      machine.toDPDA.initial_state := by
  simp [EncodedDPDA.toDPDA, EncodedDPDA.state, Nat.mod_mod]

private theorem replacement_start_mod [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    machine.replacement
        [machine.startIndex % machine.numStackSymbols] =
      [machine.toDPDA.start_symbol] := by
  simp [EncodedDPDA.toDPDA, EncodedDPDA.replacement,
    EncodedDPDA.stackSymbol, Nat.mod_mod]

/-! ## A shared, delayed-endmarker machine

The explicit alphabet list is part of the algorithmic input.  Its public
correctness theorem assumes it is duplicate-free and exhaustive.
-/

@[expose] public def endmarkedAlphabet
    (alphabet : List Action) : List (Option Action) :=
  none :: alphabet.map some

public theorem mem_endmarkedAlphabet_of_exhaustive
    {alphabet : List Action} (haustive : ∀ action, action ∈ alphabet)
    (action : Option Action) : action ∈ endmarkedAlphabet alphabet := by
  cases action with
  | none => simp [endmarkedAlphabet]
  | some action => simp [endmarkedAlphabet, haustive action]

public theorem endmarkedAlphabet_nodup [DecidableEq Action]
    {alphabet : List Action} (hnodup : alphabet.Nodup) :
    (endmarkedAlphabet alphabet).Nodup := by
  have hmapped : (alphabet.map some).Nodup :=
    List.Nodup.map (Option.some_injective Action) hnodup
  simpa [endmarkedAlphabet] using hmapped

/-! State layout of the shared endmarker machine.

`0,1` are the two buffering starts.  They are followed by the left and right
pending-letter products, then the accepting drain and rejecting sink. -/
namespace Endmarked

@[expose] public def leftStart : ℕ := 0
@[expose] public def rightStart : ℕ := 1

@[expose] public def leftPendingBase : ℕ := 2

@[expose] public def indexOf [DecidableEq Action]
    (action : Action) (alphabet : List Action) : ℕ :=
  alphabet.findIdx fun head => decide (head = action)

public theorem getElem?_indexOf [DecidableEq Action]
    (action : Action) : ∀ {alphabet : List Action},
      action ∈ alphabet → alphabet[indexOf action alphabet]? = some action := by
  intro alphabet hmem
  induction alphabet with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases hhead : head = action
      · subst head
        simp [indexOf, List.findIdx_cons]
      · have htail : action ∈ tail := by
          simp only [List.mem_cons] at hmem
          rcases hmem with hsame | htail
          · exact (hhead hsame.symm).elim
          · exact htail
        calc
          (head :: tail)[indexOf action (head :: tail)]? =
              tail[indexOf action tail]? := by
            simp [indexOf, List.findIdx_cons, List.getElem?_cons_succ,
              hhead]
          _ = some action := ih htail

public theorem indexOf_lt_length [DecidableEq Action]
    {action : Action} {alphabet : List Action} (hmem : action ∈ alphabet) :
    indexOf action alphabet < alphabet.length := by
  have hlookup := getElem?_indexOf action hmem
  exact (List.getElem?_eq_some_iff.mp hlookup).1

public theorem indexOf_injective_on_mem [DecidableEq Action]
    {left right : Action} {alphabet : List Action}
    (hleft : left ∈ alphabet) (hright : right ∈ alphabet)
    (heq : indexOf left alphabet = indexOf right alphabet) :
    left = right := by
  have hl := getElem?_indexOf left hleft
  have hr := getElem?_indexOf right hright
  rw [heq] at hl
  exact Option.some.inj (hl.symm.trans hr)

@[expose] public def rightPendingBase (left : EncodedDPDA Action)
    (alphabet : List Action) : ℕ :=
  leftPendingBase + left.numStates * alphabet.length

@[expose] public def pendingIndex [DecidableEq Action] (alphabet : List Action)
    (base q : ℕ) (action : Action) : ℕ :=
  base + q * alphabet.length + indexOf action alphabet

@[expose] public def leftPending [DecidableEq Action]
    (left : EncodedDPDA Action)
    (alphabet : List Action) (q : ℕ) (action : Action) : ℕ :=
  pendingIndex alphabet leftPendingBase (q % left.numStates) action

@[expose] public def rightPending [DecidableEq Action]
    (left right : EncodedDPDA Action)
    (alphabet : List Action) (q : ℕ) (action : Action) : ℕ :=
  pendingIndex alphabet (rightPendingBase left alphabet)
    (q % right.numStates) action

public theorem leftPending_lt_rightPendingBase [DecidableEq Action]
    (left : EncodedDPDA Action) {alphabet : List Action}
    {q : ℕ} {action : Action} (haction : action ∈ alphabet) :
    leftPending left alphabet q action < rightPendingBase left alphabet := by
  have hq := Nat.mod_lt q left.numStates_pos
  have hi := indexOf_lt_length haction
  have hwithin : (q % left.numStates) * alphabet.length +
      indexOf action alphabet <
        (q % left.numStates + 1) * alphabet.length := by
    rw [Nat.add_mul]
    simpa using Nat.add_lt_add_left hi
      ((q % left.numStates) * alphabet.length)
  have hle : (q % left.numStates + 1) * alphabet.length ≤
      left.numStates * alphabet.length :=
    Nat.mul_le_mul_right alphabet.length (Nat.succ_le_of_lt hq)
  unfold leftPending pendingIndex rightPendingBase leftPendingBase
  omega

public theorem leftPending_injective [DecidableEq Action]
    (left : EncodedDPDA Action) {alphabet : List Action}
    {q₁ q₂ : ℕ} {action₁ action₂ : Action}
    (hq₁ : q₁ < left.numStates) (hq₂ : q₂ < left.numStates)
    (ha₁ : action₁ ∈ alphabet) (ha₂ : action₂ ∈ alphabet)
    (heq : leftPending left alphabet q₁ action₁ =
      leftPending left alphabet q₂ action₂) :
    q₁ = q₂ ∧ action₁ = action₂ := by
  have hlen : 0 < alphabet.length := by
    apply List.length_pos_of_ne_nil
    intro hempty
    subst alphabet
    simp at ha₁
  have hi₁ := indexOf_lt_length ha₁
  have hi₂ := indexOf_lt_length ha₂
  have hcore : q₁ * alphabet.length + indexOf action₁ alphabet =
      q₂ * alphabet.length + indexOf action₂ alphabet := by
    have heq' := heq
    simp only [leftPending, pendingIndex, leftPendingBase,
      Nat.mod_eq_of_lt hq₁, Nat.mod_eq_of_lt hq₂] at heq'
    have heq'' : 2 + (q₁ * alphabet.length + indexOf action₁ alphabet) =
        2 + (q₂ * alphabet.length + indexOf action₂ alphabet) := by
      simpa [Nat.add_assoc] using heq'
    exact Nat.add_left_cancel heq''
  have hq : q₁ = q₂ := by
    have hdiv := congrArg (fun n => n / alphabet.length) hcore
    change (q₁ * alphabet.length + indexOf action₁ alphabet) /
        alphabet.length =
      (q₂ * alphabet.length + indexOf action₂ alphabet) /
        alphabet.length at hdiv
    have hdiv₁ :
        (q₁ * alphabet.length + indexOf action₁ alphabet) /
            alphabet.length = q₁ := by
      rw [Nat.mul_comm q₁ alphabet.length, Nat.mul_add_div hlen,
        Nat.div_eq_of_lt hi₁, Nat.add_zero]
    have hdiv₂ :
        (q₂ * alphabet.length + indexOf action₂ alphabet) /
            alphabet.length = q₂ := by
      rw [Nat.mul_comm q₂ alphabet.length, Nat.mul_add_div hlen,
        Nat.div_eq_of_lt hi₂, Nat.add_zero]
    rw [hdiv₁, hdiv₂] at hdiv
    exact hdiv
  subst q₂
  have hi : indexOf action₁ alphabet = indexOf action₂ alphabet :=
    Nat.add_left_cancel hcore
  exact ⟨rfl, indexOf_injective_on_mem ha₁ ha₂ hi⟩

public theorem rightPending_injective [DecidableEq Action]
    (left right : EncodedDPDA Action) {alphabet : List Action}
    {q₁ q₂ : ℕ} {action₁ action₂ : Action}
    (hq₁ : q₁ < right.numStates) (hq₂ : q₂ < right.numStates)
    (ha₁ : action₁ ∈ alphabet) (ha₂ : action₂ ∈ alphabet)
    (heq : rightPending left right alphabet q₁ action₁ =
      rightPending left right alphabet q₂ action₂) :
    q₁ = q₂ ∧ action₁ = action₂ := by
  have hlen : 0 < alphabet.length := by
    apply List.length_pos_of_ne_nil
    intro hempty
    subst alphabet
    simp at ha₁
  have hi₁ := indexOf_lt_length ha₁
  have hi₂ := indexOf_lt_length ha₂
  have hcore : q₁ * alphabet.length + indexOf action₁ alphabet =
      q₂ * alphabet.length + indexOf action₂ alphabet := by
    have heq' := heq
    simp only [rightPending, pendingIndex, Nat.mod_eq_of_lt hq₁,
      Nat.mod_eq_of_lt hq₂] at heq'
    have heq'' : rightPendingBase left alphabet +
          (q₁ * alphabet.length + indexOf action₁ alphabet) =
        rightPendingBase left alphabet +
          (q₂ * alphabet.length + indexOf action₂ alphabet) := by
      simpa [Nat.add_assoc] using heq'
    exact Nat.add_left_cancel heq''
  have hq : q₁ = q₂ := by
    have hdiv := congrArg (fun n => n / alphabet.length) hcore
    change (q₁ * alphabet.length + indexOf action₁ alphabet) /
        alphabet.length =
      (q₂ * alphabet.length + indexOf action₂ alphabet) /
        alphabet.length at hdiv
    have hdiv₁ :
        (q₁ * alphabet.length + indexOf action₁ alphabet) /
            alphabet.length = q₁ := by
      rw [Nat.mul_comm q₁ alphabet.length, Nat.mul_add_div hlen,
        Nat.div_eq_of_lt hi₁, Nat.add_zero]
    have hdiv₂ :
        (q₂ * alphabet.length + indexOf action₂ alphabet) /
            alphabet.length = q₂ := by
      rw [Nat.mul_comm q₂ alphabet.length, Nat.mul_add_div hlen,
        Nat.div_eq_of_lt hi₂, Nat.add_zero]
    rw [hdiv₁, hdiv₂] at hdiv
    exact hdiv
  subst q₂
  have hi : indexOf action₁ alphabet = indexOf action₂ alphabet :=
    Nat.add_left_cancel hcore
  exact ⟨rfl, indexOf_injective_on_mem ha₁ ha₂ hi⟩

@[expose] public def acceptState (left right : EncodedDPDA Action)
    (alphabet : List Action) : ℕ :=
  rightPendingBase left alphabet + right.numStates * alphabet.length

@[expose] public def rejectState (left right : EncodedDPDA Action)
    (alphabet : List Action) : ℕ :=
  acceptState left right alphabet + 1

@[expose] public def stateCount (left right : EncodedDPDA Action)
    (alphabet : List Action) : ℕ :=
  rejectState left right alphabet + 1

@[expose] public def bottom : ℕ := 0

@[expose] public def leftStack (left : EncodedDPDA Action) (Z : ℕ) : ℕ :=
  1 + Z % left.numStackSymbols

@[expose] public def rightStack (left right : EncodedDPDA Action)
    (Z : ℕ) : ℕ :=
  1 + left.numStackSymbols + Z % right.numStackSymbols

@[expose] public def stackCount (left right : EncodedDPDA Action) : ℕ :=
  1 + left.numStackSymbols + right.numStackSymbols

public theorem rightPending_lt_acceptState [DecidableEq Action]
    (left right : EncodedDPDA Action) {alphabet : List Action}
    {q : ℕ} {action : Action} (haction : action ∈ alphabet) :
    rightPending left right alphabet q action <
      acceptState left right alphabet := by
  have hq := Nat.mod_lt q right.numStates_pos
  have hi := indexOf_lt_length haction
  have hwithin : (q % right.numStates) * alphabet.length +
      indexOf action alphabet <
        (q % right.numStates + 1) * alphabet.length := by
    rw [Nat.add_mul]
    simpa using Nat.add_lt_add_left hi
      ((q % right.numStates) * alphabet.length)
  have hle : (q % right.numStates + 1) * alphabet.length ≤
      right.numStates * alphabet.length :=
    Nat.mul_le_mul_right alphabet.length (Nat.succ_le_of_lt hq)
  unfold rightPending pendingIndex acceptState
  omega

public theorem leftPending_lt_stateCount [DecidableEq Action]
    (left right : EncodedDPDA Action) {alphabet : List Action}
    {q : ℕ} {action : Action} (haction : action ∈ alphabet) :
    leftPending left alphabet q action < stateCount left right alphabet := by
  exact (leftPending_lt_rightPendingBase left haction).trans
    (by unfold stateCount rejectState acceptState; omega)

public theorem rightPending_lt_stateCount [DecidableEq Action]
    (left right : EncodedDPDA Action) {alphabet : List Action}
    {q : ℕ} {action : Action} (haction : action ∈ alphabet) :
    rightPending left right alphabet q action <
      stateCount left right alphabet := by
  exact (rightPending_lt_acceptState left right haction).trans
    (by simp [stateCount, rejectState])

public theorem leftStack_injective
    (left : EncodedDPDA Action) {Z₁ Z₂ : ℕ}
    (hZ₁ : Z₁ < left.numStackSymbols)
    (hZ₂ : Z₂ < left.numStackSymbols)
    (heq : leftStack left Z₁ = leftStack left Z₂) : Z₁ = Z₂ := by
  have heq' := heq
  simp only [leftStack, Nat.mod_eq_of_lt hZ₁,
    Nat.mod_eq_of_lt hZ₂] at heq'
  exact Nat.add_left_cancel heq'

public theorem rightStack_injective
    (left right : EncodedDPDA Action) {Z₁ Z₂ : ℕ}
    (hZ₁ : Z₁ < right.numStackSymbols)
    (hZ₂ : Z₂ < right.numStackSymbols)
    (heq : rightStack left right Z₁ = rightStack left right Z₂) :
    Z₁ = Z₂ := by
  have heq' := heq
  simp only [rightStack, Nat.mod_eq_of_lt hZ₁,
    Nat.mod_eq_of_lt hZ₂] at heq'
  have heq'' : (1 + left.numStackSymbols) + Z₁ =
      (1 + left.numStackSymbols) + Z₂ := by
    simpa [Nat.add_assoc] using heq'
  exact Nat.add_left_cancel heq''

public theorem leftPending_ge_base [DecidableEq Action]
    (left : EncodedDPDA Action) (alphabet : List Action)
    (q : ℕ) (action : Action) :
    leftPendingBase ≤ leftPending left alphabet q action := by
  unfold leftPending pendingIndex
  omega

public theorem rightPending_ge_base [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q : ℕ) (action : Action) :
    rightPendingBase left alphabet ≤
      rightPending left right alphabet q action := by
  unfold rightPending pendingIndex
  omega

public theorem acceptState_lt_stateCount
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    acceptState left right alphabet < stateCount left right alphabet := by
  unfold stateCount rejectState
  omega

public theorem rejectState_lt_stateCount
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    rejectState left right alphabet < stateCount left right alphabet := by
  unfold stateCount
  omega

public theorem leftStack_lt_stackCount
    (left right : EncodedDPDA Action) (Z : ℕ) :
    leftStack left Z < stackCount left right := by
  have hZ := Nat.mod_lt Z left.numStackSymbols_pos
  unfold leftStack stackCount
  omega

public theorem rightStack_lt_stackCount
    (left right : EncodedDPDA Action) (Z : ℕ) :
    rightStack left right Z < stackCount left right := by
  have hZ := Nat.mod_lt Z right.numStackSymbols_pos
  unfold rightStack stackCount
  omega

@[expose] public def mapLeftReplacement (left : EncodedDPDA Action)
    (replacement : List ℕ) : List ℕ :=
  replacement.map (leftStack left)

@[expose] public def mapRightReplacement (left right : EncodedDPDA Action)
    (replacement : List ℕ) : List ℕ :=
  replacement.map (rightStack left right)

@[expose] public def isFinalIndex (machine : EncodedDPDA Action) (q : ℕ) : Bool :=
  decide (q % machine.numStates ∈ normalizedFinalIndices machine)

public theorem isFinalIndex_eq_true_iff
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) :
    isFinalIndex machine q = true ↔
      machine.state q ∈ machine.toDPDA.final_states := by
  simp [isFinalIndex, normalizedFinalIndices, EncodedDPDA.toDPDA,
    EncodedDPDA.state]

@[expose] public def startRows [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    List (InputRow (Option Action)) :=
  let leftLetters := alphabet.map fun action =>
    (leftStart, some action, bottom,
      leftPending left alphabet left.initialIndex action,
      [leftStack left left.startIndex, bottom])
  let leftEnd :=
    (leftStart, none, bottom,
      if isFinalIndex left left.initialIndex then
        acceptState left right alphabet
      else rejectState left right alphabet,
      [bottom])
  let rightLetters := alphabet.map fun action =>
    (rightStart, some action, bottom,
      rightPending left right alphabet right.initialIndex action,
      [rightStack left right right.startIndex, bottom])
  let rightEnd :=
    (rightStart, none, bottom,
      if isFinalIndex right right.initialIndex then
        acceptState left right alphabet
      else rejectState left right alphabet,
      [bottom])
  leftLetters ++ [leftEnd] ++ rightLetters ++ [rightEnd]

public theorem startRows_source_lt_leftPendingBase [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    {row : InputRow (Option Action)}
    (hrow : row ∈ startRows left right alphabet) :
    row.1 < leftPendingBase := by
  simp [startRows] at hrow
  rcases hrow with hrow | hrow | hrow | hrow
  · obtain ⟨action, _, rfl⟩ := hrow
    simp [leftStart, leftPendingBase]
  · subst row
    simp [leftStart, leftPendingBase]
  · obtain ⟨action, _, rfl⟩ := hrow
    simp [rightStart, leftPendingBase]
  · subst row
    simp [rightStart, leftPendingBase]

public theorem mem_startRows_iff [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (row : InputRow (Option Action)) :
    row ∈ startRows left right alphabet ↔
      (∃ action ∈ alphabet,
        row = (leftStart, some action, bottom,
          leftPending left alphabet left.initialIndex action,
          [leftStack left left.startIndex, bottom])) ∨
      row = (leftStart, none, bottom,
        if isFinalIndex left left.initialIndex then
          acceptState left right alphabet
        else rejectState left right alphabet,
        [bottom]) ∨
      (∃ action ∈ alphabet,
        row = (rightStart, some action, bottom,
          rightPending left right alphabet right.initialIndex action,
          [rightStack left right right.startIndex, bottom])) ∨
      row = (rightStart, none, bottom,
        if isFinalIndex right right.initialIndex then
          acceptState left right alphabet
        else rejectState left right alphabet,
        [bottom]) := by
  simp [startRows]
  aesop

@[expose] public def embeddedEpsilonRows [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (pendingState : ℕ → Action → ℕ) (stackMap : ℕ → ℕ) :
    List EpsilonRow :=
  alphabet.flatMap fun pending =>
    (List.range source.numStates).flatMap fun q =>
      (List.range source.numStackSymbols).filterMap fun Z =>
        (selectedEpsilon? source q Z).map fun output =>
          (pendingState q pending, stackMap Z,
            pendingState output.1 pending, output.2.map stackMap)

@[expose] public def embeddedInputRows [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (pendingState : ℕ → Action → ℕ) (stackMap : ℕ → ℕ)
    (finishState : ℕ → ℕ) : List (InputRow (Option Action)) :=
  alphabet.flatMap fun pending =>
    (List.range source.numStates).flatMap fun q =>
      (List.range source.numStackSymbols).flatMap fun Z =>
        match selectedInput? source q pending Z with
        | none => []
        | some output =>
            (endmarkedAlphabet alphabet).map fun next =>
              (pendingState q pending, next, stackMap Z,
                match next with
                | some action => pendingState output.1 action
                | none => finishState output.1,
                output.2.map stackMap)

public theorem mem_embeddedEpsilonRows_iff [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (pendingState : ℕ → Action → ℕ) (stackMap : ℕ → ℕ)
    (row : EpsilonRow) :
    row ∈ embeddedEpsilonRows source alphabet pendingState stackMap ↔
      ∃ pending ∈ alphabet, ∃ q < source.numStates,
        ∃ Z < source.numStackSymbols, ∃ target replacement,
          selectedEpsilon? source q Z = some (target, replacement) ∧
          row = (pendingState q pending, stackMap Z,
            pendingState target pending, replacement.map stackMap) := by
  unfold embeddedEpsilonRows
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨pending, hpending, hrow⟩
    rw [List.mem_flatMap] at hrow
    obtain ⟨q, hq, hrow⟩ := hrow
    rw [List.mem_filterMap] at hrow
    obtain ⟨Z, hZ, hrow⟩ := hrow
    cases hstep : selectedEpsilon? source q Z with
    | none => simp [hstep] at hrow
    | some output =>
        rcases output with ⟨target, replacement⟩
        simp [hstep] at hrow
        subst row
        exact ⟨pending, hpending, q, List.mem_range.mp hq,
          Z, List.mem_range.mp hZ, target, replacement, hstep, rfl⟩
  · rintro ⟨pending, hpending, q, hq, Z, hZ, target, replacement,
        hstep, rfl⟩
    refine ⟨pending, hpending, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨q, List.mem_range.mpr hq, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨Z, List.mem_range.mpr hZ, by simp [hstep]⟩

public theorem mem_embeddedInputRows_iff [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (pendingState : ℕ → Action → ℕ) (stackMap : ℕ → ℕ)
    (finishState : ℕ → ℕ) (row : InputRow (Option Action)) :
    row ∈ embeddedInputRows source alphabet pendingState stackMap finishState ↔
      ∃ pending ∈ alphabet, ∃ q < source.numStates,
        ∃ Z < source.numStackSymbols, ∃ target replacement,
          selectedInput? source q pending Z = some (target, replacement) ∧
          ∃ next ∈ endmarkedAlphabet alphabet,
            row = (pendingState q pending, next, stackMap Z,
              match next with
              | some action => pendingState target action
              | none => finishState target,
              replacement.map stackMap) := by
  unfold embeddedInputRows
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨pending, hpending, hrow⟩
    rw [List.mem_flatMap] at hrow
    obtain ⟨q, hq, hrow⟩ := hrow
    rw [List.mem_flatMap] at hrow
    obtain ⟨Z, hZ, hrow⟩ := hrow
    cases hstep : selectedInput? source q pending Z with
    | none => simp [hstep] at hrow
    | some output =>
        rcases output with ⟨target, replacement⟩
        simp only [hstep] at hrow
        obtain ⟨next, hnext, rfl⟩ := List.mem_map.mp hrow
        exact ⟨pending, hpending, q, List.mem_range.mp hq,
          Z, List.mem_range.mp hZ, target, replacement, hstep,
          next, hnext, rfl⟩
  · rintro ⟨pending, hpending, q, hq, Z, hZ, target, replacement,
        hstep, next, hnext, rfl⟩
    refine ⟨pending, hpending, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨q, List.mem_range.mpr hq, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨Z, List.mem_range.mpr hZ, ?_⟩
    simp only [hstep]
    exact List.mem_map.mpr ⟨next, hnext, rfl⟩

@[expose] public def leftEpsilonRows [DecidableEq Action]
    (left : EncodedDPDA Action)
    (alphabet : List Action) : List EpsilonRow :=
  embeddedEpsilonRows left alphabet (leftPending left alphabet)
    (leftStack left)

@[expose] public def rightEpsilonRows [DecidableEq Action]
    (left right : EncodedDPDA Action)
    (alphabet : List Action) : List EpsilonRow :=
  embeddedEpsilonRows right alphabet (rightPending left right alphabet)
    (rightStack left right)

@[expose] public def leftInputRows [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    List (InputRow (Option Action)) :=
  embeddedInputRows left alphabet (leftPending left alphabet)
    (leftStack left) fun q =>
      if isFinalIndex left q then acceptState left right alphabet
      else rejectState left right alphabet

@[expose] public def rightInputRows [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    List (InputRow (Option Action)) :=
  embeddedInputRows right alphabet (rightPending left right alphabet)
    (rightStack left right) fun q =>
      if isFinalIndex right q then acceptState left right alphabet
      else rejectState left right alphabet

@[expose] public def drainRows (left right : EncodedDPDA Action)
    (alphabet : List Action) : List EpsilonRow :=
  (List.range (stackCount left right)).map fun Z =>
    (acceptState left right alphabet, Z,
      acceptState left right alphabet, [])

end Endmarked

/-- One raw machine containing the two delayed simulations. -/
@[expose] public def endmarkedPairMachine [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    EncodedDPDA (Option Action) :=
  (Endmarked.stateCount left right alphabet - 1,
    Endmarked.stackCount left right - 1,
    Endmarked.leftStart,
    Endmarked.bottom,
    [],
    Endmarked.startRows left right alphabet ++
      Endmarked.leftInputRows left right alphabet ++
      Endmarked.rightInputRows left right alphabet,
    Endmarked.leftEpsilonRows left alphabet ++
      Endmarked.rightEpsilonRows left right alphabet ++
      Endmarked.drainRows left right alphabet)

@[simp] public theorem endmarkedPairMachine_numStates [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    (endmarkedPairMachine left right alphabet).numStates =
      Endmarked.stateCount left right alphabet := by
  unfold endmarkedPairMachine EncodedDPDA.numStates
  have hpos : 0 < Endmarked.stateCount left right alphabet := by
    simp [Endmarked.stateCount, Endmarked.rejectState]
  omega

@[simp] public theorem endmarkedPairMachine_numStackSymbols [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    (endmarkedPairMachine left right alphabet).numStackSymbols =
      Endmarked.stackCount left right := by
  unfold endmarkedPairMachine EncodedDPDA.numStackSymbols
  change Endmarked.stackCount left right - 1 + 1 =
    Endmarked.stackCount left right
  have hpos : 0 < Endmarked.stackCount left right := by
    simp [Endmarked.stackCount]
  omega

private theorem find?_eq_some_of_unique
    {A : Type} {list : List A} {predicate : A → Bool} {target : A}
    (hmem : target ∈ list) (hmatch : predicate target = true)
    (hunique : ∀ item ∈ list, predicate item = true → item = target) :
    list.find? predicate = some target := by
  have hexists : ∃ item ∈ list, predicate item = true :=
    ⟨target, hmem, hmatch⟩
  cases hfind : list.find? predicate with
  | none =>
      have := List.find?_eq_none.mp hfind target hmem
      simp [hmatch] at this
  | some item =>
      have hitem := List.mem_of_find?_eq_some hfind
      have himatch := List.find?_some hfind
      rw [hunique item hitem himatch]

private theorem mem_endmarked_epsilonRows_iff [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (row : EpsilonRow) :
    row ∈ (endmarkedPairMachine left right alphabet).epsilonRows ↔
      row ∈ Endmarked.leftEpsilonRows left alphabet ∨
      row ∈ Endmarked.rightEpsilonRows left right alphabet ∨
      row ∈ Endmarked.drainRows left right alphabet := by
  change row ∈ Endmarked.leftEpsilonRows left alphabet ++
      Endmarked.rightEpsilonRows left right alphabet ++
        Endmarked.drainRows left right alphabet ↔ _
  simp

private theorem mem_endmarked_inputRows_iff [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (row : InputRow (Option Action)) :
    row ∈ (endmarkedPairMachine left right alphabet).inputRows ↔
      row ∈ Endmarked.startRows left right alphabet ∨
      row ∈ Endmarked.leftInputRows left right alphabet ∨
      row ∈ Endmarked.rightInputRows left right alphabet := by
  change row ∈ Endmarked.startRows left right alphabet ++
      Endmarked.leftInputRows left right alphabet ++
        Endmarked.rightInputRows left right alphabet ↔ _
  simp

public theorem endmarked_selectedEpsilon?_start_eq_none [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (start top : ℕ) (hstart : start < Endmarked.leftPendingBase) :
    selectedEpsilon? (endmarkedPairMachine left right alphabet) start top =
      none := by
  unfold selectedEpsilon?
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro row hrow hmatch
  simp only [decide_eq_true_eq] at hmatch
  have hstartBound : start < Endmarked.stateCount left right alphabet := by
    have hbase : Endmarked.leftPendingBase <
        Endmarked.stateCount left right alphabet := by
      unfold Endmarked.leftPendingBase Endmarked.stateCount
        Endmarked.rejectState Endmarked.acceptState Endmarked.rightPendingBase
      omega
    exact hstart.trans hbase
  rcases (mem_endmarked_epsilonRows_iff left right alphabet row).mp hrow with
    hleft | hright | hdrain
  · obtain ⟨pending, hpending, q, hq, Z, hZ, target, replacement,
        hstep, rfl⟩ :=
      (Endmarked.mem_embeddedEpsilonRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left) _).mp
        (by simpa [Endmarked.leftEpsilonRows] using hleft)
    have hsourceBound :=
      Endmarked.leftPending_lt_stateCount (q := q) left right hpending
    have hsourceEq : Endmarked.leftPending left alphabet q pending = start := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hsourceBound, Nat.mod_eq_of_lt hstartBound] using
          hmatch.1
    have hbase := Endmarked.leftPending_ge_base left alphabet q pending
    have : Endmarked.leftPendingBase ≤ start := hsourceEq ▸ hbase
    exact (Nat.not_le_of_gt hstart) this
  · obtain ⟨pending, hpending, q, hq, Z, hZ, target, replacement,
        hstep, rfl⟩ :=
      (Endmarked.mem_embeddedEpsilonRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right) _).mp
        (by simpa [Endmarked.rightEpsilonRows] using hright)
    have hsourceBound := Endmarked.rightPending_lt_stateCount
      (q := q) left right hpending
    have hsourceEq :
        Endmarked.rightPending left right alphabet q pending = start := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hsourceBound, Nat.mod_eq_of_lt hstartBound] using
          hmatch.1
    have hbase := Endmarked.rightPending_ge_base
      left right alphabet q pending
    have hrightBase : Endmarked.leftPendingBase ≤
        Endmarked.rightPendingBase left alphabet := by
      unfold Endmarked.rightPendingBase Endmarked.leftPendingBase
      omega
    have : Endmarked.leftPendingBase ≤ start := by
      rw [← hsourceEq]
      exact hrightBase.trans hbase
    exact (Nat.not_le_of_gt hstart) this
  · obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hdrain
    have hsourceBound := Endmarked.acceptState_lt_stateCount
      left right alphabet
    have hnum := endmarkedPairMachine_numStates left right alphabet
    have hsourceMod :
        Endmarked.acceptState left right alphabet %
            (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.acceptState left right alphabet := by
      rw [hnum, Nat.mod_eq_of_lt hsourceBound]
    have hstartMod :
        start % (endmarkedPairMachine left right alphabet).numStates = start := by
      rw [hnum, Nat.mod_eq_of_lt hstartBound]
    have hsourceEq : Endmarked.acceptState left right alphabet = start := by
      have := hmatch.1
      rw [hsourceMod, hstartMod] at this
      exact this
    unfold Endmarked.acceptState Endmarked.rightPendingBase
      Endmarked.leftPendingBase at hsourceEq
    have : Endmarked.leftPendingBase ≤ start := by
      unfold Endmarked.leftPendingBase
      rw [← hsourceEq]
      omega
    exact (Nat.not_le_of_gt hstart) this

public theorem endmarked_selectedEpsilon?_leftStart_eq_none
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) (top : ℕ) :
    selectedEpsilon? (endmarkedPairMachine left right alphabet)
      Endmarked.leftStart top = none := by
  apply endmarked_selectedEpsilon?_start_eq_none
  simp [Endmarked.leftStart, Endmarked.leftPendingBase]

public theorem endmarked_selectedEpsilon?_rightStart_eq_none
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) (top : ℕ) :
    selectedEpsilon? (endmarkedPairMachine left right alphabet)
      Endmarked.rightStart top = none := by
  apply endmarked_selectedEpsilon?_start_eq_none
  simp [Endmarked.rightStart, Endmarked.leftPendingBase]

private theorem endmarked_leftEpsilon_key
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (pending : Action) (hpending : pending ∈ alphabet)
    (row : EpsilonRow)
    (hrow : row ∈ (endmarkedPairMachine left right alphabet).epsilonRows)
    (hmatch :
      row.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.leftPending left alphabet q pending %
            (endmarkedPairMachine left right alphabet).numStates ∧
        row.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Endmarked.leftStack left Z %
            (endmarkedPairMachine left right alphabet).numStackSymbols) :
    ∃ target replacement,
      selectedEpsilon? left q Z = some (target, replacement) ∧
      row =
        (Endmarked.leftPending left alphabet q pending,
          Endmarked.leftStack left Z,
          Endmarked.leftPending left alphabet target pending,
          replacement.map (Endmarked.leftStack left)) := by
  have hqueryState := Endmarked.leftPending_lt_stateCount
    (q := q) left right hpending
  have hqueryTop := Endmarked.leftStack_lt_stackCount left right Z
  rcases (mem_endmarked_epsilonRows_iff left right alphabet row).mp hrow with
    hleft | hright | hdrain
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, hrowEq⟩ :=
      (Endmarked.mem_embeddedEpsilonRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left) row).mp
        (by simpa [Endmarked.leftEpsilonRows] using hleft)
    subst row
    have hrowState := Endmarked.leftPending_lt_stateCount
      (q := sourceState) left right hstored
    have hrowTop := Endmarked.leftStack_lt_stackCount
      left right sourceTop
    have hstateEq :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.leftPending left alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hstateEq' :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.leftPending left alphabet (q % left.numStates) pending := by
      simpa [Endmarked.leftPending, Nat.mod_mod] using hstateEq
    have hkeys := Endmarked.leftPending_injective left hsourceState
      (Nat.mod_lt q left.numStates_pos) hstored hpending hstateEq'
    have htopEq : Endmarked.leftStack left sourceTop =
        Endmarked.leftStack left Z := by
      simpa [endmarkedPairMachine_numStackSymbols,
        Nat.mod_eq_of_lt hrowTop, Nat.mod_eq_of_lt hqueryTop] using hmatch.2
    have htopEq' : Endmarked.leftStack left sourceTop =
        Endmarked.leftStack left (Z % left.numStackSymbols) := by
      simpa [Endmarked.leftStack, Nat.mod_mod] using htopEq
    have hsourceTopEq : sourceTop = Z % left.numStackSymbols :=
      Endmarked.leftStack_injective left hsourceTop
        (Nat.mod_lt Z left.numStackSymbols_pos) htopEq'
    have hstep' : selectedEpsilon? left q Z =
        some (target, replacement) := by
      rw [← selectedEpsilon?_normalized_key left q Z]
      simpa [hkeys.1, hsourceTopEq] using hstep
    refine ⟨target, replacement, hstep', ?_⟩
    rw [hkeys.1, hkeys.2, hsourceTopEq]
    simp [Endmarked.leftPending, Endmarked.leftStack]
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, hrowEq⟩ :=
      (Endmarked.mem_embeddedEpsilonRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right) row).mp
        (by simpa [Endmarked.rightEpsilonRows] using hright)
    subst row
    have hrowState := Endmarked.rightPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.leftPending left alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hleftLt := Endmarked.leftPending_lt_rightPendingBase
      (q := q) left hpending
    have hrightGe := Endmarked.rightPending_ge_base
      left right alphabet sourceState stored
    omega
  · obtain ⟨sourceTop, hsourceTop, hrowEq⟩ := List.mem_map.mp hdrain
    subst row
    have hrowState := Endmarked.acceptState_lt_stateCount
      left right alphabet
    have hstateEq : Endmarked.acceptState left right alphabet =
        Endmarked.leftPending left alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hleftLt := Endmarked.leftPending_lt_rightPendingBase
      (q := q) left hpending
    unfold Endmarked.acceptState at hstateEq
    omega

public theorem endmarked_selectedEpsilon?_leftPending_eq
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (pending : Action) (hpending : pending ∈ alphabet) :
    selectedEpsilon? (endmarkedPairMachine left right alphabet)
        (Endmarked.leftPending left alphabet q pending)
        (Endmarked.leftStack left Z) =
      (selectedEpsilon? left q Z).map fun output =>
        (Endmarked.leftPending left alphabet output.1 pending,
          output.2.map (Endmarked.leftStack left)) := by
  cases hsource : selectedEpsilon? left q Z with
  | none =>
      simp only [Option.map_none]
      apply Option.eq_none_iff_forall_not_mem.mpr
      intro output houtput
      unfold selectedEpsilon? at houtput
      obtain ⟨row, hfind, hout⟩ := Option.map_eq_some_iff.mp houtput
      have hrow := List.mem_of_find?_eq_some hfind
      have hmatch := List.find?_some hfind
      simp only [decide_eq_true_eq] at hmatch
      obtain ⟨target, replacement, hstep, _⟩ :=
        endmarked_leftEpsilon_key left right alphabet q Z pending hpending
          row hrow hmatch
      rw [hsource] at hstep
      simp at hstep
  | some sourceOutput =>
      rcases sourceOutput with ⟨target, replacement⟩
      let targetRow : EpsilonRow :=
        (Endmarked.leftPending left alphabet q pending,
          Endmarked.leftStack left Z,
          Endmarked.leftPending left alphabet target pending,
          replacement.map (Endmarked.leftStack left))
      have hqNorm := Nat.mod_lt q left.numStates_pos
      have hZNorm := Nat.mod_lt Z left.numStackSymbols_pos
      have htargetMem : targetRow ∈
          (endmarkedPairMachine left right alphabet).epsilonRows := by
        rw [mem_endmarked_epsilonRows_iff]
        left
        rw [Endmarked.leftEpsilonRows,
          Endmarked.mem_embeddedEpsilonRows_iff]
        refine ⟨pending, hpending, q % left.numStates, hqNorm,
          Z % left.numStackSymbols, hZNorm, target, replacement, ?_, ?_⟩
        · simpa [selectedEpsilon?_normalized_key] using hsource
        · simp [targetRow, Endmarked.leftPending, Endmarked.leftStack]
      have hqueryState := Endmarked.leftPending_lt_stateCount
        (q := q) left right hpending
      have hqueryTop := Endmarked.leftStack_lt_stackCount left right Z
      have htargetMatch : decide
          (targetRow.1 % (endmarkedPairMachine left right alphabet).numStates =
              Endmarked.leftPending left alphabet q pending %
                (endmarkedPairMachine left right alphabet).numStates ∧
            targetRow.2.1 %
                (endmarkedPairMachine left right alphabet).numStackSymbols =
              Endmarked.leftStack left Z %
                (endmarkedPairMachine left right alphabet).numStackSymbols) =
          true := by
        simp [targetRow, endmarkedPairMachine_numStates,
          endmarkedPairMachine_numStackSymbols,
          Nat.mod_eq_of_lt hqueryState, Nat.mod_eq_of_lt hqueryTop]
      have hfind :
          (endmarkedPairMachine left right alphabet).epsilonRows.find?
              (fun row => decide
                (row.1 % (endmarkedPairMachine left right alphabet).numStates =
                    Endmarked.leftPending left alphabet q pending %
                      (endmarkedPairMachine left right alphabet).numStates ∧
                  row.2.1 %
                      (endmarkedPairMachine left right alphabet).numStackSymbols =
                    Endmarked.leftStack left Z %
                      (endmarkedPairMachine left right alphabet).numStackSymbols)) =
            some targetRow := by
        apply find?_eq_some_of_unique htargetMem htargetMatch
        intro row hrow hmatch
        simp only [decide_eq_true_eq] at hmatch
        obtain ⟨rowTarget, rowReplacement, hrowStep, hrowEq⟩ :=
          endmarked_leftEpsilon_key left right alphabet q Z pending hpending
            row hrow hmatch
        have houtEq : (rowTarget, rowReplacement) =
            (target, replacement) := Option.some.inj (hrowStep.symm.trans hsource)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj houtEq
        exact hrowEq
      unfold selectedEpsilon?
      rw [hfind]
      simp [targetRow, endmarkedPairMachine_numStates,
        endmarkedPairMachine_numStackSymbols,
        Nat.mod_eq_of_lt
          (Endmarked.leftPending_lt_stateCount (q := target)
            left right hpending)]
      intro symbol hsymbol
      exact Nat.mod_eq_of_lt
        (Endmarked.leftStack_lt_stackCount left right symbol)

private theorem endmarked_rightEpsilon_key
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (pending : Action) (hpending : pending ∈ alphabet)
    (row : EpsilonRow)
    (hrow : row ∈ (endmarkedPairMachine left right alphabet).epsilonRows)
    (hmatch :
      row.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.rightPending left right alphabet q pending %
            (endmarkedPairMachine left right alphabet).numStates ∧
        row.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Endmarked.rightStack left right Z %
            (endmarkedPairMachine left right alphabet).numStackSymbols) :
    ∃ target replacement,
      selectedEpsilon? right q Z = some (target, replacement) ∧
      row =
        (Endmarked.rightPending left right alphabet q pending,
          Endmarked.rightStack left right Z,
          Endmarked.rightPending left right alphabet target pending,
          replacement.map (Endmarked.rightStack left right)) := by
  have hqueryState := Endmarked.rightPending_lt_stateCount
    (q := q) left right hpending
  have hqueryTop := Endmarked.rightStack_lt_stackCount left right Z
  rcases (mem_endmarked_epsilonRows_iff left right alphabet row).mp hrow with
    hleft | hright | hdrain
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, hrowEq⟩ :=
      (Endmarked.mem_embeddedEpsilonRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left) row).mp
        (by simpa [Endmarked.leftEpsilonRows] using hleft)
    subst row
    have hrowState := Endmarked.leftPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.rightPending left right alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hleftLt := Endmarked.leftPending_lt_rightPendingBase
      (q := sourceState) left hstored
    have hrightGe := Endmarked.rightPending_ge_base
      left right alphabet q pending
    omega
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, hrowEq⟩ :=
      (Endmarked.mem_embeddedEpsilonRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right) row).mp
        (by simpa [Endmarked.rightEpsilonRows] using hright)
    subst row
    have hrowState := Endmarked.rightPending_lt_stateCount
      (q := sourceState) left right hstored
    have hrowTop := Endmarked.rightStack_lt_stackCount
      left right sourceTop
    have hstateEq :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.rightPending left right alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hstateEq' :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.rightPending left right alphabet
            (q % right.numStates) pending := by
      simpa [Endmarked.rightPending, Nat.mod_mod] using hstateEq
    have hkeys := Endmarked.rightPending_injective left right hsourceState
      (Nat.mod_lt q right.numStates_pos) hstored hpending hstateEq'
    have htopEq : Endmarked.rightStack left right sourceTop =
        Endmarked.rightStack left right Z := by
      simpa [endmarkedPairMachine_numStackSymbols,
        Nat.mod_eq_of_lt hrowTop, Nat.mod_eq_of_lt hqueryTop] using hmatch.2
    have htopEq' : Endmarked.rightStack left right sourceTop =
        Endmarked.rightStack left right (Z % right.numStackSymbols) := by
      simpa [Endmarked.rightStack, Nat.mod_mod] using htopEq
    have hsourceTopEq : sourceTop = Z % right.numStackSymbols :=
      Endmarked.rightStack_injective left right hsourceTop
        (Nat.mod_lt Z right.numStackSymbols_pos) htopEq'
    have hstep' : selectedEpsilon? right q Z =
        some (target, replacement) := by
      rw [← selectedEpsilon?_normalized_key right q Z]
      simpa [hkeys.1, hsourceTopEq] using hstep
    refine ⟨target, replacement, hstep', ?_⟩
    rw [hkeys.1, hkeys.2, hsourceTopEq]
    simp [Endmarked.rightPending, Endmarked.rightStack]
  · obtain ⟨sourceTop, hsourceTop, hrowEq⟩ := List.mem_map.mp hdrain
    subst row
    have hrowState := Endmarked.acceptState_lt_stateCount
      left right alphabet
    have hstateEq : Endmarked.acceptState left right alphabet =
        Endmarked.rightPending left right alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hrightLt := Endmarked.rightPending_lt_acceptState
      (q := q) left right hpending
    omega

public theorem endmarked_selectedEpsilon?_rightPending_eq
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (pending : Action) (hpending : pending ∈ alphabet) :
    selectedEpsilon? (endmarkedPairMachine left right alphabet)
        (Endmarked.rightPending left right alphabet q pending)
        (Endmarked.rightStack left right Z) =
      (selectedEpsilon? right q Z).map fun output =>
        (Endmarked.rightPending left right alphabet output.1 pending,
          output.2.map (Endmarked.rightStack left right)) := by
  cases hsource : selectedEpsilon? right q Z with
  | none =>
      simp only [Option.map_none]
      apply Option.eq_none_iff_forall_not_mem.mpr
      intro output houtput
      unfold selectedEpsilon? at houtput
      obtain ⟨row, hfind, hout⟩ := Option.map_eq_some_iff.mp houtput
      have hrow := List.mem_of_find?_eq_some hfind
      have hmatch := List.find?_some hfind
      simp only [decide_eq_true_eq] at hmatch
      obtain ⟨target, replacement, hstep, _⟩ :=
        endmarked_rightEpsilon_key left right alphabet q Z pending hpending
          row hrow hmatch
      rw [hsource] at hstep
      simp at hstep
  | some sourceOutput =>
      rcases sourceOutput with ⟨target, replacement⟩
      let targetRow : EpsilonRow :=
        (Endmarked.rightPending left right alphabet q pending,
          Endmarked.rightStack left right Z,
          Endmarked.rightPending left right alphabet target pending,
          replacement.map (Endmarked.rightStack left right))
      have hqNorm := Nat.mod_lt q right.numStates_pos
      have hZNorm := Nat.mod_lt Z right.numStackSymbols_pos
      have htargetMem : targetRow ∈
          (endmarkedPairMachine left right alphabet).epsilonRows := by
        rw [mem_endmarked_epsilonRows_iff]
        right
        left
        rw [Endmarked.rightEpsilonRows,
          Endmarked.mem_embeddedEpsilonRows_iff]
        refine ⟨pending, hpending, q % right.numStates, hqNorm,
          Z % right.numStackSymbols, hZNorm, target, replacement, ?_, ?_⟩
        · simpa [selectedEpsilon?_normalized_key] using hsource
        · simp [targetRow, Endmarked.rightPending, Endmarked.rightStack]
      have hqueryState := Endmarked.rightPending_lt_stateCount
        (q := q) left right hpending
      have hqueryTop := Endmarked.rightStack_lt_stackCount left right Z
      have htargetMatch : decide
          (targetRow.1 % (endmarkedPairMachine left right alphabet).numStates =
              Endmarked.rightPending left right alphabet q pending %
                (endmarkedPairMachine left right alphabet).numStates ∧
            targetRow.2.1 %
                (endmarkedPairMachine left right alphabet).numStackSymbols =
              Endmarked.rightStack left right Z %
                (endmarkedPairMachine left right alphabet).numStackSymbols) =
          true := by
        simp [targetRow, endmarkedPairMachine_numStates,
          endmarkedPairMachine_numStackSymbols,
          Nat.mod_eq_of_lt hqueryState, Nat.mod_eq_of_lt hqueryTop]
      have hfind :
          (endmarkedPairMachine left right alphabet).epsilonRows.find?
              (fun row => decide
                (row.1 % (endmarkedPairMachine left right alphabet).numStates =
                    Endmarked.rightPending left right alphabet q pending %
                      (endmarkedPairMachine left right alphabet).numStates ∧
                  row.2.1 %
                      (endmarkedPairMachine left right alphabet).numStackSymbols =
                    Endmarked.rightStack left right Z %
                      (endmarkedPairMachine left right alphabet).numStackSymbols)) =
            some targetRow := by
        apply find?_eq_some_of_unique htargetMem htargetMatch
        intro row hrow hmatch
        simp only [decide_eq_true_eq] at hmatch
        obtain ⟨rowTarget, rowReplacement, hrowStep, hrowEq⟩ :=
          endmarked_rightEpsilon_key left right alphabet q Z pending hpending
            row hrow hmatch
        have houtEq : (rowTarget, rowReplacement) =
            (target, replacement) := Option.some.inj (hrowStep.symm.trans hsource)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj houtEq
        exact hrowEq
      unfold selectedEpsilon?
      rw [hfind]
      simp [targetRow, endmarkedPairMachine_numStates,
        endmarkedPairMachine_numStackSymbols,
        Nat.mod_eq_of_lt
          (Endmarked.rightPending_lt_stateCount (q := target)
            left right hpending)]
      intro symbol hsymbol
      exact Nat.mod_eq_of_lt
        (Endmarked.rightStack_lt_stackCount left right symbol)

private theorem endmarked_leftInput_key
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (pending : Action) (hpending : pending ∈ alphabet)
    (next : Option Action) (hnext : next ∈ endmarkedAlphabet alphabet)
    (row : InputRow (Option Action))
    (hrow : row ∈ (endmarkedPairMachine left right alphabet).inputRows)
    (hmatch :
      row.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.leftPending left alphabet q pending %
            (endmarkedPairMachine left right alphabet).numStates ∧
        row.2.1 = next ∧
        row.2.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Endmarked.leftStack left Z %
            (endmarkedPairMachine left right alphabet).numStackSymbols) :
    ∃ target replacement,
      selectedInput? left q pending Z = some (target, replacement) ∧
      row =
        (Endmarked.leftPending left alphabet q pending, next,
          Endmarked.leftStack left Z,
          match next with
          | some action => Endmarked.leftPending left alphabet target action
          | none =>
              if Endmarked.isFinalIndex left target then
                Endmarked.acceptState left right alphabet
              else Endmarked.rejectState left right alphabet,
          replacement.map (Endmarked.leftStack left)) := by
  have hqueryState := Endmarked.leftPending_lt_stateCount
    (q := q) left right hpending
  have hqueryTop := Endmarked.leftStack_lt_stackCount left right Z
  rcases (mem_endmarked_inputRows_iff left right alphabet row).mp hrow with
    hstart | hleft | hright
  · have hrowLt := Endmarked.startRows_source_lt_leftPendingBase
      left right alphabet hstart
    have hrowState : row.1 < Endmarked.stateCount left right alphabet := by
      have hbase : Endmarked.leftPendingBase <
          Endmarked.stateCount left right alphabet := by
        unfold Endmarked.leftPendingBase Endmarked.stateCount
          Endmarked.rejectState Endmarked.acceptState
          Endmarked.rightPendingBase
        omega
      exact hrowLt.trans hbase
    have hstateEq : row.1 =
        Endmarked.leftPending left alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hge := Endmarked.leftPending_ge_base left alphabet q pending
    omega
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, storedNext, hstoredNext,
        hrowEq⟩ :=
      (Endmarked.mem_embeddedInputRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left)
        (fun state =>
          if Endmarked.isFinalIndex left state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) row).mp
        (by simpa [Endmarked.leftInputRows] using hleft)
    subst row
    have hrowState := Endmarked.leftPending_lt_stateCount
      (q := sourceState) left right hstored
    have hrowTop := Endmarked.leftStack_lt_stackCount
      left right sourceTop
    have hstateEq :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.leftPending left alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hstateEq' :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.leftPending left alphabet (q % left.numStates) pending := by
      simpa [Endmarked.leftPending, Nat.mod_mod] using hstateEq
    have hkeys := Endmarked.leftPending_injective left hsourceState
      (Nat.mod_lt q left.numStates_pos) hstored hpending hstateEq'
    have htopEq : Endmarked.leftStack left sourceTop =
        Endmarked.leftStack left Z := by
      simpa [endmarkedPairMachine_numStackSymbols,
        Nat.mod_eq_of_lt hrowTop, Nat.mod_eq_of_lt hqueryTop] using hmatch.2.2
    have htopEq' : Endmarked.leftStack left sourceTop =
        Endmarked.leftStack left (Z % left.numStackSymbols) := by
      simpa [Endmarked.leftStack, Nat.mod_mod] using htopEq
    have hsourceTopEq : sourceTop = Z % left.numStackSymbols :=
      Endmarked.leftStack_injective left hsourceTop
        (Nat.mod_lt Z left.numStackSymbols_pos) htopEq'
    have hnextEq : storedNext = next := hmatch.2.1
    have hstep' : selectedInput? left q pending Z =
        some (target, replacement) := by
      rw [← selectedInput?_normalized_key left q pending Z]
      simpa [hkeys.1, hkeys.2, hsourceTopEq] using hstep
    refine ⟨target, replacement, hstep', ?_⟩
    subst storedNext
    have hstoredEq : stored = pending := hkeys.2
    subst stored
    cases next <;>
      simp [hkeys.1, hsourceTopEq, Endmarked.leftPending,
        Endmarked.leftStack]
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, storedNext, hstoredNext,
        hrowEq⟩ :=
      (Endmarked.mem_embeddedInputRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right)
        (fun state =>
          if Endmarked.isFinalIndex right state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) row).mp
        (by simpa [Endmarked.rightInputRows] using hright)
    subst row
    have hrowState := Endmarked.rightPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.leftPending left alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hleftLt := Endmarked.leftPending_lt_rightPendingBase
      (q := q) left hpending
    have hrightGe := Endmarked.rightPending_ge_base
      left right alphabet sourceState stored
    omega

public theorem endmarked_selectedInput?_leftPending_eq
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (pending : Action) (hpending : pending ∈ alphabet)
    (next : Option Action) (hnext : next ∈ endmarkedAlphabet alphabet) :
    selectedInput? (endmarkedPairMachine left right alphabet)
        (Endmarked.leftPending left alphabet q pending) next
        (Endmarked.leftStack left Z) =
      (selectedInput? left q pending Z).map fun output =>
        (match next with
        | some action => Endmarked.leftPending left alphabet output.1 action
        | none =>
            if Endmarked.isFinalIndex left output.1 then
              Endmarked.acceptState left right alphabet
            else Endmarked.rejectState left right alphabet,
          output.2.map (Endmarked.leftStack left)) := by
  have hepsilon := endmarked_selectedEpsilon?_leftPending_eq
    left right alphabet q Z pending hpending
  cases hsourceEpsilon : selectedEpsilon? left q Z with
  | some epsilonOutput =>
      unfold selectedInput?
      rw [hepsilon, hsourceEpsilon]
      simp
  | none =>
      have htargetEpsilon : selectedEpsilon?
          (endmarkedPairMachine left right alphabet)
          (Endmarked.leftPending left alphabet q pending)
          (Endmarked.leftStack left Z) = none := by
        rw [hepsilon, hsourceEpsilon]
        rfl
      cases hsource : selectedInput? left q pending Z with
      | none =>
          simp only [Option.map_none]
          unfold selectedInput?
          rw [htargetEpsilon]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          apply Option.eq_none_iff_forall_not_mem.mpr
          intro output houtput
          obtain ⟨row, hfind, hout⟩ := Option.map_eq_some_iff.mp houtput
          have hrow := List.mem_of_find?_eq_some hfind
          have hmatch := List.find?_some hfind
          simp only [decide_eq_true_eq] at hmatch
          obtain ⟨target, replacement, hstep, _⟩ :=
            endmarked_leftInput_key left right alphabet q Z pending hpending
              next hnext row hrow hmatch
          rw [hsource] at hstep
          simp at hstep
      | some sourceOutput =>
          rcases sourceOutput with ⟨target, replacement⟩
          let targetState :=
            match next with
            | some action => Endmarked.leftPending left alphabet target action
            | none =>
                if Endmarked.isFinalIndex left target then
                  Endmarked.acceptState left right alphabet
                else Endmarked.rejectState left right alphabet
          let targetRow : InputRow (Option Action) :=
            (Endmarked.leftPending left alphabet q pending, next,
              Endmarked.leftStack left Z, targetState,
              replacement.map (Endmarked.leftStack left))
          have hqNorm := Nat.mod_lt q left.numStates_pos
          have hZNorm := Nat.mod_lt Z left.numStackSymbols_pos
          have htargetMem : targetRow ∈
              (endmarkedPairMachine left right alphabet).inputRows := by
            rw [mem_endmarked_inputRows_iff]
            right
            left
            rw [Endmarked.leftInputRows,
              Endmarked.mem_embeddedInputRows_iff]
            refine ⟨pending, hpending, q % left.numStates, hqNorm,
              Z % left.numStackSymbols, hZNorm, target, replacement, ?_,
              next, hnext, ?_⟩
            · simpa [selectedInput?_normalized_key] using hsource
            · simp [targetRow, targetState, Endmarked.leftPending,
                Endmarked.leftStack]
          have hqueryState := Endmarked.leftPending_lt_stateCount
            (q := q) left right hpending
          have hqueryTop := Endmarked.leftStack_lt_stackCount left right Z
          have htargetMatch : decide
              (targetRow.1 %
                    (endmarkedPairMachine left right alphabet).numStates =
                  Endmarked.leftPending left alphabet q pending %
                    (endmarkedPairMachine left right alphabet).numStates ∧
                targetRow.2.1 = next ∧
                targetRow.2.2.1 %
                    (endmarkedPairMachine left right alphabet).numStackSymbols =
                  Endmarked.leftStack left Z %
                    (endmarkedPairMachine left right alphabet).numStackSymbols) =
              true := by
            simp [targetRow, endmarkedPairMachine_numStates,
              endmarkedPairMachine_numStackSymbols,
              Nat.mod_eq_of_lt hqueryState, Nat.mod_eq_of_lt hqueryTop]
          have hfind :
              (endmarkedPairMachine left right alphabet).inputRows.find?
                  (fun row => decide
                    (row.1 %
                          (endmarkedPairMachine left right alphabet).numStates =
                        Endmarked.leftPending left alphabet q pending %
                          (endmarkedPairMachine left right alphabet).numStates ∧
                      row.2.1 = next ∧
                      row.2.2.1 %
                          (endmarkedPairMachine left right alphabet).numStackSymbols =
                        Endmarked.leftStack left Z %
                          (endmarkedPairMachine left right alphabet).numStackSymbols)) =
                some targetRow := by
            apply find?_eq_some_of_unique htargetMem htargetMatch
            intro row hrow hmatch
            simp only [decide_eq_true_eq] at hmatch
            obtain ⟨rowTarget, rowReplacement, hrowStep, hrowEq⟩ :=
              endmarked_leftInput_key left right alphabet q Z pending hpending
                next hnext row hrow hmatch
            have houtEq : (rowTarget, rowReplacement) =
                (target, replacement) :=
              Option.some.inj (hrowStep.symm.trans hsource)
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj houtEq
            cases next <;> simpa [targetRow, targetState] using hrowEq
          unfold selectedInput?
          rw [htargetEpsilon]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          rw [hfind]
          simp only [Option.map_some]
          have htargetState : targetState <
              Endmarked.stateCount left right alphabet := by
            cases next with
            | none =>
                simp only [targetState]
                split
                · exact Endmarked.acceptState_lt_stateCount left right alphabet
                · exact Endmarked.rejectState_lt_stateCount left right alphabet
            | some action =>
                have haction : action ∈ alphabet := by
                  simpa [endmarkedAlphabet] using hnext
                exact Endmarked.leftPending_lt_stateCount
                  (q := target) left right haction
          simp only [Option.some.injEq]
          apply Prod.ext
          · cases next <;>
              simp [targetRow, targetState, endmarkedPairMachine_numStates,
                Nat.mod_eq_of_lt htargetState]
          · simp [targetRow, endmarkedPairMachine_numStackSymbols]
            intro symbol hsymbol
            exact Nat.mod_eq_of_lt
              (Endmarked.leftStack_lt_stackCount left right symbol)

private theorem endmarked_rightInput_key
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (pending : Action) (hpending : pending ∈ alphabet)
    (next : Option Action) (hnext : next ∈ endmarkedAlphabet alphabet)
    (row : InputRow (Option Action))
    (hrow : row ∈ (endmarkedPairMachine left right alphabet).inputRows)
    (hmatch :
      row.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.rightPending left right alphabet q pending %
            (endmarkedPairMachine left right alphabet).numStates ∧
        row.2.1 = next ∧
        row.2.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Endmarked.rightStack left right Z %
            (endmarkedPairMachine left right alphabet).numStackSymbols) :
    ∃ target replacement,
      selectedInput? right q pending Z = some (target, replacement) ∧
      row =
        (Endmarked.rightPending left right alphabet q pending, next,
          Endmarked.rightStack left right Z,
          match next with
          | some action =>
              Endmarked.rightPending left right alphabet target action
          | none =>
              if Endmarked.isFinalIndex right target then
                Endmarked.acceptState left right alphabet
              else Endmarked.rejectState left right alphabet,
          replacement.map (Endmarked.rightStack left right)) := by
  have hqueryState := Endmarked.rightPending_lt_stateCount
    (q := q) left right hpending
  have hqueryTop := Endmarked.rightStack_lt_stackCount left right Z
  rcases (mem_endmarked_inputRows_iff left right alphabet row).mp hrow with
    hstart | hleft | hright
  · have hrowLt := Endmarked.startRows_source_lt_leftPendingBase
      left right alphabet hstart
    have hrowState : row.1 < Endmarked.stateCount left right alphabet := by
      have hbase : Endmarked.leftPendingBase <
          Endmarked.stateCount left right alphabet := by
        unfold Endmarked.leftPendingBase Endmarked.stateCount
          Endmarked.rejectState Endmarked.acceptState
          Endmarked.rightPendingBase
        omega
      exact hrowLt.trans hbase
    have hstateEq : row.1 =
        Endmarked.rightPending left right alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hrightBase := Endmarked.rightPending_ge_base
      left right alphabet q pending
    have hbase : Endmarked.leftPendingBase ≤
        Endmarked.rightPendingBase left alphabet := by
      simp [Endmarked.rightPendingBase]
    omega
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, storedNext, hstoredNext,
        hrowEq⟩ :=
      (Endmarked.mem_embeddedInputRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left)
        (fun state =>
          if Endmarked.isFinalIndex left state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) row).mp
        (by simpa [Endmarked.leftInputRows] using hleft)
    subst row
    have hrowState := Endmarked.leftPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.rightPending left right alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hleftLt := Endmarked.leftPending_lt_rightPendingBase
      (q := sourceState) left hstored
    have hrightGe := Endmarked.rightPending_ge_base
      left right alphabet q pending
    omega
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, storedNext, hstoredNext,
        hrowEq⟩ :=
      (Endmarked.mem_embeddedInputRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right)
        (fun state =>
          if Endmarked.isFinalIndex right state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) row).mp
        (by simpa [Endmarked.rightInputRows] using hright)
    subst row
    have hrowState := Endmarked.rightPending_lt_stateCount
      (q := sourceState) left right hstored
    have hrowTop := Endmarked.rightStack_lt_stackCount
      left right sourceTop
    have hstateEq :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.rightPending left right alphabet q pending := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hqueryState] using hmatch.1
    have hstateEq' :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.rightPending left right alphabet
            (q % right.numStates) pending := by
      simpa [Endmarked.rightPending, Nat.mod_mod] using hstateEq
    have hkeys := Endmarked.rightPending_injective left right hsourceState
      (Nat.mod_lt q right.numStates_pos) hstored hpending hstateEq'
    have htopEq : Endmarked.rightStack left right sourceTop =
        Endmarked.rightStack left right Z := by
      simpa [endmarkedPairMachine_numStackSymbols,
        Nat.mod_eq_of_lt hrowTop, Nat.mod_eq_of_lt hqueryTop] using hmatch.2.2
    have htopEq' : Endmarked.rightStack left right sourceTop =
        Endmarked.rightStack left right (Z % right.numStackSymbols) := by
      simpa [Endmarked.rightStack, Nat.mod_mod] using htopEq
    have hsourceTopEq : sourceTop = Z % right.numStackSymbols :=
      Endmarked.rightStack_injective left right hsourceTop
        (Nat.mod_lt Z right.numStackSymbols_pos) htopEq'
    have hnextEq : storedNext = next := hmatch.2.1
    have hstep' : selectedInput? right q pending Z =
        some (target, replacement) := by
      rw [← selectedInput?_normalized_key right q pending Z]
      simpa [hkeys.1, hkeys.2, hsourceTopEq] using hstep
    refine ⟨target, replacement, hstep', ?_⟩
    subst storedNext
    have hstoredEq : stored = pending := hkeys.2
    subst stored
    cases next <;>
      simp [hkeys.1, hsourceTopEq, Endmarked.rightPending,
        Endmarked.rightStack]

public theorem endmarked_selectedInput?_rightPending_eq
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (pending : Action) (hpending : pending ∈ alphabet)
    (next : Option Action) (hnext : next ∈ endmarkedAlphabet alphabet) :
    selectedInput? (endmarkedPairMachine left right alphabet)
        (Endmarked.rightPending left right alphabet q pending) next
        (Endmarked.rightStack left right Z) =
      (selectedInput? right q pending Z).map fun output =>
        (match next with
        | some action =>
            Endmarked.rightPending left right alphabet output.1 action
        | none =>
            if Endmarked.isFinalIndex right output.1 then
              Endmarked.acceptState left right alphabet
            else Endmarked.rejectState left right alphabet,
          output.2.map (Endmarked.rightStack left right)) := by
  have hepsilon := endmarked_selectedEpsilon?_rightPending_eq
    left right alphabet q Z pending hpending
  cases hsourceEpsilon : selectedEpsilon? right q Z with
  | some epsilonOutput =>
      unfold selectedInput?
      rw [hepsilon, hsourceEpsilon]
      simp
  | none =>
      have htargetEpsilon : selectedEpsilon?
          (endmarkedPairMachine left right alphabet)
          (Endmarked.rightPending left right alphabet q pending)
          (Endmarked.rightStack left right Z) = none := by
        rw [hepsilon, hsourceEpsilon]
        rfl
      cases hsource : selectedInput? right q pending Z with
      | none =>
          simp only [Option.map_none]
          unfold selectedInput?
          rw [htargetEpsilon]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          apply Option.eq_none_iff_forall_not_mem.mpr
          intro output houtput
          obtain ⟨row, hfind, hout⟩ := Option.map_eq_some_iff.mp houtput
          have hrow := List.mem_of_find?_eq_some hfind
          have hmatch := List.find?_some hfind
          simp only [decide_eq_true_eq] at hmatch
          obtain ⟨target, replacement, hstep, _⟩ :=
            endmarked_rightInput_key left right alphabet q Z pending hpending
              next hnext row hrow hmatch
          rw [hsource] at hstep
          simp at hstep
      | some sourceOutput =>
          rcases sourceOutput with ⟨target, replacement⟩
          let targetState :=
            match next with
            | some action =>
                Endmarked.rightPending left right alphabet target action
            | none =>
                if Endmarked.isFinalIndex right target then
                  Endmarked.acceptState left right alphabet
                else Endmarked.rejectState left right alphabet
          let targetRow : InputRow (Option Action) :=
            (Endmarked.rightPending left right alphabet q pending, next,
              Endmarked.rightStack left right Z, targetState,
              replacement.map (Endmarked.rightStack left right))
          have hqNorm := Nat.mod_lt q right.numStates_pos
          have hZNorm := Nat.mod_lt Z right.numStackSymbols_pos
          have htargetMem : targetRow ∈
              (endmarkedPairMachine left right alphabet).inputRows := by
            rw [mem_endmarked_inputRows_iff]
            right
            right
            rw [Endmarked.rightInputRows,
              Endmarked.mem_embeddedInputRows_iff]
            refine ⟨pending, hpending, q % right.numStates, hqNorm,
              Z % right.numStackSymbols, hZNorm, target, replacement, ?_,
              next, hnext, ?_⟩
            · simpa [selectedInput?_normalized_key] using hsource
            · simp [targetRow, targetState, Endmarked.rightPending,
                Endmarked.rightStack]
          have hqueryState := Endmarked.rightPending_lt_stateCount
            (q := q) left right hpending
          have hqueryTop := Endmarked.rightStack_lt_stackCount left right Z
          have htargetMatch : decide
              (targetRow.1 %
                    (endmarkedPairMachine left right alphabet).numStates =
                  Endmarked.rightPending left right alphabet q pending %
                    (endmarkedPairMachine left right alphabet).numStates ∧
                targetRow.2.1 = next ∧
                targetRow.2.2.1 %
                    (endmarkedPairMachine left right alphabet).numStackSymbols =
                  Endmarked.rightStack left right Z %
                    (endmarkedPairMachine left right alphabet).numStackSymbols) =
              true := by
            simp [targetRow, endmarkedPairMachine_numStates,
              endmarkedPairMachine_numStackSymbols,
              Nat.mod_eq_of_lt hqueryState, Nat.mod_eq_of_lt hqueryTop]
          have hfind :
              (endmarkedPairMachine left right alphabet).inputRows.find?
                  (fun row => decide
                    (row.1 %
                          (endmarkedPairMachine left right alphabet).numStates =
                        Endmarked.rightPending left right alphabet q pending %
                          (endmarkedPairMachine left right alphabet).numStates ∧
                      row.2.1 = next ∧
                      row.2.2.1 %
                          (endmarkedPairMachine left right alphabet).numStackSymbols =
                        Endmarked.rightStack left right Z %
                          (endmarkedPairMachine left right alphabet).numStackSymbols)) =
                some targetRow := by
            apply find?_eq_some_of_unique htargetMem htargetMatch
            intro row hrow hmatch
            simp only [decide_eq_true_eq] at hmatch
            obtain ⟨rowTarget, rowReplacement, hrowStep, hrowEq⟩ :=
              endmarked_rightInput_key left right alphabet q Z pending hpending
                next hnext row hrow hmatch
            have houtEq : (rowTarget, rowReplacement) =
                (target, replacement) :=
              Option.some.inj (hrowStep.symm.trans hsource)
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj houtEq
            cases next <;> simpa [targetRow, targetState] using hrowEq
          unfold selectedInput?
          rw [htargetEpsilon]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          rw [hfind]
          simp only [Option.map_some]
          have htargetState : targetState <
              Endmarked.stateCount left right alphabet := by
            cases next with
            | none =>
                simp only [targetState]
                split
                · exact Endmarked.acceptState_lt_stateCount left right alphabet
                · exact Endmarked.rejectState_lt_stateCount left right alphabet
            | some action =>
                have haction : action ∈ alphabet := by
                  simpa [endmarkedAlphabet] using hnext
                exact Endmarked.rightPending_lt_stateCount
                  (q := target) left right haction
          simp only [Option.some.injEq]
          apply Prod.ext
          · cases next <;>
              simp [targetRow, targetState, endmarkedPairMachine_numStates,
                Nat.mod_eq_of_lt htargetState]
          · simp [targetRow, endmarkedPairMachine_numStackSymbols]
            intro symbol hsymbol
            exact Nat.mod_eq_of_lt
              (Endmarked.rightStack_lt_stackCount left right symbol)

private theorem endmarked_leftStartInput_key
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (next : Option Action) (hnext : next ∈ endmarkedAlphabet alphabet)
    (row : InputRow (Option Action))
    (hrow : row ∈ (endmarkedPairMachine left right alphabet).inputRows)
    (hmatch :
      row.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.leftStart %
            (endmarkedPairMachine left right alphabet).numStates ∧
        row.2.1 = next ∧
        row.2.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Endmarked.bottom %
            (endmarkedPairMachine left right alphabet).numStackSymbols) :
    row =
      (Endmarked.leftStart, next, Endmarked.bottom,
        match next with
        | some action =>
            Endmarked.leftPending left alphabet left.initialIndex action
        | none =>
            if Endmarked.isFinalIndex left left.initialIndex then
              Endmarked.acceptState left right alphabet
            else Endmarked.rejectState left right alphabet,
        match next with
        | some _ => [Endmarked.leftStack left left.startIndex, Endmarked.bottom]
        | none => [Endmarked.bottom]) := by
  have hstartState : Endmarked.leftStart <
      Endmarked.stateCount left right alphabet := by
    simp [Endmarked.leftStart, Endmarked.stateCount,
      Endmarked.rejectState]
  have hrightStartState : Endmarked.rightStart <
      Endmarked.stateCount left right alphabet := by
    simp [Endmarked.rightStart, Endmarked.stateCount,
      Endmarked.rejectState, Endmarked.acceptState,
      Endmarked.rightPendingBase, Endmarked.leftPendingBase]
  rcases (mem_endmarked_inputRows_iff left right alphabet row).mp hrow with
    hstart | hleft | hright
  · rcases (Endmarked.mem_startRows_iff left right alphabet row).mp hstart with
      hleftLetter | hleftEnd | hrightLetter | hrightEnd
    · obtain ⟨action, haction, rfl⟩ := hleftLetter
      have hactionEq : some action = next := hmatch.2.1
      cases next with
      | none => simp at hactionEq
      | some nextAction =>
          have : action = nextAction := Option.some.inj hactionEq
          subst action
          rfl
    · subst row
      have hactionEq : (none : Option Action) = next := hmatch.2.1
      subst next
      rfl
    · obtain ⟨action, haction, rfl⟩ := hrightLetter
      have hstate : Endmarked.rightStart = Endmarked.leftStart := by
        simpa [endmarkedPairMachine_numStates,
          Nat.mod_eq_of_lt hstartState,
          Nat.mod_eq_of_lt hrightStartState] using hmatch.1
      simp [Endmarked.leftStart, Endmarked.rightStart] at hstate
    · subst row
      have hstate : Endmarked.rightStart = Endmarked.leftStart := by
        simpa [endmarkedPairMachine_numStates,
          Nat.mod_eq_of_lt hstartState,
          Nat.mod_eq_of_lt hrightStartState] using hmatch.1
      simp [Endmarked.leftStart, Endmarked.rightStart] at hstate
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, storedNext, hstoredNext,
        hrowEq⟩ :=
      (Endmarked.mem_embeddedInputRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left)
        (fun state =>
          if Endmarked.isFinalIndex left state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) row).mp
        (by simpa [Endmarked.leftInputRows] using hleft)
    subst row
    have hrowState := Endmarked.leftPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.leftStart := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hstartState] using hmatch.1
    have hge := Endmarked.leftPending_ge_base
      left alphabet sourceState stored
    unfold Endmarked.leftStart at hstateEq
    unfold Endmarked.leftPendingBase at hge
    omega
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, storedNext, hstoredNext,
        hrowEq⟩ :=
      (Endmarked.mem_embeddedInputRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right)
        (fun state =>
          if Endmarked.isFinalIndex right state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) row).mp
        (by simpa [Endmarked.rightInputRows] using hright)
    subst row
    have hrowState := Endmarked.rightPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.leftStart := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hstartState] using hmatch.1
    have hge := Endmarked.rightPending_ge_base
      left right alphabet sourceState stored
    have hbase : 0 < Endmarked.rightPendingBase left alphabet := by
      simp [Endmarked.rightPendingBase, Endmarked.leftPendingBase]
    unfold Endmarked.leftStart at hstateEq
    omega

public theorem endmarked_selectedInput?_leftStart_eq
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (next : Option Action) (hnext : next ∈ endmarkedAlphabet alphabet) :
    selectedInput? (endmarkedPairMachine left right alphabet)
        Endmarked.leftStart next Endmarked.bottom =
      some
        (match next with
        | some action =>
            Endmarked.leftPending left alphabet left.initialIndex action
        | none =>
            if Endmarked.isFinalIndex left left.initialIndex then
              Endmarked.acceptState left right alphabet
            else Endmarked.rejectState left right alphabet,
          match next with
          | some _ =>
              [Endmarked.leftStack left left.startIndex, Endmarked.bottom]
          | none => [Endmarked.bottom]) := by
  let targetState :=
    match next with
    | some action =>
        Endmarked.leftPending left alphabet left.initialIndex action
    | none =>
        if Endmarked.isFinalIndex left left.initialIndex then
          Endmarked.acceptState left right alphabet
        else Endmarked.rejectState left right alphabet
  let targetStack :=
    match next with
    | some _ => [Endmarked.leftStack left left.startIndex, Endmarked.bottom]
    | none => [Endmarked.bottom]
  let targetRow : InputRow (Option Action) :=
    (Endmarked.leftStart, next, Endmarked.bottom, targetState, targetStack)
  have htargetMem : targetRow ∈
      (endmarkedPairMachine left right alphabet).inputRows := by
    rw [mem_endmarked_inputRows_iff]
    left
    rw [Endmarked.mem_startRows_iff]
    cases next with
    | none =>
        right
        left
        simp [targetRow, targetState, targetStack]
    | some action =>
        left
        have haction : action ∈ alphabet := by
          simpa [endmarkedAlphabet] using hnext
        exact ⟨action, haction, by
          simp [targetRow, targetState, targetStack]⟩
  have hstartState : Endmarked.leftStart <
      Endmarked.stateCount left right alphabet := by
    simp [Endmarked.leftStart, Endmarked.stateCount,
      Endmarked.rejectState]
  have hbottom : Endmarked.bottom < Endmarked.stackCount left right := by
    simp [Endmarked.bottom, Endmarked.stackCount]
  have htargetMatch : decide
      (targetRow.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.leftStart %
            (endmarkedPairMachine left right alphabet).numStates ∧
        targetRow.2.1 = next ∧
        targetRow.2.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Endmarked.bottom %
            (endmarkedPairMachine left right alphabet).numStackSymbols) =
      true := by
    simp [targetRow, endmarkedPairMachine_numStates,
      endmarkedPairMachine_numStackSymbols, Nat.mod_eq_of_lt hstartState,
      Nat.mod_eq_of_lt hbottom]
  have hfind :
      (endmarkedPairMachine left right alphabet).inputRows.find?
          (fun row => decide
            (row.1 % (endmarkedPairMachine left right alphabet).numStates =
                Endmarked.leftStart %
                  (endmarkedPairMachine left right alphabet).numStates ∧
              row.2.1 = next ∧
              row.2.2.1 %
                  (endmarkedPairMachine left right alphabet).numStackSymbols =
                Endmarked.bottom %
                  (endmarkedPairMachine left right alphabet).numStackSymbols)) =
        some targetRow := by
    apply find?_eq_some_of_unique htargetMem htargetMatch
    intro row hrow hmatch
    simp only [decide_eq_true_eq] at hmatch
    have hrowEq := endmarked_leftStartInput_key left right alphabet next
      hnext row hrow hmatch
    cases next <;> simpa [targetRow, targetState, targetStack] using hrowEq
  unfold selectedInput?
  rw [endmarked_selectedEpsilon?_leftStart_eq_none, hfind]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false,
    Option.map_some, Option.some.injEq]
  apply Prod.ext
  · have htargetState : targetState <
        Endmarked.stateCount left right alphabet := by
      cases next with
      | none =>
          simp only [targetState]
          split
          · exact Endmarked.acceptState_lt_stateCount left right alphabet
          · exact Endmarked.rejectState_lt_stateCount left right alphabet
      | some action =>
          have haction : action ∈ alphabet := by
            simpa [endmarkedAlphabet] using hnext
          exact Endmarked.leftPending_lt_stateCount
            (q := left.initialIndex) left right haction
    cases next <;>
      simp [targetRow, targetState, endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt htargetState]
  · cases next <;>
      simp [targetRow, targetStack, endmarkedPairMachine_numStackSymbols,
        Nat.mod_eq_of_lt hbottom,
        Nat.mod_eq_of_lt
          (Endmarked.leftStack_lt_stackCount left right left.startIndex)]

private theorem endmarked_rightStartInput_key
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (next : Option Action) (hnext : next ∈ endmarkedAlphabet alphabet)
    (row : InputRow (Option Action))
    (hrow : row ∈ (endmarkedPairMachine left right alphabet).inputRows)
    (hmatch :
      row.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.rightStart %
            (endmarkedPairMachine left right alphabet).numStates ∧
        row.2.1 = next ∧
        row.2.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Endmarked.bottom %
            (endmarkedPairMachine left right alphabet).numStackSymbols) :
    row =
      (Endmarked.rightStart, next, Endmarked.bottom,
        match next with
        | some action =>
            Endmarked.rightPending left right alphabet right.initialIndex action
        | none =>
            if Endmarked.isFinalIndex right right.initialIndex then
              Endmarked.acceptState left right alphabet
            else Endmarked.rejectState left right alphabet,
        match next with
        | some _ =>
            [Endmarked.rightStack left right right.startIndex,
              Endmarked.bottom]
        | none => [Endmarked.bottom]) := by
  have hstartState : Endmarked.rightStart <
      Endmarked.stateCount left right alphabet := by
    simp [Endmarked.rightStart, Endmarked.stateCount,
      Endmarked.rejectState, Endmarked.acceptState,
      Endmarked.rightPendingBase, Endmarked.leftPendingBase]
  have hleftStartState : Endmarked.leftStart <
      Endmarked.stateCount left right alphabet := by
    simp [Endmarked.leftStart, Endmarked.stateCount,
      Endmarked.rejectState]
  rcases (mem_endmarked_inputRows_iff left right alphabet row).mp hrow with
    hstart | hleft | hright
  · rcases (Endmarked.mem_startRows_iff left right alphabet row).mp hstart with
      hleftLetter | hleftEnd | hrightLetter | hrightEnd
    · obtain ⟨action, haction, rfl⟩ := hleftLetter
      have hstate : Endmarked.leftStart = Endmarked.rightStart := by
        simpa [endmarkedPairMachine_numStates,
          Nat.mod_eq_of_lt hstartState,
          Nat.mod_eq_of_lt hleftStartState] using hmatch.1
      simp [Endmarked.leftStart, Endmarked.rightStart] at hstate
    · subst row
      have hstate : Endmarked.leftStart = Endmarked.rightStart := by
        simpa [endmarkedPairMachine_numStates,
          Nat.mod_eq_of_lt hstartState,
          Nat.mod_eq_of_lt hleftStartState] using hmatch.1
      simp [Endmarked.leftStart, Endmarked.rightStart] at hstate
    · obtain ⟨action, haction, rfl⟩ := hrightLetter
      have hactionEq : some action = next := hmatch.2.1
      cases next with
      | none => simp at hactionEq
      | some nextAction =>
          have : action = nextAction := Option.some.inj hactionEq
          subst action
          rfl
    · subst row
      have hactionEq : (none : Option Action) = next := hmatch.2.1
      subst next
      rfl
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, storedNext, hstoredNext,
        hrowEq⟩ :=
      (Endmarked.mem_embeddedInputRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left)
        (fun state =>
          if Endmarked.isFinalIndex left state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) row).mp
        (by simpa [Endmarked.leftInputRows] using hleft)
    subst row
    have hrowState := Endmarked.leftPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.rightStart := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hstartState] using hmatch.1
    have hge := Endmarked.leftPending_ge_base
      left alphabet sourceState stored
    unfold Endmarked.rightStart at hstateEq
    unfold Endmarked.leftPendingBase at hge
    omega
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, storedNext, hstoredNext,
        hrowEq⟩ :=
      (Endmarked.mem_embeddedInputRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right)
        (fun state =>
          if Endmarked.isFinalIndex right state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) row).mp
        (by simpa [Endmarked.rightInputRows] using hright)
    subst row
    have hrowState := Endmarked.rightPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.rightStart := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hstartState] using hmatch.1
    have hge := Endmarked.rightPending_ge_base
      left right alphabet sourceState stored
    have hbase : Endmarked.rightStart <
        Endmarked.rightPendingBase left alphabet := by
      unfold Endmarked.rightPendingBase Endmarked.rightStart
        Endmarked.leftPendingBase
      omega
    omega

public theorem endmarked_selectedInput?_rightStart_eq
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (next : Option Action) (hnext : next ∈ endmarkedAlphabet alphabet) :
    selectedInput? (endmarkedPairMachine left right alphabet)
        Endmarked.rightStart next Endmarked.bottom =
      some
        (match next with
        | some action =>
            Endmarked.rightPending left right alphabet right.initialIndex action
        | none =>
            if Endmarked.isFinalIndex right right.initialIndex then
              Endmarked.acceptState left right alphabet
            else Endmarked.rejectState left right alphabet,
          match next with
          | some _ =>
              [Endmarked.rightStack left right right.startIndex,
                Endmarked.bottom]
          | none => [Endmarked.bottom]) := by
  let targetState :=
    match next with
    | some action =>
        Endmarked.rightPending left right alphabet right.initialIndex action
    | none =>
        if Endmarked.isFinalIndex right right.initialIndex then
          Endmarked.acceptState left right alphabet
        else Endmarked.rejectState left right alphabet
  let targetStack :=
    match next with
    | some _ =>
        [Endmarked.rightStack left right right.startIndex, Endmarked.bottom]
    | none => [Endmarked.bottom]
  let targetRow : InputRow (Option Action) :=
    (Endmarked.rightStart, next, Endmarked.bottom, targetState, targetStack)
  have htargetMem : targetRow ∈
      (endmarkedPairMachine left right alphabet).inputRows := by
    rw [mem_endmarked_inputRows_iff]
    left
    rw [Endmarked.mem_startRows_iff]
    cases next with
    | none =>
        right
        right
        right
        simp [targetRow, targetState, targetStack]
    | some action =>
        right
        right
        left
        have haction : action ∈ alphabet := by
          simpa [endmarkedAlphabet] using hnext
        exact ⟨action, haction, by
          simp [targetRow, targetState, targetStack]⟩
  have hstartState : Endmarked.rightStart <
      Endmarked.stateCount left right alphabet := by
    simp [Endmarked.rightStart, Endmarked.stateCount,
      Endmarked.rejectState, Endmarked.acceptState,
      Endmarked.rightPendingBase, Endmarked.leftPendingBase]
  have hbottom : Endmarked.bottom < Endmarked.stackCount left right := by
    simp [Endmarked.bottom, Endmarked.stackCount]
  have htargetMatch : decide
      (targetRow.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.rightStart %
            (endmarkedPairMachine left right alphabet).numStates ∧
        targetRow.2.1 = next ∧
        targetRow.2.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Endmarked.bottom %
            (endmarkedPairMachine left right alphabet).numStackSymbols) =
      true := by
    simp [targetRow, endmarkedPairMachine_numStates,
      endmarkedPairMachine_numStackSymbols, Nat.mod_eq_of_lt hstartState,
      Nat.mod_eq_of_lt hbottom]
  have hfind :
      (endmarkedPairMachine left right alphabet).inputRows.find?
          (fun row => decide
            (row.1 % (endmarkedPairMachine left right alphabet).numStates =
                Endmarked.rightStart %
                  (endmarkedPairMachine left right alphabet).numStates ∧
              row.2.1 = next ∧
              row.2.2.1 %
                  (endmarkedPairMachine left right alphabet).numStackSymbols =
                Endmarked.bottom %
                  (endmarkedPairMachine left right alphabet).numStackSymbols)) =
        some targetRow := by
    apply find?_eq_some_of_unique htargetMem htargetMatch
    intro row hrow hmatch
    simp only [decide_eq_true_eq] at hmatch
    have hrowEq := endmarked_rightStartInput_key left right alphabet next
      hnext row hrow hmatch
    cases next <;> simpa [targetRow, targetState, targetStack] using hrowEq
  unfold selectedInput?
  rw [endmarked_selectedEpsilon?_rightStart_eq_none, hfind]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false,
    Option.map_some, Option.some.injEq]
  apply Prod.ext
  · have htargetState : targetState <
        Endmarked.stateCount left right alphabet := by
      cases next with
      | none =>
          simp only [targetState]
          split
          · exact Endmarked.acceptState_lt_stateCount left right alphabet
          · exact Endmarked.rejectState_lt_stateCount left right alphabet
      | some action =>
          have haction : action ∈ alphabet := by
            simpa [endmarkedAlphabet] using hnext
          exact Endmarked.rightPending_lt_stateCount
            (q := right.initialIndex) left right haction
    cases next <;>
      simp [targetRow, targetState, endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt htargetState]
  · cases next <;>
      simp [targetRow, targetStack, endmarkedPairMachine_numStackSymbols,
        Nat.mod_eq_of_lt hbottom,
        Nat.mod_eq_of_lt
          (Endmarked.rightStack_lt_stackCount left right right.startIndex)]

public theorem endmarked_selectedEpsilon?_accept_eq
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (Z : ℕ) (hZ : Z < Endmarked.stackCount left right) :
    selectedEpsilon? (endmarkedPairMachine left right alphabet)
        (Endmarked.acceptState left right alphabet) Z =
      some (Endmarked.acceptState left right alphabet, []) := by
  let targetRow : EpsilonRow :=
    (Endmarked.acceptState left right alphabet, Z,
      Endmarked.acceptState left right alphabet, [])
  have htargetMem : targetRow ∈
      (endmarkedPairMachine left right alphabet).epsilonRows := by
    rw [mem_endmarked_epsilonRows_iff]
    right
    right
    exact List.mem_map.mpr ⟨Z, List.mem_range.mpr hZ, rfl⟩
  have haccept := Endmarked.acceptState_lt_stateCount left right alphabet
  have htargetMatch : decide
      (targetRow.1 % (endmarkedPairMachine left right alphabet).numStates =
          Endmarked.acceptState left right alphabet %
            (endmarkedPairMachine left right alphabet).numStates ∧
        targetRow.2.1 %
            (endmarkedPairMachine left right alphabet).numStackSymbols =
          Z % (endmarkedPairMachine left right alphabet).numStackSymbols) =
      true := by
    simp [targetRow]
  have hfind :
      (endmarkedPairMachine left right alphabet).epsilonRows.find?
          (fun row => decide
            (row.1 % (endmarkedPairMachine left right alphabet).numStates =
                Endmarked.acceptState left right alphabet %
                  (endmarkedPairMachine left right alphabet).numStates ∧
              row.2.1 %
                  (endmarkedPairMachine left right alphabet).numStackSymbols =
                Z %
                  (endmarkedPairMachine left right alphabet).numStackSymbols)) =
        some targetRow := by
    apply find?_eq_some_of_unique htargetMem htargetMatch
    intro row hrow hmatch
    simp only [decide_eq_true_eq] at hmatch
    rcases (mem_endmarked_epsilonRows_iff left right alphabet row).mp hrow with
      hleft | hright | hdrain
    · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
          hsourceTop, target, replacement, hstep, rfl⟩ :=
        (Endmarked.mem_embeddedEpsilonRows_iff left alphabet
          (Endmarked.leftPending left alphabet) (Endmarked.leftStack left) _).mp
          (by simpa [Endmarked.leftEpsilonRows] using hleft)
      have hrowState := Endmarked.leftPending_lt_stateCount
        (q := sourceState) left right hstored
      have hstateEq :
          Endmarked.leftPending left alphabet sourceState stored =
            Endmarked.acceptState left right alphabet := by
        simpa [endmarkedPairMachine_numStates,
          Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt haccept] using hmatch.1
      have hleftLt := Endmarked.leftPending_lt_rightPendingBase
        (q := sourceState) left hstored
      unfold Endmarked.acceptState at hstateEq
      omega
    · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
          hsourceTop, target, replacement, hstep, rfl⟩ :=
        (Endmarked.mem_embeddedEpsilonRows_iff right alphabet
          (Endmarked.rightPending left right alphabet)
          (Endmarked.rightStack left right) _).mp
          (by simpa [Endmarked.rightEpsilonRows] using hright)
      have hrowState := Endmarked.rightPending_lt_stateCount
        (q := sourceState) left right hstored
      have hstateEq :
          Endmarked.rightPending left right alphabet sourceState stored =
            Endmarked.acceptState left right alphabet := by
        simpa [endmarkedPairMachine_numStates,
          Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt haccept] using hmatch.1
      have hrightLt := Endmarked.rightPending_lt_acceptState
        (q := sourceState) left right hstored
      omega
    · obtain ⟨rowTop, hrowTop, rfl⟩ := List.mem_map.mp hdrain
      have htopEq : rowTop = Z := by
        simpa [endmarkedPairMachine_numStackSymbols,
          Nat.mod_eq_of_lt (List.mem_range.mp hrowTop),
          Nat.mod_eq_of_lt hZ] using hmatch.2
      subst rowTop
      rfl
  unfold selectedEpsilon?
  rw [hfind]
  simp [targetRow, endmarkedPairMachine_numStates,
    Nat.mod_eq_of_lt haccept]

public theorem endmarked_selectedEpsilon?_reject_eq_none
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) (Z : ℕ) :
    selectedEpsilon? (endmarkedPairMachine left right alphabet)
        (Endmarked.rejectState left right alphabet) Z = none := by
  unfold selectedEpsilon?
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro row hrow hmatch
  simp only [decide_eq_true_eq] at hmatch
  have hreject := Endmarked.rejectState_lt_stateCount left right alphabet
  rcases (mem_endmarked_epsilonRows_iff left right alphabet row).mp hrow with
    hleft | hright | hdrain
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, rfl⟩ :=
      (Endmarked.mem_embeddedEpsilonRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left) _).mp
        (by simpa [Endmarked.leftEpsilonRows] using hleft)
    have hrowState := Endmarked.leftPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.leftPending left alphabet sourceState stored =
          Endmarked.rejectState left right alphabet := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hreject] using hmatch.1
    have hleftLt := Endmarked.leftPending_lt_rightPendingBase
      (q := sourceState) left hstored
    unfold Endmarked.rejectState Endmarked.acceptState at hstateEq
    omega
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, rfl⟩ :=
      (Endmarked.mem_embeddedEpsilonRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right) _).mp
        (by simpa [Endmarked.rightEpsilonRows] using hright)
    have hrowState := Endmarked.rightPending_lt_stateCount
      (q := sourceState) left right hstored
    have hstateEq :
        Endmarked.rightPending left right alphabet sourceState stored =
          Endmarked.rejectState left right alphabet := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hreject] using hmatch.1
    have hrightLt := Endmarked.rightPending_lt_acceptState
      (q := sourceState) left right hstored
    unfold Endmarked.rejectState at hstateEq
    omega
  · obtain ⟨rowTop, hrowTop, rfl⟩ := List.mem_map.mp hdrain
    have hrowState := Endmarked.acceptState_lt_stateCount left right alphabet
    have hstateEq : Endmarked.acceptState left right alphabet =
        Endmarked.rejectState left right alphabet := by
      simpa [endmarkedPairMachine_numStates,
        Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hreject] using hmatch.1
    simp [Endmarked.rejectState] at hstateEq

@[expose] public def leftEndmarkedConfiguration
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    DPDAToFirstOrder.Configuration :=
  (Endmarked.leftStart, [Endmarked.bottom])

@[expose] public def rightEndmarkedConfiguration
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    DPDAToFirstOrder.Configuration :=
  (Endmarked.rightStart, [Endmarked.bottom])

/-! ## Finite epsilon-return summaries -/

namespace Popping

private theorem iterate_reaches_predicate_within_card
    {α : Type} [Fintype α] [DecidableEq α]
    (next : α → α) (stop : α → Prop) [DecidablePred stop]
    (start : α) (hreaches : ∃ n, stop (next^[n] start)) :
    ∃ n < Fintype.card α, stop (next^[n] start) := by
  classical
  let first := Nat.find hreaches
  let orbit : List α := List.ofFn fun i : Fin (first + 1) =>
    next^[i.val] start
  have horbit : orbit.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j heq
    have heq' := heq
    simp only [orbit, List.getElem_ofFn] at heq'
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · let gap := first - j.val
      have hjle : j.val ≤ first := by
        simpa [orbit, Nat.lt_succ_iff] using j.isLt
      have hjgap : j.val + gap = first := Nat.add_sub_of_le hjle
      have higap : i.val + gap < first := by omega
      have hiter : next^[i.val + gap] start =
          next^[j.val + gap] start := by
        have happly := congrArg (next^[gap]) heq'
        calc
          next^[i.val + gap] start =
              next^[gap] (next^[i.val] start) := by
            rw [Nat.add_comm, Function.iterate_add_apply]
          _ = next^[gap] (next^[j.val] start) := happly
          _ = next^[j.val + gap] start := by
            rw [Nat.add_comm, Function.iterate_add_apply]
      have hearlier : stop (next^[i.val + gap] start) := by
        rw [hiter, hjgap]
        exact Nat.find_spec hreaches
      have hminimal := Nat.find_min' hreaches hearlier
      exact (Nat.not_le_of_lt higap) hminimal
    · let gap := first - i.val
      have hile : i.val ≤ first := by
        simpa [orbit, Nat.lt_succ_iff] using i.isLt
      have higap : i.val + gap = first := Nat.add_sub_of_le hile
      have hjgap : j.val + gap < first := by omega
      have hiter : next^[j.val + gap] start =
          next^[i.val + gap] start := by
        have happly := congrArg (next^[gap]) heq'.symm
        calc
          next^[j.val + gap] start =
              next^[gap] (next^[j.val] start) := by
            rw [Nat.add_comm, Function.iterate_add_apply]
          _ = next^[gap] (next^[i.val] start) := happly
          _ = next^[i.val + gap] start := by
            rw [Nat.add_comm, Function.iterate_add_apply]
      have hearlier : stop (next^[j.val + gap] start) := by
        rw [hiter, higap]
        exact Nat.find_spec hreaches
      have hminimal := Nat.find_min' hreaches hearlier
      exact (Nat.not_le_of_lt hjgap) hminimal
  have hbound : first < Fintype.card α := by
    have hlength := horbit.length_le_card
    simpa [orbit, Nat.succ_le_iff] using hlength
  exact ⟨first, hbound, Nat.find_spec hreaches⟩

public abbrev ReturnTable := List (Option ℕ)

@[expose] public def headIndex (machine : EncodedDPDA Action)
    (q Z : ℕ) : ℕ :=
  (q % machine.numStates) * machine.numStackSymbols +
    Z % machine.numStackSymbols

@[expose] public def returnAt (machine : EncodedDPDA Action)
    (table : ReturnTable) (q Z : ℕ) : Option ℕ :=
  table[headIndex machine q Z]?.join

/-!
Returnability of one head is a finite P-automaton summary query.  The auxiliary
code erases input rows but retains exactly the source epsilon table and sizes.
The queried target is made the sole rejecting control; the least summary edge
`(q,Z,target)` is then exactly a computation which pops `Z` and returns in that
control state.  This reuses the executable saturation already proved for DPDA
universality rather than introducing a second fixpoint implementation.
-/

@[expose] public def epsilonOnlyTargetMachine
    (machine : EncodedDPDA Action) (target : ℕ) : EncodedDPDA Unit :=
  (machine.numStates - 1,
    machine.numStackSymbols - 1,
    0,
    0,
    (List.range machine.numStates).filter fun state =>
      decide (state ≠ target % machine.numStates),
    [],
    machine.epsilonRows)

@[expose] public def headReturnsCode (machine : EncodedDPDA Action)
    (q Z target : ℕ) : Bool :=
  decide ((q % machine.numStates, Z % machine.numStackSymbols,
    target % machine.numStates) ∈
      (epsilonOnlyTargetMachine machine target).leastSummaryRelation)

@[simp] public theorem epsilonOnlyTargetMachine_numStates
    (machine : EncodedDPDA Action) (target : ℕ) :
    (epsilonOnlyTargetMachine machine target).numStates = machine.numStates := by
  unfold epsilonOnlyTargetMachine EncodedDPDA.numStates
  omega

@[simp] public theorem epsilonOnlyTargetMachine_numStackSymbols
    (machine : EncodedDPDA Action) (target : ℕ) :
    (epsilonOnlyTargetMachine machine target).numStackSymbols =
      machine.numStackSymbols := by
  unfold epsilonOnlyTargetMachine EncodedDPDA.numStackSymbols
  change machine.numStackSymbols - 1 + 1 = machine.numStackSymbols
  have hpos := machine.numStackSymbols_pos
  omega

@[simp] public theorem epsilonOnlyTargetMachine_epsilonRows
    (machine : EncodedDPDA Action) (target : ℕ) :
    (epsilonOnlyTargetMachine machine target).epsilonRows =
      machine.epsilonRows := rfl

@[simp] public theorem epsilonOnlyTargetMachine_effectiveEpsilonRows
    (machine : EncodedDPDA Action) (target : ℕ) :
    (epsilonOnlyTargetMachine machine target).effectiveEpsilonRows =
      (epsilonOnlyTargetMachine machine 0).effectiveEpsilonRows := by
  unfold EncodedDPDA.effectiveEpsilonRows
  simp only [epsilonOnlyTargetMachine_epsilonRows]
  congr 1

@[simp] public theorem epsilonOnlyTargetMachine_effectiveEpsilonRows_source
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (target : ℕ) :
    (epsilonOnlyTargetMachine machine target).effectiveEpsilonRows =
      machine.effectiveEpsilonRows := by
  unfold EncodedDPDA.effectiveEpsilonRows
  simp only [epsilonOnlyTargetMachine_epsilonRows]
  congr 1

@[simp] public theorem epsilonOnlyTargetMachine_effectiveInputRows
    (machine : EncodedDPDA Action) (target : ℕ) :
    (epsilonOnlyTargetMachine machine target).effectiveInputRows = [] := by
  unfold EncodedDPDA.effectiveInputRows
  change List.filter _ [] = []
  rfl

/-- Semantic spelling of a head return.  The input-erased auxiliary has no
input rows, so these are precisely source epsilon computations. -/
@[expose] public def RawHeadReturns (machine : EncodedDPDA Action)
    (q Z target : ℕ) : Prop :=
  let query := epsilonOnlyTargetMachine machine target
  query.RawErasedReaches
    (q % machine.numStates, [Z % machine.numStackSymbols])
    (target % machine.numStates, [])

private theorem epsilonOnly_rawErasedStep_iff
    (machine : EncodedDPDA Action) (target : ℕ)
    (x y : ℕ × List ℕ) :
    (epsilonOnlyTargetMachine machine target).RawErasedStep x y ↔
      (epsilonOnlyTargetMachine machine 0).RawErasedStep x y := by
  constructor <;> intro hstep
  · cases hstep with
    | @epsilon row suffix hrow =>
        have hrow' : row ∈
            (epsilonOnlyTargetMachine machine 0).effectiveEpsilonRows := by
          simpa using hrow
        simpa [EncodedDPDA.normalizedEpsilonSource,
          EncodedDPDA.normalizedEpsilonTop,
          EncodedDPDA.normalizedEpsilonTarget,
          EncodedDPDA.normalizedEpsilonReplacement] using
            (EncodedDPDA.RawErasedStep.epsilon
              (c := epsilonOnlyTargetMachine machine 0)
              (suffix := suffix) hrow')
    | @input row suffix hrow =>
        simp at hrow
  · cases hstep with
    | @epsilon row suffix hrow =>
        have hrow' : row ∈
            (epsilonOnlyTargetMachine machine target).effectiveEpsilonRows := by
          simpa using hrow
        simpa [EncodedDPDA.normalizedEpsilonSource,
          EncodedDPDA.normalizedEpsilonTop,
          EncodedDPDA.normalizedEpsilonTarget,
          EncodedDPDA.normalizedEpsilonReplacement] using
            (EncodedDPDA.RawErasedStep.epsilon
              (c := epsilonOnlyTargetMachine machine target)
              (suffix := suffix) hrow')
    | @input row suffix hrow =>
        simp at hrow

public theorem rawHeadReturns_iff_canonical
    (machine : EncodedDPDA Action) (q Z target : ℕ) :
    RawHeadReturns machine q Z target ↔
      (epsilonOnlyTargetMachine machine 0).RawErasedReaches
        (q % machine.numStates, [Z % machine.numStackSymbols])
        (target % machine.numStates, []) := by
  unfold RawHeadReturns
  constructor <;> intro hreach
  · exact Relation.ReflTransGen.mono
      (fun x y hstep =>
        (epsilonOnly_rawErasedStep_iff machine target x y).mp hstep)
      hreach
  · exact Relation.ReflTransGen.mono
      (fun x y hstep =>
        (epsilonOnly_rawErasedStep_iff machine target x y).mpr hstep)
      hreach

private theorem rawErasedStep_suffix {T : Type} [Fintype T] [DecidableEq T]
    {machine : EncodedDPDA T} {x y : ℕ × List ℕ}
    (hstep : machine.RawErasedStep x y) (suffix : List ℕ) :
    machine.RawErasedStep (x.1, x.2 ++ suffix) (y.1, y.2 ++ suffix) := by
  cases hstep with
  | @epsilon row rest hrow =>
      simpa [List.append_assoc] using
        (EncodedDPDA.RawErasedStep.epsilon (c := machine)
          (suffix := rest ++ suffix) hrow)
  | @input row rest hrow =>
      simpa [List.append_assoc] using
        (EncodedDPDA.RawErasedStep.input (c := machine)
          (suffix := rest ++ suffix) hrow)

public theorem rawErasedReaches_suffix {T : Type} [Fintype T] [DecidableEq T]
    {machine : EncodedDPDA T} {x y : ℕ × List ℕ}
    (hreach : machine.RawErasedReaches x y) (suffix : List ℕ) :
    machine.RawErasedReaches
      (x.1, x.2 ++ suffix) (y.1, y.2 ++ suffix) := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (rawErasedStep_suffix hstep suffix)

public theorem rawEpsilonStep_of_selectedEpsilon?
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (replacement suffix : List ℕ)
    (hstep : selectedEpsilon? machine q Z = some (target, replacement)) :
    (epsilonOnlyTargetMachine machine 0).RawErasedStep
      (q % machine.numStates, Z % machine.numStackSymbols :: suffix)
      (target, replacement ++ suffix) := by
  unfold selectedEpsilon? at hstep
  obtain ⟨row, hfind, hout⟩ := Option.map_eq_some_iff.mp hstep
  have hrow : row ∈ machine.epsilonRows :=
    List.mem_of_find?_eq_some hfind
  have hmatch := List.find?_some hfind
  simp only [decide_eq_true_eq] at hmatch
  have hpredicate : machine.sameEpsilonKey row =
      (fun candidate : EpsilonRow => decide
        (candidate.1 % machine.numStates = q % machine.numStates ∧
          candidate.2.1 % machine.numStackSymbols =
            Z % machine.numStackSymbols)) := by
    funext candidate
    simp [EncodedDPDA.sameEpsilonKey,
      EncodedDPDA.normalizedEpsilonSource,
      EncodedDPDA.normalizedEpsilonTop, hmatch]
  have heffective : row ∈ machine.effectiveEpsilonRows := by
    rw [EncodedDPDA.effectiveEpsilonRows, List.mem_filter]
    refine ⟨hrow, ?_⟩
    rw [decide_eq_true_eq, hpredicate]
    exact hfind
  have hquery : row ∈
      (epsilonOnlyTargetMachine machine 0).effectiveEpsilonRows := by
    simpa using heffective
  have hraw := EncodedDPDA.RawErasedStep.epsilon
    (c := epsilonOnlyTargetMachine machine 0)
    (suffix := suffix) hquery
  have hout' :
      (row.2.2.1 % machine.numStates,
          row.2.2.2.map fun Y => Y % machine.numStackSymbols) =
        (target, replacement) := by
    simpa using hout
  rcases Prod.mk.inj hout' with ⟨htarget, hreplacement⟩
  simpa [EncodedDPDA.normalizedEpsilonSource,
    EncodedDPDA.normalizedEpsilonTop,
    EncodedDPDA.normalizedEpsilonTarget,
    EncodedDPDA.normalizedEpsilonReplacement, hmatch.1, hmatch.2,
    htarget, hreplacement] using hraw

@[expose] public def decodeEpsilonConf [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (configuration : ℕ × List ℕ) :
    DPDA.EpsilonConf (Fin machine.numStates) (Fin machine.numStackSymbols) :=
  (machine.state configuration.1, machine.replacement configuration.2)

public theorem selectedEpsilon?_eq_none_iff_epsilonStable
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z : ℕ) (suffix : List ℕ) :
    selectedEpsilon? machine q Z = none ↔
      machine.toDPDA.EpsilonStable
        (decodeEpsilonConf machine (q, Z :: suffix)) := by
  change selectedEpsilon? machine q Z = none ↔
    machine.toDPDA.epsilon_transition
      (machine.state q) (machine.stackSymbol Z) = none
  rw [selectedEpsilon?_eq_epsilonStep?]
  unfold DPDAToFirstOrder.Machine.epsilonStep?
  rw [Option.map_eq_none_iff]
  rfl

public theorem rawCanonicalEpsilonStep_toDPDA
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) {x y : ℕ × List ℕ}
    (hstep : (epsilonOnlyTargetMachine machine 0).RawErasedStep x y) :
    machine.toDPDA.EpsilonStep
      (decodeEpsilonConf machine x) (decodeEpsilonConf machine y) := by
  cases hstep with
  | @epsilon row suffix hrow =>
      have hsource : row ∈ machine.effectiveEpsilonRows := by
        simpa using hrow
      refine ⟨machine.replacement
          (machine.normalizedEpsilonReplacement row),
        machine.effectiveEpsilonRow_transition hsource, ?_⟩
      simp [decodeEpsilonConf, EncodedDPDA.replacement,
        EncodedDPDA.normalizedEpsilonReplacement, List.map_append]
  | @input row suffix hrow =>
      simp at hrow

public theorem rawCanonicalEpsilonReaches_toDPDA
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) {x y : ℕ × List ℕ}
    (hreach : (epsilonOnlyTargetMachine machine 0).RawErasedReaches x y) :
    machine.toDPDA.EpsilonReaches
      (decodeEpsilonConf machine x) (decodeEpsilonConf machine y) := by
  exact Relation.ReflTransGen.lift (decodeEpsilonConf machine)
    (fun _ _ hstep => rawCanonicalEpsilonStep_toDPDA machine hstep) hreach

public theorem selectedInput?_toPDA_step
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z : ℕ) (action : Action)
    (target : ℕ) (replacement suffix : List ℕ) (word : List Action)
    (hstep : selectedInput? machine q action Z = some (target, replacement)) :
    @PDA.Reaches₁ _ _ _ _ _ _ machine.toDPDA.toPDA
      ⟨machine.state q, action :: word,
        machine.stackSymbol Z :: machine.replacement suffix⟩
      ⟨machine.state target, word,
        machine.replacement (replacement ++ suffix)⟩ := by
  have hselected := hstep
  rw [selectedInput?_eq_inputStep?] at hselected
  cases hepsilon : DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
  | some output => simp [hepsilon] at hselected
  | none =>
      simp only [hepsilon, Option.isSome_none, Bool.false_eq_true, if_false]
        at hselected
      unfold DPDAToFirstOrder.Machine.inputStep? at hselected
      obtain ⟨decoded, hlookup, hout⟩ := Option.map_eq_some_iff.mp hselected
      have hnormalized := selectedInput?_normalized
        machine q action Z target replacement hstep
      have htarget : decoded.1 = machine.state target := by
        apply Fin.ext
        have hvalue := congrArg Prod.fst hout
        change decoded.1.val = target at hvalue
        exact hvalue.trans hnormalized.1.symm
      have hreplacement : decoded.2 = machine.replacement replacement := by
        apply Fin.val_injective.list_map
        have houtStack : decoded.2.map Fin.val = replacement := by
          simpa using congrArg Prod.snd hout
        rw [houtStack]
        simpa [EncodedDPDA.replacement, List.map_map, Function.comp_def]
          using hnormalized.2.symm
      have hepsilonLookup : machine.epsilonLookup
          (machine.state q) (machine.stackSymbol Z) = none := by
        unfold DPDAToFirstOrder.Machine.epsilonStep? at hepsilon
        exact (Option.map_eq_none_iff.mp hepsilon)
      have htransition : machine.toDPDA.transition
          (machine.state q) action (machine.stackSymbol Z) =
            some (machine.state target, machine.replacement replacement) := by
        change (if (machine.epsilonLookup (machine.state q)
            (machine.stackSymbol Z)).isSome then none
          else machine.inputLookup (machine.state q) action
            (machine.stackSymbol Z)) = _
        rw [hepsilonLookup]
        simp only [Option.isSome_none, Bool.false_eq_true, if_false, hlookup]
        exact congrArg some (Prod.ext htarget hreplacement)
      change ⟨machine.state target, word,
          machine.replacement (replacement ++ suffix)⟩ ∈
        PDA.step (pda := machine.toDPDA.toPDA)
          ⟨machine.state q, action :: word,
            machine.stackSymbol Z :: machine.replacement suffix⟩
      simp [PDA.step, DPDA.toPDA, htransition,
        hepsilonLookup, EncodedDPDA.replacement, List.map_append]

private theorem summaryPath_from_sink
    {machine : EncodedDPDA Unit} {R : List EncodedDPDA.SummaryTriple}
    (hR : ∀ t ∈ R,
      t.2.2 = machine.sinkIndex ∨
        (t.1 < machine.numStates ∧ t.2.1 < machine.numStackSymbols ∧
          t.2.2 < machine.numStates ∧
          machine.RawErasedReaches (t.1, [t.2.1]) (t.2.2, [])))
    {p : ℕ} (hp : p = machine.sinkIndex)
    {gamma : List ℕ} {r : ℕ}
    (hpath : EncodedDPDA.RawSummaryPath machine R p gamma r) :
    r = machine.sinkIndex := by
  induction hpath with
  | nil => exact hp
  | @cons source middle _ Z gamma _ hedge _ ih =>
      subst source
      rcases hR _ hedge with hmiddle | hsemantic
      · have hmiddle' : middle = machine.sinkIndex := by simpa using hmiddle
        subst middle
        exact ih rfl
      · simp [EncodedDPDA.sinkIndex] at hsemantic

private theorem summaryPath_returns
    {machine : EncodedDPDA Unit} {R : List EncodedDPDA.SummaryTriple}
    (hR : ∀ t ∈ R,
      t.2.2 = machine.sinkIndex ∨
        (t.1 < machine.numStates ∧ t.2.1 < machine.numStackSymbols ∧
          t.2.2 < machine.numStates ∧
          machine.RawErasedReaches (t.1, [t.2.1]) (t.2.2, [])))
    {p r : ℕ} {gamma : List ℕ}
    (hpath : EncodedDPDA.RawSummaryPath machine R p gamma r)
    (hr : r < machine.numStates) :
    machine.RawErasedReaches
      (p, gamma.map fun Z => Z % machine.numStackSymbols) (r, []) := by
  induction hpath with
  | nil => exact Relation.ReflTransGen.refl
  | @cons p middle r Z gamma hmiddle hedge htail ih =>
      have hmiddleNotSink : middle ≠ machine.sinkIndex := by
        intro hmiddleSink
        subst middle
        have hrSink := summaryPath_from_sink hR rfl htail
        subst r
        simp [EncodedDPDA.sinkIndex] at hr
      have hmiddleState : middle < machine.numStates := by
        have hle : middle ≤ machine.numStates := by
          simpa [EncodedDPDA.pStateCount] using Nat.le_of_lt_succ hmiddle
        exact lt_of_le_of_ne hle hmiddleNotSink
      have hhead : machine.RawErasedReaches
          (p, [Z % machine.numStackSymbols]) (middle, []) := by
        rcases hR _ hedge with hSink | hsemantic
        · exact (hmiddleNotSink hSink).elim
        · simpa [Nat.mod_mod] using hsemantic.2.2.2
      have hheadSuffix := rawErasedReaches_suffix hhead
        (gamma.map fun Y => Y % machine.numStackSymbols)
      exact Relation.ReflTransGen.trans (by simpa using hheadSuffix) (ih hr)

private theorem leastSummary_sound_return
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (hmem : (q % machine.numStates, Z % machine.numStackSymbols,
      target % machine.numStates) ∈
        (epsilonOnlyTargetMachine machine target).leastSummaryRelation) :
    RawHeadReturns machine q Z target := by
  classical
  let query := epsilonOnlyTargetMachine machine target
  let semantic : List EncodedDPDA.SummaryTriple :=
    query.allSummaryTriples.filter fun t => decide
      (t.2.2 = query.sinkIndex ∨
        (t.1 < query.numStates ∧ t.2.1 < query.numStackSymbols ∧
          t.2.2 < query.numStates ∧
          query.RawErasedReaches (t.1, [t.2.1]) (t.2.2, [])))
  have hsemantic : ∀ t ∈ semantic,
      t.2.2 = query.sinkIndex ∨
        (t.1 < query.numStates ∧ t.2.1 < query.numStackSymbols ∧
          t.2.2 < query.numStates ∧
          query.RawErasedReaches (t.1, [t.2.1]) (t.2.2, [])) := by
    intro t ht
    exact of_decide_eq_true (List.mem_filter.mp ht).2
  have hclosed : EncodedDPDA.RawSummaryClosed query semantic := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      apply List.mem_filter.mpr
      refine ⟨(List.mem_filter.mp ht).1, ?_⟩
      rw [decide_eq_true_eq]
      have hbase := of_decide_eq_true (List.mem_filter.mp ht).2
      rcases hbase with hsink | hreject
      · exact Or.inl hsink.2
      · exact Or.inl hreject.2
    · intro row hrow r hr hpath
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · rw [EncodedDPDA.mem_allSummaryTriples_iff]
        exact ⟨(Nat.mod_lt _ query.numStates_pos).trans
            (by simp [EncodedDPDA.pStateCount]),
          Nat.mod_lt _ query.numStackSymbols_pos, hr⟩
      · rw [decide_eq_true_eq]
        by_cases hrsink : r = query.sinkIndex
        · exact Or.inl hrsink
        · right
          have hrState : r < query.numStates := by
            have hle : r ≤ query.numStates := by
              simpa [EncodedDPDA.pStateCount] using Nat.le_of_lt_succ hr
            exact lt_of_le_of_ne hle hrsink
          have hreplacement := summaryPath_returns hsemantic hpath hrState
          refine ⟨Nat.mod_lt _ query.numStates_pos,
            Nat.mod_lt _ query.numStackSymbols_pos, hrState, ?_⟩
          have hfirst : query.RawErasedStep
              (query.normalizedEpsilonSource row,
                [query.normalizedEpsilonTop row])
              (query.normalizedEpsilonTarget row,
                query.normalizedEpsilonReplacement row) := by
            simpa using (EncodedDPDA.RawErasedStep.epsilon (c := query)
              (suffix := []) hrow)
          have hreplacement' : query.RawErasedReaches
              (query.normalizedEpsilonTarget row,
                query.normalizedEpsilonReplacement row) (r, []) := by
            simpa [EncodedDPDA.normalizedEpsilonReplacement, List.map_map,
              Function.comp_def, Nat.mod_mod] using hreplacement
          exact Relation.ReflTransGen.head hfirst hreplacement'
    · intro row hrow
      simp [query, epsilonOnlyTargetMachine_effectiveInputRows] at hrow
  have hin := EncodedDPDA.leastSummaryRelation_minimal query hclosed hmem
  have hmeaning := hsemantic _ hin
  rcases hmeaning with hsink | hreturn
  · have hlt := Nat.mod_lt target machine.numStates_pos
    simp [query, EncodedDPDA.sinkIndex] at hsink
    omega
  · simpa [RawHeadReturns, query] using hreturn.2.2.2

private theorem leastSummaryPath_of_rawReturn
    {machine : EncodedDPDA Unit}
    (hinput : machine.effectiveInputRows = [])
    {x : ℕ × List ℕ} {target : ℕ}
    (hreach : machine.RawErasedReaches x (target, [])) :
    EncodedDPDA.RawSummaryPath machine machine.leastSummaryRelation
      x.1 x.2 target := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact .nil target
  | @head x y hstep hrest ih =>
      cases hstep with
      | @epsilon row suffix hrow =>
          obtain ⟨middle, hreplacement, hsuffix⟩ :=
            EncodedDPDA.RawSummaryPath.of_append_left ih
          have hmiddle : middle < machine.pStateCount :=
            hreplacement.end_lt
              ((Nat.mod_lt _ machine.numStates_pos).trans
                (by simp [EncodedDPDA.pStateCount]))
          refine .cons hmiddle ?_ hsuffix
          simpa [EncodedDPDA.normalizedEpsilonTop, Nat.mod_mod] using
            (EncodedDPDA.leastSummaryRelation_closed machine).2.1
              row hrow middle hmiddle hreplacement
      | @input row suffix hrow =>
          rw [hinput] at hrow
          cases hrow

private theorem leastSummary_complete_return
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (hreturn : RawHeadReturns machine q Z target) :
    (q % machine.numStates, Z % machine.numStackSymbols,
      target % machine.numStates) ∈
        (epsilonOnlyTargetMachine machine target).leastSummaryRelation := by
  let query := epsilonOnlyTargetMachine machine target
  have hpath : EncodedDPDA.RawSummaryPath query query.leastSummaryRelation
      (q % machine.numStates) [Z % machine.numStackSymbols]
      (target % machine.numStates) := by
    have hreach : query.RawErasedReaches
        (q % machine.numStates, [Z % machine.numStackSymbols])
        (target % machine.numStates, []) := by
      simpa [RawHeadReturns, query] using hreturn
    exact leastSummaryPath_of_rawReturn
      (machine := query)
      (epsilonOnlyTargetMachine_effectiveInputRows machine target) hreach
  cases hpath with
  | @cons _ middle _ top tail _ hedge htail =>
      cases htail with
      | nil =>
          simpa [query, EncodedDPDA.normalizedEpsilonTop,
            Nat.mod_mod] using hedge

public theorem headReturnsCode_eq_true_iff
    (machine : EncodedDPDA Action) (q Z target : ℕ) :
    headReturnsCode machine q Z target = true ↔
      RawHeadReturns machine q Z target := by
  rw [headReturnsCode, decide_eq_true_eq]
  exact ⟨leastSummary_sound_return machine q Z target,
    leastSummary_complete_return machine q Z target⟩

@[expose] public def returnTable (machine : EncodedDPDA Action) : ReturnTable :=
  (List.range (machine.numStates * machine.numStackSymbols)).map fun head =>
    (List.range machine.numStates).find? fun target =>
      headReturnsCode machine
        (head / machine.numStackSymbols)
        (head % machine.numStackSymbols) target

public theorem returnAt_returnTable (machine : EncodedDPDA Action)
    (q Z : ℕ) :
    returnAt machine (returnTable machine) q Z =
      (List.range machine.numStates).find? fun target =>
        headReturnsCode machine (q % machine.numStates)
          (Z % machine.numStackSymbols) target := by
  have hq := Nat.mod_lt q machine.numStates_pos
  have hZ := Nat.mod_lt Z machine.numStackSymbols_pos
  have hhead : headIndex machine q Z <
      machine.numStates * machine.numStackSymbols := by
    have hwithin :
        (q % machine.numStates) * machine.numStackSymbols +
            Z % machine.numStackSymbols <
          (q % machine.numStates + 1) * machine.numStackSymbols := by
      simpa [Nat.succ_mul] using Nat.add_lt_add_left hZ
        ((q % machine.numStates) * machine.numStackSymbols)
    exact hwithin.trans_le (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hq))
  have hdiv : ((q % machine.numStates) * machine.numStackSymbols +
      Z % machine.numStackSymbols) / machine.numStackSymbols =
        q % machine.numStates := by
    rw [Nat.mul_comm (q % machine.numStates),
      Nat.mul_add_div machine.numStackSymbols_pos,
      Nat.div_eq_of_lt hZ, Nat.add_zero]
  have hmod : ((q % machine.numStates) * machine.numStackSymbols +
      Z % machine.numStackSymbols) % machine.numStackSymbols =
        Z % machine.numStackSymbols := by
    exact Nat.mul_add_mod_of_lt hZ
  have hhead' : (q % machine.numStates) * machine.numStackSymbols +
      Z % machine.numStackSymbols <
        machine.numStates * machine.numStackSymbols := by
    simpa [headIndex] using hhead
  unfold returnAt returnTable headIndex
  rw [List.getElem?_map, List.getElem?_range hhead']
  simp only [Option.map_some, Option.join_some, hdiv, hmod]

public theorem returnAt_some_rawHeadReturns
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (hreturn : returnAt machine (returnTable machine) q Z = some target) :
    RawHeadReturns machine q Z target := by
  rw [returnAt_returnTable] at hreturn
  have hcode := List.find?_some hreturn
  rw [headReturnsCode_eq_true_iff] at hcode
  simpa [RawHeadReturns, Nat.mod_mod] using hcode

public theorem returnAt_eq_none_iff
    (machine : EncodedDPDA Action) (q Z : ℕ) :
    returnAt machine (returnTable machine) q Z = none ↔
      ∀ target < machine.numStates,
        ¬ RawHeadReturns machine q Z target := by
  constructor
  · intro hnone target htarget hreturns
    rw [returnAt_returnTable] at hnone
    rw [List.find?_eq_none] at hnone
    have hfalse := hnone target (List.mem_range.mpr htarget)
    have htrue : headReturnsCode machine (q % machine.numStates)
        (Z % machine.numStackSymbols) target = true := by
      rw [headReturnsCode_eq_true_iff]
      simpa [RawHeadReturns, Nat.mod_mod] using hreturns
    simp [htrue] at hfalse
  · intro hnone
    cases hreturn : returnAt machine (returnTable machine) q Z with
    | none => rfl
    | some target =>
        have hreturns := returnAt_some_rawHeadReturns machine q Z target hreturn
        have htarget : target < machine.numStates := by
          rw [returnAt_returnTable] at hreturn
          exact List.mem_range.mp (List.mem_of_find?_eq_some hreturn)
        exact (hnone target htarget hreturns).elim

@[expose] public def normalizeStack (machine : EncodedDPDA Action)
    (stack : List ℕ) : List ℕ :=
  stack.map fun Z => Z % machine.numStackSymbols

public theorem normalizeStack_eq_self_of_lt
    (machine : EncodedDPDA Action) (stack : List ℕ)
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    normalizeStack machine stack = stack := by
  induction stack with
  | nil => rfl
  | cons Z stack ih =>
      have hZ := hstack Z (by simp)
      have hrest : ∀ X ∈ stack, X < machine.numStackSymbols := by
        intro X hX
        exact hstack X (by simp [hX])
      change Z % machine.numStackSymbols :: normalizeStack machine stack =
        Z :: stack
      rw [Nat.mod_eq_of_lt hZ, ih hrest]

public theorem lt_of_normalizeStack_eq_self
    (machine : EncodedDPDA Action) (stack : List ℕ)
    (hnormalized : normalizeStack machine stack = stack) :
    ∀ Z ∈ stack, Z < machine.numStackSymbols := by
  induction stack with
  | nil => simp
  | cons head tail ih =>
      change head % machine.numStackSymbols :: normalizeStack machine tail =
        head :: tail at hnormalized
      have hhead : head % machine.numStackSymbols = head :=
        List.cons.inj hnormalized |>.1
      have htail : normalizeStack machine tail = tail :=
        List.cons.inj hnormalized |>.2
      intro Z hZ
      simp only [List.mem_cons] at hZ
      rcases hZ with rfl | hZ
      · rw [← hhead]
        exact Nat.mod_lt _ machine.numStackSymbols_pos
      · exact ih htail Z hZ

public theorem returnAt_some_rawEpsilonReaches_suffix
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (hreturn : returnAt machine (returnTable machine) q Z = some target)
    (suffix : List ℕ) :
    (epsilonOnlyTargetMachine machine 0).RawErasedReaches
      (q % machine.numStates,
        Z % machine.numStackSymbols :: suffix)
      (target % machine.numStates, suffix) := by
  have hhead := (rawHeadReturns_iff_canonical machine q Z target).mp
    (returnAt_some_rawHeadReturns machine q Z target hreturn)
  simpa using rawErasedReaches_suffix hhead suffix

/-- Result of skipping a maximal prefix of already-returnable heads. -/
public inductive SkipResult where
  | returned (state : ℕ)
  | blocked (state symbol : ℕ) (suffix : List ℕ)
  deriving DecidableEq

@[expose] public def skipReturnable (machine : EncodedDPDA Action)
    (table : ReturnTable) : ℕ → List ℕ → SkipResult
  | q, [] => .returned (q % machine.numStates)
  | q, Z :: replacement =>
      match returnAt machine table q Z with
      | some target => skipReturnable machine table target replacement
      | none => .blocked (q % machine.numStates)
          (Z % machine.numStackSymbols)
          (replacement.map fun Y => Y % machine.numStackSymbols)

public theorem skipReturnable_spec (machine : EncodedDPDA Action) :
    ∀ (q : ℕ) (stack : List ℕ),
      match skipReturnable machine (returnTable machine) q stack with
      | .returned target =>
          (epsilonOnlyTargetMachine machine 0).RawErasedReaches
            (q % machine.numStates, normalizeStack machine stack)
            (target, [])
      | .blocked target top suffix =>
          (epsilonOnlyTargetMachine machine 0).RawErasedReaches
              (q % machine.numStates, normalizeStack machine stack)
              (target, top :: suffix) ∧
            returnAt machine (returnTable machine) target top = none := by
  intro q stack
  induction stack generalizing q with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons Z stack ih =>
      cases hreturn : returnAt machine (returnTable machine) q Z with
      | none =>
          simp only [skipReturnable, hreturn, normalizeStack, List.map_cons]
          exact ⟨Relation.ReflTransGen.refl, by
            simpa [returnAt, headIndex, Nat.mod_mod] using hreturn⟩
      | some target =>
          have hprefix := returnAt_some_rawEpsilonReaches_suffix
            machine q Z target hreturn (normalizeStack machine stack)
          cases hresult : skipReturnable machine (returnTable machine)
              target stack with
          | returned finalTarget =>
              have hrest := ih target
              rw [hresult] at hrest
              simp only [skipReturnable, hreturn, normalizeStack,
                List.map_cons, hresult]
              exact hprefix.trans hrest
          | blocked stableState stableTop stableSuffix =>
              have hrest := ih target
              rw [hresult] at hrest
              simp only [skipReturnable, hreturn, normalizeStack,
                List.map_cons, hresult]
              exact ⟨hprefix.trans hrest.1, hrest.2⟩

public theorem skipReturnable_normalized (machine : EncodedDPDA Action) :
    ∀ (q : ℕ) (stack : List ℕ),
      match skipReturnable machine (returnTable machine) q stack with
      | .returned target => target < machine.numStates
      | .blocked target top suffix =>
          target < machine.numStates ∧
            top < machine.numStackSymbols ∧
            normalizeStack machine suffix = suffix := by
  intro q stack
  induction stack generalizing q with
  | nil => exact Nat.mod_lt _ machine.numStates_pos
  | cons Z stack ih =>
      cases hreturn : returnAt machine (returnTable machine) q Z with
      | none =>
          simp only [skipReturnable, hreturn]
          exact ⟨Nat.mod_lt _ machine.numStates_pos,
            Nat.mod_lt _ machine.numStackSymbols_pos, by
              simp [normalizeStack, List.map_map, Function.comp_def,
                Nat.mod_mod]⟩
      | some target =>
          simpa only [skipReturnable, hreturn] using ih target

private theorem pdaReachesIn_trans_exact
    {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    {machine : PDA Q T S} {n m : ℕ} {a b c : PDA.conf machine}
    (hab : machine.ReachesIn n a b) (hbc : machine.ReachesIn m b c) :
    machine.ReachesIn (n + m) a c := by
  induction hbc with
  | refl => simpa using hab
  | @step m b middle c hprefix hlast ih =>
      simpa [Nat.add_assoc] using PDA.ReachesIn.step (ih hab) hlast

private theorem pdaReachesIn_split_exact
    {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    {machine : PDA Q T S} {n m : ℕ} {a c : PDA.conf machine}
    (hreach : machine.ReachesIn (n + m) a c) :
    ∃ b, machine.ReachesIn n a b ∧ machine.ReachesIn m b c := by
  induction m generalizing c with
  | zero =>
      refine ⟨c, ?_, PDA.ReachesIn.refl c⟩
      simpa using hreach
  | succ m ih =>
      rw [Nat.add_succ] at hreach
      obtain ⟨before, hbefore, hlast⟩ :=
        PDA.reachesIn_iff_split_last.mpr hreach
      obtain ⟨middle, hprefix, hsuffix⟩ := ih hbefore
      refine ⟨middle, hprefix, ?_⟩
      exact PDA.ReachesIn.step hsuffix
        (PDA.reaches₁_iff_reachesIn_one.mpr hlast)

private theorem pdaReaches_eq_self_of_epsilonStable
    {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    {machine : DPDA Q T S} {configuration : DPDA.EpsilonConf Q S}
    {target : PDA.conf machine.toPDA}
    (hstable : machine.EpsilonStable configuration)
    (hreach : @PDA.Reaches Q T S _ _ _ machine.toPDA
      ⟨configuration.1, [], configuration.2⟩ target) :
    target = ⟨configuration.1, [], configuration.2⟩ := by
  rw [PDA.reaches_iff_reachesIn] at hreach
  obtain ⟨steps, hsteps⟩ := hreach
  cases steps with
  | zero => exact (PDA.reachesIn_zero hsteps).symm
  | succ steps =>
      obtain ⟨middle, hfirst, _⟩ :=
        PDA.reachesIn_iff_split_first.mpr hsteps
      have hinput : middle.input = [] := by
        obtain ⟨consumed, hconsumed⟩ :=
          PDA.decreasing_input (PDA.reaches_of_reachesIn hfirst)
        exact (List.append_eq_nil_iff.mp hconsumed.symm).2
      rcases middle with ⟨middleState, middleInput, middleStack⟩
      change middleInput = [] at hinput
      subst middleInput
      have hfirst' : @PDA.Reaches₁ Q T S _ _ _ machine.toPDA
          ⟨configuration.1, [], configuration.2⟩
          ⟨middleState, [], middleStack⟩ :=
        PDA.reaches₁_iff_reachesIn_one.mpr hfirst
      have hepsilon := DPDA.epsilonStep_of_toPDA_empty_step
        hfirst'
      exact (DPDA.not_epsilonStep_of_stable machine hstable hepsilon).elim

/-- A blocked macro unfolding performs at least one genuine epsilon step. -/
private theorem blockedMacro_reachesIn
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action)
    (q Z target : ℕ) (replacement : List ℕ)
    (blockedState blockedTop : ℕ) (blockedSuffix suffix : List ℕ)
    (hepsilon : selectedEpsilon? machine q Z = some (target, replacement))
    (hskip : skipReturnable machine (returnTable machine) target replacement =
      .blocked blockedState blockedTop blockedSuffix) :
    ∃ steps, 0 < steps ∧
      @PDA.ReachesIn _ _ _ _ _ _ machine.toDPDA.toPDA steps
        ⟨(decodeEpsilonConf machine (q, Z :: suffix)).1, [],
          (decodeEpsilonConf machine (q, Z :: suffix)).2⟩
        ⟨(decodeEpsilonConf machine
          (blockedState, blockedTop :: (blockedSuffix ++ suffix))).1, [],
          (decodeEpsilonConf machine
            (blockedState, blockedTop :: (blockedSuffix ++ suffix))).2⟩ := by
  have hraw := rawEpsilonStep_of_selectedEpsilon?
    machine q Z target replacement (normalizeStack machine suffix) hepsilon
  have hstep := rawCanonicalEpsilonStep_toDPDA machine hraw
  have hstepPDA := DPDA.epsilonStep_toPDA (w := ([] : List Action)) hstep
  have hskipSpec := skipReturnable_spec machine target replacement
  rw [hskip] at hskipSpec
  have hskipLift := rawErasedReaches_suffix hskipSpec.1
    (normalizeStack machine suffix)
  have houtputNormalized :=
    selectedEpsilon?_normalized machine q Z target replacement hepsilon
  have hskipRaw :
      (epsilonOnlyTargetMachine machine 0).RawErasedReaches
        (target, replacement ++ normalizeStack machine suffix)
        (blockedState,
          blockedTop :: (blockedSuffix ++ normalizeStack machine suffix)) := by
    simpa [normalizeStack, List.map_append, houtputNormalized.1,
      houtputNormalized.2] using hskipLift
  have hskipEpsilon := rawCanonicalEpsilonReaches_toDPDA machine hskipRaw
  have hskipPDA := DPDA.epsilonReaches_toPDA
    (w := ([] : List Action)) hskipEpsilon
  rw [PDA.reaches_iff_reachesIn] at hskipPDA
  obtain ⟨restSteps, hrestSteps⟩ := hskipPDA
  refine ⟨1 + restSteps, by omega, ?_⟩
  have hcombined := pdaReachesIn_trans_exact
    (PDA.reaches₁_iff_reachesIn_one.mp hstepPDA) hrestSteps
  simpa [decodeEpsilonConf, normalizeStack, EncodedDPDA.replacement,
    EncodedDPDA.state, EncodedDPDA.stackSymbol, List.map_append,
    List.map_map, Function.comp_def, Nat.mod_mod] using hcombined

public abbrev NormalizedHead (machine : EncodedDPDA Action) :=
  Fin machine.numStates × Fin machine.numStackSymbols

@[expose] public def headStable (machine : EncodedDPDA Action)
    (head : NormalizedHead machine) : Prop :=
  selectedEpsilon? machine head.1.val head.2.val = none

@[expose] public def nextHead (machine : EncodedDPDA Action)
    (head : NormalizedHead machine) : NormalizedHead machine :=
  match selectedEpsilon? machine head.1.val head.2.val with
  | none => head
  | some out =>
      match skipReturnable machine (returnTable machine) out.1 out.2 with
      | .returned _ => head
      | .blocked target top _ =>
          (machine.state target, machine.stackSymbol top)

private theorem eventuallyHeadStable_of_reachesIn
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    ∀ (steps : ℕ) (q Z : ℕ) (suffix : List ℕ)
        (final : DPDA.EpsilonConf (Fin machine.numStates)
          (Fin machine.numStackSymbols)),
      @PDA.ReachesIn _ _ _ _ _ _ machine.toDPDA.toPDA steps
          ⟨(decodeEpsilonConf machine (q, Z :: suffix)).1, [],
            (decodeEpsilonConf machine (q, Z :: suffix)).2⟩
          ⟨final.1, [], final.2⟩ →
        machine.toDPDA.EpsilonStable final →
        returnAt machine (returnTable machine) q Z = none →
        ∃ unfoldings,
          headStable machine
            ((nextHead machine)^[unfoldings]
              (machine.state q, machine.stackSymbol Z)) := by
  intro steps
  induction steps using Nat.strong_induction_on with
  | h steps ih =>
      intro q Z suffix final hreach hfinalStable hreturn
      cases hepsilon : selectedEpsilon? machine q Z with
      | none =>
          refine ⟨0, ?_⟩
          simpa [headStable, EncodedDPDA.state, EncodedDPDA.stackSymbol,
            selectedEpsilon?_normalized_key] using hepsilon
      | some output =>
          rcases output with ⟨target, replacement⟩
          cases hskip : skipReturnable machine (returnTable machine)
              target replacement with
          | returned returnedState =>
              have hraw := rawEpsilonStep_of_selectedEpsilon?
                machine q Z target replacement [] hepsilon
              have hskipSpec := skipReturnable_spec machine target replacement
              rw [hskip] at hskipSpec
              have houtputNormalized := selectedEpsilon?_normalized
                machine q Z target replacement hepsilon
              have hreturnedLt := skipReturnable_normalized
                machine target replacement
              rw [hskip] at hreturnedLt
              have hreturns : RawHeadReturns machine q Z returnedState := by
                rw [rawHeadReturns_iff_canonical]
                have hrest :
                    (epsilonOnlyTargetMachine machine 0).RawErasedReaches
                      (target, replacement) (returnedState, []) := by
                  simpa [normalizeStack, houtputNormalized.1,
                    houtputNormalized.2] using hskipSpec
                have hreach := (Relation.ReflTransGen.single hraw).trans
                  (by simpa using hrest)
                simpa [Nat.mod_eq_of_lt hreturnedLt] using hreach
              exact ((returnAt_eq_none_iff machine q Z).mp hreturn
                returnedState hreturnedLt hreturns).elim
          | blocked blockedState blockedTop blockedSuffix =>
              obtain ⟨macroSteps, hmacroPositive, hmacro⟩ :=
                blockedMacro_reachesIn machine q Z target replacement
                  blockedState blockedTop blockedSuffix suffix hepsilon hskip
              have hskipSpec := skipReturnable_spec machine target replacement
              rw [hskip] at hskipSpec
              have hnext :
                  nextHead machine (machine.state q, machine.stackSymbol Z) =
                    (machine.state blockedState,
                      machine.stackSymbol blockedTop) := by
                simp only [nextHead, EncodedDPDA.state,
                  EncodedDPDA.stackSymbol]
                rw [selectedEpsilon?_normalized_key]
                simp only [hepsilon]
                rw [hskip]
              by_cases hmacroLe : macroSteps ≤ steps
              · have hsum : macroSteps + (steps - macroSteps) = steps :=
                  Nat.add_sub_of_le hmacroLe
                have hreach' :
                    @PDA.ReachesIn _ _ _ _ _ _ machine.toDPDA.toPDA
                      (macroSteps + (steps - macroSteps))
                      ⟨(decodeEpsilonConf machine (q, Z :: suffix)).1, [],
                        (decodeEpsilonConf machine (q, Z :: suffix)).2⟩
                      ⟨final.1, [], final.2⟩ := by
                  simpa [hsum] using hreach
                obtain ⟨middle, hprefix, hsuffix⟩ :=
                  pdaReachesIn_split_exact hreach'
                have hmiddle : middle =
                    ⟨(decodeEpsilonConf machine
                        (blockedState,
                          blockedTop :: (blockedSuffix ++ suffix))).1, [],
                      (decodeEpsilonConf machine
                        (blockedState,
                          blockedTop :: (blockedSuffix ++ suffix))).2⟩ :=
                  machine.toDPDA.toPDA_reachesIn_deterministic hprefix hmacro
                subst middle
                have hsmaller : steps - macroSteps < steps := by omega
                obtain ⟨unfoldings, hunfoldings⟩ := ih
                  (steps - macroSteps) hsmaller blockedState blockedTop
                  (blockedSuffix ++ suffix) final hsuffix hfinalStable hskipSpec.2
                refine ⟨unfoldings + 1, ?_⟩
                simpa [Function.iterate_succ_apply, hnext] using hunfoldings
              · have hstepsLe : steps ≤ macroSteps :=
                  Nat.le_of_lt (Nat.lt_of_not_ge hmacroLe)
                have hafter :=
                  machine.toDPDA.toPDA_reachesIn_prefix_of_le
                    hstepsLe hreach hmacro
                have hsame := pdaReaches_eq_self_of_epsilonStable
                  hfinalStable hafter
                have hconfEq :
                    decodeEpsilonConf machine
                        (blockedState,
                          blockedTop :: (blockedSuffix ++ suffix)) = final := by
                  apply Prod.ext
                  · exact congrArg PDA.conf.state hsame
                  · exact congrArg PDA.conf.stack hsame
                have hblockedStable : machine.toDPDA.EpsilonStable
                    (decodeEpsilonConf machine
                      (blockedState,
                        blockedTop :: (blockedSuffix ++ suffix))) := by
                  simpa [hconfEq] using hfinalStable
                have hblockedHead :
                    selectedEpsilon? machine blockedState blockedTop = none :=
                  (selectedEpsilon?_eq_none_iff_epsilonStable machine
                    blockedState blockedTop
                    (blockedSuffix ++ suffix)).mpr hblockedStable
                refine ⟨1, ?_⟩
                rw [Function.iterate_one, hnext]
                change selectedEpsilon? machine
                  (blockedState % machine.numStates)
                  (blockedTop % machine.numStackSymbols) = none
                rw [selectedEpsilon?_normalized_key]
                exact hblockedHead

public abbrev ExposedHead := ℕ × ℕ × List ℕ

@[expose] public def exposeHeadAux (machine : EncodedDPDA Action)
    (table : ReturnTable) : ℕ → ExposedHead → Option ExposedHead
  | 0, _ => none
  | fuel + 1, (q, Z, suffix) =>
      match selectedEpsilon? machine q Z with
      | none => some (q % machine.numStates,
          Z % machine.numStackSymbols, normalizeStack machine suffix)
      | some out =>
          match skipReturnable machine table out.1 out.2 with
          | .returned _ => none
          | .blocked target top replacement =>
              exposeHeadAux machine table fuel
                (target, top, replacement ++ suffix)

public theorem exposeHeadAux_some_normalized
    (machine : EncodedDPDA Action) :
    ∀ (fuel q Z : ℕ) (suffix : List ℕ) (target top : ℕ)
        (rest : List ℕ),
      exposeHeadAux machine (returnTable machine) fuel (q, Z, suffix) =
          some (target, top, rest) →
        target < machine.numStates ∧
          top < machine.numStackSymbols ∧
          normalizeStack machine rest = rest := by
  intro fuel
  induction fuel with
  | zero =>
      intro q Z suffix target top rest hresult
      simp [exposeHeadAux] at hresult
  | succ fuel ih =>
      intro q Z suffix target top rest hresult
      simp only [exposeHeadAux] at hresult
      cases hepsilon : selectedEpsilon? machine q Z with
      | none =>
          simp only [hepsilon, Option.some.injEq, Prod.mk.injEq] at hresult
          rcases hresult with ⟨rfl, rfl, rfl⟩
          refine ⟨Nat.mod_lt _ machine.numStates_pos,
            Nat.mod_lt _ machine.numStackSymbols_pos, ?_⟩
          simp [normalizeStack, List.map_map, Function.comp_def, Nat.mod_mod]
      | some output =>
          simp only [hepsilon] at hresult
          cases hskip : skipReturnable machine (returnTable machine)
              output.1 output.2 with
          | returned state => simp [hskip] at hresult
          | blocked blockedState blockedTop blockedSuffix =>
              simp only [hskip] at hresult
              exact ih blockedState blockedTop (blockedSuffix ++ suffix)
                target top rest hresult

public theorem exposeHeadAux_some_spec
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    ∀ (fuel q Z : ℕ) (suffix : List ℕ) (target top : ℕ)
        (rest : List ℕ),
      exposeHeadAux machine (returnTable machine) fuel (q, Z, suffix) =
          some (target, top, rest) →
        (epsilonOnlyTargetMachine machine 0).RawErasedReaches
            (q % machine.numStates,
              normalizeStack machine (Z :: suffix))
            (target, top :: rest) ∧
          selectedEpsilon? machine target top = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro q Z suffix target top rest hresult
      simp [exposeHeadAux] at hresult
  | succ fuel ih =>
      intro q Z suffix target top rest hresult
      simp only [exposeHeadAux] at hresult
      cases hepsilon : selectedEpsilon? machine q Z with
      | none =>
          simp only [hepsilon, Option.some.injEq, Prod.mk.injEq] at hresult
          rcases hresult with ⟨htarget, htop, hrest⟩
          subst target
          subst top
          subst rest
          refine ⟨Relation.ReflTransGen.refl, ?_⟩
          simpa [selectedEpsilon?_normalized_key] using hepsilon
      | some out =>
          rcases out with ⟨next, replacement⟩
          simp only [hepsilon] at hresult
          cases hskip : skipReturnable machine (returnTable machine)
              next replacement with
          | returned returnedState =>
              simp [hskip] at hresult
          | blocked blockedState blockedTop blockedSuffix =>
              simp only [hskip] at hresult
              have hrecursive := ih blockedState blockedTop
                (blockedSuffix ++ suffix) target top rest hresult
              have hraw := rawEpsilonStep_of_selectedEpsilon?
                machine q Z next replacement (normalizeStack machine suffix)
                hepsilon
              have hskipSpec := skipReturnable_spec machine next replacement
              rw [hskip] at hskipSpec
              have hskipNormalized :=
                skipReturnable_normalized machine next replacement
              rw [hskip] at hskipNormalized
              rcases hskipNormalized with
                ⟨hblockedState, hblockedTop, hblockedSuffix⟩
              have hskipLift := rawErasedReaches_suffix hskipSpec.1
                (normalizeStack machine suffix)
              have houtputNormalized :=
                selectedEpsilon?_normalized machine q Z next replacement hepsilon
              have hprefix :
                  (epsilonOnlyTargetMachine machine 0).RawErasedReaches
                    (q % machine.numStates,
                      normalizeStack machine (Z :: suffix))
                    (blockedState,
                      blockedTop ::
                        (blockedSuffix ++ normalizeStack machine suffix)) := by
                have hrawReach := Relation.ReflTransGen.single hraw
                exact hrawReach.trans (by
                  simpa [normalizeStack, List.map_append,
                    houtputNormalized.1, houtputNormalized.2]
                    using hskipLift)
              have hrecursive' :
                  (epsilonOnlyTargetMachine machine 0).RawErasedReaches
                    (blockedState,
                      blockedTop ::
                        (blockedSuffix ++ normalizeStack machine suffix))
                    (target, top :: rest) := by
                have hblockedSuffix' :
                    blockedSuffix.map
                        (fun Z => Z % machine.numStackSymbols) =
                      blockedSuffix := by
                  simpa [normalizeStack] using hblockedSuffix
                simpa [normalizeStack, List.map_append,
                  Nat.mod_eq_of_lt hblockedState,
                  Nat.mod_eq_of_lt hblockedTop,
                  hblockedSuffix'] using hrecursive.1
              exact ⟨hprefix.trans hrecursive', hrecursive.2⟩

public theorem exposeHeadAux_normalized_key
    (machine : EncodedDPDA Action) :
    ∀ (fuel q Z : ℕ) (suffix : List ℕ),
      exposeHeadAux machine (returnTable machine) fuel
          (q % machine.numStates, Z % machine.numStackSymbols, suffix) =
        exposeHeadAux machine (returnTable machine) fuel (q, Z, suffix) := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
      intro q Z suffix
      simp only [exposeHeadAux]
      rw [selectedEpsilon?_normalized_key]
      cases hepsilon : selectedEpsilon? machine q Z with
      | none => simp [Nat.mod_mod]
      | some out =>
          cases hskip : skipReturnable machine (returnTable machine)
              out.1 out.2 with
          | returned state => rfl
          | blocked target top replacement => rfl

public theorem exposeHeadAux_some_mono
    (machine : EncodedDPDA Action) :
    ∀ (fuel extra q Z : ℕ) (suffix : List ℕ) (result : ExposedHead),
      exposeHeadAux machine (returnTable machine) fuel (q, Z, suffix) =
          some result →
        exposeHeadAux machine (returnTable machine) (fuel + extra)
          (q, Z, suffix) = some result := by
  intro fuel
  induction fuel with
  | zero =>
      intro extra q Z suffix result hresult
      simp [exposeHeadAux] at hresult
  | succ fuel ih =>
      intro extra q Z suffix result hresult
      simp only [exposeHeadAux] at hresult
      rw [Nat.succ_add]
      simp only [exposeHeadAux]
      cases hepsilon : selectedEpsilon? machine q Z with
      | none =>
          simpa [hepsilon] using hresult
      | some out =>
          simp only [hepsilon] at hresult ⊢
          cases hskip : skipReturnable machine (returnTable machine)
              out.1 out.2 with
          | returned state => simp [hskip] at hresult
          | blocked target top replacement =>
              simp only [hskip] at hresult ⊢
              exact ih extra target top (replacement ++ suffix) result hresult

public theorem exposeHeadAux_some_of_iterate_stable
    (machine : EncodedDPDA Action) :
    ∀ (steps : ℕ) (head : NormalizedHead machine) (suffix : List ℕ),
      headStable machine ((nextHead machine)^[steps] head) →
        ∃ result, exposeHeadAux machine (returnTable machine) (steps + 1)
          (head.1.val, head.2.val, suffix) = some result := by
  intro steps
  induction steps with
  | zero =>
      intro head suffix hstable
      have hepsilon : selectedEpsilon? machine head.1.val head.2.val = none := by
        simpa [headStable] using hstable
      refine ⟨(head.1.val, head.2.val, normalizeStack machine suffix), ?_⟩
      simp [exposeHeadAux, hepsilon, Nat.mod_eq_of_lt head.1.isLt,
        Nat.mod_eq_of_lt head.2.isLt]
  | succ steps ih =>
      intro head suffix hstable
      cases hepsilon : selectedEpsilon? machine head.1.val head.2.val with
      | none =>
          refine ⟨(head.1.val, head.2.val, normalizeStack machine suffix), ?_⟩
          simp [exposeHeadAux, hepsilon, Nat.mod_eq_of_lt head.1.isLt,
            Nat.mod_eq_of_lt head.2.isLt]
      | some out =>
          rcases out with ⟨target, replacement⟩
          cases hskip : skipReturnable machine (returnTable machine)
              target replacement with
          | returned returnedState =>
              have hfixed : ∀ n, (nextHead machine)^[n] head = head := by
                intro n
                induction n with
                | zero => rfl
                | succ n hn =>
                    rw [Function.iterate_succ_apply]
                    have hone : nextHead machine head = head := by
                      simp [nextHead, hepsilon, hskip]
                    rw [hone]
                    exact hn
              have : headStable machine head := by
                simpa [hfixed] using hstable
              simp [headStable, hepsilon] at this
          | blocked blockedState blockedTop blockedSuffix =>
              let next : NormalizedHead machine :=
                (machine.state blockedState,
                  machine.stackSymbol blockedTop)
              have hnext : nextHead machine head = next := by
                simp [nextHead, hepsilon, hskip, next]
              have hstable' :
                  headStable machine ((nextHead machine)^[steps] next) := by
                simpa [Function.iterate_succ_apply, hnext] using hstable
              obtain ⟨result, hresult⟩ :=
                ih next (blockedSuffix ++ suffix) hstable'
              refine ⟨result, ?_⟩
              have hresult' := hresult
              change exposeHeadAux machine (returnTable machine) (steps + 1)
                (blockedState % machine.numStates,
                  blockedTop % machine.numStackSymbols,
                  blockedSuffix ++ suffix) = some result at hresult'
              rw [exposeHeadAux_normalized_key machine (steps + 1)
                blockedState blockedTop (blockedSuffix ++ suffix)] at hresult'
              simpa [exposeHeadAux, hepsilon, hskip, Nat.add_assoc,
                next, EncodedDPDA.state, EncodedDPDA.stackSymbol]
                using hresult'

@[expose] public def exposeHead (machine : EncodedDPDA Action)
    (q Z : ℕ) : Option ExposedHead :=
  exposeHeadAux machine (returnTable machine)
    (machine.numStates * machine.numStackSymbols)
    (q % machine.numStates, Z % machine.numStackSymbols, [])

public theorem exposeHead_some_of_eventually_stable
    (machine : EncodedDPDA Action) (q Z : ℕ)
    (hreaches : ∃ steps,
      headStable machine
        ((nextHead machine)^[steps]
          (machine.state q, machine.stackSymbol Z))) :
    ∃ result, exposeHead machine q Z = some result := by
  letI : DecidablePred (headStable machine) := fun head =>
    inferInstanceAs (Decidable
      (selectedEpsilon? machine head.1.val head.2.val = none))
  have hbounded := iterate_reaches_predicate_within_card
    (nextHead machine) (headStable machine)
    (machine.state q, machine.stackSymbol Z) hreaches
  obtain ⟨steps, hsteps, hstable⟩ := hbounded
  have hcard : Fintype.card (NormalizedHead machine) =
      machine.numStates * machine.numStackSymbols := by
    simp [NormalizedHead]
  rw [hcard] at hsteps
  obtain ⟨result, hresult⟩ := exposeHeadAux_some_of_iterate_stable
    machine steps (machine.state q, machine.stackSymbol Z) [] hstable
  have hresult' : exposeHeadAux machine (returnTable machine) (steps + 1)
      (q % machine.numStates, Z % machine.numStackSymbols, []) =
        some result := by
    simpa [EncodedDPDA.state, EncodedDPDA.stackSymbol] using hresult
  have hle : steps + 1 ≤
      machine.numStates * machine.numStackSymbols :=
    Nat.succ_le_of_lt hsteps
  obtain ⟨extra, htotal⟩ := Nat.exists_eq_add_of_le hle
  refine ⟨result, ?_⟩
  unfold exposeHead
  rw [htotal]
  exact exposeHeadAux_some_mono machine (steps + 1) extra
    (q % machine.numStates) (Z % machine.numStackSymbols) [] result hresult'

public theorem exposeHead_some_of_epsilonStopsAt
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z : ℕ) (suffix : List ℕ)
    (hstops : ∃ final, machine.toDPDA.EpsilonStopsAt
      (decodeEpsilonConf machine (q, Z :: suffix)) final)
    (hreturn : returnAt machine (returnTable machine) q Z = none) :
    ∃ result, exposeHead machine q Z = some result := by
  obtain ⟨final, hreach, hstable⟩ := hstops
  have hreachPDA := DPDA.epsilonReaches_toPDA
    (w := ([] : List Action)) hreach
  rw [PDA.reaches_iff_reachesIn] at hreachPDA
  obtain ⟨steps, hsteps⟩ := hreachPDA
  have heventual := eventuallyHeadStable_of_reachesIn machine steps
    q Z suffix final hsteps hstable hreturn
  exact exposeHead_some_of_eventually_stable machine q Z heventual

public theorem exposeHead_some_normalized
    (machine : EncodedDPDA Action) (q Z target top : ℕ)
    (suffix : List ℕ)
    (hresult : exposeHead machine q Z = some (target, top, suffix)) :
    target < machine.numStates ∧
      top < machine.numStackSymbols ∧
      normalizeStack machine suffix = suffix := by
  exact exposeHeadAux_some_normalized machine
    (machine.numStates * machine.numStackSymbols)
    (q % machine.numStates) (Z % machine.numStackSymbols) []
    target top suffix (by simpa [exposeHead] using hresult)

public theorem exposeHead_some_spec
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z target top : ℕ)
    (suffix : List ℕ)
    (hresult : exposeHead machine q Z = some (target, top, suffix)) :
    (epsilonOnlyTargetMachine machine 0).RawErasedReaches
        (q % machine.numStates, [Z % machine.numStackSymbols])
        (target, top :: suffix) ∧
      selectedEpsilon? machine target top = none := by
  have hspec := exposeHeadAux_some_spec machine
    (machine.numStates * machine.numStackSymbols)
    (q % machine.numStates) (Z % machine.numStackSymbols) []
    target top suffix (by simpa [exposeHead] using hresult)
  simpa [normalizeStack] using hspec

@[expose] public def deadState (machine : EncodedDPDA Action) : ℕ :=
  machine.numStates

@[expose] public def poppingRows (machine : EncodedDPDA Action) :
    List EpsilonRow :=
  (List.range machine.numStates).flatMap fun q =>
    (List.range machine.numStackSymbols).filterMap fun Z =>
      (returnAt machine (returnTable machine) q Z).map fun target =>
        (q, Z, target, [])

public theorem mem_poppingRows_iff
    (machine : EncodedDPDA Action) (row : EpsilonRow) :
    row ∈ poppingRows machine ↔
      ∃ q < machine.numStates, ∃ Z < machine.numStackSymbols,
        ∃ target,
          returnAt machine (returnTable machine) q Z = some target ∧
            row = (q, Z, target, []) := by
  unfold poppingRows
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨q, hq, hrow⟩
    rw [List.mem_filterMap] at hrow
    obtain ⟨Z, hZ, hrow⟩ := hrow
    cases hreturn : returnAt machine (returnTable machine) q Z with
    | none => simp [hreturn] at hrow
    | some target =>
        simp [hreturn] at hrow
        subst row
        exact ⟨q, List.mem_range.mp hq, Z, List.mem_range.mp hZ,
          target, hreturn, rfl⟩
  · rintro ⟨q, hq, Z, hZ, target, hreturn, rfl⟩
    refine ⟨q, List.mem_range.mpr hq, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨Z, List.mem_range.mpr hZ, by simp [hreturn]⟩

@[expose] public def normalizedRow [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z : ℕ) (action : Action) :
    InputRow Action :=
  match exposeHead machine q Z with
  | some (stableState, stableTop, suffix) =>
      match selectedInput? machine stableState action stableTop with
      | some out => (q, action, Z, out.1, out.2 ++ suffix)
      | none => (q, action, Z, deadState machine, [Z])
  | none => (q, action, Z, deadState machine, [Z])

@[expose] public def macroStep? [DecidableEq Action]
    (machine : EncodedDPDA Action) (action : Action)
    (configuration : DPDAToFirstOrder.Configuration) :
    Option DPDAToFirstOrder.Configuration :=
  match skipReturnable machine (returnTable machine)
      configuration.1 configuration.2 with
  | .returned _ => none
  | .blocked state top suffix =>
      let row := normalizedRow machine state top action
      some (row.2.2.2.1, row.2.2.2.2 ++ suffix)

@[expose] public def normalizedInputRows [DecidableEq Action]
    (machine : EncodedDPDA Action) (alphabet : List Action) :
    List (InputRow Action) :=
  (List.range machine.numStates).flatMap fun q =>
    (List.range machine.numStackSymbols).flatMap fun Z =>
      match returnAt machine (returnTable machine) q Z with
      | some _ => []
      | none => alphabet.map (normalizedRow machine q Z)

@[expose] public def deadRows (machine : EncodedDPDA Action)
    (alphabet : List Action) : List (InputRow Action) :=
  (List.range machine.numStackSymbols).flatMap fun Z =>
    alphabet.map fun action =>
      (deadState machine, action, Z, deadState machine, [Z])

public theorem mem_normalizedInputRows_iff [DecidableEq Action]
    (machine : EncodedDPDA Action) (alphabet : List Action)
    (row : InputRow Action) :
    row ∈ normalizedInputRows machine alphabet ↔
      ∃ q < machine.numStates, ∃ Z < machine.numStackSymbols,
        returnAt machine (returnTable machine) q Z = none ∧
          ∃ action ∈ alphabet, row = normalizedRow machine q Z action := by
  unfold normalizedInputRows
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨q, hq, hrow⟩
    rw [List.mem_flatMap] at hrow
    obtain ⟨Z, hZ, hrow⟩ := hrow
    cases hreturn : returnAt machine (returnTable machine) q Z with
    | none =>
        simp only [hreturn] at hrow
        obtain ⟨action, haction, rfl⟩ := List.mem_map.mp hrow
        exact ⟨q, List.mem_range.mp hq, Z, List.mem_range.mp hZ,
          hreturn, action, haction, rfl⟩
    | some target => simp [hreturn] at hrow
  · rintro ⟨q, hq, Z, hZ, hreturn, action, haction, rfl⟩
    refine ⟨q, List.mem_range.mpr hq, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨Z, List.mem_range.mpr hZ, ?_⟩
    simp only [hreturn]
    exact List.mem_map.mpr ⟨action, haction, rfl⟩

public theorem mem_deadRows_iff
    (machine : EncodedDPDA Action) (alphabet : List Action)
    (row : InputRow Action) :
    row ∈ deadRows machine alphabet ↔
      ∃ Z < machine.numStackSymbols, ∃ action ∈ alphabet,
        row = (deadState machine, action, Z, deadState machine, [Z]) := by
  unfold deadRows
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨Z, hZ, hrow⟩
    obtain ⟨action, haction, rfl⟩ := List.mem_map.mp hrow
    exact ⟨Z, List.mem_range.mp hZ, action, haction, rfl⟩
  · rintro ⟨Z, hZ, action, haction, rfl⟩
    exact ⟨Z, List.mem_range.mpr hZ,
      List.mem_map.mpr ⟨action, haction, rfl⟩⟩

end Popping

/-- Raw finite popping/complete normalization. -/
@[expose] public def poppingCompleteMachine [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action) :
    EncodedDPDA Action :=
  (source.numStates,
    source.numStackSymbols - 1,
    source.initialIndex % source.numStates,
    source.startIndex % source.numStackSymbols,
    [],
    Popping.normalizedInputRows source alphabet ++
      Popping.deadRows source alphabet,
    Popping.poppingRows source)

@[simp] public theorem poppingCompleteMachine_numStates [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action) :
    (poppingCompleteMachine source alphabet).numStates =
      source.numStates + 1 := by
  rfl

@[simp] public theorem poppingCompleteMachine_numStackSymbols [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action) :
    (poppingCompleteMachine source alphabet).numStackSymbols =
      source.numStackSymbols := by
  simp [poppingCompleteMachine, EncodedDPDA.numStackSymbols,
    Nat.succ_pred_eq_of_pos source.numStackSymbols_pos]

private theorem epsilonStep?_isSome_of_rawRow [DecidableEq Action]
    {machine : EncodedDPDA Action} {row : EpsilonRow}
    (hrow : row ∈ machine.epsilonRows) :
    (DPDAToFirstOrder.Machine.epsilonStep? machine row.1 row.2.1).isSome = true := by
  unfold DPDAToFirstOrder.Machine.epsilonStep? EncodedDPDA.epsilonLookup
  have hfind : (machine.epsilonRows.find? fun r => decide
      (r.1 % machine.numStates = (machine.state row.1).val ∧
        r.2.1 % machine.numStackSymbols =
          (machine.stackSymbol row.2.1).val)).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨row, hrow, ?_⟩
    simp [EncodedDPDA.state, EncodedDPDA.stackSymbol]
  simpa only [Option.isSome_map] using hfind

private theorem inputStep?_isSome_of_rawRow [DecidableEq Action]
    {machine : EncodedDPDA Action} {row : InputRow Action}
    (hrow : row ∈ machine.inputRows) :
    (DPDAToFirstOrder.Machine.inputStep? machine
      row.1 row.2.1 row.2.2.1).isSome = true := by
  unfold DPDAToFirstOrder.Machine.inputStep? EncodedDPDA.inputLookup
  have hfind : (machine.inputRows.find? fun r => decide
      (r.1 % machine.numStates = (machine.state row.1).val ∧
        r.2.1 = row.2.1 ∧
        r.2.2.1 % machine.numStackSymbols =
          (machine.stackSymbol row.2.2.1).val)).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨row, hrow, ?_⟩
    simp [EncodedDPDA.state, EncodedDPDA.stackSymbol]
  simpa only [Option.isSome_map] using hfind

private theorem normalizedRow_mem [DecidableEq Action]
    {source : EncodedDPDA Action} {alphabet : List Action}
    {q Z : ℕ} (hq : q < source.numStates)
    (hZ : Z < source.numStackSymbols)
    (hreturn : Popping.returnAt source (Popping.returnTable source) q Z = none)
    {action : Action} (haction : action ∈ alphabet) :
    Popping.normalizedRow source q Z action ∈
      (poppingCompleteMachine source alphabet).inputRows := by
  apply List.mem_append_left
  unfold Popping.normalizedInputRows
  rw [List.mem_flatMap]
  refine ⟨q, List.mem_range.mpr hq, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨Z, List.mem_range.mpr hZ, ?_⟩
  simp only [hreturn]
  exact List.mem_map.mpr ⟨action, haction, rfl⟩

private theorem deadRow_mem [DecidableEq Action]
    {source : EncodedDPDA Action} {alphabet : List Action}
    {Z : ℕ} (hZ : Z < source.numStackSymbols)
    {action : Action} (haction : action ∈ alphabet) :
    (Popping.deadState source, action, Z, Popping.deadState source, [Z]) ∈
      (poppingCompleteMachine source alphabet).inputRows := by
  apply List.mem_append_right
  unfold Popping.deadRows
  rw [List.mem_flatMap]
  refine ⟨Z, List.mem_range.mpr hZ, ?_⟩
  exact List.mem_map.mpr ⟨action, haction, rfl⟩

private theorem poppingRow_mem [DecidableEq Action]
    {source : EncodedDPDA Action} {q Z target : ℕ}
    (hq : q < source.numStates) (hZ : Z < source.numStackSymbols)
    (hreturn : Popping.returnAt source (Popping.returnTable source) q Z =
      some target) :
    (q, Z, target, []) ∈
      (poppingCompleteMachine source ([] : List Action)).epsilonRows := by
  change (q, Z, target, []) ∈ Popping.poppingRows source
  unfold Popping.poppingRows
  rw [List.mem_flatMap]
  refine ⟨q, List.mem_range.mpr hq, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨Z, List.mem_range.mpr hZ, by simp [hreturn]⟩

private theorem poppingRows_empty [DecidableEq Action]
    {source : EncodedDPDA Action} {alphabet : List Action}
    {row : EpsilonRow}
    (hrow : row ∈ (poppingCompleteMachine source alphabet).epsilonRows) :
    row.2.2.2 = [] := by
  change row ∈ Popping.poppingRows source at hrow
  unfold Popping.poppingRows at hrow
  rw [List.mem_flatMap] at hrow
  obtain ⟨q, _, hrow⟩ := hrow
  rw [List.mem_filterMap] at hrow
  obtain ⟨Z, _, hrow⟩ := hrow
  cases hreturn : Popping.returnAt source (Popping.returnTable source) q Z with
  | none => simp [hreturn] at hrow
  | some target =>
      simp [hreturn] at hrow
      subst row
      rfl

public theorem poppingCompleteMachine_selectedEpsilon?_eq
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (hq : q < source.numStates)
    (hZ : Z < source.numStackSymbols) :
    selectedEpsilon? (poppingCompleteMachine source alphabet) q Z =
      (Popping.returnAt source (Popping.returnTable source) q Z).map
        fun target => (target, []) := by
  let normalized := poppingCompleteMachine source alphabet
  cases hselected : selectedEpsilon? normalized q Z with
  | none =>
      cases hreturn : Popping.returnAt source
          (Popping.returnTable source) q Z with
      | none => simp [hselected, hreturn]
      | some target =>
          have hmem : (q, Z, target, []) ∈ normalized.epsilonRows := by
            simpa [normalized, poppingCompleteMachine] using
              (poppingRow_mem (Action := Action) hq hZ hreturn)
          have hisSome := epsilonStep?_isSome_of_rawRow hmem
          rw [← selectedEpsilon?_eq_epsilonStep?] at hisSome
          simp [hselected] at hisSome
  | some output =>
      rcases output with ⟨outputState, outputStack⟩
      unfold selectedEpsilon? at hselected
      obtain ⟨row, hfind, hout⟩ := Option.map_eq_some_iff.mp hselected
      have hrow : row ∈ normalized.epsilonRows :=
        List.mem_of_find?_eq_some hfind
      have hmatch := List.find?_some hfind
      simp only [decide_eq_true_eq] at hmatch
      have hrow' : row ∈ Popping.poppingRows source := by
        simpa [normalized, poppingCompleteMachine] using hrow
      obtain ⟨rowState, hrowState, rowTop, hrowTop, rowTarget,
          hreturn, rfl⟩ :=
        (Popping.mem_poppingRows_iff source row).mp hrow'
      have hrowStateTarget : rowState < normalized.numStates := by
        simp [normalized]
        omega
      have hqTarget : q < normalized.numStates := by
        simp [normalized]
        omega
      have hstateEq : rowState = q := by
        simpa [Nat.mod_eq_of_lt hrowStateTarget,
          Nat.mod_eq_of_lt hqTarget] using hmatch.1
      have htopEq : rowTop = Z := by
        simpa [normalized, Nat.mod_eq_of_lt hrowTop,
          Nat.mod_eq_of_lt hZ] using hmatch.2
      subst rowState
      subst rowTop
      have hrowTarget : rowTarget < source.numStates := by
        have hreturns := Popping.returnAt_some_rawHeadReturns
          source q Z rowTarget hreturn
        rw [Popping.returnAt_returnTable] at hreturn
        exact List.mem_range.mp (List.mem_of_find?_eq_some hreturn)
      have hrowTargetTarget : rowTarget < source.numStates + 1 := by omega
      have hout' : (rowTarget, []) = (outputState, outputStack) := by
        simpa [normalized, Nat.mod_eq_of_lt hrowTargetTarget] using hout
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hout'
      simp [hreturn]

public theorem poppingCompleteMachine_epsilonStep?_eq
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (hq : q < source.numStates)
    (hZ : Z < source.numStackSymbols) :
    DPDAToFirstOrder.Machine.epsilonStep?
        (poppingCompleteMachine source alphabet) q Z =
      (Popping.returnAt source (Popping.returnTable source) q Z).map
        fun target => (target, []) := by
  rw [← selectedEpsilon?_eq_epsilonStep?]
  exact poppingCompleteMachine_selectedEpsilon?_eq
    source alphabet q Z hq hZ

public theorem poppingCompleteMachine_dead_epsilonStep?_eq_none
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action) (Z : ℕ) :
    DPDAToFirstOrder.Machine.epsilonStep?
        (poppingCompleteMachine source alphabet)
        (Popping.deadState source) Z = none := by
  rw [← selectedEpsilon?_eq_epsilonStep?]
  let normalized := poppingCompleteMachine source alphabet
  cases hselected : selectedEpsilon? normalized
      (Popping.deadState source) Z with
  | none => rfl
  | some output =>
      unfold selectedEpsilon? at hselected
      obtain ⟨row, hfind, _⟩ := Option.map_eq_some_iff.mp hselected
      have hrow : row ∈ Popping.poppingRows source := by
        have := List.mem_of_find?_eq_some hfind
        simpa [normalized, poppingCompleteMachine] using this
      obtain ⟨rowState, hrowState, rowTop, hrowTop, rowTarget,
          hreturn, rfl⟩ :=
        (Popping.mem_poppingRows_iff source row).mp hrow
      have hmatch := List.find?_some hfind
      simp only [decide_eq_true_eq] at hmatch
      have hfalse : rowState = source.numStates := by
        simpa [normalized, Popping.deadState, EncodedDPDA.state,
          Nat.mod_eq_of_lt (show rowState < source.numStates + 1 by omega),
          Nat.mod_eq_of_lt (show source.numStates < source.numStates + 1 by
            omega)] using hmatch.1
      omega

public theorem poppingCompleteMachine_stabilize_eq_skipReturnable
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action) :
    ∀ (q : ℕ) (stack : List ℕ),
      q < source.numStates →
      (∀ Z ∈ stack, Z < source.numStackSymbols) →
      DPDAToFirstOrder.stabilize (poppingCompleteMachine source alphabet)
          (q, stack) =
        match Popping.skipReturnable source (Popping.returnTable source)
            q stack with
        | .returned target => (target, [])
        | .blocked target top suffix => (target, top :: suffix) := by
  intro q stack hq hstack
  induction stack generalizing q with
  | nil =>
      simp [DPDAToFirstOrder.stabilize, Popping.skipReturnable,
        Nat.mod_eq_of_lt hq]
  | cons Z stack ih =>
      have hZ : Z < source.numStackSymbols := hstack Z (by simp)
      have hrest : ∀ X ∈ stack, X < source.numStackSymbols := by
        intro X hX
        exact hstack X (by simp [hX])
      have hepsilon := poppingCompleteMachine_epsilonStep?_eq
        source alphabet q Z hq hZ
      cases hreturn : Popping.returnAt source
          (Popping.returnTable source) q Z with
      | none =>
          have hnormalized := Popping.normalizeStack_eq_self_of_lt
            source stack hrest
          simp [DPDAToFirstOrder.stabilize, Popping.skipReturnable,
            hreturn, hepsilon, Nat.mod_eq_of_lt hq,
            Nat.mod_eq_of_lt hZ]
          exact hnormalized.symm
      | some target =>
          have htarget : target < source.numStates := by
            rw [Popping.returnAt_returnTable] at hreturn
            exact List.mem_range.mp (List.mem_of_find?_eq_some hreturn)
          simp only [DPDAToFirstOrder.stabilize, hepsilon, hreturn,
            Option.map_some, Popping.skipReturnable]
          exact ih target htarget hrest

private theorem normalizedRow_key [DecidableEq Action]
    (source : EncodedDPDA Action) (q Z : ℕ) (action : Action) :
    (Popping.normalizedRow source q Z action).1 = q ∧
      (Popping.normalizedRow source q Z action).2.1 = action ∧
      (Popping.normalizedRow source q Z action).2.2.1 = Z := by
  unfold Popping.normalizedRow
  split
  · split <;> simp
  · simp

private theorem normalizedRow_output_valid [DecidableEq Action]
    (source : EncodedDPDA Action) (q Z : ℕ) (action : Action)
    (hZ : Z < source.numStackSymbols) :
    (Popping.normalizedRow source q Z action).2.2.2.1 <
        source.numStates + 1 ∧
      ∀ X ∈ (Popping.normalizedRow source q Z action).2.2.2.2,
        X < source.numStackSymbols := by
  unfold Popping.normalizedRow
  cases hexpose : Popping.exposeHead source q Z with
  | none =>
      simp [hexpose, Popping.deadState, hZ]
  | some exposed =>
      rcases exposed with ⟨stableState, stableTop, stableSuffix⟩
      cases hinput : selectedInput? source stableState action stableTop with
      | none =>
          simp [hexpose, hinput, Popping.deadState, hZ]
      | some output =>
          rcases output with ⟨target, replacement⟩
          have hinputNormalized := selectedInput?_normalized source
            stableState action stableTop target replacement hinput
          have hexposeNormalized := Popping.exposeHead_some_normalized
            source q Z stableState stableTop stableSuffix hexpose
          have hreplacement : ∀ X ∈ replacement,
              X < source.numStackSymbols :=
            Popping.lt_of_normalizeStack_eq_self source replacement
              hinputNormalized.2
          have hsuffix : ∀ X ∈ stableSuffix,
              X < source.numStackSymbols :=
            Popping.lt_of_normalizeStack_eq_self source stableSuffix
              hexposeNormalized.2.2
          simp only [hexpose, hinput]
          constructor
          · rw [← hinputNormalized.1]
            exact lt_trans (Nat.mod_lt _ source.numStates_pos)
              (Nat.lt_succ_self source.numStates)
          · intro X hX
            rw [List.mem_append] at hX
            exact hX.elim (hreplacement X) (hsuffix X)

public theorem poppingCompleteMachine_inputStep?_eq_normalizedRow
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (q Z : ℕ) (action : Action)
    (hq : q < source.numStates) (hZ : Z < source.numStackSymbols)
    (hreturn : Popping.returnAt source (Popping.returnTable source) q Z = none)
    (haction : action ∈ alphabet) :
    DPDAToFirstOrder.Machine.inputStep?
        (poppingCompleteMachine source alphabet) q action Z =
      some ((Popping.normalizedRow source q Z action).2.2.2.1,
        (Popping.normalizedRow source q Z action).2.2.2.2) := by
  let normalized := poppingCompleteMachine source alphabet
  let expected := Popping.normalizedRow source q Z action
  cases hselected : DPDAToFirstOrder.Machine.inputStep?
      normalized q action Z with
  | none =>
      have hmem : expected ∈ normalized.inputRows := by
        exact normalizedRow_mem hq hZ hreturn haction
      have hisSome := inputStep?_isSome_of_rawRow hmem
      obtain ⟨hsource, hrowAction, htop⟩ :=
        normalizedRow_key source q Z action
      rw [hsource, hrowAction, htop, hselected] at hisSome
      simp at hisSome
  | some output =>
      rcases output with ⟨outputState, outputStack⟩
      unfold DPDAToFirstOrder.Machine.inputStep? at hselected
      obtain ⟨decodedOutput, hlookup, hout⟩ :=
        Option.map_eq_some_iff.mp hselected
      unfold EncodedDPDA.inputLookup at hlookup
      obtain ⟨row, hfind, hrowOut⟩ := Option.map_eq_some_iff.mp hlookup
      have hrow : row ∈ normalized.inputRows :=
        List.mem_of_find?_eq_some hfind
      have hmatch := List.find?_some hfind
      simp only [decide_eq_true_eq] at hmatch
      have hrowCases : row ∈ Popping.normalizedInputRows source alphabet ∨
          row ∈ Popping.deadRows source alphabet := by
        simpa [normalized, poppingCompleteMachine] using
          (List.mem_append.mp hrow)
      have hrowExpected : row = expected := by
        rcases hrowCases with hnormalized | hdead
        · obtain ⟨rowState, hrowState, rowTop, hrowTop, rowReturn,
              rowAction, _, rfl⟩ :=
            (Popping.mem_normalizedInputRows_iff source alphabet row).mp
              hnormalized
          have hkey := normalizedRow_key source rowState rowTop rowAction
          rw [hkey.1, hkey.2.1, hkey.2.2] at hmatch
          have hrowStateTarget : rowState < normalized.numStates := by
            simp [normalized]
            omega
          have hqTarget : q < normalized.numStates := by
            simp [normalized]
            omega
          have hrowStateTarget' : rowState < source.numStates + 1 := by
            simpa [normalized] using hrowStateTarget
          have hqTarget' : q < source.numStates + 1 := by
            simpa [normalized] using hqTarget
          have hstateEq : rowState = q := by
            simpa [EncodedDPDA.state, normalized,
              Nat.mod_eq_of_lt hrowStateTarget',
              Nat.mod_eq_of_lt hqTarget'] using hmatch.1
          have htopEq : rowTop = Z := by
            simpa [EncodedDPDA.stackSymbol, normalized,
              Nat.mod_eq_of_lt hrowTop,
              Nat.mod_eq_of_lt hZ] using hmatch.2.2
          have hactionEq : rowAction = action := hmatch.2.1
          subst rowState
          subst rowTop
          subst rowAction
          rfl
        · obtain ⟨rowTop, hrowTop, rowAction, _, rfl⟩ :=
            (Popping.mem_deadRows_iff source alphabet row).mp hdead
          have hfalse : source.numStates = q := by
            simpa [EncodedDPDA.state, normalized, Popping.deadState,
              Nat.mod_eq_of_lt (show source.numStates < source.numStates + 1 by
                omega),
              Nat.mod_eq_of_lt (show q < source.numStates + 1 by omega)]
              using hmatch.1
          omega
      subst row
      subst decodedOutput
      have hvalid := normalizedRow_output_valid source q Z action hZ
      have htargetBound : expected.2.2.2.1 < normalized.numStates := by
        simpa [expected, normalized] using hvalid.1
      have hstackBound : ∀ X ∈ expected.2.2.2.2,
          X < normalized.numStackSymbols := by
        simpa [expected, normalized] using hvalid.2
      have hstackNormalized := Popping.normalizeStack_eq_self_of_lt
        normalized expected.2.2.2.2 hstackBound
      have hstackMapped :
          expected.2.2.2.2.map (Fin.val ∘ normalized.stackSymbol) =
            expected.2.2.2.2 := by
        simpa [Popping.normalizeStack, EncodedDPDA.stackSymbol,
          Function.comp_def] using hstackNormalized
      have houtRaw :
          ((normalized.state expected.2.2.2.1).val,
            (normalized.replacement expected.2.2.2.2).map Fin.val) =
            (outputState, outputStack) := by
        simpa using hout
      obtain ⟨houtState, houtStack⟩ := Prod.mk.inj houtRaw
      have houtStack' :
          expected.2.2.2.2.map (Fin.val ∘ normalized.stackSymbol) =
            outputStack := by
        simpa [EncodedDPDA.replacement, List.map_map] using houtStack
      have hout' : (expected.2.2.2.1, expected.2.2.2.2) =
          (outputState, outputStack) := by
        apply Prod.ext
        · simpa [EncodedDPDA.state, Nat.mod_eq_of_lt htargetBound]
            using houtState
        · exact hstackMapped.symm.trans houtStack'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hout'
      rfl

public theorem poppingCompleteMachine_dead_inputStep?_eq
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (Z : ℕ) (action : Action) (hZ : Z < source.numStackSymbols)
    (haction : action ∈ alphabet) :
    DPDAToFirstOrder.Machine.inputStep?
        (poppingCompleteMachine source alphabet)
        (Popping.deadState source) action Z =
      some (Popping.deadState source, [Z]) := by
  let normalized := poppingCompleteMachine source alphabet
  cases hselected : DPDAToFirstOrder.Machine.inputStep? normalized
      (Popping.deadState source) action Z with
  | none =>
      have hmem : (Popping.deadState source, action, Z,
          Popping.deadState source, [Z]) ∈ normalized.inputRows := by
        exact deadRow_mem hZ haction
      have hisSome := inputStep?_isSome_of_rawRow hmem
      simp [hselected] at hisSome
  | some output =>
      rcases output with ⟨outputState, outputStack⟩
      unfold DPDAToFirstOrder.Machine.inputStep? at hselected
      obtain ⟨decodedOutput, hlookup, hout⟩ :=
        Option.map_eq_some_iff.mp hselected
      unfold EncodedDPDA.inputLookup at hlookup
      obtain ⟨row, hfind, hrowOut⟩ := Option.map_eq_some_iff.mp hlookup
      have hrow : row ∈ normalized.inputRows :=
        List.mem_of_find?_eq_some hfind
      have hmatch := List.find?_some hfind
      simp only [decide_eq_true_eq] at hmatch
      have hrowCases : row ∈ Popping.normalizedInputRows source alphabet ∨
          row ∈ Popping.deadRows source alphabet := by
        simpa [normalized, poppingCompleteMachine] using
          (List.mem_append.mp hrow)
      rcases hrowCases with hnormal | hdead
      · obtain ⟨rowState, hrowState, rowTop, hrowTop, rowReturn,
            rowAction, _, hrowEq⟩ :=
          (Popping.mem_normalizedInputRows_iff source alphabet row).mp hnormal
        subst row
        have hkey := normalizedRow_key source rowState rowTop rowAction
        rw [hkey.1, hkey.2.1, hkey.2.2] at hmatch
        have hfalse : rowState = source.numStates := by
          simpa [normalized, Popping.deadState, EncodedDPDA.state,
            Nat.mod_eq_of_lt (show rowState < source.numStates + 1 by omega),
            Nat.mod_eq_of_lt (show source.numStates < source.numStates + 1 by
              omega)] using hmatch.1
        omega
      · obtain ⟨rowTop, hrowTop, rowAction, _, rfl⟩ :=
          (Popping.mem_deadRows_iff source alphabet row).mp hdead
        have htopEq : rowTop = Z := by
          simpa [normalized, EncodedDPDA.stackSymbol,
            Nat.mod_eq_of_lt hrowTop, Nat.mod_eq_of_lt hZ] using hmatch.2.2
        subst rowTop
        have hactionEq : rowAction = action := hmatch.2.1
        subst rowAction
        subst decodedOutput
        have hout' : (Popping.deadState source, [Z]) =
            (outputState, outputStack) := by
          simpa [normalized, Popping.deadState, EncodedDPDA.state,
            EncodedDPDA.replacement, EncodedDPDA.stackSymbol,
            Nat.mod_eq_of_lt hZ] using hout
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hout'
        rfl

public theorem poppingCompleteMachine_dead_stabilize
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (stack : List ℕ) :
    DPDAToFirstOrder.stabilize (poppingCompleteMachine source alphabet)
      (Popping.deadState source, stack) =
        (Popping.deadState source, stack) := by
  cases stack with
  | nil => simp [DPDAToFirstOrder.stabilize]
  | cons Z stack =>
      have hepsilon := poppingCompleteMachine_dead_epsilonStep?_eq_none
        source alphabet Z
      simp [DPDAToFirstOrder.stabilize, hepsilon]

public theorem poppingCompleteMachine_dead_observableRun?
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet)
    (stack : List ℕ) (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols)
    (hne : stack ≠ []) (word : List Action) :
    DPDAToFirstOrder.observableRun? (poppingCompleteMachine source alphabet)
        word (Popping.deadState source, stack) =
      some (Popping.deadState source, stack) := by
  induction word with
  | nil => rfl
  | cons action word ih =>
      obtain ⟨Z, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hZ : Z < source.numStackSymbols := hstack Z (by simp)
      have hinput := poppingCompleteMachine_dead_inputStep?_eq
        source alphabet Z action hZ (haustive action)
      have hstabilize := poppingCompleteMachine_dead_stabilize
        source alphabet (Z :: tail)
      simp [DPDAToFirstOrder.observableRun?,
        DPDAToFirstOrder.observableStep?, hstabilize, hinput, ih]

public theorem poppingCompleteMachine_observableStep?_eq_macroStep?
    [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (q : ℕ) (stack : List ℕ) (action : Action)
    (hq : q < source.numStates)
    (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols)
    (haction : action ∈ alphabet) :
    DPDAToFirstOrder.observableStep?
        (poppingCompleteMachine source alphabet) action (q, stack) =
      Popping.macroStep? source action (q, stack) := by
  have hstabilize := poppingCompleteMachine_stabilize_eq_skipReturnable
    source alphabet q stack hq hstack
  cases hskip : Popping.skipReturnable source (Popping.returnTable source)
      q stack with
  | returned returnedState =>
      simp [DPDAToFirstOrder.observableStep?, Popping.macroStep?,
        hstabilize, hskip]
  | blocked blockedState blockedTop blockedSuffix =>
      have hskipSpec := Popping.skipReturnable_spec source q stack
      rw [hskip] at hskipSpec
      have hskipNormalized := Popping.skipReturnable_normalized source q stack
      rw [hskip] at hskipNormalized
      have hinput := poppingCompleteMachine_inputStep?_eq_normalizedRow
        source alphabet blockedState blockedTop action
        hskipNormalized.1 hskipNormalized.2.1 hskipSpec.2 haction
      simp [DPDAToFirstOrder.observableStep?, Popping.macroStep?,
        hstabilize, hskip, hinput]

public theorem macroStep?_sound_of_live
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action) (q : ℕ) (stack : List ℕ)
    (action : Action) (targetState : ℕ) (targetStack : List ℕ)
    (word : List Action)
    (hq : q < source.numStates)
    (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols)
    (hmacro : Popping.macroStep? source action (q, stack) =
      some (targetState, targetStack))
    (htarget : targetState < source.numStates) :
    @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
      ⟨source.state q, action :: word, source.replacement stack⟩
      ⟨source.state targetState, word, source.replacement targetStack⟩ := by
  cases hskip : Popping.skipReturnable source (Popping.returnTable source)
      q stack with
  | returned returnedState =>
      simp [Popping.macroStep?, hskip] at hmacro
  | blocked blockedState blockedTop blockedSuffix =>
      have hskipSpec := Popping.skipReturnable_spec source q stack
      rw [hskip] at hskipSpec
      have hskipNormalized := Popping.skipReturnable_normalized source q stack
      rw [hskip] at hskipNormalized
      cases hexpose : Popping.exposeHead source blockedState blockedTop with
      | none =>
          simp [Popping.macroStep?, Popping.normalizedRow, hskip, hexpose,
            Popping.deadState] at hmacro
          omega
      | some exposed =>
          rcases exposed with ⟨stableState, stableTop, stableSuffix⟩
          cases hinput : selectedInput? source stableState action stableTop with
          | none =>
              simp [Popping.macroStep?, Popping.normalizedRow, hskip,
                hexpose, hinput, Popping.deadState] at hmacro
              omega
          | some output =>
              rcases output with ⟨inputTarget, inputReplacement⟩
              have hmacroReduced := hmacro
              simp only [Popping.macroStep?, hskip,
                Popping.normalizedRow, hexpose, hinput,
                Option.some.injEq] at hmacroReduced
              have hmacro' :
                  (inputTarget,
                    (inputReplacement ++ stableSuffix) ++ blockedSuffix) =
                    (targetState, targetStack) := by
                exact hmacroReduced
              obtain ⟨hstate, htargetStack⟩ := Prod.mk.inj hmacro'
              subst targetState
              subst targetStack
              have hstackNormalized := Popping.normalizeStack_eq_self_of_lt
                source stack hstack
              have hskipRaw :
                  (Popping.epsilonOnlyTargetMachine source 0).RawErasedReaches
                    (q % source.numStates, stack)
                    (blockedState, blockedTop :: blockedSuffix) := by
                simpa [hstackNormalized] using hskipSpec.1
              have hexposeSpec := Popping.exposeHead_some_spec source
                blockedState blockedTop stableState stableTop stableSuffix hexpose
              have hexposeLift := Popping.rawErasedReaches_suffix hexposeSpec.1
                blockedSuffix
              have hexposeRaw :
                  (Popping.epsilonOnlyTargetMachine source 0).RawErasedReaches
                    (blockedState, blockedTop :: blockedSuffix)
                    (stableState,
                      stableTop :: (stableSuffix ++ blockedSuffix)) := by
                simpa [Nat.mod_eq_of_lt hskipNormalized.1,
                  Nat.mod_eq_of_lt hskipNormalized.2.1]
                  using hexposeLift
              have hepsilonRaw := hskipRaw.trans hexposeRaw
              have hepsilon := Popping.rawCanonicalEpsilonReaches_toDPDA
                source hepsilonRaw
              have hepsilonPDA := DPDA.epsilonReaches_toPDA
                (w := action :: word) hepsilon
              have hinputPDA := Popping.selectedInput?_toPDA_step source
                stableState stableTop action inputTarget inputReplacement
                (stableSuffix ++ blockedSuffix) word hinput
              have hcombined := hepsilonPDA.trans
                (Relation.ReflTransGen.single hinputPDA)
              simpa [Popping.decodeEpsilonConf, EncodedDPDA.replacement,
                EncodedDPDA.state, EncodedDPDA.stackSymbol, List.map_append,
                List.append_assoc, hstackNormalized] using hcombined

/-- If a source computation still has an input letter to consume, one macro
step of the normalization finds exactly the same deterministic input step and
leaves a successful source suffix computation. -/
public theorem macroStep?_complete_of_reaches_nonempty
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action) (q : ℕ) (stack : List ℕ)
    (action : Action) (word : List Action) (finalState : ℕ)
    (hq : q < source.numStates)
    (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols)
    (hreach : @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
      ⟨source.state q, action :: word, source.replacement stack⟩
      ⟨source.state finalState, [], []⟩) :
    ∃ targetState targetStack,
      targetState < source.numStates ∧
      (∀ Z ∈ targetStack, Z < source.numStackSymbols) ∧
      Popping.macroStep? source action (q, stack) =
        some (targetState, targetStack) ∧
      @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
        ⟨source.state targetState, word, source.replacement targetStack⟩
        ⟨source.state finalState, [], []⟩ := by
  have hstackNormalized := Popping.normalizeStack_eq_self_of_lt
    source stack hstack
  cases hskip : Popping.skipReturnable source (Popping.returnTable source)
      q stack with
  | returned returnedState =>
      have hskipSpec := Popping.skipReturnable_spec source q stack
      rw [hskip] at hskipSpec
      have hraw :
          (Popping.epsilonOnlyTargetMachine source 0).RawErasedReaches
            (q % source.numStates, stack) (returnedState, []) := by
        simpa [hstackNormalized] using hskipSpec
      have hepsilon := Popping.rawCanonicalEpsilonReaches_toDPDA source hraw
      have hepsilon' : source.toDPDA.EpsilonReaches
          (source.state q, source.replacement stack)
          (source.state returnedState, []) := by
        simpa [Popping.decodeEpsilonConf, EncodedDPDA.state,
          EncodedDPDA.replacement, hstackNormalized] using hepsilon
      have hpda := DPDA.epsilonReaches_toPDA
        (w := action :: word) hepsilon'
      rcases source.toDPDA.toPDA_reaches_comparable hpda hreach with
        hafter | hbefore
      · have hinput :=
          (PDA.reaches_on_empty_stack (pda := source.toDPDA.toPDA) hafter).1
        simp at hinput
      · have hinput :=
          (PDA.reaches_on_empty_stack (pda := source.toDPDA.toPDA) hbefore).1
        simp at hinput
  | blocked blockedState blockedTop blockedSuffix =>
      have hskipSpec := Popping.skipReturnable_spec source q stack
      rw [hskip] at hskipSpec
      have hskipNormalized := Popping.skipReturnable_normalized source q stack
      rw [hskip] at hskipNormalized
      have hskipRaw :
          (Popping.epsilonOnlyTargetMachine source 0).RawErasedReaches
            (q % source.numStates, stack)
            (blockedState, blockedTop :: blockedSuffix) := by
        simpa [hstackNormalized] using hskipSpec.1
      have hskipEpsilon :=
        Popping.rawCanonicalEpsilonReaches_toDPDA source hskipRaw
      have hskipEpsilon' : source.toDPDA.EpsilonReaches
          (source.state q, source.replacement stack)
          (source.state blockedState,
            source.stackSymbol blockedTop ::
              source.replacement blockedSuffix) := by
        simpa [Popping.decodeEpsilonConf, EncodedDPDA.state,
          EncodedDPDA.replacement, hstackNormalized,
          Nat.mod_eq_of_lt hskipNormalized.1,
          Nat.mod_eq_of_lt hskipNormalized.2.1] using hskipEpsilon
      have hafterSkip :=
        DPDA.toPDA_reaches_suffix_of_epsilonReaches_nonempty
          hskipEpsilon' hreach
      have hstops : ∃ final,
          source.toDPDA.EpsilonStopsAt
            (Popping.decodeEpsilonConf source
              (blockedState, blockedTop :: blockedSuffix)) final := by
        simpa [Popping.decodeEpsilonConf] using
          (DPDA.epsilonStopsAt_of_toPDA_reaches_nonempty hafterSkip)
      obtain ⟨exposed, hexpose⟩ :=
        Popping.exposeHead_some_of_epsilonStopsAt source blockedState
          blockedTop blockedSuffix hstops hskipSpec.2
      rcases exposed with ⟨stableState, stableTop, stableSuffix⟩
      have hexposeSpec := Popping.exposeHead_some_spec source blockedState
        blockedTop stableState stableTop stableSuffix hexpose
      have hexposeNormalized := Popping.exposeHead_some_normalized source
        blockedState blockedTop stableState stableTop stableSuffix hexpose
      have hexposeRaw := Popping.rawErasedReaches_suffix
        hexposeSpec.1 blockedSuffix
      have hexposeEpsilon :=
        Popping.rawCanonicalEpsilonReaches_toDPDA source hexposeRaw
      have hexposeEpsilon' : source.toDPDA.EpsilonReaches
          (source.state blockedState,
            source.stackSymbol blockedTop ::
              source.replacement blockedSuffix)
          (source.state stableState,
            source.stackSymbol stableTop ::
              source.replacement (stableSuffix ++ blockedSuffix)) := by
        simpa [Popping.decodeEpsilonConf, EncodedDPDA.state,
          EncodedDPDA.replacement, List.map_append,
          Nat.mod_eq_of_lt hskipNormalized.1,
          Nat.mod_eq_of_lt hskipNormalized.2.1,
          Nat.mod_eq_of_lt hexposeNormalized.1,
          Nat.mod_eq_of_lt hexposeNormalized.2.1,
          List.append_assoc] using hexposeEpsilon
      have hafterExpose :=
        DPDA.toPDA_reaches_suffix_of_epsilonReaches_nonempty
          hexposeEpsilon' hafterSkip
      have hstable : source.toDPDA.epsilon_transition
          (source.state stableState) (source.stackSymbol stableTop) = none := by
        have := (Popping.selectedEpsilon?_eq_none_iff_epsilonStable source
          stableState stableTop (stableSuffix ++ blockedSuffix)).mp
            hexposeSpec.2
        simpa [Popping.decodeEpsilonConf, DPDA.EpsilonStable] using this
      obtain ⟨inputState, inputReplacement, hinputTransition, hrest⟩ :=
        DPDA.stable_reaches_nonempty_decompose hstable hafterExpose
      have hepsilonStep : DPDAToFirstOrder.Machine.epsilonStep? source
          stableState stableTop = none := by
        rw [← selectedEpsilon?_eq_epsilonStep?]
        exact hexposeSpec.2
      have hepsilonLookup : source.epsilonLookup
          (source.state stableState) (source.stackSymbol stableTop) = none := by
        unfold DPDAToFirstOrder.Machine.epsilonStep? at hepsilonStep
        simpa using hepsilonStep
      have hinputLookup : source.inputLookup
          (source.state stableState) action (source.stackSymbol stableTop) =
            some (inputState, inputReplacement) := by
        simpa [EncodedDPDA.toDPDA, hepsilonLookup] using hinputTransition
      have hmachineInput : DPDAToFirstOrder.Machine.inputStep? source
          stableState action stableTop =
            some (inputState.val, inputReplacement.map Fin.val) := by
        unfold DPDAToFirstOrder.Machine.inputStep?
        simp [hinputLookup]
      have hselectedInput : selectedInput? source stableState action stableTop =
          some (inputState.val, inputReplacement.map Fin.val) := by
        rw [selectedInput?_eq_inputStep?]
        simp [hepsilonStep, hmachineInput]
      let targetStack :=
        (inputReplacement.map Fin.val ++ stableSuffix) ++ blockedSuffix
      have hmacro : Popping.macroStep? source action (q, stack) =
          some (inputState.val, targetStack) := by
        simp [Popping.macroStep?, hskip, Popping.normalizedRow, hexpose,
          hselectedInput, targetStack]
      have hstableSuffix : ∀ Z ∈ stableSuffix,
          Z < source.numStackSymbols :=
        Popping.lt_of_normalizeStack_eq_self source stableSuffix
          hexposeNormalized.2.2
      have hblockedSuffix : ∀ Z ∈ blockedSuffix,
          Z < source.numStackSymbols :=
        Popping.lt_of_normalizeStack_eq_self source blockedSuffix
          hskipNormalized.2.2
      have htargetStack : ∀ Z ∈ targetStack,
          Z < source.numStackSymbols := by
        intro Z hZ
        simp only [targetStack, List.mem_append] at hZ
        rcases hZ with (hZ | hZ) | hZ
        · obtain ⟨symbol, hsymbol, rfl⟩ := List.mem_map.mp hZ
          exact symbol.isLt
        · exact hstableSuffix Z hZ
        · exact hblockedSuffix Z hZ
      have hrest' : @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
          ⟨source.state inputState.val, word,
            source.replacement targetStack⟩
          ⟨source.state finalState, [], []⟩ := by
        have hstateEq : source.state inputState.val = inputState := by
          apply Fin.ext
          simp [EncodedDPDA.state, Nat.mod_eq_of_lt inputState.isLt]
        have hstackEq : source.replacement targetStack =
            inputReplacement ++
              source.replacement (stableSuffix ++ blockedSuffix) := by
          simp [targetStack, EncodedDPDA.replacement,
            EncodedDPDA.stackSymbol, List.map_append, List.map_map,
            Function.comp_def, Nat.mod_eq_of_lt, List.append_assoc]
        rw [hstateEq, hstackEq]
        exact hrest
      exact ⟨inputState.val, targetStack, inputState.isLt,
        htargetStack, hmacro, hrest'⟩

public theorem stabilize_empty_sound
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (q : ℕ) (stack : List ℕ) (word : List Action)
    (hq : q < source.numStates)
    (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols)
    (hempty : (DPDAToFirstOrder.stabilize
      (poppingCompleteMachine source alphabet) (q, stack)).2 = []) :
    ∃ target,
      @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
        ⟨source.state q, word, source.replacement stack⟩
        ⟨source.state target, word, []⟩ := by
  have hstabilize := poppingCompleteMachine_stabilize_eq_skipReturnable
    source alphabet q stack hq hstack
  cases hskip : Popping.skipReturnable source (Popping.returnTable source)
      q stack with
  | returned target =>
      have hskipSpec := Popping.skipReturnable_spec source q stack
      rw [hskip] at hskipSpec
      have hstackNormalized := Popping.normalizeStack_eq_self_of_lt
        source stack hstack
      have hepsilonRaw :
          (Popping.epsilonOnlyTargetMachine source 0).RawErasedReaches
            (q % source.numStates, stack) (target, []) := by
        simpa [hstackNormalized] using hskipSpec
      have hepsilon := Popping.rawCanonicalEpsilonReaches_toDPDA
        source hepsilonRaw
      refine ⟨target, ?_⟩
      simpa [Popping.decodeEpsilonConf, EncodedDPDA.state,
        EncodedDPDA.stackSymbol, EncodedDPDA.replacement,
        hstackNormalized] using
          (DPDA.epsilonReaches_toPDA (w := word) hepsilon)
  | blocked blockedState blockedTop blockedSuffix =>
      rw [hstabilize, hskip] at hempty
      simp at hempty

/-- Every macro output has a normalized stack and is either a source control
state or the single added dead control. -/
public theorem macroStep?_output_valid
    [DecidableEq Action]
    (source : EncodedDPDA Action) (q : ℕ) (stack : List ℕ)
    (action : Action) (targetState : ℕ) (targetStack : List ℕ)
    (hq : q < source.numStates)
    (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols)
    (hmacro : Popping.macroStep? source action (q, stack) =
      some (targetState, targetStack)) :
    targetState < source.numStates + 1 ∧
      ∀ Z ∈ targetStack, Z < source.numStackSymbols := by
  cases hskip : Popping.skipReturnable source (Popping.returnTable source)
      q stack with
  | returned returnedState =>
      simp [Popping.macroStep?, hskip] at hmacro
  | blocked blockedState blockedTop blockedSuffix =>
      have hnormalized := Popping.skipReturnable_normalized source q stack
      rw [hskip] at hnormalized
      let row := Popping.normalizedRow source blockedState blockedTop action
      have hrowValid := normalizedRow_output_valid source blockedState
        blockedTop action hnormalized.2.1
      have hresult :
          (row.2.2.2.1, row.2.2.2.2 ++ blockedSuffix) =
            (targetState, targetStack) := by
        simpa [Popping.macroStep?, hskip, row] using hmacro
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hresult
      refine ⟨hrowValid.1, ?_⟩
      intro Z hZ
      rw [List.mem_append] at hZ
      exact hZ.elim (hrowValid.2 Z)
        ((Popping.lt_of_normalizeStack_eq_self source blockedSuffix
          hnormalized.2.2) Z)

/-- A macro transition can enter the added dead state only with a nonempty
stack.  Thus dead behavior can never witness empty-stack acceptance. -/
public theorem macroStep?_dead_stack_ne_nil
    [DecidableEq Action]
    (source : EncodedDPDA Action) (q : ℕ) (stack : List ℕ)
    (action : Action) (targetStack : List ℕ)
    (hmacro : Popping.macroStep? source action (q, stack) =
      some (Popping.deadState source, targetStack)) :
    targetStack ≠ [] := by
  cases hskip : Popping.skipReturnable source (Popping.returnTable source)
      q stack with
  | returned returnedState =>
      simp [Popping.macroStep?, hskip] at hmacro
  | blocked blockedState blockedTop blockedSuffix =>
      cases hexpose : Popping.exposeHead source blockedState blockedTop with
      | none =>
          simp [Popping.macroStep?, hskip, Popping.normalizedRow, hexpose,
            Popping.deadState] at hmacro
          subst targetStack
          simp
      | some exposed =>
          rcases exposed with ⟨stableState, stableTop, stableSuffix⟩
          cases hinput : selectedInput? source stableState action stableTop with
          | none =>
              simp [Popping.macroStep?, hskip, Popping.normalizedRow, hexpose,
                hinput, Popping.deadState] at hmacro
              subst targetStack
              simp
          | some output =>
              rcases output with ⟨inputTarget, inputReplacement⟩
              have hnormalized := selectedInput?_normalized source stableState
                action stableTop inputTarget inputReplacement hinput
              have htarget : inputTarget < source.numStates := by
                rw [← hnormalized.1]
                exact Nat.mod_lt _ source.numStates_pos
              simp only [Popping.macroStep?, hskip, Popping.normalizedRow,
                hexpose, hinput, Option.some.injEq, Prod.mk.injEq] at hmacro
              have : inputTarget = source.numStates := by
                simpa [Popping.deadState] using hmacro.1
              omega

/-- Empty-stack acceptance of the popping-complete machine is sound for the
source DPDA, from every normalized source configuration. -/
public theorem observableRun_empty_sound
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet) :
    ∀ (word : List Action) (q : ℕ) (stack : List ℕ)
      (target : DPDAToFirstOrder.Configuration),
      q < source.numStates →
      (∀ Z ∈ stack, Z < source.numStackSymbols) →
      DPDAToFirstOrder.observableRun?
          (poppingCompleteMachine source alphabet) word (q, stack) =
        some target →
      (DPDAToFirstOrder.stabilize
          (poppingCompleteMachine source alphabet) target).2 = [] →
      ∃ final,
        @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
          ⟨source.state q, word, source.replacement stack⟩
          ⟨source.state final, [], []⟩ := by
  intro word
  induction word with
  | nil =>
      intro q stack target hq hstack hrun hempty
      simp only [DPDAToFirstOrder.observableRun?, Option.some.injEq] at hrun
      subst target
      simpa using stabilize_empty_sound source alphabet q stack [] hq hstack
        hempty
  | cons action word ih =>
      intro q stack target hq hstack hrun hempty
      cases hstep : DPDAToFirstOrder.observableStep?
          (poppingCompleteMachine source alphabet) action (q, stack) with
      | none =>
          simp [DPDAToFirstOrder.observableRun?, hstep] at hrun
      | some middle =>
          have htail : DPDAToFirstOrder.observableRun?
              (poppingCompleteMachine source alphabet) word middle =
                some target := by
            simpa [DPDAToFirstOrder.observableRun?, hstep] using hrun
          have hmacro : Popping.macroStep? source action (q, stack) =
              some middle := by
            rw [← poppingCompleteMachine_observableStep?_eq_macroStep?
              source alphabet q stack action hq hstack (haustive action)]
            exact hstep
          have hmiddleValid := macroStep?_output_valid source q stack action
            middle.1 middle.2 hq hstack hmacro
          by_cases hlive : middle.1 < source.numStates
          · have hfirst := macroStep?_sound_of_live source q stack action
              middle.1 middle.2 word hq hstack hmacro hlive
            obtain ⟨final, hrest⟩ := ih middle.1 middle.2 target hlive
              hmiddleValid.2 htail hempty
            exact ⟨final, hfirst.trans hrest⟩
          · have hdead : middle.1 = Popping.deadState source := by
              unfold Popping.deadState
              omega
            have hmiddleEq :
                middle = (Popping.deadState source, middle.2) := by
              exact Prod.ext hdead rfl
            have hmacroDead : Popping.macroStep? source action (q, stack) =
                some (Popping.deadState source, middle.2) :=
              hmacro.trans (congrArg some hmiddleEq)
            have hmiddleNe : middle.2 ≠ [] := by
              exact macroStep?_dead_stack_ne_nil source q stack action
                middle.2 hmacroDead
            have hdeadRun := poppingCompleteMachine_dead_observableRun?
              source alphabet haustive middle.2 hmiddleValid.2 hmiddleNe word
            rw [hmiddleEq] at htail
            have htarget : target = (Popping.deadState source, middle.2) :=
              Option.some.inj (htail.symm.trans hdeadRun)
            subst target
            rw [poppingCompleteMachine_dead_stabilize] at hempty
            exact (hmiddleNe hempty).elim

/-- Source-side empty-stack semantics used to state preprocessing soundness
without mentioning the implementation details of the normalized machine. -/
@[expose] public def sourceEmptyStackLanguage
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action)
    (configuration : DPDAToFirstOrder.Configuration) : Language Action :=
  {word | ∃ target,
    @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
      ⟨source.state configuration.1, word,
        source.replacement configuration.2⟩
      ⟨source.state target, [], []⟩}

public theorem poppingCompleteMachine_emptyStackLanguage_subset
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet)
    (q : ℕ) (stack : List ℕ)
    (hq : q < source.numStates)
    (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols) :
    DPDAToFirstOrder.emptyStackLanguage
        (poppingCompleteMachine source alphabet) (q, stack) ≤
      sourceEmptyStackLanguage source (q, stack) := by
  intro word hword
  rcases hword with ⟨target, hrun, hempty⟩
  exact observableRun_empty_sound source alphabet haustive word q stack
    target hq hstack hrun hempty

public theorem poppingCompleteMachine_normal [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet) :
    DPDAToFirstOrder.Machine.PoppingComplete
      (poppingCompleteMachine source alphabet) alphabet := by
  rw [DPDAToFirstOrder.Machine.poppingComplete_iff]
  refine ⟨?_, ?_, haustive⟩
  · unfold DPDAToFirstOrder.Machine.epsilonPoppingCode
    apply List.all_eq_true.mpr
    intro row hrow
    simpa using poppingRows_empty hrow
  · unfold DPDAToFirstOrder.Machine.stableCompleteCode
    apply List.all_eq_true.mpr
    intro q hq
    have hqBound : q < source.numStates + 1 := by
      simpa using List.mem_range.mp hq
    apply List.all_eq_true.mpr
    intro Z hZ
    have hZBound : Z < source.numStackSymbols := by
      simpa using List.mem_range.mp hZ
    cases hstep : DPDAToFirstOrder.Machine.epsilonStep?
        (poppingCompleteMachine source alphabet) q Z with
    | some out => simp [hstep]
    | none =>
        simp only [hstep]
        apply List.all_eq_true.mpr
        intro action haction
        rw [Option.isSome_iff_ne_none]
        intro hinputNone
        have hqLe : q ≤ source.numStates := Nat.le_of_lt_succ hqBound
        rcases lt_or_eq_of_le hqLe with hqSource | hqDead
        · cases hreturn : Popping.returnAt source
              (Popping.returnTable source) q Z with
          | none =>
              have hmem := normalizedRow_mem hqSource hZBound hreturn haction
              have hsome := inputStep?_isSome_of_rawRow hmem
              obtain ⟨hrowSource, hrowAction, hrowTop⟩ :=
                normalizedRow_key source q Z action
              rw [hrowSource, hrowAction, hrowTop, hinputNone] at hsome
              simp at hsome
          | some target =>
              have hmem : (q, Z, target, []) ∈
                  (poppingCompleteMachine source alphabet).epsilonRows := by
                simpa [poppingCompleteMachine] using
                  (poppingRow_mem (Action := Action) hqSource hZBound hreturn)
              have hsome := epsilonStep?_isSome_of_rawRow hmem
              rw [hstep] at hsome
              simp at hsome
        · have hqEq : q = Popping.deadState source := by
            simpa [Popping.deadState] using hqDead
          subst q
          have hmem := deadRow_mem hZBound haction
          have hsome := inputStep?_isSome_of_rawRow hmem
          simpa [Popping.deadState, hinputNone] using hsome

/-! ## Exact delayed-endmarker semantics -/

public theorem selectedEpsilon?_toPDA_step
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (replacement suffix : List ℕ) (word : List Action)
    (hstep : selectedEpsilon? machine q Z = some (target, replacement)) :
    @PDA.Reaches₁ _ _ _ _ _ _ machine.toDPDA.toPDA
      ⟨machine.state q, word,
        machine.stackSymbol Z :: machine.replacement suffix⟩
      ⟨machine.state target, word,
        machine.replacement (replacement ++ suffix)⟩ := by
  have hraw := Popping.rawEpsilonStep_of_selectedEpsilon?
    machine q Z target replacement suffix hstep
  have hepsilon := Popping.rawCanonicalEpsilonStep_toDPDA machine hraw
  have hpda := DPDA.epsilonStep_toPDA (w := word) hepsilon
  simpa [Popping.decodeEpsilonConf, EncodedDPDA.replacement,
    List.map_append] using hpda

private theorem selectedEpsilon?_of_transition
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z : ℕ)
    (target : Fin machine.numStates)
    (replacement : List (Fin machine.numStackSymbols))
    (htransition : machine.toDPDA.epsilon_transition
      (machine.state q) (machine.stackSymbol Z) =
        some (target, replacement)) :
    selectedEpsilon? machine q Z =
      some (target.val, replacement.map Fin.val) := by
  rw [selectedEpsilon?_eq_epsilonStep?]
  unfold DPDAToFirstOrder.Machine.epsilonStep?
  change machine.epsilonLookup (machine.state q) (machine.stackSymbol Z) =
    some (target, replacement) at htransition
  simp [htransition]

private theorem selectedInput?_of_transition
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) (action : Action) (Z : ℕ)
    (target : Fin machine.numStates)
    (replacement : List (Fin machine.numStackSymbols))
    (htransition : machine.toDPDA.transition
      (machine.state q) action (machine.stackSymbol Z) =
        some (target, replacement)) :
    selectedInput? machine q action Z =
      some (target.val, replacement.map Fin.val) := by
  change (if (machine.epsilonLookup (machine.state q)
        (machine.stackSymbol Z)).isSome then none
      else machine.inputLookup (machine.state q) action
        (machine.stackSymbol Z)) = some (target, replacement) at htransition
  cases hepsilon : machine.epsilonLookup (machine.state q)
      (machine.stackSymbol Z) with
  | some output => simp [hepsilon] at htransition
  | none =>
      have hinput : machine.inputLookup (machine.state q) action
          (machine.stackSymbol Z) = some (target, replacement) := by
        simpa [hepsilon] using htransition
      rw [selectedInput?_eq_inputStep?]
      unfold DPDAToFirstOrder.Machine.epsilonStep?
        DPDAToFirstOrder.Machine.inputStep?
      simp [hepsilon, hinput]

private theorem transition_eq_some_of_toPDA_mem
    {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (machine : DPDA Q T S) (q : Q) (action : T) (Z : S)
    (target : Q) (replacement : List S)
    (hmem : (target, replacement) ∈
      machine.toPDA.transition_fun q action Z) :
    machine.transition q action Z = some (target, replacement) := by
  cases htransition : machine.transition q action Z with
  | none => simp [DPDA.toPDA, htransition] at hmem
  | some output =>
      have hout : output = (target, replacement) := by
        symm
        simpa [DPDA.toPDA, htransition] using hmem
      simpa [hout] using htransition

private theorem epsilonTransition_eq_some_of_toPDA_mem
    {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (machine : DPDA Q T S) (q : Q) (Z : S)
    (target : Q) (replacement : List S)
    (hmem : (target, replacement) ∈
      machine.toPDA.transition_fun' q Z) :
    machine.epsilon_transition q Z = some (target, replacement) := by
  cases htransition : machine.epsilon_transition q Z with
  | none => simp [DPDA.toPDA, htransition] at hmem
  | some output =>
      have hout : output = (target, replacement) := by
        symm
        simpa [DPDA.toPDA, htransition] using hmem
      simpa [hout] using htransition

private theorem rawCanonicalEpsilonReaches_of_toDPDA
    [Fintype Action] [DecidableEq Action]
    (machine : EncodedDPDA Action)
    {source target : DPDA.EpsilonConf
      (Fin machine.numStates) (Fin machine.numStackSymbols)}
    (hreach : machine.toDPDA.EpsilonReaches source target) :
    (Popping.epsilonOnlyTargetMachine machine 0).RawErasedReaches
      (source.1.val, source.2.map Fin.val)
      (target.1.val, target.2.map Fin.val) := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head source middle hstep hrest ih =>
      rcases source with ⟨q, stack⟩
      cases stack with
      | nil => simp [DPDA.EpsilonStep] at hstep
      | cons Z suffix =>
          rcases middle with ⟨targetState, targetStack⟩
          obtain ⟨replacement, htransition, rfl⟩ := hstep
          have htransition' : machine.toDPDA.epsilon_transition
              (machine.state q.val) (machine.stackSymbol Z.val) =
                some (targetState, replacement) := by
            simpa [EncodedDPDA.state, EncodedDPDA.stackSymbol,
              Nat.mod_eq_of_lt q.isLt, Nat.mod_eq_of_lt Z.isLt] using
                htransition
          have hselected := selectedEpsilon?_of_transition machine
            q.val Z.val targetState replacement htransition'
          have hraw := Popping.rawEpsilonStep_of_selectedEpsilon?
            machine q.val Z.val targetState.val (replacement.map Fin.val)
              (suffix.map Fin.val) hselected
          exact Relation.ReflTransGen.head (by
              simpa [Nat.mod_eq_of_lt q.isLt,
                Nat.mod_eq_of_lt Z.isLt] using hraw)
            (by simpa [List.map_append] using ih)

private theorem poppingCompleteMachine_stabilize_empty_complete
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (q : ℕ) (stack : List ℕ) (finalState : ℕ)
    (hq : q < source.numStates)
    (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols)
    (hreach : @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
      ⟨source.state q, [], source.replacement stack⟩
      ⟨source.state finalState, [], []⟩) :
    (DPDAToFirstOrder.stabilize
      (poppingCompleteMachine source alphabet) (q, stack)).2 = [] := by
  have hstabilize := poppingCompleteMachine_stabilize_eq_skipReturnable
    source alphabet q stack hq hstack
  cases hskip : Popping.skipReturnable source (Popping.returnTable source)
      q stack with
  | returned returnedState =>
      simp [hstabilize, hskip]
  | blocked blockedState blockedTop blockedSuffix =>
      have hskipSpec := Popping.skipReturnable_spec source q stack
      rw [hskip] at hskipSpec
      have hskipNormalized := Popping.skipReturnable_normalized source q stack
      rw [hskip] at hskipNormalized
      have hstackNormalized := Popping.normalizeStack_eq_self_of_lt
        source stack hstack
      have hprefixRaw :
          (Popping.epsilonOnlyTargetMachine source 0).RawErasedReaches
            (q, stack)
            (blockedState, blockedTop :: blockedSuffix) := by
        simpa [Nat.mod_eq_of_lt hq, hstackNormalized] using hskipSpec.1
      have hprefixEpsilon :=
        Popping.rawCanonicalEpsilonReaches_toDPDA source hprefixRaw
      have hprefix : @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
          ⟨source.state q, [], source.replacement stack⟩
          ⟨source.state blockedState, [],
            source.replacement (blockedTop :: blockedSuffix)⟩ := by
        simpa [Popping.decodeEpsilonConf, EncodedDPDA.state,
          EncodedDPDA.replacement, Nat.mod_eq_of_lt hq,
          Nat.mod_eq_of_lt hskipNormalized.1,
          Nat.mod_eq_of_lt hskipNormalized.2.1,
          Popping.normalizeStack_eq_self_of_lt source blockedSuffix
            (Popping.lt_of_normalizeStack_eq_self source blockedSuffix
              hskipNormalized.2.2)] using
          (DPDA.epsilonReaches_toPDA (w := ([] : List Action))
            hprefixEpsilon)
      have hblocked : @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
          ⟨source.state blockedState, [],
            source.replacement (blockedTop :: blockedSuffix)⟩
          ⟨source.state finalState, [], []⟩ := by
        rcases source.toDPDA.toPDA_reaches_comparable hprefix hreach with
          hafter | hbefore
        · exact hafter
        · have hempty := PDA.reaches_on_empty_stack
              (pda := source.toDPDA.toPDA) hbefore
          simp [EncodedDPDA.replacement] at hempty
      rw [PDA.reaches_iff_reachesIn] at hblocked
      obtain ⟨steps, hblocked⟩ := hblocked
      have hsplit := PDA.split_stack
        (pda := source.toDPDA.toPDA)
        (n := steps)
        (q := source.state blockedState)
        (p := source.state finalState)
        (x := ([] : List Action))
        (α := [source.stackSymbol blockedTop])
        (β := source.replacement blockedSuffix) (by
          simpa [EncodedDPDA.replacement] using hblocked)
      obtain ⟨middle, headSteps, tailSteps, headWord, tailWord,
          hwords, _, _, hhead, _⟩ := hsplit
      have hheadWord : headWord = [] := by
        exact (List.append_eq_nil_iff.mp hwords.symm).1
      subst headWord
      have hheadReach : @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
          ⟨source.state blockedState, [],
            [source.stackSymbol blockedTop]⟩
          ⟨middle, [], []⟩ := by
        exact PDA.reaches_of_reachesIn hhead
      have hheadEpsilon :=
        DPDA.epsilonReaches_of_toPDA_empty_reaches hheadReach
      have hheadRaw := rawCanonicalEpsilonReaches_of_toDPDA source
        hheadEpsilon
      have hreturns : Popping.RawHeadReturns source blockedState blockedTop
          middle.val := by
        rw [Popping.rawHeadReturns_iff_canonical]
        simpa [EncodedDPDA.state, EncodedDPDA.stackSymbol,
          Nat.mod_eq_of_lt hskipNormalized.1,
          Nat.mod_eq_of_lt hskipNormalized.2.1,
          Nat.mod_eq_of_lt middle.isLt] using hheadRaw
      have hnone := (Popping.returnAt_eq_none_iff source blockedState
        blockedTop).mp hskipSpec.2
      exact (hnone middle.val middle.isLt hreturns).elim

private theorem observableRun_empty_complete
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet) :
    ∀ (word : List Action) (q : ℕ) (stack : List ℕ) (finalState : ℕ),
      q < source.numStates →
      (∀ Z ∈ stack, Z < source.numStackSymbols) →
      @PDA.Reaches _ _ _ _ _ _ source.toDPDA.toPDA
        ⟨source.state q, word, source.replacement stack⟩
        ⟨source.state finalState, [], []⟩ →
      ∃ target,
        DPDAToFirstOrder.observableRun?
          (poppingCompleteMachine source alphabet) word (q, stack) =
            some target ∧
        (DPDAToFirstOrder.stabilize
          (poppingCompleteMachine source alphabet) target).2 = [] := by
  intro word
  induction word with
  | nil =>
      intro q stack finalState hq hstack hreach
      refine ⟨(q, stack), rfl, ?_⟩
      exact poppingCompleteMachine_stabilize_empty_complete
        source alphabet q stack finalState hq hstack hreach
  | cons action word ih =>
      intro q stack finalState hq hstack hreach
      obtain ⟨targetState, targetStack, htargetState, htargetStack,
          hmacro, hrest⟩ :=
        macroStep?_complete_of_reaches_nonempty source q stack action word
          finalState hq hstack hreach
      obtain ⟨target, hrun, hempty⟩ :=
        ih targetState targetStack finalState htargetState htargetStack hrest
      have hstep : DPDAToFirstOrder.observableStep?
          (poppingCompleteMachine source alphabet) action (q, stack) =
            some (targetState, targetStack) := by
        rw [poppingCompleteMachine_observableStep?_eq_macroStep?
          source alphabet q stack action hq hstack (haustive action)]
        exact hmacro
      refine ⟨target, ?_, hempty⟩
      simpa [DPDAToFirstOrder.observableRun?, hstep] using hrun

public theorem poppingCompleteMachine_emptyStackLanguage_eq
    [Fintype Action] [DecidableEq Action]
    (source : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet)
    (q : ℕ) (stack : List ℕ)
    (hq : q < source.numStates)
    (hstack : ∀ Z ∈ stack, Z < source.numStackSymbols) :
    DPDAToFirstOrder.emptyStackLanguage
        (poppingCompleteMachine source alphabet) (q, stack) =
      sourceEmptyStackLanguage source (q, stack) := by
  apply Set.Subset.antisymm
  · exact poppingCompleteMachine_emptyStackLanguage_subset
      source alphabet haustive q stack hq hstack
  · intro word hword
    obtain ⟨finalState, hreach⟩ := hword
    exact observableRun_empty_complete source alphabet haustive word q stack
      finalState hq hstack hreach

@[expose] public def leftMappedStack (left : EncodedDPDA Action)
    (stack : List ℕ) : List ℕ :=
  stack.map (Endmarked.leftStack left) ++ [Endmarked.bottom]

@[expose] public def rightMappedStack (left right : EncodedDPDA Action)
    (stack : List ℕ) : List ℕ :=
  stack.map (Endmarked.rightStack left right) ++ [Endmarked.bottom]

@[expose] public def leftFinishState (left right : EncodedDPDA Action)
    (alphabet : List Action) (q : ℕ) : ℕ :=
  if Endmarked.isFinalIndex left q then
    Endmarked.acceptState left right alphabet
  else Endmarked.rejectState left right alphabet

@[expose] public def rightFinishState (left right : EncodedDPDA Action)
    (alphabet : List Action) (q : ℕ) : ℕ :=
  if Endmarked.isFinalIndex right q then
    Endmarked.acceptState left right alphabet
  else Endmarked.rejectState left right alphabet

private theorem left_simulates_until_empty_in
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet) :
    ∀ (steps q : ℕ) (stack : List ℕ) (pending : Action)
      (rest : List Action) (finalState : Fin left.numStates)
      (finalStack : List (Fin left.numStackSymbols)),
      q < left.numStates →
      (∀ Z ∈ stack, Z < left.numStackSymbols) →
      pending ∈ alphabet →
      @PDA.ReachesIn _ _ _ _ _ _ left.toDPDA.toPDA steps
        ⟨left.state q, pending :: rest, left.replacement stack⟩
        ⟨finalState, [], finalStack⟩ →
      ∃ emptyState emptyStack,
        emptyState < left.numStates ∧
        (∀ Z ∈ emptyStack, Z < left.numStackSymbols) ∧
        @PDA.Reaches _ _ _ _ _ _ left.toDPDA.toPDA
          ⟨left.state q, pending :: rest, left.replacement stack⟩
          ⟨left.state emptyState, [], left.replacement emptyStack⟩ ∧
        @PDA.Reaches _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              (Endmarked.leftPending left alphabet q pending),
            rest.map some ++ [none],
            (endmarkedPairMachine left right alphabet).replacement
              (leftMappedStack left stack)⟩
          ⟨(endmarkedPairMachine left right alphabet).state
              (leftFinishState left right alphabet emptyState),
            [],
            (endmarkedPairMachine left right alphabet).replacement
              (leftMappedStack left emptyStack)⟩ := by
  intro steps
  induction steps with
  | zero =>
      intro q stack pending rest finalState finalStack hq hstack hpending
        hreach
      have heq := PDA.reachesIn_zero hreach
      have hinput := congrArg PDA.conf.input heq
      simp at hinput
  | succ steps ih =>
      intro q stack pending rest finalState finalStack hq hstack hpending
        hreach
      obtain ⟨middle, hfirst, hrest⟩ :=
        PDA.reachesIn_iff_split_first.mpr hreach
      have hstep := PDA.reaches₁_iff_reachesIn_one.mpr hfirst
      cases stack with
      | nil =>
          simp [PDA.Reaches₁, PDA.step, EncodedDPDA.replacement] at hstep
      | cons Z suffix =>
          have hZ : Z < left.numStackSymbols := hstack Z (by simp)
          have hsuffix : ∀ X ∈ suffix, X < left.numStackSymbols := by
            intro X hX
            exact hstack X (by simp [hX])
          rcases PDA.reaches₁_push hstep with hinput | hepsilon
          · obtain ⟨action, tail, target, replacement, hinputEq,
                hmiddle, hmem⟩ := hinput
            have hletters := List.cons.inj hinputEq
            have haction : action = pending := hletters.1.symm
            have htail : tail = rest := hletters.2.symm
            subst action
            subst tail
            have htransition : left.toDPDA.transition
                (left.state q) pending (left.stackSymbol Z) =
                  some (target, replacement) := by
              exact transition_eq_some_of_toPDA_mem left.toDPDA
                (left.state q) pending (left.stackSymbol Z)
                target replacement hmem
            have hselected := selectedInput?_of_transition left q pending Z
              target replacement htransition
            let nextStack := replacement.map Fin.val ++ suffix
            have hnextStack : ∀ X ∈ nextStack,
                X < left.numStackSymbols := by
              intro X hX
              simp only [nextStack, List.mem_append] at hX
              rcases hX with hX | hX
              · obtain ⟨symbol, hsymbol, rfl⟩ := List.mem_map.mp hX
                exact symbol.isLt
              · exact hsuffix X hX
            have hmiddleEq : middle =
                ⟨left.state target.val, rest,
                  left.replacement nextStack⟩ := by
              rw [hmiddle]
              apply PDA.conf.ext
              · apply Fin.ext
                simp [EncodedDPDA.state, Nat.mod_eq_of_lt target.isLt]
              · rfl
              · simp [nextStack, EncodedDPDA.replacement, List.map_append,
                  EncodedDPDA.stackSymbol, List.map_map, Function.comp_def,
                  Nat.mod_eq_of_lt]
            rw [hmiddleEq] at hstep hrest
            cases rest with
            | nil =>
                have htargetSelected : selectedInput?
                    (endmarkedPairMachine left right alphabet)
                    (Endmarked.leftPending left alphabet q pending) none
                    (Endmarked.leftStack left Z) =
                      some (leftFinishState left right alphabet target.val,
                        (replacement.map Fin.val).map
                          (Endmarked.leftStack left)) := by
                  have hlookup := endmarked_selectedInput?_leftPending_eq
                    left right alphabet q Z pending hpending none
                    (by simp [endmarkedAlphabet])
                  rw [hselected] at hlookup
                  simpa [leftFinishState] using hlookup
                have htargetStep := Popping.selectedInput?_toPDA_step
                  (endmarkedPairMachine left right alphabet)
                  (Endmarked.leftPending left alphabet q pending)
                  (Endmarked.leftStack left Z) none
                  (leftFinishState left right alphabet target.val)
                  ((replacement.map Fin.val).map
                    (Endmarked.leftStack left))
                  (suffix.map (Endmarked.leftStack left) ++
                    [Endmarked.bottom]) [] htargetSelected
                have htargetStep' : @PDA.Reaches₁ _ _ _ _ _ _
                    (endmarkedPairMachine left right alphabet).toDPDA.toPDA
                    ⟨(endmarkedPairMachine left right alphabet).state
                        (Endmarked.leftPending left alphabet q pending),
                      [none],
                      (endmarkedPairMachine left right alphabet).replacement
                        (leftMappedStack left (Z :: suffix))⟩
                    ⟨(endmarkedPairMachine left right alphabet).state
                        (leftFinishState left right alphabet target.val),
                      [],
                      (endmarkedPairMachine left right alphabet).replacement
                        (leftMappedStack left nextStack)⟩ := by
                  simpa [leftMappedStack, nextStack, List.map_append,
                    List.append_assoc] using htargetStep
                exact ⟨target.val, nextStack, target.isLt, hnextStack,
                  Relation.ReflTransGen.single hstep,
                  Relation.ReflTransGen.single htargetStep'⟩
            | cons next tail =>
                have hnextMem : next ∈ alphabet := haustive next
                have htargetSelected : selectedInput?
                    (endmarkedPairMachine left right alphabet)
                    (Endmarked.leftPending left alphabet q pending) (some next)
                    (Endmarked.leftStack left Z) =
                      some
                        (Endmarked.leftPending left alphabet target.val next,
                          (replacement.map Fin.val).map
                            (Endmarked.leftStack left)) := by
                  have hlookup := endmarked_selectedInput?_leftPending_eq
                    left right alphabet q Z pending hpending (some next)
                    (by simp [endmarkedAlphabet, hnextMem])
                  rw [hselected] at hlookup
                  simpa using hlookup
                have htargetStep := Popping.selectedInput?_toPDA_step
                  (endmarkedPairMachine left right alphabet)
                  (Endmarked.leftPending left alphabet q pending)
                  (Endmarked.leftStack left Z) (some next)
                  (Endmarked.leftPending left alphabet target.val next)
                  ((replacement.map Fin.val).map
                    (Endmarked.leftStack left))
                  (suffix.map (Endmarked.leftStack left) ++
                    [Endmarked.bottom])
                  (tail.map some ++ [none]) htargetSelected
                have htargetStep' : @PDA.Reaches₁ _ _ _ _ _ _
                    (endmarkedPairMachine left right alphabet).toDPDA.toPDA
                    ⟨(endmarkedPairMachine left right alphabet).state
                        (Endmarked.leftPending left alphabet q pending),
                      some next :: (tail.map some ++ [none]),
                      (endmarkedPairMachine left right alphabet).replacement
                        (leftMappedStack left (Z :: suffix))⟩
                    ⟨(endmarkedPairMachine left right alphabet).state
                        (Endmarked.leftPending left alphabet target.val next),
                      tail.map some ++ [none],
                      (endmarkedPairMachine left right alphabet).replacement
                        (leftMappedStack left nextStack)⟩ := by
                  simpa [leftMappedStack, nextStack, List.map_append,
                    List.append_assoc] using htargetStep
                obtain ⟨emptyState, emptyStack, hemptyState, hemptyStack,
                    hsourceRest, htargetRest⟩ :=
                  ih target.val nextStack next tail finalState finalStack
                    target.isLt hnextStack hnextMem hrest
                exact ⟨emptyState, emptyStack, hemptyState, hemptyStack,
                  (Relation.ReflTransGen.single hstep).trans hsourceRest,
                  (Relation.ReflTransGen.single htargetStep').trans
                    htargetRest⟩
          · obtain ⟨target, replacement, hmiddle, hmem⟩ := hepsilon
            have htransition : left.toDPDA.epsilon_transition
                (left.state q) (left.stackSymbol Z) =
                  some (target, replacement) := by
              exact epsilonTransition_eq_some_of_toPDA_mem left.toDPDA
                (left.state q) (left.stackSymbol Z)
                target replacement hmem
            have hselected := selectedEpsilon?_of_transition left q Z
              target replacement htransition
            let nextStack := replacement.map Fin.val ++ suffix
            have hnextStack : ∀ X ∈ nextStack,
                X < left.numStackSymbols := by
              intro X hX
              simp only [nextStack, List.mem_append] at hX
              rcases hX with hX | hX
              · obtain ⟨symbol, hsymbol, rfl⟩ := List.mem_map.mp hX
                exact symbol.isLt
              · exact hsuffix X hX
            have hmiddleEq : middle =
                ⟨left.state target.val, pending :: rest,
                  left.replacement nextStack⟩ := by
              rw [hmiddle]
              apply PDA.conf.ext
              · apply Fin.ext
                simp [EncodedDPDA.state, Nat.mod_eq_of_lt target.isLt]
              · rfl
              · simp [nextStack, EncodedDPDA.replacement, List.map_append,
                  EncodedDPDA.stackSymbol, List.map_map, Function.comp_def,
                  Nat.mod_eq_of_lt]
            rw [hmiddleEq] at hstep hrest
            have htargetSelected : selectedEpsilon?
                (endmarkedPairMachine left right alphabet)
                (Endmarked.leftPending left alphabet q pending)
                (Endmarked.leftStack left Z) =
                  some
                    (Endmarked.leftPending left alphabet target.val pending,
                      (replacement.map Fin.val).map
                        (Endmarked.leftStack left)) := by
              have hlookup := endmarked_selectedEpsilon?_leftPending_eq
                left right alphabet q Z pending hpending
              rw [hselected] at hlookup
              simpa using hlookup
            have htargetStep := selectedEpsilon?_toPDA_step
              (endmarkedPairMachine left right alphabet)
              (Endmarked.leftPending left alphabet q pending)
              (Endmarked.leftStack left Z)
              (Endmarked.leftPending left alphabet target.val pending)
              ((replacement.map Fin.val).map (Endmarked.leftStack left))
              (suffix.map (Endmarked.leftStack left) ++ [Endmarked.bottom])
              (rest.map some ++ [none]) htargetSelected
            have htargetStep' : @PDA.Reaches₁ _ _ _ _ _ _
                (endmarkedPairMachine left right alphabet).toDPDA.toPDA
                ⟨(endmarkedPairMachine left right alphabet).state
                    (Endmarked.leftPending left alphabet q pending),
                  rest.map some ++ [none],
                  (endmarkedPairMachine left right alphabet).replacement
                    (leftMappedStack left (Z :: suffix))⟩
                ⟨(endmarkedPairMachine left right alphabet).state
                    (Endmarked.leftPending left alphabet target.val pending),
                  rest.map some ++ [none],
                  (endmarkedPairMachine left right alphabet).replacement
                    (leftMappedStack left nextStack)⟩ := by
              simpa [leftMappedStack, nextStack, List.map_append,
                List.append_assoc] using htargetStep
            obtain ⟨emptyState, emptyStack, hemptyState, hemptyStack,
                hsourceRest, htargetRest⟩ :=
              ih target.val nextStack pending rest finalState finalStack
                target.isLt hnextStack hpending hrest
            exact ⟨emptyState, emptyStack, hemptyState, hemptyStack,
              (Relation.ReflTransGen.single hstep).trans hsourceRest,
              (Relation.ReflTransGen.single htargetStep').trans htargetRest⟩

private theorem right_simulates_until_empty_in
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet) :
    ∀ (steps q : ℕ) (stack : List ℕ) (pending : Action)
      (rest : List Action) (finalState : Fin right.numStates)
      (finalStack : List (Fin right.numStackSymbols)),
      q < right.numStates →
      (∀ Z ∈ stack, Z < right.numStackSymbols) →
      pending ∈ alphabet →
      @PDA.ReachesIn _ _ _ _ _ _ right.toDPDA.toPDA steps
        ⟨right.state q, pending :: rest, right.replacement stack⟩
        ⟨finalState, [], finalStack⟩ →
      ∃ emptyState emptyStack,
        emptyState < right.numStates ∧
        (∀ Z ∈ emptyStack, Z < right.numStackSymbols) ∧
        @PDA.Reaches _ _ _ _ _ _ right.toDPDA.toPDA
          ⟨right.state q, pending :: rest, right.replacement stack⟩
          ⟨right.state emptyState, [], right.replacement emptyStack⟩ ∧
        @PDA.Reaches _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              (Endmarked.rightPending left right alphabet q pending),
            rest.map some ++ [none],
            (endmarkedPairMachine left right alphabet).replacement
              (rightMappedStack left right stack)⟩
          ⟨(endmarkedPairMachine left right alphabet).state
              (rightFinishState left right alphabet emptyState),
            [],
            (endmarkedPairMachine left right alphabet).replacement
              (rightMappedStack left right emptyStack)⟩ := by
  intro steps
  induction steps with
  | zero =>
      intro q stack pending rest finalState finalStack hq hstack hpending
        hreach
      have heq := PDA.reachesIn_zero hreach
      have hinput := congrArg PDA.conf.input heq
      simp at hinput
  | succ steps ih =>
      intro q stack pending rest finalState finalStack hq hstack hpending
        hreach
      obtain ⟨middle, hfirst, hrest⟩ :=
        PDA.reachesIn_iff_split_first.mpr hreach
      have hstep := PDA.reaches₁_iff_reachesIn_one.mpr hfirst
      cases stack with
      | nil =>
          simp [PDA.Reaches₁, PDA.step, EncodedDPDA.replacement] at hstep
      | cons Z suffix =>
          have hZ : Z < right.numStackSymbols := hstack Z (by simp)
          have hsuffix : ∀ X ∈ suffix, X < right.numStackSymbols := by
            intro X hX
            exact hstack X (by simp [hX])
          rcases PDA.reaches₁_push hstep with hinput | hepsilon
          · obtain ⟨action, tail, target, replacement, hinputEq,
                hmiddle, hmem⟩ := hinput
            have hletters := List.cons.inj hinputEq
            have haction : action = pending := hletters.1.symm
            have htail : tail = rest := hletters.2.symm
            subst action
            subst tail
            have htransition : right.toDPDA.transition
                (right.state q) pending (right.stackSymbol Z) =
                  some (target, replacement) := by
              exact transition_eq_some_of_toPDA_mem right.toDPDA
                (right.state q) pending (right.stackSymbol Z)
                target replacement hmem
            have hselected := selectedInput?_of_transition right q pending Z
              target replacement htransition
            let nextStack := replacement.map Fin.val ++ suffix
            have hnextStack : ∀ X ∈ nextStack,
                X < right.numStackSymbols := by
              intro X hX
              simp only [nextStack, List.mem_append] at hX
              rcases hX with hX | hX
              · obtain ⟨symbol, hsymbol, rfl⟩ := List.mem_map.mp hX
                exact symbol.isLt
              · exact hsuffix X hX
            have hmiddleEq : middle =
                ⟨right.state target.val, rest,
                  right.replacement nextStack⟩ := by
              rw [hmiddle]
              apply PDA.conf.ext
              · apply Fin.ext
                simp [EncodedDPDA.state, Nat.mod_eq_of_lt target.isLt]
              · rfl
              · simp [nextStack, EncodedDPDA.replacement, List.map_append,
                  EncodedDPDA.stackSymbol, List.map_map, Function.comp_def,
                  Nat.mod_eq_of_lt]
            rw [hmiddleEq] at hstep hrest
            cases rest with
            | nil =>
                have htargetSelected : selectedInput?
                    (endmarkedPairMachine left right alphabet)
                    (Endmarked.rightPending left right alphabet q pending) none
                    (Endmarked.rightStack left right Z) =
                      some (rightFinishState left right alphabet target.val,
                        (replacement.map Fin.val).map
                          (Endmarked.rightStack left right)) := by
                  have hlookup := endmarked_selectedInput?_rightPending_eq
                    left right alphabet q Z pending hpending none
                    (by simp [endmarkedAlphabet])
                  rw [hselected] at hlookup
                  simpa [rightFinishState] using hlookup
                have htargetStep := Popping.selectedInput?_toPDA_step
                  (endmarkedPairMachine left right alphabet)
                  (Endmarked.rightPending left right alphabet q pending)
                  (Endmarked.rightStack left right Z) none
                  (rightFinishState left right alphabet target.val)
                  ((replacement.map Fin.val).map
                    (Endmarked.rightStack left right))
                  (suffix.map (Endmarked.rightStack left right) ++
                    [Endmarked.bottom]) [] htargetSelected
                have htargetStep' : @PDA.Reaches₁ _ _ _ _ _ _
                    (endmarkedPairMachine left right alphabet).toDPDA.toPDA
                    ⟨(endmarkedPairMachine left right alphabet).state
                        (Endmarked.rightPending left right alphabet q pending),
                      [none],
                      (endmarkedPairMachine left right alphabet).replacement
                        (rightMappedStack left right (Z :: suffix))⟩
                    ⟨(endmarkedPairMachine left right alphabet).state
                        (rightFinishState left right alphabet target.val),
                      [],
                      (endmarkedPairMachine left right alphabet).replacement
                        (rightMappedStack left right nextStack)⟩ := by
                  simpa [rightMappedStack, nextStack, List.map_append,
                    List.append_assoc] using htargetStep
                exact ⟨target.val, nextStack, target.isLt, hnextStack,
                  Relation.ReflTransGen.single hstep,
                  Relation.ReflTransGen.single htargetStep'⟩
            | cons next tail =>
                have hnextMem : next ∈ alphabet := haustive next
                have htargetSelected : selectedInput?
                    (endmarkedPairMachine left right alphabet)
                    (Endmarked.rightPending left right alphabet q pending)
                    (some next) (Endmarked.rightStack left right Z) =
                      some
                        (Endmarked.rightPending left right alphabet
                            target.val next,
                          (replacement.map Fin.val).map
                            (Endmarked.rightStack left right)) := by
                  have hlookup := endmarked_selectedInput?_rightPending_eq
                    left right alphabet q Z pending hpending (some next)
                    (by simp [endmarkedAlphabet, hnextMem])
                  rw [hselected] at hlookup
                  simpa using hlookup
                have htargetStep := Popping.selectedInput?_toPDA_step
                  (endmarkedPairMachine left right alphabet)
                  (Endmarked.rightPending left right alphabet q pending)
                  (Endmarked.rightStack left right Z) (some next)
                  (Endmarked.rightPending left right alphabet target.val next)
                  ((replacement.map Fin.val).map
                    (Endmarked.rightStack left right))
                  (suffix.map (Endmarked.rightStack left right) ++
                    [Endmarked.bottom])
                  (tail.map some ++ [none]) htargetSelected
                have htargetStep' : @PDA.Reaches₁ _ _ _ _ _ _
                    (endmarkedPairMachine left right alphabet).toDPDA.toPDA
                    ⟨(endmarkedPairMachine left right alphabet).state
                        (Endmarked.rightPending left right alphabet q pending),
                      some next :: (tail.map some ++ [none]),
                      (endmarkedPairMachine left right alphabet).replacement
                        (rightMappedStack left right (Z :: suffix))⟩
                    ⟨(endmarkedPairMachine left right alphabet).state
                        (Endmarked.rightPending left right alphabet
                          target.val next),
                      tail.map some ++ [none],
                      (endmarkedPairMachine left right alphabet).replacement
                        (rightMappedStack left right nextStack)⟩ := by
                  simpa [rightMappedStack, nextStack, List.map_append,
                    List.append_assoc] using htargetStep
                obtain ⟨emptyState, emptyStack, hemptyState, hemptyStack,
                    hsourceRest, htargetRest⟩ :=
                  ih target.val nextStack next tail finalState finalStack
                    target.isLt hnextStack hnextMem hrest
                exact ⟨emptyState, emptyStack, hemptyState, hemptyStack,
                  (Relation.ReflTransGen.single hstep).trans hsourceRest,
                  (Relation.ReflTransGen.single htargetStep').trans
                    htargetRest⟩
          · obtain ⟨target, replacement, hmiddle, hmem⟩ := hepsilon
            have htransition : right.toDPDA.epsilon_transition
                (right.state q) (right.stackSymbol Z) =
                  some (target, replacement) := by
              exact epsilonTransition_eq_some_of_toPDA_mem right.toDPDA
                (right.state q) (right.stackSymbol Z)
                target replacement hmem
            have hselected := selectedEpsilon?_of_transition right q Z
              target replacement htransition
            let nextStack := replacement.map Fin.val ++ suffix
            have hnextStack : ∀ X ∈ nextStack,
                X < right.numStackSymbols := by
              intro X hX
              simp only [nextStack, List.mem_append] at hX
              rcases hX with hX | hX
              · obtain ⟨symbol, hsymbol, rfl⟩ := List.mem_map.mp hX
                exact symbol.isLt
              · exact hsuffix X hX
            have hmiddleEq : middle =
                ⟨right.state target.val, pending :: rest,
                  right.replacement nextStack⟩ := by
              rw [hmiddle]
              apply PDA.conf.ext
              · apply Fin.ext
                simp [EncodedDPDA.state, Nat.mod_eq_of_lt target.isLt]
              · rfl
              · simp [nextStack, EncodedDPDA.replacement, List.map_append,
                  EncodedDPDA.stackSymbol, List.map_map, Function.comp_def,
                  Nat.mod_eq_of_lt]
            rw [hmiddleEq] at hstep hrest
            have htargetSelected : selectedEpsilon?
                (endmarkedPairMachine left right alphabet)
                (Endmarked.rightPending left right alphabet q pending)
                (Endmarked.rightStack left right Z) =
                  some
                    (Endmarked.rightPending left right alphabet
                        target.val pending,
                      (replacement.map Fin.val).map
                        (Endmarked.rightStack left right)) := by
              have hlookup := endmarked_selectedEpsilon?_rightPending_eq
                left right alphabet q Z pending hpending
              rw [hselected] at hlookup
              simpa using hlookup
            have htargetStep := selectedEpsilon?_toPDA_step
              (endmarkedPairMachine left right alphabet)
              (Endmarked.rightPending left right alphabet q pending)
              (Endmarked.rightStack left right Z)
              (Endmarked.rightPending left right alphabet target.val pending)
              ((replacement.map Fin.val).map
                (Endmarked.rightStack left right))
              (suffix.map (Endmarked.rightStack left right) ++
                [Endmarked.bottom])
              (rest.map some ++ [none]) htargetSelected
            have htargetStep' : @PDA.Reaches₁ _ _ _ _ _ _
                (endmarkedPairMachine left right alphabet).toDPDA.toPDA
                ⟨(endmarkedPairMachine left right alphabet).state
                    (Endmarked.rightPending left right alphabet q pending),
                  rest.map some ++ [none],
                  (endmarkedPairMachine left right alphabet).replacement
                    (rightMappedStack left right (Z :: suffix))⟩
                ⟨(endmarkedPairMachine left right alphabet).state
                    (Endmarked.rightPending left right alphabet
                      target.val pending),
                  rest.map some ++ [none],
                  (endmarkedPairMachine left right alphabet).replacement
                    (rightMappedStack left right nextStack)⟩ := by
              simpa [rightMappedStack, nextStack, List.map_append,
                List.append_assoc] using htargetStep
            obtain ⟨emptyState, emptyStack, hemptyState, hemptyStack,
                hsourceRest, htargetRest⟩ :=
              ih target.val nextStack pending rest finalState finalStack
                target.isLt hnextStack hpending hrest
            exact ⟨emptyState, emptyStack, hemptyState, hemptyStack,
              (Relation.ReflTransGen.single hstep).trans hsourceRest,
              (Relation.ReflTransGen.single htargetStep').trans htargetRest⟩

private theorem endmarked_accept_reaches_empty
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    ∀ (stack : List ℕ),
      (∀ Z ∈ stack, Z < Endmarked.stackCount left right) →
      @PDA.Reaches _ _ _ _ _ _
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.acceptState left right alphabet),
          [],
          (endmarkedPairMachine left right alphabet).replacement stack⟩
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.acceptState left right alphabet),
          [], []⟩ := by
  intro stack hstack
  induction stack with
  | nil => exact Relation.ReflTransGen.refl
  | cons Z stack ih =>
      have hZ : Z < Endmarked.stackCount left right := hstack Z (by simp)
      have hrest : ∀ X ∈ stack,
          X < Endmarked.stackCount left right := by
        intro X hX
        exact hstack X (by simp [hX])
      have hselected := endmarked_selectedEpsilon?_accept_eq
        left right alphabet Z hZ
      have hstep := selectedEpsilon?_toPDA_step
        (endmarkedPairMachine left right alphabet)
        (Endmarked.acceptState left right alphabet) Z
        (Endmarked.acceptState left right alphabet) [] stack [] hselected
      have hstep' : @PDA.Reaches₁ _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              (Endmarked.acceptState left right alphabet),
            [],
            (endmarkedPairMachine left right alphabet).replacement
              (Z :: stack)⟩
          ⟨(endmarkedPairMachine left right alphabet).state
              (Endmarked.acceptState left right alphabet),
            [],
            (endmarkedPairMachine left right alphabet).replacement stack⟩ := by
        simpa [EncodedDPDA.replacement] using hstep
      exact (Relation.ReflTransGen.single hstep').trans (ih hrest)

private theorem endmarked_reject_cannot_reach_empty
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (stack : List ℕ) (hne : stack ≠ []) :
    ¬ ∃ target,
      @PDA.Reaches _ _ _ _ _ _
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.rejectState left right alphabet),
          [],
          (endmarkedPairMachine left right alphabet).replacement stack⟩
        ⟨(endmarkedPairMachine left right alphabet).state target, [], []⟩ := by
  rintro ⟨target, hreach⟩
  obtain ⟨Z, suffix, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hselected := endmarked_selectedEpsilon?_reject_eq_none
    left right alphabet Z
  have hepsilon :
      (endmarkedPairMachine left right alphabet).toDPDA.epsilon_transition
        ((endmarkedPairMachine left right alphabet).state
          (Endmarked.rejectState left right alphabet))
        ((endmarkedPairMachine left right alphabet).stackSymbol Z) = none := by
    rw [selectedEpsilon?_eq_epsilonStep?] at hselected
    unfold DPDAToFirstOrder.Machine.epsilonStep? at hselected
    exact Option.map_eq_none_iff.mp hselected
  have hstable :
      (endmarkedPairMachine left right alphabet).toDPDA.EpsilonStable
        ((endmarkedPairMachine left right alphabet).state
            (Endmarked.rejectState left right alphabet),
          (endmarkedPairMachine left right alphabet).replacement
            (Z :: suffix)) := by
    change (endmarkedPairMachine left right alphabet).toDPDA.epsilon_transition
      ((endmarkedPairMachine left right alphabet).state
        (Endmarked.rejectState left right alphabet))
      ((endmarkedPairMachine left right alphabet).stackSymbol Z) = none
    exact hepsilon
  have heq := Popping.pdaReaches_eq_self_of_epsilonStable hstable hreach
  have hstackEq := congrArg PDA.conf.stack heq
  simp [EncodedDPDA.replacement] at hstackEq

private theorem left_canonical_endmarked_run
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (hvalid : EncodedDPDA.Valid left)
    (haustive : ∀ action, action ∈ alphabet) (word : List Action) :
    ∃ sourceState sourceStack targetStack,
      sourceState < left.numStates ∧
      (∀ Z ∈ sourceStack, Z < left.numStackSymbols) ∧
      targetStack ≠ [] ∧
      (∀ Z ∈ targetStack, Z < Endmarked.stackCount left right) ∧
      @PDA.Reaches _ _ _ _ _ _ left.toDPDA.toPDA
        ⟨left.toDPDA.initial_state, word, [left.toDPDA.start_symbol]⟩
        ⟨left.state sourceState, [], left.replacement sourceStack⟩ ∧
      @PDA.Reaches _ _ _ _ _ _
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA
        ⟨(endmarkedPairMachine left right alphabet).state
            Endmarked.leftStart,
          word.map some ++ [none],
          (endmarkedPairMachine left right alphabet).replacement
            [Endmarked.bottom]⟩
        ⟨(endmarkedPairMachine left right alphabet).state
            (leftFinishState left right alphabet sourceState),
          [],
          (endmarkedPairMachine left right alphabet).replacement
            targetStack⟩ := by
  cases word with
  | nil =>
      let sourceState := left.initialIndex % left.numStates
      let sourceStack := [left.startIndex % left.numStackSymbols]
      let targetStack := [Endmarked.bottom]
      have hsourceState : sourceState < left.numStates :=
        Nat.mod_lt _ left.numStates_pos
      have hsourceStack : ∀ Z ∈ sourceStack,
          Z < left.numStackSymbols := by
        intro Z hZ
        simp only [sourceStack, List.mem_singleton] at hZ
        subst Z
        exact Nat.mod_lt _ left.numStackSymbols_pos
      have htargetStack : ∀ Z ∈ targetStack,
          Z < Endmarked.stackCount left right := by
        intro Z hZ
        simp only [targetStack, List.mem_singleton] at hZ
        subst Z
        simp [Endmarked.bottom, Endmarked.stackCount]
      have hselected := endmarked_selectedInput?_leftStart_eq
        left right alphabet none (by simp [endmarkedAlphabet])
      have hselected' : selectedInput?
          (endmarkedPairMachine left right alphabet)
          Endmarked.leftStart none Endmarked.bottom =
            some (leftFinishState left right alphabet sourceState,
              targetStack) := by
        simpa [leftFinishState, sourceState, targetStack,
          Endmarked.isFinalIndex, Nat.mod_mod] using hselected
      have hstep := Popping.selectedInput?_toPDA_step
        (endmarkedPairMachine left right alphabet)
        Endmarked.leftStart Endmarked.bottom none
        (leftFinishState left right alphabet sourceState) targetStack [] []
        hselected'
      refine ⟨sourceState, sourceStack, targetStack, hsourceState,
        hsourceStack, by simp [targetStack], htargetStack, ?_, ?_⟩
      · simpa [sourceState, sourceStack, state_initial_mod,
          replacement_start_mod] using
          (Relation.ReflTransGen.refl : @PDA.Reaches _ _ _ _ _ _
            left.toDPDA.toPDA
            ⟨left.toDPDA.initial_state, [], [left.toDPDA.start_symbol]⟩
            ⟨left.toDPDA.initial_state, [], [left.toDPDA.start_symbol]⟩)
      · simpa [targetStack, EncodedDPDA.replacement] using
          (Relation.ReflTransGen.single hstep)
  | cons pending rest =>
      obtain ⟨finalState, finalStack, hsource⟩ := hvalid.1 (pending :: rest)
      obtain ⟨steps, hsourceSteps⟩ :=
        (PDA.reaches_iff_reachesIn.mp hsource)
      have hsourceSteps' : @PDA.ReachesIn _ _ _ _ _ _ left.toDPDA.toPDA
          steps
          ⟨left.state (left.initialIndex % left.numStates),
            pending :: rest,
            left.replacement [left.startIndex % left.numStackSymbols]⟩
          ⟨finalState, [], finalStack⟩ := by
        simpa [state_initial_mod, replacement_start_mod] using hsourceSteps
      obtain ⟨sourceState, sourceStack, hsourceState, hsourceStack,
          hsourceReach, htargetReach⟩ :=
        left_simulates_until_empty_in left right alphabet haustive steps
          (left.initialIndex % left.numStates)
          [left.startIndex % left.numStackSymbols] pending rest
          finalState finalStack
          (Nat.mod_lt _ left.numStates_pos)
          (by
            intro Z hZ
            simp only [List.mem_singleton] at hZ
            subst Z
            exact Nat.mod_lt _ left.numStackSymbols_pos)
          (haustive pending) hsourceSteps'
      let targetStack := leftMappedStack left sourceStack
      have htargetNe : targetStack ≠ [] := by
        simp [targetStack, leftMappedStack]
      have htargetStack : ∀ Z ∈ targetStack,
          Z < Endmarked.stackCount left right := by
        intro Z hZ
        simp only [targetStack, leftMappedStack, List.mem_append,
          List.mem_map, List.mem_singleton] at hZ
        rcases hZ with ⟨X, _, rfl⟩ | rfl
        · exact Endmarked.leftStack_lt_stackCount left right X
        · simp [Endmarked.bottom, Endmarked.stackCount]
      have hselected := endmarked_selectedInput?_leftStart_eq
        left right alphabet (some pending)
          (by simp [endmarkedAlphabet, haustive pending])
      have hstart := Popping.selectedInput?_toPDA_step
        (endmarkedPairMachine left right alphabet)
        Endmarked.leftStart Endmarked.bottom (some pending)
        (Endmarked.leftPending left alphabet left.initialIndex pending)
        [Endmarked.leftStack left left.startIndex, Endmarked.bottom] []
        (rest.map some ++ [none]) (by simpa using hselected)
      have hstart' : @PDA.Reaches₁ _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              Endmarked.leftStart,
            (pending :: rest).map some ++ [none],
            (endmarkedPairMachine left right alphabet).replacement
              [Endmarked.bottom]⟩
          ⟨(endmarkedPairMachine left right alphabet).state
              (Endmarked.leftPending left alphabet
                (left.initialIndex % left.numStates) pending),
            rest.map some ++ [none],
            (endmarkedPairMachine left right alphabet).replacement
              (leftMappedStack left
                [left.startIndex % left.numStackSymbols])⟩ := by
        simpa [leftMappedStack, Endmarked.leftPending,
          Endmarked.pendingIndex, Endmarked.leftStack, Nat.mod_mod,
          EncodedDPDA.replacement] using hstart
      refine ⟨sourceState, sourceStack, targetStack, hsourceState,
        hsourceStack, htargetNe, htargetStack, ?_, ?_⟩
      · simpa [state_initial_mod, replacement_start_mod] using hsourceReach
      · exact (Relation.ReflTransGen.single hstart').trans
          (by simpa [targetStack] using htargetReach)

private theorem right_canonical_endmarked_run
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (hvalid : EncodedDPDA.Valid right)
    (haustive : ∀ action, action ∈ alphabet) (word : List Action) :
    ∃ sourceState sourceStack targetStack,
      sourceState < right.numStates ∧
      (∀ Z ∈ sourceStack, Z < right.numStackSymbols) ∧
      targetStack ≠ [] ∧
      (∀ Z ∈ targetStack, Z < Endmarked.stackCount left right) ∧
      @PDA.Reaches _ _ _ _ _ _ right.toDPDA.toPDA
        ⟨right.toDPDA.initial_state, word, [right.toDPDA.start_symbol]⟩
        ⟨right.state sourceState, [], right.replacement sourceStack⟩ ∧
      @PDA.Reaches _ _ _ _ _ _
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA
        ⟨(endmarkedPairMachine left right alphabet).state
            Endmarked.rightStart,
          word.map some ++ [none],
          (endmarkedPairMachine left right alphabet).replacement
            [Endmarked.bottom]⟩
        ⟨(endmarkedPairMachine left right alphabet).state
            (rightFinishState left right alphabet sourceState),
          [],
          (endmarkedPairMachine left right alphabet).replacement
            targetStack⟩ := by
  cases word with
  | nil =>
      let sourceState := right.initialIndex % right.numStates
      let sourceStack := [right.startIndex % right.numStackSymbols]
      let targetStack := [Endmarked.bottom]
      have hsourceState : sourceState < right.numStates :=
        Nat.mod_lt _ right.numStates_pos
      have hsourceStack : ∀ Z ∈ sourceStack,
          Z < right.numStackSymbols := by
        intro Z hZ
        simp only [sourceStack, List.mem_singleton] at hZ
        subst Z
        exact Nat.mod_lt _ right.numStackSymbols_pos
      have htargetStack : ∀ Z ∈ targetStack,
          Z < Endmarked.stackCount left right := by
        intro Z hZ
        simp only [targetStack, List.mem_singleton] at hZ
        subst Z
        simp [Endmarked.bottom, Endmarked.stackCount]
      have hselected := endmarked_selectedInput?_rightStart_eq
        left right alphabet none (by simp [endmarkedAlphabet])
      have hselected' : selectedInput?
          (endmarkedPairMachine left right alphabet)
          Endmarked.rightStart none Endmarked.bottom =
            some (rightFinishState left right alphabet sourceState,
              targetStack) := by
        simpa [rightFinishState, sourceState, targetStack,
          Endmarked.isFinalIndex, Nat.mod_mod] using hselected
      have hstep := Popping.selectedInput?_toPDA_step
        (endmarkedPairMachine left right alphabet)
        Endmarked.rightStart Endmarked.bottom none
        (rightFinishState left right alphabet sourceState) targetStack [] []
        hselected'
      refine ⟨sourceState, sourceStack, targetStack, hsourceState,
        hsourceStack, by simp [targetStack], htargetStack, ?_, ?_⟩
      · simpa [sourceState, sourceStack, state_initial_mod,
          replacement_start_mod] using
          (Relation.ReflTransGen.refl : @PDA.Reaches _ _ _ _ _ _
            right.toDPDA.toPDA
            ⟨right.toDPDA.initial_state, [], [right.toDPDA.start_symbol]⟩
            ⟨right.toDPDA.initial_state, [], [right.toDPDA.start_symbol]⟩)
      · simpa [targetStack, EncodedDPDA.replacement] using
          (Relation.ReflTransGen.single hstep)
  | cons pending rest =>
      obtain ⟨finalState, finalStack, hsource⟩ := hvalid.1 (pending :: rest)
      obtain ⟨steps, hsourceSteps⟩ :=
        (PDA.reaches_iff_reachesIn.mp hsource)
      have hsourceSteps' : @PDA.ReachesIn _ _ _ _ _ _ right.toDPDA.toPDA
          steps
          ⟨right.state (right.initialIndex % right.numStates),
            pending :: rest,
            right.replacement [right.startIndex % right.numStackSymbols]⟩
          ⟨finalState, [], finalStack⟩ := by
        simpa [state_initial_mod, replacement_start_mod] using hsourceSteps
      obtain ⟨sourceState, sourceStack, hsourceState, hsourceStack,
          hsourceReach, htargetReach⟩ :=
        right_simulates_until_empty_in left right alphabet haustive steps
          (right.initialIndex % right.numStates)
          [right.startIndex % right.numStackSymbols] pending rest
          finalState finalStack
          (Nat.mod_lt _ right.numStates_pos)
          (by
            intro Z hZ
            simp only [List.mem_singleton] at hZ
            subst Z
            exact Nat.mod_lt _ right.numStackSymbols_pos)
          (haustive pending) hsourceSteps'
      let targetStack := rightMappedStack left right sourceStack
      have htargetNe : targetStack ≠ [] := by
        simp [targetStack, rightMappedStack]
      have htargetStack : ∀ Z ∈ targetStack,
          Z < Endmarked.stackCount left right := by
        intro Z hZ
        simp only [targetStack, rightMappedStack, List.mem_append,
          List.mem_map, List.mem_singleton] at hZ
        rcases hZ with ⟨X, _, rfl⟩ | rfl
        · exact Endmarked.rightStack_lt_stackCount left right X
        · simp [Endmarked.bottom, Endmarked.stackCount]
      have hselected := endmarked_selectedInput?_rightStart_eq
        left right alphabet (some pending)
          (by simp [endmarkedAlphabet, haustive pending])
      have hstart := Popping.selectedInput?_toPDA_step
        (endmarkedPairMachine left right alphabet)
        Endmarked.rightStart Endmarked.bottom (some pending)
        (Endmarked.rightPending left right alphabet right.initialIndex pending)
        [Endmarked.rightStack left right right.startIndex, Endmarked.bottom] []
        (rest.map some ++ [none]) (by simpa using hselected)
      have hstart' : @PDA.Reaches₁ _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              Endmarked.rightStart,
            (pending :: rest).map some ++ [none],
            (endmarkedPairMachine left right alphabet).replacement
              [Endmarked.bottom]⟩
          ⟨(endmarkedPairMachine left right alphabet).state
              (Endmarked.rightPending left right alphabet
                (right.initialIndex % right.numStates) pending),
            rest.map some ++ [none],
            (endmarkedPairMachine left right alphabet).replacement
              (rightMappedStack left right
                [right.startIndex % right.numStackSymbols])⟩ := by
        simpa [rightMappedStack, Endmarked.rightPending,
          Endmarked.pendingIndex, Endmarked.rightStack, Nat.mod_mod,
          EncodedDPDA.replacement] using hstart
      refine ⟨sourceState, sourceStack, targetStack, hsourceState,
        hsourceStack, htargetNe, htargetStack, ?_, ?_⟩
      · simpa [state_initial_mod, replacement_start_mod] using hsourceReach
      · exact (Relation.ReflTransGen.single hstart').trans
          (by simpa [targetStack] using htargetReach)

private theorem endmarked_inputRow_source_lt_accept
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (row : InputRow (Option Action))
    (hrow : row ∈ (endmarkedPairMachine left right alphabet).inputRows) :
    row.1 < Endmarked.acceptState left right alphabet := by
  rcases (mem_endmarked_inputRows_iff left right alphabet row).mp hrow with
    hstart | hleft | hright
  · have hlt := Endmarked.startRows_source_lt_leftPendingBase
      left right alphabet hstart
    unfold Endmarked.acceptState Endmarked.rightPendingBase
    omega
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, next, hnext, rfl⟩ :=
      (Endmarked.mem_embeddedInputRows_iff left alphabet
        (Endmarked.leftPending left alphabet) (Endmarked.leftStack left)
        (fun state =>
          if Endmarked.isFinalIndex left state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) _).mp
        (by simpa [Endmarked.leftInputRows] using hleft)
    exact (Endmarked.leftPending_lt_rightPendingBase
      (q := sourceState) left hstored).trans_le (by
        simp [Endmarked.acceptState])
  · obtain ⟨stored, hstored, sourceState, hsourceState, sourceTop,
        hsourceTop, target, replacement, hstep, next, hnext, rfl⟩ :=
      (Endmarked.mem_embeddedInputRows_iff right alphabet
        (Endmarked.rightPending left right alphabet)
        (Endmarked.rightStack left right)
        (fun state =>
          if Endmarked.isFinalIndex right state then
            Endmarked.acceptState left right alphabet
          else Endmarked.rejectState left right alphabet) _).mp
        (by simpa [Endmarked.rightInputRows] using hright)
    exact Endmarked.rightPending_lt_acceptState
      (q := sourceState) left right hstored

private theorem endmarked_selectedInput?_reject_eq_none
    [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (action : Option Action) (Z : ℕ) :
    selectedInput? (endmarkedPairMachine left right alphabet)
      (Endmarked.rejectState left right alphabet) action Z = none := by
  unfold selectedInput?
  rw [endmarked_selectedEpsilon?_reject_eq_none]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false]
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro row hrow hmatch
  simp only [decide_eq_true_eq] at hmatch
  have hrowLt := endmarked_inputRow_source_lt_accept
    left right alphabet row hrow
  have hrowState : row.1 < Endmarked.stateCount left right alphabet :=
    hrowLt.trans (Endmarked.acceptState_lt_stateCount left right alphabet)
  have hreject := Endmarked.rejectState_lt_stateCount left right alphabet
  have hstateEq : row.1 = Endmarked.rejectState left right alphabet := by
    simpa [endmarkedPairMachine_numStates,
      Nat.mod_eq_of_lt hrowState, Nat.mod_eq_of_lt hreject] using hmatch.1
  unfold Endmarked.rejectState at hstateEq
  omega

private theorem endmarked_reject_cannot_reach_empty_with_input
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (input : List (Option Action)) (stack : List ℕ) (hne : stack ≠ []) :
    ¬ ∃ target,
      @PDA.Reaches _ _ _ _ _ _
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.rejectState left right alphabet),
          input,
          (endmarkedPairMachine left right alphabet).replacement stack⟩
        ⟨(endmarkedPairMachine left right alphabet).state target, [], []⟩ := by
  rintro ⟨target, hreach⟩
  obtain ⟨Z, suffix, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hepsilonRaw := endmarked_selectedEpsilon?_reject_eq_none
    left right alphabet Z
  have hepsilon :
      (endmarkedPairMachine left right alphabet).toDPDA.epsilon_transition
        ((endmarkedPairMachine left right alphabet).state
          (Endmarked.rejectState left right alphabet))
        ((endmarkedPairMachine left right alphabet).stackSymbol Z) = none := by
    rw [selectedEpsilon?_eq_epsilonStep?] at hepsilonRaw
    unfold DPDAToFirstOrder.Machine.epsilonStep? at hepsilonRaw
    exact Option.map_eq_none_iff.mp hepsilonRaw
  have hnoStep : ¬ ∃ next,
      @PDA.Reaches₁ _ _ _ _ _ _
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.rejectState left right alphabet),
          input,
          (endmarkedPairMachine left right alphabet).replacement
            (Z :: suffix)⟩ next := by
    rintro ⟨next, hstep⟩
    cases input with
    | nil =>
        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hepsilon,
          EncodedDPDA.replacement] at hstep
    | cons action rest =>
        have hinputRaw := endmarked_selectedInput?_reject_eq_none
          left right alphabet action Z
        have hinput :
            (endmarkedPairMachine left right alphabet).toDPDA.transition
              ((endmarkedPairMachine left right alphabet).state
                (Endmarked.rejectState left right alphabet)) action
              ((endmarkedPairMachine left right alphabet).stackSymbol Z) =
                none := by
          rw [selectedInput?_eq_inputStep?] at hinputRaw
          rw [selectedEpsilon?_eq_epsilonStep?] at hepsilonRaw
          simp only [hepsilonRaw, Option.isSome_none, Bool.false_eq_true,
            if_false] at hinputRaw
          unfold DPDAToFirstOrder.Machine.inputStep? at hinputRaw
          have hlookup := Option.map_eq_none_iff.mp hinputRaw
          change (if ((endmarkedPairMachine left right alphabet).epsilonLookup
              ((endmarkedPairMachine left right alphabet).state
                (Endmarked.rejectState left right alphabet))
              ((endmarkedPairMachine left right alphabet).stackSymbol Z)).isSome
            then none
            else (endmarkedPairMachine left right alphabet).inputLookup
              ((endmarkedPairMachine left right alphabet).state
                (Endmarked.rejectState left right alphabet)) action
              ((endmarkedPairMachine left right alphabet).stackSymbol Z)) = none
          change (endmarkedPairMachine left right alphabet).epsilonLookup
              ((endmarkedPairMachine left right alphabet).state
                (Endmarked.rejectState left right alphabet))
              ((endmarkedPairMachine left right alphabet).stackSymbol Z) = none
            at hepsilon
          rw [hepsilon]
          simp [hlookup]
        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hepsilon, hinput,
          EncodedDPDA.replacement] at hstep
  rw [PDA.reaches_iff_reachesIn] at hreach
  obtain ⟨steps, hsteps⟩ := hreach
  cases steps with
  | zero =>
      have heq := PDA.reachesIn_zero hsteps
      have hstackEq := congrArg PDA.conf.stack heq
      simp [EncodedDPDA.replacement] at hstackEq
  | succ steps =>
      obtain ⟨middle, hfirst, _⟩ :=
        PDA.reachesIn_iff_split_first.mpr hsteps
      exact hnoStep ⟨middle, PDA.reaches₁_iff_reachesIn_one.mpr hfirst⟩

private theorem left_finish_reaches_empty
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (sourceState : ℕ) (input : List (Option Action)) (stack : List ℕ)
    (hstack : ∀ Z ∈ stack, Z < Endmarked.stackCount left right)
    (hne : stack ≠ []) (target : ℕ)
    (hreach : @PDA.Reaches _ _ _ _ _ _
      (endmarkedPairMachine left right alphabet).toDPDA.toPDA
      ⟨(endmarkedPairMachine left right alphabet).state
          (leftFinishState left right alphabet sourceState),
        input,
        (endmarkedPairMachine left right alphabet).replacement stack⟩
      ⟨(endmarkedPairMachine left right alphabet).state target, [], []⟩) :
    input = [] ∧ Endmarked.isFinalIndex left sourceState = true := by
  by_cases hfinal : Endmarked.isFinalIndex left sourceState = true
  · have hfinish : leftFinishState left right alphabet sourceState =
        Endmarked.acceptState left right alphabet := by
      simp [leftFinishState, hfinal]
    rw [hfinish] at hreach
    have hdrain := endmarked_accept_reaches_empty
      left right alphabet stack hstack
    have hdrain' : @PDA.Reaches _ _ _ _ _ _
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.acceptState left right alphabet),
          input,
          (endmarkedPairMachine left right alphabet).replacement stack⟩
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.acceptState left right alphabet),
          input, []⟩ := by
      exact (PDA.unconsumed_input (pda :=
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA) input).mp
          hdrain
    rcases (endmarkedPairMachine left right alphabet).toDPDA.toPDA_reaches_comparable
        hreach hdrain' with hcompare | hcompare
    · exact ⟨(PDA.reaches_on_empty_stack hcompare).1.symm, hfinal⟩
    · exact ⟨(PDA.reaches_on_empty_stack hcompare).1, hfinal⟩
  · have hfalse : Endmarked.isFinalIndex left sourceState = false :=
      Bool.eq_false_of_not_eq_true hfinal
    have hfinish : leftFinishState left right alphabet sourceState =
        Endmarked.rejectState left right alphabet := by
      simp [leftFinishState, hfalse]
    rw [hfinish] at hreach
    exact (endmarked_reject_cannot_reach_empty_with_input
      left right alphabet input stack hne ⟨target, hreach⟩).elim

private theorem right_finish_reaches_empty
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (sourceState : ℕ) (input : List (Option Action)) (stack : List ℕ)
    (hstack : ∀ Z ∈ stack, Z < Endmarked.stackCount left right)
    (hne : stack ≠ []) (target : ℕ)
    (hreach : @PDA.Reaches _ _ _ _ _ _
      (endmarkedPairMachine left right alphabet).toDPDA.toPDA
      ⟨(endmarkedPairMachine left right alphabet).state
          (rightFinishState left right alphabet sourceState),
        input,
        (endmarkedPairMachine left right alphabet).replacement stack⟩
      ⟨(endmarkedPairMachine left right alphabet).state target, [], []⟩) :
    input = [] ∧ Endmarked.isFinalIndex right sourceState = true := by
  by_cases hfinal : Endmarked.isFinalIndex right sourceState = true
  · have hfinish : rightFinishState left right alphabet sourceState =
        Endmarked.acceptState left right alphabet := by
      simp [rightFinishState, hfinal]
    rw [hfinish] at hreach
    have hdrain := endmarked_accept_reaches_empty
      left right alphabet stack hstack
    have hdrain' : @PDA.Reaches _ _ _ _ _ _
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.acceptState left right alphabet),
          input,
          (endmarkedPairMachine left right alphabet).replacement stack⟩
        ⟨(endmarkedPairMachine left right alphabet).state
            (Endmarked.acceptState left right alphabet),
          input, []⟩ := by
      exact (PDA.unconsumed_input (pda :=
        (endmarkedPairMachine left right alphabet).toDPDA.toPDA) input).mp
          hdrain
    rcases (endmarkedPairMachine left right alphabet).toDPDA.toPDA_reaches_comparable
        hreach hdrain' with hcompare | hcompare
    · exact ⟨(PDA.reaches_on_empty_stack hcompare).1.symm, hfinal⟩
    · exact ⟨(PDA.reaches_on_empty_stack hcompare).1, hfinal⟩
  · have hfalse : Endmarked.isFinalIndex right sourceState = false :=
      Bool.eq_false_of_not_eq_true hfinal
    have hfinish : rightFinishState left right alphabet sourceState =
        Endmarked.rejectState left right alphabet := by
      simp [rightFinishState, hfalse]
    rw [hfinish] at hreach
    exact (endmarked_reject_cannot_reach_empty_with_input
      left right alphabet input stack hne ⟨target, hreach⟩).elim

private theorem optionWord_decomposition (word : List (Option Action)) :
    (∃ sourceWord : List Action,
      word = sourceWord.map (Option.some : Action → Option Action)) ∨
      ∃ (sourceWord : List Action) (suffix : List (Option Action)),
        word = sourceWord.map (Option.some : Action → Option Action) ++
          none :: suffix := by
  induction word with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons head tail ih =>
      cases head with
      | none => exact Or.inr ⟨[], tail, by simp⟩
      | some action =>
          rcases ih with ⟨sourceWord, rfl⟩ | ⟨sourceWord, suffix, rfl⟩
          · exact Or.inl ⟨action :: sourceWord, by simp⟩
          · exact Or.inr ⟨action :: sourceWord, suffix, by simp⟩

public theorem leftEndmarkedLanguage_eq
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (hvalid : EncodedDPDA.Valid left)
    (haustive : ∀ action, action ∈ alphabet) :
    sourceEmptyStackLanguage (endmarkedPairMachine left right alphabet)
        (leftEndmarkedConfiguration left right alphabet) =
      {word | ∃ sourceWord ∈ EncodedDPDA.language left,
        word = sourceWord.map some ++ [none]} := by
  ext word
  constructor
  · rintro ⟨target, haccepted⟩
    rcases optionWord_decomposition word with
      ⟨sourceWord, hword⟩ | ⟨sourceWord, suffix, hword⟩
    · obtain ⟨sourceState, sourceStack, targetStack, hsourceState,
          hsourceStack, htargetNe, htargetStack, hsourceReach,
          hcanonical⟩ :=
        left_canonical_endmarked_run left right alphabet hvalid haustive
          sourceWord
      have hlift : @PDA.Reaches _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              Endmarked.leftStart,
            sourceWord.map some ++ [none],
            (endmarkedPairMachine left right alphabet).replacement
              [Endmarked.bottom]⟩
          ⟨(endmarkedPairMachine left right alphabet).state target,
            [none], []⟩ := by
        have happended := (PDA.unconsumed_input (pda :=
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA)
            [none]).mp haccepted
        simpa [sourceEmptyStackLanguage, leftEndmarkedConfiguration,
          hword, PDA.conf.appendInput, List.append_assoc] using happended
      rcases (endmarkedPairMachine left right alphabet).toDPDA.toPDA_reaches_comparable
          hlift hcanonical with hcompare | hcompare
      · have hstackEmpty := (PDA.reaches_on_empty_stack hcompare).2.1
        have : targetStack = [] := by
          simpa [EncodedDPDA.replacement] using hstackEmpty
        exact (htargetNe this).elim
      · obtain ⟨consumed, hinput⟩ := PDA.decreasing_input hcompare
        simp at hinput
    · subst word
      obtain ⟨sourceState, sourceStack, targetStack, hsourceState,
          hsourceStack, htargetNe, htargetStack, hsourceReach,
          hcanonical⟩ :=
        left_canonical_endmarked_run left right alphabet hvalid haustive
          sourceWord
      have hlift : @PDA.Reaches _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              Endmarked.leftStart,
            sourceWord.map some ++ none :: suffix,
            (endmarkedPairMachine left right alphabet).replacement
              [Endmarked.bottom]⟩
          ⟨(endmarkedPairMachine left right alphabet).state
              (leftFinishState left right alphabet sourceState),
            suffix,
            (endmarkedPairMachine left right alphabet).replacement
              targetStack⟩ := by
        have happended := (PDA.unconsumed_input (pda :=
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA)
            suffix).mp hcanonical
        simpa [PDA.conf.appendInput, List.append_assoc] using happended
      rcases (endmarkedPairMachine left right alphabet).toDPDA.toPDA_reaches_comparable
          hlift haccepted with hcompare | hcompare
      · obtain ⟨rfl, hfinal⟩ := left_finish_reaches_empty
          left right alphabet sourceState suffix targetStack htargetStack
          htargetNe target hcompare
        have hsourceFinal : left.state sourceState ∈
            left.toDPDA.final_states :=
          (Endmarked.isFinalIndex_eq_true_iff left sourceState).mp hfinal
        refine ⟨sourceWord, ?_, by simp⟩
        exact ⟨left.state sourceState, hsourceFinal,
          left.replacement sourceStack, hsourceReach⟩
      · have hstackEmpty := (PDA.reaches_on_empty_stack hcompare).2.1
        have : targetStack = [] := by
          simpa [EncodedDPDA.replacement] using hstackEmpty
        exact (htargetNe this).elim
  · rintro ⟨sourceWord, hsourceWord, rfl⟩
    obtain ⟨sourceState, sourceStack, targetStack, hsourceState,
        hsourceStack, htargetNe, htargetStack, hsourceReach,
        hcanonical⟩ :=
      left_canonical_endmarked_run left right alphabet hvalid haustive
        sourceWord
    rcases hsourceWord with ⟨acceptState, hacceptState, acceptStack,
      hacceptReach⟩
    have hconsistency := hvalid.2 sourceWord acceptState
      (left.state sourceState) acceptStack (left.replacement sourceStack)
      hacceptReach hsourceReach
    have hsourceFinal : left.state sourceState ∈ left.toDPDA.final_states :=
      hconsistency.mp hacceptState
    have hfinal : Endmarked.isFinalIndex left sourceState = true :=
      (Endmarked.isFinalIndex_eq_true_iff left sourceState).mpr hsourceFinal
    have hfinish : leftFinishState left right alphabet sourceState =
        Endmarked.acceptState left right alphabet := by
      simp [leftFinishState, hfinal]
    rw [hfinish] at hcanonical
    have hdrain := endmarked_accept_reaches_empty
      left right alphabet targetStack htargetStack
    exact ⟨Endmarked.acceptState left right alphabet,
      hcanonical.trans hdrain⟩

public theorem rightEndmarkedLanguage_eq
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (hvalid : EncodedDPDA.Valid right)
    (haustive : ∀ action, action ∈ alphabet) :
    sourceEmptyStackLanguage (endmarkedPairMachine left right alphabet)
        (rightEndmarkedConfiguration left right alphabet) =
      {word | ∃ sourceWord ∈ EncodedDPDA.language right,
        word = sourceWord.map some ++ [none]} := by
  ext word
  constructor
  · rintro ⟨target, haccepted⟩
    rcases optionWord_decomposition word with
      ⟨sourceWord, hword⟩ | ⟨sourceWord, suffix, hword⟩
    · obtain ⟨sourceState, sourceStack, targetStack, hsourceState,
          hsourceStack, htargetNe, htargetStack, hsourceReach,
          hcanonical⟩ :=
        right_canonical_endmarked_run left right alphabet hvalid haustive
          sourceWord
      have hlift : @PDA.Reaches _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              Endmarked.rightStart,
            sourceWord.map some ++ [none],
            (endmarkedPairMachine left right alphabet).replacement
              [Endmarked.bottom]⟩
          ⟨(endmarkedPairMachine left right alphabet).state target,
            [none], []⟩ := by
        have happended := (PDA.unconsumed_input (pda :=
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA)
            [none]).mp haccepted
        simpa [sourceEmptyStackLanguage, rightEndmarkedConfiguration,
          hword, PDA.conf.appendInput, List.append_assoc] using happended
      rcases (endmarkedPairMachine left right alphabet).toDPDA.toPDA_reaches_comparable
          hlift hcanonical with hcompare | hcompare
      · have hstackEmpty := (PDA.reaches_on_empty_stack hcompare).2.1
        have : targetStack = [] := by
          simpa [EncodedDPDA.replacement] using hstackEmpty
        exact (htargetNe this).elim
      · obtain ⟨consumed, hinput⟩ := PDA.decreasing_input hcompare
        simp at hinput
    · subst word
      obtain ⟨sourceState, sourceStack, targetStack, hsourceState,
          hsourceStack, htargetNe, htargetStack, hsourceReach,
          hcanonical⟩ :=
        right_canonical_endmarked_run left right alphabet hvalid haustive
          sourceWord
      have hlift : @PDA.Reaches _ _ _ _ _ _
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA
          ⟨(endmarkedPairMachine left right alphabet).state
              Endmarked.rightStart,
            sourceWord.map some ++ none :: suffix,
            (endmarkedPairMachine left right alphabet).replacement
              [Endmarked.bottom]⟩
          ⟨(endmarkedPairMachine left right alphabet).state
              (rightFinishState left right alphabet sourceState),
            suffix,
            (endmarkedPairMachine left right alphabet).replacement
              targetStack⟩ := by
        have happended := (PDA.unconsumed_input (pda :=
          (endmarkedPairMachine left right alphabet).toDPDA.toPDA)
            suffix).mp hcanonical
        simpa [PDA.conf.appendInput, List.append_assoc] using happended
      rcases (endmarkedPairMachine left right alphabet).toDPDA.toPDA_reaches_comparable
          hlift haccepted with hcompare | hcompare
      · obtain ⟨rfl, hfinal⟩ := right_finish_reaches_empty
          left right alphabet sourceState suffix targetStack htargetStack
          htargetNe target hcompare
        have hsourceFinal : right.state sourceState ∈
            right.toDPDA.final_states :=
          (Endmarked.isFinalIndex_eq_true_iff right sourceState).mp hfinal
        refine ⟨sourceWord, ?_, by simp⟩
        exact ⟨right.state sourceState, hsourceFinal,
          right.replacement sourceStack, hsourceReach⟩
      · have hstackEmpty := (PDA.reaches_on_empty_stack hcompare).2.1
        have : targetStack = [] := by
          simpa [EncodedDPDA.replacement] using hstackEmpty
        exact (htargetNe this).elim
  · rintro ⟨sourceWord, hsourceWord, rfl⟩
    obtain ⟨sourceState, sourceStack, targetStack, hsourceState,
        hsourceStack, htargetNe, htargetStack, hsourceReach,
        hcanonical⟩ :=
      right_canonical_endmarked_run left right alphabet hvalid haustive
        sourceWord
    rcases hsourceWord with ⟨acceptState, hacceptState, acceptStack,
      hacceptReach⟩
    have hconsistency := hvalid.2 sourceWord acceptState
      (right.state sourceState) acceptStack (right.replacement sourceStack)
      hacceptReach hsourceReach
    have hsourceFinal : right.state sourceState ∈ right.toDPDA.final_states :=
      hconsistency.mp hacceptState
    have hfinal : Endmarked.isFinalIndex right sourceState = true :=
      (Endmarked.isFinalIndex_eq_true_iff right sourceState).mpr hsourceFinal
    have hfinish : rightFinishState left right alphabet sourceState =
        Endmarked.acceptState left right alphabet := by
      simp [rightFinishState, hfinal]
    rw [hfinish] at hcanonical
    have hdrain := endmarked_accept_reaches_empty
      left right alphabet targetStack htargetStack
    exact ⟨Endmarked.acceptState left right alphabet,
      hcanonical.trans hdrain⟩

/-! ## Pair-level result -/

public structure PairNormalizationResult [DecidableEq Action] [Fintype Action]
    (left right : EncodedDPDA Action) where
  leftValid : EncodedDPDA.Valid left
  rightValid : EncodedDPDA.Valid right
  machine : EncodedDPDA (Option Action)
  alphabet : List (Option Action)
  alphabet_nodup : alphabet.Nodup
  leftInitial : DPDAToFirstOrder.Configuration
  rightInitial : DPDAToFirstOrder.Configuration
  leftState_lt : leftInitial.1 < machine.numStates
  rightState_lt : rightInitial.1 < machine.numStates
  leftStack_lt : ∀ Z ∈ leftInitial.2, Z < machine.numStackSymbols
  rightStack_lt : ∀ Z ∈ rightInitial.2, Z < machine.numStackSymbols
  normal : DPDAToFirstOrder.Machine.PoppingComplete machine alphabet
  leftLanguage : DPDAToFirstOrder.emptyStackLanguage machine leftInitial =
    {word | ∃ sourceWord ∈ EncodedDPDA.language left,
      word = sourceWord.map some ++ [none]}
  rightLanguage : DPDAToFirstOrder.emptyStackLanguage machine rightInitial =
    {word | ∃ sourceWord ∈ EncodedDPDA.language right,
      word = sourceWord.map some ++ [none]}

/-!
The executable data projection is kept separate from the proof-bearing result;
this is the object whose primitive recursiveness is required by the eventual
decision procedure.
-/

public structure PairNormalizationData (Action : Type) where
  machine : EncodedDPDA (Option Action)
  alphabet : List (Option Action)
  leftInitial : DPDAToFirstOrder.Configuration
  rightInitial : DPDAToFirstOrder.Configuration

public abbrev PairNormalizationDataCode (Action : Type) :=
  EncodedDPDA (Option Action) × List (Option Action) ×
    DPDAToFirstOrder.Configuration × DPDAToFirstOrder.Configuration

public def pairNormalizationDataEquiv (Action : Type) :
    PairNormalizationData Action ≃ PairNormalizationDataCode Action where
  toFun data :=
    (data.machine, data.alphabet, data.leftInitial, data.rightInitial)
  invFun code :=
    { machine := code.1
      alphabet := code.2.1
      leftInitial := code.2.2.1
      rightInitial := code.2.2.2 }
  left_inv data := by cases data; rfl
  right_inv code := by rcases code with ⟨machine, alphabet, left, right⟩; rfl

public instance pairNormalizationDataPrimcodable
    (Action : Type) [Primcodable Action] :
    Primcodable (PairNormalizationData Action) :=
  Primcodable.ofEquiv (PairNormalizationDataCode Action)
    (pairNormalizationDataEquiv Action)

@[expose] public def pairNormalizationData [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    PairNormalizationData Action :=
  let endmarked := endmarkedPairMachine left right alphabet
  let targetAlphabet := endmarkedAlphabet alphabet
  { machine := poppingCompleteMachine endmarked targetAlphabet
    alphabet := targetAlphabet
    leftInitial := leftEndmarkedConfiguration left right alphabet
    rightInitial := rightEndmarkedConfiguration left right alphabet }

public theorem pairNormalizationData_leftState_lt [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    (pairNormalizationData left right alphabet).leftInitial.1 <
      (pairNormalizationData left right alphabet).machine.numStates := by
  simp [pairNormalizationData, leftEndmarkedConfiguration,
    Endmarked.leftStart]

public theorem pairNormalizationData_rightState_lt [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    (pairNormalizationData left right alphabet).rightInitial.1 <
      (pairNormalizationData left right alphabet).machine.numStates := by
  simp [pairNormalizationData, rightEndmarkedConfiguration,
    Endmarked.rightStart, endmarkedPairMachine_numStates,
    Endmarked.stateCount, Endmarked.rejectState, Endmarked.acceptState,
    Endmarked.rightPendingBase, Endmarked.leftPendingBase]

public theorem pairNormalizationData_leftStack_lt [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    ∀ Z ∈ (pairNormalizationData left right alphabet).leftInitial.2,
      Z < (pairNormalizationData left right alphabet).machine.numStackSymbols := by
  intro Z hZ
  simp [pairNormalizationData, leftEndmarkedConfiguration,
    Endmarked.bottom] at hZ ⊢
  subst Z
  simp [endmarkedPairMachine_numStackSymbols, Endmarked.stackCount]

public theorem pairNormalizationData_rightStack_lt [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action) :
    ∀ Z ∈ (pairNormalizationData left right alphabet).rightInitial.2,
      Z < (pairNormalizationData left right alphabet).machine.numStackSymbols := by
  intro Z hZ
  simp [pairNormalizationData, rightEndmarkedConfiguration,
    Endmarked.bottom] at hZ ⊢
  subst Z
  simp [endmarkedPairMachine_numStackSymbols, Endmarked.stackCount]

public theorem pairNormalizationData_normal [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (haustive : ∀ action, action ∈ alphabet) :
    DPDAToFirstOrder.Machine.PoppingComplete
      (pairNormalizationData left right alphabet).machine
      (pairNormalizationData left right alphabet).alphabet := by
  apply poppingCompleteMachine_normal
  exact mem_endmarkedAlphabet_of_exhaustive haustive

public def pairNormalizationResult
    [Fintype Action] [DecidableEq Action]
    (left right : EncodedDPDA Action) (alphabet : List Action)
    (leftValid : EncodedDPDA.Valid left)
    (rightValid : EncodedDPDA.Valid right)
    (alphabetNodup : alphabet.Nodup)
    (exhaustive : ∀ action, action ∈ alphabet) :
    PairNormalizationResult left right where
  leftValid := leftValid
  rightValid := rightValid
  machine := (pairNormalizationData left right alphabet).machine
  alphabet := (pairNormalizationData left right alphabet).alphabet
  alphabet_nodup := endmarkedAlphabet_nodup alphabetNodup
  leftInitial := (pairNormalizationData left right alphabet).leftInitial
  rightInitial := (pairNormalizationData left right alphabet).rightInitial
  leftState_lt := pairNormalizationData_leftState_lt left right alphabet
  rightState_lt := pairNormalizationData_rightState_lt left right alphabet
  leftStack_lt := pairNormalizationData_leftStack_lt left right alphabet
  rightStack_lt := pairNormalizationData_rightStack_lt left right alphabet
  normal := pairNormalizationData_normal left right alphabet exhaustive
  leftLanguage := by
    change DPDAToFirstOrder.emptyStackLanguage
        (poppingCompleteMachine (endmarkedPairMachine left right alphabet)
          (endmarkedAlphabet alphabet))
        (leftEndmarkedConfiguration left right alphabet) = _
    rw [poppingCompleteMachine_emptyStackLanguage_eq]
    · exact leftEndmarkedLanguage_eq left right alphabet leftValid exhaustive
    · exact mem_endmarkedAlphabet_of_exhaustive exhaustive
    · simp [leftEndmarkedConfiguration, Endmarked.leftStart,
        endmarkedPairMachine_numStates, Endmarked.stateCount,
        Endmarked.rejectState]
    · intro Z hZ
      simp only [leftEndmarkedConfiguration, List.mem_singleton] at hZ
      subst Z
      simp [endmarkedPairMachine_numStackSymbols, Endmarked.bottom,
        Endmarked.stackCount]
  rightLanguage := by
    change DPDAToFirstOrder.emptyStackLanguage
        (poppingCompleteMachine (endmarkedPairMachine left right alphabet)
          (endmarkedAlphabet alphabet))
        (rightEndmarkedConfiguration left right alphabet) = _
    rw [poppingCompleteMachine_emptyStackLanguage_eq]
    · exact rightEndmarkedLanguage_eq left right alphabet rightValid exhaustive
    · exact mem_endmarkedAlphabet_of_exhaustive exhaustive
    · simp [rightEndmarkedConfiguration, Endmarked.rightStart,
        endmarkedPairMachine_numStates, Endmarked.stateCount,
        Endmarked.rejectState, Endmarked.acceptState,
        Endmarked.rightPendingBase, Endmarked.leftPendingBase]
    · intro Z hZ
      simp only [rightEndmarkedConfiguration, List.mem_singleton] at hZ
      subst Z
      simp [endmarkedPairMachine_numStackSymbols, Endmarked.bottom,
        Endmarked.stackCount]


end DPDANormalization

end DCFEquivalence
