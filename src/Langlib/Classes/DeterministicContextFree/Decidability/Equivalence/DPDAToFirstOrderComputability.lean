module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAToFirstOrder
public import Langlib.Utilities.PrimrecHelpers

@[expose]
public section

/-!
# Effectivity of the DPDA-to-first-order translation

The semantic translation is defined directly through the decoded finite DPDA.
For computability it is convenient to erase the dependent `Fin` wrappers and
evaluate the same table lookups on normalized natural indices.  This file
proves that those raw evaluators agree with the semantic definitions and then
records total computability of the translated grammar and configuration terms.
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDAToFirstOrder

variable {Action : Type} [Primcodable Action] [DecidableEq Action]

private theorem primrec_list_find?
    {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  have hguard : Primrec₂ (fun a b =>
      bif p a b then some b else none) := by
    show Primrec (fun q : A × B =>
      bif p q.1 q.2 then some q.2 else none)
    exact Primrec.cond
      (hp.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)
  have hhead := Primrec.list_head?.comp
    (Primrec.listFilterMap hf hguard)
  apply Primrec.of_eq hhead
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih =>
      cases h : p a b <;> simp [h, ih]

omit [DecidableEq Action] in
private theorem numStates_primrec :
    Primrec (EncodedDPDA.numStates : EncodedDPDA Action → ℕ) := by
  unfold EncodedDPDA.numStates EncodedDPDA
  exact Primrec.succ.comp Primrec.fst

omit [DecidableEq Action] in
private theorem numStackSymbols_primrec :
    Primrec (EncodedDPDA.numStackSymbols : EncodedDPDA Action → ℕ) := by
  unfold EncodedDPDA.numStackSymbols EncodedDPDA
  exact Primrec.succ.comp (Primrec.fst.comp Primrec.snd)

omit [DecidableEq Action] in
private theorem inputRows_primrec :
    Primrec (EncodedDPDA.inputRows :
      EncodedDPDA Action → List (InputRow Action)) := by
  unfold EncodedDPDA.inputRows EncodedDPDA
  exact Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))

omit [DecidableEq Action] in
private theorem epsilonRows_primrec :
    Primrec (EncodedDPDA.epsilonRows :
      EncodedDPDA Action → List EpsilonRow) := by
  unfold EncodedDPDA.epsilonRows EncodedDPDA
  exact Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))

private abbrev HeadInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × ℕ)

private def epsilonMatches (input : HeadInput Action)
    (row : EpsilonRow) : Bool :=
  decide (row.1 % input.1.numStates = input.2.1 % input.1.numStates ∧
    row.2.1 % input.1.numStackSymbols =
      input.2.2 % input.1.numStackSymbols)

omit [DecidableEq Action] in
private theorem epsilonMatches_primrec :
    Primrec₂ (epsilonMatches (Action := Action)) := by
  show Primrec (fun q : HeadInput Action × EpsilonRow =>
    epsilonMatches q.1 q.2)
  have hstates : Primrec (fun q : HeadInput Action × EpsilonRow =>
      q.1.1.numStates) :=
    numStates_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hstack : Primrec (fun q : HeadInput Action × EpsilonRow =>
      q.1.1.numStackSymbols) :=
    numStackSymbols_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hrowState := Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd) hstates
  have hqueryState := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hstates
  have hrowStack := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hstack
  have hqueryStack := Primrec.nat_mod.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hstack
  apply Primrec.of_eq (Primrec.and.comp
    ((PrimrecRel.decide Primrec.eq).comp hrowState hqueryState)
    ((PrimrecRel.decide Primrec.eq).comp hrowStack hqueryStack))
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [epsilonMatches]

private def rawEpsilonStep? (input : HeadInput Action) :
    Option (ℕ × List ℕ) :=
  (input.1.epsilonRows.find? (epsilonMatches input)).map fun row =>
    (row.2.2.1 % input.1.numStates,
      row.2.2.2.map fun symbol => symbol % input.1.numStackSymbols)

omit [DecidableEq Action] in
private theorem rawEpsilonStep?_primrec :
    Primrec (rawEpsilonStep? (Action := Action)) := by
  have hfind : Primrec (fun input : HeadInput Action =>
      input.1.epsilonRows.find? (epsilonMatches input)) :=
    primrec_list_find?
      (epsilonRows_primrec.comp Primrec.fst)
      epsilonMatches_primrec
  have hresult : Primrec₂ (fun (input : HeadInput Action)
      (row : EpsilonRow) =>
      (row.2.2.1 % input.1.numStates,
        row.2.2.2.map fun symbol =>
          symbol % input.1.numStackSymbols)) := by
    show Primrec (fun q : HeadInput Action × EpsilonRow =>
      (q.2.2.2.1 % q.1.1.numStates,
        q.2.2.2.2.map fun symbol =>
          symbol % q.1.1.numStackSymbols))
    have hstates : Primrec (fun q : HeadInput Action × EpsilonRow =>
        q.1.1.numStates) := numStates_primrec.comp
      (Primrec.fst.comp Primrec.fst)
    have hrow : Primrec (fun q : HeadInput Action × EpsilonRow => q.2) :=
      Primrec.snd
    have hrowTail : Primrec (fun q : HeadInput Action × EpsilonRow =>
        q.2.2) := Primrec.snd.comp hrow
    have hrowOutput : Primrec (fun q : HeadInput Action × EpsilonRow =>
        q.2.2.2) := Primrec.snd.comp hrowTail
    have hrawTarget : Primrec (fun q : HeadInput Action × EpsilonRow =>
        q.2.2.2.1) :=
      Primrec.fst.comp hrowOutput
    have htarget : Primrec (fun q : HeadInput Action × EpsilonRow =>
        q.2.2.2.1 % q.1.1.numStates) :=
      Primrec.nat_mod.comp hrawTarget hstates
    have hrawReplacement : Primrec (fun q :
        HeadInput Action × EpsilonRow => q.2.2.2.2) :=
      Primrec.snd.comp hrowOutput
    have hmod : Primrec₂ (fun (q : HeadInput Action × EpsilonRow)
        (symbol : ℕ) => symbol % q.1.1.numStackSymbols) := by
      show Primrec (fun p : (HeadInput Action × EpsilonRow) × ℕ =>
        p.2 % p.1.1.1.numStackSymbols)
      exact Primrec.nat_mod.comp Primrec.snd
        (numStackSymbols_primrec.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hreplacement : Primrec (fun q : HeadInput Action × EpsilonRow =>
        q.2.2.2.2.map fun symbol =>
          symbol % q.1.1.numStackSymbols) :=
      Primrec.list_map hrawReplacement hmod
    exact Primrec.pair htarget hreplacement
  exact Primrec.option_map hfind hresult

omit [Primcodable Action] in
private theorem rawEpsilonStep?_eq
    (machine : EncodedDPDA Action) (q Z : ℕ) :
    rawEpsilonStep? (machine, q, Z) =
      Machine.epsilonStep? machine q Z := by
  unfold rawEpsilonStep? epsilonMatches Machine.epsilonStep?
  unfold EncodedDPDA.epsilonLookup EncodedDPDA.state
    EncodedDPDA.stackSymbol EncodedDPDA.replacement
  simp [EncodedDPDA.stackSymbol, List.map_map, Function.comp_def]

/-- The decoded normalized epsilon-transition evaluator is primitive recursive
on raw machine, state, and stack-symbol codes. -/
public theorem epsilonStep?_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      Machine.epsilonStep? input.1 input.2.1 input.2.2) := by
  apply rawEpsilonStep?_primrec.of_eq
  intro input
  exact rawEpsilonStep?_eq input.1 input.2.1 input.2.2

/-- A small primitive-recursive evaluator witnessing the normalized epsilon
query, packaged opaquely so clients need not elaborate the decoded lookup. -/
public theorem epsilonStepEvaluator_exists :
    ∃ evaluator :
        (EncodedDPDA Action × (ℕ × ℕ)) → Option (ℕ × List ℕ),
      Primrec evaluator ∧
        ∀ input, evaluator input =
          Machine.epsilonStep? input.1 input.2.1 input.2.2 :=
  ⟨rawEpsilonStep?, rawEpsilonStep?_primrec,
    fun input => rawEpsilonStep?_eq input.1 input.2.1 input.2.2⟩

/-- The decoded normalized epsilon-transition evaluator is total computable
on raw machine, state, and stack-symbol codes. -/
public theorem epsilonStep?_computable :
    Computable (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      Machine.epsilonStep? input.1 input.2.1 input.2.2) :=
  epsilonStep?_primrec.to_comp

private abbrev InputHeadInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × Action × ℕ)

private def inputMatches (input : InputHeadInput Action)
    (row : InputRow Action) : Bool :=
  decide (row.1 % input.1.numStates = input.2.1 % input.1.numStates ∧
    row.2.1 = input.2.2.1 ∧
    row.2.2.1 % input.1.numStackSymbols =
      input.2.2.2 % input.1.numStackSymbols)

private theorem inputMatches_primrec :
    Primrec₂ (inputMatches (Action := Action)) := by
  show Primrec (fun q : InputHeadInput Action × InputRow Action =>
    inputMatches q.1 q.2)
  have hstates : Primrec (fun q :
      InputHeadInput Action × InputRow Action => q.1.1.numStates) :=
    numStates_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hstack : Primrec (fun q :
      InputHeadInput Action × InputRow Action =>
        q.1.1.numStackSymbols) :=
    numStackSymbols_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hrowState := Primrec.nat_mod.comp
    (Primrec.fst.comp Primrec.snd) hstates
  have hqueryState := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hstates
  have hrowAction : Primrec (fun q :
      InputHeadInput Action × InputRow Action => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hqueryAction : Primrec (fun q :
      InputHeadInput Action × InputRow Action => q.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))
  have hrowStack := Primrec.nat_mod.comp
    (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))) hstack
  have hqueryStack := Primrec.nat_mod.comp
    (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))) hstack
  apply Primrec.of_eq (Primrec.and.comp
    ((PrimrecRel.decide Primrec.eq).comp hrowState hqueryState)
    (Primrec.and.comp
      ((PrimrecRel.decide Primrec.eq).comp hrowAction hqueryAction)
      ((PrimrecRel.decide Primrec.eq).comp hrowStack hqueryStack)))
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [inputMatches]

private def rawInputStep? (input : InputHeadInput Action) :
    Option (ℕ × List ℕ) :=
  (input.1.inputRows.find? (inputMatches input)).map fun row =>
    (row.2.2.2.1 % input.1.numStates,
      row.2.2.2.2.map fun symbol => symbol % input.1.numStackSymbols)

private theorem rawInputStep?_primrec :
    Primrec (rawInputStep? (Action := Action)) := by
  have hfind : Primrec (fun input : InputHeadInput Action =>
      input.1.inputRows.find? (inputMatches input)) :=
    primrec_list_find?
      (inputRows_primrec.comp Primrec.fst)
      inputMatches_primrec
  have hresult : Primrec₂ (fun (input : InputHeadInput Action)
      (row : InputRow Action) =>
      (row.2.2.2.1 % input.1.numStates,
        row.2.2.2.2.map fun symbol =>
          symbol % input.1.numStackSymbols)) := by
    show Primrec (fun q : InputHeadInput Action × InputRow Action =>
      (q.2.2.2.2.1 % q.1.1.numStates,
        q.2.2.2.2.2.map fun symbol =>
          symbol % q.1.1.numStackSymbols))
    have hstates : Primrec (fun q :
        InputHeadInput Action × InputRow Action =>
        q.1.1.numStates) := numStates_primrec.comp
      (Primrec.fst.comp Primrec.fst)
    have hrow : Primrec (fun q :
        InputHeadInput Action × InputRow Action => q.2) := Primrec.snd
    have hrowTail : Primrec (fun q :
        InputHeadInput Action × InputRow Action => q.2.2) :=
      Primrec.snd.comp hrow
    have hrowStackTail : Primrec (fun q :
        InputHeadInput Action × InputRow Action => q.2.2.2) :=
      Primrec.snd.comp hrowTail
    have hrowOutput : Primrec (fun q :
        InputHeadInput Action × InputRow Action => q.2.2.2.2) :=
      Primrec.snd.comp hrowStackTail
    have hrawTarget : Primrec (fun q :
        InputHeadInput Action × InputRow Action => q.2.2.2.2.1) :=
      Primrec.fst.comp hrowOutput
    have htarget : Primrec (fun q :
        InputHeadInput Action × InputRow Action =>
        q.2.2.2.2.1 % q.1.1.numStates) :=
      Primrec.nat_mod.comp hrawTarget hstates
    have hrawReplacement : Primrec (fun q :
        InputHeadInput Action × InputRow Action => q.2.2.2.2.2) :=
      Primrec.snd.comp hrowOutput
    have hmod : Primrec₂ (fun
        (q : InputHeadInput Action × InputRow Action) (symbol : ℕ) =>
        symbol % q.1.1.numStackSymbols) := by
      show Primrec (fun p :
          (InputHeadInput Action × InputRow Action) × ℕ =>
        p.2 % p.1.1.1.numStackSymbols)
      exact Primrec.nat_mod.comp Primrec.snd
        (numStackSymbols_primrec.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hreplacement : Primrec (fun q :
        InputHeadInput Action × InputRow Action =>
        q.2.2.2.2.2.map fun symbol =>
          symbol % q.1.1.numStackSymbols) :=
      Primrec.list_map hrawReplacement hmod
    exact Primrec.pair htarget hreplacement
  exact Primrec.option_map hfind hresult

omit [Primcodable Action] in
private theorem rawInputStep?_eq
    (machine : EncodedDPDA Action) (q : ℕ) (action : Action) (Z : ℕ) :
    rawInputStep? (machine, q, action, Z) =
      Machine.inputStep? machine q action Z := by
  unfold rawInputStep? inputMatches Machine.inputStep?
  unfold EncodedDPDA.inputLookup EncodedDPDA.state
    EncodedDPDA.stackSymbol EncodedDPDA.replacement
  simp [EncodedDPDA.stackSymbol, List.map_map, Function.comp_def]

/-- The decoded normalized input-transition evaluator is primitive recursive
on raw machine, state, action, and stack-symbol codes. -/
public theorem inputStep?_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × Action × ℕ) =>
      Machine.inputStep? input.1 input.2.1 input.2.2.1 input.2.2.2) := by
  apply rawInputStep?_primrec.of_eq
  intro input
  exact rawInputStep?_eq input.1 input.2.1 input.2.2.1 input.2.2.2

/-- A small primitive-recursive evaluator witnessing the normalized input
query, packaged opaquely so clients need not elaborate the decoded lookup. -/
public theorem inputStepEvaluator_exists :
    ∃ evaluator :
        (EncodedDPDA Action × (ℕ × Action × ℕ)) → Option (ℕ × List ℕ),
      Primrec evaluator ∧
        ∀ input, evaluator input =
          Machine.inputStep? input.1 input.2.1 input.2.2.1 input.2.2.2 :=
  ⟨rawInputStep?, rawInputStep?_primrec,
    fun input => rawInputStep?_eq input.1 input.2.1
      input.2.2.1 input.2.2.2⟩

/-- The decoded normalized input-transition evaluator is total computable on
raw machine, state, action, and stack-symbol codes. -/
public theorem inputStep?_computable :
    Computable (fun input : EncodedDPDA Action × (ℕ × Action × ℕ) =>
      Machine.inputStep? input.1 input.2.1 input.2.2.1 input.2.2.2) :=
  inputStep?_primrec.to_comp

private def rawEpsilonEnabled (input : InputHeadInput Action) : Bool :=
  (input.1.epsilonRows.find? (epsilonMatches
    (input.1, input.2.1, input.2.2.2))).isSome

private theorem rawEpsilonEnabled_primrec :
    Primrec (rawEpsilonEnabled (Action := Action)) := by
  have hheadContext : Primrec (fun input : InputHeadInput Action =>
      (input.1, input.2.1, input.2.2.2)) :=
    Primrec.pair Primrec.fst
      (Primrec.pair
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hmatches : Primrec₂ (fun (input : InputHeadInput Action)
      (row : EpsilonRow) => epsilonMatches
        (input.1, input.2.1, input.2.2.2) row) := by
    show Primrec (fun q : InputHeadInput Action × EpsilonRow =>
      epsilonMatches (q.1.1, q.1.2.1, q.1.2.2.2) q.2)
    exact epsilonMatches_primrec.comp
      (hheadContext.comp Primrec.fst) Primrec.snd
  have hfind : Primrec (fun input : InputHeadInput Action =>
      input.1.epsilonRows.find? (epsilonMatches
        (input.1, input.2.1, input.2.2.2))) :=
    primrec_list_find?
      (epsilonRows_primrec.comp Primrec.fst)
      hmatches
  exact Primrec.option_isSome.comp hfind

private theorem rawDeterministicInputStep_primrec :
    Primrec (fun input : InputHeadInput Action =>
      bif rawEpsilonEnabled input then
        (none : Option (ℕ × List ℕ))
      else rawInputStep? input) :=
  Primrec.cond rawEpsilonEnabled_primrec
    (Primrec.const none) rawInputStep?_primrec

/-- The deterministic input evaluator, including epsilon priority, is
primitive recursive on raw machine, state, action, and stack-symbol codes. -/
public theorem deterministicInputStep?_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × Action × ℕ) =>
      if (Machine.epsilonStep? input.1 input.2.1 input.2.2.2).isSome then
        (none : Option (ℕ × List ℕ))
      else Machine.inputStep? input.1 input.2.1
        input.2.2.1 input.2.2.2) := by
  apply rawDeterministicInputStep_primrec.of_eq
  intro input
  rw [rawInputStep?_eq]
  have henabled : rawEpsilonEnabled input =
      (Machine.epsilonStep? input.1 input.2.1 input.2.2.2).isSome := by
    have hraw := congrArg Option.isSome
      (rawEpsilonStep?_eq input.1 input.2.1 input.2.2.2)
    unfold rawEpsilonStep? at hraw
    unfold rawEpsilonEnabled
    simpa using hraw
  rw [henabled]
  cases (Machine.epsilonStep?
    input.1 input.2.1 input.2.2.2).isSome <;> rfl

/-- An opaque primitive-recursive witness for the deterministic input query,
including epsilon priority. -/
public theorem deterministicInputStepEvaluator_exists :
    ∃ evaluator :
        (EncodedDPDA Action × (ℕ × Action × ℕ)) → Option (ℕ × List ℕ),
      Primrec evaluator ∧
        ∀ input, evaluator input =
          if (Machine.epsilonStep? input.1 input.2.1 input.2.2.2).isSome then
            none
          else Machine.inputStep? input.1 input.2.1
            input.2.2.1 input.2.2.2 := by
  refine ⟨(fun input => bif rawEpsilonEnabled input then
      (none : Option (ℕ × List ℕ)) else rawInputStep? input),
    rawDeterministicInputStep_primrec, ?_⟩
  intro input
  change (bif rawEpsilonEnabled input then
      (none : Option (ℕ × List ℕ)) else rawInputStep? input) = _
  rw [rawInputStep?_eq]
  have henabled : rawEpsilonEnabled input =
      (Machine.epsilonStep? input.1 input.2.1 input.2.2.2).isSome := by
    have hraw := congrArg Option.isSome
      (rawEpsilonStep?_eq input.1 input.2.1 input.2.2.2)
    unfold rawEpsilonStep? at hraw
    unfold rawEpsilonEnabled
    simpa using hraw
  rw [henabled]
  cases (Machine.epsilonStep?
    input.1 input.2.1 input.2.2.2).isSome <;> rfl

/-- The deterministic input evaluator, including epsilon priority, is total
computable on raw machine, state, action, and stack-symbol codes. -/
public theorem deterministicInputStep?_computable :
    Computable (fun input : EncodedDPDA Action × (ℕ × Action × ℕ) =>
      if (Machine.epsilonStep? input.1 input.2.1 input.2.2.2).isSome then
        (none : Option (ℕ × List ℕ))
      else Machine.inputStep? input.1 input.2.1
        input.2.2.1 input.2.2.2) := by
  exact deterministicInputStep?_primrec.to_comp

/-! ## Configuration-term evaluator -/

private abbrev LayerCode := List RawNode × List ℕ

private def layerCode (layer : TermLayer) : LayerCode :=
  (layer.nodes, layer.roots)

private abbrev ExtendInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × LayerCode)

private abbrev ExtendPointInput (Action : Type) :=
  ExtendInput Action × ℕ

private def rawExtendNode (input : ExtendPointInput Action) : RawNode :=
  let machine := input.1.1
  let Z := input.1.2.1
  let roots := input.1.2.2.2
  let q := input.2
  bif (rawEpsilonStep? (machine, q, Z)).isSome then
    .inl 0
  else
    .inr (headSymbol machine q Z, roots)

omit [DecidableEq Action] in
private theorem rawExtendNode_primrec :
    Primrec (rawExtendNode (Action := Action)) := by
  have hmachine : Primrec (fun input : ExtendPointInput Action =>
      input.1.1) := Primrec.fst.comp Primrec.fst
  have hZ : Primrec (fun input : ExtendPointInput Action =>
      input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hroots : Primrec (fun input : ExtendPointInput Action =>
      input.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))
  have hq : Primrec (fun input : ExtendPointInput Action => input.2) :=
    Primrec.snd
  have hepsilonInput : Primrec (fun input : ExtendPointInput Action =>
      ((input.1.1, input.2, input.1.2.1) : HeadInput Action)) :=
    Primrec.pair hmachine (Primrec.pair hq hZ)
  have hepsilon : Primrec (fun input : ExtendPointInput Action =>
      rawEpsilonStep? (input.1.1, input.2, input.1.2.1)) :=
    rawEpsilonStep?_primrec.comp hepsilonInput
  have hsome : Primrec (fun input : ExtendPointInput Action =>
      (rawEpsilonStep? (input.1.1, input.2, input.1.2.1)).isSome) :=
    Primrec.option_isSome.comp hepsilon
  have hhead : Primrec (fun input : ExtendPointInput Action =>
      headSymbol input.1.1 input.2 input.1.2.1) := by
    unfold headSymbol
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp hq
        (numStackSymbols_primrec.comp hmachine)) hZ
  have hvariable : Primrec (fun _ : ExtendPointInput Action =>
      (.inl 0 : RawNode)) :=
    Primrec.sumInl.comp (Primrec.const 0)
  have happlication : Primrec (fun input : ExtendPointInput Action =>
      (.inr (headSymbol input.1.1 input.2 input.1.2.1,
        input.1.2.2.2) : RawNode)) :=
    Primrec.sumInr.comp (Primrec.pair hhead hroots)
  exact Primrec.cond hsome hvariable happlication

private def rawExtendRoot (input : ExtendPointInput Action) : ℕ :=
  let machine := input.1.1
  let Z := input.1.2.1
  let nodes := input.1.2.2.1
  let roots := input.1.2.2.2
  let q := input.2
  let result := rawEpsilonStep? (machine, q, Z)
  bif result.isSome then
    roots.getD (result.getD (0, [])).1 0
  else
    nodes.length + q

omit [DecidableEq Action] in
private theorem rawExtendRoot_primrec :
    Primrec (rawExtendRoot (Action := Action)) := by
  have hmachine : Primrec (fun input : ExtendPointInput Action =>
      input.1.1) := Primrec.fst.comp Primrec.fst
  have hZ : Primrec (fun input : ExtendPointInput Action =>
      input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hnodes : Primrec (fun input : ExtendPointInput Action =>
      input.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))
  have hroots : Primrec (fun input : ExtendPointInput Action =>
      input.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))
  have hq : Primrec (fun input : ExtendPointInput Action => input.2) :=
    Primrec.snd
  have hepsilonInput : Primrec (fun input : ExtendPointInput Action =>
      ((input.1.1, input.2, input.1.2.1) : HeadInput Action)) :=
    Primrec.pair hmachine (Primrec.pair hq hZ)
  have hepsilon : Primrec (fun input : ExtendPointInput Action =>
      rawEpsilonStep? (input.1.1, input.2, input.1.2.1)) :=
    rawEpsilonStep?_primrec.comp hepsilonInput
  have hsome : Primrec (fun input : ExtendPointInput Action =>
      (rawEpsilonStep? (input.1.1, input.2, input.1.2.1)).isSome) :=
    Primrec.option_isSome.comp hepsilon
  have hresult : Primrec (fun input : ExtendPointInput Action =>
      (rawEpsilonStep? (input.1.1, input.2,
        input.1.2.1)).getD (0, [])) :=
    Primrec.option_getD.comp hepsilon (Primrec.const (0, []))
  have htarget : Primrec (fun input : ExtendPointInput Action =>
      (rawEpsilonStep? (input.1.1, input.2,
        input.1.2.1)).getD (0, []) |>.1) :=
    Primrec.fst.comp hresult
  have hselected : Primrec (fun input : ExtendPointInput Action =>
      input.1.2.2.2.getD
        ((rawEpsilonStep? (input.1.1, input.2,
          input.1.2.1)).getD (0, [])).1 0) :=
    Primrec.list_getD 0 |>.comp hroots htarget
  have hfresh : Primrec (fun input : ExtendPointInput Action =>
      input.1.2.2.1.length + input.2) :=
    Primrec.nat_add.comp (Primrec.list_length.comp hnodes) hq
  exact Primrec.cond hsome hselected hfresh

private def rawExtendLayer (input : ExtendInput Action) : LayerCode :=
  let machine := input.1
  let nodes := input.2.2.1
  let newNodes := (List.range machine.numStates).map fun q =>
    rawExtendNode (input, q)
  let newRoots := (List.range machine.numStates).map fun q =>
    rawExtendRoot (input, q)
  (nodes ++ newNodes, newRoots)

omit [DecidableEq Action] in
private theorem rawExtendLayer_primrec :
    Primrec (rawExtendLayer (Action := Action)) := by
  have hmachine : Primrec (fun input : ExtendInput Action => input.1) :=
    Primrec.fst
  have hnodes : Primrec (fun input : ExtendInput Action =>
      input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrange : Primrec (fun input : ExtendInput Action =>
      List.range input.1.numStates) :=
    Primrec.list_range.comp (numStates_primrec.comp hmachine)
  have hnewNodes : Primrec (fun input : ExtendInput Action =>
      (List.range input.1.numStates).map fun q =>
        rawExtendNode (input, q)) :=
    Primrec.list_map hrange rawExtendNode_primrec.to₂
  have hnewRoots : Primrec (fun input : ExtendInput Action =>
      (List.range input.1.numStates).map fun q =>
        rawExtendRoot (input, q)) :=
    Primrec.list_map hrange rawExtendRoot_primrec.to₂
  exact Primrec.pair
    (Primrec.list_append.comp hnodes hnewNodes) hnewRoots

omit [Primcodable Action] in
private theorem rawExtendLayer_eq
    (machine : EncodedDPDA Action) (Z : ℕ) (layer : TermLayer) :
    rawExtendLayer (machine, Z, layerCode layer) =
      layerCode (extendLayer machine Z layer) := by
  change
    (layer.nodes ++
        (List.range machine.numStates).map (fun q =>
          rawExtendNode ((machine, Z, (layer.nodes, layer.roots)), q)),
      (List.range machine.numStates).map (fun q =>
        rawExtendRoot ((machine, Z, (layer.nodes, layer.roots)), q))) =
    (layer.nodes ++
        (List.range machine.numStates).map (fun q =>
          match Machine.epsilonStep? machine q Z with
          | some _ => (.inl 0 : RawNode)
          | none => .inr (headSymbol machine q Z, layer.roots)),
      (List.range machine.numStates).map (fun q =>
        match Machine.epsilonStep? machine q Z with
        | some (target, _) => layer.roots[target]?.getD 0
        | none => layer.nodes.length + q))
  apply Prod.ext
  · change layer.nodes ++
        (List.range machine.numStates).map (fun q =>
          rawExtendNode ((machine, Z, (layer.nodes, layer.roots)), q)) =
      layer.nodes ++
        (List.range machine.numStates).map (fun q =>
          match Machine.epsilonStep? machine q Z with
          | some _ => (.inl 0 : RawNode)
          | none => .inr (headSymbol machine q Z, layer.roots))
    congr 1
    apply List.map_congr_left
    intro q hq
    dsimp [rawExtendNode]
    rw [rawEpsilonStep?_eq]
    cases Machine.epsilonStep? machine q Z <;> rfl
  · change (List.range machine.numStates).map (fun q =>
        rawExtendRoot ((machine, Z, (layer.nodes, layer.roots)), q)) =
      (List.range machine.numStates).map (fun q =>
        match Machine.epsilonStep? machine q Z with
        | some (target, _) => layer.roots[target]?.getD 0
        | none => layer.nodes.length + q)
    apply List.map_congr_left
    intro q hq
    dsimp [rawExtendRoot]
    rw [rawEpsilonStep?_eq]
    cases Machine.epsilonStep? machine q Z <;> rfl

private def rawGroundBaseLayer
    (machine : EncodedDPDA Action) : LayerCode :=
  ([.inr (bottomSymbol machine, [])],
    (List.range machine.numStates).map fun _ => 0)

omit [DecidableEq Action] in
private theorem rawGroundBaseLayer_primrec :
    Primrec (rawGroundBaseLayer (Action := Action)) := by
  have hbottom : Primrec (fun machine : EncodedDPDA Action =>
      bottomSymbol machine) := by
    unfold bottomSymbol
    exact Primrec.nat_mul.comp numStates_primrec
      numStackSymbols_primrec
  have hnode : Primrec (fun machine : EncodedDPDA Action =>
      (.inr (bottomSymbol machine, []) : RawNode)) :=
    Primrec.sumInr.comp
      (Primrec.pair hbottom (Primrec.const []))
  have hnodes : Primrec (fun machine : EncodedDPDA Action =>
      [(.inr (bottomSymbol machine, []) : RawNode)]) :=
    Primrec.list_cons.comp hnode (Primrec.const [])
  have hrange : Primrec (fun machine : EncodedDPDA Action =>
      List.range machine.numStates) :=
    Primrec.list_range.comp numStates_primrec
  have hroots : Primrec (fun machine : EncodedDPDA Action =>
      (List.range machine.numStates).map fun _ => 0) :=
    Primrec.list_map hrange (Primrec.const 0).to₂
  exact Primrec.pair hnodes hroots

omit [Primcodable Action] [DecidableEq Action] in
private theorem rawGroundBaseLayer_eq (machine : EncodedDPDA Action) :
    rawGroundBaseLayer machine = layerCode (groundBaseLayer machine) := by
  simp [rawGroundBaseLayer, layerCode, groundBaseLayer]

private abbrev LayerRunInput (Action : Type) :=
  EncodedDPDA Action × List ℕ

private def rawConfigurationLayer
    (input : LayerRunInput Action) : LayerCode :=
  input.2.reverse.foldl
    (fun layer Z => rawExtendLayer (input.1, Z, layer))
    (rawGroundBaseLayer input.1)

omit [DecidableEq Action] in
private theorem rawConfigurationLayer_primrec :
    Primrec (rawConfigurationLayer (Action := Action)) := by
  have hmachine : Primrec (fun input : LayerRunInput Action => input.1) :=
    Primrec.fst
  have hstack : Primrec (fun input : LayerRunInput Action =>
      input.2.reverse) :=
    Primrec.list_reverse.comp Primrec.snd
  have hbase : Primrec (fun input : LayerRunInput Action =>
      rawGroundBaseLayer input.1) :=
    rawGroundBaseLayer_primrec.comp hmachine
  have hstep : Primrec₂ (fun (input : LayerRunInput Action)
      (point : LayerCode × ℕ) =>
      rawExtendLayer (input.1, point.2, point.1)) := by
    show Primrec (fun q : LayerRunInput Action × (LayerCode × ℕ) =>
      rawExtendLayer (q.1.1, q.2.2, q.2.1))
    have hextendInput : Primrec (fun q :
        LayerRunInput Action × (LayerCode × ℕ) =>
        ((q.1.1, q.2.2, q.2.1) : ExtendInput Action)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.snd)
          (Primrec.fst.comp Primrec.snd))
    exact rawExtendLayer_primrec.comp hextendInput
  have hfold := Primrec.list_foldl
    (α := LayerRunInput Action) (β := ℕ) (σ := LayerCode)
    (f := fun input => input.2.reverse)
    (g := fun input => rawGroundBaseLayer input.1)
    (h := fun input point =>
      rawExtendLayer (input.1, point.2, point.1))
    hstack hbase hstep
  exact hfold

omit [Primcodable Action] in
private theorem rawLayerFold_eq
    (machine : EncodedDPDA Action) (work : List ℕ)
    (rawLayer : LayerCode) (layer : TermLayer)
    (hlayer : rawLayer = layerCode layer) :
    work.foldl (fun current Z =>
        rawExtendLayer (machine, Z, current)) rawLayer =
      layerCode (work.foldl (fun current Z =>
        extendLayer machine Z current) layer) := by
  induction work generalizing rawLayer layer with
  | nil => simpa using hlayer
  | cons Z work ih =>
      simp only [List.foldl_cons]
      calc
        work.foldl (fun current Z =>
            rawExtendLayer (machine, Z, current))
            (rawExtendLayer (machine, Z, rawLayer)) =
          work.foldl (fun current Z =>
            rawExtendLayer (machine, Z, current))
            (rawExtendLayer (machine, Z, layerCode layer)) := by rw [hlayer]
        _ = work.foldl (fun current Z =>
            rawExtendLayer (machine, Z, current))
            (layerCode (extendLayer machine Z layer)) := by
          rw [rawExtendLayer_eq]
        _ = layerCode (work.foldl (fun current Z =>
            extendLayer machine Z current)
            (extendLayer machine Z layer)) :=
          ih _ _ rfl

omit [Primcodable Action] in
private theorem rawConfigurationLayer_eq
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    rawConfigurationLayer (machine, stack) =
      layerCode (configurationLayer machine stack) := by
  unfold rawConfigurationLayer configurationLayer
  exact rawLayerFold_eq machine stack.reverse _ _
    (rawGroundBaseLayer_eq machine)

private def rawConfigurationTerm
    (input : EncodedDPDA Action × Configuration) : RegularTerm :=
  let layer := rawConfigurationLayer (input.1, input.2.2)
  (layer.1, layer.2.getD input.2.1 0)

omit [DecidableEq Action] in
private theorem rawConfigurationTerm_primrec :
    Primrec (rawConfigurationTerm (Action := Action)) := by
  have hlayerInput : Primrec (fun input :
      EncodedDPDA Action × Configuration =>
      ((input.1, input.2.2) : LayerRunInput Action)) :=
    Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hlayer : Primrec (fun input :
      EncodedDPDA Action × Configuration =>
      rawConfigurationLayer (input.1, input.2.2)) :=
    rawConfigurationLayer_primrec.comp hlayerInput
  have hstate : Primrec (fun input :
      EncodedDPDA Action × Configuration => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hroot : Primrec (fun input :
      EncodedDPDA Action × Configuration =>
      (rawConfigurationLayer (input.1, input.2.2)).2.getD
        input.2.1 0) :=
    Primrec.list_getD 0 |>.comp (Primrec.snd.comp hlayer) hstate
  exact Primrec.pair (Primrec.fst.comp hlayer) hroot

omit [Primcodable Action] in
private theorem rawConfigurationTerm_eq
    (machine : EncodedDPDA Action) (configuration : Configuration) :
    rawConfigurationTerm (machine, configuration) =
      configurationTerm machine configuration.1 configuration.2 := by
  unfold rawConfigurationTerm configurationTerm
  rw [rawConfigurationLayer_eq]
  rfl

/-- The ground regular term representing a normalized DPDA configuration is a
total computable function of the raw machine code and configuration. -/
public theorem configurationTerm_computable :
    Computable (fun input : EncodedDPDA Action × Configuration =>
      configurationTerm input.1 input.2.1 input.2.2) := by
  apply rawConfigurationTerm_primrec.to_comp.of_eq
  intro input
  exact rawConfigurationTerm_eq input.1 input.2

/-- Curried form of `configurationTerm_computable`. -/
public theorem configurationTerm_computable₂ :
    Computable₂ (fun (machine : EncodedDPDA Action)
      (configuration : Configuration) =>
      configurationTerm machine configuration.1 configuration.2) :=
  Computable₂.mk configurationTerm_computable

/-! ## Grammar evaluator -/

private def rawBaseLayer (machine : EncodedDPDA Action) : LayerCode :=
  ((List.range machine.numStates).map fun q => (.inl q : RawNode),
    List.range machine.numStates)

omit [DecidableEq Action] in
private theorem rawBaseLayer_primrec :
    Primrec (rawBaseLayer (Action := Action)) := by
  have hrange : Primrec (fun machine : EncodedDPDA Action =>
      List.range machine.numStates) :=
    Primrec.list_range.comp numStates_primrec
  have hnodes : Primrec (fun machine : EncodedDPDA Action =>
      (List.range machine.numStates).map fun q => (.inl q : RawNode)) := by
    have hnode : Primrec₂ (fun (_ : EncodedDPDA Action) (q : ℕ) =>
        (.inl q : RawNode)) := by
      show Primrec (fun p : EncodedDPDA Action × ℕ =>
        (.inl p.2 : RawNode))
      exact Primrec.sumInl.comp Primrec.snd
    exact Primrec.list_map hrange hnode
  exact Primrec.pair hnodes hrange

omit [Primcodable Action] [DecidableEq Action] in
private theorem rawBaseLayer_eq (machine : EncodedDPDA Action) :
    rawBaseLayer machine = layerCode (baseLayer machine) := rfl

private def rawStackLayer (input : LayerRunInput Action) : LayerCode :=
  input.2.reverse.foldl
    (fun layer Z => rawExtendLayer (input.1, Z, layer))
    (rawBaseLayer input.1)

omit [DecidableEq Action] in
private theorem rawStackLayer_primrec :
    Primrec (rawStackLayer (Action := Action)) := by
  have hstack : Primrec (fun input : LayerRunInput Action =>
      input.2.reverse) :=
    Primrec.list_reverse.comp Primrec.snd
  have hbase : Primrec (fun input : LayerRunInput Action =>
      rawBaseLayer input.1) :=
    rawBaseLayer_primrec.comp Primrec.fst
  have hstep : Primrec₂ (fun (input : LayerRunInput Action)
      (point : LayerCode × ℕ) =>
      rawExtendLayer (input.1, point.2, point.1)) := by
    show Primrec (fun q : LayerRunInput Action × (LayerCode × ℕ) =>
      rawExtendLayer (q.1.1, q.2.2, q.2.1))
    have hextendInput : Primrec (fun q :
        LayerRunInput Action × (LayerCode × ℕ) =>
        ((q.1.1, q.2.2, q.2.1) : ExtendInput Action)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.snd)
          (Primrec.fst.comp Primrec.snd))
    exact rawExtendLayer_primrec.comp hextendInput
  have hfold := Primrec.list_foldl
    (α := LayerRunInput Action) (β := ℕ) (σ := LayerCode)
    (f := fun input => input.2.reverse)
    (g := fun input => rawBaseLayer input.1)
    (h := fun input point =>
      rawExtendLayer (input.1, point.2, point.1))
    hstack hbase hstep
  exact hfold

omit [Primcodable Action] in
private theorem rawStackLayer_eq
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    rawStackLayer (machine, stack) =
      layerCode (stackLayer machine stack) := by
  unfold rawStackLayer stackLayer
  exact rawLayerFold_eq machine stack.reverse _ _
    (rawBaseLayer_eq machine)

private abbrev StackSchemaInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × List ℕ)

private def rawStackSchema
    (input : StackSchemaInput Action) : RegularTerm :=
  let layer := rawStackLayer (input.1, input.2.2)
  (layer.1, layer.2.getD input.2.1 0)

omit [DecidableEq Action] in
private theorem rawStackSchema_primrec :
    Primrec (rawStackSchema (Action := Action)) := by
  have hlayerInput : Primrec (fun input : StackSchemaInput Action =>
      ((input.1, input.2.2) : LayerRunInput Action)) :=
    Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hlayer : Primrec (fun input : StackSchemaInput Action =>
      rawStackLayer (input.1, input.2.2)) :=
    rawStackLayer_primrec.comp hlayerInput
  have hstate : Primrec (fun input : StackSchemaInput Action =>
      input.2.1) := Primrec.fst.comp Primrec.snd
  have hroot : Primrec (fun input : StackSchemaInput Action =>
      (rawStackLayer (input.1, input.2.2)).2.getD input.2.1 0) :=
    Primrec.list_getD 0 |>.comp (Primrec.snd.comp hlayer) hstate
  exact Primrec.pair (Primrec.fst.comp hlayer) hroot

omit [Primcodable Action] in
private theorem rawStackSchema_eq
    (machine : EncodedDPDA Action) (q : ℕ) (stack : List ℕ) :
    rawStackSchema (machine, q, stack) = stackSchema machine q stack := by
  unfold rawStackSchema stackSchema
  rw [rawStackLayer_eq]
  rfl

private def rawGrammarRanks
    (machine : EncodedDPDA Action) : List ℕ :=
  (List.range (bottomSymbol machine)).map (fun _ => machine.numStates) ++ [0]

omit [DecidableEq Action] in
private theorem rawGrammarRanks_primrec :
    Primrec (rawGrammarRanks (Action := Action)) := by
  have hbottom : Primrec (fun machine : EncodedDPDA Action =>
      bottomSymbol machine) := by
    unfold bottomSymbol
    exact Primrec.nat_mul.comp numStates_primrec
      numStackSymbols_primrec
  have hrange : Primrec (fun machine : EncodedDPDA Action =>
      List.range (bottomSymbol machine)) :=
    Primrec.list_range.comp hbottom
  have hreplicate : Primrec (fun machine : EncodedDPDA Action =>
      (List.range (bottomSymbol machine)).map
        (fun _ => machine.numStates)) := by
    have hvalue : Primrec₂ (fun (machine : EncodedDPDA Action)
        (_ : ℕ) => machine.numStates) := by
      show Primrec (fun p : EncodedDPDA Action × ℕ => p.1.numStates)
      exact numStates_primrec.comp Primrec.fst
    exact Primrec.list_map hrange hvalue
  exact Primrec.list_append.comp hreplicate (Primrec.const [0])

omit [Primcodable Action] [DecidableEq Action] in
private theorem rawGrammarRanks_eq (machine : EncodedDPDA Action) :
    rawGrammarRanks machine = grammarRanks machine := by
  simp [rawGrammarRanks, grammarRanks]

private def keyMember (key : InputKey Action)
    (keys : List (InputKey Action)) : Bool :=
  keys.any fun item => decide (key = item)

private theorem keyMember_primrec :
    Primrec₂ (keyMember (Action := Action)) := by
  show Primrec (fun q : InputKey Action × List (InputKey Action) =>
    keyMember q.1 q.2)
  have hequal : Primrec₂ (fun
      (q : InputKey Action × List (InputKey Action))
      (item : InputKey Action) => decide (q.1 = item)) := by
    show Primrec (fun p :
        (InputKey Action × List (InputKey Action)) × InputKey Action =>
      decide (p.1.1 = p.2))
    exact (PrimrecRel.decide Primrec.eq).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact primrec_list_any (f := fun q :
      InputKey Action × List (InputKey Action) => q.2)
    (p := fun q item => decide (q.1 = item)) Primrec.snd hequal

private def dedupKeys (keys : List (InputKey Action)) :
    List (InputKey Action) :=
  keys.foldr (fun key result =>
    bif keyMember key result then result else key :: result) []

private theorem dedupKeys_primrec :
    Primrec (dedupKeys (Action := Action)) := by
  have hstep : Primrec₂ (fun (_ : List (InputKey Action))
      (point : InputKey Action × List (InputKey Action)) =>
      bif keyMember point.1 point.2 then
        point.2 else point.1 :: point.2) := by
    show Primrec (fun q :
        List (InputKey Action) ×
          (InputKey Action × List (InputKey Action)) =>
      bif keyMember q.2.1 q.2.2 then q.2.2 else q.2.1 :: q.2.2)
    have hpoint : Primrec (fun q :
        List (InputKey Action) ×
          (InputKey Action × List (InputKey Action)) => q.2) :=
      Primrec.snd
    have hmember : Primrec (fun q :
        List (InputKey Action) ×
          (InputKey Action × List (InputKey Action)) =>
        keyMember q.2.1 q.2.2) :=
      keyMember_primrec.comp
        (Primrec.fst.comp hpoint) (Primrec.snd.comp hpoint)
    have hkeep : Primrec (fun q :
        List (InputKey Action) ×
          (InputKey Action × List (InputKey Action)) => q.2.2) :=
      Primrec.snd.comp hpoint
    have hcons : Primrec (fun q :
        List (InputKey Action) ×
          (InputKey Action × List (InputKey Action)) =>
        q.2.1 :: q.2.2) :=
      Primrec.list_cons.comp (Primrec.fst.comp hpoint)
        (Primrec.snd.comp hpoint)
    exact Primrec.cond hmember hkeep hcons
  have hfold := Primrec.list_foldr
    (α := List (InputKey Action)) (β := InputKey Action)
    (σ := List (InputKey Action))
    (f := fun keys => keys) (g := fun _ => [])
    (h := fun _ point =>
      bif keyMember point.1 point.2 then
        point.2 else point.1 :: point.2)
    Primrec.id (Primrec.const []) hstep
  exact hfold

omit [Primcodable Action] in
private theorem dedupKeys_eq (keys : List (InputKey Action)) :
    dedupKeys keys = keys.dedup := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simp only [dedupKeys, List.foldr]
      change
        (bif keyMember key (dedupKeys keys) then
          dedupKeys keys else key :: dedupKeys keys) =
        (key :: keys).dedup
      rw [ih, List.dedup_cons]
      by_cases hmem : key ∈ keys
      · have hmember : keyMember key keys.dedup = true := by
          simp [keyMember, List.any_eq_true, List.mem_dedup, hmem]
        simp [hmember, hmem]
      · have hmember : keyMember key keys.dedup = false := by
          apply Bool.eq_false_iff.mpr
          intro htrue
          rw [keyMember, List.any_eq_true] at htrue
          obtain ⟨item, hitem, hequal⟩ := htrue
          have hequal' : key = item := of_decide_eq_true hequal
          subst item
          exact hmem (List.mem_dedup.mp hitem)
        simp [hmember, hmem]

private def rawInputKey
    (input : EncodedDPDA Action × InputRow Action) : InputKey Action :=
  (input.2.1 % input.1.numStates, input.2.2.1,
    input.2.2.2.1 % input.1.numStackSymbols)

omit [DecidableEq Action] in
private theorem rawInputKey_primrec :
    Primrec (rawInputKey (Action := Action)) := by
  have hmachine : Primrec (fun input :
      EncodedDPDA Action × InputRow Action => input.1) := Primrec.fst
  have hrow : Primrec (fun input :
      EncodedDPDA Action × InputRow Action => input.2) := Primrec.snd
  have hstate : Primrec (fun input :
      EncodedDPDA Action × InputRow Action =>
      input.2.1 % input.1.numStates) :=
    Primrec.nat_mod.comp (Primrec.fst.comp hrow)
      (numStates_primrec.comp hmachine)
  have haction : Primrec (fun input :
      EncodedDPDA Action × InputRow Action => input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hrow)
  have htop : Primrec (fun input :
      EncodedDPDA Action × InputRow Action =>
      input.2.2.2.1 % input.1.numStackSymbols) :=
    Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.snd.comp hrow)))
      (numStackSymbols_primrec.comp hmachine)
  exact Primrec.pair hstate (Primrec.pair haction htop)

private def rawInputKeys (machine : EncodedDPDA Action) :
    List (InputKey Action) :=
  dedupKeys (machine.inputRows.map fun row => rawInputKey (machine, row))

private theorem rawInputKeys_primrec :
    Primrec (rawInputKeys (Action := Action)) := by
  have hmapped : Primrec (fun machine : EncodedDPDA Action =>
      machine.inputRows.map fun row => rawInputKey (machine, row)) :=
    Primrec.list_map inputRows_primrec rawInputKey_primrec.to₂
  exact dedupKeys_primrec.comp hmapped

omit [Primcodable Action] in
private theorem rawInputKeys_eq (machine : EncodedDPDA Action) :
    rawInputKeys machine = inputKeys machine := by
  unfold rawInputKeys inputKeys rawInputKey
  rw [dedupKeys_eq]

/-- The duplicate-free normalized input-key enumeration is primitive
recursive in the encoded transition table. -/
public theorem inputKeys_primrec :
    Primrec (inputKeys :
      EncodedDPDA Action → List (InputKey Action)) := by
  apply rawInputKeys_primrec.of_eq
  intro machine
  exact rawInputKeys_eq machine

private abbrev RuleInput (Action : Type) :=
  EncodedDPDA Action × InputKey Action

private def rawRuleForKey (input : RuleInput Action) :
    Option (RawRule Action) :=
  let machine := input.1
  let key := input.2
  let epsilon := rawEpsilonStep? (machine, key.1, key.2.2)
  bif epsilon.isSome then none else
    (rawInputStep? (machine, key.1, key.2.1, key.2.2)).map fun out =>
      (headSymbol machine key.1 key.2.2, key.2.1,
        rawStackSchema (machine, out.1, out.2))

private theorem rawRuleForKey_primrec :
    Primrec (rawRuleForKey (Action := Action)) := by
  have hmachine : Primrec (fun input : RuleInput Action => input.1) :=
    Primrec.fst
  have hkey : Primrec (fun input : RuleInput Action => input.2) :=
    Primrec.snd
  have hstate : Primrec (fun input : RuleInput Action => input.2.1) :=
    Primrec.fst.comp hkey
  have haction : Primrec (fun input : RuleInput Action => input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hkey)
  have htop : Primrec (fun input : RuleInput Action => input.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hkey)
  have hepsilonInput : Primrec (fun input : RuleInput Action =>
      ((input.1, input.2.1, input.2.2.2) : HeadInput Action)) :=
    Primrec.pair hmachine (Primrec.pair hstate htop)
  have hepsilon : Primrec (fun input : RuleInput Action =>
      rawEpsilonStep? (input.1, input.2.1, input.2.2.2)) :=
    rawEpsilonStep?_primrec.comp hepsilonInput
  have hsome : Primrec (fun input : RuleInput Action =>
      (rawEpsilonStep? (input.1, input.2.1,
        input.2.2.2)).isSome) :=
    Primrec.option_isSome.comp hepsilon
  have hinputInput : Primrec (fun input : RuleInput Action =>
      ((input.1, input.2.1, input.2.2.1, input.2.2.2) :
        InputHeadInput Action)) :=
    Primrec.pair hmachine
      (Primrec.pair hstate (Primrec.pair haction htop))
  have hinput : Primrec (fun input : RuleInput Action =>
      rawInputStep? (input.1, input.2.1,
        input.2.2.1, input.2.2.2)) :=
    rawInputStep?_primrec.comp hinputInput
  have hresult : Primrec₂ (fun (input : RuleInput Action)
      (out : ℕ × List ℕ) =>
      ((headSymbol input.1 input.2.1 input.2.2.2,
        input.2.2.1,
        rawStackSchema (input.1, out.1, out.2)) : RawRule Action)) := by
    show Primrec (fun q : RuleInput Action × (ℕ × List ℕ) =>
      ((headSymbol q.1.1 q.1.2.1 q.1.2.2.2,
        q.1.2.2.1,
        rawStackSchema (q.1.1, q.2.1, q.2.2)) : RawRule Action))
    have hmachine' : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) => q.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hstate' : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) => q.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have haction' : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) => q.1.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst))
    have htop' : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) => q.1.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst))
    have houtState : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) => q.2.1) :=
      Primrec.fst.comp Primrec.snd
    have houtStack : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) => q.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hhead : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) =>
        headSymbol q.1.1 q.1.2.1 q.1.2.2.2) := by
      unfold headSymbol
      exact Primrec.nat_add.comp
        (Primrec.nat_mul.comp hstate'
          (numStackSymbols_primrec.comp hmachine')) htop'
    have hschemaInput : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) =>
        ((q.1.1, q.2.1, q.2.2) : StackSchemaInput Action)) :=
      Primrec.pair hmachine' (Primrec.pair houtState houtStack)
    have hschema : Primrec (fun q :
        RuleInput Action × (ℕ × List ℕ) =>
        rawStackSchema (q.1.1, q.2.1, q.2.2)) :=
      rawStackSchema_primrec.comp hschemaInput
    exact Primrec.pair hhead (Primrec.pair haction' hschema)
  have hmapped : Primrec (fun input : RuleInput Action =>
      (rawInputStep? (input.1, input.2.1, input.2.2.1,
        input.2.2.2)).map (fun out =>
          ((headSymbol input.1 input.2.1 input.2.2.2,
            input.2.2.1,
            rawStackSchema (input.1, out.1, out.2)) : RawRule Action))) :=
    Primrec.option_map hinput hresult
  exact Primrec.cond hsome (Primrec.const none) hmapped

omit [Primcodable Action] in
private theorem rawRuleForKey_eq
    (machine : EncodedDPDA Action) (key : InputKey Action) :
    rawRuleForKey (machine, key) = ruleForKey machine key := by
  dsimp [rawRuleForKey, ruleForKey]
  rw [rawEpsilonStep?_eq]
  cases hepsilon : Machine.epsilonStep? machine key.1 key.2.2 with
  | some out => rfl
  | none =>
      rw [rawInputStep?_eq]
      cases hinput : Machine.inputStep? machine key.1 key.2.1 key.2.2 with
      | none => rfl
      | some out =>
          rcases out with ⟨target, stack⟩
          simp only [Option.map_some]
          rw [rawStackSchema_eq]
          simp

private def rawGrammar
    (machine : EncodedDPDA Action) : EncodedFirstOrderGrammar Action :=
  (rawGrammarRanks machine,
    (rawInputKeys machine).filterMap fun key =>
      rawRuleForKey (machine, key))

private theorem rawGrammar_primrec :
    Primrec (rawGrammar (Action := Action)) := by
  have hrules : Primrec (fun machine : EncodedDPDA Action =>
      (rawInputKeys machine).filterMap fun key =>
        rawRuleForKey (machine, key)) :=
    Primrec.listFilterMap rawInputKeys_primrec
      rawRuleForKey_primrec.to₂
  exact Primrec.pair rawGrammarRanks_primrec hrules

omit [Primcodable Action] in
private theorem rawGrammar_eq (machine : EncodedDPDA Action) :
    rawGrammar machine = grammar machine := by
  unfold rawGrammar grammar
  rw [rawGrammarRanks_eq, rawInputKeys_eq]
  congr 1
  apply List.filterMap_congr
  intro key hkey
  exact rawRuleForKey_eq machine key

/-- The Appendix-1 first-order grammar is a total computable function of the
raw encoded DPDA transition table. -/
public theorem grammar_computable :
    Computable (grammar :
      EncodedDPDA Action → EncodedFirstOrderGrammar Action) := by
  apply rawGrammar_primrec.to_comp.of_eq
  intro machine
  exact rawGrammar_eq machine

end DPDAToFirstOrder

end DCFEquivalence
