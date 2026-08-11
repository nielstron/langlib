module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAToExposingFirstOrder
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAObservableReturnsComputability
public import Langlib.Utilities.PrimrecHelpers

@[expose]
public section

/-!
# Effectivity of the compressed DPDA translation

The exposing translation retains only observable return continuations.  This
file shows that its compressed rank table and finite graph constructors are
still uniform computable functions of the raw encoded DPDA.
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDAToExposingFirstOrder

variable {Action : Type} [Fintype Action] [Primcodable Action]
  [DecidableEq Action]

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

private abbrev HeadInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × ℕ)

omit [Fintype Action] [DecidableEq Action] in
public theorem headSymbol_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      headSymbol input.1 input.2.1 input.2.2) := by
  unfold headSymbol DPDAToFirstOrder.headSymbol
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.fst.comp Primrec.snd)
      (numStackSymbols_primrec.comp Primrec.fst))
    (Primrec.snd.comp Primrec.snd)

omit [Fintype Action] [DecidableEq Action] in
public theorem bottomSymbol_primrec :
    Primrec (bottomSymbol : EncodedDPDA Action → ℕ) := by
  unfold bottomSymbol DPDAToFirstOrder.bottomSymbol
  exact Primrec.nat_mul.comp numStates_primrec
    numStackSymbols_primrec

/-- The compressed continuation domain is primitive recursive. -/
public theorem headTargets_primrec :
    Primrec (fun input : EncodedDPDA Action × (ℕ × ℕ) =>
      headTargets input.1 input.2.1 input.2.2) := by
  unfold headTargets
  exact DPDAObservableReturns.exposedTargets_primrec

private abbrev RankInput (Action : Type) :=
  EncodedDPDA Action × ℕ

private def codedRankTargets (input : RankInput Action) : List ℕ :=
  headTargets input.1
    (input.2 / input.1.numStackSymbols)
    (input.2 % input.1.numStackSymbols)

private theorem codedRankTargets_primrec :
    Primrec (codedRankTargets (Action := Action)) := by
  have hmachine : Primrec (fun input : RankInput Action => input.1) :=
    Primrec.fst
  have hsymbol : Primrec (fun input : RankInput Action => input.2) :=
    Primrec.snd
  have hstack : Primrec (fun input : RankInput Action =>
      input.1.numStackSymbols) :=
    numStackSymbols_primrec.comp hmachine
  have hstate : Primrec (fun input : RankInput Action =>
      input.2 / input.1.numStackSymbols) :=
    Primrec.nat_div.comp hsymbol hstack
  have htop : Primrec (fun input : RankInput Action =>
      input.2 % input.1.numStackSymbols) :=
    Primrec.nat_mod.comp hsymbol hstack
  apply (headTargets_primrec.comp
    (Primrec.pair hmachine (Primrec.pair hstate htop))).of_eq
  intro input
  rfl

private def codedRankAt (input : RankInput Action) : ℕ :=
  bif decide (input.2 < bottomSymbol input.1) then
    (codedRankTargets input).length
  else
    0

private theorem codedRankAt_primrec :
    Primrec (codedRankAt (Action := Action)) := by
  have hbelow : Primrec (fun input : RankInput Action =>
      decide (input.2 < bottomSymbol input.1)) :=
    (PrimrecRel.decide Primrec.nat_lt).comp Primrec.snd
      (bottomSymbol_primrec.comp Primrec.fst)
  apply (Primrec.cond hbelow
    (Primrec.list_length.comp codedRankTargets_primrec)
    (Primrec.const 0)).of_eq
  intro input
  rfl

/-- Each entry of the compressed rank table is primitive recursive. -/
public theorem rankAt_primrec :
    Primrec (fun input : EncodedDPDA Action × ℕ =>
      rankAt input.1 input.2) := by
  apply codedRankAt_primrec.of_eq
  intro input
  simp [codedRankAt, codedRankTargets, rankAt]

/-- The complete compressed rank table is primitive recursive. -/
public theorem grammarRanks_primrec :
    Primrec (grammarRanks :
      EncodedDPDA Action → List ℕ) := by
  have hrange : Primrec (fun machine : EncodedDPDA Action =>
      List.range (bottomSymbol machine)) :=
    Primrec.list_range.comp bottomSymbol_primrec
  have hranks : Primrec (fun machine : EncodedDPDA Action =>
      (List.range (bottomSymbol machine)).map
        (rankAt machine)) :=
    Primrec.list_map hrange rankAt_primrec.to₂
  unfold grammarRanks
  exact Primrec.list_append.comp hranks (Primrec.const [0])

/-- Selecting retained continuation roots is primitive recursive in both
lists. -/
public theorem selectRoots_primrec :
    Primrec (fun input : List ℕ × List ℕ =>
      selectRoots input.1 input.2) := by
  have hselect : Primrec₂ (fun (input : List ℕ × List ℕ)
      (target : ℕ) => input.2[target]?.getD 0) := by
    show Primrec (fun input : (List ℕ × List ℕ) × ℕ =>
      input.1.2[input.2]?.getD 0)
    have hget : Primrec (fun input : (List ℕ × List ℕ) × ℕ =>
        input.1.2[input.2]?) :=
      Primrec.list_getElem?.comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact Primrec.option_getD.comp hget (Primrec.const 0)
  unfold selectRoots
  exact Primrec.list_map Primrec.fst hselect

private abbrev LayerCode := List RawNode × List ℕ

private def layerCode (layer : TermLayer) : LayerCode :=
  (layer.nodes, layer.roots)

private abbrev SchemaBaseInput (Action : Type) :=
  EncodedDPDA Action × List ℕ

private theorem natList_idxOf_primrec :
    Primrec (fun input : List ℕ × ℕ => input.1.idxOf input.2) := by
  exact Primrec.list_idxOf.comp Primrec.snd Primrec.fst

private def rawSchemaBaseLayer
    (input : SchemaBaseInput Action) : LayerCode :=
  ((List.range input.2.length).map Sum.inl ++
      [.inr (bottomSymbol input.1, [])],
    (List.range input.1.numStates).map fun state =>
      input.2.idxOf state)

private def rawSchemaVariables
    (input : SchemaBaseInput Action) : List RawNode :=
  (List.range input.2.length).map Sum.inl

private theorem rawSchemaVariables_primrec :
    Primrec (rawSchemaVariables (Action := Action)) := by
  have hrange : Primrec (fun input : SchemaBaseInput Action =>
      List.range input.2.length) :=
    Primrec.list_range.comp
      (Primrec.list_length.comp Primrec.snd)
  have hnode : Primrec₂ (fun (_ : SchemaBaseInput Action)
      (index : ℕ) => (.inl index : RawNode)) := by
    show Primrec (fun input : SchemaBaseInput Action × ℕ =>
      (.inl input.2 : RawNode))
    exact Primrec.sumInl.comp Primrec.snd
  unfold rawSchemaVariables
  exact Primrec.list_map hrange hnode

private def rawSchemaBottomNode
    (input : SchemaBaseInput Action) : RawNode :=
  .inr (bottomSymbol input.1, [])

private theorem rawSchemaBottomNode_primrec :
    Primrec (rawSchemaBottomNode (Action := Action)) := by
  unfold rawSchemaBottomNode
  exact Primrec.sumInr.comp
    (Primrec.pair (bottomSymbol_primrec.comp Primrec.fst)
      (Primrec.const []))

private def rawSchemaRoots
    (input : SchemaBaseInput Action) : List ℕ :=
  (List.range input.1.numStates).map fun state =>
    input.2.idxOf state

private def rawSchemaRootAt
    (input : SchemaBaseInput Action × ℕ) : ℕ :=
  input.1.2.idxOf input.2

private theorem rawSchemaRootAt_primrec :
    Primrec (rawSchemaRootAt (Action := Action)) := by
  apply (natList_idxOf_primrec.comp
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)).of_eq
  intro input
  rfl

private theorem rawSchemaRoots_primrec :
    Primrec (rawSchemaRoots (Action := Action)) := by
  have hstates : Primrec (fun input : SchemaBaseInput Action =>
      List.range input.1.numStates) :=
    Primrec.list_range.comp (numStates_primrec.comp Primrec.fst)
  apply (Primrec.list_map hstates rawSchemaRootAt_primrec.to₂).of_eq
  intro input
  rfl

private theorem rawSchemaBaseLayer_primrec :
    Primrec (rawSchemaBaseLayer (Action := Action)) := by
  have hnodes : Primrec (fun input : SchemaBaseInput Action =>
      rawSchemaVariables input ++ [rawSchemaBottomNode input]) :=
    Primrec.list_append.comp rawSchemaVariables_primrec
      (Primrec.list_cons.comp rawSchemaBottomNode_primrec
        (Primrec.const []))
  apply (Primrec.pair hnodes rawSchemaRoots_primrec).of_eq
  intro input
  rfl

omit [Primcodable Action] in
private theorem rawSchemaBaseLayer_eq
    (machine : EncodedDPDA Action) (domain : List ℕ) :
    rawSchemaBaseLayer (machine, domain) =
      layerCode (schemaBaseLayer machine domain) := by
  rfl

private def rawGroundBaseLayer
    (machine : EncodedDPDA Action) : LayerCode :=
  ([.inr (bottomSymbol machine, [])],
    (List.range machine.numStates).map fun _ => 0)

private theorem rawGroundBaseLayer_primrec :
    Primrec (rawGroundBaseLayer (Action := Action)) := by
  have hnode : Primrec (fun machine : EncodedDPDA Action =>
      (.inr (bottomSymbol machine, []) : RawNode)) :=
    Primrec.sumInr.comp
      (Primrec.pair bottomSymbol_primrec (Primrec.const []))
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
private theorem rawGroundBaseLayer_eq
    (machine : EncodedDPDA Action) :
    rawGroundBaseLayer machine =
      layerCode (groundBaseLayer machine) := by
  simp [rawGroundBaseLayer, layerCode, groundBaseLayer]

private abbrev ExtendInput (Action : Type) :=
  EncodedDPDA Action × (ℕ × LayerCode)

private abbrev ExtendPointInput (Action : Type) :=
  ExtendInput Action × ℕ

private def rawExtendHeadInput
    (input : ExtendPointInput Action) :
    EncodedDPDA Action × (ℕ × ℕ) :=
  (input.1.1, input.2, input.1.2.1)

private theorem rawExtendHeadInput_primrec :
    Primrec (rawExtendHeadInput (Action := Action)) := by
  unfold rawExtendHeadInput
  exact Primrec.pair (Primrec.fst.comp Primrec.fst)
    (Primrec.pair Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))

private def rawExtendEpsilon
    (input : ExtendPointInput Action) : Option (ℕ × List ℕ) :=
  DPDAToFirstOrder.Machine.epsilonStep?
    input.1.1 input.2 input.1.2.1

private theorem rawExtendEpsilon_primrec :
    Primrec (rawExtendEpsilon (Action := Action)) := by
  apply (DPDAToFirstOrder.epsilonStep?_primrec.comp
    rawExtendHeadInput_primrec).of_eq
  intro input
  rfl

private def rawExtendBottomNode
    (input : ExtendPointInput Action) : RawNode :=
  .inr (bottomSymbol input.1.1, [])

private theorem rawExtendBottomNode_primrec :
    Primrec (rawExtendBottomNode (Action := Action)) := by
  unfold rawExtendBottomNode
  exact Primrec.sumInr.comp
    (Primrec.pair
      (bottomSymbol_primrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const []))

private def rawExtendChildren
    (input : ExtendPointInput Action) : List ℕ :=
  selectRoots
    (headTargets input.1.1 input.2 input.1.2.1)
    input.1.2.2.2

private def rawExtendTargets
    (input : ExtendPointInput Action) : List ℕ :=
  headTargets input.1.1 input.2 input.1.2.1

private theorem rawExtendTargets_primrec :
    Primrec (rawExtendTargets (Action := Action)) := by
  apply (headTargets_primrec.comp rawExtendHeadInput_primrec).of_eq
  intro input
  rfl

private theorem rawExtendChildren_primrec :
    Primrec (rawExtendChildren (Action := Action)) := by
  apply (selectRoots_primrec.comp
    (Primrec.pair rawExtendTargets_primrec
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst))))).of_eq
  intro input
  rfl

private def rawExtendApplication
    (input : ExtendPointInput Action) : RawNode :=
  .inr (headSymbol input.1.1 input.2 input.1.2.1,
    rawExtendChildren input)

private def rawExtendHeadSymbol
    (input : ExtendPointInput Action) : ℕ :=
  headSymbol input.1.1 input.2 input.1.2.1

private theorem rawExtendHeadSymbol_primrec :
    Primrec (rawExtendHeadSymbol (Action := Action)) := by
  apply (headSymbol_primrec.comp rawExtendHeadInput_primrec).of_eq
  intro input
  rfl

private theorem rawExtendApplication_primrec :
    Primrec (rawExtendApplication (Action := Action)) := by
  unfold rawExtendApplication
  exact Primrec.sumInr.comp
    (Primrec.pair rawExtendHeadSymbol_primrec
      rawExtendChildren_primrec)

private def rawExtendNode
    (input : ExtendPointInput Action) : RawNode :=
  let machine := input.1.1
  let Z := input.1.2.1
  let roots := input.1.2.2.2
  let q := input.2
  bif (DPDAToFirstOrder.Machine.epsilonStep? machine q Z).isSome then
    .inr (bottomSymbol machine, [])
  else
    .inr (headSymbol machine q Z,
      selectRoots (headTargets machine q Z) roots)

private theorem rawExtendNode_primrec :
    Primrec (rawExtendNode (Action := Action)) := by
  have hsome : Primrec (fun input : ExtendPointInput Action =>
      (rawExtendEpsilon input).isSome) :=
    Primrec.option_isSome.comp rawExtendEpsilon_primrec
  apply (Primrec.cond hsome rawExtendBottomNode_primrec
    rawExtendApplication_primrec).of_eq
  intro input
  cases h : DPDAToFirstOrder.Machine.epsilonStep?
      input.1.1 input.2 input.1.2.1 <;>
    simp [rawExtendNode, rawExtendEpsilon,
      rawExtendBottomNode, rawExtendApplication,
      rawExtendChildren, h]

private def rawExtendRoot
    (input : ExtendPointInput Action) : ℕ :=
  let machine := input.1.1
  let Z := input.1.2.1
  let nodes := input.1.2.2.1
  let roots := input.1.2.2.2
  let q := input.2
  let result := DPDAToFirstOrder.Machine.epsilonStep? machine q Z
  bif result.isSome then
    roots[result.getD (0, []) |>.1]?.getD 0
  else
    nodes.length + q

private def rawExtendTarget
    (input : ExtendPointInput Action) : ℕ :=
  (rawExtendEpsilon input).getD (0, []) |>.1

private theorem rawExtendTarget_primrec :
    Primrec (rawExtendTarget (Action := Action)) := by
  unfold rawExtendTarget
  exact Primrec.fst.comp
    (Primrec.option_getD.comp rawExtendEpsilon_primrec
      (Primrec.const (0, [])))

private def rawExtendSelectedRoot
    (input : ExtendPointInput Action) : ℕ :=
  input.1.2.2.2[rawExtendTarget input]?.getD 0

private theorem rawExtendSelectedRoot_primrec :
    Primrec (rawExtendSelectedRoot (Action := Action)) := by
  have hoption : Primrec (fun input : ExtendPointInput Action =>
      input.1.2.2.2[rawExtendTarget input]?) :=
    Primrec.list_getElem?.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst)))
      rawExtendTarget_primrec
  unfold rawExtendSelectedRoot
  exact Primrec.option_getD.comp hoption (Primrec.const 0)

private def rawExtendFreshRoot
    (input : ExtendPointInput Action) : ℕ :=
  input.1.2.2.1.length + input.2

private theorem rawExtendFreshRoot_primrec :
    Primrec (rawExtendFreshRoot (Action := Action)) := by
  unfold rawExtendFreshRoot
  exact Primrec.nat_add.comp
    (Primrec.list_length.comp
      (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst))))
    Primrec.snd

private theorem rawExtendRoot_primrec :
    Primrec (rawExtendRoot (Action := Action)) := by
  have hsome : Primrec (fun input : ExtendPointInput Action =>
      (rawExtendEpsilon input).isSome) :=
    Primrec.option_isSome.comp rawExtendEpsilon_primrec
  apply (Primrec.cond hsome rawExtendSelectedRoot_primrec
    rawExtendFreshRoot_primrec).of_eq
  intro input
  cases h : DPDAToFirstOrder.Machine.epsilonStep?
      input.1.1 input.2 input.1.2.1 <;>
    simp [rawExtendRoot, rawExtendEpsilon, rawExtendTarget,
      rawExtendSelectedRoot, rawExtendFreshRoot, h]

private def rawExtendLayer (input : ExtendInput Action) : LayerCode :=
  let machine := input.1
  let nodes := input.2.2.1
  let newNodes := (List.range machine.numStates).map fun q =>
    rawExtendNode (input, q)
  let newRoots := (List.range machine.numStates).map fun q =>
    rawExtendRoot (input, q)
  (nodes ++ newNodes, newRoots)

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
  apply Prod.ext
  · change layer.nodes ++
        (List.range machine.numStates).map (fun q =>
          rawExtendNode ((machine, Z,
            (layer.nodes, layer.roots)), q)) =
      layer.nodes ++
        (List.range machine.numStates).map (fun q =>
          match DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
          | some _ => (.inr (bottomSymbol machine, []) : RawNode)
          | none => .inr (headSymbol machine q Z,
              selectRoots (headTargets machine q Z) layer.roots))
    congr 1
    apply List.map_congr_left
    intro q hq
    dsimp [rawExtendNode]
    cases DPDAToFirstOrder.Machine.epsilonStep? machine q Z <;> rfl
  · change (List.range machine.numStates).map (fun q =>
        rawExtendRoot ((machine, Z,
          (layer.nodes, layer.roots)), q)) =
      (List.range machine.numStates).map (fun q =>
        match DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
        | some (target, _) => layer.roots[target]?.getD 0
        | none => layer.nodes.length + q)
    apply List.map_congr_left
    intro q hq
    dsimp [rawExtendRoot]
    cases DPDAToFirstOrder.Machine.epsilonStep? machine q Z <;> rfl

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
      apply ih
      rw [hlayer, rawExtendLayer_eq]

private abbrev LayerRunInput (Action : Type) :=
  EncodedDPDA Action × List ℕ

private def rawConfigurationLayer
    (input : LayerRunInput Action) : LayerCode :=
  input.2.reverse.foldl
    (fun layer Z => rawExtendLayer (input.1, Z, layer))
    (rawGroundBaseLayer input.1)

private def rawConfigurationFoldStep
    (input : LayerRunInput Action × (LayerCode × ℕ)) : LayerCode :=
  rawExtendLayer (input.1.1, input.2.2, input.2.1)

private theorem rawConfigurationFoldStep_primrec :
    Primrec (rawConfigurationFoldStep (Action := Action)) := by
  apply (rawExtendLayer_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)))).of_eq
  intro input
  rfl

private theorem rawConfigurationLayer_primrec :
    Primrec (rawConfigurationLayer (Action := Action)) := by
  have hstack : Primrec (fun input : LayerRunInput Action =>
      input.2.reverse) :=
    Primrec.list_reverse.comp Primrec.snd
  have hbase : Primrec (fun input : LayerRunInput Action =>
      rawGroundBaseLayer input.1) :=
    rawGroundBaseLayer_primrec.comp Primrec.fst
  apply (Primrec.list_foldl hstack hbase
    rawConfigurationFoldStep_primrec.to₂).of_eq
  intro input
  rfl

omit [Primcodable Action] in
private theorem rawConfigurationLayer_eq
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    rawConfigurationLayer (machine, stack) =
      layerCode (configurationLayer machine stack) := by
  unfold rawConfigurationLayer configurationLayer
  exact rawLayerFold_eq machine stack.reverse _ _
    (rawGroundBaseLayer_eq machine)

private def rawConfigurationTerm
    (input : EncodedDPDA Action × DPDAToFirstOrder.Configuration) :
    RegularTerm :=
  let layer := rawConfigurationLayer (input.1, input.2.2)
  (layer.1, layer.2[input.2.1]?.getD 0)

private theorem rawConfigurationTerm_primrec :
    Primrec (rawConfigurationTerm (Action := Action)) := by
  have hlayer : Primrec (fun input :
      EncodedDPDA Action × DPDAToFirstOrder.Configuration =>
      rawConfigurationLayer (input.1, input.2.2)) :=
    rawConfigurationLayer_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.snd.comp Primrec.snd))
  have hstate : Primrec (fun input :
      EncodedDPDA Action × DPDAToFirstOrder.Configuration =>
      input.2.1) := Primrec.fst.comp Primrec.snd
  have hrootOption : Primrec (fun input :
      EncodedDPDA Action × DPDAToFirstOrder.Configuration =>
      (rawConfigurationLayer
        (input.1, input.2.2)).2[input.2.1]?) :=
    Primrec.list_getElem?.comp (Primrec.snd.comp hlayer) hstate
  have hroot : Primrec (fun input :
      EncodedDPDA Action × DPDAToFirstOrder.Configuration =>
      (rawConfigurationLayer
        (input.1, input.2.2)).2[input.2.1]?.getD 0) :=
    Primrec.option_getD.comp hrootOption (Primrec.const 0)
  exact Primrec.pair (Primrec.fst.comp hlayer) hroot

omit [Primcodable Action] in
private theorem rawConfigurationTerm_eq
    (machine : EncodedDPDA Action)
    (configuration : DPDAToFirstOrder.Configuration) :
    rawConfigurationTerm (machine, configuration) =
      configurationTerm machine configuration.1 configuration.2 := by
  unfold rawConfigurationTerm configurationTerm
  rw [rawConfigurationLayer_eq]
  rfl

/-- The compressed ground term is a total computable function of the raw
machine and configuration. -/
public theorem configurationTerm_computable :
    Computable (fun input :
      EncodedDPDA Action × DPDAToFirstOrder.Configuration =>
      configurationTerm input.1 input.2.1 input.2.2) := by
  apply rawConfigurationTerm_primrec.to_comp.of_eq
  intro input
  exact rawConfigurationTerm_eq input.1 input.2

/-- Curried form of `configurationTerm_computable`. -/
public theorem configurationTerm_computable₂ :
    Computable₂ (fun (machine : EncodedDPDA Action)
      (configuration : DPDAToFirstOrder.Configuration) =>
      configurationTerm machine configuration.1 configuration.2) :=
  Computable₂.mk configurationTerm_computable

private abbrev SchemaLayerRunInput (Action : Type) :=
  EncodedDPDA Action × (List ℕ × List ℕ)

private def rawStackLayer
    (input : SchemaLayerRunInput Action) : LayerCode :=
  input.2.2.reverse.foldl
    (fun layer Z => rawExtendLayer (input.1, Z, layer))
    (rawSchemaBaseLayer (input.1, input.2.1))

private def rawStackFoldStep
    (input : SchemaLayerRunInput Action × (LayerCode × ℕ)) :
    LayerCode :=
  rawExtendLayer (input.1.1, input.2.2, input.2.1)

private theorem rawStackFoldStep_primrec :
    Primrec (rawStackFoldStep (Action := Action)) := by
  apply (rawExtendLayer_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)))).of_eq
  intro input
  rfl

private theorem rawStackLayer_primrec :
    Primrec (rawStackLayer (Action := Action)) := by
  have hstack : Primrec (fun input : SchemaLayerRunInput Action =>
      input.2.2.reverse) :=
    Primrec.list_reverse.comp (Primrec.snd.comp Primrec.snd)
  have hbase : Primrec (fun input : SchemaLayerRunInput Action =>
      rawSchemaBaseLayer (input.1, input.2.1)) :=
    rawSchemaBaseLayer_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.fst.comp Primrec.snd))
  apply (Primrec.list_foldl hstack hbase
    rawStackFoldStep_primrec.to₂).of_eq
  intro input
  rfl

omit [Primcodable Action] in
private theorem rawStackLayer_eq
    (machine : EncodedDPDA Action) (domain stack : List ℕ) :
    rawStackLayer (machine, domain, stack) =
      layerCode (stackLayer machine domain stack) := by
  unfold rawStackLayer stackLayer
  exact rawLayerFold_eq machine stack.reverse _ _
    (rawSchemaBaseLayer_eq machine domain)

private abbrev StackSchemaInput (Action : Type) :=
  EncodedDPDA Action × (List ℕ × (ℕ × List ℕ))

private def rawStackSchema
    (input : StackSchemaInput Action) : RegularTerm :=
  let layer := rawStackLayer
    (input.1, input.2.1, input.2.2.2)
  (layer.1, layer.2[input.2.2.1]?.getD 0)

private theorem rawStackSchema_primrec :
    Primrec (rawStackSchema (Action := Action)) := by
  have hlayer : Primrec (fun input : StackSchemaInput Action =>
      rawStackLayer (input.1, input.2.1, input.2.2.2)) :=
    rawStackLayer_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hstate : Primrec (fun input : StackSchemaInput Action =>
      input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrootOption : Primrec (fun input : StackSchemaInput Action =>
      (rawStackLayer
        (input.1, input.2.1, input.2.2.2)).2[input.2.2.1]?) :=
    Primrec.list_getElem?.comp (Primrec.snd.comp hlayer) hstate
  have hroot : Primrec (fun input : StackSchemaInput Action =>
      (rawStackLayer
        (input.1, input.2.1,
          input.2.2.2)).2[input.2.2.1]?.getD 0) :=
    Primrec.option_getD.comp hrootOption (Primrec.const 0)
  exact Primrec.pair (Primrec.fst.comp hlayer) hroot

omit [Primcodable Action] in
private theorem rawStackSchema_eq
    (machine : EncodedDPDA Action) (domain : List ℕ)
    (q : ℕ) (stack : List ℕ) :
    rawStackSchema (machine, domain, q, stack) =
      stackSchema machine domain q stack := by
  unfold rawStackSchema stackSchema
  rw [rawStackLayer_eq]
  rfl

/-- The compressed open stack schema is a total computable function of its
machine, continuation domain, control state, and stack prefix. -/
public theorem stackSchema_computable :
    Computable (fun input :
      EncodedDPDA Action × (List ℕ × (ℕ × List ℕ)) =>
      stackSchema input.1 input.2.1 input.2.2.1 input.2.2.2) := by
  apply rawStackSchema_primrec.to_comp.of_eq
  intro input
  exact rawStackSchema_eq input.1 input.2.1
    input.2.2.1 input.2.2.2

private abbrev RuleInput (Action : Type) :=
  EncodedDPDA Action × InputKey Action

private def rawRuleHeadInput
    (input : RuleInput Action) :
    EncodedDPDA Action × (ℕ × ℕ) :=
  (input.1, input.2.1, input.2.2.2)

private theorem rawRuleHeadInput_primrec :
    Primrec (rawRuleHeadInput (Action := Action)) := by
  unfold rawRuleHeadInput
  exact Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private def rawRuleEpsilon
    (input : RuleInput Action) : Option (ℕ × List ℕ) :=
  DPDAToFirstOrder.Machine.epsilonStep?
    input.1 input.2.1 input.2.2.2

private theorem rawRuleEpsilon_primrec :
    Primrec (rawRuleEpsilon (Action := Action)) := by
  apply (DPDAToFirstOrder.epsilonStep?_primrec.comp
    rawRuleHeadInput_primrec).of_eq
  intro input
  rfl

private def rawRuleInputStep
    (input : RuleInput Action) : Option (ℕ × List ℕ) :=
  DPDAToFirstOrder.Machine.inputStep?
    input.1 input.2.1 input.2.2.1 input.2.2.2

private theorem rawRuleInputStep_primrec :
    Primrec (rawRuleInputStep (Action := Action)) := by
  apply (DPDAToFirstOrder.inputStep?_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp
            (Primrec.snd.comp Primrec.snd)))))).of_eq
  intro input
  rfl

private abbrev RuleOutputInput (Action : Type) :=
  RuleInput Action × (ℕ × List ℕ)

private def rawRuleOutput
    (input : RuleOutputInput Action) : RawRule Action :=
  (headSymbol input.1.1 input.1.2.1 input.1.2.2.2,
    input.1.2.2.1,
    rawStackSchema
      (input.1.1,
        headTargets input.1.1 input.1.2.1 input.1.2.2.2,
        input.2.1, input.2.2))

private def rawRuleOutputHeadInput
    (input : RuleOutputInput Action) :
    EncodedDPDA Action × (ℕ × ℕ) :=
  (input.1.1, input.1.2.1, input.1.2.2.2)

private theorem rawRuleOutputHeadInput_primrec :
    Primrec (rawRuleOutputHeadInput (Action := Action)) := by
  unfold rawRuleOutputHeadInput
  exact Primrec.pair (Primrec.fst.comp Primrec.fst)
    (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp Primrec.fst))))

private def rawRuleOutputDomain
    (input : RuleOutputInput Action) : List ℕ :=
  headTargets input.1.1 input.1.2.1 input.1.2.2.2

private theorem rawRuleOutputDomain_primrec :
    Primrec (rawRuleOutputDomain (Action := Action)) := by
  apply (headTargets_primrec.comp
    rawRuleOutputHeadInput_primrec).of_eq
  intro input
  rfl

private def rawRuleOutputSchemaInput
    (input : RuleOutputInput Action) : StackSchemaInput Action :=
  (input.1.1, rawRuleOutputDomain input,
    input.2.1, input.2.2)

private theorem rawRuleOutputSchemaInput_primrec :
    Primrec (rawRuleOutputSchemaInput (Action := Action)) := by
  unfold rawRuleOutputSchemaInput
  exact Primrec.pair (Primrec.fst.comp Primrec.fst)
    (Primrec.pair rawRuleOutputDomain_primrec
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))

private def rawRuleOutputHeadSymbol
    (input : RuleOutputInput Action) : ℕ :=
  headSymbol input.1.1 input.1.2.1 input.1.2.2.2

private theorem rawRuleOutputHeadSymbol_primrec :
    Primrec (rawRuleOutputHeadSymbol (Action := Action)) := by
  apply (headSymbol_primrec.comp
    rawRuleOutputHeadInput_primrec).of_eq
  intro input
  rfl

private def rawRuleOutputSchema
    (input : RuleOutputInput Action) : RegularTerm :=
  rawStackSchema
    (input.1.1,
      headTargets input.1.1 input.1.2.1 input.1.2.2.2,
      input.2.1, input.2.2)

private theorem rawRuleOutputSchema_primrec :
    Primrec (rawRuleOutputSchema (Action := Action)) := by
  apply (rawStackSchema_primrec.comp
    rawRuleOutputSchemaInput_primrec).of_eq
  intro input
  rfl

private theorem rawRuleOutput_primrec :
    Primrec (rawRuleOutput (Action := Action)) := by
  have haction : Primrec (fun input : RuleOutputInput Action =>
      input.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))
  apply (Primrec.pair rawRuleOutputHeadSymbol_primrec
    (Primrec.pair haction rawRuleOutputSchema_primrec)).of_eq
  intro input
  rfl

private def rawRuleForKey
    (input : RuleInput Action) : Option (RawRule Action) :=
  bif (rawRuleEpsilon input).isSome then
    none
  else
    (rawRuleInputStep input).map fun output =>
      rawRuleOutput (input, output)

private theorem rawRuleForKey_primrec :
    Primrec (rawRuleForKey (Action := Action)) := by
  have hsome : Primrec (fun input : RuleInput Action =>
      (rawRuleEpsilon input).isSome) :=
    Primrec.option_isSome.comp rawRuleEpsilon_primrec
  have hmapped : Primrec (fun input : RuleInput Action =>
      (rawRuleInputStep input).map fun output =>
        rawRuleOutput (input, output)) :=
    Primrec.option_map rawRuleInputStep_primrec
      rawRuleOutput_primrec.to₂
  unfold rawRuleForKey
  exact Primrec.cond hsome (Primrec.const none) hmapped

omit [Primcodable Action] in
private theorem rawRuleForKey_eq
    (machine : EncodedDPDA Action) (key : InputKey Action) :
    rawRuleForKey (machine, key) = ruleForKey machine key := by
  cases hepsilon : DPDAToFirstOrder.Machine.epsilonStep?
      machine key.1 key.2.2 with
  | some output =>
      simp [rawRuleForKey, ruleForKey, rawRuleEpsilon, hepsilon]
  | none =>
      cases hinput : DPDAToFirstOrder.Machine.inputStep?
          machine key.1 key.2.1 key.2.2 with
      | none =>
          simp [rawRuleForKey, ruleForKey, rawRuleEpsilon,
            rawRuleInputStep, hepsilon, hinput]
      | some output =>
          rcases output with ⟨target, stack⟩
          simp [rawRuleForKey, ruleForKey, rawRuleEpsilon,
            rawRuleInputStep, rawRuleOutput, hepsilon, hinput,
            rawStackSchema_eq]

private def rawGrammar
    (machine : EncodedDPDA Action) :
    EncodedFirstOrderGrammar Action :=
  (grammarRanks machine,
    (DPDAToFirstOrder.inputKeys machine).filterMap fun key =>
      rawRuleForKey (machine, key))

private theorem rawGrammar_primrec :
    Primrec (rawGrammar (Action := Action)) := by
  have hrules : Primrec (fun machine : EncodedDPDA Action =>
      (DPDAToFirstOrder.inputKeys machine).filterMap fun key =>
        rawRuleForKey (machine, key)) :=
    Primrec.listFilterMap DPDAToFirstOrder.inputKeys_primrec
      rawRuleForKey_primrec.to₂
  exact Primrec.pair grammarRanks_primrec hrules

omit [Primcodable Action] in
private theorem rawGrammar_eq (machine : EncodedDPDA Action) :
    rawGrammar machine = grammar machine := by
  unfold rawGrammar grammar
  congr 1
  apply List.filterMap_congr
  intro key hkey
  exact rawRuleForKey_eq machine key

/-- The compressed exposing first-order grammar is a total computable
function of the raw encoded DPDA transition table. -/
public theorem grammar_computable :
    Computable (grammar :
      EncodedDPDA Action → EncodedFirstOrderGrammar Action) := by
  apply rawGrammar_primrec.to_comp.of_eq
  intro machine
  exact rawGrammar_eq machine

end DPDAToExposingFirstOrder

end DCFEquivalence
