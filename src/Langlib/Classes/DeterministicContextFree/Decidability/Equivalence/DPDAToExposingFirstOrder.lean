module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAObservableReturnsComputability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GrammarNormalForm

@[expose]
public section

/-!
# DPDA translation with only observable return arguments

The ordinary Appendix-1 translation assigns one argument to every control
state.  Some of those arguments can never be exposed: no input word can pop
the represented stack head and return in that state.  This file gives the
effective compressed translation which retains exactly the targets computed
by `DPDAObservableReturns.exposedTargets`.

For a rule whose left-hand side represents `(q,Z)`, the retained target list
also determines its variable environment.  A continuation state in that list
is represented by its `idxOf`; an omitted continuation is represented by the
existing nullary stuck symbol.  Nested stable applications independently
project their children to their own observable return lists.
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDAToExposingFirstOrder

variable {Action : Type} [Fintype Action] [DecidableEq Action]

public abbrev TermLayer := DPDAToFirstOrder.TermLayer
public abbrev InputKey (Action : Type) := DPDAToFirstOrder.InputKey Action

@[expose] public def headSymbol (machine : EncodedDPDA Action)
    (q Z : ℕ) : ℕ :=
  DPDAToFirstOrder.headSymbol machine q Z

@[expose] public def bottomSymbol (machine : EncodedDPDA Action) : ℕ :=
  DPDAToFirstOrder.bottomSymbol machine

@[expose] public def headTargets
    (machine : EncodedDPDA Action) (q Z : ℕ) : List ℕ :=
  DPDAObservableReturns.exposedTargets machine q Z

@[expose] public def rankAt
    (machine : EncodedDPDA Action) (X : ℕ) : ℕ :=
  if X < bottomSymbol machine then
    (headTargets machine
      (X / machine.numStackSymbols)
      (X % machine.numStackSymbols)).length
  else
    0

/-- Rank table for all compressed head symbols and the nullary stuck symbol. -/
@[expose] public def grammarRanks
    (machine : EncodedDPDA Action) : List ℕ :=
  (List.range (bottomSymbol machine)).map (rankAt machine) ++ [0]

omit [Fintype Action] [DecidableEq Action] in
public theorem headSymbol_lt_bottom
    (machine : EncodedDPDA Action) {q Z : ℕ}
    (hq : q < machine.numStates) (hZ : Z < machine.numStackSymbols) :
    headSymbol machine q Z < bottomSymbol machine := by
  exact DPDAToFirstOrder.headSymbol_lt_bottom machine hq hZ

omit [Fintype Action] [DecidableEq Action] in
public theorem headSymbol_div_numStackSymbols
    (machine : EncodedDPDA Action) (q : ℕ) {Z : ℕ}
    (hZ : Z < machine.numStackSymbols) :
    headSymbol machine q Z / machine.numStackSymbols = q := by
  unfold headSymbol DPDAToFirstOrder.headSymbol
  rw [Nat.mul_comm]
  rw [Nat.mul_add_div machine.numStackSymbols_pos]
  simp [Nat.div_eq_of_lt hZ]

omit [Fintype Action] [DecidableEq Action] in
public theorem headSymbol_mod_numStackSymbols
    (machine : EncodedDPDA Action) (q : ℕ) {Z : ℕ}
    (hZ : Z < machine.numStackSymbols) :
    headSymbol machine q Z % machine.numStackSymbols = Z := by
  simp [headSymbol, DPDAToFirstOrder.headSymbol,
    Nat.add_mod, Nat.mod_eq_of_lt hZ]

omit [Fintype Action] in
public theorem grammarRanks_headSymbol
    (machine : EncodedDPDA Action) {q Z : ℕ}
    (hq : q < machine.numStates) (hZ : Z < machine.numStackSymbols) :
    (grammarRanks machine)[headSymbol machine q Z]? =
      some (headTargets machine q Z).length := by
  have hhead := headSymbol_lt_bottom machine hq hZ
  unfold grammarRanks
  rw [List.getElem?_append_left (by simpa using hhead)]
  rw [List.getElem?_map, List.getElem?_range hhead]
  simp [rankAt, hhead, headSymbol_div_numStackSymbols machine q hZ,
    headSymbol_mod_numStackSymbols machine q hZ]

omit [Fintype Action] in
public theorem grammarRanks_bottomSymbol
    (machine : EncodedDPDA Action) :
    (grammarRanks machine)[bottomSymbol machine]? = some 0 := by
  simp [grammarRanks, bottomSymbol]

/-- Select the continuation roots retained by one compressed head. -/
@[expose] public def selectRoots
    (targets roots : List ℕ) : List ℕ :=
  targets.map fun target => roots[target]?.getD 0

/-- Base environment for one rule.  Retained controls denote variables in
their list order; all other controls denote the nullary stuck term. -/
@[expose] public def schemaBaseLayer
    (machine : EncodedDPDA Action) (domain : List ℕ) : TermLayer where
  nodes :=
    (List.range domain.length).map Sum.inl ++
      [.inr (bottomSymbol machine, [])]
  roots :=
    (List.range machine.numStates).map fun state =>
      domain.idxOf state

/-- Base layer for a ground configuration. -/
@[expose] public def groundBaseLayer
    (machine : EncodedDPDA Action) : TermLayer where
  nodes := [.inr (bottomSymbol machine, [])]
  roots := List.replicate machine.numStates 0

/-- Add one compressed stack-symbol layer.  Epsilon heads reuse their selected
continuation root; stable heads allocate an application containing only
observable return continuations. -/
@[expose] public def extendLayer
    (machine : EncodedDPDA Action) (Z : ℕ) (layer : TermLayer) : TermLayer :=
  let offset := layer.nodes.length
  let newNodes := (List.range machine.numStates).map fun q =>
    match DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
    | some _ => (.inr (bottomSymbol machine, []) : RawNode)
    | none =>
        .inr (headSymbol machine q Z,
          selectRoots (headTargets machine q Z) layer.roots)
  let newRoots := (List.range machine.numStates).map fun q =>
    match DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
    | some (target, _) => layer.roots[target]?.getD 0
    | none => offset + q
  ⟨layer.nodes ++ newNodes, newRoots⟩

/-- Open compressed schema for a stack prefix. -/
@[expose] public def stackLayer
    (machine : EncodedDPDA Action) (domain stack : List ℕ) : TermLayer :=
  stack.reverse.foldl (fun layer Z => extendLayer machine Z layer)
    (schemaBaseLayer machine domain)

@[expose] public def stackSchema
    (machine : EncodedDPDA Action) (domain : List ℕ)
    (q : ℕ) (stack : List ℕ) : RegularTerm :=
  let layer := stackLayer machine domain stack
  (layer.nodes, layer.roots[q]?.getD 0)

/-- Compressed ground graph for a concrete configuration. -/
@[expose] public def configurationLayer
    (machine : EncodedDPDA Action) (stack : List ℕ) : TermLayer :=
  stack.reverse.foldl (fun layer Z => extendLayer machine Z layer)
    (groundBaseLayer machine)

@[expose] public def configurationTerm
    (machine : EncodedDPDA Action) (q : ℕ) (stack : List ℕ) :
    RegularTerm :=
  let layer := configurationLayer machine stack
  (layer.nodes, layer.roots[q]?.getD 0)

/-- Translate one selected input row.  Its source return mask is the variable
domain of the compressed right-hand side. -/
@[expose] public def ruleForKey
    (machine : EncodedDPDA Action) (key : InputKey Action) :
    Option (RawRule Action) :=
  match DPDAToFirstOrder.Machine.epsilonStep?
      machine key.1 key.2.2 with
  | some _ => none
  | none =>
      (DPDAToFirstOrder.Machine.inputStep?
        machine key.1 key.2.1 key.2.2).map fun out =>
        (headSymbol machine key.1 key.2.2, key.2.1,
          stackSchema machine
            (headTargets machine key.1 key.2.2)
            out.1 out.2)

@[expose] public def grammar
    (machine : EncodedDPDA Action) : EncodedFirstOrderGrammar Action :=
  (grammarRanks machine,
    (DPDAToFirstOrder.inputKeys machine).filterMap
      (ruleForKey machine))

omit [Fintype Action] in
@[simp] public theorem stackLayer_nil
    (machine : EncodedDPDA Action) (domain : List ℕ) :
    stackLayer machine domain [] = schemaBaseLayer machine domain := rfl

omit [Fintype Action] in
public theorem stackLayer_cons
    (machine : EncodedDPDA Action) (domain : List ℕ)
    (Z : ℕ) (stack : List ℕ) :
    stackLayer machine domain (Z :: stack) =
      extendLayer machine Z (stackLayer machine domain stack) := by
  simp [stackLayer, List.foldl_append]

omit [Fintype Action] in
@[simp] public theorem configurationLayer_nil
    (machine : EncodedDPDA Action) :
    configurationLayer machine [] = groundBaseLayer machine := rfl

omit [Fintype Action] in
public theorem configurationLayer_cons
    (machine : EncodedDPDA Action) (Z : ℕ) (stack : List ℕ) :
    configurationLayer machine (Z :: stack) =
      extendLayer machine Z (configurationLayer machine stack) := by
  simp [configurationLayer, List.foldl_append]

omit [Fintype Action] in
@[simp] public theorem extendLayer_nodes_length
    (machine : EncodedDPDA Action) (Z : ℕ) (layer : TermLayer) :
    (extendLayer machine Z layer).nodes.length =
      layer.nodes.length + machine.numStates := by
  simp [extendLayer]

omit [Fintype Action] in
@[simp] public theorem extendLayer_roots_length
    (machine : EncodedDPDA Action) (Z : ℕ) (layer : TermLayer) :
    (extendLayer machine Z layer).roots.length = machine.numStates := by
  simp [extendLayer]

@[expose] public def LayerReferences
    (machine : EncodedDPDA Action) (layer : TermLayer) : Prop :=
  layer.roots.length = machine.numStates ∧
    ∀ root ∈ layer.roots, root < layer.nodes.length

private theorem idxOf_le_length (domain : List ℕ) (state : ℕ) :
    domain.idxOf state ≤ domain.length := by
  by_cases hstate : state ∈ domain
  · exact Nat.le_of_lt (List.idxOf_lt_length_iff.mpr hstate)
  · exact (List.idxOf_eq_length_iff.mpr hstate).le

omit [Fintype Action] [DecidableEq Action] in
public theorem schemaBaseLayer_references
    (machine : EncodedDPDA Action) (domain : List ℕ) :
    LayerReferences machine (schemaBaseLayer machine domain) := by
  constructor
  · simp [schemaBaseLayer]
  · intro root hroot
    obtain ⟨state, hstate, rfl⟩ := List.mem_map.mp hroot
    have hle := idxOf_le_length domain state
    simp only [schemaBaseLayer, List.length_append, List.length_map,
      List.length_range, List.length_cons, List.length_nil]
    omega

omit [Fintype Action] [DecidableEq Action] in
public theorem groundBaseLayer_references
    (machine : EncodedDPDA Action) :
    LayerReferences machine (groundBaseLayer machine) := by
  constructor
  · simp [groundBaseLayer]
  · intro root hroot
    have hzero : root = 0 := by
      have hparts : machine.numStates ≠ 0 ∧ root = 0 := by
        simpa [groundBaseLayer] using hroot
      exact hparts.2
    subst root
    simp [groundBaseLayer]

omit [Fintype Action] in
public theorem extendLayer_references
    (machine : EncodedDPDA Action) (Z : ℕ) {layer : TermLayer}
    (hlayer : LayerReferences machine layer) :
    LayerReferences machine (extendLayer machine Z layer) := by
  constructor
  · exact extendLayer_roots_length machine Z layer
  · intro root hroot
    simp only [extendLayer] at hroot
    obtain ⟨q, hqRange, hrootEq⟩ := List.mem_map.mp hroot
    have hq : q < machine.numStates := List.mem_range.mp hqRange
    rw [extendLayer_nodes_length]
    cases hstep :
        DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
    | none =>
        simp only [hstep] at hrootEq
        subst root
        exact Nat.add_lt_add_left hq layer.nodes.length
    | some out =>
        rcases out with ⟨target, replacement⟩
        simp only [hstep] at hrootEq
        subst root
        have htarget : target < machine.numStates :=
          DPDAToFirstOrder.Machine.epsilonStep?_target_lt hstep
        have htargetRoots : target < layer.roots.length := by
          simpa [hlayer.1] using htarget
        have hlookup : layer.roots[target]? =
            some (layer.roots[target]'htargetRoots) := by
          rw [List.getElem?_eq_some_iff]
          exact ⟨htargetRoots, rfl⟩
        rw [hlookup]
        simp only [Option.getD_some]
        have hbound := hlayer.2 _ (List.getElem_mem htargetRoots)
        omega

public theorem stackLayer_references
    (machine : EncodedDPDA Action) (domain stack : List ℕ) :
    LayerReferences machine (stackLayer machine domain stack) := by
  induction stack with
  | nil => exact schemaBaseLayer_references machine domain
  | cons Z stack ih =>
      rw [stackLayer_cons]
      exact extendLayer_references machine Z ih

public theorem configurationLayer_references
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    LayerReferences machine (configurationLayer machine stack) := by
  induction stack with
  | nil => exact groundBaseLayer_references machine
  | cons Z stack ih =>
      rw [configurationLayer_cons]
      exact extendLayer_references machine Z ih

/-- Rank/reference validity of all nodes in a compressed layer. -/
@[expose] public def LayerNodesValid
    (machine : EncodedDPDA Action) (variableBound : ℕ)
    (layer : TermLayer) : Prop :=
  ∀ node ∈ layer.nodes,
    match node with
    | .inl x => x < variableBound
    | .inr (X, children) =>
        (grammarRanks machine)[X]? = some children.length ∧
          ∀ child ∈ children, child < layer.nodes.length

omit [Fintype Action] in
public theorem schemaBaseLayer_nodesValid
    (machine : EncodedDPDA Action) (domain : List ℕ) :
    LayerNodesValid machine domain.length
      (schemaBaseLayer machine domain) := by
  intro node hnode
  simp only [schemaBaseLayer] at hnode
  rw [List.mem_append] at hnode
  rcases hnode with hvariable | hbottom
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hvariable
    exact List.mem_range.mp hx
  · have hnode : node =
        .inr (bottomSymbol machine, []) := by
      simpa using hbottom
    subst node
    exact ⟨by simpa using grammarRanks_bottomSymbol machine, by simp⟩

omit [Fintype Action] in
public theorem groundBaseLayer_nodesValid
    (machine : EncodedDPDA Action) :
    LayerNodesValid machine 0 (groundBaseLayer machine) := by
  intro node hnode
  have hnode : node = .inr (bottomSymbol machine, []) := by
    simpa [groundBaseLayer] using hnode
  subst node
  exact ⟨by simpa using grammarRanks_bottomSymbol machine, by simp⟩

public theorem extendLayer_nodesValid
    (machine : EncodedDPDA Action) {variableBound : ℕ}
    {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    (hvalid : LayerNodesValid machine variableBound layer)
    {Z : ℕ} (hZ : Z < machine.numStackSymbols) :
    LayerNodesValid machine variableBound
      (extendLayer machine Z layer) := by
  intro node hnode
  simp only [extendLayer] at hnode
  rw [List.mem_append] at hnode
  rcases hnode with hold | hnew
  · have holdValid := hvalid node hold
    cases node with
    | inl x => exact holdValid
    | inr app =>
        rcases app with ⟨X, children⟩
        refine ⟨holdValid.1, ?_⟩
        intro child hchild
        have hbound := holdValid.2 child hchild
        rw [extendLayer_nodes_length]
        omega
  · obtain ⟨q, hqMem, hnodeEq⟩ := List.mem_map.mp hnew
    have hq : q < machine.numStates := List.mem_range.mp hqMem
    cases hstep :
        DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
    | some out =>
        simp only [hstep] at hnodeEq
        subst node
        exact ⟨by simpa using grammarRanks_bottomSymbol machine, by simp⟩
    | none =>
        simp only [hstep] at hnodeEq
        subst node
        refine ⟨?_, ?_⟩
        · simpa [selectRoots] using
            grammarRanks_headSymbol machine hq hZ
        · intro child hchild
          obtain ⟨target, htarget, hchildEq⟩ :=
            List.mem_map.mp hchild
          subst child
          have htargetBound : target < machine.numStates :=
            (DPDAObservableReturns.mem_exposedTargets_iff
              machine q Z target).mp htarget |>.2.1
          have htargetRoots : target < layer.roots.length := by
            simpa [hreferences.1] using htargetBound
          have hlookup : layer.roots[target]? =
              some (layer.roots[target]'htargetRoots) := by
            rw [List.getElem?_eq_some_iff]
            exact ⟨htargetRoots, rfl⟩
          rw [hlookup]
          simp only [Option.getD_some]
          have hbound :=
            hreferences.2 _ (List.getElem_mem htargetRoots)
          rw [extendLayer_nodes_length]
          omega

public theorem stackLayer_nodesValid
    (machine : EncodedDPDA Action) (domain : List ℕ)
    {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    LayerNodesValid machine domain.length
      (stackLayer machine domain stack) := by
  induction stack with
  | nil => exact schemaBaseLayer_nodesValid machine domain
  | cons Z stack ih =>
      rw [stackLayer_cons]
      apply extendLayer_nodesValid machine
        (stackLayer_references machine domain stack)
      · exact ih fun symbol hsymbol =>
          hstack symbol (by simp [hsymbol])
      · exact hstack Z (by simp)

public theorem configurationLayer_nodesValid
    (machine : EncodedDPDA Action) {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    LayerNodesValid machine 0 (configurationLayer machine stack) := by
  induction stack with
  | nil => exact groundBaseLayer_nodesValid machine
  | cons Z stack ih =>
      rw [configurationLayer_cons]
      apply extendLayer_nodesValid machine
        (configurationLayer_references machine stack)
      · exact ih fun symbol hsymbol =>
          hstack symbol (by simp [hsymbol])
      · exact hstack Z (by simp)

/-- Every application edge points into an earlier layer. -/
@[expose] public def LayerBackward (layer : TermLayer) : Prop :=
  ∀ i X children,
    layer.nodes[i]? = some (Sum.inr (X, children) : RawNode) →
    ∀ child ∈ children, child < i

omit [Fintype Action] [DecidableEq Action] in
public theorem schemaBaseLayer_backward
    (machine : EncodedDPDA Action) (domain : List ℕ) :
    LayerBackward (schemaBaseLayer machine domain) := by
  intro i X children hnode child hchild
  have hi : i < domain.length + 1 := by
    simpa [schemaBaseLayer] using
      (List.getElem?_eq_some_iff.mp hnode).1
  by_cases hprefix : i < domain.length
  · have hprefix' : i <
        ((List.range domain.length).map
          (Sum.inl : ℕ → RawNode)).length := by
      simpa using hprefix
    have hvariable := hnode
    change
      (((List.range domain.length).map
          (Sum.inl : ℕ → RawNode)) ++
        [.inr (bottomSymbol machine, [])])[i]? =
          some (Sum.inr (X, children) : RawNode) at hvariable
    rw [List.getElem?_append_left hprefix'] at hvariable
    rw [List.getElem?_map] at hvariable
    cases hsource :
        (List.range domain.length)[i]? <;> simp [hsource] at hvariable
  · have hiLast : i = domain.length := by
      omega
    subst i
    simp [schemaBaseLayer] at hnode
    rcases hnode with ⟨rfl, rfl⟩
    simp at hchild

omit [Fintype Action] [DecidableEq Action] in
public theorem groundBaseLayer_backward
    (machine : EncodedDPDA Action) :
    LayerBackward (groundBaseLayer machine) := by
  intro i X children hnode child hchild
  have hi : i < 1 := by
    simpa [groundBaseLayer] using
      (List.getElem?_eq_some_iff.mp hnode).1
  have hizero : i = 0 := by omega
  subst i
  simp [groundBaseLayer] at hnode
  rcases hnode with ⟨rfl, rfl⟩
  simp at hchild

public theorem extendLayer_backward
    (machine : EncodedDPDA Action) (Z : ℕ) {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    (hbackward : LayerBackward layer) :
    LayerBackward (extendLayer machine Z layer) := by
  intro i X children hnode child hchild
  have hi : i < layer.nodes.length + machine.numStates := by
    simpa [extendLayer_nodes_length] using
      (List.getElem?_eq_some_iff.mp hnode).1
  by_cases hprefix : i < layer.nodes.length
  · have hsource : layer.nodes[i]? =
        some (Sum.inr (X, children) : RawNode) := by
      simpa [extendLayer,
        List.getElem?_append_left hprefix] using hnode
    exact hbackward i X children hsource child hchild
  · let q := i - layer.nodes.length
    have hq : q < machine.numStates := by
      dsimp [q]
      omega
    have hiSplit : i = layer.nodes.length + q := by
      dsimp [q]
      omega
    have hnew :
        ((List.range machine.numStates).map fun state =>
          match DPDAToFirstOrder.Machine.epsilonStep?
              machine state Z with
          | some _ => (.inr (bottomSymbol machine, []) : RawNode)
          | none =>
              .inr (headSymbol machine state Z,
                selectRoots (headTargets machine state Z)
                  layer.roots))[q]? =
          some (Sum.inr (X, children) : RawNode) := by
      rw [hiSplit] at hnode
      simpa [extendLayer,
        List.getElem?_append_right] using hnode
    rw [List.getElem?_map] at hnew
    have hqRange : (List.range machine.numStates)[q]? = some q := by
      simp [hq]
    rw [hqRange] at hnew
    cases hstep :
        DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
    | some out =>
        simp only [hstep, Option.map_some, Option.some.injEq,
          Sum.inr.injEq, Prod.mk.injEq] at hnew
        rcases hnew with ⟨_, hchildren⟩
        subst children
        simp at hchild
    | none =>
        simp only [hstep, Option.map_some, Option.some.injEq,
          Sum.inr.injEq, Prod.mk.injEq] at hnew
        rcases hnew with ⟨_, hchildren⟩
        subst children
        obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hchild
        have htargetBound : target < machine.numStates :=
          (DPDAObservableReturns.mem_exposedTargets_iff
            machine q Z target).mp htarget |>.2.1
        have htargetRoots : target < layer.roots.length := by
          simpa [hreferences.1] using htargetBound
        have hlookup : layer.roots[target]? =
            some (layer.roots[target]'htargetRoots) := by
          rw [List.getElem?_eq_some_iff]
          exact ⟨htargetRoots, rfl⟩
        rw [hlookup]
        simp only [Option.getD_some]
        have hbound :=
          hreferences.2 _ (List.getElem_mem htargetRoots)
        rw [hiSplit]
        omega

public theorem stackLayer_backward
    (machine : EncodedDPDA Action) (domain stack : List ℕ) :
    LayerBackward (stackLayer machine domain stack) := by
  induction stack with
  | nil => exact schemaBaseLayer_backward machine domain
  | cons Z stack ih =>
      rw [stackLayer_cons]
      exact extendLayer_backward machine Z
        (stackLayer_references machine domain stack) ih

public theorem configurationLayer_backward
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    LayerBackward (configurationLayer machine stack) := by
  induction stack with
  | nil => exact groundBaseLayer_backward machine
  | cons Z stack ih =>
      rw [configurationLayer_cons]
      exact extendLayer_backward machine Z
        (configurationLayer_references machine stack) ih

private theorem unfoldsFiniteFrom_eq_true_of_backward
    (nodes : List RawNode)
    (hbackward : ∀ i X children,
      nodes[i]? = some (Sum.inr (X, children) : RawNode) →
      ∀ child ∈ children, child < i) :
    ∀ fuel visiting i,
      i < nodes.length → i < fuel →
      (∀ ancestor ∈ visiting, i < ancestor) →
      RegularTerm.unfoldsFiniteFrom nodes fuel visiting i = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro visiting i _ hi
      omega
  | succ fuel ih =>
      intro visiting i hiNodes hiFuel hvisiting
      simp only [RegularTerm.unfoldsFiniteFrom]
      have hnotMem : i ∉ visiting := by
        intro hmem
        exact (Nat.lt_irrefl i) (hvisiting i hmem)
      rw [if_neg hnotMem]
      let node : RawNode := nodes[i]'hiNodes
      have hnode : nodes[i]? = some node := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hiNodes, rfl⟩
      rw [hnode]
      cases hkind : node with
      | inl x => rfl
      | inr app =>
          rcases app with ⟨X, children⟩
          apply List.all_eq_true.mpr
          intro child hchild
          have hnodeApp : nodes[i]? =
              some (Sum.inr (X, children) : RawNode) := by
            simpa [hkind] using hnode
          have hchildLt : child < i :=
            hbackward i X children hnodeApp child hchild
          apply ih (visiting := i :: visiting) (i := child)
          · omega
          · omega
          · intro ancestor hancestor
            simp only [List.mem_cons] at hancestor
            rcases hancestor with rfl | hancestor
            · exact hchildLt
            · exact hchildLt.trans (hvisiting ancestor hancestor)

private theorem unfoldsFiniteCode_eq_true_of_backward
    {term : RegularTerm}
    (hroot : term.root < term.nodes.length)
    (hbackward : ∀ i X children,
      term.nodes[i]? = some (Sum.inr (X, children) : RawNode) →
      ∀ child ∈ children, child < i) :
    term.unfoldsFiniteCode = true := by
  unfold RegularTerm.unfoldsFiniteCode
  apply unfoldsFiniteFrom_eq_true_of_backward term.nodes hbackward
  · exact hroot
  · omega
  · simp

omit [Fintype Action] [DecidableEq Action] in
private theorem layerRoot_getElem?
    {machine : EncodedDPDA Action} {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    {q : ℕ} (hq : q < machine.numStates) :
    ∃ root, layer.roots[q]? = some root ∧
      root < layer.nodes.length := by
  have hqRoots : q < layer.roots.length := by
    simpa [hreferences.1] using hq
  refine ⟨layer.roots[q]'hqRoots, ?_,
    hreferences.2 _ (List.getElem_mem hqRoots)⟩
  rw [List.getElem?_eq_some_iff]
  exact ⟨hqRoots, rfl⟩

omit [Fintype Action] in
private theorem termWellFormed_of_layer
    {machine : EncodedDPDA Action} {variableBound : ℕ}
    {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    (hvalid : LayerNodesValid machine variableBound layer)
    {q : ℕ} (hq : q < machine.numStates) :
    RegularTerm.WellFormed (grammarRanks machine) variableBound
      (layer.nodes, layer.roots[q]?.getD 0) := by
  obtain ⟨root, hroot, hrootBound⟩ :=
    layerRoot_getElem? hreferences hq
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode
  rw [Bool.and_eq_true]
  refine ⟨by simpa [hroot] using decide_eq_true hrootBound, ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  have hnodeValid := hvalid node hnode
  cases node with
  | inl x =>
      exact decide_eq_true hnodeValid
  | inr app =>
      rcases app with ⟨X, children⟩
      simp only at hnodeValid
      simp only [RegularTerm.nodeWellFormedCode, RegularTerm.nodes]
      rw [hnodeValid.1]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨trivial, ?_⟩
      apply List.all_eq_true.mpr
      intro child hchild
      exact decide_eq_true (hnodeValid.2 child hchild)

public theorem stackSchema_wellFormed
    (machine : EncodedDPDA Action) (domain : List ℕ)
    {q : ℕ} (hq : q < machine.numStates)
    {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    (stackSchema machine domain q stack).WellFormed
      (grammarRanks machine) domain.length := by
  unfold stackSchema
  exact termWellFormed_of_layer
    (stackLayer_references machine domain stack)
    (stackLayer_nodesValid machine domain hstack) hq

public theorem stackSchema_unfoldsFiniteCode
    (machine : EncodedDPDA Action) (domain : List ℕ)
    {q : ℕ} (hq : q < machine.numStates)
    (stack : List ℕ) :
    (stackSchema machine domain q stack).unfoldsFiniteCode = true := by
  unfold stackSchema
  have hreferences := stackLayer_references machine domain stack
  obtain ⟨root, hroot, hrootBound⟩ :=
    layerRoot_getElem? hreferences hq
  apply unfoldsFiniteCode_eq_true_of_backward
  · simpa [hroot] using hrootBound
  · exact stackLayer_backward machine domain stack

private theorem ruleForKey_wellFormedCode
    (machine : EncodedDPDA Action) {key : InputKey Action}
    (hkey : key ∈ DPDAToFirstOrder.inputKeys machine)
    {rule : RawRule Action}
    (hrule : ruleForKey machine key = some rule) :
    (grammar machine).ruleWellFormedCode rule = true := by
  obtain ⟨hq, hZ⟩ := DPDAToFirstOrder.inputKey_bounds machine hkey
  unfold ruleForKey at hrule
  cases hepsilon :
      DPDAToFirstOrder.Machine.epsilonStep?
        machine key.1 key.2.2 with
  | some out => simp [hepsilon] at hrule
  | none =>
      simp only [hepsilon] at hrule
      cases hinput :
          DPDAToFirstOrder.Machine.inputStep?
            machine key.1 key.2.1 key.2.2 with
      | none => simp [hinput] at hrule
      | some out =>
          rcases out with ⟨target, replacement⟩
          simp only [hinput, Option.map_some,
            Option.some.injEq] at hrule
          subst rule
          have htarget : target < machine.numStates :=
            DPDAToFirstOrder.Machine.inputStep?_target_lt hinput
          have hreplacement : ∀ symbol ∈ replacement,
              symbol < machine.numStackSymbols :=
            DPDAToFirstOrder.Machine.inputStep?_replacement_lt hinput
          unfold EncodedFirstOrderGrammar.ruleWellFormedCode
          change (match (grammarRanks machine)[
              headSymbol machine key.1 key.2.2]? with
            | none => false
            | some rank =>
                (stackSchema machine
                    (headTargets machine key.1 key.2.2)
                    target replacement).wellFormedCode
                      (grammarRanks machine) rank &&
                  (stackSchema machine
                    (headTargets machine key.1 key.2.2)
                    target replacement).unfoldsFiniteCode) = true
          rw [grammarRanks_headSymbol machine hq hZ]
          rw [Bool.and_eq_true]
          exact ⟨stackSchema_wellFormed machine
              (headTargets machine key.1 key.2.2)
              htarget hreplacement,
            stackSchema_unfoldsFiniteCode machine
              (headTargets machine key.1 key.2.2)
              htarget replacement⟩

omit [Fintype Action] in
private theorem ruleForKey_some_key
    {machine : EncodedDPDA Action} {key : InputKey Action}
    {rule : RawRule Action}
    (hrule : ruleForKey machine key = some rule) :
    rule.lhs = headSymbol machine key.1 key.2.2 ∧
      rule.action = key.2.1 := by
  unfold ruleForKey at hrule
  cases hepsilon :
      DPDAToFirstOrder.Machine.epsilonStep?
        machine key.1 key.2.2 with
  | some out => simp [hepsilon] at hrule
  | none =>
      simp only [hepsilon] at hrule
      cases hinput :
          DPDAToFirstOrder.Machine.inputStep?
            machine key.1 key.2.1 key.2.2 with
      | none => simp [hinput] at hrule
      | some out =>
          simp only [hinput, Option.map_some,
            Option.some.injEq] at hrule
          subst rule
          exact ⟨rfl, rfl⟩

omit [Fintype Action] in
private theorem compiled_rule_key_injective
    {machine : EncodedDPDA Action}
    {key₁ key₂ : InputKey Action}
    (hkey₁ : key₁ ∈ DPDAToFirstOrder.inputKeys machine)
    (hkey₂ : key₂ ∈ DPDAToFirstOrder.inputKeys machine)
    {rule₁ rule₂ : RawRule Action}
    (hrule₁ : ruleForKey machine key₁ = some rule₁)
    (hrule₂ : ruleForKey machine key₂ = some rule₂)
    (hlhs : rule₁.lhs = rule₂.lhs)
    (haction : rule₁.action = rule₂.action) :
    key₁ = key₂ := by
  obtain ⟨hq₁, hZ₁⟩ :=
    DPDAToFirstOrder.inputKey_bounds machine hkey₁
  obtain ⟨hq₂, hZ₂⟩ :=
    DPDAToFirstOrder.inputKey_bounds machine hkey₂
  have hcompiled₁ := ruleForKey_some_key hrule₁
  have hcompiled₂ := ruleForKey_some_key hrule₂
  have hhead : headSymbol machine key₁.1 key₁.2.2 =
      headSymbol machine key₂.1 key₂.2.2 := by
    rw [← hcompiled₁.1, ← hcompiled₂.1]
    exact hlhs
  obtain ⟨hq, hZ⟩ :=
    DPDAToFirstOrder.headSymbol_injective_on_bounds machine
      hq₁ hq₂ hZ₁ hZ₂ hhead
  have ha : key₁.2.1 = key₂.2.1 := by
    rw [← hcompiled₁.2, ← hcompiled₂.2]
    exact haction
  rcases key₁ with ⟨q₁, action₁, Z₁⟩
  rcases key₂ with ⟨q₂, action₂, Z₂⟩
  simp only at hq hZ ha
  subst q₂
  subst action₂
  subst Z₂
  rfl

private theorem compiledRules_actionDeterministicCode
    (machine : EncodedDPDA Action) :
    ∀ keys : List (InputKey Action),
    (∀ key ∈ keys, key ∈ DPDAToFirstOrder.inputKeys machine) →
    keys.Nodup →
    EncodedFirstOrderGrammar.actionDeterministicRulesCode
      (keys.filterMap (ruleForKey machine)) = true := by
  intro keys
  induction keys with
  | nil =>
      simp [EncodedFirstOrderGrammar.actionDeterministicRulesCode]
  | cons key keys ih =>
      intro hsubset hnodup
      have hkey : key ∈ DPDAToFirstOrder.inputKeys machine :=
        hsubset key (by simp)
      have htail :
          ∀ key' ∈ keys,
            key' ∈ DPDAToFirstOrder.inputKeys machine := by
        intro key' hkey'
        exact hsubset key' (by simp [hkey'])
      have hnodupParts := List.nodup_cons.mp hnodup
      cases hcompiled : ruleForKey machine key with
      | none =>
          simp only [List.filterMap_cons, hcompiled]
          exact ih htail hnodupParts.2
      | some rule =>
          simp only [List.filterMap_cons, hcompiled,
            EncodedFirstOrderGrammar.actionDeterministicRulesCode,
            Bool.and_eq_true]
          refine ⟨?_, ih htail hnodupParts.2⟩
          apply List.all_eq_true.mpr
          intro other hother
          rw [List.mem_filterMap] at hother
          obtain ⟨otherKey, hotherKey, hotherCompiled⟩ := hother
          apply decide_eq_true
          by_contra hsame
          push_neg at hsame
          have hkeysEqual := compiled_rule_key_injective hkey
            (htail otherKey hotherKey) hcompiled hotherCompiled
            hsame.1 hsame.2
          exact hnodupParts.1 (hkeysEqual ▸ hotherKey)

public theorem grammar_rulesWellFormedCode
    (machine : EncodedDPDA Action) :
    (grammar machine).rawRules.all
      (grammar machine).ruleWellFormedCode = true := by
  apply List.all_eq_true.mpr
  intro rule hrule
  change rule ∈
    (DPDAToFirstOrder.inputKeys machine).filterMap
      (ruleForKey machine) at hrule
  rw [List.mem_filterMap] at hrule
  obtain ⟨key, hkey, hcompiled⟩ := hrule
  exact ruleForKey_wellFormedCode machine hkey hcompiled

public theorem grammar_actionDeterministicCode
    (machine : EncodedDPDA Action) :
    (grammar machine).actionDeterministicCode = true := by
  unfold EncodedFirstOrderGrammar.actionDeterministicCode grammar
  apply compiledRules_actionDeterministicCode machine
    (DPDAToFirstOrder.inputKeys machine)
  · intro key hkey
    exact hkey
  · unfold DPDAToFirstOrder.inputKeys
    exact List.nodup_dedup _

/-- The compressed translation is a finite ranked deterministic grammar. -/
public theorem grammar_wellFormed
    (machine : EncodedDPDA Action) :
    (grammar machine).WellFormed := by
  unfold EncodedFirstOrderGrammar.WellFormed
    EncodedFirstOrderGrammar.wellFormedCode
  rw [Bool.and_eq_true]
  exact ⟨grammar_rulesWellFormedCode machine,
    grammar_actionDeterministicCode machine⟩

private theorem grammar_rule_unique
    {machine : EncodedDPDA Action} {left right : RawRule Action}
    (hleft : left ∈ (grammar machine).rawRules)
    (hright : right ∈ (grammar machine).rawRules)
    (hlhs : left.lhs = right.lhs)
    (haction : left.action = right.action) :
    left = right := by
  change left ∈
    (DPDAToFirstOrder.inputKeys machine).filterMap
      (ruleForKey machine) at hleft
  change right ∈
    (DPDAToFirstOrder.inputKeys machine).filterMap
      (ruleForKey machine) at hright
  rw [List.mem_filterMap] at hleft hright
  obtain ⟨leftKey, hleftKey, hleftCompiled⟩ := hleft
  obtain ⟨rightKey, hrightKey, hrightCompiled⟩ := hright
  have hkeys := compiled_rule_key_injective
    hleftKey hrightKey hleftCompiled hrightCompiled hlhs haction
  subst rightKey
  rw [hleftCompiled] at hrightCompiled
  exact Option.some.inj hrightCompiled

/-- Exact compressed rule selected for one stable input transition. -/
public theorem grammar_ruleLookup_of_inputStep?
    (machine : EncodedDPDA Action) {q Z : ℕ} {action : Action}
    {target : ℕ} {replacement : List ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none)
    (hinput :
      DPDAToFirstOrder.Machine.inputStep? machine q action Z =
        some (target, replacement)) :
    (grammar machine).ruleLookup
        (headSymbol machine q Z) action =
      some (stackSchema machine (headTargets machine q Z)
        target replacement) := by
  let key : InputKey Action := (q, action, Z)
  let rule : RawRule Action :=
    (headSymbol machine q Z, action,
      stackSchema machine (headTargets machine q Z)
        target replacement)
  have hkey : key ∈ DPDAToFirstOrder.inputKeys machine :=
    DPDAToFirstOrder.inputKey_mem_of_inputStep?
      machine hq hZ hinput
  have hcompiled : ruleForKey machine key = some rule := by
    simp [ruleForKey, key, rule, hstable, hinput]
  have hruleMem : rule ∈ (grammar machine).rawRules := by
    change rule ∈
      (DPDAToFirstOrder.inputKeys machine).filterMap
        (ruleForKey machine)
    rw [List.mem_filterMap]
    exact ⟨key, hkey, hcompiled⟩
  unfold EncodedFirstOrderGrammar.ruleLookup
  cases hfind : (grammar machine).findRule
      (headSymbol machine q Z) action with
  | none =>
      unfold EncodedFirstOrderGrammar.findRule at hfind
      rw [List.find?_eq_none] at hfind
      have hfalse := hfind rule hruleMem
      simp [rule] at hfalse
      exact ((hfalse rfl) rfl).elim
  | some found =>
      have hfoundMem :=
        EncodedFirstOrderGrammar.findRule_mem hfind
      have hfoundKey :=
        EncodedFirstOrderGrammar.findRule_key hfind
      have hfoundEq := grammar_rule_unique hfoundMem hruleMem
        hfoundKey.1 (hfoundKey.2.trans rfl)
      subst found
      rfl

/-! ## Machine witnesses behind every compressed successor -/

omit [Fintype Action] in
public theorem successor_symbol_lt_bottom
    (machine : EncodedDPDA Action)
    (position : (grammar machine).SuccessorPosition) :
    position.1.val < bottomSymbol machine := by
  have hsymbolBound : position.1.val <
      (grammarRanks machine).length := by
    have hbound := position.1.isLt
    change position.1.val < (grammarRanks machine).length at hbound
    exact hbound
  have hle : position.1.val ≤ bottomSymbol machine := by
    have hlength :
        (grammarRanks machine).length =
          bottomSymbol machine + 1 := by
      simp [grammarRanks]
    omega
  by_contra hnot
  have heq : position.1.val = bottomSymbol machine := by
    omega
  have hpositionLookup :
      (grammarRanks machine)[position.1.val]? =
        some ((grammarRanks machine).get
          ⟨position.1.val, hsymbolBound⟩) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨hsymbolBound, rfl⟩
  have hrankZero :
      (grammarRanks machine).get
        ⟨position.1.val, hsymbolBound⟩ = 0 := by
    have hbottom := grammarRanks_bottomSymbol machine
    have hpositionLookup' :
        (grammarRanks machine)[bottomSymbol machine]? =
          some ((grammarRanks machine).get
            ⟨position.1.val, hsymbolBound⟩) := by
      simpa only [heq] using hpositionLookup
    exact Option.some.inj
      (hpositionLookup'.symm.trans hbottom)
  have hpositionRank :
      (grammar machine).ranks.get position.1 =
        (grammarRanks machine).get
          ⟨position.1.val, hsymbolBound⟩ := by
    rfl
  have hi := position.2.isLt
  have hrankEq :
      (grammar machine).ranks.get position.1 = 0 :=
    hpositionRank.trans hrankZero
  omega

/-- Decoded machine data and an actual input word for one formal successor of
the compressed grammar. -/
public structure SuccessorReturnWitness
    (machine : EncodedDPDA Action)
    (position : (grammar machine).SuccessorPosition) where
  state : ℕ
  stackSymbol : ℕ
  target : ℕ
  state_lt : state < machine.numStates
  stackSymbol_lt : stackSymbol < machine.numStackSymbols
  symbol_eq :
    position.1.val = headSymbol machine state stackSymbol
  target_get :
    (headTargets machine state stackSymbol)[position.2.val]? =
      some target
  target_idxOf :
    (headTargets machine state stackSymbol).idxOf target =
      position.2.val
  stable :
    DPDAToFirstOrder.Machine.epsilonStep?
      machine state stackSymbol = none
  target_lt : target < machine.numStates
  returns :
    DPDAObservableReturns.RawHeadReturns
      machine state stackSymbol target
  word : List Action
  reaches :
    @PDA.Reaches _ _ _ _ _ _ machine.toDPDA.toPDA
      (machine.decodeRawConf (state, [stackSymbol]) word)
      (machine.decodeRawConf (target, []) [])

public theorem successorReturnWitness_nonempty
    (machine : EncodedDPDA Action)
    (position : (grammar machine).SuccessorPosition) :
    Nonempty (SuccessorReturnWitness machine position) := by
  let X := position.1.val
  let q := X / machine.numStackSymbols
  let Z := X % machine.numStackSymbols
  have hX : X < bottomSymbol machine := by
    exact successor_symbol_lt_bottom machine position
  have hZ : Z < machine.numStackSymbols := by
    exact Nat.mod_lt X machine.numStackSymbols_pos
  have hq : q < machine.numStates := by
    apply (Nat.div_lt_iff_lt_mul machine.numStackSymbols_pos).mpr
    simpa [X, bottomSymbol, DPDAToFirstOrder.bottomSymbol,
      Nat.mul_comm] using hX
  have hsymbol : X = headSymbol machine q Z := by
    unfold X q Z headSymbol DPDAToFirstOrder.headSymbol
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod position.1.val
      machine.numStackSymbols).symm
  have hsymbolBound : X < (grammarRanks machine).length := by
    have hlength :
        (grammarRanks machine).length =
          bottomSymbol machine + 1 := by
      simp [grammarRanks]
    omega
  have hpositionLookup :
      (grammarRanks machine)[X]? =
        some ((grammarRanks machine).get
          ⟨X, hsymbolBound⟩) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨hsymbolBound, rfl⟩
  have hrankLookup :
      (grammarRanks machine)[X]? =
        some (headTargets machine q Z).length := by
    rw [hsymbol]
    exact grammarRanks_headSymbol machine hq hZ
  have hrank :
      (grammar machine).ranks.get position.1 =
        (headTargets machine q Z).length := by
    have hget :
        (grammar machine).ranks.get position.1 =
          (grammarRanks machine).get
            ⟨X, hsymbolBound⟩ := by
      rfl
    rw [hget]
    exact Option.some.inj
      (hpositionLookup.symm.trans hrankLookup)
  have hi : position.2.val <
      (headTargets machine q Z).length := by
    have hi' := position.2.isLt
    omega
  let target := (headTargets machine q Z)[position.2.val]'hi
  have htargetGet :
      (headTargets machine q Z)[position.2.val]? =
        some target := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨hi, rfl⟩
  have htargetMem : target ∈ headTargets machine q Z :=
    List.getElem_mem hi
  have hmeaning :=
    (DPDAObservableReturns.mem_exposedTargets_iff
      machine q Z target).mp htargetMem
  have hidx :
      (headTargets machine q Z).idxOf target =
        position.2.val := by
    let index : Fin (headTargets machine q Z).length :=
      ⟨position.2.val, hi⟩
    have hnodup :
        (headTargets machine q Z).Nodup :=
      DPDAObservableReturns.exposedTargets_nodup machine q Z
    have hindex := List.get_idxOf hnodup index
    simpa [target, index, List.get_eq_getElem] using hindex
  have hcode :
      DPDAObservableReturns.headReturnsCode
        machine q Z target = true :=
    (DPDAObservableReturns.headReturnsCode_eq_true_iff
      machine q Z target).mpr hmeaning.2.2
  obtain ⟨word, hreach⟩ :=
    DPDAObservableReturns.exists_word_reaches_of_headReturnsCode
      machine hcode
  refine ⟨
    { state := q
      stackSymbol := Z
      target := target
      state_lt := hq
      stackSymbol_lt := hZ
      symbol_eq := ?_
      target_get := htargetGet
      target_idxOf := hidx
      stable := hmeaning.1
      target_lt := hmeaning.2.1
      returns := hmeaning.2.2
      word := word
      reaches := ?_ }⟩
  · simpa [X] using hsymbol
  · simpa [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hZ,
      Nat.mod_eq_of_lt hmeaning.2.1] using hreach

noncomputable def successorReturnWitness
    (machine : EncodedDPDA Action)
    (position : (grammar machine).SuccessorPosition) :
    SuccessorReturnWitness machine position :=
  Classical.choice (successorReturnWitness_nonempty machine position)

/-! ## Return-domain closure for compressed right-hand sides -/

public theorem toDPDA_epsilonTransition_of_epsilonStep?
    (machine : EncodedDPDA Action) {q Z target : ℕ}
    {replacement : List ℕ}
    (hstep :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z =
        some (target, replacement)) :
    machine.toDPDA.epsilon_transition
        (machine.state q) (machine.stackSymbol Z) =
      some (machine.state target,
        machine.replacement replacement) := by
  unfold DPDAToFirstOrder.Machine.epsilonStep? at hstep
  obtain ⟨out, hlookup, hout⟩ :=
    Option.map_eq_some_iff.mp hstep
  have hstate : machine.state out.1.val = out.1 := by
    apply Fin.ext
    simp [EncodedDPDA.state, Nat.mod_eq_of_lt out.1.isLt]
  have hreplacement :
      machine.replacement (out.2.map Fin.val) = out.2 := by
    simp [EncodedDPDA.replacement, List.map_map,
      Function.comp_def, EncodedDPDA.stackSymbol,
      Nat.mod_eq_of_lt]
  have houtEq :
      (machine.state target, machine.replacement replacement) =
        out := by
    have htarget : out.1.val = target := by
      simpa using congrArg Prod.fst hout
    have hrepl : out.2.map Fin.val = replacement := by
      simpa using congrArg Prod.snd hout
    rw [← htarget, ← hrepl, hstate, hreplacement]
  change machine.epsilonLookup
      (machine.state q) (machine.stackSymbol Z) = _
  rw [hlookup]
  exact congrArg some houtEq.symm

public theorem toDPDA_inputTransition_of_inputStep?
    (machine : EncodedDPDA Action) {q Z target : ℕ}
    {action : Action} {replacement : List ℕ}
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none)
    (hstep :
      DPDAToFirstOrder.Machine.inputStep? machine q action Z =
        some (target, replacement)) :
    machine.toDPDA.transition
        (machine.state q) action (machine.stackSymbol Z) =
      some (machine.state target,
        machine.replacement replacement) := by
  unfold DPDAToFirstOrder.Machine.inputStep? at hstep
  obtain ⟨out, hlookup, hout⟩ :=
    Option.map_eq_some_iff.mp hstep
  have hepsilon :
      machine.epsilonLookup
        (machine.state q) (machine.stackSymbol Z) = none := by
    unfold DPDAToFirstOrder.Machine.epsilonStep? at hstable
    cases hlookupEpsilon :
        machine.epsilonLookup
          (machine.state q) (machine.stackSymbol Z) with
    | none => rfl
    | some out =>
        simp [hlookupEpsilon] at hstable
  have hstate : machine.state out.1.val = out.1 := by
    apply Fin.ext
    simp [EncodedDPDA.state, Nat.mod_eq_of_lt out.1.isLt]
  have hreplacement :
      machine.replacement (out.2.map Fin.val) = out.2 := by
    simp [EncodedDPDA.replacement, List.map_map,
      Function.comp_def, EncodedDPDA.stackSymbol,
      Nat.mod_eq_of_lt]
  have houtEq :
      (machine.state target, machine.replacement replacement) =
        out := by
    have htarget : out.1.val = target := by
      simpa using congrArg Prod.fst hout
    have hrepl : out.2.map Fin.val = replacement := by
      simpa using congrArg Prod.snd hout
    rw [← htarget, ← hrepl, hstate, hreplacement]
  change (if (machine.epsilonLookup
      (machine.state q) (machine.stackSymbol Z)).isSome then none
    else machine.inputLookup
      (machine.state q) action (machine.stackSymbol Z)) = _
  rw [hepsilon]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false]
  rw [hlookup]
  exact congrArg some houtEq.symm

public theorem rawErasedReaches_of_epsilonStep?
    (machine : EncodedDPDA Action) {q Z target : ℕ}
    {replacement suffix : List ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (hstep :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z =
        some (target, replacement))
    (hreplacement : replacement = []) :
    machine.RawErasedReaches
      (q, Z :: suffix) (target, suffix) := by
  have htarget : target < machine.numStates :=
    DPDAToFirstOrder.Machine.epsilonStep?_target_lt hstep
  have htransition :=
    toDPDA_epsilonTransition_of_epsilonStep? machine hstep
  subst replacement
  have hreach₁ :
      @PDA.Reaches₁ _ _ _ _ _ _ machine.toDPDA.toPDA
        (machine.decodeRawConf (q, Z :: suffix) [])
        (machine.decodeRawConf (target, suffix) []) := by
    simp [EncodedDPDA.decodeRawConf, EncodedDPDA.replacement,
      PDA.Reaches₁, PDA.step, DPDA.toPDA, htransition,
      List.map_append]
  apply machine.rawErasedReaches_of_reaches
      (x := (q, Z :: suffix)) (y := (target, suffix))
      (w := [])
  · exact ⟨hq, by
      intro symbol hsymbol
      simp only [List.mem_cons] at hsymbol
      rcases hsymbol with rfl | hsymbol
      · exact hZ
      · exact hsuffix symbol hsymbol⟩
  · exact ⟨htarget, hsuffix⟩
  · exact Relation.ReflTransGen.single hreach₁

public theorem rawErasedReaches_of_inputStep?
    (machine : EncodedDPDA Action) {q Z target : ℕ}
    {action : Action} {replacement suffix : List ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none)
    (hstep :
      DPDAToFirstOrder.Machine.inputStep? machine q action Z =
        some (target, replacement)) :
    machine.RawErasedReaches
      (q, Z :: suffix) (target, replacement ++ suffix) := by
  have htarget : target < machine.numStates :=
    DPDAToFirstOrder.Machine.inputStep?_target_lt hstep
  have hreplacement : ∀ symbol ∈ replacement,
      symbol < machine.numStackSymbols :=
    DPDAToFirstOrder.Machine.inputStep?_replacement_lt hstep
  have htransition :=
    toDPDA_inputTransition_of_inputStep? machine hstable hstep
  have hreach₁ :
      @PDA.Reaches₁ _ _ _ _ _ _ machine.toDPDA.toPDA
        (machine.decodeRawConf (q, Z :: suffix) [action])
        (machine.decodeRawConf
          (target, replacement ++ suffix) []) := by
    simp [EncodedDPDA.decodeRawConf, EncodedDPDA.replacement,
      PDA.Reaches₁, PDA.step, DPDA.toPDA, htransition,
      List.map_append]
  apply machine.rawErasedReaches_of_reaches
      (x := (q, Z :: suffix))
      (y := (target, replacement ++ suffix))
      (w := [action])
  · exact ⟨hq, by
      intro symbol hsymbol
      simp only [List.mem_cons] at hsymbol
      rcases hsymbol with rfl | hsymbol
      · exact hZ
      · exact hsuffix symbol hsymbol⟩
  · refine ⟨htarget, ?_⟩
    intro symbol hsymbol
    rw [List.mem_append] at hsymbol
    rcases hsymbol with hsymbol | hsymbol
    · exact hreplacement symbol hsymbol
    · exact hsuffix symbol hsymbol
  · exact Relation.ReflTransGen.single hreach₁

/-- Every bounded control reachable after completely popping a stack prefix is
retained by `domain`. -/
@[expose] public def ReturnClosed
    (machine : EncodedDPDA Action) (domain : List ℕ)
    (q : ℕ) (stack : List ℕ) : Prop :=
  ∀ target, target < machine.numStates →
    machine.RawErasedReaches (q, stack) (target, []) →
      target ∈ domain

public theorem rawHeadReturns_of_rawErasedReaches
    (machine : EncodedDPDA Action) {q Z target : ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (htarget : target < machine.numStates)
    (hreach :
      machine.RawErasedReaches (q, [Z]) (target, [])) :
    DPDAObservableReturns.RawHeadReturns
      machine q Z target := by
  unfold DPDAObservableReturns.RawHeadReturns
  apply (DPDAObservableReturns.targetMachine_rawErasedReaches_iff
    machine target _ _).mpr
  simpa [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hZ,
    Nat.mod_eq_of_lt htarget] using hreach

public theorem rawErasedReaches_of_rawHeadReturns
    (machine : EncodedDPDA Action) {q Z target : ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (htarget : target < machine.numStates)
    (hreturn :
      DPDAObservableReturns.RawHeadReturns
        machine q Z target) :
    machine.RawErasedReaches (q, [Z]) (target, []) := by
  unfold DPDAObservableReturns.RawHeadReturns at hreturn
  have hreach :=
    (DPDAObservableReturns.targetMachine_rawErasedReaches_iff
      machine target _ _).mp hreturn
  simpa [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hZ,
    Nat.mod_eq_of_lt htarget] using hreach

public theorem headTargets_returnClosed
    (machine : EncodedDPDA Action) {q Z : ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none) :
    ReturnClosed machine (headTargets machine q Z) q [Z] := by
  intro target htarget hreach
  apply (DPDAObservableReturns.mem_exposedTargets_iff
    machine q Z target).mpr
  exact ⟨hstable, htarget,
    rawHeadReturns_of_rawErasedReaches machine
      hq hZ htarget hreach⟩

public theorem ReturnClosed.after_input
    {machine : EncodedDPDA Action} {q Z target : ℕ}
    {action : Action} {replacement : List ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none)
    (hinput :
      DPDAToFirstOrder.Machine.inputStep? machine q action Z =
        some (target, replacement)) :
    ReturnClosed machine (headTargets machine q Z)
      target replacement := by
  intro returned hreturned hrest
  have hfirst :=
    rawErasedReaches_of_inputStep? machine hq hZ
      (suffix := []) (by simp) hstable hinput
  have hwhole : machine.RawErasedReaches
      (q, [Z]) (returned, []) :=
    Relation.ReflTransGen.trans hfirst (by simpa using hrest)
  exact headTargets_returnClosed machine hq hZ hstable
    returned hreturned hwhole

public theorem ReturnClosed.after_retained_head
    {machine : EncodedDPDA Action} {domain : List ℕ}
    {q Z returned : ℕ} {stack : List ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hclosed : ReturnClosed machine domain q (Z :: stack))
    (hreturned : returned ∈ headTargets machine q Z) :
    ReturnClosed machine domain returned stack := by
  have hmeaning :=
    (DPDAObservableReturns.mem_exposedTargets_iff
      machine q Z returned).mp hreturned
  have hhead :=
    rawErasedReaches_of_rawHeadReturns machine
      hq hZ hmeaning.2.1 hmeaning.2.2
  have hheadSuffix :=
    DPDANormalization.Popping.rawErasedReaches_suffix
      hhead stack
  intro target htarget hrest
  apply hclosed target htarget
  exact Relation.ReflTransGen.trans
    (by simpa using hheadSuffix) hrest

public theorem ReturnClosed.after_epsilon
    {machine : EncodedDPDA Action} {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {domain : List ℕ} {q Z target : ℕ} {stack : List ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    (hclosed : ReturnClosed machine domain q (Z :: stack))
    {replacement : List ℕ}
    (hstep :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z =
        some (target, replacement)) :
    ReturnClosed machine domain target stack := by
  have hreplacement :
      replacement = [] :=
    DPDAToFirstOrder.Machine.epsilonStep?_replacement_eq_nil_of_poppingComplete
      hnormal hstep
  have hfirst :=
    rawErasedReaches_of_epsilonStep? machine hq hZ hstack
      hstep hreplacement
  intro returned hreturned hrest
  exact hclosed returned hreturned
    (Relation.ReflTransGen.trans hfirst hrest)

private theorem selectRoots_schemaBaseLayer
    (machine : EncodedDPDA Action) {domain : List ℕ}
    (hnodup : domain.Nodup)
    (hbound : ∀ target ∈ domain, target < machine.numStates) :
    selectRoots domain (schemaBaseLayer machine domain).roots =
      List.range domain.length := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < domain.length
  · let target := domain[i]'hi
    have htargetMem : target ∈ domain := List.getElem_mem hi
    have htargetBound := hbound target htargetMem
    have htargetLookup : domain[i]? = some target := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨hi, rfl⟩
    have hidx : domain.idxOf target = i := by
      let index : Fin domain.length := ⟨i, hi⟩
      have hindex := List.get_idxOf hnodup index
      simpa [target, index, List.get_eq_getElem] using hindex
    simp [selectRoots, schemaBaseLayer, htargetLookup,
      htargetBound, hidx, List.getElem?_range hi]
  · have hleft : (selectRoots domain
        (schemaBaseLayer machine domain).roots)[i]? = none := by
      rw [List.getElem?_eq_none]
      simpa [selectRoots] using Nat.le_of_not_gt hi
    have hright : (List.range domain.length)[i]? = none :=
      List.getElem?_eq_none (by simpa using hi)
    rw [hleft, hright]

public theorem stackSchema_rootApplication?_of_stable
    (machine : EncodedDPDA Action) (domain : List ℕ)
    {q Z : ℕ} (hq : q < machine.numStates)
    (stack : List ℕ)
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none) :
    (stackSchema machine domain q (Z :: stack)).rootApplication? =
      some (headSymbol machine q Z,
        selectRoots (headTargets machine q Z)
          (stackLayer machine domain stack).roots) := by
  let layer := stackLayer machine domain stack
  have hqRange : (List.range machine.numStates)[q]? = some q := by
    simp [hq]
  have hroot :
      (extendLayer machine Z layer).roots[q]? =
        some (layer.nodes.length + q) := by
    simp [extendLayer, List.getElem?_map, hqRange, hstable]
  have hrootBound : layer.nodes.length + q <
      (extendLayer machine Z layer).nodes.length := by
    rw [extendLayer_nodes_length]
    omega
  dsimp [layer] at hroot hrootBound
  unfold stackSchema
  rw [stackLayer_cons]
  change RegularTerm.rootApplication?
      ((extendLayer machine Z
        (stackLayer machine domain stack)).nodes,
        (extendLayer machine Z
          (stackLayer machine domain stack)).roots[q]?.getD 0) =
    _
  unfold RegularTerm.rootApplication? RegularTerm.rootNode?
    RegularTerm.nodeAt? RegularTerm.root RegularTerm.nodes
  rw [hroot]
  simp only [Option.getD_some]
  simp only [extendLayer]
  rw [List.getElem?_append_right (by omega)]
  simp [List.getElem?_map, hqRange, hstable, layer]

public theorem stackSchema_nil_rootNode?_of_mem
    (machine : EncodedDPDA Action) {domain : List ℕ}
    {q : ℕ} (hq : q < machine.numStates)
    (hqDomain : q ∈ domain) :
    (stackSchema machine domain q []).rootNode? =
      some (.inl (domain.idxOf q) : RawNode) := by
  have hidx : domain.idxOf q < domain.length :=
    List.idxOf_lt_length_iff.mpr hqDomain
  have hqRange : (List.range machine.numStates)[q]? = some q := by
    simp [hq]
  have hroot :
      (schemaBaseLayer machine domain).roots[q]? =
        some (domain.idxOf q) := by
    simp [schemaBaseLayer, List.getElem?_map, hqRange]
  unfold stackSchema
  rw [stackLayer_nil]
  change RegularTerm.rootNode?
      ((schemaBaseLayer machine domain).nodes,
        (schemaBaseLayer machine domain).roots[q]?.getD 0) =
    _
  unfold RegularTerm.rootNode? RegularTerm.nodeAt?
    RegularTerm.root RegularTerm.nodes
  rw [hroot]
  simp only [Option.getD_some, schemaBaseLayer]
  rw [List.getElem?_append_left (by simpa using hidx)]
  simp [List.getElem?_map, List.getElem?_range hidx]

private theorem nodeAt?_root_of_rootApplication?
    {term : RegularTerm} {X : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (X, children)) :
    term.nodeAt? term.root =
      some (Sum.inr (X, children) : RawNode) := by
  unfold RegularTerm.rootApplication? at hroot
  cases hnode : term.rootNode? with
  | none => simp [hnode] at hroot
  | some node =>
      cases hkind : node with
      | inl x => simp [hnode, hkind] at hroot
      | inr application =>
          rcases application with ⟨Y, targetChildren⟩
          simp only [hnode, hkind, Option.some.injEq,
            Prod.mk.injEq] at hroot
          rcases hroot with ⟨rfl, rfl⟩
          simpa [RegularTerm.rootNode?, hkind] using hnode

private theorem stackSchema_singleton_variableNode
    (machine : EncodedDPDA Action) (domain : List ℕ)
    (q Z i : ℕ) (hi : i < domain.length) :
    (stackSchema machine domain q [Z]).nodeAt? i =
      some (.inl i : RawNode) := by
  unfold stackSchema RegularTerm.nodeAt? RegularTerm.nodes
  rw [stackLayer_cons]
  simp only [stackLayer_nil, extendLayer]
  rw [List.getElem?_append_left]
  · simp only [schemaBaseLayer]
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [List.getElem?_map, List.getElem?_range hi]
  · simp [schemaBaseLayer]
    omega

public theorem stackSchema_nil_unfoldingEquivalent_variable
    (machine : EncodedDPDA Action) {domain : List ℕ}
    {q : ℕ} (hq : q < machine.numStates)
    (hqDomain : q ∈ domain) :
    (stackSchema machine domain q []).UnfoldingEquivalent
      (RegularTerm.variableTerm (domain.idxOf q)) := by
  let left := stackSchema machine domain q []
  let right := RegularTerm.variableTerm (domain.idxOf q)
  let R : ℕ → ℕ → Prop :=
    fun i j => i = left.root ∧ j = right.root
  refine ⟨R, ⟨rfl, rfl⟩, ?_⟩
  intro i j hij
  rcases hij with ⟨rfl, rfl⟩
  unfold RegularTerm.NodeCompatible
  have hleftRoot :
      left.nodeAt? left.root =
        some (.inl (domain.idxOf q) : RawNode) := by
    have hroot :=
      stackSchema_nil_rootNode?_of_mem machine hq hqDomain
    simpa [left, RegularTerm.rootNode?] using hroot
  rw [hleftRoot]
  simp [right, RegularTerm.variableTerm,
    RegularTerm.nodeAt?, RegularTerm.nodes, RegularTerm.root,
    RegularTerm.RawCompatible]

public theorem stackSchema_singleton_unfoldingEquivalent_symbolTemplate
    (machine : EncodedDPDA Action) {q Z : ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none) :
    RegularTerm.UnfoldingEquivalent
      (stackSchema machine (headTargets machine q Z) q [Z])
      (RegularTerm.symbolTemplate
        (headSymbol machine q Z)
        (headTargets machine q Z).length) := by
  let domain := headTargets machine q Z
  let left := stackSchema machine domain q [Z]
  let right := RegularTerm.symbolTemplate
    (headSymbol machine q Z) domain.length
  have hdomainNodup : domain.Nodup :=
    DPDAObservableReturns.exposedTargets_nodup machine q Z
  have hdomainBound :
      ∀ target ∈ domain, target < machine.numStates := by
    intro target htarget
    exact (DPDAObservableReturns.mem_exposedTargets_iff
      machine q Z target).mp htarget |>.2.1
  have hselected :
      selectRoots domain (schemaBaseLayer machine domain).roots =
        List.range domain.length :=
    selectRoots_schemaBaseLayer machine hdomainNodup hdomainBound
  have hleftRoot :
      left.rootApplication? =
        some (headSymbol machine q Z, List.range domain.length) := by
    have hroot :=
      stackSchema_rootApplication?_of_stable machine domain
        hq [] hstable
    change selectRoots (headTargets machine q Z)
        (schemaBaseLayer machine domain).roots =
      List.range domain.length at hselected
    simp only [stackLayer_nil] at hroot
    rw [hselected] at hroot
    simpa [left] using hroot
  have hrightRoot :
      right.rootApplication? =
        some (headSymbol machine q Z,
          (List.range domain.length).map (fun i => i + 1)) := by
    simpa [right] using
      RegularTerm.symbolTemplate_rootApplication?
        (headSymbol machine q Z) domain.length
  let R : ℕ → ℕ → Prop :=
    fun i j =>
      (i = left.root ∧ j = right.root) ∨
        ∃ k, k < domain.length ∧ i = k ∧ j = k + 1
  refine ⟨R, Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro i j hij
  rcases hij with hroots | hvariables
  · rcases hroots with ⟨rfl, rfl⟩
    unfold RegularTerm.NodeCompatible
    rw [nodeAt?_root_of_rootApplication? hleftRoot,
      nodeAt?_root_of_rootApplication? hrightRoot]
    simp only [RegularTerm.RawCompatible]
    refine ⟨trivial, ?_⟩
    rw [List.forall₂_iff_get]
    refine ⟨by simp, ?_⟩
    intro k hkLeft hkRight
    simp only [List.length_range] at hkLeft
    simp [R, hkLeft]
  · rcases hvariables with ⟨k, hk, hi, hj⟩
    subst i
    subst j
    unfold RegularTerm.NodeCompatible
    have hleftNode :
        left.nodeAt? k = some (.inl k : RawNode) := by
      simpa [left, domain] using
        stackSchema_singleton_variableNode
          machine domain q Z k hk
    rw [hleftNode]
    have hrightNode :=
      RegularTerm.symbolTemplate_variableNode
        (headSymbol machine q Z) domain.length k hk
    rw [hrightNode]
    rfl

/-! ## Semantic composition of pruned stack schemas -/

private theorem appendNodes_unfoldingEquivalent
    {term : RegularTerm} (hterm : term.ReferenceClosed)
    (extra : List RawNode) :
    term.UnfoldingEquivalent (term.nodes ++ extra, term.root) := by
  let R : ℕ → ℕ → Prop := fun i j =>
    i = j ∧ i < term.nodes.length
  refine ⟨R, ⟨rfl, hterm.1⟩, ?_⟩
  intro i j hij
  rcases hij with ⟨rfl, hi⟩
  unfold RegularTerm.NodeCompatible
  have hlookup :
      (term.nodes ++ extra)[i]? = term.nodes[i]? := by
    rw [List.getElem?_append_left hi]
  change RegularTerm.RawCompatible R (term.nodeAt? i)
    ((term.nodes ++ extra)[i]?)
  rw [hlookup]
  change RegularTerm.RawCompatible R
    (term.nodeAt? i) (term.nodeAt? i)
  cases hnode : term.nodeAt? i with
  | none => trivial
  | some node =>
      cases node with
      | inl x => simp [RegularTerm.RawCompatible]
      | inr app =>
          rcases app with ⟨X, children⟩
          simp only [RegularTerm.RawCompatible]
          refine ⟨trivial, ?_⟩
          apply List.forall₂_same.mpr
          intro child hchild
          exact ⟨rfl,
            hterm.2 i X children hnode child hchild⟩

private theorem instantiateArgument_unfoldingEquivalent
    {rhs : RegularTerm} {arguments : List RegularTerm}
    {x : ℕ} {argument : RegularTerm}
    (hargument : arguments[x]? = some argument)
    (hclosed : argument.ReferenceClosed) :
    ((rhs.instantiate arguments).withRoot
      (RegularTerm.argumentOffset rhs.nodes.length arguments x +
        argument.root)).UnfoldingEquivalent argument := by
  let offset :=
    RegularTerm.argumentOffset rhs.nodes.length arguments x
  let R : ℕ → ℕ → Prop := fun i j =>
    i = offset + j ∧ j < argument.nodes.length
  refine ⟨R, ⟨rfl, hclosed.1⟩, ?_⟩
  intro i j hij
  rcases hij with ⟨rfl, hj⟩
  unfold RegularTerm.NodeCompatible
  rw [RegularTerm.withRoot_nodeAt?]
  let node : RawNode := argument.nodes[j]'hj
  have hnode : argument.nodeAt? j = some node := by
    unfold RegularTerm.nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hj, rfl⟩
  rw [RegularTerm.instantiate_nodeAt?_argument rhs arguments
    hargument hnode, hnode]
  cases hkind : node with
  | inl xvar =>
      simp [RegularTerm.shiftNode,
        RegularTerm.RawCompatible]
  | inr application =>
      rcases application with ⟨X, children⟩
      simp only [RegularTerm.shiftNode,
        RegularTerm.RawCompatible]
      refine ⟨trivial, ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_same]
      intro child hchild
      exact ⟨by simp [offset], hclosed.2 j X children
        (by simpa [hkind] using hnode)
        child hchild⟩

private theorem rawCompatible_mono
    {R S : ℕ → ℕ → Prop} {left right : Option RawNode}
    (hmono : ∀ i j, R i j → S i j)
    (hcompatible : RegularTerm.RawCompatible R left right) :
    RegularTerm.RawCompatible S left right := by
  cases left with
  | none =>
      cases right <;>
        simp_all [RegularTerm.RawCompatible]
  | some leftNode =>
      cases right with
      | none =>
          simp_all [RegularTerm.RawCompatible]
      | some rightNode =>
          cases leftNode with
          | inl leftVariable =>
              cases rightNode with
              | inl rightVariable => exact hcompatible
              | inr rightApplication =>
                  simp [RegularTerm.RawCompatible] at hcompatible
          | inr leftApplication =>
              cases rightNode with
              | inl rightVariable =>
                  simp [RegularTerm.RawCompatible] at hcompatible
              | inr rightApplication =>
                  exact ⟨hcompatible.1,
                    hcompatible.2.imp fun i j hij =>
                      hmono i j hij⟩

private theorem unfoldingEquivalent_of_rootApplications
    {left right : RegularTerm} {X : ℕ}
    {leftChildren rightChildren : List ℕ}
    (hleft :
      left.rootApplication? = some (X, leftChildren))
    (hright :
      right.rootApplication? = some (X, rightChildren))
    (hchildren : List.Forall₂
      (fun i j => left.BisimilarAt i right j)
      leftChildren rightChildren) :
    left.UnfoldingEquivalent right := by
  let R : ℕ → ℕ → Prop := fun i j =>
    (i = left.root ∧ j = right.root) ∨
      left.BisimilarAt i right j
  refine ⟨R, Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro i j hij
  rcases hij with hroots | hbisimilar
  · rcases hroots with ⟨rfl, rfl⟩
    unfold RegularTerm.NodeCompatible
    rw [nodeAt?_root_of_rootApplication? hleft,
      nodeAt?_root_of_rootApplication? hright]
    exact ⟨rfl,
      hchildren.imp fun i j hij => Or.inr hij⟩
  · obtain ⟨S, hij, hS⟩ := hbisimilar
    exact rawCompatible_mono
      (fun child target hchild =>
        Or.inr ⟨S, hchild, hS⟩)
      (hS i j hij)

private theorem instantiate_rootApplication?
    {rhs : RegularTerm} (arguments : List RegularTerm)
    {X : ℕ} {children : List ℕ}
    (hroot : rhs.rootApplication? = some (X, children)) :
    (rhs.instantiate arguments).rootApplication? =
      some (X, children.map
        (rhs.resolveRHSRef arguments)) := by
  have hrootNode := nodeAt?_root_of_rootApplication? hroot
  have hrootBound :=
    (List.getElem?_eq_some_iff.mp hrootNode).1
  have hresolved :
      rhs.resolveRHSRef arguments rhs.root = rhs.root := by
    simp [RegularTerm.resolveRHSRef, hrootNode]
  have hinstantiatedNode :
      (rhs.instantiate arguments).nodeAt? rhs.root =
        some (.inr
          (X, children.map
            (rhs.resolveRHSRef arguments))) := by
    rw [RegularTerm.instantiate_nodeAt?_rhs
      rhs arguments hrootBound, hrootNode]
    rfl
  unfold RegularTerm.rootApplication? RegularTerm.rootNode?
  change (match (rhs.instantiate arguments).nodeAt?
      (rhs.resolveRHSRef arguments rhs.root) with
    | some (.inr app) => some app
    | _ => none) = _
  rw [hresolved, hinstantiatedNode]

private def extendStack
    (machine : EncodedDPDA Action) (stack : List ℕ)
    (base : TermLayer) : TermLayer :=
  stack.reverse.foldl
    (fun layer Z => extendLayer machine Z layer) base

@[simp] private theorem extendStack_nil
    (machine : EncodedDPDA Action) (base : TermLayer) :
    extendStack machine [] base = base := rfl

private theorem extendStack_cons
    (machine : EncodedDPDA Action)
    (Z : ℕ) (stack : List ℕ) (base : TermLayer) :
    extendStack machine (Z :: stack) base =
      extendLayer machine Z
        (extendStack machine stack base) := by
  simp [extendStack, List.foldl_append]

private theorem extendStack_schemaBaseLayer
    (machine : EncodedDPDA Action)
    (domain stack : List ℕ) :
    extendStack machine stack (schemaBaseLayer machine domain) =
      stackLayer machine domain stack := rfl

private theorem stackLayer_append
    (machine : EncodedDPDA Action) (domain : List ℕ)
    (front suffix : List ℕ) :
    stackLayer machine domain (front ++ suffix) =
      extendStack machine front
        (stackLayer machine domain suffix) := by
  simp [stackLayer, extendStack, List.reverse_append,
    List.foldl_append]

@[expose] public def stackArguments
    (machine : EncodedDPDA Action)
    (globalDomain localDomain suffix : List ℕ) :
    List RegularTerm :=
  localDomain.map fun state =>
    stackSchema machine globalDomain state suffix

private theorem stackArguments_getElem?_idxOf
    (machine : EncodedDPDA Action)
    (globalDomain : List ℕ) {localDomain : List ℕ}
    (suffix : List ℕ) {state : ℕ}
    (hstate : state ∈ localDomain) :
    (stackArguments machine globalDomain localDomain suffix)[
        localDomain.idxOf state]? =
      some (stackSchema machine globalDomain state suffix) := by
  have hidx :
      localDomain.idxOf state < localDomain.length :=
    List.idxOf_lt_length_iff.mpr hstate
  have hget :
      localDomain[localDomain.idxOf state] = state := by
    exact List.getElem_idxOf hidx
  simp [stackArguments, List.getElem?_map,
    List.getElem?_eq_getElem hidx, hget]

private theorem stackArguments_referenceClosed
    (machine : EncodedDPDA Action)
    {globalDomain localDomain suffix : List ℕ}
    (hlocalBound :
      ∀ state ∈ localDomain, state < machine.numStates)
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols) :
    ∀ argument ∈
      stackArguments machine globalDomain localDomain suffix,
      argument.ReferenceClosed := by
  intro argument hargument
  obtain ⟨state, hstate, rfl⟩ :=
    List.mem_map.mp hargument
  exact RegularTerm.referenceClosed_of_wellFormed
    (stackSchema_wellFormed machine globalDomain
      (hlocalBound state hstate) hsuffix)

private theorem schemaBaseLayerInstantiation_unfoldingEquivalent
    (machine : EncodedDPDA Action)
    {globalDomain localDomain suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    {q : ℕ} (hq : q < machine.numStates)
    (hqLocal : q ∈ localDomain)
    (schemaExtra targetExtra : List RawNode) :
    RegularTerm.UnfoldingEquivalent
      (RegularTerm.instantiate
        (((schemaBaseLayer machine localDomain).nodes ++ schemaExtra,
          (schemaBaseLayer machine localDomain).roots[q]?.getD 0) :
          RegularTerm)
        (stackArguments machine globalDomain localDomain suffix))
      (((stackLayer machine globalDomain suffix).nodes ++ targetExtra,
        (stackLayer machine globalDomain suffix).roots[q]?.getD 0) :
        RegularTerm) := by
  let rhs : RegularTerm :=
    ((schemaBaseLayer machine localDomain).nodes ++ schemaExtra,
      (schemaBaseLayer machine localDomain).roots[q]?.getD 0)
  let argument :=
    stackSchema machine globalDomain q suffix
  let arguments :=
    stackArguments machine globalDomain localDomain suffix
  have hargument :
      arguments[localDomain.idxOf q]? = some argument := by
    exact stackArguments_getElem?_idxOf machine globalDomain
      suffix hqLocal
  have hclosed : argument.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed
      (stackSchema_wellFormed machine globalDomain hq hsuffix)
  have hidx :
      localDomain.idxOf q < localDomain.length :=
    List.idxOf_lt_length_iff.mpr hqLocal
  have hqRange : (List.range machine.numStates)[q]? = some q := by
    simp [hq]
  have hbaseRoot :
      (schemaBaseLayer machine localDomain).roots[q]? =
        some (localDomain.idxOf q) := by
    simp [schemaBaseLayer, List.getElem?_map, hqRange]
  have hrhsRoot : rhs.root = localDomain.idxOf q := by
    simp [rhs, RegularTerm.root, hbaseRoot]
  have hrhsNode :
      rhs.nodeAt? (localDomain.idxOf q) =
        some (.inl (localDomain.idxOf q) : RawNode) := by
    unfold rhs RegularTerm.nodeAt? RegularTerm.nodes
    rw [List.getElem?_append_left]
    · simp only [schemaBaseLayer]
      rw [List.getElem?_append_left (by simpa using hidx)]
      simp [List.getElem?_map, List.getElem?_range hidx]
    · simp [schemaBaseLayer]
      omega
  have hroot :
      (rhs.instantiate arguments).root =
        RegularTerm.argumentOffset rhs.nodes.length arguments
            (localDomain.idxOf q) + argument.root := by
    unfold RegularTerm.instantiate
    change rhs.resolveRHSRef arguments rhs.root = _
    rw [hrhsRoot]
    simp [RegularTerm.resolveRHSRef, hrhsNode,
      RegularTerm.argumentRoot?, hargument]
  have hcopy := instantiateArgument_unfoldingEquivalent
    (rhs := rhs) hargument hclosed
  have hsame :
      (rhs.instantiate arguments).withRoot
          (RegularTerm.argumentOffset rhs.nodes.length arguments
            (localDomain.idxOf q) + argument.root) =
        rhs.instantiate arguments := by
    apply Prod.ext
    · rfl
    · simpa [RegularTerm.withRoot] using hroot.symm
  rw [hsame] at hcopy
  have happend :=
    appendNodes_unfoldingEquivalent hclosed targetExtra
  exact hcopy.trans (by
    simpa [argument, stackSchema] using happend)

private theorem extendedTerm_rootApplication?
    (machine : EncodedDPDA Action) (Z : ℕ)
    (layer : TermLayer) {q : ℕ}
    (hq : q < machine.numStates)
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none)
    (extra : List RawNode) :
    RegularTerm.rootApplication?
      (((extendLayer machine Z layer).nodes ++ extra,
        (extendLayer machine Z layer).roots[q]?.getD 0) :
        RegularTerm) =
      some (headSymbol machine q Z,
        selectRoots (headTargets machine q Z) layer.roots) := by
  have hqRange : (List.range machine.numStates)[q]? = some q := by
    simp [hq]
  have hroot :
      (extendLayer machine Z layer).roots[q]? =
        some (layer.nodes.length + q) := by
    simp [extendLayer, List.getElem?_map, hqRange, hstable]
  have hrootBound : layer.nodes.length + q <
      (extendLayer machine Z layer).nodes.length := by
    rw [extendLayer_nodes_length]
    omega
  unfold RegularTerm.rootApplication? RegularTerm.rootNode?
    RegularTerm.nodeAt? RegularTerm.root RegularTerm.nodes
  rw [hroot]
  simp only [Option.getD_some]
  rw [List.getElem?_append_left hrootBound]
  simp only [extendLayer]
  rw [List.getElem?_append_right (by omega)]
  simp [List.getElem?_map, hqRange, hstable]

private theorem selectedRoots_forall₂
    {R : ℕ → ℕ → Prop} {targets left right : List ℕ}
    (f : ℕ → ℕ)
    (hrel : ∀ target, target ∈ targets →
      R (f (left[target]?.getD 0))
        (right[target]?.getD 0)) :
    List.Forall₂ R
      ((selectRoots targets left).map f)
      (selectRoots targets right) := by
  unfold selectRoots
  induction targets with
  | nil => exact .nil
  | cons target targets ih =>
      simp only [List.map_cons]
      exact .cons
        (hrel target (by simp))
        (ih fun next hnext =>
          hrel next (by simp [hnext]))

private theorem stackLayerInstantiationAux
    (machine : EncodedDPDA Action)
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {globalDomain localDomain suffix front : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (hfront : ∀ symbol ∈ front,
      symbol < machine.numStackSymbols)
    {q : ℕ} (hq : q < machine.numStates)
    (hclosed : ReturnClosed machine localDomain q front)
    (schemaExtra targetExtra : List RawNode) :
    RegularTerm.UnfoldingEquivalent
      (RegularTerm.instantiate
        (((extendStack machine front
            (schemaBaseLayer machine localDomain)).nodes ++
              schemaExtra,
          (extendStack machine front
            (schemaBaseLayer machine localDomain)).roots[q]?.getD 0) :
          RegularTerm)
        (stackArguments machine globalDomain localDomain suffix))
      (((extendStack machine front
          (stackLayer machine globalDomain suffix)).nodes ++ targetExtra,
        (extendStack machine front
          (stackLayer machine globalDomain suffix)).roots[q]?.getD 0) :
        RegularTerm) := by
  induction front generalizing q schemaExtra targetExtra with
  | nil =>
      have hqLocal : q ∈ localDomain := by
        apply hclosed q hq
        exact Relation.ReflTransGen.refl
      simpa using
        schemaBaseLayerInstantiation_unfoldingEquivalent
          machine hsuffix hq hqLocal schemaExtra targetExtra
  | cons Z front ih =>
      have hZ : Z < machine.numStackSymbols :=
        hfront Z (by simp)
      have htail : ∀ symbol ∈ front,
          symbol < machine.numStackSymbols := by
        intro symbol hsymbol
        exact hfront symbol (by simp [hsymbol])
      rw [extendStack_cons, extendStack_cons]
      let schema :=
        extendStack machine front
          (schemaBaseLayer machine localDomain)
      let target :=
        extendStack machine front
          (stackLayer machine globalDomain suffix)
      let schemaNew : List RawNode :=
        (List.range machine.numStates).map fun state =>
          match DPDAToFirstOrder.Machine.epsilonStep?
              machine state Z with
          | some _ =>
              (.inr (bottomSymbol machine, []) : RawNode)
          | none =>
              .inr (headSymbol machine state Z,
                selectRoots (headTargets machine state Z)
                  schema.roots)
      let targetNew : List RawNode :=
        (List.range machine.numStates).map fun state =>
          match DPDAToFirstOrder.Machine.epsilonStep?
              machine state Z with
          | some _ =>
              (.inr (bottomSymbol machine, []) : RawNode)
          | none =>
              .inr (headSymbol machine state Z,
                selectRoots (headTargets machine state Z)
                  target.roots)
      cases hstep :
          DPDAToFirstOrder.Machine.epsilonStep?
            machine q Z with
      | some out =>
          rcases out with ⟨next, replacement⟩
          have hnext : next < machine.numStates :=
            DPDAToFirstOrder.Machine.epsilonStep?_target_lt hstep
          have hnextClosed :
              ReturnClosed machine localDomain next front :=
            hclosed.after_epsilon hnormal hq hZ htail hstep
          have hih := ih htail hnext hnextClosed
            (schemaNew ++ schemaExtra)
            (targetNew ++ targetExtra)
          simpa [schema, target, schemaNew, targetNew,
            extendLayer, hstep, hq, List.append_assoc] using hih
      | none =>
          let schemaTerm : RegularTerm :=
            ((extendLayer machine Z schema).nodes ++ schemaExtra,
              (extendLayer machine Z schema).roots[q]?.getD 0)
          let targetTerm : RegularTerm :=
            ((extendLayer machine Z target).nodes ++ targetExtra,
              (extendLayer machine Z target).roots[q]?.getD 0)
          have hschemaRoot :=
            extendedTerm_rootApplication?
              machine Z schema hq hstep schemaExtra
          have hleftRoot :
              (schemaTerm.instantiate
                (stackArguments machine globalDomain
                  localDomain suffix)).rootApplication? =
                some (headSymbol machine q Z,
                  (selectRoots (headTargets machine q Z)
                    schema.roots).map
                      (schemaTerm.resolveRHSRef
                        (stackArguments machine globalDomain
                          localDomain suffix))) := by
            exact instantiate_rootApplication?
              (stackArguments machine globalDomain
                localDomain suffix)
              (by simpa [schemaTerm] using hschemaRoot)
          have hrightRoot :
              targetTerm.rootApplication? =
                some (headSymbol machine q Z,
                  selectRoots (headTargets machine q Z)
                    target.roots) := by
            simpa [targetTerm] using
              extendedTerm_rootApplication?
                machine Z target hq hstep targetExtra
          apply unfoldingEquivalent_of_rootApplications
            hleftRoot hrightRoot
          apply selectedRoots_forall₂
            (schemaTerm.resolveRHSRef
              (stackArguments machine globalDomain
                localDomain suffix))
          intro state hstate
          have hstateBound : state < machine.numStates :=
            (DPDAObservableReturns.mem_exposedTargets_iff
              machine q Z state).mp hstate |>.2.1
          have hstateClosed :
              ReturnClosed machine localDomain state front :=
            hclosed.after_retained_head hq hZ hstate
          rw [← RegularTerm.withRoot_unfoldingEquivalent_iff_bisimilarAt]
          have hih := ih htail hstateBound hstateClosed
            (schemaNew ++ schemaExtra)
            (targetNew ++ targetExtra)
          simpa [schemaTerm, targetTerm, schema, target,
            schemaNew, targetNew, extendLayer,
            List.append_assoc, RegularTerm.withRoot] using hih

/-- Pruned schema composition.  `ReturnClosed` is precisely the condition
ensuring that every base variable reachable through the compressed prefix is
present in the local argument domain. -/
public theorem stackSchema_instantiate_stackArguments
    (machine : EncodedDPDA Action)
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {globalDomain localDomain front suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (hfront : ∀ symbol ∈ front,
      symbol < machine.numStackSymbols)
    {q : ℕ} (hq : q < machine.numStates)
    (hclosed : ReturnClosed machine localDomain q front) :
    RegularTerm.UnfoldingEquivalent
      ((stackSchema machine localDomain q front).instantiate
        (stackArguments machine globalDomain localDomain suffix))
      (stackSchema machine globalDomain q (front ++ suffix)) := by
  have hcomposition :=
    stackLayerInstantiationAux machine hnormal
      (globalDomain := globalDomain)
      (localDomain := localDomain)
      (suffix := suffix) (front := front)
      hsuffix hfront hq hclosed [] []
  simpa [stackSchema, extendStack_schemaBaseLayer,
    ← stackLayer_append machine globalDomain front suffix]
    using hcomposition

private theorem stackRootArguments_forall₂
    (machine : EncodedDPDA Action)
    (globalDomain : List ℕ) {q Z : ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    {suffix targets : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (htargets : ∀ target ∈ targets,
      target < machine.numStates) :
    List.Forall₂ RegularTerm.UnfoldingEquivalent
      ((selectRoots targets
          (stackLayer machine globalDomain suffix).roots).map
        (stackSchema machine globalDomain q (Z :: suffix)).withRoot)
      (stackArguments machine globalDomain targets suffix) := by
  let layer := stackLayer machine globalDomain suffix
  let source := stackSchema machine globalDomain q (Z :: suffix)
  let newNodes : List RawNode :=
    (List.range machine.numStates).map fun state =>
      match DPDAToFirstOrder.Machine.epsilonStep?
          machine state Z with
      | some _ =>
          (.inr (bottomSymbol machine, []) : RawNode)
      | none =>
          .inr (headSymbol machine state Z,
            selectRoots (headTargets machine state Z)
              layer.roots)
  have hlayerReferences :=
    stackLayer_references machine globalDomain suffix
  have hfullStack : ∀ symbol ∈ Z :: suffix,
      symbol < machine.numStackSymbols := by
    intro symbol hsymbol
    simp only [List.mem_cons] at hsymbol
    rcases hsymbol with rfl | hsymbol
    · exact hZ
    · exact hsuffix symbol hsymbol
  induction targets with
  | nil => exact .nil
  | cons target targets ih =>
      have htarget : target < machine.numStates :=
        htargets target (by simp)
      have htargetRoots : target < layer.roots.length := by
        simpa [layer, hlayerReferences.1] using htarget
      have hrootLookup :
          layer.roots[target]? =
            some (layer.roots[target]'htargetRoots) := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨htargetRoots, rfl⟩
      let argument :=
        stackSchema machine globalDomain target suffix
      have hclosed : argument.ReferenceClosed :=
        RegularTerm.referenceClosed_of_wellFormed
          (stackSchema_wellFormed machine globalDomain
            htarget hsuffix)
      have happend :=
        appendNodes_unfoldingEquivalent hclosed newNodes
      have hactual :
          source.withRoot
              (layer.roots[target]?.getD 0) =
            (argument.nodes ++ newNodes, argument.root) := by
        apply Prod.ext
        · change
            (stackLayer machine globalDomain (Z :: suffix)).nodes =
              (stackLayer machine globalDomain suffix).nodes ++
                newNodes
          rw [stackLayer_cons]
          rfl
        · rfl
      simp only [selectRoots, stackArguments, List.map_cons]
      exact .cons
        (by
          rw [hactual]
          exact happend.symm)
        (ih (fun next hnext =>
          htargets next (by simp [hnext])))

private theorem stackRootArguments_referenceClosed
    (machine : EncodedDPDA Action)
    (globalDomain : List ℕ) {q Z : ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    {suffix targets : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (htargets : ∀ target ∈ targets,
      target < machine.numStates) :
    ∀ argument ∈
      (selectRoots targets
          (stackLayer machine globalDomain suffix).roots).map
        (stackSchema machine globalDomain q (Z :: suffix)).withRoot,
      argument.ReferenceClosed := by
  have hfullStack : ∀ symbol ∈ Z :: suffix,
      symbol < machine.numStackSymbols := by
    intro symbol hsymbol
    simp only [List.mem_cons] at hsymbol
    rcases hsymbol with rfl | hsymbol
    · exact hZ
    · exact hsuffix symbol hsymbol
  have hsourceClosed :=
    RegularTerm.referenceClosed_of_wellFormed
      (stackSchema_wellFormed machine globalDomain hq hfullStack)
  have hlayerReferences :=
    stackLayer_references machine globalDomain suffix
  intro argument hargument
  obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hargument
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hroot
  have htargetBound := htargets target htarget
  have htargetRoots : target <
      (stackLayer machine globalDomain suffix).roots.length := by
    simpa [hlayerReferences.1] using htargetBound
  have hlookup :
      (stackLayer machine globalDomain suffix).roots[target]? =
        some ((stackLayer machine globalDomain suffix).roots[
          target]'htargetRoots) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨htargetRoots, rfl⟩
  rw [hlookup]
  simp only [Option.getD_some]
  apply RegularTerm.withRoot_referenceClosed hsourceClosed
  have hrootOld :=
    hlayerReferences.2 _
      (List.getElem_mem htargetRoots)
  change (stackLayer machine globalDomain suffix).roots[target] <
    (stackLayer machine globalDomain (Z :: suffix)).nodes.length
  rw [stackLayer_cons, extendLayer_nodes_length]
  omega

/-- One stable machine input transition is simulated by one compressed grammar
rewrite on an arbitrary open continuation domain. -/
public theorem grammar_rootRewrite?_of_inputStep_schema
    (machine : EncodedDPDA Action)
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    (globalDomain : List ℕ)
    {q Z : ℕ} (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    {action : Action} {target : ℕ}
    {replacement : List ℕ}
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none)
    (hinput :
      DPDAToFirstOrder.Machine.inputStep? machine q action Z =
        some (target, replacement)) :
    ∃ result,
      (grammar machine).rootRewrite? action
          (stackSchema machine globalDomain q (Z :: suffix)) =
        some result ∧
      result.UnfoldingEquivalent
        (stackSchema machine globalDomain target
          (replacement ++ suffix)) := by
  have htarget : target < machine.numStates :=
    DPDAToFirstOrder.Machine.inputStep?_target_lt hinput
  have hreplacement : ∀ symbol ∈ replacement,
      symbol < machine.numStackSymbols :=
    DPDAToFirstOrder.Machine.inputStep?_replacement_lt hinput
  let localDomain := headTargets machine q Z
  let source := stackSchema machine globalDomain q (Z :: suffix)
  have hroot :
      source.rootApplication? =
        some (headSymbol machine q Z,
          selectRoots localDomain
            (stackLayer machine globalDomain suffix).roots) := by
    simpa [source, localDomain] using
      stackSchema_rootApplication?_of_stable
        machine globalDomain hq suffix hstable
  have hrule :=
    grammar_ruleLookup_of_inputStep? machine
      hq hZ hstable hinput
  unfold EncodedFirstOrderGrammar.rootRewrite?
  simp only [source, hroot, hrule, Option.map_some]
  let actualArguments :=
    (selectRoots localDomain
      (stackLayer machine globalDomain suffix).roots).map
        source.withRoot
  let canonicalArguments :=
    stackArguments machine globalDomain localDomain suffix
  let rhs :=
    stackSchema machine localDomain target replacement
  refine ⟨rhs.instantiate actualArguments, rfl, ?_⟩
  have hlocalBound :
      ∀ state ∈ localDomain, state < machine.numStates := by
    intro state hstate
    exact (DPDAObservableReturns.mem_exposedTargets_iff
      machine q Z state).mp hstate |>.2.1
  have hrhsClosed : rhs.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed
      (stackSchema_wellFormed machine localDomain
        htarget hreplacement)
  have hactualCanonical :
      List.Forall₂ RegularTerm.UnfoldingEquivalent
        actualArguments canonicalArguments := by
    simpa [actualArguments, canonicalArguments, source,
      localDomain] using
      stackRootArguments_forall₂ machine globalDomain
        hq hZ hsuffix hlocalBound
  have hactualClosed :
      ∀ argument ∈ actualArguments,
        argument.ReferenceClosed := by
    simpa [actualArguments, source, localDomain] using
      stackRootArguments_referenceClosed machine globalDomain
        hq hZ hsuffix hlocalBound
  have hcanonicalClosed :
      ∀ argument ∈ canonicalArguments,
        argument.ReferenceClosed := by
    simpa [canonicalArguments, localDomain] using
      stackArguments_referenceClosed machine
        (globalDomain := globalDomain)
        (localDomain := localDomain)
        (suffix := suffix) hlocalBound hsuffix
  have harguments :=
    RegularTerm.instantiate_unfoldingEquivalent
      hrhsClosed hactualCanonical
      hactualClosed hcanonicalClosed
  have hclosed :
      ReturnClosed machine localDomain target replacement := by
    simpa [localDomain] using
      ReturnClosed.after_input hq hZ hstable hinput
  have hcomposition :=
    stackSchema_instantiate_stackArguments
      machine hnormal hsuffix hreplacement htarget hclosed
      (globalDomain := globalDomain)
  exact harguments.trans (by
    simpa [rhs, canonicalArguments, localDomain] using hcomposition)

private theorem epsilonStep?_of_effectiveEpsilonRow
    (machine : EncodedDPDA Action)
    {row : EpsilonRow}
    (hrow : row ∈ machine.effectiveEpsilonRows) :
    DPDAToFirstOrder.Machine.epsilonStep? machine
        (machine.normalizedEpsilonSource row)
        (machine.normalizedEpsilonTop row) =
      some (machine.normalizedEpsilonTarget row,
        machine.normalizedEpsilonReplacement row) := by
  have htransition :=
    machine.effectiveEpsilonRow_transition hrow
  change machine.epsilonLookup
      (machine.state (machine.normalizedEpsilonSource row))
      (machine.stackSymbol (machine.normalizedEpsilonTop row)) =
    some (machine.state (machine.normalizedEpsilonTarget row),
      machine.replacement
        (machine.normalizedEpsilonReplacement row)) at htransition
  unfold DPDAToFirstOrder.Machine.epsilonStep?
  rw [htransition]
  simp [EncodedDPDA.state, EncodedDPDA.replacement,
    EncodedDPDA.stackSymbol, EncodedDPDA.normalizedEpsilonTarget,
    EncodedDPDA.normalizedEpsilonReplacement, List.map_map,
    Function.comp_def, Nat.mod_mod]

private theorem inputStep?_of_effectiveInputRow
    (machine : EncodedDPDA Action)
    {row : InputRow Action}
    (hrow : row ∈ machine.effectiveInputRows) :
    DPDAToFirstOrder.Machine.epsilonStep? machine
        (machine.normalizedInputSource row)
        (machine.normalizedInputTop row) = none ∧
      DPDAToFirstOrder.Machine.inputStep? machine
          (machine.normalizedInputSource row) row.2.1
          (machine.normalizedInputTop row) =
        some (machine.normalizedInputTarget row,
          machine.normalizedInputReplacement row) := by
  have htransition :=
    machine.effectiveInputRow_transition hrow
  change (if (machine.epsilonLookup
      (machine.state (machine.normalizedInputSource row))
      (machine.stackSymbol (machine.normalizedInputTop row))).isSome
    then none
    else machine.inputLookup
      (machine.state (machine.normalizedInputSource row)) row.2.1
      (machine.stackSymbol (machine.normalizedInputTop row))) =
    some (machine.state (machine.normalizedInputTarget row),
      machine.replacement
        (machine.normalizedInputReplacement row)) at htransition
  cases hepsilon : machine.epsilonLookup
      (machine.state (machine.normalizedInputSource row))
      (machine.stackSymbol (machine.normalizedInputTop row)) with
  | some out =>
      simp [hepsilon] at htransition
  | none =>
      have hinput : machine.inputLookup
          (machine.state (machine.normalizedInputSource row)) row.2.1
          (machine.stackSymbol (machine.normalizedInputTop row)) =
        some (machine.state (machine.normalizedInputTarget row),
          machine.replacement
            (machine.normalizedInputReplacement row)) := by
        simpa [hepsilon] using htransition
      constructor
      · simp [DPDAToFirstOrder.Machine.epsilonStep?, hepsilon]
      · unfold DPDAToFirstOrder.Machine.inputStep?
        rw [hinput]
        simp [EncodedDPDA.state, EncodedDPDA.replacement,
          EncodedDPDA.stackSymbol, EncodedDPDA.normalizedInputTarget,
          EncodedDPDA.normalizedInputReplacement, List.map_map,
          Function.comp_def, Nat.mod_mod]

private theorem stackSchema_epsilon_unfoldingEquivalent
    (machine : EncodedDPDA Action)
    (globalDomain : List ℕ)
    {q Z target : ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    {suffix replacement : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (hstep :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z =
        some (target, replacement)) :
    RegularTerm.UnfoldingEquivalent
      (stackSchema machine globalDomain q (Z :: suffix))
      (stackSchema machine globalDomain target suffix) := by
  let layer := stackLayer machine globalDomain suffix
  let source := stackSchema machine globalDomain q (Z :: suffix)
  let targetSchema := stackSchema machine globalDomain target suffix
  let newNodes : List RawNode :=
    (List.range machine.numStates).map fun state =>
      match DPDAToFirstOrder.Machine.epsilonStep?
          machine state Z with
      | some _ =>
          (.inr (bottomSymbol machine, []) : RawNode)
      | none =>
          .inr (headSymbol machine state Z,
            selectRoots (headTargets machine state Z) layer.roots)
  have htarget : target < machine.numStates :=
    DPDAToFirstOrder.Machine.epsilonStep?_target_lt hstep
  have htargetClosed : targetSchema.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed
      (stackSchema_wellFormed machine globalDomain
        htarget hsuffix)
  have hsource :
      source = (targetSchema.nodes ++ newNodes, targetSchema.root) := by
    apply Prod.ext
    · change
        (stackLayer machine globalDomain (Z :: suffix)).nodes =
          (stackLayer machine globalDomain suffix).nodes ++ newNodes
      rw [stackLayer_cons]
      rfl
    · change
        (stackLayer machine globalDomain (Z :: suffix)).roots[q]?.getD 0 =
          (stackLayer machine globalDomain suffix).roots[target]?.getD 0
      rw [stackLayer_cons]
      have hqRange :
          (List.range machine.numStates)[q]? = some q := by
        simp [hq]
      have hroot :
          (extendLayer machine Z
            (stackLayer machine globalDomain suffix)).roots[q]? =
          some ((stackLayer machine globalDomain suffix).roots[target]?.getD 0) := by
        simp [extendLayer, List.getElem?_map, hqRange, hstep]
      simp [hroot]
  change source.UnfoldingEquivalent targetSchema
  rw [hsource]
  exact (appendNodes_unfoldingEquivalent htargetClosed newNodes).symm

private theorem exists_runActions_of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action}
    (hg : g.WellFormed)
    {left right rightTarget : RegularTerm}
    {word : List Action}
    (hequivalent : left.UnfoldingEquivalent right)
    (hleftClosed : left.ReferenceClosed)
    (hrightClosed : right.ReferenceClosed)
    (hrun : g.runActions? word right = some rightTarget) :
    ∃ leftTarget,
      g.runActions? word left = some leftTarget ∧
      leftTarget.UnfoldingEquivalent rightTarget := by
  induction word generalizing left right with
  | nil =>
      simp [EncodedFirstOrderGrammar.runActions?] at hrun
      subst rightTarget
      exact ⟨left, rfl, hequivalent⟩
  | cons action word ih =>
      simp only [EncodedFirstOrderGrammar.runActions?,
        List.map_cons, EncodedFirstOrderGrammar.run?_cons] at hrun
      cases hrightStep : g.step? (.inl action) right with
      | none =>
          simp [hrightStep] at hrun
      | some rightNext =>
          simp only [hrightStep, Option.bind_some] at hrun
          have hsteps :=
            EncodedFirstOrderGrammar.step?_respects_unfoldingEquivalent
              (label := (.inl action))
              hequivalent hleftClosed hrightClosed
              (fun X action rhs hrule =>
                EncodedFirstOrderGrammar.selected_rhs_referenceClosed
                  hg hrule)
          rw [hrightStep] at hsteps
          cases hleftStep : g.step? (.inl action) left with
          | none =>
              rw [hleftStep] at hsteps
              cases hsteps
          | some leftNext =>
              rw [hleftStep] at hsteps
              cases hsteps with
              | some hnextEquivalent =>
                  have hleftNextClosed :=
                    EncodedFirstOrderGrammar.step?_preserves_referenceClosed
                      hg hleftClosed hleftStep
                  have hrightNextClosed :=
                    EncodedFirstOrderGrammar.step?_preserves_referenceClosed
                      hg hrightClosed hrightStep
                  obtain ⟨leftTarget, hleftRun,
                      htargetEquivalent⟩ :=
                    ih hnextEquivalent hleftNextClosed
                      hrightNextClosed hrun
                  refine ⟨leftTarget, ?_, htargetEquivalent⟩
                  simp only [EncodedFirstOrderGrammar.runActions?,
                    List.map_cons, EncodedFirstOrderGrammar.run?_cons,
                    hleftStep, Option.bind_some]
                  simpa [EncodedFirstOrderGrammar.runActions?] using
                    hleftRun

private theorem normalizedEpsilonResult
    (machine : EncodedDPDA Action)
    (row : EpsilonRow) {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols) :
    machine.RawNormalized
      (machine.normalizedEpsilonTarget row,
        machine.normalizedEpsilonReplacement row ++ suffix) := by
  refine ⟨Nat.mod_lt _ machine.numStates_pos, ?_⟩
  intro symbol hsymbol
  rw [List.mem_append] at hsymbol
  rcases hsymbol with hsymbol | hsymbol
  · rw [EncodedDPDA.normalizedEpsilonReplacement,
      List.mem_map] at hsymbol
    obtain ⟨source, _, rfl⟩ := hsymbol
    exact Nat.mod_lt _ machine.numStackSymbols_pos
  · exact hsuffix symbol hsymbol

private theorem normalizedInputResult
    (machine : EncodedDPDA Action)
    (row : InputRow Action) {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols) :
    machine.RawNormalized
      (machine.normalizedInputTarget row,
        machine.normalizedInputReplacement row ++ suffix) := by
  refine ⟨Nat.mod_lt _ machine.numStates_pos, ?_⟩
  intro symbol hsymbol
  rw [List.mem_append] at hsymbol
  rcases hsymbol with hsymbol | hsymbol
  · rw [EncodedDPDA.normalizedInputReplacement,
      List.mem_map] at hsymbol
    obtain ⟨source, _, rfl⟩ := hsymbol
    exact Nat.mod_lt _ machine.numStackSymbols_pos
  · exact hsuffix symbol hsymbol

/-- Every input-erased machine run is simulated by an ordinary grammar run,
uniformly over the chosen continuation-variable domain. -/
public theorem stackSchema_run_of_rawErasedReaches
    (machine : EncodedDPDA Action)
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    (domain : List ℕ)
    {x y : ℕ × List ℕ}
    (hx : machine.RawNormalized x)
    (hreach : machine.RawErasedReaches x y) :
    ∃ word result,
      (grammar machine).runActions? word
          (stackSchema machine domain x.1 x.2) =
        some result ∧
      result.UnfoldingEquivalent
        (stackSchema machine domain y.1 y.2) := by
  have main : ∀ {x y : ℕ × List ℕ},
      machine.RawErasedReaches x y →
      machine.RawNormalized x →
      ∃ word result,
        (grammar machine).runActions? word
            (stackSchema machine domain x.1 x.2) =
          some result ∧
        result.UnfoldingEquivalent
          (stackSchema machine domain y.1 y.2) := by
    intro x y hrun
    induction hrun using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hx
        exact ⟨[], stackSchema machine domain y.1 y.2,
          rfl, RegularTerm.unfoldingEquivalent_refl _⟩
    | @head x next hstep hrest ih =>
        intro hx
        cases hstep with
        | @epsilon row suffix hrow =>
            have hq : machine.normalizedEpsilonSource row <
                machine.numStates := hx.1
            have hZ : machine.normalizedEpsilonTop row <
                machine.numStackSymbols :=
              hx.2 _ (by simp)
            have hsuffix : ∀ symbol ∈ suffix,
                symbol < machine.numStackSymbols := by
              intro symbol hsymbol
              exact hx.2 symbol (by simp [hsymbol])
            have hmachineStep :=
              epsilonStep?_of_effectiveEpsilonRow machine hrow
            have hempty :
                machine.normalizedEpsilonReplacement row = [] :=
              DPDAToFirstOrder.Machine.epsilonStep?_replacement_eq_nil_of_poppingComplete
                hnormal hmachineStep
            have hnextNormalized :=
              normalizedEpsilonResult machine row hsuffix
            obtain ⟨word, result, htail, hequivalent⟩ :=
              ih hnextNormalized
            have htail' :
                (grammar machine).runActions? word
                    (stackSchema machine domain
                      (machine.normalizedEpsilonTarget row) suffix) =
                  some result := by
              simpa [hempty] using htail
            have hsourceEquivalent :=
              stackSchema_epsilon_unfoldingEquivalent
                machine domain hq hZ hsuffix hmachineStep
            have hsourceClosed :
                (stackSchema machine domain
                    (machine.normalizedEpsilonSource row)
                    (machine.normalizedEpsilonTop row :: suffix)).ReferenceClosed :=
              RegularTerm.referenceClosed_of_wellFormed
                (stackSchema_wellFormed machine domain hq
                  (by
                    intro symbol hsymbol
                    simp only [List.mem_cons] at hsymbol
                    rcases hsymbol with rfl | hsymbol
                    · exact hZ
                    · exact hsuffix symbol hsymbol))
            have hnextClosed :
                (stackSchema machine domain
                    (machine.normalizedEpsilonTarget row) suffix).ReferenceClosed :=
              RegularTerm.referenceClosed_of_wellFormed
                (stackSchema_wellFormed machine domain
                  (DPDAToFirstOrder.Machine.epsilonStep?_target_lt
                    hmachineStep)
                  hsuffix)
            obtain ⟨sourceResult, hsourceRun,
                hsourceResultEquivalent⟩ :=
              exists_runActions_of_unfoldingEquivalent
                (grammar_wellFormed machine)
                hsourceEquivalent hsourceClosed hnextClosed htail'
            exact ⟨word, sourceResult, hsourceRun,
              hsourceResultEquivalent.trans hequivalent⟩
        | @input row suffix hrow =>
            have hq : machine.normalizedInputSource row <
                machine.numStates := hx.1
            have hZ : machine.normalizedInputTop row <
                machine.numStackSymbols :=
              hx.2 _ (by simp)
            have hsuffix : ∀ symbol ∈ suffix,
                symbol < machine.numStackSymbols := by
              intro symbol hsymbol
              exact hx.2 symbol (by simp [hsymbol])
            obtain ⟨hstable, hmachineStep⟩ :=
              inputStep?_of_effectiveInputRow machine hrow
            have htarget :
                machine.normalizedInputTarget row <
                  machine.numStates :=
              DPDAToFirstOrder.Machine.inputStep?_target_lt
                hmachineStep
            have hreplacement :
                ∀ symbol ∈ machine.normalizedInputReplacement row,
                  symbol < machine.numStackSymbols :=
              DPDAToFirstOrder.Machine.inputStep?_replacement_lt
                hmachineStep
            have hnextNormalized :=
              normalizedInputResult machine row hsuffix
            obtain ⟨word, result, htail, hequivalent⟩ :=
              ih hnextNormalized
            obtain ⟨firstResult, hfirstRoot,
                hfirstEquivalent⟩ :=
              grammar_rootRewrite?_of_inputStep_schema
                machine hnormal domain hq hZ hsuffix
                hstable hmachineStep
            have hfirstStep :
                (grammar machine).step? (.inl row.2.1)
                    (stackSchema machine domain
                      (machine.normalizedInputSource row)
                      (machine.normalizedInputTop row :: suffix)) =
                  some firstResult := by
              exact hfirstRoot
            have hsourceClosed :
                (stackSchema machine domain
                    (machine.normalizedInputSource row)
                    (machine.normalizedInputTop row :: suffix)).ReferenceClosed :=
              RegularTerm.referenceClosed_of_wellFormed
                (stackSchema_wellFormed machine domain hq
                  (by
                    intro symbol hsymbol
                    simp only [List.mem_cons] at hsymbol
                    rcases hsymbol with rfl | hsymbol
                    · exact hZ
                    · exact hsuffix symbol hsymbol))
            have hfirstClosed : firstResult.ReferenceClosed :=
              EncodedFirstOrderGrammar.step?_preserves_referenceClosed
                (grammar_wellFormed machine) hsourceClosed hfirstStep
            have hnextClosed :
                (stackSchema machine domain
                    (machine.normalizedInputTarget row)
                    (machine.normalizedInputReplacement row ++ suffix)).ReferenceClosed :=
              RegularTerm.referenceClosed_of_wellFormed
                (stackSchema_wellFormed machine domain htarget
                  (by
                    intro symbol hsymbol
                    rw [List.mem_append] at hsymbol
                    rcases hsymbol with hsymbol | hsymbol
                    · exact hreplacement symbol hsymbol
                    · exact hsuffix symbol hsymbol))
            obtain ⟨tailResult, htailRun,
                htailResultEquivalent⟩ :=
              exists_runActions_of_unfoldingEquivalent
                (grammar_wellFormed machine)
                hfirstEquivalent hfirstClosed hnextClosed htail
            refine ⟨row.2.1 :: word, tailResult, ?_,
              htailResultEquivalent.trans hequivalent⟩
            simp only [EncodedFirstOrderGrammar.runActions?,
              List.map_cons, EncodedFirstOrderGrammar.run?_cons,
              hfirstStep, Option.bind_some]
            exact htailRun
  exact main hreach hx

/-- The observable-return translation is in exposing-successor normal form:
every retained argument is exposed by a word that pops its represented stack
head and returns in the corresponding control state. -/
public theorem grammar_exposingNormalForm
    (machine : EncodedDPDA Action)
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet) :
    (grammar machine).ExposingNormalForm := by
  intro position
  let witness := successorReturnWitness machine position
  let domain := headTargets machine
    witness.state witness.stackSymbol
  have hrank :
      (grammar machine).ranks.get position.1 = domain.length := by
    have hpositionLookup :
        (grammarRanks machine)[position.1.val]? =
          some ((grammar machine).ranks.get position.1) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨position.1.isLt, rfl⟩
    have hheadLookup :
        (grammarRanks machine)[
          headSymbol machine witness.state witness.stackSymbol]? =
          some domain.length := by
      simpa [domain] using
        grammarRanks_headSymbol machine
          witness.state_lt witness.stackSymbol_lt
    rw [witness.symbol_eq] at hpositionLookup
    exact Option.some.inj
      (hpositionLookup.symm.trans hheadLookup)
  have hraw :
      machine.RawErasedReaches
        (witness.state, [witness.stackSymbol])
        (witness.target, []) :=
    rawErasedReaches_of_rawHeadReturns machine
      witness.state_lt witness.stackSymbol_lt
      witness.target_lt witness.returns
  have hnormalized :
      machine.RawNormalized
        (witness.state, [witness.stackSymbol]) := by
    exact ⟨witness.state_lt, by
      intro symbol hsymbol
      simp only [List.mem_singleton] at hsymbol
      subst symbol
      exact witness.stackSymbol_lt⟩
  obtain ⟨word, result, hrun, hresultEmpty⟩ :=
    stackSchema_run_of_rawErasedReaches
      machine hnormal domain hnormalized hraw
  have hschemaTemplate :
      (stackSchema machine domain witness.state
        [witness.stackSymbol]).UnfoldingEquivalent
      (RegularTerm.symbolTemplate position.1
        ((grammar machine).ranks.get position.1)) := by
    rw [hrank]
    change
      (stackSchema machine domain witness.state
        [witness.stackSymbol]).UnfoldingEquivalent
      (RegularTerm.symbolTemplate position.1.val domain.length)
    rw [witness.symbol_eq]
    simpa [domain] using
      stackSchema_singleton_unfoldingEquivalent_symbolTemplate
        machine witness.state_lt witness.stackSymbol_lt
        witness.stable
  have hschemaClosed :
      (stackSchema machine domain witness.state
        [witness.stackSymbol]).ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed
      (stackSchema_wellFormed machine domain
        witness.state_lt (by
          intro symbol hsymbol
          simp only [List.mem_singleton] at hsymbol
          subst symbol
          exact witness.stackSymbol_lt))
  have htemplateClosed :
      (RegularTerm.symbolTemplate position.1
        ((grammar machine).ranks.get position.1)).ReferenceClosed :=
    RegularTerm.symbolTemplate_referenceClosed _ _
  obtain ⟨templateResult, htemplateRun,
      htemplateResult⟩ :=
    exists_runActions_of_unfoldingEquivalent
      (grammar_wellFormed machine)
      hschemaTemplate.symm htemplateClosed hschemaClosed hrun
  have htargetMem : witness.target ∈ domain := by
    exact List.mem_of_getElem? witness.target_get
  have hemptyVariable :
      (stackSchema machine domain witness.target []).UnfoldingEquivalent
      (RegularTerm.variableTerm position.2) := by
    have hbase :=
      stackSchema_nil_unfoldingEquivalent_variable
        machine witness.target_lt htargetMem
    simpa [domain, witness.target_idxOf] using hbase
  exact ⟨word, templateResult, htemplateRun,
    htemplateResult.trans
      (hresultEmpty.trans hemptyVariable)⟩

/-! ## Ground configurations and observable traces -/

omit [Fintype Action] [DecidableEq Action] in
private theorem schemaBaseLayer_nil_eq_groundBaseLayer
    (machine : EncodedDPDA Action) :
    schemaBaseLayer machine [] = groundBaseLayer machine := by
  simp [schemaBaseLayer, groundBaseLayer]

omit [Fintype Action] in
public theorem stackLayer_nilDomain_eq_configurationLayer
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    stackLayer machine [] stack =
      configurationLayer machine stack := by
  unfold stackLayer configurationLayer
  rw [schemaBaseLayer_nil_eq_groundBaseLayer]

omit [Fintype Action] in
public theorem stackSchema_nilDomain_eq_configurationTerm
    (machine : EncodedDPDA Action) (q : ℕ) (stack : List ℕ) :
    stackSchema machine [] q stack =
      configurationTerm machine q stack := by
  unfold stackSchema configurationTerm
  rw [stackLayer_nilDomain_eq_configurationLayer]

public theorem configurationTerm_wellFormed
    (machine : EncodedDPDA Action)
    {q : ℕ} (hq : q < machine.numStates)
    {stack : List ℕ}
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) :
    (configurationTerm machine q stack).WellFormed
      (grammarRanks machine) 0 := by
  rw [← stackSchema_nilDomain_eq_configurationTerm]
  simpa using stackSchema_wellFormed machine [] hq hstack

private theorem ground_of_wellFormed_zero
    {ranks : List ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks 0) :
    term.Ground ranks := by
  have hclosed :=
    RegularTerm.referenceClosed_of_wellFormed hterm
  refine ⟨RegularTerm.shapeWellFormed_of_wellFormed hterm,
    List.range term.nodes.length, ?_, ?_⟩
  · exact List.mem_sublists'.mpr
      (List.Sublist.refl _)
  · constructor
    · exact List.mem_range.mpr hclosed.1
    · intro i hi
      have hiBound : i < term.nodes.length :=
        List.mem_range.mp hi
      let node : RawNode := term.nodes[i]'hiBound
      have hnode : term.nodeAt? i = some node := by
        unfold RegularTerm.nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hiBound, rfl⟩
      cases hkind : node with
      | inl x =>
          unfold RegularTerm.WellFormed
            RegularTerm.wellFormedCode at hterm
          rw [Bool.and_eq_true] at hterm
          have hmem : (.inl x : RawNode) ∈ term.nodes := by
            exact List.mem_of_getElem? (by
              simpa [hkind] using hnode)
          have hwell :=
            (List.all_eq_true.mp hterm.2) _ hmem
          simp [RegularTerm.nodeWellFormedCode] at hwell
      | inr application =>
          rcases application with ⟨X, children⟩
          refine ⟨X, children, by simpa [hkind] using hnode, ?_⟩
          intro child hchild
          exact List.mem_range.mpr
            (hclosed.2 i X children
              (by simpa [hkind] using hnode)
              child hchild)

/-- Every valid encoded configuration is a ground term of the compressed
grammar. -/
public theorem configurationTerm_ground
    (machine : EncodedDPDA Action)
    {q : ℕ} (hq : q < machine.numStates)
    {stack : List ℕ}
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) :
    (configurationTerm machine q stack).Ground
      (grammarRanks machine) :=
  ground_of_wellFormed_zero
    (configurationTerm_wellFormed machine hq hstack)

/-- A selected epsilon pop only redirects the compressed configuration root
to the target-state continuation. -/
public theorem configurationTerm_epsilon_unfoldingEquivalent
    (machine : EncodedDPDA Action)
    {q Z target : ℕ} {replacement : List ℕ}
    (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (hstep :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z =
        some (target, replacement)) :
    (configurationTerm machine q (Z :: suffix)).UnfoldingEquivalent
      (configurationTerm machine target suffix) := by
  rw [← stackSchema_nilDomain_eq_configurationTerm,
    ← stackSchema_nilDomain_eq_configurationTerm]
  exact stackSchema_epsilon_unfoldingEquivalent
    machine [] hq hZ hsuffix hstep

/-- One stable input transition is simulated by one compressed rewrite on the
ground configuration graph. -/
public theorem grammar_rootRewrite?_of_inputStep
    (machine : EncodedDPDA Action)
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {q Z : ℕ} (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    {action : Action} {target : ℕ}
    {replacement : List ℕ}
    (hstable :
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none)
    (hinput :
      DPDAToFirstOrder.Machine.inputStep? machine q action Z =
        some (target, replacement)) :
    ∃ result,
      (grammar machine).rootRewrite? action
          (configurationTerm machine q (Z :: suffix)) =
        some result ∧
      result.UnfoldingEquivalent
        (configurationTerm machine target
          (replacement ++ suffix)) := by
  simpa [← stackSchema_nilDomain_eq_configurationTerm] using
    grammar_rootRewrite?_of_inputStep_schema
      machine hnormal [] hq hZ hsuffix hstable hinput

/-- Forced epsilon popping is already reflected at the compressed graph root. -/
public theorem configurationTerm_stabilize_unfoldingEquivalent
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ}
    (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) :
    (configurationTerm machine q stack).UnfoldingEquivalent
      (configurationTerm machine
        (DPDAToFirstOrder.stabilize machine (q, stack)).1
        (DPDAToFirstOrder.stabilize machine (q, stack)).2) := by
  induction stack generalizing q with
  | nil =>
      simp only [DPDAToFirstOrder.stabilize]
      exact RegularTerm.unfoldingEquivalent_refl _
  | cons Z stack ih =>
      have hZ : Z < machine.numStackSymbols :=
        hstack Z (by simp)
      have htail : ∀ symbol ∈ stack,
          symbol < machine.numStackSymbols := by
        intro symbol hsymbol
        exact hstack symbol (by simp [hsymbol])
      cases hstep :
          DPDAToFirstOrder.Machine.epsilonStep? machine q Z with
      | none =>
          simp only [DPDAToFirstOrder.stabilize, hstep]
          exact RegularTerm.unfoldingEquivalent_refl _
      | some out =>
          rcases out with ⟨target, replacement⟩
          have hempty : replacement = [] :=
            DPDAToFirstOrder.Machine.epsilonStep?_replacement_eq_nil_of_poppingComplete
              hnormal hstep
          subst replacement
          have htarget : target < machine.numStates :=
            DPDAToFirstOrder.Machine.epsilonStep?_target_lt hstep
          simp only [DPDAToFirstOrder.stabilize, hstep]
          exact
            (configurationTerm_epsilon_unfoldingEquivalent
              machine hq hZ htail hstep).trans
              (ih htarget htail)

private theorem stabilize_eq_cons_stable
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet) :
    ∀ {q : ℕ} {stack : List ℕ}
      {state Z : ℕ} {tail : List ℕ},
      DPDAToFirstOrder.stabilize machine (q, stack) =
        (state, Z :: tail) →
      DPDAToFirstOrder.Machine.epsilonStep?
        machine state Z = none := by
  intro q stack
  induction stack generalizing q with
  | nil =>
      intro state Z tail hresult
      simp [DPDAToFirstOrder.stabilize] at hresult
  | cons top stack ih =>
      intro state Z tail hresult
      cases hstep :
          DPDAToFirstOrder.Machine.epsilonStep? machine q top with
      | none =>
          simp only [DPDAToFirstOrder.stabilize, hstep] at hresult
          injection hresult with hstate hstack
          subst state
          have htop : Z = top := by
            simpa using (congrArg List.head? hstack).symm
          subst Z
          exact hstep
      | some out =>
          rcases out with ⟨target, replacement⟩
          have hempty : replacement = [] :=
            DPDAToFirstOrder.Machine.epsilonStep?_replacement_eq_nil_of_poppingComplete
              hnormal hstep
          subst replacement
          simp only [DPDAToFirstOrder.stabilize, hstep] at hresult
          exact ih hresult

/-- One normalized observable DPDA action is simulated by one compressed
grammar rewrite, even when the source first performs forced epsilon pops. -/
public theorem grammar_rootRewrite?_of_observableStep
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ}
    (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    {action : Action}
    {targetConfiguration : DPDAToFirstOrder.Configuration}
    (hstep :
      DPDAToFirstOrder.observableStep? machine action (q, stack) =
        some targetConfiguration) :
    ∃ result,
      (grammar machine).rootRewrite? action
          (configurationTerm machine q stack) =
        some result ∧
      result.UnfoldingEquivalent
        (configurationTerm machine targetConfiguration.1
          targetConfiguration.2) := by
  have hstableValid :=
    DPDAToFirstOrder.stabilize_preserves_valid
      hnormal hq hstack
  cases hstable :
      DPDAToFirstOrder.stabilize machine (q, stack) with
  | mk stableState stableStack =>
      have hstableState : stableState < machine.numStates := by
        simpa [hstable] using hstableValid.1
      have hstableStack : ∀ symbol ∈ stableStack,
          symbol < machine.numStackSymbols := by
        simpa [hstable] using hstableValid.2
      cases stableStack with
      | nil =>
          unfold DPDAToFirstOrder.observableStep? at hstep
          rw [hstable] at hstep
          simp at hstep
      | cons top tail =>
          have htop : top < machine.numStackSymbols :=
            hstableStack top (by simp)
          have htail : ∀ symbol ∈ tail,
              symbol < machine.numStackSymbols := by
            intro symbol hsymbol
            exact hstableStack symbol (by simp [hsymbol])
          have hstableHead :
              DPDAToFirstOrder.Machine.epsilonStep?
                machine stableState top = none :=
            stabilize_eq_cons_stable hnormal hstable
          unfold DPDAToFirstOrder.observableStep? at hstep
          rw [hstable] at hstep
          obtain ⟨out, hinput, hout⟩ :=
            Option.map_eq_some_iff.mp hstep
          rcases out with ⟨target, replacement⟩
          have hconfiguration :
              (target, replacement ++ tail) =
                targetConfiguration := hout
          subst targetConfiguration
          obtain ⟨stableResult, hstableRewrite,
              hstableResult⟩ :=
            grammar_rootRewrite?_of_inputStep
              machine hnormal hstableState htop htail
              hstableHead hinput
          have hsourceStable :=
            configurationTerm_stabilize_unfoldingEquivalent
              hnormal hq hstack
          have hsourceStable' :
              (configurationTerm machine q stack).UnfoldingEquivalent
              (configurationTerm machine stableState
                (top :: tail)) := by
            simpa [hstable] using hsourceStable
          have hsourceClosed :
              (configurationTerm machine q stack).ReferenceClosed :=
            RegularTerm.referenceClosed_of_wellFormed
              (configurationTerm_wellFormed machine hq hstack)
          have hstableClosed :
              (configurationTerm machine stableState
                (top :: tail)).ReferenceClosed :=
            RegularTerm.referenceClosed_of_wellFormed
              (configurationTerm_wellFormed machine
                hstableState hstableStack)
          have hcongruence :=
            EncodedFirstOrderGrammar.rootRewrite?_respects_unfoldingEquivalent
              (g := grammar machine) (a := action)
              hsourceStable' hsourceClosed hstableClosed
              (fun X nextAction rhs hlookup =>
                EncodedFirstOrderGrammar.selected_rhs_referenceClosed
                  (grammar_wellFormed machine) hlookup)
          rw [hstableRewrite] at hcongruence
          cases hsourceRewrite :
              (grammar machine).rootRewrite? action
                (configurationTerm machine q stack) with
          | none =>
              simp [hsourceRewrite] at hcongruence
          | some result =>
              have hresult :
                  result.UnfoldingEquivalent stableResult := by
                simpa [hsourceRewrite] using hcongruence
              exact ⟨result, rfl,
                hresult.trans hstableResult⟩

public theorem grammar_ruleLookup_bottomSymbol_none
    (machine : EncodedDPDA Action) (action : Action) :
    (grammar machine).ruleLookup
      (bottomSymbol machine) action = none := by
  unfold EncodedFirstOrderGrammar.ruleLookup
  cases hfind : (grammar machine).findRule
      (bottomSymbol machine) action with
  | none => rfl
  | some rule =>
      have hruleMem :=
        EncodedFirstOrderGrammar.findRule_mem hfind
      have hkey :=
        EncodedFirstOrderGrammar.findRule_key hfind
      change rule ∈
        (DPDAToFirstOrder.inputKeys machine).filterMap
          (ruleForKey machine) at hruleMem
      rw [List.mem_filterMap] at hruleMem
      obtain ⟨key, hkeyMem, hcompiled⟩ := hruleMem
      have hcompiledKey := ruleForKey_some_key hcompiled
      obtain ⟨hq, hZ⟩ :=
        DPDAToFirstOrder.inputKey_bounds machine hkeyMem
      have hhead := headSymbol_lt_bottom machine hq hZ
      have hfalse :
          headSymbol machine key.1 key.2.2 =
            bottomSymbol machine :=
        hcompiledKey.1.symm.trans hkey.1
      omega

public theorem configurationTerm_nil_rootRewrite?_eq_none
    (machine : EncodedDPDA Action)
    {q : ℕ} (hq : q < machine.numStates)
    (action : Action) :
    (grammar machine).rootRewrite? action
      (configurationTerm machine q []) = none := by
  have hroot :
      (configurationTerm machine q []).rootApplication? =
        some (bottomSymbol machine, []) := by
    simp [configurationTerm, groundBaseLayer,
      RegularTerm.rootApplication?, RegularTerm.rootNode?,
      RegularTerm.nodeAt?, RegularTerm.root,
      RegularTerm.nodes, hq]
  unfold EncodedFirstOrderGrammar.rootRewrite?
  simp [hroot, grammar_ruleLookup_bottomSymbol_none]

/-- Enabled compressed grammar actions are exactly enabled normalized
observable DPDA actions. -/
public theorem
    grammar_rootRewrite?_isSome_iff_observableStep?_isSome
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ}
    (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    (action : Action) :
    ((grammar machine).rootRewrite? action
        (configurationTerm machine q stack)).isSome = true ↔
      (DPDAToFirstOrder.observableStep?
        machine action (q, stack)).isSome = true := by
  constructor
  · intro hgrammar
    have hstableValid :=
      DPDAToFirstOrder.stabilize_preserves_valid
        hnormal hq hstack
    cases hstable :
        DPDAToFirstOrder.stabilize machine (q, stack) with
    | mk stableState stableStack =>
        have hstableState :
            stableState < machine.numStates := by
          simpa [hstable] using hstableValid.1
        have hstableStack : ∀ symbol ∈ stableStack,
            symbol < machine.numStackSymbols := by
          simpa [hstable] using hstableValid.2
        cases stableStack with
        | nil =>
            have hsourceStable :=
              configurationTerm_stabilize_unfoldingEquivalent
                hnormal hq hstack
            have hsourceStable' :
                (configurationTerm machine q stack).UnfoldingEquivalent
                (configurationTerm machine stableState []) := by
              simpa [hstable] using hsourceStable
            have hsourceClosed :
                (configurationTerm machine q stack).ReferenceClosed :=
              RegularTerm.referenceClosed_of_wellFormed
                (configurationTerm_wellFormed
                  machine hq hstack)
            have hstableClosed :
                (configurationTerm machine stableState []).ReferenceClosed :=
              RegularTerm.referenceClosed_of_wellFormed
                (configurationTerm_wellFormed
                  machine hstableState (by simp))
            have hcongruence :=
              EncodedFirstOrderGrammar.rootRewrite?_respects_unfoldingEquivalent
                (g := grammar machine) (a := action)
                hsourceStable' hsourceClosed hstableClosed
                (fun X nextAction rhs hlookup =>
                  EncodedFirstOrderGrammar.selected_rhs_referenceClosed
                    (grammar_wellFormed machine) hlookup)
            rw [configurationTerm_nil_rootRewrite?_eq_none
              machine hstableState action] at hcongruence
            cases hsource :
                (grammar machine).rootRewrite? action
                  (configurationTerm machine q stack) with
            | none =>
                simp [hsource] at hgrammar
            | some result =>
                simp [hsource] at hcongruence
        | cons top tail =>
            have htop : top < machine.numStackSymbols :=
              hstableStack top (by simp)
            have hstableHead :
                DPDAToFirstOrder.Machine.epsilonStep?
                  machine stableState top = none :=
              stabilize_eq_cons_stable hnormal hstable
            obtain ⟨out, hinput⟩ :=
              DPDAToFirstOrder.Machine.inputStep?_exists_of_poppingComplete
                hnormal hstableState htop hstableHead action
            unfold DPDAToFirstOrder.observableStep?
            simp [hstable, hinput]
  · intro hobservable
    cases hstep :
        DPDAToFirstOrder.observableStep?
          machine action (q, stack) with
    | none =>
        simp [hstep] at hobservable
    | some targetConfiguration =>
        obtain ⟨result, hrewrite, _⟩ :=
          grammar_rootRewrite?_of_observableStep
            hnormal hq hstack hstep
        simp [hrewrite]

private theorem grammar_traceEquivalent_of_unfoldingEquivalent
    (machine : EncodedDPDA Action)
    {left right : RegularTerm}
    (hleft : left.ReferenceClosed)
    (hright : right.ReferenceClosed)
    (hequivalent : left.UnfoldingEquivalent right) :
    (grammar machine).TraceEquivalent left right := by
  rw [EncodedFirstOrderGrammar.traceEquivalent_iff_forall_traceApprox]
  intro n
  exact
    (EncodedFirstOrderGrammar.guardedContextLaws_of_wellFormed
      (grammar_wellFormed machine)).unfoldingApprox
        n left right hleft hright hequivalent

/-- Ordinary compressed-grammar traces are exactly the normalized DPDA's
observable traces. -/
public theorem grammar_isTrace_map_inl_iff
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ}
    (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    (word : List Action) :
    (grammar machine).IsTrace
        (configurationTerm machine q stack)
        (word.map Sum.inl) ↔
      DPDAToFirstOrder.IsObservableTrace
        machine (q, stack) word := by
  induction word generalizing q stack with
  | nil =>
      unfold EncodedFirstOrderGrammar.IsTrace
        DPDAToFirstOrder.IsObservableTrace
      rfl
  | cons action word ih =>
      cases hobservable :
          DPDAToFirstOrder.observableStep?
            machine action (q, stack) with
      | none =>
          cases hgrammar :
              (grammar machine).rootRewrite? action
                (configurationTerm machine q stack) with
          | none =>
              unfold EncodedFirstOrderGrammar.IsTrace
                DPDAToFirstOrder.IsObservableTrace
              simp only [List.map_cons,
                EncodedFirstOrderGrammar.run?_cons,
                EncodedFirstOrderGrammar.step?,
                DPDAToFirstOrder.observableRun?]
              rw [hgrammar, hobservable]
              rfl
          | some result =>
              have hgrammarEnabled :
                  ((grammar machine).rootRewrite? action
                    (configurationTerm machine q stack)).isSome = true := by
                simp [hgrammar]
              have hobservableEnabled :=
                (grammar_rootRewrite?_isSome_iff_observableStep?_isSome
                  hnormal hq hstack action).mp hgrammarEnabled
              simp [hobservable] at hobservableEnabled
      | some target =>
          obtain ⟨result, hrewrite, hresult⟩ :=
            grammar_rootRewrite?_of_observableStep
              hnormal hq hstack hobservable
          have htargetValid :=
            DPDAToFirstOrder.observableStep_preserves_valid
              hnormal hq hstack hobservable
          have hsourceClosed :
              (configurationTerm machine q stack).ReferenceClosed :=
            RegularTerm.referenceClosed_of_wellFormed
              (configurationTerm_wellFormed
                machine hq hstack)
          have hresultClosed : result.ReferenceClosed :=
            EncodedFirstOrderGrammar.step?_preserves_referenceClosed
              (label := (.inl action))
              (grammar_wellFormed machine) hsourceClosed hrewrite
          have htargetClosed :
              (configurationTerm machine
                target.1 target.2).ReferenceClosed :=
            RegularTerm.referenceClosed_of_wellFormed
              (configurationTerm_wellFormed machine
                htargetValid.1 htargetValid.2)
          have htraceEquivalent :=
            grammar_traceEquivalent_of_unfoldingEquivalent
              machine hresultClosed htargetClosed hresult
          have hleftReduce :
              (grammar machine).IsTrace
                  (configurationTerm machine q stack)
                  (Sum.inl action :: word.map Sum.inl) ↔
                (grammar machine).IsTrace result
                  (word.map Sum.inl) := by
            rw [EncodedFirstOrderGrammar.isTrace_cons_iff]
            simp [EncodedFirstOrderGrammar.Step,
              EncodedFirstOrderGrammar.step?, hrewrite]
          have hrightReduce :
              DPDAToFirstOrder.IsObservableTrace
                  machine (q, stack) (action :: word) ↔
                DPDAToFirstOrder.IsObservableTrace
                  machine target word := by
            unfold DPDAToFirstOrder.IsObservableTrace
            simp [DPDAToFirstOrder.observableRun?, hobservable]
          simp only [List.map_cons]
          rw [hleftReduce, hrightReduce]
          have hresultTrace :
              (grammar machine).IsTrace result
                  (word.map Sum.inl) ↔
                (grammar machine).IsTrace
                  (configurationTerm machine
                    target.1 target.2)
                  (word.map Sum.inl) := by
            change word.map Sum.inl ∈
                (grammar machine).traceLanguage result ↔
              word.map Sum.inl ∈
                (grammar machine).traceLanguage
                  (configurationTerm machine
                    target.1 target.2)
            rw [htraceEquivalent]
          exact hresultTrace.trans
            (ih htargetValid.1 htargetValid.2)

private theorem configurationTerm_privateStep?_eq_none
    (machine : EncodedDPDA Action)
    {q : ℕ} {stack : List ℕ}
    (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    (x : ℕ) :
    (grammar machine).step? (.inr x)
      (configurationTerm machine q stack) = none := by
  obtain ⟨_, support, _, hwitness⟩ :=
    configurationTerm_ground machine hq hstack
  obtain ⟨X, children, hrootNode, _⟩ :=
    hwitness.2 _ hwitness.1
  unfold EncodedFirstOrderGrammar.step?
  have hroot :
      (configurationTerm machine q stack).rootNode? =
        some (.inr (X, children)) := by
    simpa [RegularTerm.rootNode?] using hrootNode
  simp [hroot]

private theorem grammar_trace_has_ordinary_word
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet) :
    ∀ {q : ℕ} {stack : List ℕ},
      q < machine.numStates →
      (∀ symbol ∈ stack,
        symbol < machine.numStackSymbols) →
      ∀ labels : List (Label Action),
        (grammar machine).IsTrace
          (configurationTerm machine q stack) labels →
        ∃ word : List Action,
          labels = word.map Sum.inl := by
  intro q stack hq hstack labels
  induction labels generalizing q stack with
  | nil =>
      intro _
      exact ⟨[], rfl⟩
  | cons label labels ih =>
      intro htrace
      rw [EncodedFirstOrderGrammar.isTrace_cons_iff] at htrace
      obtain ⟨result, hstep, htailTrace⟩ := htrace
      cases label with
      | inr x =>
          unfold EncodedFirstOrderGrammar.Step at hstep
          rw [configurationTerm_privateStep?_eq_none
            machine hq hstack x] at hstep
          simp at hstep
      | inl action =>
          have hrewrite :
              (grammar machine).rootRewrite? action
                (configurationTerm machine q stack) =
              some result := by
            simpa [EncodedFirstOrderGrammar.Step,
              EncodedFirstOrderGrammar.step?] using hstep
          have hgrammarEnabled :
              ((grammar machine).rootRewrite? action
                (configurationTerm machine q stack)).isSome = true := by
            simp [hrewrite]
          have hobservableEnabled :=
            (grammar_rootRewrite?_isSome_iff_observableStep?_isSome
              hnormal hq hstack action).mp hgrammarEnabled
          cases hobservable :
              DPDAToFirstOrder.observableStep?
                machine action (q, stack) with
          | none =>
              simp [hobservable] at hobservableEnabled
          | some target =>
              obtain ⟨simulated, hsimulatedRewrite,
                  hsimulated⟩ :=
                grammar_rootRewrite?_of_observableStep
                  hnormal hq hstack hobservable
              have hresultEq : result = simulated :=
                Option.some.inj
                  (hrewrite.symm.trans hsimulatedRewrite)
              subst simulated
              have htargetValid :=
                DPDAToFirstOrder.observableStep_preserves_valid
                  hnormal hq hstack hobservable
              have hsourceClosed :
                  (configurationTerm machine q stack).ReferenceClosed :=
                RegularTerm.referenceClosed_of_wellFormed
                  (configurationTerm_wellFormed
                    machine hq hstack)
              have hresultClosed : result.ReferenceClosed :=
                EncodedFirstOrderGrammar.step?_preserves_referenceClosed
                  (label := (.inl action))
                  (grammar_wellFormed machine)
                  hsourceClosed hrewrite
              have htargetClosed :
                  (configurationTerm machine
                    target.1 target.2).ReferenceClosed :=
                RegularTerm.referenceClosed_of_wellFormed
                  (configurationTerm_wellFormed machine
                    htargetValid.1 htargetValid.2)
              have htraceEquivalent :=
                grammar_traceEquivalent_of_unfoldingEquivalent
                  machine hresultClosed htargetClosed hsimulated
              have htargetTrace :
                  (grammar machine).IsTrace
                    (configurationTerm machine
                      target.1 target.2) labels := by
                change labels ∈
                  (grammar machine).traceLanguage
                    (configurationTerm machine
                      target.1 target.2)
                rw [← htraceEquivalent]
                exact htailTrace
              obtain ⟨word, hlabels⟩ :=
                ih htargetValid.1 htargetValid.2 htargetTrace
              exact ⟨action :: word, by simp [hlabels]⟩

/-- Full compressed-grammar traces contain no private variable labels and are
precisely the ordinary-label images of observable DPDA words. -/
public theorem grammar_isTrace_iff_exists_observableWord
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ}
    (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    (labels : List (Label Action)) :
    (grammar machine).IsTrace
        (configurationTerm machine q stack) labels ↔
      ∃ word : List Action,
        labels = word.map Sum.inl ∧
          DPDAToFirstOrder.IsObservableTrace
            machine (q, stack) word := by
  constructor
  · intro htrace
    obtain ⟨word, hlabels⟩ :=
      grammar_trace_has_ordinary_word
        hnormal hq hstack labels htrace
    refine ⟨word, hlabels, ?_⟩
    apply (grammar_isTrace_map_inl_iff
      hnormal hq hstack word).mp
    simpa [hlabels] using htrace
  · rintro ⟨word, rfl, hobservable⟩
    exact (grammar_isTrace_map_inl_iff
      hnormal hq hstack word).mpr hobservable

/-- Trace equivalence of two compressed configuration terms is exactly
observable-trace equivalence of the represented configurations. -/
public theorem
    configurationTerm_traceEquivalent_iff_observableTraceEquivalent
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {left right : DPDAToFirstOrder.Configuration}
    (hleftState : left.1 < machine.numStates)
    (hleftStack : ∀ symbol ∈ left.2,
      symbol < machine.numStackSymbols)
    (hrightState : right.1 < machine.numStates)
    (hrightStack : ∀ symbol ∈ right.2,
      symbol < machine.numStackSymbols) :
    (grammar machine).TraceEquivalent
        (configurationTerm machine left.1 left.2)
        (configurationTerm machine right.1 right.2) ↔
      DPDAToFirstOrder.ObservableTraceEquivalent
        machine left right := by
  constructor
  · intro hgrammar word
    have hgrammarWord :
        (grammar machine).IsTrace
            (configurationTerm machine left.1 left.2)
            (word.map Sum.inl) ↔
          (grammar machine).IsTrace
            (configurationTerm machine right.1 right.2)
            (word.map Sum.inl) := by
      change word.map Sum.inl ∈
          (grammar machine).traceLanguage
            (configurationTerm machine left.1 left.2) ↔
        word.map Sum.inl ∈
          (grammar machine).traceLanguage
            (configurationTerm machine right.1 right.2)
      rw [hgrammar]
    exact
      (grammar_isTrace_map_inl_iff
        hnormal hleftState hleftStack word).symm.trans
        (hgrammarWord.trans
          (grammar_isTrace_map_inl_iff
            hnormal hrightState hrightStack word))
  · intro hobservable
    apply Set.ext
    intro labels
    change (grammar machine).IsTrace
        (configurationTerm machine left.1 left.2) labels ↔
      (grammar machine).IsTrace
        (configurationTerm machine right.1 right.2) labels
    rw [grammar_isTrace_iff_exists_observableWord
        hnormal hleftState hleftStack,
      grammar_isTrace_iff_exists_observableWord
        hnormal hrightState hrightStack]
    constructor
    · rintro ⟨word, hlabels, htrace⟩
      exact ⟨word, hlabels, (hobservable word).mp htrace⟩
    · rintro ⟨word, hlabels, htrace⟩
      exact ⟨word, hlabels, (hobservable word).mpr htrace⟩

/-- Pair-level semantic endpoint of the compressed translation. -/
public theorem
    configurationTerm_traceEquivalent_iff_emptyStackLanguage_eq
    {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    (witness : Action)
    {left right : DPDAToFirstOrder.Configuration}
    (hleftState : left.1 < machine.numStates)
    (hleftStack : ∀ symbol ∈ left.2,
      symbol < machine.numStackSymbols)
    (hrightState : right.1 < machine.numStates)
    (hrightStack : ∀ symbol ∈ right.2,
      symbol < machine.numStackSymbols) :
    (grammar machine).TraceEquivalent
        (configurationTerm machine left.1 left.2)
        (configurationTerm machine right.1 right.2) ↔
      DPDAToFirstOrder.emptyStackLanguage machine left =
        DPDAToFirstOrder.emptyStackLanguage machine right := by
  rw [configurationTerm_traceEquivalent_iff_observableTraceEquivalent
    hnormal hleftState hleftStack hrightState hrightStack]
  exact
    (DPDAToFirstOrder.emptyStackLanguage_eq_iff_observableTraceEquivalent
      hnormal witness hleftState hleftStack
      hrightState hrightStack).symm

/-- Structural validity package needed by the exposing first-order decision
procedure. -/
public theorem grammar_wellFormed_and_exposingNormalForm
    (machine : EncodedDPDA Action)
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet) :
    (grammar machine).WellFormed ∧
      (grammar machine).ExposingNormalForm :=
  ⟨grammar_wellFormed machine,
    grammar_exposingNormalForm machine hnormal⟩

/-- Complete validity data for a translated pair, stated without depending on
the downstream `ValidExposingTracePair` wrapper. -/
public theorem configurationTracePair_valid
    (machine : EncodedDPDA Action)
    {alphabet : List Action}
    (hnormal :
      DPDAToFirstOrder.Machine.PoppingComplete machine alphabet)
    {left right : DPDAToFirstOrder.Configuration}
    (hleftState : left.1 < machine.numStates)
    (hleftStack : ∀ symbol ∈ left.2,
      symbol < machine.numStackSymbols)
    (hrightState : right.1 < machine.numStates)
    (hrightStack : ∀ symbol ∈ right.2,
      symbol < machine.numStackSymbols) :
    (grammar machine).WellFormed ∧
      (grammar machine).ActionDeterministic ∧
      (configurationTerm machine left.1 left.2).Ground
        (grammar machine).ranks ∧
      (configurationTerm machine right.1 right.2).Ground
        (grammar machine).ranks ∧
      (grammar machine).ExposingNormalForm := by
  exact ⟨grammar_wellFormed machine,
    grammar_actionDeterministicCode machine,
    configurationTerm_ground machine hleftState hleftStack,
    configurationTerm_ground machine hrightState hrightStack,
    grammar_exposingNormalForm machine hnormal⟩

end DPDAToExposingFirstOrder

end DCFEquivalence
