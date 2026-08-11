module

public import Langlib.Classes.DeterministicContextFree.Basics.EncodedDPDA
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GroundPreservation
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GuardedContextOperational
public import Mathlib.Data.List.Dedup

@[expose]
public section

/-!
# Effective DPDA-to-first-order-grammar translation

This file formalizes Appendix 1 of Jančar, arXiv:1010.4760v4.  The concrete
translation starts from the effective target normal form used there:

* every epsilon transition pops exactly one stack symbol;
* a head with an epsilon transition has no input transition (already enforced
  by `DPDA.no_mixed`);
* every stable head has an input transition for every input letter.

The arbitrary-DPDA preprocessing which produces this target is deliberately a
separate theorem boundary.  Thus the later equivalence result cannot silently
assume the paper's "standard polynomial-time algorithm".
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDAToFirstOrder

variable {Action : Type}

/-! ## Executable popping/complete target normal form -/

namespace Machine

/-- Selected epsilon transition, projected back to normalized natural indices.
The replacement is retained so the popping condition can be checked. -/
@[expose] public def epsilonStep? [DecidableEq Action]
    (machine : EncodedDPDA Action) (q Z : ℕ) :
    Option (ℕ × List ℕ) :=
  (machine.epsilonLookup (machine.state q) (machine.stackSymbol Z)).map
    fun out => (out.1.val, out.2.map Fin.val)

/-- Selected input transition, projected back to normalized natural indices. -/
@[expose] public def inputStep? [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) (action : Action) (Z : ℕ) :
    Option (ℕ × List ℕ) :=
  (machine.inputLookup (machine.state q) action
      (machine.stackSymbol Z)).map
    fun out => (out.1.val, out.2.map Fin.val)

/-- All selected epsilon rows are popping.  Checking every raw row is slightly
stronger than necessary for duplicate shadowed rows and gives a canonical,
fully executable target presentation. -/
@[expose] public def epsilonPoppingCode
    (machine : EncodedDPDA Action) : Bool :=
  machine.epsilonRows.all fun row => row.2.2.2.isEmpty

/-- Every stable normalized head has a selected transition for every action in
the supplied finite alphabet list.  Carrying that list explicitly keeps the
normal-form checker executable; `Finset.univ.toList` is noncomputable for an
abstract `Fintype`. -/
@[expose] public def stableCompleteCode [DecidableEq Action]
    (machine : EncodedDPDA Action) (alphabet : List Action) : Bool :=
  (List.range machine.numStates).all fun q =>
    (List.range machine.numStackSymbols).all fun Z =>
      match epsilonStep? machine q Z with
      | some _ => true
      | none => alphabet.all fun action =>
          (inputStep? machine q action Z).isSome

/-- Executable target-normal-form check used by the Appendix-1 translation. -/
@[expose] public def poppingCompleteCode [DecidableEq Action]
    (machine : EncodedDPDA Action) (alphabet : List Action) : Bool :=
  epsilonPoppingCode machine && stableCompleteCode machine alphabet

/-- Semantic spelling of the executable target-normal-form promise. -/
@[expose] public def PoppingComplete [DecidableEq Action]
    (machine : EncodedDPDA Action) (alphabet : List Action) : Prop :=
  poppingCompleteCode machine alphabet = true ∧
    ∀ action, action ∈ alphabet

public theorem poppingComplete_iff [DecidableEq Action]
    (machine : EncodedDPDA Action) (alphabet : List Action) :
    PoppingComplete machine alphabet ↔
      epsilonPoppingCode machine = true ∧
        stableCompleteCode machine alphabet = true ∧
        ∀ action, action ∈ alphabet := by
  simp [PoppingComplete, poppingCompleteCode, and_assoc]

/-- The executable completeness check supplies a transition at every stable,
in-range head and every action of the represented alphabet. -/
public theorem inputStep?_exists_of_poppingComplete
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action} (hnormal : PoppingComplete machine alphabet)
    {q Z : ℕ} (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols)
    (hstable : epsilonStep? machine q Z = none)
    (action : Action) :
    ∃ out, inputStep? machine q action Z = some out := by
  have hcomplete := (poppingComplete_iff machine alphabet).mp hnormal |>.2.1
  unfold stableCompleteCode at hcomplete
  have hqCode := (List.all_eq_true.mp hcomplete) q
    (List.mem_range.mpr hq)
  have hZCode := (List.all_eq_true.mp hqCode) Z
    (List.mem_range.mpr hZ)
  have haCode := (List.all_eq_true.mp (by
    simpa [hstable] using hZCode)) action (hnormal.2 action)
  cases hstep : inputStep? machine q action Z with
  | none => simp [hstep] at haCode
  | some out => exact ⟨out, rfl⟩

/-- Every selected epsilon transition in a checked target machine really pops
the current top symbol. -/
public theorem epsilonStep?_replacement_eq_nil_of_poppingComplete
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action} (hnormal : PoppingComplete machine alphabet)
    {q Z target : ℕ} {replacement : List ℕ}
    (hstep : epsilonStep? machine q Z = some (target, replacement)) :
    replacement = [] := by
  have hpopping := (poppingComplete_iff machine alphabet).mp hnormal |>.1
  unfold epsilonPoppingCode at hpopping
  unfold epsilonStep? at hstep
  obtain ⟨out, hlookup, hout⟩ := Option.map_eq_some_iff.mp hstep
  unfold DCFEncodedDPDA.EncodedDPDA.epsilonLookup at hlookup
  obtain ⟨row, hfind, hrowOut⟩ := Option.map_eq_some_iff.mp hlookup
  have hrowMem : row ∈ machine.epsilonRows :=
    List.mem_of_find?_eq_some hfind
  have hempty := (List.all_eq_true.mp hpopping) row hrowMem
  rcases row with ⟨source, top, rowTarget, rowReplacement⟩
  have hrowReplacement : rowReplacement = [] := by
    simpa using hempty
  subst rowReplacement
  simp [DCFEncodedDPDA.EncodedDPDA.replacement] at hrowOut
  subst out
  simpa using congrArg Prod.snd hout

public theorem epsilonStep?_target_lt [DecidableEq Action]
    {machine : EncodedDPDA Action} {q Z target : ℕ}
    {replacement : List ℕ}
    (hstep : epsilonStep? machine q Z = some (target, replacement)) :
    target < machine.numStates := by
  unfold epsilonStep? at hstep
  obtain ⟨out, _, hout⟩ := Option.map_eq_some_iff.mp hstep
  have htarget : out.1.val = target := by
    simpa using congrArg Prod.fst hout
  rw [← htarget]
  exact out.1.isLt

public theorem inputStep?_target_lt [DecidableEq Action]
    {machine : EncodedDPDA Action} {q Z target : ℕ}
    {action : Action} {replacement : List ℕ}
    (hstep : inputStep? machine q action Z =
      some (target, replacement)) :
    target < machine.numStates := by
  unfold inputStep? at hstep
  obtain ⟨out, _, hout⟩ := Option.map_eq_some_iff.mp hstep
  have htarget : out.1.val = target := by
    simpa using congrArg Prod.fst hout
  rw [← htarget]
  exact out.1.isLt

public theorem inputStep?_replacement_lt [DecidableEq Action]
    {machine : EncodedDPDA Action} {q Z target : ℕ}
    {action : Action} {replacement : List ℕ}
    (hstep : inputStep? machine q action Z =
      some (target, replacement)) :
    ∀ symbol ∈ replacement, symbol < machine.numStackSymbols := by
  unfold inputStep? at hstep
  obtain ⟨out, _, hout⟩ := Option.map_eq_some_iff.mp hstep
  have hreplacement : out.2.map Fin.val = replacement := by
    simpa using congrArg Prod.snd hout
  rw [← hreplacement]
  intro symbol hsymbol
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hsymbol
  exact source.isLt

end Machine

/-! ## Finite graph construction for `T(qαx)` -/

/-- The grammar symbol representing a stable DPDA head `(q,Z)`. -/
@[expose] public def headSymbol (machine : EncodedDPDA Action)
    (q Z : ℕ) : ℕ :=
  q * machine.numStackSymbols + Z

/-- The special nullary stuck symbol `⊥`. -/
@[expose] public def bottomSymbol (machine : EncodedDPDA Action) : ℕ :=
  machine.numStates * machine.numStackSymbols

/-- A graph layer stores all nodes allocated so far and, for every control
state, the root reference denoting the already processed stack suffix. -/
public structure TermLayer where
  nodes : List RawNode
  roots : List ℕ
  deriving DecidableEq

/-- At the formal tail `x`, control state `q` denotes variable `x_q`. -/
@[expose] public def baseLayer (machine : EncodedDPDA Action) : TermLayer where
  nodes := (List.range machine.numStates).map Sum.inl
  roots := List.range machine.numStates

/-- Add one stack symbol above a previously translated suffix.  Stable heads
allocate an application node with all state continuations as arguments.
Unstable popping heads simply select the continuation of their epsilon target;
their allocated node is an unreachable variable placeholder. -/
@[expose] public def extendLayer [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) (layer : TermLayer) : TermLayer :=
  let offset := layer.nodes.length
  let newNodes := (List.range machine.numStates).map fun q =>
    match Machine.epsilonStep? machine q Z with
    | some _ => (.inl 0 : RawNode)
    | none => .inr (headSymbol machine q Z, layer.roots)
  let newRoots := (List.range machine.numStates).map fun q =>
    match Machine.epsilonStep? machine q Z with
    | some (target, _) => layer.roots[target]?.getD 0
    | none => offset + q
  ⟨layer.nodes ++ newNodes, newRoots⟩

/-- Process a stack from bottom to top, thereby sharing all state continuations
at each suffix. -/
@[expose] public def stackLayer [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) : TermLayer :=
  stack.reverse.foldl (fun layer Z => extendLayer machine Z layer)
    (baseLayer machine)

/-- Finite schema for the Appendix-1 term `T(qαx)`. -/
@[expose] public def stackSchema [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) (stack : List ℕ) :
    RegularTerm :=
  let layer := stackLayer machine stack
  (layer.nodes, layer.roots[q]?.getD 0)

/-- The special stuck ground term `⊥`. -/
@[expose] public def bottomTerm (machine : EncodedDPDA Action) : RegularTerm :=
  ([.inr (bottomSymbol machine, [])], 0)

/-! ## Executable grammar -/

/-- Normalized input-row key `(q,a,Z)`. -/
public abbrev InputKey (Action : Type) := ℕ × Action × ℕ

/-- The finite list of normalized input keys occurring in the raw table. -/
@[expose] public def inputKeys [DecidableEq Action]
    (machine : EncodedDPDA Action) : List (InputKey Action) :=
  (machine.inputRows.map fun row =>
    (row.1 % machine.numStates, row.2.1,
      row.2.2.1 % machine.numStackSymbols)).dedup

/-- Translate a selected stable input head into one first-order grammar rule. -/
@[expose] public def ruleForKey [DecidableEq Action]
    (machine : EncodedDPDA Action) (key : InputKey Action) :
    Option (RawRule Action) :=
  match Machine.epsilonStep? machine key.1 key.2.2 with
  | some _ => none
  | none =>
      (Machine.inputStep? machine key.1 key.2.1 key.2.2).map fun out =>
        (headSymbol machine key.1 key.2.2, key.2.1,
          stackSchema machine out.1 out.2)

/-- Rank table for all head symbols plus the nullary bottom symbol. -/
@[expose] public def grammarRanks (machine : EncodedDPDA Action) : List ℕ :=
  List.replicate (bottomSymbol machine) machine.numStates ++ [0]

public theorem headSymbol_lt_bottom
    (machine : EncodedDPDA Action) {q Z : ℕ}
    (hq : q < machine.numStates) (hZ : Z < machine.numStackSymbols) :
    headSymbol machine q Z < bottomSymbol machine := by
  have hfirst : q * machine.numStackSymbols + Z <
      (q + 1) * machine.numStackSymbols := by
    rw [Nat.add_mul]
    simpa using Nat.add_lt_add_left hZ (q * machine.numStackSymbols)
  have hsecond : (q + 1) * machine.numStackSymbols ≤
      machine.numStates * machine.numStackSymbols :=
    Nat.mul_le_mul_right machine.numStackSymbols (Nat.succ_le_of_lt hq)
  exact hfirst.trans_le hsecond

public theorem headSymbol_injective_on_bounds
    (machine : EncodedDPDA Action) {q₁ q₂ Z₁ Z₂ : ℕ}
    (_hq₁ : q₁ < machine.numStates) (_hq₂ : q₂ < machine.numStates)
    (hZ₁ : Z₁ < machine.numStackSymbols)
    (hZ₂ : Z₂ < machine.numStackSymbols)
    (heq : headSymbol machine q₁ Z₁ =
      headSymbol machine q₂ Z₂) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  have hpositive := machine.numStackSymbols_pos
  have hdecode : ∀ q Z, Z < machine.numStackSymbols →
      headSymbol machine q Z / machine.numStackSymbols = q := by
    intro q Z hZ
    rw [headSymbol, Nat.mul_comm]
    rw [Nat.mul_add_div hpositive]
    simp [Nat.div_eq_of_lt hZ]
  have hq : q₁ = q₂ := by
    have hdiv := congrArg (· / machine.numStackSymbols) heq
    simpa [hdecode q₁ Z₁ hZ₁, hdecode q₂ Z₂ hZ₂] using hdiv
  subst q₂
  have hZ : Z₁ = Z₂ := by
    unfold headSymbol at heq
    exact Nat.add_left_cancel heq
  exact ⟨rfl, hZ⟩

public theorem grammarRanks_headSymbol
    (machine : EncodedDPDA Action) {q Z : ℕ}
    (hq : q < machine.numStates) (hZ : Z < machine.numStackSymbols) :
    (grammarRanks machine)[headSymbol machine q Z]? =
      some machine.numStates := by
  have hhead := headSymbol_lt_bottom machine hq hZ
  unfold grammarRanks
  rw [List.getElem?_append_left (by simpa using hhead)]
  simp [hhead]

public theorem grammarRanks_bottomSymbol
    (machine : EncodedDPDA Action) :
    (grammarRanks machine)[bottomSymbol machine]? = some 0 := by
  simp [grammarRanks, bottomSymbol]

public theorem inputKey_bounds [DecidableEq Action]
    (machine : EncodedDPDA Action) {key : InputKey Action}
    (hkey : key ∈ inputKeys machine) :
    key.1 < machine.numStates ∧ key.2.2 < machine.numStackSymbols := by
  unfold inputKeys at hkey
  have hmap : key ∈ machine.inputRows.map fun row =>
      (row.1 % machine.numStates, row.2.1,
        row.2.2.1 % machine.numStackSymbols) := by
    exact List.mem_dedup.mp hkey
  obtain ⟨row, _, hrow⟩ := List.mem_map.mp hmap
  subst key
  exact ⟨Nat.mod_lt _ machine.numStates_pos,
    Nat.mod_lt _ machine.numStackSymbols_pos⟩

public theorem inputKey_mem_of_inputStep? [DecidableEq Action]
    (machine : EncodedDPDA Action) {q Z : ℕ} {action : Action}
    {target : ℕ} {replacement : List ℕ}
    (hq : q < machine.numStates) (hZ : Z < machine.numStackSymbols)
    (hstep : Machine.inputStep? machine q action Z =
      some (target, replacement)) :
    (q, action, Z) ∈ inputKeys machine := by
  unfold Machine.inputStep? at hstep
  obtain ⟨out, hlookup, _⟩ := Option.map_eq_some_iff.mp hstep
  unfold DCFEncodedDPDA.EncodedDPDA.inputLookup at hlookup
  obtain ⟨row, hfind, _⟩ := Option.map_eq_some_iff.mp hlookup
  have hrowMem : row ∈ machine.inputRows :=
    List.mem_of_find?_eq_some hfind
  have hmatch := List.find?_some hfind
  have hstate : (machine.state q).val = q := by
    simp [DCFEncodedDPDA.EncodedDPDA.state, Nat.mod_eq_of_lt hq]
  have hstack : (machine.stackSymbol Z).val = Z := by
    simp [DCFEncodedDPDA.EncodedDPDA.stackSymbol, Nat.mod_eq_of_lt hZ]
  change decide (row.1 % machine.numStates = (machine.state q).val ∧
    row.2.1 = action ∧
      row.2.2.1 % machine.numStackSymbols =
        (machine.stackSymbol Z).val) = true at hmatch
  have hparts := of_decide_eq_true hmatch
  unfold inputKeys
  rw [List.mem_dedup]
  apply List.mem_map.mpr
  refine ⟨row, hrowMem, ?_⟩
  simp only [hstate, hstack] at hparts
  rcases hparts with ⟨hqRow, haRow, hZRow⟩
  simp [hqRow, haRow, hZRow]

/-- Deterministic first-order grammar associated with a popping/complete DPDA. -/
@[expose] public def grammar [DecidableEq Action]
    (machine : EncodedDPDA Action) : EncodedFirstOrderGrammar Action :=
  (grammarRanks machine,
    (inputKeys machine).filterMap (ruleForKey machine))

/-! ## Observable semantics of a popping machine -/

/-- A normalized control/stack configuration. -/
public abbrev Configuration := ℕ × List ℕ

/-- Execute the forced epsilon-popping phase.  The recursion is structurally
bounded by the stack because only an actually empty replacement is followed. -/
@[expose] public def stabilize [DecidableEq Action]
    (machine : EncodedDPDA Action) : Configuration → Configuration
  | (q, []) => (q, [])
  | (q, Z :: stack) =>
      match Machine.epsilonStep? machine q Z with
      | some (target, []) => stabilize machine (target, stack)
      | _ => (q, Z :: stack)
termination_by configuration => configuration.2.length

/-- One observable input-labelled move, after exhausting forced epsilon pops. -/
@[expose] public def observableStep? [DecidableEq Action]
    (machine : EncodedDPDA Action) (action : Action)
    (configuration : Configuration) : Option Configuration :=
  match stabilize machine configuration with
  | (_, []) => none
  | (q, Z :: stack) =>
      (Machine.inputStep? machine q action Z).map fun out =>
        (out.1, out.2 ++ stack)

/-- Execute a finite observable word. -/
@[expose] public def observableRun? [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    List Action → Configuration → Option Configuration
  | [], configuration => some configuration
  | action :: word, configuration =>
      (observableStep? machine action configuration).bind
        (observableRun? machine word)

/-- A word is enabled from a popping-machine configuration. -/
@[expose] public def IsObservableTrace [DecidableEq Action]
    (machine : EncodedDPDA Action) (configuration : Configuration)
    (word : List Action) : Prop :=
  (observableRun? machine word configuration).isSome = true

/-- Empty-stack language of a normalized configuration. -/
@[expose] public def emptyStackLanguage [DecidableEq Action]
    (machine : EncodedDPDA Action) (configuration : Configuration) :
    Language Action :=
  {word | ∃ target,
    observableRun? machine word configuration = some target ∧
      (stabilize machine target).2 = []}

/-! ## Ground graph presentation of configurations -/

/-- Base layer for an actual stack: all control states at the empty suffix
point to the single stuck bottom node. -/
@[expose] public def groundBaseLayer
    (machine : EncodedDPDA Action) : TermLayer where
  nodes := [.inr (bottomSymbol machine, [])]
  roots := List.replicate machine.numStates 0

/-- Shared finite graph layer for an actual stack. -/
@[expose] public def configurationLayer [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) : TermLayer :=
  stack.reverse.foldl (fun layer Z => extendLayer machine Z layer)
    (groundBaseLayer machine)

/-- Ground regular term representing the normalized configuration `(q,α)`. -/
@[expose] public def configurationTerm [DecidableEq Action]
    (machine : EncodedDPDA Action) (q : ℕ) (stack : List ℕ) :
    RegularTerm :=
  let layer := configurationLayer machine stack
  (layer.nodes, layer.roots[q]?.getD 0)

@[simp] public theorem stackLayer_nil [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    stackLayer machine [] = baseLayer machine := rfl

public theorem stackLayer_cons [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) (stack : List ℕ) :
    stackLayer machine (Z :: stack) =
      extendLayer machine Z (stackLayer machine stack) := by
  simp [stackLayer, List.foldl_append]

@[simp] public theorem configurationLayer_nil [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    configurationLayer machine [] = groundBaseLayer machine := rfl

public theorem configurationLayer_cons [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) (stack : List ℕ) :
    configurationLayer machine (Z :: stack) =
      extendLayer machine Z (configurationLayer machine stack) := by
  simp [configurationLayer, List.foldl_append]

@[simp] public theorem extendLayer_nodes_length [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) (layer : TermLayer) :
    (extendLayer machine Z layer).nodes.length =
      layer.nodes.length + machine.numStates := by
  simp [extendLayer]

@[simp] public theorem extendLayer_roots_length [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) (layer : TermLayer) :
    (extendLayer machine Z layer).roots.length = machine.numStates := by
  simp [extendLayer]

/-- Every state root in a layer is present and points inside the layer graph. -/
@[expose] public def LayerReferences
    (machine : EncodedDPDA Action) (layer : TermLayer) : Prop :=
  layer.roots.length = machine.numStates ∧
    ∀ root ∈ layer.roots, root < layer.nodes.length

public theorem baseLayer_references (machine : EncodedDPDA Action) :
    LayerReferences machine (baseLayer machine) := by
  constructor
  · simp [baseLayer]
  · intro root hroot
    simp [baseLayer] at hroot ⊢
    exact hroot

public theorem groundBaseLayer_references (machine : EncodedDPDA Action) :
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

public theorem extendLayer_references [DecidableEq Action]
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
    cases hstep : Machine.epsilonStep? machine q Z with
    | none =>
        simp only [hstep] at hrootEq
        subst root
        exact Nat.add_lt_add_left hq layer.nodes.length
    | some out =>
        rcases out with ⟨target, replacement⟩
        simp only [hstep] at hrootEq
        subst root
        have htarget : target < machine.numStates :=
          Machine.epsilonStep?_target_lt hstep
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

public theorem stackLayer_references [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    LayerReferences machine (stackLayer machine stack) := by
  induction stack with
  | nil => exact baseLayer_references machine
  | cons Z stack ih =>
      rw [stackLayer_cons]
      exact extendLayer_references machine Z ih

public theorem configurationLayer_references [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    LayerReferences machine (configurationLayer machine stack) := by
  induction stack with
  | nil => exact groundBaseLayer_references machine
  | cons Z stack ih =>
      rw [configurationLayer_cons]
      exact extendLayer_references machine Z ih

/-- Rank/reference validity of every raw node in a layer, parameterized by the
admissible variables. -/
@[expose] public def LayerNodesValid
    (machine : EncodedDPDA Action) (variableOK : ℕ → Prop)
    (layer : TermLayer) : Prop :=
  ∀ node ∈ layer.nodes,
    match node with
    | .inl x => variableOK x
    | .inr (X, children) =>
        (grammarRanks machine)[X]? = some children.length ∧
          ∀ child ∈ children, child < layer.nodes.length

public theorem baseLayer_nodesValid (machine : EncodedDPDA Action) :
    LayerNodesValid machine (fun x => x < machine.numStates)
      (baseLayer machine) := by
  intro node hnode
  simp only [baseLayer] at hnode
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hnode
  exact List.mem_range.mp hq

public theorem groundBaseLayer_nodesValid (machine : EncodedDPDA Action) :
    LayerNodesValid machine (fun _ => True) (groundBaseLayer machine) := by
  intro node hnode
  have hnodeEq : node = .inr (bottomSymbol machine, []) := by
    simpa [groundBaseLayer] using hnode
  subst node
  exact ⟨by simpa using grammarRanks_bottomSymbol machine, by simp⟩

public theorem extendLayer_nodesValid [DecidableEq Action]
    (machine : EncodedDPDA Action) {variableOK : ℕ → Prop}
    (hzero : variableOK 0) {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    (hvalid : LayerNodesValid machine variableOK layer)
    {Z : ℕ} (hZ : Z < machine.numStackSymbols) :
    LayerNodesValid machine variableOK (extendLayer machine Z layer) := by
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
    cases hstep : Machine.epsilonStep? machine q Z with
    | none =>
        simp only [hstep] at hnodeEq
        subst node
        refine ⟨?_, ?_⟩
        · simpa [hreferences.1] using grammarRanks_headSymbol machine hq hZ
        · intro child hchild
          have hbound := hreferences.2 child hchild
          rw [extendLayer_nodes_length]
          omega
    | some out =>
        simp only [hstep] at hnodeEq
        subst node
        exact hzero

public theorem stackLayer_nodesValid [DecidableEq Action]
    (machine : EncodedDPDA Action) {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    LayerNodesValid machine (fun x => x < machine.numStates)
      (stackLayer machine stack) := by
  induction stack with
  | nil => exact baseLayer_nodesValid machine
  | cons Z stack ih =>
      rw [stackLayer_cons]
      apply extendLayer_nodesValid machine machine.numStates_pos
        (stackLayer_references machine stack)
      · exact ih fun symbol hsymbol => hstack symbol (by simp [hsymbol])
      · exact hstack Z (by simp)

public theorem configurationLayer_nodesValid [DecidableEq Action]
    (machine : EncodedDPDA Action) {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    LayerNodesValid machine (fun _ => True)
      (configurationLayer machine stack) := by
  induction stack with
  | nil => exact groundBaseLayer_nodesValid machine
  | cons Z stack ih =>
      rw [configurationLayer_cons]
      apply extendLayer_nodesValid machine trivial
        (configurationLayer_references machine stack)
      · exact ih fun symbol hsymbol => hstack symbol (by simp [hsymbol])
      · exact hstack Z (by simp)

/-- Every application edge points strictly backward in the node list. -/
@[expose] public def LayerBackward (layer : TermLayer) : Prop :=
  ∀ i X children,
    layer.nodes[i]? = some (Sum.inr (X, children) : RawNode) →
    ∀ child ∈ children, child < i

public theorem baseLayer_backward (machine : EncodedDPDA Action) :
    LayerBackward (baseLayer machine) := by
  intro i X children hnode
  simp [baseLayer, List.getElem?_map] at hnode

public theorem groundBaseLayer_backward (machine : EncodedDPDA Action) :
    LayerBackward (groundBaseLayer machine) := by
  intro i X children hnode child hchild
  have hi : i < 1 := by
    simpa [groundBaseLayer] using (List.getElem?_eq_some_iff.mp hnode).1
  have hizero : i = 0 := by omega
  subst i
  simp [groundBaseLayer] at hnode
  rcases hnode with ⟨rfl, rfl⟩
  simp at hchild

public theorem extendLayer_backward [DecidableEq Action]
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
      simpa [extendLayer, List.getElem?_append_left hprefix] using hnode
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
          match Machine.epsilonStep? machine state Z with
          | some _ => (.inl 0 : RawNode)
          | none => Sum.inr (headSymbol machine state Z, layer.roots))[q]? =
          some (Sum.inr (X, children) : RawNode) := by
      rw [hiSplit] at hnode
      simpa [extendLayer, List.getElem?_append_right] using hnode
    rw [List.getElem?_map] at hnew
    have hqRange : (List.range machine.numStates)[q]? = some q := by
      simp [hq]
    rw [hqRange] at hnew
    cases hstep : Machine.epsilonStep? machine q Z with
    | some out => simp [hstep] at hnew
    | none =>
        simp only [hstep, Option.map_some, Option.some.injEq,
          Sum.inr.injEq, Prod.mk.injEq] at hnew
        rcases hnew with ⟨_, hchildren⟩
        subst children
        have hchildBound := hreferences.2 child hchild
        rw [hiSplit]
        omega

public theorem stackLayer_backward [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    LayerBackward (stackLayer machine stack) := by
  induction stack with
  | nil => exact baseLayer_backward machine
  | cons Z stack ih =>
      rw [stackLayer_cons]
      exact extendLayer_backward machine Z
        (stackLayer_references machine stack) ih

public theorem configurationLayer_backward [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    LayerBackward (configurationLayer machine stack) := by
  induction stack with
  | nil => exact groundBaseLayer_backward machine
  | cons Z stack ih =>
      rw [configurationLayer_cons]
      exact extendLayer_backward machine Z
        (configurationLayer_references machine stack) ih

/-- Every control-state continuation root of a ground layer is an application
node (initially `⊥`, later either a stable head or an earlier continuation). -/
@[expose] public def LayerRootApplications
    (machine : EncodedDPDA Action) (layer : TermLayer) : Prop :=
  ∀ q, q < machine.numStates →
    ∃ root X children, layer.roots[q]? = some root ∧
      layer.nodes[root]? = some (Sum.inr (X, children) : RawNode)

public theorem groundBaseLayer_rootApplications
    (machine : EncodedDPDA Action) :
    LayerRootApplications machine (groundBaseLayer machine) := by
  intro q hq
  refine ⟨0, bottomSymbol machine, [], ?_, ?_⟩
  · simp [groundBaseLayer, hq]
  · simp [groundBaseLayer]

public theorem extendLayer_rootApplications [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) {layer : TermLayer}
    (hroots : LayerRootApplications machine layer) :
    LayerRootApplications machine (extendLayer machine Z layer) := by
  intro q hq
  have hqRange : (List.range machine.numStates)[q]? = some q := by
    simp [hq]
  cases hstep : Machine.epsilonStep? machine q Z with
  | none =>
      refine ⟨layer.nodes.length + q, headSymbol machine q Z,
        layer.roots, ?_, ?_⟩
      · simp [extendLayer, List.getElem?_map, hqRange, hstep]
      · simp only [extendLayer]
        rw [List.getElem?_append_right (by omega)]
        simp [List.getElem?_map, hqRange, hstep]
  | some out =>
      rcases out with ⟨target, replacement⟩
      have htarget : target < machine.numStates :=
        Machine.epsilonStep?_target_lt hstep
      obtain ⟨root, X, children, hrootLookup, hrootNode⟩ :=
        hroots target htarget
      refine ⟨root, X, children, ?_, ?_⟩
      · simp [extendLayer, List.getElem?_map, hqRange, hstep,
          hrootLookup]
      · simp only [extendLayer]
        rw [List.getElem?_append_left
          (List.getElem?_eq_some_iff.mp hrootNode).1]
        exact hrootNode

public theorem configurationLayer_rootApplications [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    LayerRootApplications machine (configurationLayer machine stack) := by
  induction stack with
  | nil => exact groundBaseLayer_rootApplications machine
  | cons Z stack ih =>
      rw [configurationLayer_cons]
      exact extendLayer_rootApplications machine Z ih

/-- Application nodes in a ground layer only point to application nodes.
Variable placeholders allocated for epsilon-popping heads may remain in the
finite graph, but no reachable application edge can enter them. -/
@[expose] public def LayerApplicationsClosed (layer : TermLayer) : Prop :=
  ∀ (i X : ℕ) (children : List ℕ),
    layer.nodes[i]? = some (Sum.inr (X, children) : RawNode) →
    ∀ (child : ℕ), child ∈ children → ∃ Y grandchildren,
      layer.nodes[child]? =
        some (Sum.inr (Y, grandchildren) : RawNode)

public theorem groundBaseLayer_applicationsClosed
    (machine : EncodedDPDA Action) :
    LayerApplicationsClosed (groundBaseLayer machine) := by
  intro i X children hnode child hchild
  have hi : i < 1 := by
    simpa [groundBaseLayer] using (List.getElem?_eq_some_iff.mp hnode).1
  have hizero : i = 0 := by omega
  subst i
  simp [groundBaseLayer] at hnode
  rcases hnode with ⟨rfl, rfl⟩
  simp at hchild

public theorem extendLayer_applicationsClosed [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    (hroots : LayerRootApplications machine layer)
    (hclosed : LayerApplicationsClosed layer) :
    LayerApplicationsClosed (extendLayer machine Z layer) := by
  intro i X children hnode child hchild
  have hi : i < layer.nodes.length + machine.numStates := by
    simpa [extendLayer_nodes_length] using
      (List.getElem?_eq_some_iff.mp hnode).1
  by_cases hprefix : i < layer.nodes.length
  · have hsource : layer.nodes[i]? =
        some (Sum.inr (X, children) : RawNode) := by
      simpa [extendLayer, List.getElem?_append_left hprefix] using hnode
    obtain ⟨Y, grandchildren, hchildNode⟩ :=
      hclosed i X children hsource child hchild
    refine ⟨Y, grandchildren, ?_⟩
    have hchildPrefix := (List.getElem?_eq_some_iff.mp hchildNode).1
    simpa [extendLayer, List.getElem?_append_left hchildPrefix] using
      hchildNode
  · let q := i - layer.nodes.length
    have hq : q < machine.numStates := by
      dsimp [q]
      omega
    have hiSplit : i = layer.nodes.length + q := by
      dsimp [q]
      omega
    have hnew :
        ((List.range machine.numStates).map fun state =>
          match Machine.epsilonStep? machine state Z with
          | some _ => (.inl 0 : RawNode)
          | none => Sum.inr (headSymbol machine state Z, layer.roots))[q]? =
          some (Sum.inr (X, children) : RawNode) := by
      rw [hiSplit] at hnode
      simpa [extendLayer, List.getElem?_append_right] using hnode
    rw [List.getElem?_map] at hnew
    have hqRange : (List.range machine.numStates)[q]? = some q := by
      simp [hq]
    rw [hqRange] at hnew
    cases hstep : Machine.epsilonStep? machine q Z with
    | some out => simp [hstep] at hnew
    | none =>
        simp only [hstep, Option.map_some, Option.some.injEq,
          Sum.inr.injEq, Prod.mk.injEq] at hnew
        rcases hnew with ⟨_, hchildren⟩
        subst children
        obtain ⟨state, hstateBound, hstateGet⟩ :=
          List.mem_iff_getElem.mp hchild
        have hstate : state < machine.numStates := by
          simpa [hreferences.1] using hstateBound
        obtain ⟨root, Y, grandchildren, hrootLookup, hrootNode⟩ :=
          hroots state hstate
        have hchildLookup : layer.roots[state]? = some child := by
          rw [List.getElem?_eq_some_iff]
          exact ⟨hstateBound, hstateGet⟩
        rw [hchildLookup] at hrootLookup
        have hrootEq : root = child := (Option.some.inj hrootLookup).symm
        subst root
        refine ⟨Y, grandchildren, ?_⟩
        have hchildPrefix := (List.getElem?_eq_some_iff.mp hrootNode).1
        simpa [extendLayer, List.getElem?_append_left hchildPrefix] using
          hrootNode

public theorem configurationLayer_applicationsClosed [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    LayerApplicationsClosed (configurationLayer machine stack) := by
  induction stack with
  | nil => exact groundBaseLayer_applicationsClosed machine
  | cons Z stack ih =>
      rw [configurationLayer_cons]
      exact extendLayer_applicationsClosed machine Z
        (configurationLayer_references machine stack)
        (configurationLayer_rootApplications machine stack) ih

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

private theorem layerRoot_getElem?
    {machine : EncodedDPDA Action} {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    {q : ℕ} (hq : q < machine.numStates) :
    ∃ root, layer.roots[q]? = some root ∧ root < layer.nodes.length := by
  have hqRoots : q < layer.roots.length := by simpa [hreferences.1] using hq
  refine ⟨layer.roots[q]'hqRoots, ?_,
    hreferences.2 _ (List.getElem_mem hqRoots)⟩
  rw [List.getElem?_eq_some_iff]
  exact ⟨hqRoots, rfl⟩

private theorem termWellFormed_of_layer
    {machine : EncodedDPDA Action} {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    (hvalid : LayerNodesValid machine
      (fun x => x < machine.numStates) layer)
    {q : ℕ} (hq : q < machine.numStates) :
    RegularTerm.WellFormed (grammarRanks machine) machine.numStates
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

/-- Every generated open stack schema is ranked and uses exactly the state
variables. -/
public theorem stackSchema_wellFormed [DecidableEq Action]
    (machine : EncodedDPDA Action) {q : ℕ} (hq : q < machine.numStates)
    {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    (stackSchema machine q stack).WellFormed
      (grammarRanks machine) machine.numStates := by
  unfold stackSchema
  exact termWellFormed_of_layer (stackLayer_references machine stack)
    (stackLayer_nodesValid machine hstack) hq

/-- The shared DAG schema has a genuinely finite unfolding; every edge points
to a strictly earlier layer node. -/
public theorem stackSchema_unfoldsFiniteCode [DecidableEq Action]
    (machine : EncodedDPDA Action) {q : ℕ} (hq : q < machine.numStates)
    (stack : List ℕ) :
    (stackSchema machine q stack).unfoldsFiniteCode = true := by
  unfold stackSchema
  have hreferences := stackLayer_references machine stack
  obtain ⟨root, hroot, hrootBound⟩ :=
    layerRoot_getElem? hreferences hq
  apply unfoldsFiniteCode_eq_true_of_backward
  · simpa [hroot] using hrootBound
  · exact stackLayer_backward machine stack

private theorem ruleForKey_wellFormedCode [DecidableEq Action]
    (machine : EncodedDPDA Action) {key : InputKey Action}
    (hkey : key ∈ inputKeys machine) {rule : RawRule Action}
    (hrule : ruleForKey machine key = some rule) :
    (grammar machine).ruleWellFormedCode rule = true := by
  obtain ⟨hq, hZ⟩ := inputKey_bounds machine hkey
  unfold ruleForKey at hrule
  cases hepsilon : Machine.epsilonStep? machine key.1 key.2.2 with
  | some out => simp [hepsilon] at hrule
  | none =>
      simp only [hepsilon] at hrule
      cases hinput : Machine.inputStep? machine key.1 key.2.1 key.2.2 with
      | none => simp [hinput] at hrule
      | some out =>
          rcases out with ⟨target, replacement⟩
          simp only [hinput, Option.map_some, Option.some.injEq] at hrule
          subst rule
          have htarget : target < machine.numStates :=
            Machine.inputStep?_target_lt hinput
          have hreplacement : ∀ symbol ∈ replacement,
              symbol < machine.numStackSymbols :=
            Machine.inputStep?_replacement_lt hinput
          unfold EncodedFirstOrderGrammar.ruleWellFormedCode
          change (match (grammar machine).ranks[
              headSymbol machine key.1 key.2.2]? with
            | none => false
            | some rank =>
                (stackSchema machine target replacement).wellFormedCode
                    (grammar machine).ranks rank &&
                  (stackSchema machine target replacement).unfoldsFiniteCode) =
            true
          change (match (grammarRanks machine)[
              headSymbol machine key.1 key.2.2]? with
            | none => false
            | some rank =>
                (stackSchema machine target replacement).wellFormedCode
                    (grammarRanks machine) rank &&
                  (stackSchema machine target replacement).unfoldsFiniteCode) =
            true
          rw [grammarRanks_headSymbol machine hq hZ]
          rw [Bool.and_eq_true]
          exact ⟨stackSchema_wellFormed machine htarget hreplacement,
            stackSchema_unfoldsFiniteCode machine htarget replacement⟩

private theorem ruleForKey_some_key [DecidableEq Action]
    {machine : EncodedDPDA Action} {key : InputKey Action}
    {rule : RawRule Action} (hrule : ruleForKey machine key = some rule) :
    rule.lhs = headSymbol machine key.1 key.2.2 ∧
      rule.action = key.2.1 := by
  unfold ruleForKey at hrule
  cases hepsilon : Machine.epsilonStep? machine key.1 key.2.2 with
  | some out => simp [hepsilon] at hrule
  | none =>
      simp only [hepsilon] at hrule
      cases hinput : Machine.inputStep? machine key.1 key.2.1 key.2.2 with
      | none => simp [hinput] at hrule
      | some out =>
          simp only [hinput, Option.map_some, Option.some.injEq] at hrule
          subst rule
          exact ⟨rfl, rfl⟩

private theorem compiled_rule_key_injective [DecidableEq Action]
    {machine : EncodedDPDA Action} {key₁ key₂ : InputKey Action}
    (hkey₁ : key₁ ∈ inputKeys machine)
    (hkey₂ : key₂ ∈ inputKeys machine)
    {rule₁ rule₂ : RawRule Action}
    (hrule₁ : ruleForKey machine key₁ = some rule₁)
    (hrule₂ : ruleForKey machine key₂ = some rule₂)
    (hlhs : rule₁.lhs = rule₂.lhs)
    (haction : rule₁.action = rule₂.action) :
    key₁ = key₂ := by
  obtain ⟨hq₁, hZ₁⟩ := inputKey_bounds machine hkey₁
  obtain ⟨hq₂, hZ₂⟩ := inputKey_bounds machine hkey₂
  have hcompiled₁ := ruleForKey_some_key hrule₁
  have hcompiled₂ := ruleForKey_some_key hrule₂
  have hhead : headSymbol machine key₁.1 key₁.2.2 =
      headSymbol machine key₂.1 key₂.2.2 := by
    rw [← hcompiled₁.1, ← hcompiled₂.1]
    exact hlhs
  obtain ⟨hq, hZ⟩ := headSymbol_injective_on_bounds machine
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

private theorem compiledRules_actionDeterministicCode [DecidableEq Action]
    (machine : EncodedDPDA Action) : ∀ keys : List (InputKey Action),
    (∀ key ∈ keys, key ∈ inputKeys machine) → keys.Nodup →
    EncodedFirstOrderGrammar.actionDeterministicRulesCode
      (keys.filterMap (ruleForKey machine)) = true := by
  intro keys
  induction keys with
  | nil => simp [EncodedFirstOrderGrammar.actionDeterministicRulesCode]
  | cons key keys ih =>
      intro hsubset hnodup
      have hkey : key ∈ inputKeys machine := hsubset key (by simp)
      have htail : ∀ key' ∈ keys, key' ∈ inputKeys machine := by
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

public theorem grammar_rulesWellFormedCode [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    (grammar machine).rawRules.all (grammar machine).ruleWellFormedCode =
      true := by
  apply List.all_eq_true.mpr
  intro rule hrule
  change rule ∈ (inputKeys machine).filterMap (ruleForKey machine) at hrule
  rw [List.mem_filterMap] at hrule
  obtain ⟨key, hkey, hcompiled⟩ := hrule
  exact ruleForKey_wellFormedCode machine hkey hcompiled

public theorem grammar_actionDeterministicCode [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    (grammar machine).actionDeterministicCode = true := by
  unfold EncodedFirstOrderGrammar.actionDeterministicCode grammar
  apply compiledRules_actionDeterministicCode machine (inputKeys machine)
  · intro key hkey
    exact hkey
  · unfold inputKeys
    exact List.nodup_dedup _

/-- The executable Appendix-1 grammar is a finite, ranked,
action-deterministic first-order grammar. -/
public theorem grammar_wellFormed [DecidableEq Action]
    (machine : EncodedDPDA Action) :
    (grammar machine).WellFormed := by
  unfold EncodedFirstOrderGrammar.WellFormed
    EncodedFirstOrderGrammar.wellFormedCode
  rw [Bool.and_eq_true]
  exact ⟨grammar_rulesWellFormedCode machine,
    grammar_actionDeterministicCode machine⟩

private theorem grammar_rule_unique [DecidableEq Action]
    {machine : EncodedDPDA Action} {left right : RawRule Action}
    (hleft : left ∈ (grammar machine).rawRules)
    (hright : right ∈ (grammar machine).rawRules)
    (hlhs : left.lhs = right.lhs)
    (haction : left.action = right.action) :
    left = right := by
  change left ∈ (inputKeys machine).filterMap (ruleForKey machine) at hleft
  change right ∈ (inputKeys machine).filterMap (ruleForKey machine) at hright
  rw [List.mem_filterMap] at hleft hright
  obtain ⟨leftKey, hleftKey, hleftCompiled⟩ := hleft
  obtain ⟨rightKey, hrightKey, hrightCompiled⟩ := hright
  have hkeys := compiled_rule_key_injective hleftKey hrightKey
    hleftCompiled hrightCompiled hlhs haction
  subst rightKey
  rw [hleftCompiled] at hrightCompiled
  exact Option.some.inj hrightCompiled

/-- Exact selected grammar rule for one stable normalized DPDA input step. -/
public theorem grammar_ruleLookup_of_inputStep? [DecidableEq Action]
    (machine : EncodedDPDA Action) {q Z : ℕ} {action : Action}
    {target : ℕ} {replacement : List ℕ}
    (hq : q < machine.numStates) (hZ : Z < machine.numStackSymbols)
    (hstable : Machine.epsilonStep? machine q Z = none)
    (hinput : Machine.inputStep? machine q action Z =
      some (target, replacement)) :
    (grammar machine).ruleLookup (headSymbol machine q Z) action =
      some (stackSchema machine target replacement) := by
  let key : InputKey Action := (q, action, Z)
  let rule : RawRule Action :=
    (headSymbol machine q Z, action,
      stackSchema machine target replacement)
  have hkey : key ∈ inputKeys machine :=
    inputKey_mem_of_inputStep? machine hq hZ hinput
  have hcompiled : ruleForKey machine key = some rule := by
    simp [ruleForKey, key, rule, hstable, hinput]
  have hruleMem : rule ∈ (grammar machine).rawRules := by
    change rule ∈ (inputKeys machine).filterMap (ruleForKey machine)
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
      have hfoundMem := EncodedFirstOrderGrammar.findRule_mem hfind
      have hfoundKey := EncodedFirstOrderGrammar.findRule_key hfind
      have hfoundEq : found = rule := grammar_rule_unique hfoundMem hruleMem
        (by simpa [rule] using hfoundKey.1)
        (by simpa [rule] using hfoundKey.2)
      subst found
      rfl

/-! ## Groundness of translated configurations -/

/-- The finite support consisting of all application nodes in a term graph. -/
private def applicationSupport (term : RegularTerm) : List ℕ :=
  (List.range term.nodes.length).filter fun i =>
    match term.nodeAt? i with
    | some (.inr _) => true
    | _ => false

private theorem mem_applicationSupport_iff
    {term : RegularTerm} {i : ℕ} :
    i ∈ applicationSupport term ↔
      ∃ X children,
        term.nodeAt? i = some (.inr (X, children)) := by
  constructor
  · intro hi
    obtain ⟨_, happlication⟩ := List.mem_filter.mp hi
    cases hnode : term.nodeAt? i with
    | none => simp [hnode] at happlication
    | some node =>
        cases node with
        | inl x => simp [hnode] at happlication
        | inr app =>
            rcases app with ⟨X, children⟩
            exact ⟨X, children, rfl⟩
  · rintro ⟨X, children, hnode⟩
    apply List.mem_filter.mpr
    refine ⟨?_, by simp [hnode]⟩
    exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp hnode).1

private theorem applicationSupport_sublist (term : RegularTerm) :
    List.Sublist (applicationSupport term)
      (List.range term.nodes.length) :=
  List.filter_sublist

private theorem ground_of_closed_applications
    {ranks : List ℕ} {term : RegularTerm}
    (hshape : term.ShapeWellFormed ranks)
    (hroot : ∃ X children,
      term.nodeAt? term.root = some (.inr (X, children)))
    (hchildren : ∀ i X children,
      term.nodeAt? i = some (.inr (X, children)) →
      ∀ child ∈ children, ∃ Y grandchildren,
        term.nodeAt? child = some (.inr (Y, grandchildren))) :
    term.Ground ranks := by
  refine ⟨hshape, applicationSupport term, ?_, ?_⟩
  · exact List.mem_sublists'.mpr (applicationSupport_sublist term)
  · constructor
    · exact mem_applicationSupport_iff.mpr hroot
    · intro i hi
      obtain ⟨X, children, hnode⟩ := mem_applicationSupport_iff.mp hi
      refine ⟨X, children, hnode, ?_⟩
      intro child hchild
      exact mem_applicationSupport_iff.mpr
        (hchildren i X children hnode child hchild)

private theorem termShapeWellFormed_of_layer
    {machine : EncodedDPDA Action} {layer : TermLayer}
    (hreferences : LayerReferences machine layer)
    (hvalid : LayerNodesValid machine (fun _ => True) layer)
    {q : ℕ} (hq : q < machine.numStates) :
    RegularTerm.ShapeWellFormed (grammarRanks machine)
      (layer.nodes, layer.roots[q]?.getD 0) := by
  obtain ⟨root, hroot, hrootBound⟩ :=
    layerRoot_getElem? hreferences hq
  unfold RegularTerm.ShapeWellFormed RegularTerm.shapeWellFormedCode
  rw [Bool.and_eq_true]
  refine ⟨by simpa [hroot] using decide_eq_true hrootBound, ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  have hnodeValid := hvalid node hnode
  cases node with
  | inl x => rfl
  | inr app =>
      rcases app with ⟨X, children⟩
      simp only at hnodeValid
      simp only [RegularTerm.nodeShapeWellFormedCode, RegularTerm.nodes]
      rw [hnodeValid.1]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨trivial, ?_⟩
      apply List.all_eq_true.mpr
      intro child hchild
      exact decide_eq_true (hnodeValid.2 child hchild)

public theorem configurationTerm_shapeWellFormed [DecidableEq Action]
    (machine : EncodedDPDA Action) {q : ℕ} (hq : q < machine.numStates)
    {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    (configurationTerm machine q stack).ShapeWellFormed
      (grammarRanks machine) := by
  unfold configurationTerm
  exact termShapeWellFormed_of_layer
    (configurationLayer_references machine stack)
    (configurationLayer_nodesValid machine hstack) hq

/-- Every in-range configuration over a well-formed encoded stack is a ground
term of the translated grammar.  Unreachable variable placeholders introduced
at epsilon-popping heads are intentionally ignored by the reachable support. -/
public theorem configurationTerm_ground [DecidableEq Action]
    (machine : EncodedDPDA Action) {q : ℕ} (hq : q < machine.numStates)
    {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    (configurationTerm machine q stack).Ground
      (grammarRanks machine) := by
  apply ground_of_closed_applications
    (configurationTerm_shapeWellFormed machine hq hstack)
  · obtain ⟨root, X, children, hrootLookup, hrootNode⟩ :=
      configurationLayer_rootApplications machine stack q hq
    refine ⟨X, children, ?_⟩
    simpa [configurationTerm, hrootLookup,
      RegularTerm.nodeAt?] using hrootNode
  · intro i X children hnode child hchild
    have hsource : (configurationLayer machine stack).nodes[i]? =
        some (Sum.inr (X, children) : RawNode) := by
      simpa [configurationTerm, RegularTerm.nodeAt?] using hnode
    obtain ⟨Y, grandchildren, hchildNode⟩ :=
      configurationLayer_applicationsClosed machine stack i X children
        hsource child hchild
    refine ⟨Y, grandchildren, ?_⟩
    simpa [configurationTerm, RegularTerm.nodeAt?] using hchildNode

/-! ## Semantic composition of stack schemas -/

/-- Appending unreachable graph nodes does not change the tree denoted from an
old, reference-closed root.  This small layout lemma lets the stack induction
retain later layers as graph suffixes. -/
private theorem appendNodes_unfoldingEquivalent
    {term : RegularTerm} (hterm : term.ReferenceClosed)
    (extra : List RawNode) :
    term.UnfoldingEquivalent (term.nodes ++ extra, term.root) := by
  let R : ℕ → ℕ → Prop := fun i j => i = j ∧ i < term.nodes.length
  refine ⟨R, ⟨rfl, hterm.1⟩, ?_⟩
  intro i j hij
  rcases hij with ⟨rfl, hi⟩
  unfold RegularTerm.NodeCompatible
  have hlookup : (term.nodes ++ extra)[i]? = term.nodes[i]? := by
    rw [List.getElem?_append_left hi]
  change RegularTerm.RawCompatible R (term.nodeAt? i)
    ((term.nodes ++ extra)[i]?)
  rw [hlookup]
  change RegularTerm.RawCompatible R (term.nodeAt? i) (term.nodeAt? i)
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
          exact ⟨rfl, hterm.2 i X children hnode child hchild⟩

/-- A copied argument component of an instantiated graph denotes the same tree
as the original argument, independently of its numeric offset. -/
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
      cases right <;> simp_all [RegularTerm.RawCompatible]
  | some leftNode =>
      cases right with
      | none => simp_all [RegularTerm.RawCompatible]
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
                    hcompatible.2.imp fun i j hij => hmono i j hij⟩

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

/-- Pointwise bisimilar children beneath equal application symbols suffice for
pointed unfolding equivalence. -/
private theorem unfoldingEquivalent_of_rootApplications
    {left right : RegularTerm} {X : ℕ}
    {leftChildren rightChildren : List ℕ}
    (hleft : left.rootApplication? = some (X, leftChildren))
    (hright : right.rootApplication? = some (X, rightChildren))
    (hchildren : List.Forall₂
      (fun i j => left.BisimilarAt i right j)
      leftChildren rightChildren) :
    left.UnfoldingEquivalent right := by
  let R : ℕ → ℕ → Prop := fun i j =>
    (i = left.root ∧ j = right.root) ∨ left.BisimilarAt i right j
  refine ⟨R, Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro i j hij
  rcases hij with hroots | hbisimilar
  · rcases hroots with ⟨rfl, rfl⟩
    unfold RegularTerm.NodeCompatible
    rw [nodeAt?_root_of_rootApplication? hleft,
      nodeAt?_root_of_rootApplication? hright]
    exact ⟨rfl, hchildren.imp fun i j hij => Or.inr hij⟩
  · obtain ⟨S, hij, hS⟩ := hbisimilar
    exact rawCompatible_mono
      (fun child target hchild =>
        Or.inr ⟨S, hchild, hS⟩)
      (hS i j hij)

/-- Apply a finite stack prefix above an arbitrary continuation layer. -/
private def extendStack [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ)
    (base : TermLayer) : TermLayer :=
  stack.reverse.foldl (fun layer Z => extendLayer machine Z layer) base

@[simp] private theorem extendStack_nil [DecidableEq Action]
    (machine : EncodedDPDA Action) (base : TermLayer) :
    extendStack machine [] base = base := rfl

private theorem extendStack_cons [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) (stack : List ℕ)
    (base : TermLayer) :
    extendStack machine (Z :: stack) base =
      extendLayer machine Z (extendStack machine stack base) := by
  simp [extendStack, List.foldl_append]

private theorem extendStack_baseLayer [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    extendStack machine stack (baseLayer machine) =
      stackLayer machine stack := rfl

private theorem configurationLayer_append [DecidableEq Action]
    (machine : EncodedDPDA Action) (front suffix : List ℕ) :
    configurationLayer machine (front ++ suffix) =
      extendStack machine front (configurationLayer machine suffix) := by
  simp [configurationLayer, extendStack, List.reverse_append,
    List.foldl_append]

/-- State-indexed roots in two layers can be related pointwise by checking the
common normalized state index. -/
private theorem roots_forall₂
    {R : ℕ → ℕ → Prop} {left right : List ℕ} {n : ℕ}
    (hleft : left.length = n) (hright : right.length = n)
    (f : ℕ → ℕ)
    (hrel : ∀ q, q < n → R (f (left[q]?.getD 0))
      (right[q]?.getD 0)) :
    List.Forall₂ R (left.map f) right := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hleft, hright], ?_⟩
  intro q hqLeft hqRight
  have hq : q < n := by simpa [hleft] using hqLeft
  have hqLeft' : q < left.length := by simpa using hqLeft
  have hleftLookup : left[q]? = some (left[q]'hqLeft') := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨hqLeft', rfl⟩
  have hrightLookup : right[q]? = some (right[q]'hqRight) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨hqRight, rfl⟩
  simpa [hleftLookup, hrightLookup] using hrel q hq

@[expose] public def configurationArguments [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ) :
    List RegularTerm :=
  (List.range machine.numStates).map fun q =>
    configurationTerm machine q stack

public theorem configurationArguments_getElem? [DecidableEq Action]
    (machine : EncodedDPDA Action) (stack : List ℕ)
    {q : ℕ} (hq : q < machine.numStates) :
    (configurationArguments machine stack)[q]? =
      some (configurationTerm machine q stack) := by
  simp [configurationArguments, hq]

private theorem configurationArguments_referenceClosed
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {stack : List ℕ}
    (hstack : ∀ Z ∈ stack, Z < machine.numStackSymbols) :
    ∀ argument ∈ configurationArguments machine stack,
      argument.ReferenceClosed := by
  intro argument hargument
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hargument
  have hqBound := List.mem_range.mp hq
  exact RegularTerm.referenceClosed_of_ground
    (configurationTerm_ground machine hqBound hstack)

private theorem baseLayerInstantiation_unfoldingEquivalent
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {suffix : List ℕ}
    (hsuffix : ∀ Z ∈ suffix, Z < machine.numStackSymbols)
    {q : ℕ} (hq : q < machine.numStates)
    (schemaExtra targetExtra : List RawNode) :
    (RegularTerm.instantiate
      (((baseLayer machine).nodes ++ schemaExtra,
        (baseLayer machine).roots[q]?.getD 0) : RegularTerm)
      (configurationArguments machine suffix)).UnfoldingEquivalent
      ((configurationLayer machine suffix).nodes ++ targetExtra,
        (configurationLayer machine suffix).roots[q]?.getD 0) := by
  let rhs : RegularTerm :=
    ((baseLayer machine).nodes ++ schemaExtra,
      (baseLayer machine).roots[q]?.getD 0)
  let argument := configurationTerm machine q suffix
  have hargument : (configurationArguments machine suffix)[q]? =
      some argument := by
    exact configurationArguments_getElem? machine suffix hq
  have hclosed : argument.ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground
      (configurationTerm_ground machine hq hsuffix)
  have hrhsRoot : rhs.root = q := by
    simp [rhs, baseLayer, RegularTerm.root, hq]
  have hrhsNode : rhs.nodeAt? q = some (.inl q) := by
    change ((List.range machine.numStates).map Sum.inl ++
      schemaExtra)[q]? = some (.inl q)
    rw [List.getElem?_append_left (by simp [hq])]
    simp [hq]
  have hroot :
      (rhs.instantiate (configurationArguments machine suffix)).root =
        RegularTerm.argumentOffset rhs.nodes.length
            (configurationArguments machine suffix) q + argument.root := by
    unfold RegularTerm.instantiate
    change rhs.resolveRHSRef (configurationArguments machine suffix)
      rhs.root = _
    rw [hrhsRoot]
    simp [RegularTerm.resolveRHSRef, hrhsNode,
      RegularTerm.argumentRoot?, hargument]
  have hcopy := instantiateArgument_unfoldingEquivalent
    (rhs := rhs) hargument hclosed
  have hsame :
      (rhs.instantiate (configurationArguments machine suffix)).withRoot
          (RegularTerm.argumentOffset rhs.nodes.length
            (configurationArguments machine suffix) q + argument.root) =
        rhs.instantiate (configurationArguments machine suffix) := by
    apply Prod.ext
    · rfl
    · simpa [RegularTerm.withRoot] using hroot.symm
  rw [hsame] at hcopy
  have happend := appendNodes_unfoldingEquivalent hclosed targetExtra
  exact hcopy.trans (by
    simpa [argument, configurationTerm] using happend)

private theorem extendedTerm_rootApplication? [DecidableEq Action]
    (machine : EncodedDPDA Action) (Z : ℕ) (layer : TermLayer)
    {q : ℕ} (hq : q < machine.numStates)
    (hstable : Machine.epsilonStep? machine q Z = none)
    (extra : List RawNode) :
    RegularTerm.rootApplication?
      (((extendLayer machine Z layer).nodes ++ extra,
        (extendLayer machine Z layer).roots[q]?.getD 0) : RegularTerm) =
        some (headSymbol machine q Z, layer.roots) := by
  have hqRange : (List.range machine.numStates)[q]? = some q := by
    simp [hq]
  have hroot : (extendLayer machine Z layer).roots[q]? =
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

private theorem instantiate_rootApplication?
    {rhs : RegularTerm} (arguments : List RegularTerm)
    {X : ℕ} {children : List ℕ}
    (hroot : rhs.rootApplication? = some (X, children)) :
    (rhs.instantiate arguments).rootApplication? =
      some (X, children.map (rhs.resolveRHSRef arguments)) := by
  have hrootNode := nodeAt?_root_of_rootApplication? hroot
  have hrootBound := (List.getElem?_eq_some_iff.mp hrootNode).1
  have hresolved : rhs.resolveRHSRef arguments rhs.root = rhs.root := by
    simp [RegularTerm.resolveRHSRef, hrootNode]
  have hinstantiatedNode :
      (rhs.instantiate arguments).nodeAt? rhs.root =
        some (.inr
          (X, children.map (rhs.resolveRHSRef arguments))) := by
    rw [RegularTerm.instantiate_nodeAt?_rhs rhs arguments hrootBound,
      hrootNode]
    rfl
  unfold RegularTerm.rootApplication? RegularTerm.rootNode?
  change (match (rhs.instantiate arguments).nodeAt?
      (rhs.resolveRHSRef arguments rhs.root) with
    | some (.inr app) => some app
    | _ => none) = _
  rw [hresolved, hinstantiatedNode]

private theorem stackLayerInstantiationAux [DecidableEq Action]
    (machine : EncodedDPDA Action) {suffix : List ℕ}
    (hsuffix : ∀ Z ∈ suffix, Z < machine.numStackSymbols)
    (front : List ℕ) {q : ℕ} (hq : q < machine.numStates)
    (schemaExtra targetExtra : List RawNode) :
    (RegularTerm.instantiate
      (((extendStack machine front (baseLayer machine)).nodes ++
          schemaExtra,
        (extendStack machine front (baseLayer machine)).roots[q]?.getD 0) :
        RegularTerm)
      (configurationArguments machine suffix)).UnfoldingEquivalent
      (((extendStack machine front
          (configurationLayer machine suffix)).nodes ++ targetExtra,
        (extendStack machine front
          (configurationLayer machine suffix)).roots[q]?.getD 0) :
        RegularTerm) := by
  induction front generalizing q schemaExtra targetExtra with
  | nil =>
      simpa using baseLayerInstantiation_unfoldingEquivalent machine
        hsuffix hq schemaExtra targetExtra
  | cons Z front ih =>
      rw [extendStack_cons, extendStack_cons]
      let schema := extendStack machine front (baseLayer machine)
      let target := extendStack machine front
        (configurationLayer machine suffix)
      let schemaNew : List RawNode :=
        (List.range machine.numStates).map fun state =>
          match Machine.epsilonStep? machine state Z with
          | some _ => (.inl 0 : RawNode)
          | none => .inr (headSymbol machine state Z, schema.roots)
      let targetNew : List RawNode :=
        (List.range machine.numStates).map fun state =>
          match Machine.epsilonStep? machine state Z with
          | some _ => (.inl 0 : RawNode)
          | none => .inr (headSymbol machine state Z, target.roots)
      cases hstep : Machine.epsilonStep? machine q Z with
      | some out =>
          rcases out with ⟨next, replacement⟩
          have hnext : next < machine.numStates :=
            Machine.epsilonStep?_target_lt hstep
          have hih := ih hnext (schemaNew ++ schemaExtra)
            (targetNew ++ targetExtra)
          simpa [schema, target, schemaNew, targetNew, extendLayer,
            hstep, hq, List.append_assoc] using hih
      | none =>
          let schemaTerm : RegularTerm :=
            ((extendLayer machine Z schema).nodes ++ schemaExtra,
              (extendLayer machine Z schema).roots[q]?.getD 0)
          let targetTerm : RegularTerm :=
            ((extendLayer machine Z target).nodes ++ targetExtra,
              (extendLayer machine Z target).roots[q]?.getD 0)
          have hschemaRoot := extendedTerm_rootApplication?
            machine Z schema hq hstep schemaExtra
          have hleftRoot :
              (schemaTerm.instantiate
                (configurationArguments machine suffix)).rootApplication? =
                some (headSymbol machine q Z,
                  schema.roots.map (schemaTerm.resolveRHSRef
                    (configurationArguments machine suffix))) := by
            exact instantiate_rootApplication?
              (configurationArguments machine suffix) (by
                simpa [schemaTerm] using hschemaRoot)
          have hrightRoot : targetTerm.rootApplication? =
              some (headSymbol machine q Z, target.roots) := by
            simpa [targetTerm] using extendedTerm_rootApplication?
              machine Z target hq hstep targetExtra
          apply unfoldingEquivalent_of_rootApplications
            hleftRoot hrightRoot
          have hschemaReferences : LayerReferences machine schema := by
            simpa [schema, extendStack_baseLayer] using
              stackLayer_references machine front
          have htargetReferences : LayerReferences machine target := by
            change LayerReferences machine
              (extendStack machine front
                (configurationLayer machine suffix))
            rw [← configurationLayer_append machine front suffix]
            exact configurationLayer_references machine (front ++ suffix)
          apply roots_forall₂ hschemaReferences.1
            htargetReferences.1
            (schemaTerm.resolveRHSRef
              (configurationArguments machine suffix))
          intro state hstate
          rw [← RegularTerm.withRoot_unfoldingEquivalent_iff_bisimilarAt]
          have hih := ih hstate (schemaNew ++ schemaExtra)
            (targetNew ++ targetExtra)
          simpa [schemaTerm, targetTerm, schema, target, schemaNew,
            targetNew, extendLayer, List.append_assoc,
            RegularTerm.withRoot] using hih

/-- Substituting the state-indexed continuation configurations into the open
schema for a stack prefix denotes exactly that prefix above the continuation
stack.  This is the semantic composition law used by every translated rule. -/
public theorem stackSchema_instantiate_configurationArguments
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {front suffix : List ℕ}
    (hsuffix : ∀ Z ∈ suffix, Z < machine.numStackSymbols)
    {q : ℕ} (hq : q < machine.numStates) :
    ((stackSchema machine q front).instantiate
      (configurationArguments machine suffix)).UnfoldingEquivalent
      (configurationTerm machine q (front ++ suffix)) := by
  have hcomposition := stackLayerInstantiationAux machine hsuffix
    front hq [] []
  simpa [stackSchema, configurationTerm, extendStack_baseLayer,
    ← configurationLayer_append machine front suffix] using hcomposition

/-- A continuation root embedded in the graph for one additional stack layer
denotes the corresponding suffix configuration; the newly allocated layer is
unreachable from that changed root. -/
public theorem configurationTerm_continuation_unfoldingEquivalent
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {state : ℕ} (hstate : state < machine.numStates)
    {q Z : ℕ} {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols) :
    RegularTerm.UnfoldingEquivalent
      ((configurationTerm machine q (Z :: suffix)).withRoot
        ((configurationLayer machine suffix).roots[state]?.getD 0))
      (configurationTerm machine state suffix) := by
  let newNodes : List RawNode :=
    (List.range machine.numStates).map fun current =>
      match Machine.epsilonStep? machine current Z with
      | some _ => (.inl 0 : RawNode)
      | none => .inr (headSymbol machine current Z,
          (configurationLayer machine suffix).roots)
  have hclosed :
      (configurationTerm machine state suffix).ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground
      (configurationTerm_ground machine hstate hsuffix)
  have happended :=
    (appendNodes_unfoldingEquivalent hclosed newNodes).symm
  simpa [configurationTerm, configurationLayer_cons, extendLayer,
    newNodes, RegularTerm.withRoot, RegularTerm.nodes,
    RegularTerm.root] using happended

private theorem roots_map_forall₂
    {Left Right : Type} {R : Left → Right → Prop}
    {left right : List ℕ} {n : ℕ}
    (hleft : left.length = n) (hright : right.length = n)
    (f : ℕ → Left) (g : ℕ → Right)
    (hrel : ∀ q, q < n → R (f (left[q]?.getD 0))
      (g (right[q]?.getD 0))) :
    List.Forall₂ R (left.map f) (right.map g) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hleft, hright], ?_⟩
  intro q hqLeft hqRight
  have hq : q < n := by simpa [hleft] using hqLeft
  have hqLeft' : q < left.length := by simpa using hqLeft
  have hqRight' : q < right.length := by simpa using hqRight
  have hleftLookup : left[q]? = some (left[q]'hqLeft') := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨hqLeft', rfl⟩
  have hrightLookup : right[q]? = some (right[q]'hqRight') := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨hqRight', rfl⟩
  simpa [hleftLookup, hrightLookup] using hrel q hq

/-- The child arguments exposed at a stable configuration head are pointwise
the canonical state-indexed suffix configurations. -/
public theorem configurationRootArguments_forall₂
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {q Z : ℕ} {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols) :
    List.Forall₂ RegularTerm.UnfoldingEquivalent
      ((configurationLayer machine suffix).roots.map
        (configurationTerm machine q (Z :: suffix)).withRoot)
      (configurationArguments machine suffix) := by
  unfold configurationArguments
  apply roots_map_forall₂
    (configurationLayer_references machine suffix).1
    (by simp)
    (configurationTerm machine q (Z :: suffix)).withRoot
    (fun state => configurationTerm machine state suffix)
  intro state hstate
  simpa [hstate] using
    configurationTerm_continuation_unfoldingEquivalent
      machine hstate (q := q) (Z := Z) hsuffix

private theorem configurationRootArguments_referenceClosed
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {q Z : ℕ} (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols) {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols) :
    ∀ argument ∈
        (configurationLayer machine suffix).roots.map
          (configurationTerm machine q (Z :: suffix)).withRoot,
      argument.ReferenceClosed := by
  have hfull : ∀ symbol ∈ Z :: suffix,
      symbol < machine.numStackSymbols := by
    intro symbol hsymbol
    simp only [List.mem_cons] at hsymbol
    rcases hsymbol with rfl | hsymbol
    · exact hZ
    · exact hsuffix symbol hsymbol
  have hsourceClosed :
      (configurationTerm machine q (Z :: suffix)).ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground
      (configurationTerm_ground machine hq hfull)
  intro argument hargument
  obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hargument
  have hrootOld : root <
      (configurationLayer machine suffix).nodes.length :=
    (configurationLayer_references machine suffix).2 root hroot
  have hrootFull : root <
      (configurationTerm machine q (Z :: suffix)).nodes.length := by
    change root < (configurationLayer machine (Z :: suffix)).nodes.length
    rw [configurationLayer_cons, extendLayer_nodes_length]
    omega
  exact RegularTerm.withRoot_referenceClosed hsourceClosed hrootFull

public theorem configurationTerm_rootApplication?_of_stable
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {q Z : ℕ} (hq : q < machine.numStates) {suffix : List ℕ}
    (hstable : Machine.epsilonStep? machine q Z = none) :
    (configurationTerm machine q (Z :: suffix)).rootApplication? =
      some (headSymbol machine q Z,
        (configurationLayer machine suffix).roots) := by
  simpa [configurationTerm, configurationLayer_cons] using
    extendedTerm_rootApplication? machine Z
      (configurationLayer machine suffix) hq hstable []

/-- One selected stable DPDA input transition is simulated by the translated
grammar rule, up to the semantic equality of regular-term graph layouts. -/
public theorem grammar_rootRewrite?_of_inputStep
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {q Z : ℕ} (hq : q < machine.numStates)
    (hZ : Z < machine.numStackSymbols) {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    {action : Action} {targetState : ℕ} {replacement : List ℕ}
    (hstable : Machine.epsilonStep? machine q Z = none)
    (hinput : Machine.inputStep? machine q action Z =
      some (targetState, replacement)) :
    ∃ result,
      (grammar machine).rootRewrite? action
          (configurationTerm machine q (Z :: suffix)) = some result ∧
        result.UnfoldingEquivalent
          (configurationTerm machine targetState
            (replacement ++ suffix)) := by
  have htarget : targetState < machine.numStates :=
    Machine.inputStep?_target_lt hinput
  have hreplacement : ∀ symbol ∈ replacement,
      symbol < machine.numStackSymbols :=
    Machine.inputStep?_replacement_lt hinput
  have hroot := configurationTerm_rootApplication?_of_stable
    machine hq (suffix := suffix) hstable
  have hrule := grammar_ruleLookup_of_inputStep? machine hq hZ
    hstable hinput
  unfold EncodedFirstOrderGrammar.rootRewrite?
  simp only [hroot, hrule, Option.map_some]
  let actualArguments :=
    (configurationLayer machine suffix).roots.map
      (configurationTerm machine q (Z :: suffix)).withRoot
  refine ⟨(stackSchema machine targetState replacement).instantiate
    actualArguments, rfl, ?_⟩
  have hschemaClosed :
      (stackSchema machine targetState replacement).ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed
      (stackSchema_wellFormed machine htarget hreplacement)
  have hactualCanonical :=
    RegularTerm.instantiate_unfoldingEquivalent hschemaClosed
      (configurationRootArguments_forall₂ machine
        (q := q) (Z := Z) hsuffix)
      (configurationRootArguments_referenceClosed machine hq hZ hsuffix)
      (configurationArguments_referenceClosed machine hsuffix)
  have hcomposition :=
    stackSchema_instantiate_configurationArguments machine hsuffix htarget
      (front := replacement)
  exact hactualCanonical.trans hcomposition

/-- At an epsilon-popping head the translated configuration root is exactly the
selected target-state continuation, so the extra top layer is unreachable. -/
public theorem configurationTerm_epsilon_unfoldingEquivalent
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {q Z targetState : ℕ} {replacement : List ℕ}
    (hq : q < machine.numStates) {suffix : List ℕ}
    (hsuffix : ∀ symbol ∈ suffix,
      symbol < machine.numStackSymbols)
    (hstep : Machine.epsilonStep? machine q Z =
      some (targetState, replacement)) :
    (configurationTerm machine q (Z :: suffix)).UnfoldingEquivalent
      (configurationTerm machine targetState suffix) := by
  have htarget : targetState < machine.numStates :=
    Machine.epsilonStep?_target_lt hstep
  have hroot : (configurationTerm machine q (Z :: suffix)).root =
      (configurationLayer machine suffix).roots[targetState]?.getD 0 := by
    simp [configurationTerm, configurationLayer_cons, extendLayer,
      hq, hstep, RegularTerm.root]
  have hcontinuation :=
    configurationTerm_continuation_unfoldingEquivalent machine htarget
      (q := q) (Z := Z) hsuffix
  have hsame :
      (configurationTerm machine q (Z :: suffix)).withRoot
          ((configurationLayer machine suffix).roots[targetState]?.getD 0) =
        configurationTerm machine q (Z :: suffix) := by
    apply Prod.ext
    · rfl
    · simpa [RegularTerm.withRoot, RegularTerm.root] using hroot.symm
  rw [hsame] at hcontinuation
  exact hcontinuation

private theorem grammar_ruleLookup_referenceClosed [DecidableEq Action]
    (machine : EncodedDPDA Action) {X : ℕ} {action : Action}
    {rhs : RegularTerm}
    (hlookup : (grammar machine).ruleLookup X action = some rhs) :
    rhs.ReferenceClosed := by
  unfold EncodedFirstOrderGrammar.ruleLookup at hlookup
  obtain ⟨rule, hfind, hrhs⟩ := Option.map_eq_some_iff.mp hlookup
  have hruleMem : rule ∈ (grammar machine).rawRules :=
    EncodedFirstOrderGrammar.findRule_mem hfind
  have hwell := (List.all_eq_true.mp
    (grammar_rulesWellFormedCode machine)) rule hruleMem
  unfold EncodedFirstOrderGrammar.ruleWellFormedCode at hwell
  cases hrank : (grammar machine).ranks[rule.lhs]? with
  | none => simp [hrank] at hwell
  | some rank =>
      simp only [hrank, Bool.and_eq_true] at hwell
      have hrhsEq : rule.rhs = rhs := hrhs
      subst rhs
      exact RegularTerm.referenceClosed_of_wellFormed hwell.1

/-- Forced epsilon popping preserves the finite-state and stack-symbol bounds. -/
public theorem stabilize_preserves_valid [DecidableEq Action]
    {machine : EncodedDPDA Action} {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) :
    (stabilize machine (q, stack)).1 < machine.numStates ∧
      ∀ symbol ∈ (stabilize machine (q, stack)).2,
        symbol < machine.numStackSymbols := by
  induction stack generalizing q with
  | nil =>
      simp [stabilize, hq]
  | cons Z stack ih =>
      have htail : ∀ symbol ∈ stack,
          symbol < machine.numStackSymbols := by
        intro symbol hsymbol
        exact hstack symbol (by simp [hsymbol])
      cases hstep : Machine.epsilonStep? machine q Z with
      | none =>
          simp only [stabilize, hstep]
          exact ⟨hq, hstack⟩
      | some out =>
          rcases out with ⟨targetState, replacement⟩
          have hreplacement : replacement = [] :=
            Machine.epsilonStep?_replacement_eq_nil_of_poppingComplete
              hnormal hstep
          subst replacement
          have htarget : targetState < machine.numStates :=
            Machine.epsilonStep?_target_lt hstep
          simp only [stabilize, hstep]
          exact ih htarget htail

/-- A configuration graph already exposes the result of its complete forced
epsilon-popping phase at the root. -/
public theorem configurationTerm_stabilize_unfoldingEquivalent
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) :
    (configurationTerm machine q stack).UnfoldingEquivalent
      (configurationTerm machine (stabilize machine (q, stack)).1
        (stabilize machine (q, stack)).2) := by
  induction stack generalizing q with
  | nil =>
      simp only [stabilize]
      exact RegularTerm.unfoldingEquivalent_refl _
  | cons Z stack ih =>
      have htail : ∀ symbol ∈ stack,
          symbol < machine.numStackSymbols := by
        intro symbol hsymbol
        exact hstack symbol (by simp [hsymbol])
      cases hstep : Machine.epsilonStep? machine q Z with
      | none =>
          simp only [stabilize, hstep]
          exact RegularTerm.unfoldingEquivalent_refl _
      | some out =>
          rcases out with ⟨targetState, replacement⟩
          have hreplacement : replacement = [] :=
            Machine.epsilonStep?_replacement_eq_nil_of_poppingComplete
              hnormal hstep
          subst replacement
          have htarget : targetState < machine.numStates :=
            Machine.epsilonStep?_target_lt hstep
          simp only [stabilize, hstep]
          exact (configurationTerm_epsilon_unfoldingEquivalent machine
            hq htail hstep).trans (ih htarget htail)

private theorem stabilize_eq_cons_stable [DecidableEq Action]
    {machine : EncodedDPDA Action} {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet) :
    ∀ {q : ℕ} {stack : List ℕ} {state Z : ℕ} {tail : List ℕ},
      stabilize machine (q, stack) = (state, Z :: tail) →
        Machine.epsilonStep? machine state Z = none := by
  intro q stack
  induction stack generalizing q with
  | nil =>
      intro state Z tail hresult
      simp [stabilize] at hresult
  | cons top stack ih =>
      intro state Z tail hresult
      cases hstep : Machine.epsilonStep? machine q top with
      | none =>
          simp only [stabilize, hstep] at hresult
          injection hresult with hstate hstack
          subst state
          have htop : Z = top := by
            simpa using (congrArg List.head? hstack).symm
          subst Z
          exact hstep
      | some out =>
          rcases out with ⟨targetState, replacement⟩
          have hreplacement : replacement = [] :=
            Machine.epsilonStep?_replacement_eq_nil_of_poppingComplete
              hnormal hstep
          subst replacement
          simp only [stabilize, hstep] at hresult
          exact ih hresult

/-- One normalized observable DPDA move is simulated by one translated grammar
rewrite from the original (possibly epsilon-unstable) configuration graph. -/
public theorem grammar_rootRewrite?_of_observableStep
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    {action : Action} {targetConfiguration : Configuration}
    (hstep : observableStep? machine action (q, stack) =
      some targetConfiguration) :
    ∃ result,
      (grammar machine).rootRewrite? action
          (configurationTerm machine q stack) = some result ∧
        result.UnfoldingEquivalent
          (configurationTerm machine targetConfiguration.1
            targetConfiguration.2) := by
  have hstableValid := stabilize_preserves_valid hnormal hq hstack
  cases hstable : stabilize machine (q, stack) with
  | mk stableState stableStack =>
      have hstableState : stableState < machine.numStates := by
        simpa [hstable] using hstableValid.1
      have hstableStack : ∀ symbol ∈ stableStack,
          symbol < machine.numStackSymbols := by
        simpa [hstable] using hstableValid.2
      cases stableStack with
      | nil =>
          unfold observableStep? at hstep
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
              Machine.epsilonStep? machine stableState top = none :=
            stabilize_eq_cons_stable hnormal hstable
          unfold observableStep? at hstep
          rw [hstable] at hstep
          obtain ⟨out, hinput, hout⟩ := Option.map_eq_some_iff.mp hstep
          rcases out with ⟨targetState, replacement⟩
          have hconfiguration :
              (targetState, replacement ++ tail) = targetConfiguration :=
            hout
          subst targetConfiguration
          obtain ⟨stableResult, hstableRewrite, hstableResult⟩ :=
            grammar_rootRewrite?_of_inputStep machine hstableState htop
              htail hstableHead hinput
          have hsourceStable :=
            configurationTerm_stabilize_unfoldingEquivalent
              hnormal hq hstack
          have hsourceStable' :
              (configurationTerm machine q stack).UnfoldingEquivalent
                (configurationTerm machine stableState (top :: tail)) := by
            simpa [hstable] using hsourceStable
          have hsourceClosed :
              (configurationTerm machine q stack).ReferenceClosed :=
            RegularTerm.referenceClosed_of_ground
              (configurationTerm_ground machine hq hstack)
          have hstableClosed :
              (configurationTerm machine stableState
                (top :: tail)).ReferenceClosed :=
            RegularTerm.referenceClosed_of_ground
              (configurationTerm_ground machine hstableState hstableStack)
          have hcongruence :=
            EncodedFirstOrderGrammar.rootRewrite?_respects_unfoldingEquivalent
              (g := grammar machine) (a := action)
              hsourceStable' hsourceClosed hstableClosed
              (fun X nextAction rhs hlookup =>
                grammar_ruleLookup_referenceClosed machine hlookup)
          rw [hstableRewrite] at hcongruence
          cases hsourceRewrite : (grammar machine).rootRewrite? action
              (configurationTerm machine q stack) with
          | none => simp [hsourceRewrite] at hcongruence
          | some result =>
              have hresult : result.UnfoldingEquivalent stableResult := by
                simpa [hsourceRewrite] using hcongruence
              exact ⟨result, rfl,
                hresult.trans hstableResult⟩

public theorem grammar_ruleLookup_bottomSymbol_none [DecidableEq Action]
    (machine : EncodedDPDA Action) (action : Action) :
    (grammar machine).ruleLookup (bottomSymbol machine) action = none := by
  unfold EncodedFirstOrderGrammar.ruleLookup
  cases hfind : (grammar machine).findRule
      (bottomSymbol machine) action with
  | none => rfl
  | some rule =>
      have hruleMem := EncodedFirstOrderGrammar.findRule_mem hfind
      have hkey := EncodedFirstOrderGrammar.findRule_key hfind
      change rule ∈
        (inputKeys machine).filterMap (ruleForKey machine) at hruleMem
      rw [List.mem_filterMap] at hruleMem
      obtain ⟨key, hkeyMem, hcompiled⟩ := hruleMem
      have hcompiledKey := ruleForKey_some_key hcompiled
      obtain ⟨hq, hZ⟩ := inputKey_bounds machine hkeyMem
      have hhead := headSymbol_lt_bottom machine hq hZ
      have hfalse : headSymbol machine key.1 key.2.2 =
          bottomSymbol machine := hcompiledKey.1.symm.trans hkey.1
      omega

public theorem configurationTerm_nil_rootRewrite?_eq_none
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {q : ℕ} (hq : q < machine.numStates) (action : Action) :
    (grammar machine).rootRewrite? action
      (configurationTerm machine q []) = none := by
  have hroot : (configurationTerm machine q []).rootApplication? =
      some (bottomSymbol machine, []) := by
    simp [configurationTerm, groundBaseLayer,
      RegularTerm.rootApplication?, RegularTerm.rootNode?,
      RegularTerm.nodeAt?, RegularTerm.root, RegularTerm.nodes, hq]
  unfold EncodedFirstOrderGrammar.rootRewrite?
  simp [hroot, grammar_ruleLookup_bottomSymbol_none]

/-- Enabled ordinary grammar actions are exactly enabled normalized observable
DPDA actions on translated valid configurations. -/
public theorem grammar_rootRewrite?_isSome_iff_observableStep?_isSome
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) (action : Action) :
    ((grammar machine).rootRewrite? action
        (configurationTerm machine q stack)).isSome = true ↔
      (observableStep? machine action (q, stack)).isSome = true := by
  constructor
  · intro hgrammar
    have hstableValid := stabilize_preserves_valid hnormal hq hstack
    cases hstable : stabilize machine (q, stack) with
    | mk stableState stableStack =>
        have hstableState : stableState < machine.numStates := by
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
              RegularTerm.referenceClosed_of_ground
                (configurationTerm_ground machine hq hstack)
            have hstableClosed :
                (configurationTerm machine stableState []).ReferenceClosed :=
              RegularTerm.referenceClosed_of_ground
                (configurationTerm_ground machine hstableState (by simp))
            have hcongruence :=
              EncodedFirstOrderGrammar.rootRewrite?_respects_unfoldingEquivalent
                (g := grammar machine) (a := action)
                hsourceStable' hsourceClosed hstableClosed
                (fun X nextAction rhs hlookup =>
                  grammar_ruleLookup_referenceClosed machine hlookup)
            rw [configurationTerm_nil_rootRewrite?_eq_none
              machine hstableState action] at hcongruence
            cases hsource : (grammar machine).rootRewrite? action
                (configurationTerm machine q stack) with
            | none => simp [hsource] at hgrammar
            | some result => simp [hsource] at hcongruence
        | cons top tail =>
            have htop : top < machine.numStackSymbols :=
              hstableStack top (by simp)
            have hstableHead :
                Machine.epsilonStep? machine stableState top = none :=
              stabilize_eq_cons_stable hnormal hstable
            obtain ⟨out, hinput⟩ :=
              Machine.inputStep?_exists_of_poppingComplete hnormal
                hstableState htop hstableHead action
            unfold observableStep?
            simp [hstable, hinput]
  · intro hobservable
    cases hstep : observableStep? machine action (q, stack) with
    | none => simp [hstep] at hobservable
    | some targetConfiguration =>
        obtain ⟨result, hrewrite, _⟩ :=
          grammar_rootRewrite?_of_observableStep hnormal hq hstack hstep
        simp [hrewrite]

private theorem grammar_rootRewrite?_referenceClosed
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {action : Action} {source target : RegularTerm}
    (hsource : source.ReferenceClosed)
    (hstep : (grammar machine).rootRewrite? action source = some target) :
    target.ReferenceClosed := by
  unfold EncodedFirstOrderGrammar.rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ := Option.map_eq_some_iff.mp hstep
      subst target
      apply RegularTerm.instantiate_referenceClosed
        (grammar_ruleLookup_referenceClosed machine hrule)
      intro argument hargument
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
      exact RegularTerm.withRoot_referenceClosed hsource
        (RegularTerm.rootApplication_children_lt hsource hroot
          child hchild)

public theorem observableStep_preserves_valid [DecidableEq Action]
    {machine : EncodedDPDA Action} {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    {action : Action} {target : Configuration}
    (hstep : observableStep? machine action (q, stack) = some target) :
    target.1 < machine.numStates ∧
      ∀ symbol ∈ target.2, symbol < machine.numStackSymbols := by
  have hstableValid := stabilize_preserves_valid hnormal hq hstack
  cases hstable : stabilize machine (q, stack) with
  | mk stableState stableStack =>
      have hstableStack : ∀ symbol ∈ stableStack,
          symbol < machine.numStackSymbols := by
        simpa [hstable] using hstableValid.2
      cases stableStack with
      | nil =>
          unfold observableStep? at hstep
          rw [hstable] at hstep
          simp at hstep
      | cons top tail =>
          unfold observableStep? at hstep
          rw [hstable] at hstep
          obtain ⟨out, hinput, hout⟩ := Option.map_eq_some_iff.mp hstep
          rcases out with ⟨targetState, replacement⟩
          have htargetState : targetState < machine.numStates :=
            Machine.inputStep?_target_lt hinput
          have hreplacement : ∀ symbol ∈ replacement,
              symbol < machine.numStackSymbols :=
            Machine.inputStep?_replacement_lt hinput
          have htarget : (targetState, replacement ++ tail) = target := hout
          subst target
          refine ⟨htargetState, ?_⟩
          intro symbol hsymbol
          rw [List.mem_append] at hsymbol
          rcases hsymbol with hsymbol | hsymbol
          · exact hreplacement symbol hsymbol
          · exact hstableStack symbol (by simp [hsymbol])

private theorem grammar_traceEquivalent_of_unfoldingEquivalent
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {left right : RegularTerm}
    (hleft : left.ReferenceClosed) (hright : right.ReferenceClosed)
    (hequivalent : left.UnfoldingEquivalent right) :
    (grammar machine).TraceEquivalent left right := by
  rw [EncodedFirstOrderGrammar.traceEquivalent_iff_forall_traceApprox]
  intro n
  exact (EncodedFirstOrderGrammar.guardedContextLaws_of_wellFormed
    (grammar_wellFormed machine)).unfoldingApprox n left right
      hleft hright hequivalent

/-- Ordinary grammar traces from a translated valid configuration are exactly
the normalized DPDA's observable traces. -/
public theorem grammar_isTrace_map_inl_iff
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) (word : List Action) :
    (grammar machine).IsTrace (configurationTerm machine q stack)
        (word.map Sum.inl) ↔
      IsObservableTrace machine (q, stack) word := by
  induction word generalizing q stack with
  | nil =>
      unfold EncodedFirstOrderGrammar.IsTrace IsObservableTrace
      rfl
  | cons action word ih =>
      cases hobservable : observableStep? machine action (q, stack) with
      | none =>
          cases hgrammar : (grammar machine).rootRewrite? action
              (configurationTerm machine q stack) with
          | none =>
              unfold EncodedFirstOrderGrammar.IsTrace IsObservableTrace
              simp only [List.map_cons,
                EncodedFirstOrderGrammar.run?_cons,
                EncodedFirstOrderGrammar.step?, observableRun?]
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
            grammar_rootRewrite?_of_observableStep hnormal hq hstack
              hobservable
          have htargetValid := observableStep_preserves_valid
            hnormal hq hstack hobservable
          have hsourceClosed :
              (configurationTerm machine q stack).ReferenceClosed :=
            RegularTerm.referenceClosed_of_ground
              (configurationTerm_ground machine hq hstack)
          have hresultClosed : result.ReferenceClosed :=
            grammar_rootRewrite?_referenceClosed machine hsourceClosed
              hrewrite
          have htargetClosed :
              (configurationTerm machine target.1 target.2).ReferenceClosed :=
            RegularTerm.referenceClosed_of_ground
              (configurationTerm_ground machine htargetValid.1
                htargetValid.2)
          have htraceEquivalent :=
            grammar_traceEquivalent_of_unfoldingEquivalent machine
              hresultClosed htargetClosed hresult
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
              IsObservableTrace machine (q, stack) (action :: word) ↔
                IsObservableTrace machine target word := by
            unfold IsObservableTrace
            simp [observableRun?, hobservable]
          simp only [List.map_cons]
          rw [hleftReduce, hrightReduce]
          have hresultTrace :
              (grammar machine).IsTrace result (word.map Sum.inl) ↔
                (grammar machine).IsTrace
                  (configurationTerm machine target.1 target.2)
                  (word.map Sum.inl) := by
            change word.map Sum.inl ∈
                (grammar machine).traceLanguage result ↔
              word.map Sum.inl ∈ (grammar machine).traceLanguage
                (configurationTerm machine target.1 target.2)
            rw [htraceEquivalent]
          exact hresultTrace.trans
            (ih htargetValid.1 htargetValid.2)

private theorem configurationTerm_privateStep?_eq_none
    [DecidableEq Action] (machine : EncodedDPDA Action)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) (x : ℕ) :
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
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet) :
    ∀ {q : ℕ} {stack : List ℕ}, q < machine.numStates →
      (∀ symbol ∈ stack, symbol < machine.numStackSymbols) →
      ∀ labels : List (Label Action),
        (grammar machine).IsTrace (configurationTerm machine q stack)
          labels →
        ∃ word : List Action, labels = word.map Sum.inl := by
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
          have hrewrite : (grammar machine).rootRewrite? action
              (configurationTerm machine q stack) = some result := by
            simpa [EncodedFirstOrderGrammar.Step,
              EncodedFirstOrderGrammar.step?] using hstep
          have hgrammarEnabled :
              ((grammar machine).rootRewrite? action
                (configurationTerm machine q stack)).isSome = true := by
            simp [hrewrite]
          have hobservableEnabled :=
            (grammar_rootRewrite?_isSome_iff_observableStep?_isSome
              hnormal hq hstack action).mp hgrammarEnabled
          cases hobservable : observableStep? machine action (q, stack) with
          | none => simp [hobservable] at hobservableEnabled
          | some target =>
              obtain ⟨simulated, hsimulatedRewrite, hsimulated⟩ :=
                grammar_rootRewrite?_of_observableStep hnormal hq hstack
                  hobservable
              have hresultEq : result = simulated :=
                Option.some.inj (hrewrite.symm.trans hsimulatedRewrite)
              subst simulated
              have htargetValid := observableStep_preserves_valid
                hnormal hq hstack hobservable
              have hsourceClosed :
                  (configurationTerm machine q stack).ReferenceClosed :=
                RegularTerm.referenceClosed_of_ground
                  (configurationTerm_ground machine hq hstack)
              have hresultClosed : result.ReferenceClosed :=
                grammar_rootRewrite?_referenceClosed machine hsourceClosed
                  hrewrite
              have htargetClosed :
                  (configurationTerm machine target.1
                    target.2).ReferenceClosed :=
                RegularTerm.referenceClosed_of_ground
                  (configurationTerm_ground machine htargetValid.1
                    htargetValid.2)
              have htraceEquivalent :=
                grammar_traceEquivalent_of_unfoldingEquivalent machine
                  hresultClosed htargetClosed hsimulated
              have htargetTrace :
                  (grammar machine).IsTrace
                    (configurationTerm machine target.1 target.2)
                    labels := by
                change labels ∈ (grammar machine).traceLanguage
                  (configurationTerm machine target.1 target.2)
                rw [← htraceEquivalent]
                exact htailTrace
              obtain ⟨word, hlabels⟩ :=
                ih htargetValid.1 htargetValid.2 htargetTrace
              exact ⟨action :: word, by simp [hlabels]⟩

/-- Full translated-grammar traces contain no private variable labels and are
precisely the `inl` images of normalized observable words. -/
public theorem grammar_isTrace_iff_exists_observableWord
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) (labels : List (Label Action)) :
    (grammar machine).IsTrace (configurationTerm machine q stack) labels ↔
      ∃ word : List Action,
        labels = word.map Sum.inl ∧
          IsObservableTrace machine (q, stack) word := by
  constructor
  · intro htrace
    obtain ⟨word, hlabels⟩ :=
      grammar_trace_has_ordinary_word hnormal hq hstack labels htrace
    refine ⟨word, hlabels, ?_⟩
    apply (grammar_isTrace_map_inl_iff hnormal hq hstack word).mp
    simpa [hlabels] using htrace
  · rintro ⟨word, rfl, hobservable⟩
    exact (grammar_isTrace_map_inl_iff hnormal hq hstack word).mpr
      hobservable

public theorem observableRun?_append [DecidableEq Action]
    (machine : EncodedDPDA Action) (first second : List Action)
    (configuration : Configuration) :
    observableRun? machine (first ++ second) configuration =
      (observableRun? machine first configuration).bind
        (observableRun? machine second) := by
  induction first generalizing configuration with
  | nil => rfl
  | cons action first ih =>
      simp only [List.cons_append, observableRun?]
      cases hstep : observableStep? machine action configuration with
      | none => simp
      | some target => simpa [hstep] using ih target

public theorem observableRun_preserves_valid [DecidableEq Action]
    {machine : EncodedDPDA Action} {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    {word : List Action} {target : Configuration}
    (hrun : observableRun? machine word (q, stack) = some target) :
    target.1 < machine.numStates ∧
      ∀ symbol ∈ target.2, symbol < machine.numStackSymbols := by
  induction word generalizing q stack with
  | nil =>
      simp only [observableRun?, Option.some.injEq] at hrun
      subst target
      exact ⟨hq, hstack⟩
  | cons action word ih =>
      simp only [observableRun?] at hrun
      cases hstep : observableStep? machine action (q, stack) with
      | none => simp [hstep] at hrun
      | some middle =>
          rw [hstep] at hrun
          have hmiddle := observableStep_preserves_valid
            hnormal hq hstack hstep
          exact ih hmiddle.1 hmiddle.2 hrun

public theorem observableStep?_isSome_iff_stabilize_stack_ne_nil
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols) (action : Action) :
    (observableStep? machine action (q, stack)).isSome = true ↔
      (stabilize machine (q, stack)).2 ≠ [] := by
  have hstableValid := stabilize_preserves_valid hnormal hq hstack
  cases hstable : stabilize machine (q, stack) with
  | mk stableState stableStack =>
      have hstableState : stableState < machine.numStates := by
        simpa [hstable] using hstableValid.1
      have hstableStack : ∀ symbol ∈ stableStack,
          symbol < machine.numStackSymbols := by
        simpa [hstable] using hstableValid.2
      cases stableStack with
      | nil =>
          simp [observableStep?, hstable]
      | cons top tail =>
          have htop : top < machine.numStackSymbols :=
            hstableStack top (by simp)
          have hstableHead :
              Machine.epsilonStep? machine stableState top = none :=
            stabilize_eq_cons_stable hnormal hstable
          obtain ⟨out, hinput⟩ :=
            Machine.inputStep?_exists_of_poppingComplete hnormal
              hstableState htop hstableHead action
          simp [observableStep?, hstable, hinput]

public theorem observableTrace_append_singleton_iff
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    (word : List Action) (action : Action) :
    IsObservableTrace machine (q, stack) (word ++ [action]) ↔
      IsObservableTrace machine (q, stack) word ∧
        word ∉ emptyStackLanguage machine (q, stack) := by
  cases hrun : observableRun? machine word (q, stack) with
  | none =>
      simp [IsObservableTrace, emptyStackLanguage,
        observableRun?_append, hrun]
  | some target =>
      have htargetValid := observableRun_preserves_valid
        hnormal hq hstack hrun
      have hstep := observableStep?_isSome_iff_stabilize_stack_ne_nil
        hnormal htargetValid.1 htargetValid.2 action
      have hmemberIff :
          word ∈ emptyStackLanguage machine (q, stack) ↔
            (stabilize machine target).2 = [] := by
        constructor
        · rintro ⟨final, hfinal, hempty⟩
          have hfinalEq : target = final :=
            Option.some.inj (hrun.symm.trans hfinal)
          subst final
          exact hempty
        · intro hempty
          exact ⟨target, hrun, hempty⟩
      rw [hmemberIff]
      simpa [IsObservableTrace, observableRun?_append,
        observableRun?, hrun] using hstep

public theorem mem_emptyStackLanguage_iff_trace_and_not_extension
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {q : ℕ} {stack : List ℕ} (hq : q < machine.numStates)
    (hstack : ∀ symbol ∈ stack,
      symbol < machine.numStackSymbols)
    (word : List Action) (witness : Action) :
    word ∈ emptyStackLanguage machine (q, stack) ↔
      IsObservableTrace machine (q, stack) word ∧
        ¬IsObservableTrace machine (q, stack) (word ++ [witness]) := by
  constructor
  · intro hmember
    rcases hmember with ⟨target, hrun, hempty⟩
    have htrace : IsObservableTrace machine (q, stack) word := by
      unfold IsObservableTrace
      rw [hrun]
      rfl
    refine ⟨htrace, ?_⟩
    intro hextension
    have hparts := (observableTrace_append_singleton_iff
      hnormal hq hstack word witness).mp hextension
    exact hparts.2 ⟨target, hrun, hempty⟩
  · rintro ⟨htrace, hnoExtension⟩
    by_contra hnotMember
    have hextension := (observableTrace_append_singleton_iff
      hnormal hq hstack word witness).mpr ⟨htrace, hnotMember⟩
    exact hnoExtension hextension

@[expose] public def ObservableTraceEquivalent [DecidableEq Action]
    (machine : EncodedDPDA Action)
    (left right : Configuration) : Prop :=
  ∀ word, IsObservableTrace machine left word ↔
    IsObservableTrace machine right word

/-- In a popping/complete machine, the prefix-closed observable trace language
and the prefix-free empty-stack language determine one another.  A single
action witness distinguishes a maximal trace from a dead-end-free nonempty
configuration; normalized `Option` alphabets use `none`. -/
public theorem emptyStackLanguage_eq_iff_observableTraceEquivalent
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    (witness : Action) {left right : Configuration}
    (hleftState : left.1 < machine.numStates)
    (hleftStack : ∀ symbol ∈ left.2,
      symbol < machine.numStackSymbols)
    (hrightState : right.1 < machine.numStates)
    (hrightStack : ∀ symbol ∈ right.2,
      symbol < machine.numStackSymbols) :
    emptyStackLanguage machine left = emptyStackLanguage machine right ↔
      ObservableTraceEquivalent machine left right := by
  constructor
  · intro hlanguage word
    induction word using List.reverseRecOn with
    | nil =>
        unfold IsObservableTrace
        rfl
    | append_singleton word action ih =>
        rw [observableTrace_append_singleton_iff hnormal
            hleftState hleftStack,
          observableTrace_append_singleton_iff hnormal
            hrightState hrightStack]
        have hmember :
            word ∈ emptyStackLanguage machine left ↔
              word ∈ emptyStackLanguage machine right := by
          rw [hlanguage]
        exact and_congr ih (not_congr hmember)
  · intro htrace
    apply Set.ext
    intro word
    rw [mem_emptyStackLanguage_iff_trace_and_not_extension hnormal
        hleftState hleftStack word witness,
      mem_emptyStackLanguage_iff_trace_and_not_extension hnormal
        hrightState hrightStack word witness]
    exact and_congr (htrace word)
      (not_congr (htrace (word ++ [witness])))

/-- Both normalized configurations are compared as ground terms in the same
translated first-order grammar, and grammar trace equivalence is exactly
observable-trace equivalence of those configurations. -/
public theorem configurationTerm_traceEquivalent_iff_observableTraceEquivalent
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    {left right : Configuration}
    (hleftState : left.1 < machine.numStates)
    (hleftStack : ∀ symbol ∈ left.2,
      symbol < machine.numStackSymbols)
    (hrightState : right.1 < machine.numStates)
    (hrightStack : ∀ symbol ∈ right.2,
      symbol < machine.numStackSymbols) :
    (grammar machine).TraceEquivalent
        (configurationTerm machine left.1 left.2)
        (configurationTerm machine right.1 right.2) ↔
      ObservableTraceEquivalent machine left right := by
  constructor
  · intro hgrammar word
    have hgrammarWord :
        (grammar machine).IsTrace
            (configurationTerm machine left.1 left.2)
            (word.map Sum.inl) ↔
          (grammar machine).IsTrace
            (configurationTerm machine right.1 right.2)
            (word.map Sum.inl) := by
      change word.map Sum.inl ∈ (grammar machine).traceLanguage
          (configurationTerm machine left.1 left.2) ↔
        word.map Sum.inl ∈ (grammar machine).traceLanguage
          (configurationTerm machine right.1 right.2)
      rw [hgrammar]
    exact (grammar_isTrace_map_inl_iff hnormal hleftState
      hleftStack word).symm.trans (hgrammarWord.trans
        (grammar_isTrace_map_inl_iff hnormal hrightState
          hrightStack word))
  · intro hobservable
    apply Set.ext
    intro labels
    change (grammar machine).IsTrace
        (configurationTerm machine left.1 left.2) labels ↔
      (grammar machine).IsTrace
        (configurationTerm machine right.1 right.2) labels
    rw [grammar_isTrace_iff_exists_observableWord hnormal
        hleftState hleftStack,
      grammar_isTrace_iff_exists_observableWord hnormal
        hrightState hrightStack]
    constructor
    · rintro ⟨word, hlabels, htrace⟩
      exact ⟨word, hlabels, (hobservable word).mp htrace⟩
    · rintro ⟨word, hlabels, htrace⟩
      exact ⟨word, hlabels, (hobservable word).mpr htrace⟩

/-- Appendix-1 reduction theorem at the normalized pair/configuration level.
The two terms are ground terms of one shared grammar, and their full grammar
trace equivalence is equivalent to equality of the normalized empty-stack
languages. -/
public theorem configurationTerm_traceEquivalent_iff_emptyStackLanguage_eq
    [DecidableEq Action] {machine : EncodedDPDA Action}
    {alphabet : List Action}
    (hnormal : Machine.PoppingComplete machine alphabet)
    (witness : Action) {left right : Configuration}
    (hleftState : left.1 < machine.numStates)
    (hleftStack : ∀ symbol ∈ left.2,
      symbol < machine.numStackSymbols)
    (hrightState : right.1 < machine.numStates)
    (hrightStack : ∀ symbol ∈ right.2,
      symbol < machine.numStackSymbols) :
    (grammar machine).TraceEquivalent
        (configurationTerm machine left.1 left.2)
        (configurationTerm machine right.1 right.2) ↔
      emptyStackLanguage machine left = emptyStackLanguage machine right := by
  rw [configurationTerm_traceEquivalent_iff_observableTraceEquivalent
    hnormal hleftState hleftStack hrightState hrightStack]
  exact (emptyStackLanguage_eq_iff_observableTraceEquivalent hnormal
    witness hleftState hleftStack hrightState hrightStack).symm

/-! ## Explicit preprocessing dependency -/

/-- Data promised by the still-separate effective normalization from arbitrary
final-state encoded DPDAs to the prefix-free empty-stack, popping/complete
configuration problem consumed above.  This structure is a theorem target, not
an assumption used to expose a decision procedure. -/
public structure NormalizationResult [DecidableEq Action]
    (source : EncodedDPDA Action) where
  machine : EncodedDPDA Action
  alphabet : List Action
  initialState : ℕ
  initialStack : List ℕ
  normal : Machine.PoppingComplete machine alphabet

end DPDAToFirstOrder

end DCFEquivalence
