module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SufficientBasisReduction

@[expose]
public section

/-!
# The exposing-successor normal form

Jančar's balancing argument is stated for deterministic first-order grammars
in which every formal successor of every ranked symbol can be exposed by a
finite action word.  This file records that condition directly for the finite
graph semantics used in this development.

The witnesses and the resulting constant `exposureBound` are semantic here.
For the grammars produced by the DPDA translation they are supplied by the
explicit popping computations of the normalized machine.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- The one-node graph denoting the variable `x`. -/
@[expose] public def variableTerm (x : ℕ) : RegularTerm :=
  ([.inl x], 0)

/-- The finite open term `X(x₀,…,xₙ₋₁)`.  The root is node zero and
the variable nodes occupy positions `1,…,n`. -/
@[expose] public def symbolTemplate (X rank : ℕ) : RegularTerm :=
  (.inr (X, (List.range rank).map (fun i => i + 1)) ::
      (List.range rank).map Sum.inl,
    0)

@[simp] public theorem variableTerm_nodes (x : ℕ) :
    (variableTerm x).nodes = [.inl x] := rfl

@[simp] public theorem variableTerm_root (x : ℕ) :
    (variableTerm x).root = 0 := rfl

@[simp] public theorem variableTerm_rootNode? (x : ℕ) :
    (variableTerm x).rootNode? = some (.inl x) := by
  simp [variableTerm, rootNode?, nodeAt?, nodes, root]

@[simp] public theorem symbolTemplate_root (X rank : ℕ) :
    (symbolTemplate X rank).root = 0 := rfl

@[simp] public theorem symbolTemplate_rootApplication? (X rank : ℕ) :
    (symbolTemplate X rank).rootApplication? =
      some (X, (List.range rank).map (fun i => i + 1)) := by
  simp [symbolTemplate, rootApplication?, rootNode?, nodeAt?, nodes, root]

public theorem symbolTemplate_variableNode
    (X rank i : ℕ) (hi : i < rank) :
    (symbolTemplate X rank).nodeAt? (i + 1) = some (.inl i) := by
  unfold symbolTemplate nodeAt? nodes
  simp [hi]

public theorem symbolTemplate_referenceClosed (X rank : ℕ) :
    (symbolTemplate X rank).ReferenceClosed := by
  constructor
  · simp [symbolTemplate, nodes, root]
  · intro i Y children hnode child hchild
    cases i with
    | zero =>
        simp [symbolTemplate, nodeAt?, nodes] at hnode
        rcases hnode with ⟨rfl, rfl⟩
        obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hchild
        simp [symbolTemplate, nodes] at hsource ⊢
        omega
    | succ i =>
        simp [symbolTemplate, nodeAt?, nodes] at hnode

/-- A symbol template is ranked and well formed exactly when its declared
arity agrees with the grammar's rank table. -/
public theorem symbolTemplate_wellFormed
    {ranks : List ℕ} {X rank : ℕ}
    (hrank : ranks[X]? = some rank) :
    (symbolTemplate X rank).WellFormed ranks rank := by
  unfold WellFormed wellFormedCode
  rw [Bool.and_eq_true]
  constructor
  · simp [symbolTemplate, root, nodes]
  · rw [List.all_eq_true]
    intro node hnode
    simp only [symbolTemplate, nodes, List.mem_cons] at hnode
    rcases hnode with rfl | hnode
    · simp only [nodeWellFormedCode, hrank, List.length_map,
          List.length_range, decide_eq_true_eq, Bool.and_eq_true,
          List.all_eq_true]
      constructor
      · trivial
      · intro child hchild
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hchild
        simp [symbolTemplate, nodes] at hi ⊢
        omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hnode
      simp [nodeWellFormedCode] at hi ⊢
      exact hi

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A formal successor position `(X,i)` of a ranked symbol in the grammar. -/
public abbrev SuccessorPosition
    (g : EncodedFirstOrderGrammar Action) :=
  Σ X : Fin g.ranks.length, Fin (g.ranks.get X)

/-- Explicit finite enumeration of all formal successor positions. -/
@[expose] public def successorPositions
    (g : EncodedFirstOrderGrammar Action) : List g.SuccessorPosition :=
  (List.finRange g.ranks.length).flatMap fun X =>
    (List.finRange (g.ranks.get X)).map fun i => ⟨X, i⟩

omit [DecidableEq Action] in
public theorem mem_successorPositions
    (g : EncodedFirstOrderGrammar Action) (position : g.SuccessorPosition) :
    position ∈ g.successorPositions := by
  rcases position with ⟨X, i⟩
  simp [successorPositions, List.mem_finRange]

/-- Execute a word containing only ordinary grammar actions. -/
@[expose] public def runActions?
    (g : EncodedFirstOrderGrammar Action) (word : List Action)
    (source : RegularTerm) : Option RegularTerm :=
  g.run? (word.map Sum.inl) source

/-- An ordinary action word exposes a formal successor when it rewrites the
open root template to that variable, up to equality of graph unfoldings. -/
@[expose] public def ExposesSuccessor
    (g : EncodedFirstOrderGrammar Action)
    (position : g.SuccessorPosition) (word : List Action) : Prop :=
  ∃ target,
    g.runActions? word
      (RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)) = some target ∧
    target.UnfoldingEquivalent (RegularTerm.variableTerm position.2)

/-- Jančar normal form: every formal successor of every ranked symbol has
an exposing word. -/
@[expose] public def ExposingNormalForm
    (g : EncodedFirstOrderGrammar Action) : Prop :=
  ∀ position : g.SuccessorPosition, ∃ word, g.ExposesSuccessor position word

/-- Existence of a numerical length carrying an exposing word. -/
public theorem exists_exposingLength
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (position : g.SuccessorPosition) :
    ∃ length, ∃ word : List Action,
      word.length = length ∧ g.ExposesSuccessor position word := by
  obtain ⟨word, hexposes⟩ := hnormal position
  exact ⟨word.length, word, rfl, hexposes⟩

/-- The least possible length of an exposing word.  Using the least length,
rather than an arbitrary choice from the normal-form proof, makes the bound
independent of proof terms and stable under conservative grammar extensions. -/
noncomputable def exposingLength
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (position : g.SuccessorPosition) : ℕ := by
  classical
  exact Nat.find (exists_exposingLength hnormal position)

/-- A shortest exposing word selected at the canonical least length. -/
noncomputable def exposingWord
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (position : g.SuccessorPosition) :
    List Action := by
  classical
  exact Classical.choose (Nat.find_spec
    (exists_exposingLength hnormal position))

public theorem exposingWord_length
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (position : g.SuccessorPosition) :
    (g.exposingWord hnormal position).length =
      g.exposingLength hnormal position := by
  classical
  exact (Classical.choose_spec (Nat.find_spec
    (exists_exposingLength hnormal position))).1

public theorem exposingWord_exposes
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (position : g.SuccessorPosition) :
    g.ExposesSuccessor position (g.exposingWord hnormal position) := by
  classical
  exact (Classical.choose_spec (Nat.find_spec
    (exists_exposingLength hnormal position))).2

/-- Every exposing word is at least as long as the canonical shortest one. -/
public theorem exposingLength_le
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (position : g.SuccessorPosition)
    {word : List Action} (hexposes : g.ExposesSuccessor position word) :
    g.exposingLength hnormal position ≤ word.length := by
  classical
  exact Nat.find_min' (exists_exposingLength hnormal position)
    ⟨word, rfl, hexposes⟩

/-- One plus the maximum length of the selected exposing words.  This is the
constant `M₀` in the balancing proof. -/
noncomputable def exposureBound
    (g : EncodedFirstOrderGrammar Action) (hnormal : g.ExposingNormalForm) : ℕ := by
  exact 1 + ((g.successorPositions.map fun position =>
    (g.exposingWord hnormal position).length).foldr max 0)

public theorem exposingWord_length_lt_exposureBound
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (position : g.SuccessorPosition) :
    (g.exposingWord hnormal position).length < g.exposureBound hnormal := by
  unfold exposureBound
  have hle : (g.exposingWord hnormal position).length ≤
      (g.successorPositions.map fun position =>
        (g.exposingWord hnormal position).length).foldr max 0 :=
    List.le_max_of_le
      (List.mem_map.mpr ⟨position, g.mem_successorPositions position, rfl⟩)
      (le_refl _)
  omega

public theorem exposureBound_pos
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) : 0 < g.exposureBound hnormal := by
  unfold exposureBound
  omega

/-! ## The exposable core of an arbitrary grammar -/

/-- A successor position together with the semantic fact that some ordinary
action word exposes it.  This lets the balancing construction work directly
with a grammar that has unexposable (and therefore trace-irrelevant) formal
arguments, without first renaming every ranked symbol. -/
public def ExposablePosition
    (g : EncodedFirstOrderGrammar Action) :=
  { position : g.SuccessorPosition //
    ∃ word : List Action, g.ExposesSuccessor position word }

/-- Select an exposing word at exposable positions and the empty word at the
remaining positions.  Keeping the domain equal to the explicit complete
position list avoids dependent filtering in later maximum calculations. -/
noncomputable def coreExposingWord
    (g : EncodedFirstOrderGrammar Action)
    (position : g.SuccessorPosition) : List Action := by
  classical
  exact if h : ∃ word : List Action, g.ExposesSuccessor position word then
    Classical.choose h
  else []

public theorem coreExposingWord_exposes
    (g : EncodedFirstOrderGrammar Action)
    (position : g.ExposablePosition) :
    g.ExposesSuccessor position.1 (g.coreExposingWord position.1) := by
  classical
  unfold coreExposingWord
  simp only [dif_pos position.2]
  exact Classical.choose_spec position.2

/-- One plus the greatest selected exposing-word length in the finite core. -/
noncomputable def coreExposureBound
    (g : EncodedFirstOrderGrammar Action) : ℕ :=
  1 + ((g.successorPositions.map fun position =>
    (g.coreExposingWord position).length).foldr max 0)

public theorem coreExposingWord_length_lt_coreExposureBound
    (g : EncodedFirstOrderGrammar Action)
    (position : g.ExposablePosition) :
    (g.coreExposingWord position.1).length < g.coreExposureBound := by
  unfold coreExposureBound
  have hle : (g.coreExposingWord position.1).length ≤
      (g.successorPositions.map fun position =>
        (g.coreExposingWord position).length).foldr max 0 :=
    List.le_max_of_le
      (List.mem_map.mpr
        ⟨position.1, g.mem_successorPositions position.1, rfl⟩)
      (le_refl _)
  omega

public theorem coreExposureBound_pos
    (g : EncodedFirstOrderGrammar Action) : 0 < g.coreExposureBound := by
  unfold coreExposureBound
  omega

/-- The normal-form bound and core bound agree extensionally at the only point
needed later: every selected normal-form witness is shorter than the core-free
bound `exposureBound`. -/
public theorem exposes_of_exposingNormalForm
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (position : g.SuccessorPosition) :
    ∃ word, g.ExposesSuccessor position word :=
  hnormal position

end EncodedFirstOrderGrammar

end DCFEquivalence
