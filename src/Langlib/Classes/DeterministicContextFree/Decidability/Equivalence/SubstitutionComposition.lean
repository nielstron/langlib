module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GroundStepPreservation

@[expose]
public section

/-!
# Composition of regular-term substitutions

The graph implementation of simultaneous substitution deliberately shares
argument graphs and retains unreachable variable nodes.  Substitution is
therefore not associative as raw code, but it is associative as a regular
tree.  This file gives the explicit three-layer bisimulation: outer-schema
nodes, copied context nodes, and copied argument nodes.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Substitute the final arguments into every intermediate context. -/
@[expose] public def composedContexts
    (contexts arguments : List RegularTerm) : List RegularTerm :=
  contexts.map fun context => context.instantiate arguments

/-- The explicit relation witnessing substitution composition. -/
@[expose] public def CompositionRelation
    (outer : RegularTerm) (contexts arguments : List RegularTerm)
    (leftIndex rightIndex : ℕ) : Prop :=
  (∃ i, i < outer.nodes.length ∧
      leftIndex = i ∧ rightIndex = i) ∨
  (∃ x context i,
      contexts[x]? = some context ∧ i < context.nodes.length ∧
      leftIndex = argumentOffset outer.nodes.length contexts x + i ∧
      rightIndex = argumentOffset outer.nodes.length
        (composedContexts contexts arguments) x + i) ∨
  (∃ x context y argument i,
      contexts[x]? = some context ∧
      arguments[y]? = some argument ∧ i < argument.nodes.length ∧
      leftIndex = argumentOffset
          (outer.instantiate contexts).nodes.length arguments y + i ∧
      rightIndex =
        argumentOffset outer.nodes.length
            (composedContexts contexts arguments) x +
          (argumentOffset context.nodes.length arguments y + i))

private theorem variable_lt_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound)
    {i x : ℕ} (hnode : term.nodeAt? i = some (.inl x)) :
    x < variableBound := by
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inl x : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  simpa [nodeWellFormedCode] using of_decide_eq_true hwell

private theorem get_context
    {contexts : List RegularTerm} {x : ℕ} (hx : x < contexts.length) :
    ∃ context, contexts[x]? = some context := by
  exact ⟨contexts[x], List.getElem?_eq_getElem hx⟩

private theorem get_argument
    {arguments : List RegularTerm} {y : ℕ} (hy : y < arguments.length) :
    ∃ argument, arguments[y]? = some argument := by
  exact ⟨arguments[y], List.getElem?_eq_getElem hy⟩

private theorem get_composedContext
    {contexts arguments : List RegularTerm} {x : ℕ}
    {context : RegularTerm} (hcontext : contexts[x]? = some context) :
    (composedContexts contexts arguments)[x]? =
      some (context.instantiate arguments) := by
  simp [composedContexts, List.getElem?_map, hcontext]

private theorem forall₂_map_relation
    {A : Type} {R : ℕ → ℕ → Prop} (left right : A → ℕ)
    (values : List A) (h : ∀ value ∈ values, R (left value) (right value)) :
    List.Forall₂ R (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun tail htail => h tail (by simp [htail]))

private theorem contextResolve_relation
    {outer : RegularTerm} {contexts arguments : List RegularTerm}
    (harguments : ∀ argument ∈ arguments, argument.ReferenceClosed)
    {x : ℕ} {context : RegularTerm}
    (hcontext : contexts[x]? = some context)
    {i : ℕ} (hi : i < context.nodes.length) :
    CompositionRelation outer contexts arguments
      ((outer.instantiate contexts).resolveRHSRef arguments
        (argumentOffset outer.nodes.length contexts x + i))
      (argumentOffset outer.nodes.length
          (composedContexts contexts arguments) x +
        context.resolveRHSRef arguments i) := by
  let source : RawNode := context.nodes[i]
  have hsource : context.nodeAt? i = some source := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hi, rfl⟩
  have hcopied := instantiate_nodeAt?_argument outer contexts
    hcontext hsource
  cases hkind : source with
  | inl y =>
      have hvariable : context.nodeAt? i = some (.inl y) := by
        simpa [hkind] using hsource
      have hcopiedVariable : (outer.instantiate contexts).nodeAt?
          (argumentOffset outer.nodes.length contexts x + i) =
          some (.inl y) := by
        simpa [hkind, shiftNode] using hcopied
      cases hargument : arguments[y]? with
      | none =>
          have hleftResolve :
              (outer.instantiate contexts).resolveRHSRef arguments
                  (argumentOffset outer.nodes.length contexts x + i) =
                argumentOffset outer.nodes.length contexts x + i := by
            simp [resolveRHSRef, hcopiedVariable, argumentRoot?, hargument]
          have hrightResolve : context.resolveRHSRef arguments i = i := by
            simp [resolveRHSRef, hvariable, argumentRoot?, hargument]
          rw [hleftResolve, hrightResolve]
          right; left
          exact ⟨x, context, i, hcontext, hi, rfl, rfl⟩
      | some argument =>
          have hargumentBound : y < arguments.length :=
            (List.getElem?_eq_some_iff.mp hargument).1
          have hargumentRoot : argument.root < argument.nodes.length := by
            exact (harguments argument
              (List.mem_of_getElem? hargument)).1
          right; right
          refine ⟨x, context, y, argument, argument.root,
            hcontext, hargument, hargumentRoot, ?_, ?_⟩
          · simp [resolveRHSRef, hcopiedVariable, argumentRoot?, hargument]
          · simp [resolveRHSRef, hvariable, argumentRoot?, hargument]
    | inr app =>
      rcases app with ⟨X, children⟩
      have happ : context.nodeAt? i = some (.inr (X, children)) := by
        simpa [hkind] using hsource
      have hcopiedApp : (outer.instantiate contexts).nodeAt?
          (argumentOffset outer.nodes.length contexts x + i) =
          some (.inr (X, children.map
            (argumentOffset outer.nodes.length contexts x + ·))) := by
        simpa [hkind, shiftNode] using hcopied
      have hleftResolve :
          (outer.instantiate contexts).resolveRHSRef arguments
              (argumentOffset outer.nodes.length contexts x + i) =
            argumentOffset outer.nodes.length contexts x + i := by
        simp [resolveRHSRef, hcopiedApp]
      have hrightResolve : context.resolveRHSRef arguments i = i := by
        simp [resolveRHSRef, happ]
      rw [hleftResolve, hrightResolve]
      right; left
      exact ⟨x, context, i, hcontext, hi, rfl, rfl⟩

private theorem outerResolve_relation
    {ranks : List ℕ} {outer : RegularTerm}
    {contexts arguments : List RegularTerm}
    (houter : outer.WellFormed ranks contexts.length)
    (hcontexts : ∀ context ∈ contexts, context.ReferenceClosed)
    (harguments : ∀ argument ∈ arguments, argument.ReferenceClosed)
    {i : ℕ} (hi : i < outer.nodes.length) :
    CompositionRelation outer contexts arguments
      ((outer.instantiate contexts).resolveRHSRef arguments
        (outer.resolveRHSRef contexts i))
      (outer.resolveRHSRef (composedContexts contexts arguments) i) := by
  let source : RawNode := outer.nodes[i]
  have hsource : outer.nodeAt? i = some source := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hi, rfl⟩
  cases hkind : source with
  | inl x =>
      have hvariable : outer.nodeAt? i = some (.inl x) := by
        simpa [hkind] using hsource
      have hx := variable_lt_of_wellFormed houter hvariable
      obtain ⟨context, hcontext⟩ := get_context hx
      have hcontextRoot := (List.getElem?_eq_some_iff.mp hcontext).1
      have hleftOuterResolve : outer.resolveRHSRef contexts i =
          argumentOffset outer.nodes.length contexts x + context.root := by
        simp [resolveRHSRef, hvariable, argumentRoot?, hcontext]
      have hrightContext := get_composedContext
        (arguments := arguments) hcontext
      have hrightOuterResolve :
          outer.resolveRHSRef (composedContexts contexts arguments) i =
            argumentOffset outer.nodes.length
                (composedContexts contexts arguments) x +
              (context.instantiate arguments).root := by
        simp [resolveRHSRef, hvariable, argumentRoot?, hrightContext]
      rw [hleftOuterResolve, hrightOuterResolve]
      change CompositionRelation outer contexts arguments
        ((outer.instantiate contexts).resolveRHSRef arguments
          (argumentOffset outer.nodes.length contexts x + context.root))
        (argumentOffset outer.nodes.length
            (composedContexts contexts arguments) x +
          context.resolveRHSRef arguments context.root)
      exact contextResolve_relation harguments hcontext
        (hcontexts context (List.mem_of_getElem? hcontext)).1
  | inr app =>
      rcases app with ⟨X, children⟩
      have happ : outer.nodeAt? i = some (.inr (X, children)) := by
        simpa [hkind] using hsource
      have houterResolve : outer.resolveRHSRef contexts i = i := by
        simp [resolveRHSRef, happ]
      have hcomposedResolve : outer.resolveRHSRef
          (composedContexts contexts arguments) i = i := by
        simp [resolveRHSRef, happ]
      have hintermediateNode := instantiate_nodeAt?_rhs outer contexts hi
      rw [happ] at hintermediateNode
      have hintermediateResolve :
          (outer.instantiate contexts).resolveRHSRef arguments i = i := by
        simp [resolveRHSRef, hintermediateNode, instantiateNode]
      rw [houterResolve, hcomposedResolve, hintermediateResolve]
      left
      exact ⟨i, hi, rfl, rfl⟩

private theorem compositionRelation_isBisimulation
    {ranks : List ℕ} {outer : RegularTerm}
    {contexts arguments : List RegularTerm}
    (houter : outer.WellFormed ranks contexts.length)
    (hcontexts : ∀ context ∈ contexts, context.ReferenceClosed)
    (harguments : ∀ argument ∈ arguments, argument.ReferenceClosed) :
    ((outer.instantiate contexts).instantiate arguments).IsBisimulation
      (outer.instantiate (composedContexts contexts arguments))
      (CompositionRelation outer contexts arguments) := by
  intro leftIndex rightIndex hrelation
  rcases hrelation with houterNode | hrest
  · obtain ⟨i, hi, hleftIndex, hrightIndex⟩ := houterNode
    subst leftIndex
    subst rightIndex
    let source : RawNode := outer.nodes[i]
    have hsource : outer.nodeAt? i = some source := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hi, rfl⟩
    have hfirstNode := instantiate_nodeAt?_rhs outer contexts hi
    rw [hsource] at hfirstNode
    have hiFirst : i < (outer.instantiate contexts).nodes.length :=
      (List.getElem?_eq_some_iff.mp hfirstNode).1
    have hleftNode := instantiate_nodeAt?_rhs
      (outer.instantiate contexts) arguments hiFirst
    rw [hfirstNode] at hleftNode
    have hrightNode := instantiate_nodeAt?_rhs outer
      (composedContexts contexts arguments) hi
    rw [hsource] at hrightNode
    cases hkind : source with
    | inl x =>
        have hleftVariable :
            ((outer.instantiate contexts).instantiate arguments).nodeAt? i =
              some (.inl x) := by
          simpa [hkind, instantiateNode] using hleftNode
        have hrightVariable :
            (outer.instantiate (composedContexts contexts arguments)).nodeAt?
                i = some (.inl x) := by
          simpa [hkind, instantiateNode] using hrightNode
        simp [NodeCompatible, RawCompatible, hleftVariable, hrightVariable]
    | inr app =>
        rcases app with ⟨X, children⟩
        have hleftApplication :
            ((outer.instantiate contexts).instantiate arguments).nodeAt? i =
              some (.inr (X, children.map fun child =>
                (outer.instantiate contexts).resolveRHSRef arguments
                  (outer.resolveRHSRef contexts child))) := by
          simpa [hkind, instantiateNode, List.map_map,
            Function.comp_def] using hleftNode
        have hrightApplication :
            (outer.instantiate (composedContexts contexts arguments)).nodeAt?
                i = some (.inr (X, children.map fun child =>
                  outer.resolveRHSRef
                    (composedContexts contexts arguments) child)) := by
          simpa [hkind, instantiateNode] using hrightNode
        unfold NodeCompatible
        rw [hleftApplication, hrightApplication]
        refine ⟨rfl, forall₂_map_relation _ _ children ?_⟩
        intro child hchild
        exact outerResolve_relation houter hcontexts harguments
          ((referenceClosed_of_wellFormed houter).2 i X children
            (by simpa [hkind] using hsource) child hchild)
  · rcases hrest with hcontextNode | hargumentNode
    · obtain ⟨x, context, i, hcontext, hi, rfl, rfl⟩ := hcontextNode
      let contextOffset := argumentOffset outer.nodes.length contexts x
      let composedOffset := argumentOffset outer.nodes.length
        (composedContexts contexts arguments) x
      let source : RawNode := context.nodes[i]
      have hsource : context.nodeAt? i = some source := by
        unfold nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hi, rfl⟩
      have hfirstNode := instantiate_nodeAt?_argument outer contexts
        hcontext hsource
      have hiFirst : contextOffset + i <
          (outer.instantiate contexts).nodes.length := by
        exact (List.getElem?_eq_some_iff.mp hfirstNode).1
      have hleftNode := instantiate_nodeAt?_rhs
        (outer.instantiate contexts) arguments hiFirst
      rw [hfirstNode] at hleftNode
      have hcomposedContext := get_composedContext
        (arguments := arguments) hcontext
      have hinnerNode := instantiate_nodeAt?_rhs context arguments hi
      rw [hsource] at hinnerNode
      have hrightNode := instantiate_nodeAt?_argument outer
        (composedContexts contexts arguments) hcomposedContext hinnerNode
      cases hkind : source with
      | inl y =>
          have hleftVariable :
              ((outer.instantiate contexts).instantiate arguments).nodeAt?
                  (contextOffset + i) = some (.inl y) := by
            simpa [contextOffset, hkind, shiftNode, instantiateNode]
              using hleftNode
          have hrightVariable :
              (outer.instantiate (composedContexts contexts arguments)).nodeAt?
                  (composedOffset + i) = some (.inl y) := by
            simpa [composedOffset, hkind, shiftNode, instantiateNode]
              using hrightNode
          unfold NodeCompatible
          rw [show
            ((outer.instantiate contexts).instantiate arguments).nodeAt?
                (argumentOffset outer.nodes.length contexts x + i) =
              some (.inl y) by
                simpa [contextOffset] using hleftVariable,
            show
              (outer.instantiate
                (composedContexts contexts arguments)).nodeAt?
                  (argumentOffset outer.nodes.length
                    (composedContexts contexts arguments) x + i) =
                some (.inl y) by
                  simpa [composedOffset] using hrightVariable]
          rfl
      | inr app =>
          rcases app with ⟨X, children⟩
          have hleftApplication :
              ((outer.instantiate contexts).instantiate arguments).nodeAt?
                  (contextOffset + i) =
                some (.inr (X, children.map fun child =>
                  (outer.instantiate contexts).resolveRHSRef arguments
                    (contextOffset + child))) := by
            simpa [contextOffset, hkind, shiftNode, instantiateNode,
              List.map_map, Function.comp_def] using hleftNode
          have hrightApplication :
              (outer.instantiate (composedContexts contexts arguments)).nodeAt?
                  (composedOffset + i) =
                some (.inr (X, children.map fun child =>
                  composedOffset + context.resolveRHSRef arguments child)) := by
            simpa [composedOffset, hkind, shiftNode, instantiateNode,
              List.map_map, Function.comp_def, Nat.add_assoc]
              using hrightNode
          unfold NodeCompatible
          rw [hleftApplication, hrightApplication]
          refine ⟨rfl, forall₂_map_relation _ _ children ?_⟩
          intro child hchild
          exact contextResolve_relation harguments hcontext
            ((hcontexts context (List.mem_of_getElem? hcontext)).2
              i X children (by simpa [hkind] using hsource) child hchild)
    · obtain ⟨x, context, y, argument, i, hcontext, hargument, hi,
        rfl, rfl⟩ := hargumentNode
      let leftOffset := argumentOffset
        (outer.instantiate contexts).nodes.length arguments y
      let composedOffset := argumentOffset outer.nodes.length
        (composedContexts contexts arguments) x
      let innerOffset := argumentOffset context.nodes.length arguments y
      let source : RawNode := argument.nodes[i]
      have hsource : argument.nodeAt? i = some source := by
        unfold nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hi, rfl⟩
      have hleftNode := instantiate_nodeAt?_argument
        (outer.instantiate contexts) arguments hargument hsource
      have hcomposedContext := get_composedContext
        (arguments := arguments) hcontext
      have hinnerNode := instantiate_nodeAt?_argument context arguments
        hargument hsource
      have hrightNode := instantiate_nodeAt?_argument outer
        (composedContexts contexts arguments) hcomposedContext hinnerNode
      cases hkind : source with
      | inl z =>
          have hleftVariable :
              ((outer.instantiate contexts).instantiate arguments).nodeAt?
                  (leftOffset + i) = some (.inl z) := by
            simpa [leftOffset, hkind, shiftNode] using hleftNode
          have hrightVariable :
              (outer.instantiate (composedContexts contexts arguments)).nodeAt?
                  (composedOffset + (innerOffset + i)) =
                some (.inl z) := by
            simpa [composedOffset, innerOffset, hkind, shiftNode,
              Nat.add_assoc] using hrightNode
          unfold NodeCompatible
          rw [show
            ((outer.instantiate contexts).instantiate arguments).nodeAt?
                (argumentOffset (outer.instantiate contexts).nodes.length
                  arguments y + i) = some (.inl z) by
                simpa [leftOffset] using hleftVariable,
            show
              (outer.instantiate
                (composedContexts contexts arguments)).nodeAt?
                  (argumentOffset outer.nodes.length
                      (composedContexts contexts arguments) x +
                    (argumentOffset context.nodes.length arguments y + i)) =
                some (.inl z) by
                  simpa [composedOffset, innerOffset] using hrightVariable]
          rfl
      | inr app =>
          rcases app with ⟨X, children⟩
          have hleftApplication :
              ((outer.instantiate contexts).instantiate arguments).nodeAt?
                  (leftOffset + i) =
                some (.inr (X, children.map (leftOffset + ·))) := by
            simpa [leftOffset, hkind, shiftNode] using hleftNode
          have hrightApplication :
              (outer.instantiate (composedContexts contexts arguments)).nodeAt?
                  (composedOffset + (innerOffset + i)) =
                some (.inr (X, children.map fun child =>
                  composedOffset + (innerOffset + child))) := by
            simpa [composedOffset, innerOffset, hkind, shiftNode,
              List.map_map, Function.comp_def, Nat.add_assoc]
              using hrightNode
          unfold NodeCompatible
          rw [hleftApplication, hrightApplication]
          refine ⟨rfl, forall₂_map_relation _ _ children ?_⟩
          intro child hchild
          right; right
          exact ⟨x, context, y, argument, child, hcontext, hargument,
            (harguments argument (List.mem_of_getElem? hargument)).2
              i X children (by simpa [hkind] using hsource) child hchild,
            rfl, rfl⟩

/-- Graph substitution is associative up to equality of the denoted regular
tree.  Intermediate contexts need only be reference closed; variables outside
the final argument tuple remain the same variables on both sides. -/
public theorem instantiate_comp_unfoldingEquivalent
    {ranks : List ℕ} {outer : RegularTerm}
    {contexts arguments : List RegularTerm}
    (houter : outer.WellFormed ranks contexts.length)
    (hcontexts : ∀ context ∈ contexts, context.ReferenceClosed)
    (harguments : ∀ argument ∈ arguments, argument.ReferenceClosed) :
    ((outer.instantiate contexts).instantiate arguments).UnfoldingEquivalent
      (outer.instantiate (composedContexts contexts arguments)) := by
  refine ⟨CompositionRelation outer contexts arguments, ?_,
    compositionRelation_isBisimulation houter hcontexts harguments⟩
  change CompositionRelation outer contexts arguments
    ((outer.instantiate contexts).resolveRHSRef arguments
      (outer.resolveRHSRef contexts outer.root))
    (outer.resolveRHSRef (composedContexts contexts arguments) outer.root)
  exact outerResolve_relation houter hcontexts harguments
    (referenceClosed_of_wellFormed houter).1

end RegularTerm

end DCFEquivalence
