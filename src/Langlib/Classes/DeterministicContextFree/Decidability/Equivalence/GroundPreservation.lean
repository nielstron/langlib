module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisSemantics

@[expose]
public section

/-!
# Reachable groundness after unary substitution and tying

Substitution deliberately retains the variable nodes of an open context as
unreachable graph garbage.  These lemmas verify that the semantic/runtime
notion of `RegularTerm.Ground` ignores precisely that garbage: substituting a
ground argument in a well-formed unary context, and tying a nontrivial unary
context into its regular limit, both produce ground terms.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- The indices at which a raw graph stores application nodes. -/
private def applicationSupport (term : RegularTerm) : List ℕ :=
  (List.range term.nodes.length).filter fun i =>
    match term.nodeAt? i with
    | some (.inr _) => true
    | _ => false

private theorem mem_applicationSupport_iff
    {term : RegularTerm} {i : ℕ} :
    i ∈ applicationSupport term ↔
      ∃ X children, term.nodeAt? i = some (.inr (X, children)) := by
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
    List.Sublist (applicationSupport term) (List.range term.nodes.length) :=
  List.filter_sublist

/-- If the root and every child of every application node are applications,
the application indices themselves form a finite ground support. -/
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
      obtain ⟨X, children, hnode⟩ :=
        mem_applicationSupport_iff.mp hi
      refine ⟨X, children, hnode, ?_⟩
      intro child hchild
      exact mem_applicationSupport_iff.mpr
        (hchildren i X children hnode child hchild)

/-- Ranked well-formedness implies the shape-only condition used by runtime
groundness. -/
public theorem shapeWellFormed_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound) :
    term.ShapeWellFormed ranks := by
  unfold WellFormed wellFormedCode at hterm
  unfold ShapeWellFormed shapeWellFormedCode
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨hterm.1, ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  have hwell := (List.all_eq_true.mp hterm.2) node hnode
  cases node with
  | inl x => rfl
  | inr app =>
      simpa [nodeWellFormedCode, nodeShapeWellFormedCode] using hwell

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

private theorem root_application_of_nontrivial_unary
    {ranks : List ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    (hnontrivial : context.nontrivialUnaryCode = true) :
    ∃ X children,
      context.nodeAt? context.root = some (.inr (X, children)) := by
  have hclosed := referenceClosed_of_wellFormed hcontext
  let rootNode : RawNode := context.nodes[context.root]'hclosed.1
  have hroot : context.nodeAt? context.root = some rootNode := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hclosed.1, rfl⟩
  cases hkind : rootNode with
  | inl x =>
      have hx : x < 1 := variable_lt_of_wellFormed hcontext (by
        simpa [hkind] using hroot)
      have hxzero : x = 0 := by omega
      subst x
      have hrootVariable : context.rootNode? = some (.inl 0) := by
        simpa [rootNode?, hkind] using hroot
      simp [nontrivialUnaryCode, hrootVariable] at hnontrivial
  | inr app =>
      rcases app with ⟨X, children⟩
      exact ⟨X, children, by simpa [hkind] using hroot⟩

private theorem closeUnaryReference_lt_of_referenceClosed
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {i : ℕ} (hi : i < context.nodes.length) :
    context.closeUnaryReference i < context.nodes.length := by
  unfold closeUnaryReference
  cases hnode : context.nodeAt? i with
  | none => exact hi
  | some node =>
      cases node with
      | inl x =>
          cases x with
          | zero => exact hclosed.1
          | succ x => exact hi
      | inr app => exact hi

/-- Tying a shape-correct, reference-closed unary graph preserves its global
rank and reference shape. -/
public theorem unaryLimit_shapeWellFormed
    {ranks : List ℕ} {context : RegularTerm}
    (hshape : context.ShapeWellFormed ranks)
    (hclosed : context.ReferenceClosed) :
    context.unaryLimit.ShapeWellFormed ranks := by
  unfold ShapeWellFormed shapeWellFormedCode at hshape ⊢
  rw [Bool.and_eq_true] at hshape ⊢
  refine ⟨?_, ?_⟩
  · apply decide_eq_true
    rw [unaryLimit_nodes, List.length_map]
    exact closeUnaryReference_lt_of_referenceClosed hclosed
      (of_decide_eq_true hshape.1)
  · apply List.all_eq_true.mpr
    intro node hnode
    rw [unaryLimit_nodes] at hnode
    obtain ⟨source, hsourceMem, rfl⟩ := List.mem_map.mp hnode
    have hsourceShape :=
      (List.all_eq_true.mp hshape.2) source hsourceMem
    cases source with
    | inl x => rfl
    | inr app =>
        rcases app with ⟨X, children⟩
        simp only [closeUnaryNode]
        unfold nodeShapeWellFormedCode at hsourceShape ⊢
        cases hrank : ranks[X]? with
        | none => simp [hrank] at hsourceShape
        | some rank =>
            simp only [hrank] at hsourceShape ⊢
            rw [Bool.and_eq_true] at hsourceShape ⊢
            refine ⟨by simpa using hsourceShape.1, ?_⟩
            apply List.all_eq_true.mpr
            intro child hchild
            obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
              List.mem_map.mp hchild
            apply decide_eq_true
            rw [unaryLimit_nodes, List.length_map]
            apply closeUnaryReference_lt_of_referenceClosed hclosed
            exact of_decide_eq_true
              ((List.all_eq_true.mp hsourceShape.2) sourceChild
                hsourceChild)

private theorem unaryLimit_application_child_is_application
    {ranks : List ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    (hnontrivial : context.nontrivialUnaryCode = true)
    {i X : ℕ} {children : List ℕ}
    (hnode : context.unaryLimit.nodeAt? i =
      some (.inr (X, children))) :
    ∀ child ∈ children, ∃ Y grandchildren,
      context.unaryLimit.nodeAt? child =
        some (.inr (Y, grandchildren)) := by
  have hclosed := referenceClosed_of_wellFormed hcontext
  have hroot := root_application_of_nontrivial_unary hcontext hnontrivial
  rw [unaryLimit_nodeAt?] at hnode
  cases hsource : context.nodeAt? i with
  | none => simp [hsource] at hnode
  | some source =>
      rw [hsource] at hnode
      cases source with
      | inl x => simp [closeUnaryNode] at hnode
      | inr app =>
          rcases app with ⟨Y, sourceChildren⟩
          simp only [Option.map_some, closeUnaryNode, Option.some.injEq,
            Sum.inr.injEq, Prod.mk.injEq] at hnode
          rcases hnode with ⟨hYX, hchildren⟩
          subst Y
          subst children
          intro child hchild
          obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
            List.mem_map.mp hchild
          have hsourceChildLt : sourceChild < context.nodes.length :=
            hclosed.2 i X sourceChildren hsource sourceChild hsourceChild
          let sourceNode : RawNode :=
            context.nodes[sourceChild]'hsourceChildLt
          have hsourceNode : context.nodeAt? sourceChild = some sourceNode := by
            unfold nodeAt?
            rw [List.getElem?_eq_some_iff]
            exact ⟨hsourceChildLt, rfl⟩
          cases hkind : sourceNode with
          | inl x =>
              have hx : x < 1 := variable_lt_of_wellFormed hcontext (by
                simpa [hkind] using hsourceNode)
              have hxzero : x = 0 := by omega
              subst x
              have hsourceVariable : context.nodeAt? sourceChild =
                  some (.inl 0) := by
                simpa [hkind] using hsourceNode
              obtain ⟨rootSymbol, rootChildren, hrootNode⟩ := hroot
              refine ⟨rootSymbol,
                rootChildren.map context.closeUnaryReference, ?_⟩
              have hclose : context.closeUnaryReference sourceChild =
                  context.root := by
                simp [closeUnaryReference, hsourceVariable]
              rw [hclose, unaryLimit_nodeAt?, hrootNode]
              rfl
          | inr targetApp =>
              rcases targetApp with ⟨targetSymbol, targetChildren⟩
              have hsourceApplication : context.nodeAt? sourceChild =
                  some (.inr (targetSymbol, targetChildren)) := by
                simpa [hkind] using hsourceNode
              refine ⟨targetSymbol,
                targetChildren.map context.closeUnaryReference, ?_⟩
              have hclose : context.closeUnaryReference sourceChild =
                  sourceChild := by
                simp [closeUnaryReference, hsourceApplication]
              rw [hclose, unaryLimit_nodeAt?, hsourceApplication]
              rfl

/-- A nontrivial well-formed unary context becomes a ground regular graph when
its variable edges are tied to the root.  Retained variable nodes outside the
root support are harmless. -/
public theorem unaryLimit_ground
    {ranks : List ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    (hnontrivial : context.nontrivialUnaryCode = true) :
    context.unaryLimit.Ground ranks := by
  apply ground_of_closed_applications
  · exact unaryLimit_shapeWellFormed
      (shapeWellFormed_of_wellFormed hcontext)
      (referenceClosed_of_wellFormed hcontext)
  · obtain ⟨X, children, hroot⟩ :=
      root_application_of_nontrivial_unary hcontext hnontrivial
    refine ⟨X, children.map context.closeUnaryReference, ?_⟩
    simp [unaryLimit_nodeAt?, hroot, closeUnaryNode]
  · intro i X children hnode child hchild
    exact unaryLimit_application_child_is_application hcontext hnontrivial
      hnode child hchild

private theorem rank_arity_of_shapeWellFormed
    {ranks : List ℕ} {term : RegularTerm}
    (hshape : term.ShapeWellFormed ranks)
    {i X : ℕ} {children : List ℕ}
    (hnode : term.nodeAt? i = some (.inr (X, children))) :
    ∃ rank, ranks[X]? = some rank ∧ children.length = rank := by
  unfold ShapeWellFormed shapeWellFormedCode at hshape
  rw [Bool.and_eq_true] at hshape
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have happ := (List.all_eq_true.mp hshape.2) _ hmem
  unfold nodeShapeWellFormedCode at happ
  cases hrank : ranks[X]? with
  | none => simp [hrank] at happ
  | some rank =>
      simp only [hrank] at happ
      rw [Bool.and_eq_true] at happ
      exact ⟨rank, rfl, of_decide_eq_true happ.1⟩

private theorem shapeWellFormed_of_referenceClosed_and_rankArity
    {ranks : List ℕ} {term : RegularTerm}
    (hclosed : term.ReferenceClosed)
    (hrankArity : ∀ i X children,
      term.nodeAt? i = some (.inr (X, children)) →
      ∃ rank, ranks[X]? = some rank ∧ children.length = rank) :
    term.ShapeWellFormed ranks := by
  unfold ShapeWellFormed shapeWellFormedCode
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true hclosed.1, ?_⟩
  apply List.all_eq_true.mpr
  intro node hmem
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hnode : term.nodeAt? i = some node := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hi, hget⟩
  cases node with
  | inl x => rfl
  | inr app =>
      rcases app with ⟨X, children⟩
      obtain ⟨rank, hrank, harity⟩ :=
        hrankArity i X children hnode
      unfold nodeShapeWellFormedCode
      simp only [hrank, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨harity, ?_⟩
      apply List.all_eq_true.mpr
      intro child hchild
      exact decide_eq_true (hclosed.2 i X children hnode child hchild)

private theorem instantiate_singleton_rankArity
    {ranks : List ℕ} {context argument : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    (hargument : argument.ShapeWellFormed ranks)
    {i X : ℕ} {children : List ℕ}
    (hnode : (context.instantiate [argument]).nodeAt? i =
      some (.inr (X, children))) :
    ∃ rank, ranks[X]? = some rank ∧ children.length = rank := by
  have hi : i < (context.instantiate [argument]).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  by_cases hprefix : i < context.nodes.length
  · rw [instantiate_nodeAt?_rhs context [argument] hprefix] at hnode
    cases hsource : context.nodeAt? i with
    | none => simp [hsource] at hnode
    | some source =>
        rw [hsource] at hnode
        cases source with
        | inl x => simp [instantiateNode] at hnode
        | inr app =>
            rcases app with ⟨Y, sourceChildren⟩
            simp only [Option.map_some, instantiateNode, Option.some.injEq,
              Sum.inr.injEq, Prod.mk.injEq] at hnode
            rcases hnode with ⟨hYX, hchildren⟩
            subst Y
            subst children
            obtain ⟨rank, hrank, harity⟩ :=
              rank_arity_of_shapeWellFormed
                (shapeWellFormed_of_wellFormed hcontext) hsource
            exact ⟨rank, hrank, by simpa using harity⟩
  · rw [instantiate_singleton_nodes_length] at hi
    let argumentIndex := i - context.nodes.length
    have hargumentIndex : argumentIndex < argument.nodes.length := by
      dsimp [argumentIndex]
      omega
    have hiSplit : i = context.nodes.length + argumentIndex := by
      dsimp [argumentIndex]
      omega
    let sourceNode : RawNode := argument.nodes[argumentIndex]'hargumentIndex
    have hsource : argument.nodeAt? argumentIndex = some sourceNode := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hargumentIndex, rfl⟩
    have hcopied : (context.instantiate [argument]).nodeAt? i =
        some (shiftNode context.nodes.length sourceNode) := by
      rw [hiSplit]
      simpa using instantiate_nodeAt?_argument context [argument]
        (x := 0) (argument := argument) (i := argumentIndex)
        (node := sourceNode) (by simp) hsource
    rw [hcopied] at hnode
    cases hkind : sourceNode with
    | inl x => simp [hkind, shiftNode] at hnode
    | inr app =>
        rcases app with ⟨Y, sourceChildren⟩
        simp only [hkind, shiftNode, Option.some.injEq, Sum.inr.injEq,
          Prod.mk.injEq] at hnode
        rcases hnode with ⟨hYX, hchildren⟩
        subst Y
        subst children
        obtain ⟨rank, hrank, harity⟩ :=
          rank_arity_of_shapeWellFormed hargument (by
            simpa [hkind] using hsource)
        exact ⟨rank, hrank, by simpa using harity⟩

/-- Substituting a shape-correct closed graph in a well-formed unary context
preserves global rank/reference shape, including the unreachable context
variable nodes retained in the raw presentation. -/
public theorem instantiate_singleton_shapeWellFormed
    {ranks : List ℕ} {context argument : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    (hargument : argument.ShapeWellFormed ranks)
    (hargumentClosed : argument.ReferenceClosed) :
    (context.instantiate [argument]).ShapeWellFormed ranks := by
  apply shapeWellFormed_of_referenceClosed_and_rankArity
  · exact instantiate_singleton_referenceClosed
      (referenceClosed_of_wellFormed hcontext) hargumentClosed
  · intro i X children hnode
    exact instantiate_singleton_rankArity hcontext hargument hnode

/-- A support for unary substitution consists of every application node of the
context prefix and the shifted copy of one ground support of the argument. -/
private def singletonInstantiationSupport
    (context argument : RegularTerm) (argumentSupport : List ℕ) : List ℕ :=
  (List.range (context.instantiate [argument]).nodes.length).filter fun i =>
    if i < context.nodes.length then
      match (context.instantiate [argument]).nodeAt? i with
      | some (.inr _) => true
      | _ => false
    else
      decide (i - context.nodes.length ∈ argumentSupport)

private theorem singletonInstantiationSupport_sublist
    (context argument : RegularTerm) (argumentSupport : List ℕ) :
    List.Sublist (singletonInstantiationSupport context argument argumentSupport)
      (List.range (context.instantiate [argument]).nodes.length) :=
  List.filter_sublist

private theorem mem_singletonInstantiationSupport_of_prefix_application
    {context argument : RegularTerm} {argumentSupport : List ℕ}
    {i X : ℕ} {children : List ℕ}
    (hi : i < context.nodes.length)
    (hnode : (context.instantiate [argument]).nodeAt? i =
      some (.inr (X, children))) :
    i ∈ singletonInstantiationSupport context argument argumentSupport := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr
      (List.getElem?_eq_some_iff.mp hnode).1, ?_⟩
  simp [hi, hnode]

private theorem mem_singletonInstantiationSupport_of_shift
    {context argument : RegularTerm} {argumentSupport : List ℕ}
    (hsublist : List.Sublist argumentSupport
      (List.range argument.nodes.length))
    {i : ℕ} (hi : i ∈ argumentSupport) :
    context.nodes.length + i ∈
      singletonInstantiationSupport context argument argumentSupport := by
  have hiBound : i < argument.nodes.length :=
    List.mem_range.mp (hsublist.subset hi)
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_range.mpr
    rw [instantiate_singleton_nodes_length]
    omega
  · have hnotPrefix : ¬context.nodes.length + i <
        context.nodes.length := by omega
    simp [hnotPrefix, hi]

private theorem mem_singletonInstantiationSupport_cases
    {context argument : RegularTerm} {argumentSupport : List ℕ}
    {i : ℕ}
    (hi : i ∈ singletonInstantiationSupport context argument
      argumentSupport) :
    (∃ X children, i < context.nodes.length ∧
      (context.instantiate [argument]).nodeAt? i =
        some (.inr (X, children))) ∨
      (context.nodes.length ≤ i ∧
        i - context.nodes.length ∈ argumentSupport) := by
  obtain ⟨_, htest⟩ := List.mem_filter.mp hi
  by_cases hprefix : i < context.nodes.length
  · left
    simp only [hprefix, if_true] at htest
    cases hnode : (context.instantiate [argument]).nodeAt? i with
    | none => simp [hnode] at htest
    | some node =>
        cases node with
        | inl x => simp [hnode] at htest
        | inr app =>
            rcases app with ⟨X, children⟩
            exact ⟨X, children, hprefix, rfl⟩
  · right
    simp only [hprefix, if_false,
      decide_eq_true_eq] at htest
    exact ⟨Nat.le_of_not_gt hprefix, htest⟩

private theorem resolveRHSRef_mem_singletonInstantiationSupport
    {ranks : List ℕ} {context argument : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    {argumentSupport : List ℕ}
    (hsublist : List.Sublist argumentSupport
      (List.range argument.nodes.length))
    (hwitness : argument.GroundWitness argumentSupport)
    {i : ℕ} (hi : i < context.nodes.length) :
    context.resolveRHSRef [argument] i ∈
      singletonInstantiationSupport context argument argumentSupport := by
  let sourceNode : RawNode := context.nodes[i]'hi
  have hsource : context.nodeAt? i = some sourceNode := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hi, rfl⟩
  cases hkind : sourceNode with
  | inl x =>
      have hx : x < 1 := variable_lt_of_wellFormed hcontext (by
        simpa [hkind] using hsource)
      have hxzero : x = 0 := by omega
      subst x
      have hresolve : context.resolveRHSRef [argument] i =
          context.nodes.length + argument.root := by
        simp [resolveRHSRef, hsource, hkind, argumentRoot?]
      rw [hresolve]
      exact mem_singletonInstantiationSupport_of_shift hsublist hwitness.1
  | inr app =>
      rcases app with ⟨X, children⟩
      have hsourceApplication : context.nodeAt? i =
          some (.inr (X, children)) := by
        simpa [hkind] using hsource
      have hresolve : context.resolveRHSRef [argument] i = i := by
        simp [resolveRHSRef, hsourceApplication]
      rw [hresolve]
      apply mem_singletonInstantiationSupport_of_prefix_application
        (X := X)
        (children := children.map (context.resolveRHSRef [argument])) hi
      rw [instantiate_nodeAt?_rhs context [argument] hi]
      simp [hsourceApplication, instantiateNode]

/-- Instantiating a well-formed unary context by a ground graph yields a ground
graph.  In particular, the context's retained variable nodes do not make the
result spuriously nonground. -/
public theorem instantiate_singleton_ground
    {ranks : List ℕ} {context argument : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    (hargument : argument.Ground ranks) :
    (context.instantiate [argument]).Ground ranks := by
  obtain ⟨argumentSupport, hsupportEnumerated, hwitness⟩ := hargument.2
  have hsublist : List.Sublist argumentSupport
      (List.range argument.nodes.length) :=
    List.mem_sublists'.mp hsupportEnumerated
  have hcontextClosed := referenceClosed_of_wellFormed hcontext
  have hargumentClosed := referenceClosed_of_ground hargument
  refine ⟨instantiate_singleton_shapeWellFormed hcontext hargument.1
      hargumentClosed,
    singletonInstantiationSupport context argument argumentSupport,
    List.mem_sublists'.mpr
      (singletonInstantiationSupport_sublist context argument
        argumentSupport), ?_⟩
  constructor
  · change context.resolveRHSRef [argument] context.root ∈
      singletonInstantiationSupport context argument argumentSupport
    exact resolveRHSRef_mem_singletonInstantiationSupport hcontext hsublist
      hwitness hcontextClosed.1
  · intro i hi
    rcases mem_singletonInstantiationSupport_cases hi with
      hprefix | hsuffix
    · obtain ⟨X, children, hiPrefix, hnode⟩ := hprefix
      refine ⟨X, children, hnode, ?_⟩
      rw [instantiate_nodeAt?_rhs context [argument] hiPrefix] at hnode
      cases hsource : context.nodeAt? i with
      | none => simp [hsource] at hnode
      | some source =>
          rw [hsource] at hnode
          cases source with
          | inl x => simp [instantiateNode] at hnode
          | inr app =>
              rcases app with ⟨Y, sourceChildren⟩
              simp only [Option.map_some, instantiateNode,
                Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at hnode
              rcases hnode with ⟨hYX, hchildren⟩
              subst Y
              subst children
              intro child hchild
              obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
                List.mem_map.mp hchild
              apply resolveRHSRef_mem_singletonInstantiationSupport
                hcontext hsublist hwitness
              exact hcontextClosed.2 i X sourceChildren hsource sourceChild
                hsourceChild
    · obtain ⟨hiSuffix, hiArgumentSupport⟩ := hsuffix
      let argumentIndex := i - context.nodes.length
      have hiSplit : i = context.nodes.length + argumentIndex := by
        dsimp [argumentIndex]
        omega
      obtain ⟨X, children, hargumentNode, hargumentChildren⟩ :=
        hwitness.2 argumentIndex hiArgumentSupport
      refine ⟨X, children.map (context.nodes.length + ·), ?_, ?_⟩
      · rw [hiSplit]
        simpa [shiftNode] using
          instantiate_nodeAt?_argument context [argument]
            (x := 0) (argument := argument) (i := argumentIndex)
            (node := .inr (X, children)) (by simp) hargumentNode
      · intro child hchild
        obtain ⟨argumentChild, hargumentChild, rfl⟩ :=
          List.mem_map.mp hchild
        apply mem_singletonInstantiationSupport_of_shift hsublist
        exact hargumentChildren argumentChild hargumentChild

end RegularTerm

end DCFEquivalence
