module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisSemantics
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.IdentitySubstitution

@[expose]
public section

/-!
# Parametric regular-tree tying

The certificate calculus already contains the nullary regular solution of a
unary context.  Tail elimination needs the same graph operation while retaining
the context's other formal parameters.  `tieVariable context x` redirects every
application edge aimed at variable `x` back to the root of `context`; all
variable nodes, including the other positional parameters, are retained.

The operation does not reindex parameters.  Its fixed-point theorem therefore
uses the identity substitution with exactly slot `x` replaced by the tied
graph.  This same-arity presentation is convenient for padded schemas: every
parameter other than `x` remains at its original index.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Redirect a reference to the chosen variable back to the root. -/
@[expose] public def tieReference
    (context : RegularTerm) (x i : ℕ) : ℕ :=
  match context.nodeAt? i with
  | some (.inl y) => if y = x then context.root else i
  | _ => i

/-- Redirect application children while retaining the raw variable nodes. -/
@[expose] public def tieNode
    (context : RegularTerm) (x : ℕ) : RawNode → RawNode
  | .inl y => .inl y
  | .inr (X, children) =>
      .inr (X, children.map (context.tieReference x))

/-- Tie the chosen variable of a regular context back to its root. -/
@[expose] public def tieVariable
    (context : RegularTerm) (x : ℕ) : RegularTerm :=
  (context.nodes.map (context.tieNode x),
    context.tieReference x context.root)

@[simp] public theorem tieVariable_nodes
    (context : RegularTerm) (x : ℕ) :
    (context.tieVariable x).nodes =
      context.nodes.map (context.tieNode x) := rfl

@[simp] public theorem tieVariable_root
    (context : RegularTerm) (x : ℕ) :
    (context.tieVariable x).root =
      context.tieReference x context.root := rfl

public theorem tieVariable_nodeAt?
    (context : RegularTerm) (x i : ℕ) :
    (context.tieVariable x).nodeAt? i =
      (context.nodeAt? i).map (context.tieNode x) := by
  simp [tieVariable, nodeAt?, nodes, List.getElem?_map]

@[simp] public theorem tieReference_root
    (context : RegularTerm) (x : ℕ) :
    context.tieReference x context.root = context.root := by
  generalize hnode : context.nodeAt? context.root = node
  cases node with
  | none => simp [tieReference, hnode]
  | some node =>
      cases node with
      | inl y => simp [tieReference, hnode]
      | inr app => simp [tieReference, hnode]

private theorem tieReference_lt
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {x i : ℕ} (hi : i < context.nodes.length) :
    context.tieReference x i < context.nodes.length := by
  cases hnode : context.nodeAt? i with
  | none => simpa [tieReference, hnode] using hi
  | some node =>
      cases node with
      | inr app => simpa [tieReference, hnode] using hi
      | inl y =>
          by_cases hyx : y = x
          · simpa [tieReference, hnode, hyx] using hclosed.1
          · simpa [tieReference, hnode, hyx] using hi

/-- Tying a parameter preserves graph reference closure. -/
public theorem tieVariable_referenceClosed
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    (x : ℕ) :
    (context.tieVariable x).ReferenceClosed := by
  constructor
  · simpa using tieReference_lt hclosed (x := x) hclosed.1
  · intro i X children hnode child hchild
    rw [tieVariable_nodeAt?] at hnode
    cases hsource : context.nodeAt? i with
    | none => simp [hsource] at hnode
    | some source =>
        rw [hsource] at hnode
        cases source with
        | inl y => simp [tieNode] at hnode
        | inr app =>
            rcases app with ⟨Y, sourceChildren⟩
            simp only [Option.map_some, tieNode, Option.some.injEq,
              Sum.inr.injEq, Prod.mk.injEq] at hnode
            rcases hnode with ⟨hYX, hchildren⟩
            subst Y
            subst children
            obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
              List.mem_map.mp hchild
            rw [tieVariable_nodes, List.length_map]
            apply tieReference_lt hclosed
            exact hclosed.2 i X sourceChildren hsource
              sourceChild hsourceChild

/-- Tying changes only application references, so ranked well-formedness and
the ambient positional arity are preserved. -/
public theorem tieVariable_wellFormed
    {ranks : List ℕ} {arity : ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks arity)
    (x : ℕ) :
    (context.tieVariable x).WellFormed ranks arity := by
  have hclosed := referenceClosed_of_wellFormed hcontext
  unfold WellFormed wellFormedCode at hcontext ⊢
  rw [Bool.and_eq_true] at hcontext ⊢
  refine ⟨?_, ?_⟩
  · apply decide_eq_true
    rw [tieVariable_nodes, List.length_map]
    exact tieReference_lt hclosed
      (of_decide_eq_true hcontext.1)
  · apply List.all_eq_true.mpr
    intro node hnode
    rw [tieVariable_nodes] at hnode
    obtain ⟨source, hsourceMem, rfl⟩ := List.mem_map.mp hnode
    have hsourceWell :=
      (List.all_eq_true.mp hcontext.2) source hsourceMem
    cases source with
    | inl y =>
        simpa [tieNode] using hsourceWell
    | inr app =>
        rcases app with ⟨X, children⟩
        simp only [tieNode]
        unfold nodeWellFormedCode at hsourceWell ⊢
        cases hrank : ranks[X]? with
        | none => simp [hrank] at hsourceWell
        | some rank =>
            simp only [hrank] at hsourceWell ⊢
            rw [Bool.and_eq_true] at hsourceWell ⊢
            refine ⟨by simpa using hsourceWell.1, ?_⟩
            apply List.all_eq_true.mpr
            intro child hchild
            obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
              List.mem_map.mp hchild
            apply decide_eq_true
            rw [tieVariable_nodes, List.length_map]
            apply tieReference_lt hclosed
            exact of_decide_eq_true
              ((List.all_eq_true.mp hsourceWell.2)
                sourceChild hsourceChild)

/-- The positional substitution which leaves every parameter in place except
for `x`, where it inserts the tied graph itself. -/
@[expose] public def tieArguments
    (context : RegularTerm) (arity x : ℕ) : List RegularTerm :=
  (identityArguments arity).set x (context.tieVariable x)

@[simp] public theorem tieArguments_length
    (context : RegularTerm) (arity x : ℕ) :
    (context.tieArguments arity x).length = arity := by
  simp [tieArguments]

public theorem tieArguments_getElem?_eq
    {context : RegularTerm} {arity x : ℕ} (hx : x < arity) :
    (context.tieArguments arity x)[x]? =
      some (context.tieVariable x) := by
  simp [tieArguments, hx]

public theorem tieArguments_getElem?_ne
    {context : RegularTerm} {arity x y : ℕ}
    (hy : y < arity) (hxy : x ≠ y) :
    (context.tieArguments arity x)[y]? =
      some (variableTerm y) := by
  rw [tieArguments, List.getElem?_set_ne hxy]
  exact identityArguments_getElem? hy

/-- Every component of the fixed-point substitution is reference closed. -/
public theorem tieArguments_referenceClosed
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {arity x : ℕ} (hx : x < arity) :
    ∀ argument ∈ context.tieArguments arity x,
      argument.ReferenceClosed := by
  intro argument hargument
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hargument
  have hibound : i < arity := by
    have := (List.getElem?_eq_some_iff.mp hi).choose
    simpa using this
  by_cases hix : i = x
  · subst i
    rw [tieArguments_getElem?_eq hx] at hi
    cases Option.some.inj hi
    exact tieVariable_referenceClosed hclosed x
  · have hslot := tieArguments_getElem?_ne
        (context := context) hibound (fun hxi => hix hxi.symm)
    rw [hslot] at hi
    cases Option.some.inj hi
    apply identityArguments_referenceClosed arity
    exact List.mem_of_getElem?
      (identityArguments_getElem? hibound)

private theorem variable_lt_of_wellFormed
    {ranks : List ℕ} {arity : ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks arity)
    {i y : ℕ} (hnode : context.nodeAt? i = some (.inl y)) :
    y < arity := by
  unfold WellFormed wellFormedCode at hcontext
  rw [Bool.and_eq_true] at hcontext
  have hmem : (.inl y : RawNode) ∈ context.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hcontext.2) _ hmem
  simpa [nodeWellFormedCode] using of_decide_eq_true hwell

/-- The fixed-point bisimulation has one layer for references resolved in the
original context and one layer for the copied tied graph inserted at slot
`x`. -/
@[expose] public def TieVariableRelation
    (context : RegularTerm) (arity x : ℕ) (i j : ℕ) : Prop :=
  (∃ source, source < context.nodes.length ∧
      i = context.tieReference x source ∧
      j = context.resolveRHSRef (context.tieArguments arity x) source) ∨
  (i < context.nodes.length ∧
      j = argumentOffset context.nodes.length
        (context.tieArguments arity x) x + i)

private theorem forall₂_map_same_local
    {A B C : Type} {R : B → C → Prop}
    (left : A → B) (right : A → C) (values : List A)
    (h : ∀ value ∈ values, R (left value) (right value)) :
    List.Forall₂ R (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun tail htail => h tail (by simp [htail]))

private theorem tieVariableRelation_original_children
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {arity x i X : ℕ} {children : List ℕ}
    (hnode : context.nodeAt? i = some (.inr (X, children))) :
    List.Forall₂ (context.TieVariableRelation arity x)
      (children.map (context.tieReference x))
      (children.map
        (context.resolveRHSRef (context.tieArguments arity x))) := by
  apply forall₂_map_same_local
  intro child hchild
  left
  exact ⟨child, hclosed.2 i X children hnode child hchild, rfl, rfl⟩

private theorem tieVariableRelation_shifted_children
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {arity x : ℕ} {children : List ℕ}
    (hchildren : ∀ child ∈ children, child < context.nodes.length) :
    List.Forall₂ (context.TieVariableRelation arity x)
      (children.map (context.tieReference x))
      ((children.map (context.tieReference x)).map
        (argumentOffset context.nodes.length
          (context.tieArguments arity x) x + ·)) := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
      simp only [List.map_cons]
      apply List.Forall₂.cons
      · right
        exact ⟨tieReference_lt hclosed
            (hchildren child (by simp)),
          rfl⟩
      · exact ih fun tail htail => hchildren tail (by simp [htail])

private theorem tieVariableRelation_copy_compatible
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {arity x : ℕ} (hx : x < arity)
    {i : ℕ} (hi : i < context.nodes.length) :
    (context.tieVariable x).NodeCompatible
      (context.instantiate (context.tieArguments arity x))
      (context.TieVariableRelation arity x)
      i
      (argumentOffset context.nodes.length
        (context.tieArguments arity x) x + i) := by
  let source : RawNode := context.nodes[i]
  have hsource : context.nodeAt? i = some source := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hi, rfl⟩
  have htiedNode :
      (context.tieVariable x).nodeAt? i =
        some (context.tieNode x source) := by
    rw [tieVariable_nodeAt?, hsource]
    rfl
  have hargument :
      (context.tieArguments arity x)[x]? =
        some (context.tieVariable x) :=
    tieArguments_getElem?_eq hx
  have hcopied := instantiate_nodeAt?_argument
    context (context.tieArguments arity x)
    hargument htiedNode
  unfold NodeCompatible
  rw [htiedNode, hcopied]
  cases hkind : source with
  | inl y =>
      simp [tieNode, shiftNode, RawCompatible]
  | inr app =>
      rcases app with ⟨X, children⟩
      simp only [tieNode, shiftNode, RawCompatible]
      refine ⟨trivial, tieVariableRelation_shifted_children hclosed ?_⟩
      intro child hchild
      have happ : context.nodeAt? i =
          some (.inr (X, children)) := by
        simpa [hkind] using hsource
      exact hclosed.2 i X children happ child hchild

private theorem tieVariableRelation_isBisimulation
    {ranks : List ℕ} {arity x : ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks arity)
    (hx : x < arity) :
    (context.tieVariable x).IsBisimulation
      (context.instantiate (context.tieArguments arity x))
      (context.TieVariableRelation arity x) := by
  have hclosed := referenceClosed_of_wellFormed hcontext
  intro leftIndex rightIndex hrelation
  rcases hrelation with horiginal | hcopy
  · obtain ⟨i, hi, rfl, rfl⟩ := horiginal
    let source : RawNode := context.nodes[i]
    have hsource : context.nodeAt? i = some source := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hi, rfl⟩
    cases hkind : source with
    | inr app =>
        rcases app with ⟨X, children⟩
        have happ : context.nodeAt? i =
            some (.inr (X, children)) := by
          simpa [hkind] using hsource
        have htie :
            context.tieReference x i = i := by
          simp [tieReference, happ]
        have hresolve :
            context.resolveRHSRef
              (context.tieArguments arity x) i = i := by
          simp [resolveRHSRef, happ]
        unfold NodeCompatible
        rw [htie, hresolve, tieVariable_nodeAt?,
          instantiate_nodeAt?_rhs context
            (context.tieArguments arity x) hi,
          happ]
        simp only [Option.map_some, tieNode, instantiateNode,
          RawCompatible]
        exact ⟨trivial,
          tieVariableRelation_original_children hclosed happ⟩
    | inl y =>
        have hvariable : context.nodeAt? i =
            some (.inl y) := by
          simpa [hkind] using hsource
        have hy : y < arity :=
          variable_lt_of_wellFormed hcontext hvariable
        by_cases hyx : y = x
        · subst y
          have htie :
              context.tieReference x i = context.root := by
            simp [tieReference, hvariable]
          have hargument :
              (context.tieArguments arity x)[x]? =
                some (context.tieVariable x) :=
            tieArguments_getElem?_eq hx
          have hresolve :
              context.resolveRHSRef
                  (context.tieArguments arity x) i =
                argumentOffset context.nodes.length
                    (context.tieArguments arity x) x +
                  context.root := by
            simp [resolveRHSRef, hvariable, argumentRoot?,
              hargument]
          rw [htie, hresolve]
          exact tieVariableRelation_copy_compatible
            hclosed hx hclosed.1
        · have hargument :
              (context.tieArguments arity x)[y]? =
                some (variableTerm y) :=
            tieArguments_getElem?_ne hy (fun hxy => hyx hxy.symm)
          have htie :
              context.tieReference x i = i := by
            simp [tieReference, hvariable, hyx]
          have hresolve :
              context.resolveRHSRef
                  (context.tieArguments arity x) i =
                argumentOffset context.nodes.length
                  (context.tieArguments arity x) y := by
            simp [resolveRHSRef, hvariable, argumentRoot?,
              hargument]
          have hargumentNode :
              (variableTerm y).nodeAt? 0 = some (.inl y) := by
            simpa [rootNode?] using variableTerm_rootNode? y
          have hcopied := instantiate_nodeAt?_argument
            context (context.tieArguments arity x)
            hargument hargumentNode
          have hcopied' :
              (context.instantiate
                  (context.tieArguments arity x)).nodeAt?
                (argumentOffset context.nodes.length
                  (context.tieArguments arity x) y) =
                some (.inl y) := by
            simpa [shiftNode] using hcopied
          unfold NodeCompatible
          rw [htie, hresolve, tieVariable_nodeAt?, hvariable]
          rw [hcopied']
          simp [tieNode, RawCompatible]
  · obtain ⟨hi, rfl⟩ := hcopy
    exact tieVariableRelation_copy_compatible hclosed hx hi

/-- Tying one selected parameter gives a semantic fixed point while every
other parameter remains in its original positional slot. -/
public theorem tieVariable_unfoldingEquivalent_instantiate
    {ranks : List ℕ} {arity x : ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks arity)
    (hx : x < arity) :
    (context.tieVariable x).UnfoldingEquivalent
      (context.instantiate (context.tieArguments arity x)) := by
  refine ⟨context.TieVariableRelation arity x, ?_,
    tieVariableRelation_isBisimulation hcontext hx⟩
  change context.TieVariableRelation arity x
    (context.tieReference x context.root)
    (context.resolveRHSRef
      (context.tieArguments arity x) context.root)
  left
  exact ⟨context.root,
    (referenceClosed_of_wellFormed hcontext).1, rfl, rfl⟩

/-- Fixed-point law in the conventional `H[H^{lim x}/x] = H^{lim x}`
orientation. -/
public theorem instantiate_tieArguments_unfoldingEquivalent_tieVariable
    {ranks : List ℕ} {arity x : ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks arity)
    (hx : x < arity) :
    (context.instantiate
        (context.tieArguments arity x)).UnfoldingEquivalent
      (context.tieVariable x) :=
  (tieVariable_unfoldingEquivalent_instantiate hcontext hx).symm

end RegularTerm

end DCFEquivalence
