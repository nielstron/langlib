module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveParameterReindexing
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ParametricTying

@[expose]
public section

/-!
# Unary specialization of an arbitrary open schema

The limit rule consumes a genuinely unary context.  Ordinary graph
substitution is not enough to construct one: it retains every schema variable
and every variable node occurring as unreachable garbage inside ground
arguments.  This file specializes all fixed parameters and then sanitizes
every remaining raw variable label to `0`.

Semantic proofs use a finite support closed under application children on which
the only permitted variable is `0`.  Nodes outside that support are precisely
the presentation garbage ignored by unfolding equivalence.
-/

namespace DCFEquivalence

namespace RegularTerm

/-! ## Congruence of substitution in the open schema -/

@[expose] public def EquivalentSchemaInstantiationRelation
    (left right : RegularTerm) (arguments : List RegularTerm)
    (R : ℕ → ℕ → Prop) (i j : ℕ) : Prop :=
  (∃ leftSource rightSource,
      leftSource < left.nodes.length ∧
      rightSource < right.nodes.length ∧
      R leftSource rightSource ∧
      i = left.resolveRHSRef arguments leftSource ∧
      j = right.resolveRHSRef arguments rightSource) ∨
  (∃ x argument source,
      arguments[x]? = some argument ∧
      source < argument.nodes.length ∧
      i = argumentOffset left.nodes.length arguments x + source ∧
      j = argumentOffset right.nodes.length arguments x + source)

private theorem equivalentSchemaInstantiation_suffix_children
    {left right : RegularTerm} {arguments : List RegularTerm}
    {R : ℕ → ℕ → Prop} {x : ℕ}
    {argument : RegularTerm} {children : List ℕ}
    (hargument : arguments[x]? = some argument)
    (hchildren :
      ∀ child ∈ children, child < argument.nodes.length) :
    List.Forall₂
      (EquivalentSchemaInstantiationRelation
        left right arguments R)
      (children.map
        (argumentOffset left.nodes.length arguments x + ·))
      (children.map
        (argumentOffset right.nodes.length arguments x + ·)) := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
      exact .cons
        (Or.inr ⟨x, argument, child, hargument,
          hchildren child (by simp), rfl, rfl⟩)
        (ih fun tail htail =>
          hchildren tail (by simp [htail]))

private theorem equivalentSchemaInstantiation_suffix_compatible
    {left right : RegularTerm} {arguments : List RegularTerm}
    {R : ℕ → ℕ → Prop}
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed)
    {x : ℕ} {argument : RegularTerm}
    (hargument : arguments[x]? = some argument)
    {i : ℕ} (hi : i < argument.nodes.length) :
    (left.instantiate arguments).NodeCompatible
      (right.instantiate arguments)
      (EquivalentSchemaInstantiationRelation
        left right arguments R)
      (argumentOffset left.nodes.length arguments x + i)
      (argumentOffset right.nodes.length arguments x + i) := by
  let node : RawNode := argument.nodes[i]
  have hnode : argument.nodeAt? i = some node := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hi, rfl⟩
  have hleft := instantiate_nodeAt?_argument
    left arguments hargument hnode
  have hright := instantiate_nodeAt?_argument
    right arguments hargument hnode
  unfold NodeCompatible
  rw [hleft, hright]
  cases hkind : node with
  | inl y =>
      simp [shiftNode, RawCompatible]
  | inr app =>
      rcases app with ⟨X, children⟩
      simp only [shiftNode, RawCompatible]
      refine ⟨trivial,
        equivalentSchemaInstantiation_suffix_children
          hargument ?_⟩
      intro child hchild
      exact (hargumentsClosed argument
        (List.mem_of_getElem? hargument)).2
          i X children
          (by simpa [hkind] using hnode)
          child hchild

private theorem equivalentSchemaInstantiation_prefix_children
    {left right : RegularTerm} {arguments : List RegularTerm}
    {R : ℕ → ℕ → Prop}
    {leftChildren rightChildren : List ℕ}
    (hleftBounds :
      ∀ child ∈ leftChildren, child < left.nodes.length)
    (hrightBounds :
      ∀ child ∈ rightChildren, child < right.nodes.length)
    (hchildren : List.Forall₂ R leftChildren rightChildren) :
    List.Forall₂
      (EquivalentSchemaInstantiationRelation
        left right arguments R)
      (leftChildren.map (left.resolveRHSRef arguments))
      (rightChildren.map (right.resolveRHSRef arguments)) := by
  induction hchildren with
  | nil => exact .nil
  | @cons leftChild rightChild leftTail rightTail
      hchild htail ih =>
      apply List.Forall₂.cons
      · left
        exact ⟨leftChild, rightChild,
          hleftBounds leftChild (by simp),
          hrightBounds rightChild (by simp),
          hchild, rfl, rfl⟩
      · exact ih
          (fun child hmem =>
            hleftBounds child (by simp [hmem]))
          (fun child hmem =>
            hrightBounds child (by simp [hmem]))

private theorem equivalentSchemaInstantiationRelation_isBisimulation
    {ranks : List ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm} {R : ℕ → ℕ → Prop}
    (hleft : left.WellFormed ranks arguments.length)
    (hright : right.WellFormed ranks arguments.length)
    (hR : left.IsBisimulation right R)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    (left.instantiate arguments).IsBisimulation
      (right.instantiate arguments)
      (EquivalentSchemaInstantiationRelation
        left right arguments R) := by
  have hleftClosed := referenceClosed_of_wellFormed hleft
  have hrightClosed := referenceClosed_of_wellFormed hright
  intro leftIndex rightIndex hrelation
  rcases hrelation with hprefix | hsuffix
  · obtain ⟨i, j, hi, hj, hij, rfl, rfl⟩ := hprefix
    let leftNode : RawNode := left.nodes[i]
    let rightNode : RawNode := right.nodes[j]
    have hleftNode : left.nodeAt? i = some leftNode := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hi, rfl⟩
    have hrightNode : right.nodeAt? j = some rightNode := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hj, rfl⟩
    have hcompatible := hR i j hij
    unfold NodeCompatible at hcompatible
    rw [hleftNode, hrightNode] at hcompatible
    cases hleftKind : leftNode with
    | inl x =>
        cases hrightKind : rightNode with
        | inr app =>
            simp [hleftKind, hrightKind,
              RawCompatible] at hcompatible
        | inl y =>
            simp only [hleftKind, hrightKind,
              RawCompatible] at hcompatible
            subst y
            have hx : x < arguments.length := by
              unfold WellFormed wellFormedCode at hleft
              rw [Bool.and_eq_true] at hleft
              have hmem : (.inl x : RawNode) ∈ left.nodes :=
                List.mem_of_getElem? (by
                  simpa [hleftKind] using hleftNode)
              have hwell :=
                (List.all_eq_true.mp hleft.2) _ hmem
              simpa [nodeWellFormedCode] using
                of_decide_eq_true hwell
            let argument := arguments[x]
            have hargument : arguments[x]? = some argument :=
              List.getElem?_eq_getElem hx
            have hleftResolve :
                left.resolveRHSRef arguments i =
                  argumentOffset left.nodes.length arguments x +
                    argument.root := by
              simp [resolveRHSRef, hleftNode, hleftKind,
                argumentRoot?, hargument]
            have hrightResolve :
                right.resolveRHSRef arguments j =
                  argumentOffset right.nodes.length arguments x +
                    argument.root := by
              simp [resolveRHSRef, hrightNode, hrightKind,
                argumentRoot?, hargument]
            rw [hleftResolve, hrightResolve]
            exact equivalentSchemaInstantiation_suffix_compatible
              hargumentsClosed hargument
              (hargumentsClosed argument
                (List.mem_of_getElem? hargument)).1
    | inr leftApp =>
        rcases leftApp with ⟨X, leftChildren⟩
        cases hrightKind : rightNode with
        | inl y =>
            simp [hleftKind, hrightKind,
              RawCompatible] at hcompatible
        | inr rightApp =>
            rcases rightApp with ⟨Y, rightChildren⟩
            simp only [hleftKind, hrightKind,
              RawCompatible] at hcompatible
            rcases hcompatible with ⟨hXY, hchildren⟩
            subst Y
            have hleftApplication : left.nodeAt? i =
                some (.inr (X, leftChildren)) := by
              simpa [hleftKind] using hleftNode
            have hrightApplication : right.nodeAt? j =
                some (.inr (X, rightChildren)) := by
              simpa [hrightKind] using hrightNode
            have hleftResolve :
                left.resolveRHSRef arguments i = i := by
              simp [resolveRHSRef, hleftApplication]
            have hrightResolve :
                right.resolveRHSRef arguments j = j := by
              simp [resolveRHSRef, hrightApplication]
            rw [hleftResolve, hrightResolve]
            unfold NodeCompatible
            rw [instantiate_nodeAt?_rhs left arguments hi,
              instantiate_nodeAt?_rhs right arguments hj,
              hleftApplication, hrightApplication]
            simp only [Option.map_some, instantiateNode,
              RawCompatible]
            exact ⟨trivial,
              equivalentSchemaInstantiation_prefix_children
                (fun child hmem =>
                  hleftClosed.2 i X leftChildren
                    hleftApplication child hmem)
                (fun child hmem =>
                  hrightClosed.2 j X rightChildren
                    hrightApplication child hmem)
                hchildren⟩
  · obtain ⟨x, argument, i, hargument, hi,
        rfl, rfl⟩ := hsuffix
    exact equivalentSchemaInstantiation_suffix_compatible
      hargumentsClosed hargument hi

/-- Unfolding equivalence of well-formed open schemas is a congruence for one
common reference-closed substitution. -/
public theorem UnfoldingEquivalent.instantiate_sameArguments
    {ranks : List ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    (hleft : left.WellFormed ranks arguments.length)
    (hright : right.WellFormed ranks arguments.length)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    (left.instantiate arguments).UnfoldingEquivalent
      (right.instantiate arguments) := by
  obtain ⟨R, hroot, hR⟩ := hequivalent
  refine ⟨EquivalentSchemaInstantiationRelation
      left right arguments R, ?_,
    equivalentSchemaInstantiationRelation_isBisimulation
      hleft hright hR hargumentsClosed⟩
  left
  exact ⟨left.root, right.root,
    (referenceClosed_of_wellFormed hleft).1,
    (referenceClosed_of_wellFormed hright).1,
    hroot, rfl, rfl⟩

/-- Relabel raw variable garbage to the sole unary parameter. -/
@[expose] public def sanitizeUnaryNode : RawNode → RawNode
  | .inl _ => .inl 0
  | .inr app => .inr app

/-- Relabel every raw variable node to `0`, preserving graph layout and the
distinguished root. -/
@[expose] public def sanitizeUnary (term : RegularTerm) : RegularTerm :=
  (term.nodes.map sanitizeUnaryNode, term.root)

@[simp] public theorem sanitizeUnary_nodes (term : RegularTerm) :
    term.sanitizeUnary.nodes = term.nodes.map sanitizeUnaryNode := rfl

@[simp] public theorem sanitizeUnary_root (term : RegularTerm) :
    term.sanitizeUnary.root = term.root := rfl

public theorem sanitizeUnary_nodeAt?
    (term : RegularTerm) (i : ℕ) :
    term.sanitizeUnary.nodeAt? i =
      (term.nodeAt? i).map sanitizeUnaryNode := by
  simp [sanitizeUnary, nodeAt?, nodes, List.getElem?_map]

/-- A support for an open unary unfolding: every supported node is either the
sole parameter `0`, or an application all of whose children remain supported. -/
@[expose] public def UnaryWitness
    (term : RegularTerm) (support : List ℕ) : Prop :=
  term.root ∈ support ∧
    ∀ i ∈ support,
      term.nodeAt? i = some (.inl 0) ∨
      ∃ X children,
        term.nodeAt? i = some (.inr (X, children)) ∧
          ∀ child ∈ children, child ∈ support

/-- A regular graph denotes a term with at most the single open variable `0`
when it has a finite unary support. -/
@[expose] public def HasUnaryWitness (term : RegularTerm) : Prop :=
  ∃ support, term.UnaryWitness support

public theorem variableTerm_zero_hasUnaryWitness :
    (variableTerm 0).HasUnaryWitness := by
  refine ⟨[0], ?_⟩
  constructor
  · simp [variableTerm, root]
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    left
    simpa [rootNode?] using variableTerm_rootNode? 0

/-- A ground support is in particular a unary support with no variable case. -/
public theorem Ground.hasUnaryWitness
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) :
    term.HasUnaryWitness := by
  obtain ⟨support, _hsupport, hwitness⟩ := hground.2
  refine ⟨support, hwitness.1, ?_⟩
  intro i hi
  obtain ⟨X, children, hnode, hchildren⟩ :=
    hwitness.2 i hi
  exact Or.inr ⟨X, children, hnode, hchildren⟩

/-- Sanitizing a shape-correct graph produces a genuinely unary well-formed
raw graph. -/
public theorem sanitizeUnary_wellFormed_of_shape
    {ranks : List ℕ} {term : RegularTerm}
    (hshape : term.ShapeWellFormed ranks) :
    term.sanitizeUnary.WellFormed ranks 1 := by
  unfold ShapeWellFormed shapeWellFormedCode at hshape
  unfold WellFormed wellFormedCode
  rw [Bool.and_eq_true] at hshape ⊢
  refine ⟨?_, ?_⟩
  · apply decide_eq_true
    rw [sanitizeUnary_nodes, List.length_map]
    exact of_decide_eq_true hshape.1
  · apply List.all_eq_true.mpr
    intro node hnode
    rw [sanitizeUnary_nodes] at hnode
    obtain ⟨source, hsourceMem, rfl⟩ := List.mem_map.mp hnode
    have hsourceShape :=
      (List.all_eq_true.mp hshape.2) source hsourceMem
    cases source with
    | inl x =>
        simp [sanitizeUnaryNode, nodeWellFormedCode]
    | inr app =>
        rcases app with ⟨X, children⟩
        simp only [sanitizeUnaryNode]
        unfold nodeShapeWellFormedCode at hsourceShape
        unfold nodeWellFormedCode
        cases hrank : ranks[X]? with
        | none => simp [hrank] at hsourceShape
        | some rank =>
            simp only [hrank] at hsourceShape ⊢
            rw [Bool.and_eq_true] at hsourceShape ⊢
            refine ⟨hsourceShape.1, ?_⟩
            apply List.all_eq_true.mpr
            intro child hchild
            apply decide_eq_true
            rw [sanitizeUnary_nodes, List.length_map]
            exact of_decide_eq_true
              ((List.all_eq_true.mp hsourceShape.2) child hchild)

public theorem sanitizeUnary_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound) :
    term.sanitizeUnary.WellFormed ranks 1 :=
  sanitizeUnary_wellFormed_of_shape
    (shapeWellFormed_of_wellFormed hterm)

/-- Sanitization preserves the same unary support. -/
public theorem UnaryWitness.sanitizeUnary
    {term : RegularTerm} {support : List ℕ}
    (hwitness : term.UnaryWitness support) :
    term.sanitizeUnary.UnaryWitness support := by
  constructor
  · simpa using hwitness.1
  · intro i hi
    rcases hwitness.2 i hi with hvariable | happlication
    · left
      rw [sanitizeUnary_nodeAt?, hvariable]
      rfl
    · obtain ⟨X, children, hnode, hchildren⟩ := happlication
      right
      refine ⟨X, children, ?_, hchildren⟩
      rw [sanitizeUnary_nodeAt?, hnode]
      rfl

@[expose] public def SanitizeUnaryRelation
    (support : List ℕ) (i j : ℕ) : Prop :=
  i = j ∧ i ∈ support

private theorem forall₂_self_sanitizeRelation
    {support children : List ℕ}
    (hchildren : ∀ child ∈ children, child ∈ support) :
    List.Forall₂ (SanitizeUnaryRelation support)
      children children := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
      exact .cons
        ⟨rfl, hchildren child (by simp)⟩
        (ih fun tail htail =>
          hchildren tail (by simp [htail]))

private theorem sanitizeUnaryRelation_isBisimulation
    {term : RegularTerm} {support : List ℕ}
    (hwitness : term.UnaryWitness support) :
    term.sanitizeUnary.IsBisimulation term
      (SanitizeUnaryRelation support) := by
  intro i j hij
  rcases hij with ⟨rfl, hi⟩
  unfold NodeCompatible
  rw [sanitizeUnary_nodeAt?]
  rcases hwitness.2 i hi with hvariable | happlication
  · rw [hvariable]
    simp [sanitizeUnaryNode, RawCompatible]
  · obtain ⟨X, children, hnode, hchildren⟩ := happlication
    rw [hnode]
    simp only [Option.map_some, sanitizeUnaryNode, RawCompatible]
    exact ⟨trivial,
      forall₂_self_sanitizeRelation hchildren⟩

/-- Sanitizing unreachable variable garbage preserves the denoted unary
regular tree. -/
public theorem UnaryWitness.sanitizeUnary_unfoldingEquivalent
    {term : RegularTerm} {support : List ℕ}
    (hwitness : term.UnaryWitness support) :
    term.sanitizeUnary.UnfoldingEquivalent term := by
  refine ⟨SanitizeUnaryRelation support, ?_,
    sanitizeUnaryRelation_isBisimulation hwitness⟩
  exact ⟨rfl, hwitness.1⟩

public theorem HasUnaryWitness.sanitizeUnary_unfoldingEquivalent
    {term : RegularTerm} (hwitness : term.HasUnaryWitness) :
    term.sanitizeUnary.UnfoldingEquivalent term := by
  obtain ⟨support, hsupport⟩ := hwitness
  exact hsupport.sanitizeUnary_unfoldingEquivalent

/-- Sanitization preserves reachable groundness. -/
public theorem Ground.sanitizeUnary
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) :
    term.sanitizeUnary.Ground ranks := by
  obtain ⟨support, hsupportEnumerated, hwitness⟩ := hground.2
  refine ⟨shapeWellFormed_of_wellFormed
      (sanitizeUnary_wellFormed_of_shape hground.1),
    support, ?_, ?_⟩
  · simpa [sanitizeUnary_nodes] using hsupportEnumerated
  · constructor
    · simpa using hwitness.1
    · intro i hi
      obtain ⟨X, children, hnode, hchildren⟩ :=
        hwitness.2 i hi
      refine ⟨X, children, ?_, hchildren⟩
      rw [sanitizeUnary_nodeAt?, hnode]
      rfl

@[expose] public def GroundInstantiationRelation
    (support : List ℕ) (i j : ℕ) : Prop :=
  i = j ∧ i ∈ support

private theorem groundInstantiation_children
    {term : RegularTerm} {support : List ℕ}
    (hwitness : term.GroundWitness support)
    (arguments : List RegularTerm)
    {children : List ℕ}
    (hchildren : ∀ child ∈ children, child ∈ support) :
    List.Forall₂ (GroundInstantiationRelation support)
      (children.map (term.resolveRHSRef arguments)) children := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
      have hchildSupport : child ∈ support :=
        hchildren child (by simp)
      obtain ⟨X, grandchildren, hchildNode, _⟩ :=
        hwitness.2 child hchildSupport
      have hresolve :
          term.resolveRHSRef arguments child = child := by
        simp [resolveRHSRef, hchildNode]
      exact .cons
        ⟨hresolve, by simpa [hresolve] using hchildSupport⟩
        (ih fun tail htail =>
          hchildren tail (by simp [htail]))

private theorem groundInstantiationRelation_isBisimulation
    {term : RegularTerm} {support : List ℕ}
    (hwitness : term.GroundWitness support)
    (arguments : List RegularTerm) :
    (term.instantiate arguments).IsBisimulation term
      (GroundInstantiationRelation support) := by
  intro i j hij
  rcases hij with ⟨rfl, hi⟩
  obtain ⟨X, children, hnode, hchildren⟩ :=
    hwitness.2 i hi
  have hiBound : i < term.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  unfold NodeCompatible
  rw [instantiate_nodeAt?_rhs term arguments hiBound, hnode]
  simp only [Option.map_some, instantiateNode, RawCompatible]
  exact ⟨trivial,
    groundInstantiation_children hwitness arguments hchildren⟩

/-- Instantiating a reachable-ground graph cannot change its denoted tree,
because no variable node is reachable from its root. -/
public theorem Ground.instantiate_unfoldingEquivalent
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks)
    (arguments : List RegularTerm) :
    (term.instantiate arguments).UnfoldingEquivalent term := by
  obtain ⟨support, _hsupport, hwitness⟩ := hground.2
  refine ⟨GroundInstantiationRelation support, ?_,
    groundInstantiationRelation_isBisimulation hwitness arguments⟩
  have hrootNode := hwitness.2 term.root hwitness.1
  obtain ⟨X, children, hrootNode, _⟩ := hrootNode
  change GroundInstantiationRelation support
    (term.resolveRHSRef arguments term.root) term.root
  have hresolve :
      term.resolveRHSRef arguments term.root = term.root := by
    simp [resolveRHSRef, hrootNode]
  exact ⟨hresolve, by simpa [hresolve] using hwitness.1⟩

/-- Sanitize every fixed ground argument and replace slot `x` by the sole open
parameter. -/
@[expose] public def unarySpecializationArguments
    (arguments : List RegularTerm) (x : ℕ) : List RegularTerm :=
  (arguments.map sanitizeUnary).set x (variableTerm 0)

@[simp] public theorem unarySpecializationArguments_length
    (arguments : List RegularTerm) (x : ℕ) :
    (unarySpecializationArguments arguments x).length =
      arguments.length := by
  simp [unarySpecializationArguments]

public theorem unarySpecializationArguments_getElem?_eq
    {arguments : List RegularTerm} {x : ℕ}
    (hx : x < arguments.length) :
    (unarySpecializationArguments arguments x)[x]? =
      some (variableTerm 0) := by
  simp [unarySpecializationArguments, hx]

public theorem unarySpecializationArguments_getElem?_ne
    {arguments : List RegularTerm} {x i : ℕ}
    (hi : i < arguments.length) (hxi : x ≠ i) :
    (unarySpecializationArguments arguments x)[i]? =
      some arguments[i].sanitizeUnary := by
  rw [unarySpecializationArguments,
    List.getElem?_set_ne hxi]
  simp [hi]

private theorem unarySpecializationArguments_cases
    {arguments : List RegularTerm} {x : ℕ}
    {argument : RegularTerm}
    (hargument :
      argument ∈ unarySpecializationArguments arguments x) :
    argument = variableTerm 0 ∨
      ∃ i source, arguments[i]? = some source ∧ x ≠ i ∧
        argument = source.sanitizeUnary := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hargument
  have hiBound : i < arguments.length := by
    have := (List.getElem?_eq_some_iff.mp hi).choose
    simpa using this
  by_cases hix : i = x
  · subst i
    rw [unarySpecializationArguments_getElem?_eq hiBound] at hi
    left
    exact Option.some.inj hi |>.symm
  · right
    let source := arguments[i]
    have hsource : arguments[i]? = some source :=
      List.getElem?_eq_getElem hiBound
    refine ⟨i, source, hsource,
      fun hxi => hix hxi.symm, ?_⟩
    rw [unarySpecializationArguments_getElem?_ne hiBound
      (fun hxi => hix hxi.symm)] at hi
    simpa [source] using (Option.some.inj hi).symm

public theorem unarySpecializationArguments_referenceClosed
    {ranks : List ℕ} {arguments : List RegularTerm} {x : ℕ}
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    ∀ argument ∈ unarySpecializationArguments arguments x,
      argument.ReferenceClosed := by
  intro argument hargument
  rcases unarySpecializationArguments_cases hargument with
    rfl | ⟨i, source, hsource, _hxi, rfl⟩
  · exact variableTerm_referenceClosed 0
  · exact referenceClosed_of_wellFormed
      (sanitizeUnary_wellFormed_of_shape
        (harguments source
          (List.mem_of_getElem? hsource)).1)

public theorem unarySpecializationArguments_wellFormed
    {ranks : List ℕ} {arguments : List RegularTerm} {x : ℕ}
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    ∀ argument ∈ unarySpecializationArguments arguments x,
      argument.WellFormed ranks 1 := by
  intro argument hargument
  rcases unarySpecializationArguments_cases hargument with
    rfl | ⟨i, source, hsource, _hxi, rfl⟩
  · exact variableTerm_wellFormed (ranks := ranks) (by omega)
  · exact sanitizeUnary_wellFormed_of_shape
      (harguments source
        (List.mem_of_getElem? hsource)).1

public theorem unarySpecializationArguments_hasUnaryWitness
    {ranks : List ℕ} {arguments : List RegularTerm} {x : ℕ}
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    ∀ argument ∈ unarySpecializationArguments arguments x,
      argument.HasUnaryWitness := by
  intro argument hargument
  rcases unarySpecializationArguments_cases hargument with
    rfl | ⟨i, source, hsource, _hxi, rfl⟩
  · exact variableTerm_zero_hasUnaryWitness
  · obtain ⟨support, hwitness⟩ :=
      (harguments source
        (List.mem_of_getElem? hsource)).hasUnaryWitness
    exact ⟨support, hwitness.sanitizeUnary⟩

private theorem UnaryWitness.node_lt
    {term : RegularTerm} {support : List ℕ}
    (hwitness : term.UnaryWitness support)
    {i : ℕ} (hi : i ∈ support) :
    i < term.nodes.length := by
  rcases hwitness.2 i hi with hvariable | happlication
  · exact (List.getElem?_eq_some_iff.mp hvariable).1
  · obtain ⟨X, children, hnode, _⟩ := happlication
    exact (List.getElem?_eq_some_iff.mp hnode).1

/-- Simultaneous substitution preserves the existence of a unary support when
every supplied argument has one. -/
public theorem instantiate_hasUnaryWitness
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm}
    (hschema : schema.WellFormed ranks arguments.length)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed)
    (hargumentsUnary :
      ∀ argument ∈ arguments, argument.HasUnaryWitness) :
    (schema.instantiate arguments).HasUnaryWitness := by
  classical
  let supportFor : RegularTerm → List ℕ := fun argument =>
    if hmem : argument ∈ arguments then
      Classical.choose (hargumentsUnary argument hmem)
    else []
  have supportFor_spec (argument : RegularTerm)
      (hmem : argument ∈ arguments) :
      argument.UnaryWitness (supportFor argument) := by
    dsimp [supportFor]
    split
    · exact Classical.choose_spec (hargumentsUnary argument hmem)
    · contradiction
  let result := schema.instantiate arguments
  let Supported : ℕ → Prop := fun i =>
    (i < schema.nodes.length ∧
      ∃ X children,
        result.nodeAt? i = some (.inr (X, children))) ∨
    ∃ x argument j,
      arguments[x]? = some argument ∧
      j ∈ supportFor argument ∧
      i = argumentOffset schema.nodes.length arguments x + j
  let support :=
    (List.range result.nodes.length).filter Supported
  have hresultClosed : result.ReferenceClosed := by
    dsimp [result]
    exact instantiate_referenceClosed
      (referenceClosed_of_wellFormed hschema)
      hargumentsClosed
  have mem_support_of_supported {i : ℕ}
      (hi : i < result.nodes.length)
      (hsupported : Supported i) :
      i ∈ support := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr hi,
      decide_eq_true hsupported⟩
  have resolve_supported {i : ℕ}
      (hi : i < schema.nodes.length) :
      Supported (schema.resolveRHSRef arguments i) := by
    let source : RawNode := schema.nodes[i]
    have hsource : schema.nodeAt? i = some source := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hi, rfl⟩
    cases hkind : source with
    | inl x =>
        have hvariable : schema.nodeAt? i = some (.inl x) := by
          simpa [hkind] using hsource
        have hx : x < arguments.length := by
          unfold WellFormed wellFormedCode at hschema
          rw [Bool.and_eq_true] at hschema
          have hmem : (.inl x : RawNode) ∈ schema.nodes :=
            List.mem_of_getElem? hvariable
          have hwell :=
            (List.all_eq_true.mp hschema.2) _ hmem
          simpa [nodeWellFormedCode] using
            of_decide_eq_true hwell
        let argument := arguments[x]
        have hargument : arguments[x]? = some argument :=
          List.getElem?_eq_getElem hx
        have hargumentMem : argument ∈ arguments :=
          List.mem_of_getElem? hargument
        have hwitness := supportFor_spec argument hargumentMem
        right
        refine ⟨x, argument, argument.root,
          hargument, hwitness.1, ?_⟩
        simp [resolveRHSRef, hvariable, argumentRoot?, hargument]
    | inr app =>
        rcases app with ⟨X, children⟩
        have happlication : schema.nodeAt? i =
            some (.inr (X, children)) := by
          simpa [hkind] using hsource
        have hresolve :
            schema.resolveRHSRef arguments i = i := by
          simp [resolveRHSRef, happlication]
        rw [hresolve]
        left
        refine ⟨hi, X,
          children.map (schema.resolveRHSRef arguments), ?_⟩
        dsimp [result]
        rw [instantiate_nodeAt?_rhs schema arguments hi,
          happlication]
        rfl
  refine ⟨support, ?_⟩
  constructor
  · change schema.resolveRHSRef arguments schema.root ∈ support
    apply mem_support_of_supported hresultClosed.1
    exact resolve_supported
      (referenceClosed_of_wellFormed hschema).1
  · intro i hi
    have hiFilter : Supported i :=
      of_decide_eq_true (List.mem_filter.mp hi).2
    rcases hiFilter with hprefix | hsuffix
    · obtain ⟨hiSchema, X, children, hnode⟩ := hprefix
      right
      refine ⟨X, children, hnode, ?_⟩
      rw [show result = schema.instantiate arguments by rfl,
        instantiate_nodeAt?_rhs schema arguments hiSchema] at hnode
      cases hsource : schema.nodeAt? i with
      | none => simp [hsource] at hnode
      | some source =>
          rw [hsource] at hnode
          cases source with
          | inl z => simp [instantiateNode] at hnode
          | inr app =>
              rcases app with ⟨Y, sourceChildren⟩
              simp only [Option.map_some, instantiateNode,
                Option.some.injEq, Sum.inr.injEq,
                Prod.mk.injEq] at hnode
              rcases hnode with ⟨hYX, hchildren⟩
              subst Y
              subst children
              intro child hchild
              obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
                List.mem_map.mp hchild
              apply mem_support_of_supported
              · exact hresultClosed.2 i X
                  (sourceChildren.map
                    (schema.resolveRHSRef arguments))
                  (by
                    dsimp [result]
                    rw [instantiate_nodeAt?_rhs
                      schema arguments hiSchema, hsource]
                    rfl)
                  (schema.resolveRHSRef arguments sourceChild)
                  (List.mem_map.mpr
                    ⟨sourceChild, hsourceChild, rfl⟩)
              · exact resolve_supported
                  ((referenceClosed_of_wellFormed hschema).2
                    i X sourceChildren hsource
                    sourceChild hsourceChild)
    · obtain ⟨x, argument, j, hargument,
          hjSupport, rfl⟩ := hsuffix
      have hargumentMem : argument ∈ arguments :=
        List.mem_of_getElem? hargument
      have hwitness := supportFor_spec argument hargumentMem
      rcases hwitness.2 j hjSupport with
        hvariable | happlication
      · left
        simpa [result, shiftNode] using
          instantiate_nodeAt?_argument schema arguments
            hargument hvariable
      · obtain ⟨X, children, hargumentNode,
            hargumentChildren⟩ := happlication
        right
        refine ⟨X,
          children.map
            (argumentOffset schema.nodes.length arguments x + ·),
          ?_, ?_⟩
        · simpa [result, shiftNode] using
            instantiate_nodeAt?_argument schema arguments
              hargument hargumentNode
        · intro child hchild
          obtain ⟨argumentChild, hargumentChild, rfl⟩ :=
            List.mem_map.mp hchild
          apply mem_support_of_supported
          · apply hresultClosed.2
              (argumentOffset schema.nodes.length arguments x + j)
              X
              (children.map
                (argumentOffset schema.nodes.length arguments x + ·))
            · simpa [result, shiftNode] using
                instantiate_nodeAt?_argument schema arguments
                  hargument hargumentNode
            · exact List.mem_map.mpr
                ⟨argumentChild, hargumentChild, rfl⟩
          · right
            exact ⟨x, argument, argumentChild, hargument,
              hargumentChildren argumentChild hargumentChild, rfl⟩

@[expose] public def SanitizeInstantiationRelation
    (term argument : RegularTerm) (support : List ℕ)
    (i j : ℕ) : Prop :=
  (∃ source, source ∈ support ∧
      i = term.sanitizeUnary.resolveRHSRef [argument] source ∧
      j = term.resolveRHSRef [argument] source) ∨
  (∃ source, source < argument.nodes.length ∧
      i = term.nodes.length + source ∧
      j = term.nodes.length + source)

private theorem sanitizeInstantiation_shifted_children
    {term argument : RegularTerm} {support children : List ℕ}
    (hchildren :
      ∀ child ∈ children, child < argument.nodes.length) :
    List.Forall₂
      (SanitizeInstantiationRelation term argument support)
      (children.map (term.nodes.length + ·))
      (children.map (term.nodes.length + ·)) := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
      exact .cons
        (Or.inr ⟨child,
          hchildren child (by simp), rfl, rfl⟩)
        (ih fun tail htail =>
          hchildren tail (by simp [htail]))

private theorem sanitizeInstantiation_suffix_compatible
    {term argument : RegularTerm} {support : List ℕ}
    (hargumentClosed : argument.ReferenceClosed)
    {i : ℕ} (hi : i < argument.nodes.length) :
    (term.sanitizeUnary.instantiate [argument]).NodeCompatible
      (term.instantiate [argument])
      (SanitizeInstantiationRelation term argument support)
      (term.nodes.length + i) (term.nodes.length + i) := by
  let node : RawNode := argument.nodes[i]
  have hnode : argument.nodeAt? i = some node := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hi, rfl⟩
  have hleft := instantiate_nodeAt?_argument
    term.sanitizeUnary [argument]
    (x := 0) (argument := argument)
    (by simp) hnode
  have hright := instantiate_nodeAt?_argument
    term [argument]
    (x := 0) (argument := argument)
    (by simp) hnode
  have hleft' :
      (term.sanitizeUnary.instantiate [argument]).nodeAt?
          (term.nodes.length + i) =
        some (shiftNode term.nodes.length node) := by
    simpa using hleft
  have hright' :
      (term.instantiate [argument]).nodeAt?
          (term.nodes.length + i) =
        some (shiftNode term.nodes.length node) := by
    simpa using hright
  unfold NodeCompatible
  rw [hleft', hright']
  cases hkind : node with
  | inl y =>
      simp [shiftNode, RawCompatible]
  | inr app =>
      rcases app with ⟨X, children⟩
      simp only [shiftNode, RawCompatible]
      refine ⟨trivial,
        sanitizeInstantiation_shifted_children ?_⟩
      intro child hchild
      exact hargumentClosed.2 i X children
        (by simpa [hkind] using hnode)
        child hchild

private theorem sanitizeInstantiation_prefix_children
    {term argument : RegularTerm} {support : List ℕ}
    {children : List ℕ}
    (hchildren : ∀ child ∈ children, child ∈ support) :
    List.Forall₂
      (SanitizeInstantiationRelation term argument support)
      (children.map
        (term.sanitizeUnary.resolveRHSRef [argument]))
      (children.map (term.resolveRHSRef [argument])) := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
      exact .cons
        (Or.inl ⟨child, hchildren child (by simp), rfl, rfl⟩)
        (ih fun tail htail =>
          hchildren tail (by simp [htail]))

private theorem sanitizeInstantiationRelation_isBisimulation
    {term argument : RegularTerm} {support : List ℕ}
    (hwitness : term.UnaryWitness support)
    (hargumentClosed : argument.ReferenceClosed) :
    (term.sanitizeUnary.instantiate [argument]).IsBisimulation
      (term.instantiate [argument])
      (SanitizeInstantiationRelation term argument support) := by
  intro leftIndex rightIndex hrelation
  rcases hrelation with hprefix | hsuffix
  · obtain ⟨i, hiSupport, rfl, rfl⟩ := hprefix
    rcases hwitness.2 i hiSupport with
      hvariable | happlication
    · have hleftResolve :
          term.sanitizeUnary.resolveRHSRef [argument] i =
            term.nodes.length + argument.root := by
        have hsanitized :
            term.sanitizeUnary.nodeAt? i =
              some (.inl 0) := by
          rw [sanitizeUnary_nodeAt?, hvariable]
          rfl
        simp [resolveRHSRef, hsanitized, argumentRoot?]
      have hrightResolve :
          term.resolveRHSRef [argument] i =
            term.nodes.length + argument.root := by
        simp [resolveRHSRef, hvariable, argumentRoot?]
      rw [hleftResolve, hrightResolve]
      exact sanitizeInstantiation_suffix_compatible
        hargumentClosed hargumentClosed.1
    · obtain ⟨X, children, hnode, hchildren⟩ :=
        happlication
      have hi : i < term.nodes.length :=
        (List.getElem?_eq_some_iff.mp hnode).1
      have hleftNode :
          term.sanitizeUnary.nodeAt? i =
            some (.inr (X, children)) := by
        rw [sanitizeUnary_nodeAt?, hnode]
        rfl
      have hleftResolve :
          term.sanitizeUnary.resolveRHSRef [argument] i = i := by
        simp [resolveRHSRef, hleftNode]
      have hrightResolve :
          term.resolveRHSRef [argument] i = i := by
        simp [resolveRHSRef, hnode]
      rw [hleftResolve, hrightResolve]
      unfold NodeCompatible
      rw [instantiate_nodeAt?_rhs
          term.sanitizeUnary [argument] (by simpa using hi),
        instantiate_nodeAt?_rhs term [argument] hi,
        hleftNode, hnode]
      simp only [Option.map_some, instantiateNode,
        RawCompatible]
      exact ⟨trivial,
        sanitizeInstantiation_prefix_children
          hchildren⟩
  · obtain ⟨i, hi, rfl, rfl⟩ := hsuffix
    exact sanitizeInstantiation_suffix_compatible
      hargumentClosed hi

/-- Sanitization remains semantically invisible after the sole unary
parameter is instantiated. -/
public theorem UnaryWitness.sanitizeUnary_instantiate_unfoldingEquivalent
    {term argument : RegularTerm} {support : List ℕ}
    (hwitness : term.UnaryWitness support)
    (hargumentClosed : argument.ReferenceClosed) :
    (term.sanitizeUnary.instantiate [argument]).UnfoldingEquivalent
      (term.instantiate [argument]) := by
  refine ⟨SanitizeInstantiationRelation term argument support, ?_,
    sanitizeInstantiationRelation_isBisimulation
      hwitness hargumentClosed⟩
  left
  exact ⟨term.root, hwitness.1, rfl, rfl⟩

public theorem HasUnaryWitness.sanitizeUnary_instantiate_unfoldingEquivalent
    {term argument : RegularTerm}
    (hwitness : term.HasUnaryWitness)
    (hargumentClosed : argument.ReferenceClosed) :
    (term.sanitizeUnary.instantiate [argument]).UnfoldingEquivalent
      (term.instantiate [argument]) := by
  obtain ⟨support, hsupport⟩ := hwitness
  exact hsupport.sanitizeUnary_instantiate_unfoldingEquivalent
    hargumentClosed

/-- The raw partially instantiated schema before garbage relabeling. -/
@[expose] public def unarySpecializationRaw
    (schema : RegularTerm) (arguments : List RegularTerm)
    (x : ℕ) : RegularTerm :=
  schema.instantiate (unarySpecializationArguments arguments x)

/-- A genuinely unary context obtained by fixing every parameter except `x`. -/
@[expose] public def unarySpecialization
    (schema : RegularTerm) (arguments : List RegularTerm)
    (x : ℕ) : RegularTerm :=
  (unarySpecializationRaw schema arguments x).sanitizeUnary

public theorem unarySpecializationRaw_wellFormed
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    (unarySpecializationRaw schema arguments x).WellFormed
      ranks (max arguments.length 1) := by
  unfold unarySpecializationRaw
  have hresult := instantiate_wellFormed_max
    (arguments := unarySpecializationArguments arguments x)
    (variableBound := 1)
    (by simpa using hschema)
    (unarySpecializationArguments_wellFormed
      harguments)
  simpa using hresult

/-- Unary specialization is structurally valid at variable bound exactly one,
including all unreachable graph nodes. -/
public theorem unarySpecialization_wellFormed
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    (unarySpecialization schema arguments x).WellFormed ranks 1 := by
  unfold unarySpecialization
  exact sanitizeUnary_wellFormed
    (unarySpecializationRaw_wellFormed hschema harguments)

public theorem unarySpecializationRaw_hasUnaryWitness
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    (unarySpecializationRaw schema arguments x).HasUnaryWitness := by
  unfold unarySpecializationRaw
  apply instantiate_hasUnaryWitness
  · simpa using hschema
  · exact unarySpecializationArguments_referenceClosed
      harguments
  · exact unarySpecializationArguments_hasUnaryWitness
      harguments

public theorem unarySpecialization_unfoldingEquivalent_raw
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    (unarySpecialization schema arguments x).UnfoldingEquivalent
      (unarySpecializationRaw schema arguments x) := by
  exact (unarySpecializationRaw_hasUnaryWitness
    hschema harguments).sanitizeUnary_unfoldingEquivalent

private theorem unarySpecialization_composed_forall₂
    {ranks : List ℕ} {arguments : List RegularTerm} {x : ℕ}
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    List.Forall₂ UnfoldingEquivalent
      (composedContexts
        (unarySpecializationArguments arguments x)
        [arguments[x]])
      arguments := by
  apply (List.forall₂_iff_get).2
  constructor
  · simp [composedContexts]
  · intro i hleft hright
    have hi : i < arguments.length := hright
    let source := arguments[i]
    have hsource : arguments[i]? = some source :=
      List.getElem?_eq_getElem hi
    have hrightGet :
        arguments.get ⟨i, hright⟩ = source := by
      exact Option.some.inj
        ((List.getElem?_eq_getElem hright).symm.trans
          hsource)
    by_cases hix : i = x
    · subst i
      have hpartial :=
        unarySpecializationArguments_getElem?_eq hx
      have hcomposed :
          (composedContexts
            (unarySpecializationArguments arguments x)
            [arguments[x]])[x]? =
            some ((variableTerm 0).instantiate
              [arguments[x]]) := by
        simp [composedContexts, hpartial]
      have hleftGet :
          (composedContexts
            (unarySpecializationArguments arguments x)
            [arguments[x]]).get ⟨x, hleft⟩ =
              (variableTerm 0).instantiate [arguments[x]] :=
        Option.some.inj
          ((List.getElem?_eq_getElem hleft).symm.trans
            hcomposed)
      rw [hleftGet, hrightGet]
      apply instantiate_unfoldingEquivalent_argument
      · simpa [rootNode?] using variableTerm_rootNode? 0
      · simpa [source]
      · exact referenceClosed_of_ground
          (harguments arguments[x]
            (List.getElem_mem hx))
    · have hpartial :=
        unarySpecializationArguments_getElem?_ne hi
          (fun hxi => hix hxi.symm)
      have hcomposed :
          (composedContexts
            (unarySpecializationArguments arguments x)
            [arguments[x]])[i]? =
            some (source.sanitizeUnary.instantiate
              [arguments[x]]) := by
        simp [composedContexts, hpartial, source]
      have hleftGet :
          (composedContexts
            (unarySpecializationArguments arguments x)
            [arguments[x]]).get ⟨i, hleft⟩ =
              source.sanitizeUnary.instantiate
                [arguments[x]] :=
        Option.some.inj
          ((List.getElem?_eq_getElem hleft).symm.trans
            hcomposed)
      rw [hleftGet, hrightGet]
      have hsourceGround :=
        harguments source
          (List.mem_of_getElem? hsource)
      exact
        (hsourceGround.sanitizeUnary
          |>.instantiate_unfoldingEquivalent
            [arguments[x]]).trans
          (hsourceGround.hasUnaryWitness
            |>.sanitizeUnary_unfoldingEquivalent)

private theorem unarySpecialization_composed_referenceClosed
    {ranks : List ℕ} {arguments : List RegularTerm} {x : ℕ}
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    ∀ context ∈
        composedContexts
          (unarySpecializationArguments arguments x)
          [arguments[x]],
      context.ReferenceClosed := by
  intro context hcontext
  obtain ⟨source, hsource, rfl⟩ :=
    List.mem_map.mp hcontext
  apply instantiate_referenceClosed
  · exact unarySpecializationArguments_referenceClosed
      harguments source hsource
  · intro argument hargument
    simp only [List.mem_singleton] at hargument
    subst argument
    exact referenceClosed_of_ground
      (harguments arguments[x]
        (List.getElem_mem hx))

/-- Filling the sole open slot of the raw specialization reconstructs the
original fully instantiated schema semantically. -/
public theorem unarySpecializationRaw_instantiate_unfoldingEquivalent
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    (unarySpecializationRaw schema arguments x
        |>.instantiate [arguments[x]]).UnfoldingEquivalent
      (schema.instantiate arguments) := by
  have hpartialClosed :
      ∀ argument ∈ unarySpecializationArguments arguments x,
        argument.ReferenceClosed :=
    unarySpecializationArguments_referenceClosed
      (x := x) harguments
  have hactualClosed := referenceClosed_of_ground
    (harguments arguments[x] (List.getElem_mem hx))
  have hcomposition := instantiate_comp_unfoldingEquivalent
    (outer := schema)
    (contexts := unarySpecializationArguments arguments x)
    (arguments := [arguments[x]])
    (by simpa using hschema)
    hpartialClosed
    (by simpa)
  have hcongruence := instantiate_unfoldingEquivalent
    (referenceClosed_of_wellFormed hschema)
    (unarySpecialization_composed_forall₂
      hx harguments)
    (unarySpecialization_composed_referenceClosed
      hx harguments)
    (fun argument hargument =>
      referenceClosed_of_ground
        (harguments argument hargument))
  exact hcomposition.trans hcongruence

/-- Main specialization law: filling the constructed unary context at its
selected ground argument recovers the original instance. -/
public theorem unarySpecialization_instantiate_unfoldingEquivalent
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks) :
    (unarySpecialization schema arguments x
        |>.instantiate [arguments[x]]).UnfoldingEquivalent
      (schema.instantiate arguments) := by
  have hsanitize :=
    (unarySpecializationRaw_hasUnaryWitness
      (x := x) hschema harguments)
      |>.sanitizeUnary_instantiate_unfoldingEquivalent
        (referenceClosed_of_ground
          (harguments arguments[x]
            (List.getElem_mem hx)))
  exact hsanitize.trans
    (unarySpecializationRaw_instantiate_unfoldingEquivalent
      hschema hx harguments)

/-- Replace one positional argument while retaining tuple length. -/
@[expose] public def replaceArgument
    (arguments : List RegularTerm) (x : ℕ)
    (replacement : RegularTerm) : List RegularTerm :=
  arguments.set x replacement

@[simp] public theorem replaceArgument_length
    (arguments : List RegularTerm) (x : ℕ)
    (replacement : RegularTerm) :
    (replaceArgument arguments x replacement).length =
      arguments.length := by
  simp [replaceArgument]

public theorem replaceArgument_getElem?_eq
    {arguments : List RegularTerm} {x : ℕ}
    {replacement : RegularTerm}
    (hx : x < arguments.length) :
    (replaceArgument arguments x replacement)[x]? =
      some replacement := by
  simp [replaceArgument, hx]

public theorem replaceArgument_getElem?_ne
    {arguments : List RegularTerm} {x i : ℕ}
    {replacement : RegularTerm} (hxi : x ≠ i) :
    (replaceArgument arguments x replacement)[i]? =
      arguments[i]? := by
  exact List.getElem?_set_ne hxi

public theorem replaceArgument_referenceClosed
    {arguments : List RegularTerm} {x : ℕ}
    {replacement : RegularTerm}
    (hx : x < arguments.length)
    (harguments :
      ∀ argument ∈ arguments, argument.ReferenceClosed)
    (hreplacement : replacement.ReferenceClosed) :
    ∀ argument ∈ replaceArgument arguments x replacement,
      argument.ReferenceClosed := by
  intro argument hargument
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hargument
  have hiBound : i < arguments.length := by
    have := (List.getElem?_eq_some_iff.mp hi).choose
    simpa using this
  by_cases hix : i = x
  · subst i
    rw [replaceArgument_getElem?_eq hx] at hi
    cases Option.some.inj hi
    exact hreplacement
  · rw [replaceArgument_getElem?_ne
      (fun hxi => hix hxi.symm)] at hi
    exact harguments argument (List.mem_of_getElem? hi)

/-- Pointwise equivalence of two replacements lifts to the corresponding
same-length argument tuples. -/
public theorem replaceArgument_forall₂
    {arguments : List RegularTerm} {x : ℕ}
    {leftReplacement rightReplacement : RegularTerm}
    (hx : x < arguments.length)
    (hreplacement : leftReplacement.UnfoldingEquivalent rightReplacement) :
    List.Forall₂ UnfoldingEquivalent
      (replaceArgument arguments x leftReplacement)
      (replaceArgument arguments x rightReplacement) := by
  apply (List.forall₂_iff_get).2
  constructor
  · simp
  · intro i hleft hright
    have hi : i < arguments.length := by
      simpa using hleft
    by_cases hix : i = x
    · subst i
      have hleftSlot := replaceArgument_getElem?_eq
        (arguments := arguments) (replacement := leftReplacement) hx
      have hrightSlot := replaceArgument_getElem?_eq
        (arguments := arguments) (replacement := rightReplacement) hx
      have hleftGet :
          (replaceArgument arguments x leftReplacement).get
              ⟨x, hleft⟩ = leftReplacement :=
        Option.some.inj
          ((List.getElem?_eq_getElem hleft).symm.trans hleftSlot)
      have hrightGet :
          (replaceArgument arguments x rightReplacement).get
              ⟨x, hright⟩ = rightReplacement :=
        Option.some.inj
          ((List.getElem?_eq_getElem hright).symm.trans hrightSlot)
      rw [hleftGet, hrightGet]
      exact hreplacement
    · let argument := arguments[i]
      have hsource : arguments[i]? = some argument :=
        List.getElem?_eq_getElem hi
      have hleftSlot :
          (replaceArgument arguments x leftReplacement)[i]? =
            some argument := by
        rw [replaceArgument_getElem?_ne
          (fun hxi => hix hxi.symm)]
        exact hsource
      have hrightSlot :
          (replaceArgument arguments x rightReplacement)[i]? =
            some argument := by
        rw [replaceArgument_getElem?_ne
          (fun hxi => hix hxi.symm)]
        exact hsource
      have hleftGet :
          (replaceArgument arguments x leftReplacement).get
              ⟨i, hleft⟩ = argument :=
        Option.some.inj
          ((List.getElem?_eq_getElem hleft).symm.trans hleftSlot)
      have hrightGet :
          (replaceArgument arguments x rightReplacement).get
              ⟨i, hright⟩ = argument :=
        Option.some.inj
          ((List.getElem?_eq_getElem hright).symm.trans hrightSlot)
      rw [hleftGet, hrightGet]

private theorem unarySpecialization_composed_focus_forall₂
    {ranks : List ℕ} {arguments : List RegularTerm} {x : ℕ}
    {focus : RegularTerm}
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks)
    (hfocus : focus.ReferenceClosed) :
    List.Forall₂ UnfoldingEquivalent
      (composedContexts
        (unarySpecializationArguments arguments x)
        [focus])
      (replaceArgument arguments x focus) := by
  apply (List.forall₂_iff_get).2
  constructor
  · simp [composedContexts]
  · intro i hleft hright
    have hi : i < arguments.length := by
      simpa using hright
    by_cases hix : i = x
    · subst i
      have hpartial :=
        unarySpecializationArguments_getElem?_eq hx
      have hcomposed :
          (composedContexts
            (unarySpecializationArguments arguments x)
            [focus])[x]? =
            some ((variableTerm 0).instantiate [focus]) := by
        simp [composedContexts, hpartial]
      have htarget :=
        replaceArgument_getElem?_eq
          (replacement := focus) hx
      have hleftGet :
          (composedContexts
            (unarySpecializationArguments arguments x)
            [focus]).get ⟨x, hleft⟩ =
              (variableTerm 0).instantiate [focus] :=
        Option.some.inj
          ((List.getElem?_eq_getElem hleft).symm.trans
            hcomposed)
      have hrightGet :
          (replaceArgument arguments x focus).get
              ⟨x, hright⟩ = focus :=
        Option.some.inj
          ((List.getElem?_eq_getElem hright).symm.trans
            htarget)
      rw [hleftGet, hrightGet]
      exact instantiate_unfoldingEquivalent_argument
        (by simpa [rootNode?] using variableTerm_rootNode? 0)
        (by simp) hfocus
    · let source := arguments[i]
      have hsource : arguments[i]? = some source :=
        List.getElem?_eq_getElem hi
      have hpartial :=
        unarySpecializationArguments_getElem?_ne hi
          (fun hxi => hix hxi.symm)
      have hcomposed :
          (composedContexts
            (unarySpecializationArguments arguments x)
            [focus])[i]? =
            some (source.sanitizeUnary.instantiate [focus]) := by
        simp [composedContexts, hpartial, source]
      have htarget :
          (replaceArgument arguments x focus)[i]? =
            some source := by
        rw [replaceArgument_getElem?_ne
          (fun hxi => hix hxi.symm)]
        exact hsource
      have hleftGet :
          (composedContexts
            (unarySpecializationArguments arguments x)
            [focus]).get ⟨i, hleft⟩ =
              source.sanitizeUnary.instantiate [focus] :=
        Option.some.inj
          ((List.getElem?_eq_getElem hleft).symm.trans
            hcomposed)
      have hrightGet :
          (replaceArgument arguments x focus).get
              ⟨i, hright⟩ = source :=
        Option.some.inj
          ((List.getElem?_eq_getElem hright).symm.trans
            htarget)
      rw [hleftGet, hrightGet]
      have hsourceGround :=
        harguments source (List.mem_of_getElem? hsource)
      exact
        (hsourceGround.sanitizeUnary
          |>.instantiate_unfoldingEquivalent [focus]).trans
        (hsourceGround.hasUnaryWitness
          |>.sanitizeUnary_unfoldingEquivalent)

/-- General filling law with an arbitrary reference-closed focus in the open
slot. -/
public theorem unarySpecialization_instantiate_focus
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    {focus : RegularTerm}
    (hschema : schema.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks)
    (hfocus : focus.ReferenceClosed) :
    (unarySpecialization schema arguments x
        |>.instantiate [focus]).UnfoldingEquivalent
      (schema.instantiate
        (replaceArgument arguments x focus)) := by
  have hpartialClosed :=
    unarySpecializationArguments_referenceClosed
      (x := x) harguments
  have hrawWitness :=
    unarySpecializationRaw_hasUnaryWitness
      (x := x) hschema harguments
  have hsanitize :=
    hrawWitness.sanitizeUnary_instantiate_unfoldingEquivalent
      hfocus
  have hcomposition := instantiate_comp_unfoldingEquivalent
    (outer := schema)
    (contexts := unarySpecializationArguments arguments x)
    (arguments := [focus])
    (by simpa using hschema)
    hpartialClosed (by simpa)
  have hcomposedClosed :
      ∀ context ∈
          composedContexts
            (unarySpecializationArguments arguments x) [focus],
        context.ReferenceClosed := by
    intro context hcontext
    obtain ⟨source, hsource, rfl⟩ :=
      List.mem_map.mp hcontext
    exact instantiate_referenceClosed
      (hpartialClosed source hsource) (by simpa)
  have htargetClosed :=
    replaceArgument_referenceClosed hx
      (fun argument hargument =>
        referenceClosed_of_ground
          (harguments argument hargument))
      hfocus
  have hcongruence := instantiate_unfoldingEquivalent
    (referenceClosed_of_wellFormed hschema)
    (unarySpecialization_composed_focus_forall₂
      hx harguments hfocus)
    hcomposedClosed htargetClosed
  exact hsanitize.trans
    (hcomposition.trans hcongruence)

public theorem tieArguments_wellFormed
    {ranks : List ℕ} {context : RegularTerm}
    {arity x : ℕ}
    (hcontext : context.WellFormed ranks arity)
    (hx : x < arity) :
    ∀ argument ∈ context.tieArguments arity x,
      argument.WellFormed ranks arity := by
  intro argument hargument
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hargument
  have hiBound : i < arity := by
    have := (List.getElem?_eq_some_iff.mp hi).choose
    simpa using this
  by_cases hix : i = x
  · subst i
    rw [tieArguments_getElem?_eq hx] at hi
    cases Option.some.inj hi
    exact tieVariable_wellFormed hcontext x
  · have hslot := tieArguments_getElem?_ne
        (context := context) hiBound
        (fun hxi => hix hxi.symm)
    rw [hslot] at hi
    cases Option.some.inj hi
    exact variableTerm_wellFormed hiBound

private theorem tieComposed_forall₂_replace
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    List.Forall₂ UnfoldingEquivalent
      (composedContexts
        (schema.tieArguments arguments.length x) arguments)
      (replaceArgument arguments x
        ((schema.tieVariable x).instantiate arguments)) := by
  apply (List.forall₂_iff_get).2
  constructor
  · simp [composedContexts]
  · intro i hleft hright
    have hi : i < arguments.length := by
      simpa using hright
    by_cases hix : i = x
    · subst i
      have hslot := tieArguments_getElem?_eq
        (context := schema) hx
      have hcomposed :
          (composedContexts
            (schema.tieArguments arguments.length x)
            arguments)[x]? =
            some ((schema.tieVariable x).instantiate
              arguments) := by
        simp [composedContexts, hslot]
      have htarget := replaceArgument_getElem?_eq
        (arguments := arguments) (x := x)
        (replacement :=
          (schema.tieVariable x).instantiate arguments) hx
      have hleftGet :
          (composedContexts
            (schema.tieArguments arguments.length x)
            arguments).get ⟨x, hleft⟩ =
              (schema.tieVariable x).instantiate arguments :=
        Option.some.inj
          ((List.getElem?_eq_getElem hleft).symm.trans
            hcomposed)
      have hrightGet :
          (replaceArgument arguments x
            ((schema.tieVariable x).instantiate
              arguments)).get ⟨x, hright⟩ =
                (schema.tieVariable x).instantiate arguments :=
        Option.some.inj
          ((List.getElem?_eq_getElem hright).symm.trans
            htarget)
      rw [hleftGet, hrightGet]
    · let source := arguments[i]
      have hsource : arguments[i]? = some source :=
        List.getElem?_eq_getElem hi
      have hslot := tieArguments_getElem?_ne
        (context := schema) hi
        (fun hxi => hix hxi.symm)
      have hcomposed :
          (composedContexts
            (schema.tieArguments arguments.length x)
            arguments)[i]? =
            some ((variableTerm i).instantiate
              arguments) := by
        simp [composedContexts, hslot]
      have htarget :
          (replaceArgument arguments x
            ((schema.tieVariable x).instantiate
              arguments))[i]? = some source := by
        rw [replaceArgument_getElem?_ne
          (fun hxi => hix hxi.symm)]
        exact hsource
      have hleftGet :
          (composedContexts
            (schema.tieArguments arguments.length x)
            arguments).get ⟨i, hleft⟩ =
              (variableTerm i).instantiate arguments :=
        Option.some.inj
          ((List.getElem?_eq_getElem hleft).symm.trans
            hcomposed)
      have hrightGet :
          (replaceArgument arguments x
            ((schema.tieVariable x).instantiate
              arguments)).get ⟨i, hright⟩ = source :=
        Option.some.inj
          ((List.getElem?_eq_getElem hright).symm.trans
            htarget)
      rw [hleftGet, hrightGet]
      exact instantiate_unfoldingEquivalent_argument
        (by simpa [rootNode?] using variableTerm_rootNode? i)
        hsource
        (hargumentsClosed source
          (List.mem_of_getElem? hsource))

private theorem tieComposed_referenceClosed
    {context : RegularTerm} {arguments : List RegularTerm}
    {x : ℕ}
    (hcontextClosed : context.ReferenceClosed)
    (hx : x < arguments.length)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    ∀ term ∈
        composedContexts
          (context.tieArguments arguments.length x) arguments,
      term.ReferenceClosed := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ :=
    List.mem_map.mp hterm
  exact instantiate_referenceClosed
    (tieArguments_referenceClosed hcontextClosed hx
      source hsource)
    hargumentsClosed

/-- Instantiating an outer schema after parametrically tying `context` is
equivalent to filling the selected slot by the concrete tied instance. -/
public theorem instantiate_tieArguments_fixedInstance
    {ranks : List ℕ} {outer context : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (houter : outer.WellFormed ranks arguments.length)
    (hcontext : context.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    ((outer.instantiate
        (context.tieArguments arguments.length x)).instantiate
          arguments).UnfoldingEquivalent
      (outer.instantiate
        (replaceArgument arguments x
          ((context.tieVariable x).instantiate arguments))) := by
  have hcomposition := instantiate_comp_unfoldingEquivalent
    (outer := outer)
    (contexts := context.tieArguments arguments.length x)
    (arguments := arguments)
    (by simpa using houter)
    (tieArguments_referenceClosed
      (referenceClosed_of_wellFormed hcontext) hx)
    hargumentsClosed
  have hreplacementClosed :=
    replaceArgument_referenceClosed hx hargumentsClosed
      (instantiate_referenceClosed
        (tieVariable_referenceClosed
          (referenceClosed_of_wellFormed hcontext) x)
        hargumentsClosed)
  have hcongruence := instantiate_unfoldingEquivalent
    (referenceClosed_of_wellFormed houter)
    (tieComposed_forall₂_replace
      hcontext hx hargumentsClosed)
    (tieComposed_referenceClosed
      (referenceClosed_of_wellFormed hcontext)
      hx hargumentsClosed)
    hreplacementClosed
  exact hcomposition.trans hcongruence

/-- A concrete instance of the bounded parametric tying is a semantic fixed
point of the original schema with only slot `x` replaced by that instance. -/
public theorem tieVariable_instance_fixedPoint
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    RegularTerm.UnfoldingEquivalent
      ((schema.tieVariable x).instantiate arguments)
      (schema.instantiate
        (replaceArgument arguments x
          ((schema.tieVariable x).instantiate arguments))) := by
  have htiedWellFormed :=
    tieVariable_wellFormed hschema x
  have htieArgumentsWellFormed :=
    tieArguments_wellFormed hschema hx
  have hfixedSchemaWellFormed :
      RegularTerm.WellFormed ranks arguments.length
        (schema.instantiate
          (schema.tieArguments arguments.length x)) := by
    have hresult := instantiate_wellFormed_max
      (arguments :=
        schema.tieArguments arguments.length x)
      (variableBound := arguments.length)
      (by simpa using hschema)
      htieArgumentsWellFormed
    simpa using hresult
  have hopen :=
    tieVariable_unfoldingEquivalent_instantiate
      hschema hx
  have hlifted := hopen.instantiate_sameArguments
    htiedWellFormed hfixedSchemaWellFormed
      hargumentsClosed
  have hcomposition := instantiate_comp_unfoldingEquivalent
    (outer := schema)
    (contexts :=
      schema.tieArguments arguments.length x)
    (arguments := arguments)
    (by simpa using hschema)
    (tieArguments_referenceClosed
      (referenceClosed_of_wellFormed hschema) hx)
    hargumentsClosed
  have hreplacementClosed :=
    replaceArgument_referenceClosed hx hargumentsClosed
      (instantiate_referenceClosed
        (tieVariable_referenceClosed
          (referenceClosed_of_wellFormed hschema) x)
        hargumentsClosed)
  have hcongruence := instantiate_unfoldingEquivalent
    (referenceClosed_of_wellFormed hschema)
    (tieComposed_forall₂_replace
      hschema hx hargumentsClosed)
    (tieComposed_referenceClosed
      (referenceClosed_of_wellFormed hschema)
      hx hargumentsClosed)
    hreplacementClosed
  exact hlifted.trans
    (hcomposition.trans hcongruence)

private theorem nontrivialUnaryCode_eq_false_root
    {context : RegularTerm}
    (hfalse : context.nontrivialUnaryCode ≠ true) :
    context.rootNode? = some (.inl 0) := by
  unfold nontrivialUnaryCode at hfalse
  cases hroot : context.rootNode? with
  | none => simp [hroot] at hfalse
  | some node =>
      cases node with
      | inr app => simp [hroot] at hfalse
      | inl y =>
          cases y with
          | zero => rfl
          | succ y => simp [hroot] at hfalse

private theorem rootNode_variable_of_unfoldingEquivalent_variableTerm
    {term : RegularTerm} {x : ℕ}
    (hequivalent :
      term.UnfoldingEquivalent (variableTerm x)) :
    term.rootNode? = some (.inl x) := by
  obtain ⟨R, hroot, hR⟩ := hequivalent
  have hcompatible := hR term.root (variableTerm x).root hroot
  unfold NodeCompatible at hcompatible
  change RawCompatible R term.rootNode?
    (variableTerm x).rootNode? at hcompatible
  rw [variableTerm_rootNode?] at hcompatible
  cases hterm : term.rootNode? with
  | none =>
      rw [hterm] at hcompatible
      simp [RawCompatible] at hcompatible
  | some node =>
      cases node with
      | inr app =>
          rw [hterm] at hcompatible
          simp [RawCompatible] at hcompatible
      | inl y =>
          rw [hterm] at hcompatible
          simp only [RawCompatible] at hcompatible
          simpa [hcompatible] using hterm

private theorem unfoldingEquivalent_variableTerm_of_rootNode
    {ranks : List ℕ} {arity x : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks arity)
    (hx : x < arity)
    (hroot : term.rootNode? = some (.inl x)) :
    term.UnfoldingEquivalent (variableTerm x) := by
  have hargument :
      (identityArguments arity)[x]? =
        some (variableTerm x) :=
    identityArguments_getElem? hx
  have hinstance :=
    instantiate_unfoldingEquivalent_argument
      (schema := term)
      (arguments := identityArguments arity)
      (by simpa [rootNode?] using hroot)
      hargument (variableTerm_referenceClosed x)
  exact (instantiate_identity_unfoldingEquivalent hterm).symm.trans
    hinstance

private theorem rawSpecialization_not_variable_of_schema_not_variable
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks)
    (hnonvariable :
      ¬schema.UnfoldingEquivalent (variableTerm x)) :
    ¬RegularTerm.UnfoldingEquivalent
      (unarySpecializationRaw schema arguments x)
      (variableTerm 0) := by
  intro hequivalent
  have hrawRoot :=
    rootNode_variable_of_unfoldingEquivalent_variableTerm
      hequivalent
  have hschemaClosed := referenceClosed_of_wellFormed hschema
  let rootNode : RawNode :=
    schema.nodes[schema.root]'hschemaClosed.1
  have hrootNode : schema.rootNode? = some rootNode := by
    unfold rootNode? nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hschemaClosed.1, rfl⟩
  cases hkind : rootNode with
  | inr app =>
      rcases app with ⟨X, children⟩
      have hrootApplication : schema.rootNode? =
          some (.inr (X, children)) := by
        simpa [hkind] using hrootNode
      have hrootApplicationNode : schema.nodeAt? schema.root =
          some (.inr (X, children)) := by
        simpa [rootNode?] using hrootApplication
      have hrawApplication :
          (unarySpecializationRaw schema arguments x).rootNode? =
            some (.inr (X,
              children.map
                (schema.resolveRHSRef
                  (unarySpecializationArguments arguments x)))) := by
        change
          (schema.instantiate
            (unarySpecializationArguments arguments x)).nodeAt?
              (schema.resolveRHSRef
                (unarySpecializationArguments arguments x)
                schema.root) =
            some (.inr (X,
              children.map
                (schema.resolveRHSRef
                  (unarySpecializationArguments arguments x))))
        have hrootResolve :
            schema.resolveRHSRef
                (unarySpecializationArguments arguments x)
                schema.root = schema.root := by
          simp [resolveRHSRef, hrootApplicationNode]
        rw [hrootResolve,
          instantiate_nodeAt?_rhs schema
            (unarySpecializationArguments arguments x)
            hschemaClosed.1,
          hrootApplicationNode]
        rfl
      rw [hrawApplication] at hrawRoot
      simp at hrawRoot
  | inl y =>
      have hvariable : schema.rootNode? =
          some (.inl y) := by
        simpa [hkind] using hrootNode
      have hvariableNode : schema.nodeAt? schema.root =
          some (.inl y) := by
        simpa [rootNode?] using hvariable
      have hy : y < arguments.length := by
        unfold WellFormed wellFormedCode at hschema
        rw [Bool.and_eq_true] at hschema
        have hmem : (.inl y : RawNode) ∈ schema.nodes :=
          List.mem_of_getElem? hvariable
        have hwell :=
          (List.all_eq_true.mp hschema.2) _ hmem
        simpa [nodeWellFormedCode] using
          of_decide_eq_true hwell
      by_cases hyx : y = x
      · subst y
        exact hnonvariable
          (unfoldingEquivalent_variableTerm_of_rootNode
            hschema hx hvariable)
      · let argument := arguments[y]
        have hargument : arguments[y]? = some argument :=
          List.getElem?_eq_getElem hy
        have hpartial :
            (unarySpecializationArguments arguments x)[y]? =
              some argument.sanitizeUnary := by
          simpa [argument] using
            unarySpecializationArguments_getElem?_ne
              hy (fun hxy => hyx hxy.symm)
        have hground :=
          (harguments argument
            (List.mem_of_getElem? hargument)).sanitizeUnary
        obtain ⟨support, _hsupport, hwitness⟩ := hground.2
        obtain ⟨X, children, hargumentRoot, _⟩ :=
          hwitness.2 argument.sanitizeUnary.root hwitness.1
        have hcopied := instantiate_nodeAt?_argument
          schema (unarySpecializationArguments arguments x)
          hpartial hargumentRoot
        have hrawApplication :
            (unarySpecializationRaw schema arguments x).rootNode? =
              some (.inr (X,
                children.map
                  (argumentOffset schema.nodes.length
                    (unarySpecializationArguments arguments x) y + ·))) := by
          change
            (schema.instantiate
              (unarySpecializationArguments arguments x)).nodeAt?
                (schema.resolveRHSRef
                  (unarySpecializationArguments arguments x)
                  schema.root) =
              some (.inr (X,
                children.map
                  (argumentOffset schema.nodes.length
                    (unarySpecializationArguments arguments x) y + ·)))
          have hresolve :
              schema.resolveRHSRef
                  (unarySpecializationArguments arguments x)
                  schema.root =
                argumentOffset schema.nodes.length
                    (unarySpecializationArguments arguments x) y +
                  argument.sanitizeUnary.root := by
            simp [resolveRHSRef, hvariableNode,
              argumentRoot?, hpartial]
          rw [hresolve]
          simpa [shiftNode] using hcopied
        rw [hrawApplication] at hrawRoot
        simp at hrawRoot

/-- If the open term before sanitization is not the bare variable, the
sanitized unary context satisfies the certificate rule's syntactic
nontriviality check. -/
public theorem HasUnaryWitness.sanitizeUnary_nontrivial
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hwitness : term.HasUnaryWitness)
    (hterm : term.WellFormed ranks variableBound)
    (hnonvariable :
      ¬term.UnfoldingEquivalent (variableTerm 0)) :
    term.sanitizeUnary.nontrivialUnaryCode = true := by
  by_contra hfalse
  have hroot := nontrivialUnaryCode_eq_false_root hfalse
  have hcontextWellFormed :
      term.sanitizeUnary.WellFormed ranks 1 :=
    sanitizeUnary_wellFormed hterm
  have hidentity :=
    instantiate_identity_unfoldingEquivalent
      hcontextWellFormed
  have hrootNode :
      term.sanitizeUnary.nodeAt?
          term.sanitizeUnary.root =
        some (.inl 0) := by
    simpa [rootNode?] using hroot
  have hargument :=
    instantiate_unfoldingEquivalent_argument
      (schema := term.sanitizeUnary)
      (arguments := [variableTerm 0])
      hrootNode (by simp)
      (variableTerm_referenceClosed 0)
  have hcontextVariable :
      term.sanitizeUnary.UnfoldingEquivalent
        (variableTerm 0) :=
    hidentity.symm.trans hargument
  exact hnonvariable
    (hwitness.sanitizeUnary_unfoldingEquivalent.symm.trans
      hcontextVariable)

/-- Specialization-specific nontriviality criterion.  The premise says that
`H` with every fixed argument installed and slot `x` left open is not merely
that open variable. -/
public theorem unarySpecialization_nontrivial
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks)
    (hnonvariable :
      ¬RegularTerm.UnfoldingEquivalent
        (unarySpecializationRaw schema arguments x)
        (variableTerm 0)) :
    nontrivialUnaryCode
      (unarySpecialization schema arguments x) = true := by
  apply HasUnaryWitness.sanitizeUnary_nontrivial
    (unarySpecializationRaw_hasUnaryWitness
      (x := x) hschema harguments)
    (unarySpecializationRaw_wellFormed
      (x := x) hschema harguments)
    hnonvariable

/-- Exact exposed-equation endpoint: if the original open schema is not the
selected positional variable, freezing all other slots yields a nontrivial
unary context. -/
public theorem unarySpecialization_nontrivial_of_schema_not_variable
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks)
    (hnonvariable :
      ¬schema.UnfoldingEquivalent (variableTerm x)) :
    nontrivialUnaryCode
      (unarySpecialization schema arguments x) = true := by
  apply unarySpecialization_nontrivial
    (x := x) hschema harguments
  exact rawSpecialization_not_variable_of_schema_not_variable
    hschema hx harguments hnonvariable

end RegularTerm

end DCFEquivalence
