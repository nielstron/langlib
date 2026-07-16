module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisSemantics

@[expose]
public section

/-!
# Operational laws for guarded unary contexts

This module discharges the operational interface used by the finite-basis
semantics.  In particular, the laws below are consequences of the executable
root-rewriting semantics and syntactic grammar well-formedness; they are not
additional promises on grammar codes.
-/

namespace DCFEquivalence

namespace RegularTerm

private def EdgesBound (nodes : List RawNode) (bound : ℕ) : Prop :=
  ∀ X children, (.inr (X, children) : RawNode) ∈ nodes →
    ∀ child ∈ children, child < bound

/-- Appending argument graphs contributes exactly the sum of their node
counts; the starting offset changes references but not list length. -/
public theorem appendArguments_length (offset : ℕ)
    (arguments : List RegularTerm) :
    (appendArguments offset arguments).length =
      (arguments.map (fun argument => argument.nodes.length)).sum := by
  induction arguments generalizing offset with
  | nil => simp [appendArguments]
  | cons argument arguments ih =>
      rw [appendArguments_cons]
      simp [ih]

private theorem argument_segment_le
    {arguments : List RegularTerm} {x : ℕ} {argument : RegularTerm}
    (hargument : arguments[x]? = some argument) (base : ℕ) :
    argumentOffset base arguments x + argument.nodes.length ≤
      base + (arguments.map (fun term => term.nodes.length)).sum := by
  induction arguments generalizing x base with
  | nil => simp at hargument
  | cons first rest ih =>
      cases x with
      | zero =>
          have hfirst : first = argument := by simpa using hargument
          subst first
          simp
      | succ x =>
          have hrest : rest[x]? = some argument := by simpa using hargument
          rw [argumentOffset_cons_succ]
          simpa [Nat.add_assoc] using ih hrest (base + first.nodes.length)

private theorem resolveRHSRef_lt
    {rhs : RegularTerm} {arguments : List RegularTerm}
    (harguments : ∀ argument ∈ arguments, argument.ReferenceClosed)
    {i : ℕ} (hi : i < rhs.nodes.length) :
    rhs.resolveRHSRef arguments i <
      rhs.nodes.length +
        (arguments.map (fun argument => argument.nodes.length)).sum := by
  unfold resolveRHSRef
  cases hnode : rhs.nodeAt? i with
  | none => simp; omega
  | some node =>
      cases node with
      | inr app => simp; omega
      | inl x =>
          cases hargument : arguments[x]? with
          | none => simp [argumentRoot?, hargument]; omega
          | some argument =>
              have hmem : argument ∈ arguments :=
                List.mem_of_getElem? hargument
              have hroot := (harguments argument hmem).1
              have hspan := argument_segment_le hargument rhs.nodes.length
              simp only [argumentRoot?, hargument, Option.map_some,
                Option.getD_some]
              omega

private theorem appendArguments_edgesBound
    {arguments : List RegularTerm}
    (harguments : ∀ argument ∈ arguments, argument.ReferenceClosed)
    (offset : ℕ) :
    EdgesBound (appendArguments offset arguments)
      (offset +
        (arguments.map (fun argument => argument.nodes.length)).sum) := by
  induction arguments generalizing offset with
  | nil => simp [EdgesBound, appendArguments]
  | cons argument arguments ih =>
      rw [appendArguments_cons]
      intro X children hnode child hchild
      rw [List.mem_append] at hnode
      cases hnode with
      | inl hfirst =>
          obtain ⟨source, hsourceMem, hsource⟩ := List.mem_map.mp hfirst
          cases hkind : source with
          | inl x => simp [hkind, shiftNode] at hsource
          | inr app =>
              rcases app with ⟨Y, sourceChildren⟩
              simp only [hkind, shiftNode, Sum.inr.injEq,
                Prod.mk.injEq] at hsource
              rcases hsource with ⟨hYX, hchildren⟩
              subst Y
              subst children
              obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
                List.mem_map.mp hchild
              obtain ⟨sourceIndex, hsourceIndex, hsourceGet⟩ :=
                List.mem_iff_getElem.mp hsourceMem
              have hsourceNode : argument.nodeAt? sourceIndex =
                  some (.inr (X, sourceChildren)) := by
                unfold nodeAt?
                rw [List.getElem?_eq_some_iff]
                exact ⟨hsourceIndex, hsourceGet.trans hkind⟩
              have hbound := (harguments argument (by simp)).2
                sourceIndex X sourceChildren hsourceNode
                sourceChild hsourceChild
              simp
              omega
      | inr hrest =>
          simpa [Nat.add_assoc] using
            ih (fun term hterm => harguments term (by simp [hterm]))
              (offset + argument.nodes.length) X children hrest child hchild

private theorem instantiate_edgesBound
    {rhs : RegularTerm} {arguments : List RegularTerm}
    (hrhs : rhs.ReferenceClosed)
    (harguments : ∀ argument ∈ arguments, argument.ReferenceClosed) :
    EdgesBound (rhs.instantiate arguments).nodes
      (rhs.nodes.length +
        (arguments.map (fun argument => argument.nodes.length)).sum) := by
  intro X children hnode child hchild
  unfold instantiate nodes at hnode
  rw [List.mem_append] at hnode
  cases hnode with
  | inl hrhsNode =>
      obtain ⟨source, hsourceMem, hsource⟩ := List.mem_map.mp hrhsNode
      cases hkind : source with
      | inl x => simp [hkind, instantiateNode] at hsource
      | inr app =>
          rcases app with ⟨Y, sourceChildren⟩
          simp only [hkind, instantiateNode, Sum.inr.injEq,
            Prod.mk.injEq] at hsource
          rcases hsource with ⟨hYX, hchildren⟩
          subst Y
          subst children
          obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
            List.mem_map.mp hchild
          obtain ⟨sourceIndex, hsourceIndex, hsourceGet⟩ :=
            List.mem_iff_getElem.mp hsourceMem
          apply resolveRHSRef_lt harguments
          exact hrhs.2 sourceIndex X sourceChildren (by
            unfold nodeAt?
            rw [List.getElem?_eq_some_iff]
            exact ⟨hsourceIndex, hsourceGet.trans hkind⟩)
            sourceChild hsourceChild
  | inr hargumentsNode =>
      exact appendArguments_edgesBound harguments rhs.nodes.length
        X children hargumentsNode child hchild

/-- Instantiating a reference-closed schema by reference-closed argument
graphs yields a reference-closed graph, for any finite arity. -/
public theorem instantiate_referenceClosed
    {rhs : RegularTerm} {arguments : List RegularTerm}
    (hrhs : rhs.ReferenceClosed)
    (harguments : ∀ argument ∈ arguments, argument.ReferenceClosed) :
    (rhs.instantiate arguments).ReferenceClosed := by
  have hlength : (rhs.instantiate arguments).nodes.length =
      rhs.nodes.length +
        (arguments.map (fun argument => argument.nodes.length)).sum := by
    simp [instantiate, nodes, appendArguments_length]
  constructor
  · change rhs.resolveRHSRef arguments rhs.root <
      (rhs.instantiate arguments).nodes.length
    rw [hlength]
    exact resolveRHSRef_lt harguments hrhs.1
  · intro i X children hnode child hchild
    rw [hlength]
    apply instantiate_edgesBound hrhs harguments X children
    · exact List.mem_of_getElem? hnode
    · exact hchild

@[simp] public theorem instantiate_withRoot
    (schema : RegularTerm) (arguments : List RegularTerm) (child : ℕ) :
    (schema.instantiate arguments).withRoot
        (schema.resolveRHSRef arguments child) =
      (schema.withRoot child).instantiate arguments := by
  rfl

/-- Reading a successful root-application view returns that application node. -/
public theorem nodeAt?_root_of_rootApplication?
    {term : RegularTerm} {X : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (X, children)) :
    term.nodeAt? term.root = some (.inr (X, children)) := by
  unfold rootApplication? rootNode? at hroot
  cases hnode : term.nodeAt? term.root with
  | none => simp [hnode] at hroot
  | some node =>
      cases node with
      | inl x => simp [hnode] at hroot
      | inr app =>
          rcases app with ⟨Y, sourceChildren⟩
          simp only [hnode, Option.some.injEq, Prod.mk.injEq] at hroot
          rcases hroot with ⟨rfl, rfl⟩
          rfl

/-- Instantiation preserves an application root and resolves its child
references into the combined graph. -/
public theorem instantiate_rootApplication?
    {schema : RegularTerm} {arguments : List RegularTerm}
    {X : ℕ} {children : List ℕ}
    (hclosed : schema.ReferenceClosed)
    (hroot : schema.rootApplication? = some (X, children)) :
    (schema.instantiate arguments).rootApplication? =
      some (X, children.map (schema.resolveRHSRef arguments)) := by
  have hnode := nodeAt?_root_of_rootApplication? hroot
  have hresolve : schema.resolveRHSRef arguments schema.root =
      schema.root := by
    simp [resolveRHSRef, hnode]
  have hinstRoot : (schema.instantiate arguments).root = schema.root := by
    simpa [instantiate] using hresolve
  unfold rootApplication? rootNode?
  rw [hinstRoot, instantiate_nodeAt?_rhs schema arguments hclosed.1,
    hnode]
  rfl

private def EmbeddedArgumentRelation
    (schema : RegularTerm) (arguments : List RegularTerm)
    (x : ℕ) (argument : RegularTerm) (i j : ℕ) : Prop :=
  j < argument.nodes.length ∧
    i = argumentOffset schema.nodes.length arguments x + j

private theorem forall₂_map_self
    {A B : Type} {R : B → A → Prop} (f : A → B)
    (values : List A) (h : ∀ value ∈ values, R (f value) value) :
    List.Forall₂ R (values.map f) values := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun tail htail => h tail (by simp [htail]))

private theorem embeddedArgumentRelation_isBisimulation
    {schema : RegularTerm} {arguments : List RegularTerm}
    {x : ℕ} {argument : RegularTerm}
    (hargument : arguments[x]? = some argument)
    (hclosed : argument.ReferenceClosed) :
    (schema.instantiate arguments).IsBisimulation argument
      (EmbeddedArgumentRelation schema arguments x argument) := by
  intro i j hij
  rcases hij with ⟨hj, rfl⟩
  let node : RawNode := argument.nodes[j]
  have hnode : argument.nodeAt? j = some node := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hj, rfl⟩
  unfold NodeCompatible
  rw [instantiate_nodeAt?_argument schema arguments hargument hnode,
    hnode]
  cases hkind : node with
  | inl y => simp [shiftNode, RawCompatible]
  | inr app =>
      rcases app with ⟨X, children⟩
      simp only [shiftNode, RawCompatible]
      refine ⟨trivial, ?_⟩
      have happNode : argument.nodeAt? j =
          some (.inr (X, children)) := by
        simpa [hkind] using hnode
      have hchildren : ∀ child ∈ children,
          child < argument.nodes.length :=
        hclosed.2 j X children happNode
      apply forall₂_map_self
      intro child hchild
      exact ⟨hchildren child hchild, rfl⟩

/-- If the root of a schema is a variable, instantiating the schema denotes
the corresponding argument graph. -/
public theorem instantiate_unfoldingEquivalent_argument
    {schema : RegularTerm} {arguments : List RegularTerm}
    {x : ℕ} {argument : RegularTerm}
    (hroot : schema.nodeAt? schema.root = some (.inl x))
    (hargument : arguments[x]? = some argument)
    (hclosed : argument.ReferenceClosed) :
    (schema.instantiate arguments).UnfoldingEquivalent argument := by
  refine ⟨EmbeddedArgumentRelation schema arguments x argument, ?_,
    embeddedArgumentRelation_isBisimulation hargument hclosed⟩
  change EmbeddedArgumentRelation schema arguments x argument
    (schema.resolveRHSRef arguments schema.root) argument.root
  refine ⟨hclosed.1, ?_⟩
  simp [resolveRHSRef, hroot, argumentRoot?, hargument]

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

private theorem rank_arity_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound)
    {i X : ℕ} {children : List ℕ}
    (hnode : term.nodeAt? i = some (.inr (X, children))) :
    ∃ rank, ranks[X]? = some rank ∧ children.length = rank := by
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  unfold nodeWellFormedCode at hwell
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hwell
  | some rank =>
      simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hwell
      exact ⟨rank, rfl, hwell.1⟩

private theorem withRoot_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound)
    {i : ℕ} (hi : i < term.nodes.length) :
    (term.withRoot i).WellFormed ranks variableBound := by
  unfold WellFormed wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨?_, ?_⟩
  · simpa [withRoot, root, nodes] using decide_eq_true hi
  · simpa [withRoot, nodes] using hterm.2

private theorem rootApplication?_of_nontrivialUnary
    {ranks : List ℕ} {context : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    (hnontrivial : context.nontrivialUnaryCode = true) :
    ∃ X children, context.rootApplication? = some (X, children) := by
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
      refine ⟨X, children, ?_⟩
      unfold rootApplication? rootNode?
      have happ : context.nodeAt? context.root =
          some (.inr (X, children)) := by
        simpa [hkind] using hroot
      rw [happ]

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private def ArgumentApprox (g : EncodedFirstOrderGrammar Action)
    (n : ℕ) (left right : RegularTerm) : Prop :=
  left.ReferenceClosed ∧ right.ReferenceClosed ∧
    g.TraceApprox n left right

private theorem argumentApprox_anti
    (g : EncodedFirstOrderGrammar Action) {m n : ℕ} (hmn : m ≤ n)
    {leftArguments rightArguments : List RegularTerm}
    (harguments : List.Forall₂ (ArgumentApprox g n)
      leftArguments rightArguments) :
    List.Forall₂ (ArgumentApprox g m) leftArguments rightArguments := by
  apply harguments.imp
  intro left right hpair
  exact ⟨hpair.1, hpair.2.1,
    g.traceApprox_anti hmn hpair.2.2⟩

private theorem forall₂_getElem?_some
    {R : RegularTerm → RegularTerm → Prop}
    {left right : List RegularTerm} (h : List.Forall₂ R left right)
    {x : ℕ} {leftArgument : RegularTerm}
    (hleft : left[x]? = some leftArgument) :
    ∃ rightArgument, right[x]? = some rightArgument ∧
      R leftArgument rightArgument := by
  induction h generalizing x with
  | nil => simp at hleft
  | cons hhead htail ih =>
      cases x with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hleft
          subst leftArgument
          exact ⟨_, rfl, hhead⟩
      | succ x => exact ih (by simpa using hleft)

private theorem arguments_left_referenceClosed
    {g : EncodedFirstOrderGrammar Action} {n : ℕ}
    {left right : List RegularTerm}
    (h : List.Forall₂ (ArgumentApprox g n) left right) :
    ∀ argument ∈ left, argument.ReferenceClosed := by
  intro argument hargument
  induction h with
  | nil => simp at hargument
  | cons hhead htail ih =>
      rw [List.mem_cons] at hargument
      rcases hargument with rfl | htailMem
      · exact hhead.1
      · exact ih htailMem

private theorem arguments_right_referenceClosed
    {g : EncodedFirstOrderGrammar Action} {n : ℕ}
    {left right : List RegularTerm}
    (h : List.Forall₂ (ArgumentApprox g n) left right) :
    ∀ argument ∈ right, argument.ReferenceClosed := by
  intro argument hargument
  induction h with
  | nil => simp at hargument
  | cons hhead htail ih =>
      rw [List.mem_cons] at hargument
      rcases hargument with rfl | htailMem
      · exact hhead.2.1
      · exact ih htailMem

private def pluggedChildren (schema : RegularTerm)
    (arguments : List RegularTerm) (children : List ℕ) :
    List RegularTerm :=
  children.map fun child => (schema.withRoot child).instantiate arguments

private theorem forall₂_map_both_same
    {A B C : Type} {R : B → C → Prop}
    (left : A → B) (right : A → C) (values : List A)
    (h : ∀ value ∈ values, R (left value) (right value)) :
    List.Forall₂ R (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun tail htail => h tail (by simp [htail]))

/-- Re-rooting an instantiated context at one of its resolved children is
literally the same graph code as instantiating the corresponding re-rooted
context.  This is the residual-substitution identity used after root rewrite. -/
private theorem resolvedChildren_eq_pluggedChildren
    (schema : RegularTerm) (arguments : List RegularTerm)
    (children : List ℕ) :
    (children.map (schema.resolveRHSRef arguments)).map
        (schema.instantiate arguments).withRoot =
      pluggedChildren schema arguments children := by
  simp [pluggedChildren, List.map_map]

private theorem selected_rhs_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {X : ℕ} {action : Action} {rhs : RegularTerm}
    (hrule : g.ruleLookup X action = some rhs) :
    ∃ rank, g.ranks[X]? = some rank ∧
      rhs.WellFormed g.ranks rank := by
  unfold WellFormed wellFormedCode at hg
  rw [Bool.and_eq_true] at hg
  unfold ruleLookup at hrule
  obtain ⟨rule, hfind, hrhs⟩ := Option.map_eq_some_iff.mp hrule
  have hmem := findRule_mem hfind
  have hrow := (List.all_eq_true.mp hg.1) rule hmem
  unfold ruleWellFormedCode at hrow
  cases hrank : g.ranks[rule.lhs]? with
  | none => simp [hrank] at hrow
  | some rank =>
      rw [hrank, Bool.and_eq_true] at hrow
      have hkey := findRule_key hfind
      have hX : rule.lhs = X := hkey.1
      subst X
      have hrhsEq : rule.rhs = rhs := by simpa using hrhs
      subst rhs
      exact ⟨rank, hrank, hrow.1⟩

public theorem selected_rhs_referenceClosed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {X : ℕ} {action : Action} {rhs : RegularTerm}
    (hrule : g.ruleLookup X action = some rhs) :
    rhs.ReferenceClosed := by
  obtain ⟨rank, _, hrhs⟩ := selected_rhs_wellFormed hg hrule
  exact RegularTerm.referenceClosed_of_wellFormed hrhs

private theorem pluggedChildren_argumentApprox
    {g : EncodedFirstOrderGrammar Action} {n : ℕ}
    {schema : RegularTerm}
    {leftArguments rightArguments : List RegularTerm}
    {X : ℕ} {children : List ℕ}
    (hschema : schema.WellFormed g.ranks leftArguments.length)
    (hroot : schema.nodeAt? schema.root = some (.inr (X, children)))
    (harguments : List.Forall₂ (ArgumentApprox g n)
      leftArguments rightArguments)
    (hcongruent : ∀ (inner : RegularTerm)
      (innerLeft innerRight : List RegularTerm),
      inner.WellFormed g.ranks innerLeft.length →
      List.Forall₂ (ArgumentApprox g n) innerLeft innerRight →
      g.TraceApprox n (inner.instantiate innerLeft)
        (inner.instantiate innerRight)) :
    List.Forall₂ (ArgumentApprox g n)
      (pluggedChildren schema leftArguments children)
      (pluggedChildren schema rightArguments children) := by
  have hschemaClosed := RegularTerm.referenceClosed_of_wellFormed hschema
  have hleftClosed := arguments_left_referenceClosed harguments
  have hrightClosed := arguments_right_referenceClosed harguments
  unfold pluggedChildren
  apply forall₂_map_both_same
  intro child hchildMem
  have hchild : child < schema.nodes.length :=
    hschemaClosed.2 schema.root X children hroot child hchildMem
  have hchildSchema : (schema.withRoot child).WellFormed
      g.ranks leftArguments.length :=
    RegularTerm.withRoot_wellFormed hschema hchild
  refine ⟨?_, ?_, hcongruent (schema.withRoot child)
    leftArguments rightArguments hchildSchema harguments⟩
  · exact RegularTerm.instantiate_referenceClosed
      (RegularTerm.withRoot_referenceClosed hschemaClosed hchild)
      hleftClosed
  · exact RegularTerm.instantiate_referenceClosed
      (RegularTerm.withRoot_referenceClosed hschemaClosed hchild)
      hrightClosed

private theorem application_context_delay
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {n : ℕ} {schema : RegularTerm}
    {leftArguments rightArguments : List RegularTerm}
    {X : ℕ} {children : List ℕ}
    (hschema : schema.WellFormed g.ranks leftArguments.length)
    (hroot : schema.rootApplication? = some (X, children))
    (harguments : List.Forall₂ (ArgumentApprox g n)
      leftArguments rightArguments)
    (hcongruent : ∀ (inner : RegularTerm)
      (innerLeft innerRight : List RegularTerm),
      inner.WellFormed g.ranks innerLeft.length →
      List.Forall₂ (ArgumentApprox g n) innerLeft innerRight →
      g.TraceApprox n (inner.instantiate innerLeft)
        (inner.instantiate innerRight)) :
    g.TraceApprox (n + 1) (schema.instantiate leftArguments)
      (schema.instantiate rightArguments) := by
  have hschemaClosed := RegularTerm.referenceClosed_of_wellFormed hschema
  have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
  have hleftRoot := RegularTerm.instantiate_rootApplication?
    (arguments := leftArguments) hschemaClosed hroot
  have hrightRoot := RegularTerm.instantiate_rootApplication?
    (arguments := rightArguments) hschemaClosed hroot
  have hchildrenApprox := pluggedChildren_argumentApprox hschema hrootNode
    harguments hcongruent
  intro label
  cases label with
  | inr x =>
      have hleftNode : (schema.instantiate leftArguments).rootNode? =
          some (.inr
            (X, children.map (schema.resolveRHSRef leftArguments))) := by
        simpa [RegularTerm.rootNode?] using
          RegularTerm.nodeAt?_root_of_rootApplication? hleftRoot
      have hrightNode : (schema.instantiate rightArguments).rootNode? =
          some (.inr
            (X, children.map (schema.resolveRHSRef rightArguments))) := by
        simpa [RegularTerm.rootNode?] using
          RegularTerm.nodeAt?_root_of_rootApplication? hrightRoot
      unfold step?
      rw [hleftNode, hrightNode]
      exact .none
  | inl action =>
      change Option.Rel (g.TraceApprox n)
        (g.rootRewrite? action (schema.instantiate leftArguments))
        (g.rootRewrite? action (schema.instantiate rightArguments))
      unfold rootRewrite?
      rw [hleftRoot, hrightRoot]
      change Option.Rel (g.TraceApprox n)
        ((g.ruleLookup X action).map fun rhs => rhs.instantiate
          ((children.map (schema.resolveRHSRef leftArguments)).map
            (schema.instantiate leftArguments).withRoot))
        ((g.ruleLookup X action).map fun rhs => rhs.instantiate
          ((children.map (schema.resolveRHSRef rightArguments)).map
            (schema.instantiate rightArguments).withRoot))
      rw [resolvedChildren_eq_pluggedChildren,
        resolvedChildren_eq_pluggedChildren]
      cases hrule : g.ruleLookup X action with
      | none =>
          simp only [Option.map_none]
          exact .none
      | some rhs =>
          simp only [Option.map_some]
          apply Option.Rel.some
          obtain ⟨ruleRank, hruleRank, hrhs⟩ :=
            selected_rhs_wellFormed hg hrule
          obtain ⟨schemaRank, hschemaRank, hchildrenLength⟩ :=
            RegularTerm.rank_arity_of_wellFormed hschema hrootNode
          have hranks : ruleRank = schemaRank := by
            exact Option.some.inj (hruleRank.symm.trans hschemaRank)
          have hchildrenRuleRank : children.length = ruleRank :=
            hchildrenLength.trans hranks.symm
          have hrhsChildren : rhs.WellFormed g.ranks children.length := by
            rw [hchildrenRuleRank]
            exact hrhs
          apply hcongruent rhs
            (pluggedChildren schema leftArguments children)
            (pluggedChildren schema rightArguments children)
          · simpa [pluggedChildren] using hrhsChildren
          · exact hchildrenApprox

private theorem rootRewrite?_preserves_referenceClosed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {action : Action} {source target : RegularTerm}
    (hsource : source.ReferenceClosed)
    (hstep : g.rootRewrite? action source = some target) :
    target.ReferenceClosed := by
  unfold rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some app =>
      rcases app with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ := Option.map_eq_some_iff.mp hstep
      subst target
      apply RegularTerm.instantiate_referenceClosed
        (selected_rhs_referenceClosed hg hrule)
      intro argument hargument
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
      apply RegularTerm.withRoot_referenceClosed hsource
      exact RegularTerm.rootApplication_children_lt hsource hroot
        child hchild

public theorem step?_preserves_referenceClosed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {label : Label Action} {source target : RegularTerm}
    (hsource : source.ReferenceClosed)
    (hstep : g.step? label source = some target) :
    target.ReferenceClosed := by
  cases label with
  | inl action =>
      exact rootRewrite?_preserves_referenceClosed hg hsource hstep
  | inr x =>
      unfold step? at hstep
      cases hroot : source.rootNode? with
      | none => simp [hroot] at hstep
      | some node =>
          cases node with
          | inr app => simp [hroot] at hstep
          | inl y =>
              by_cases hxy : x = y
              · simp [hroot, hxy] at hstep
                subst target
                exact hsource
              · simp [hroot, hxy] at hstep

private theorem unfoldingApprox_of_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed) :
    ∀ (n : ℕ) (left right : RegularTerm),
      left.ReferenceClosed → right.ReferenceClosed →
      left.UnfoldingEquivalent right → g.TraceApprox n left right := by
  intro n
  induction n with
  | zero =>
      intro left right hleft hright hequivalent
      trivial
  | succ n ih =>
      intro left right hleft hright hequivalent label
      have hrel := step?_respects_unfoldingEquivalent (label := label)
        hequivalent
        hleft hright (fun X action rhs hrule =>
          selected_rhs_referenceClosed hg hrule)
      cases hleftStep : g.step? label left with
      | none =>
          rw [hleftStep] at hrel
          cases hrightStep : g.step? label right with
          | none => exact .none
          | some right' =>
              rw [hrightStep] at hrel
              cases hrel
      | some left' =>
          rw [hleftStep] at hrel
          cases hrightStep : g.step? label right with
          | none =>
              rw [hrightStep] at hrel
              cases hrel
          | some right' =>
              rw [hrightStep] at hrel
              cases hrel with
              | some hequivalent' =>
                  exact .some (ih left' right'
                    (step?_preserves_referenceClosed hg hleft hleftStep)
                    (step?_preserves_referenceClosed hg hright hrightStep)
                    hequivalent')

private theorem instantiate_traceApprox_of_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed) :
    ∀ (n : ℕ) (schema : RegularTerm)
      (leftArguments rightArguments : List RegularTerm),
      schema.WellFormed g.ranks leftArguments.length →
      List.Forall₂ (ArgumentApprox g n) leftArguments rightArguments →
      g.TraceApprox n (schema.instantiate leftArguments)
        (schema.instantiate rightArguments) := by
  intro n
  induction n with
  | zero =>
      intro schema leftArguments rightArguments hschema harguments
      trivial
  | succ n ih =>
      intro schema leftArguments rightArguments hschema harguments
      have hschemaClosed :=
        RegularTerm.referenceClosed_of_wellFormed hschema
      let rootNode : RawNode := schema.nodes[schema.root]'hschemaClosed.1
      have hrootNode : schema.nodeAt? schema.root = some rootNode := by
        unfold RegularTerm.nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hschemaClosed.1, rfl⟩
      cases hkind : rootNode with
      | inl x =>
          have hvariable : schema.nodeAt? schema.root = some (.inl x) := by
            simpa [hkind] using hrootNode
          have hx : x < leftArguments.length :=
            RegularTerm.variable_lt_of_wellFormed hschema hvariable
          let leftArgument : RegularTerm := leftArguments[x]
          have hleftArgument : leftArguments[x]? = some leftArgument := by
            unfold leftArgument
            rw [List.getElem?_eq_some_iff]
            exact ⟨hx, rfl⟩
          obtain ⟨rightArgument, hrightArgument, hpair⟩ :=
            forall₂_getElem?_some harguments hleftArgument
          have hleftEquivalent :
              (schema.instantiate leftArguments).UnfoldingEquivalent
                leftArgument :=
            RegularTerm.instantiate_unfoldingEquivalent_argument hvariable
              hleftArgument hpair.1
          have hrightEquivalent :
              (schema.instantiate rightArguments).UnfoldingEquivalent
                rightArgument :=
            RegularTerm.instantiate_unfoldingEquivalent_argument hvariable
              hrightArgument hpair.2.1
          have hleftSourceClosed :
              (schema.instantiate leftArguments).ReferenceClosed :=
            RegularTerm.instantiate_referenceClosed hschemaClosed
              (arguments_left_referenceClosed harguments)
          have hrightSourceClosed :
              (schema.instantiate rightArguments).ReferenceClosed :=
            RegularTerm.instantiate_referenceClosed hschemaClosed
              (arguments_right_referenceClosed harguments)
          have hleftApprox := unfoldingApprox_of_wellFormed hg (n + 1)
            (schema.instantiate leftArguments) leftArgument
            hleftSourceClosed hpair.1 hleftEquivalent
          have hrightApprox := unfoldingApprox_of_wellFormed hg (n + 1)
            (schema.instantiate rightArguments) rightArgument
            hrightSourceClosed hpair.2.1 hrightEquivalent
          exact hleftApprox.trans (hpair.2.2.trans hrightApprox.symm)
      | inr app =>
          rcases app with ⟨X, children⟩
          have happlication : schema.rootApplication? =
              some (X, children) := by
            unfold RegularTerm.rootApplication? RegularTerm.rootNode?
            have happNode : schema.nodeAt? schema.root =
                some (.inr (X, children)) := by
              simpa [hkind] using hrootNode
            rw [happNode]
          apply application_context_delay hg hschema happlication
            (argumentApprox_anti g (Nat.le_succ n) harguments)
          intro inner innerLeft innerRight hinner hinnerArguments
          exact ih inner innerLeft innerRight hinner hinnerArguments

/-- Every syntactically well-formed deterministic first-order grammar satisfies
the unfolding, context-congruence, and one-step guarded-delay laws used by the
finite-basis semantics. -/
public theorem guardedContextLaws_of_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed) :
    g.GuardedContextLaws := by
  constructor
  · exact unfoldingApprox_of_wellFormed hg
  · intro n context left right hcontext hleft hright happrox
    apply instantiate_traceApprox_of_wellFormed hg n context [left] [right]
      (by simpa using hcontext)
    exact .cons ⟨hleft, hright, happrox⟩ .nil
  · intro n context left right hcontext hnontrivial hleft hright happrox
    obtain ⟨X, children, hroot⟩ :=
      RegularTerm.rootApplication?_of_nontrivialUnary hcontext hnontrivial
    apply application_context_delay hg (n := n) (X := X)
      (children := children) (leftArguments := [left])
      (rightArguments := [right]) (by simpa using hcontext) hroot
    · exact .cons ⟨hleft, hright, happrox⟩ .nil
    · intro inner innerLeft innerRight hinner hinnerArguments
      exact instantiate_traceApprox_of_wellFormed hg n inner innerLeft
        innerRight hinner hinnerArguments

end EncodedFirstOrderGrammar

end DCFEquivalence
