module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.UnarySpecialization

@[expose]
public section

/-!
# Uniqueness of guarded unary fixed points

The graph `context.unaryLimit` is the canonical solution of a nontrivial
unary regular context.  This file proves the coinductive uniqueness property
needed to identify that concrete certificate term with parametric tying.
-/

namespace DCFEquivalence

namespace RegularTerm

private theorem variable_lt_of_wellFormed_local
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

private theorem root_application_of_nontrivial_unary_local
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
      have hx : x < 1 := variable_lt_of_wellFormed_local hcontext (by
        simpa [hkind] using hroot)
      have hxzero : x = 0 := by omega
      subst x
      have hrootVariable : context.rootNode? = some (.inl 0) := by
        simpa [rootNode?, hkind] using hroot
      simp [nontrivialUnaryCode, hrootVariable] at hnontrivial
  | inr app =>
      rcases app with ⟨X, children⟩
      exact ⟨X, children, by simpa [hkind] using hroot⟩

/-- Candidate bisimulation between the canonical unary limit and another
fixed point.  A closed context reference on the left is paired with any node
on the right bisimilar to the corresponding reference in `context[term]`. -/
@[expose] public def UnaryFixedPointRelation
    (context term : RegularTerm) (left right : ℕ) : Prop :=
  ∃ source, source < context.nodes.length ∧
    left = context.closeUnaryReference source ∧
    (context.instantiate [term]).BisimilarAt
      (context.resolveRHSRef [term] source) term right

private theorem unaryFixedPointRelation_children
    {context term : RegularTerm} {parent symbol : ℕ}
    {children rightChildren : List ℕ}
    (hclosed : context.ReferenceClosed)
    (hnode : context.nodeAt? parent =
      some (.inr (symbol, children)))
    (hchildren : List.Forall₂
      (fun left right =>
        (context.instantiate [term]).BisimilarAt left term right)
      (children.map (context.resolveRHSRef [term])) rightChildren) :
    List.Forall₂ (context.UnaryFixedPointRelation term)
      (children.map context.closeUnaryReference) rightChildren := by
  have hchildrenBound :
      ∀ child ∈ children, child < context.nodes.length := by
    intro child hchild
    exact hclosed.2 parent symbol children hnode child hchild
  clear hnode hclosed parent symbol
  induction children generalizing rightChildren with
  | nil =>
      simp only [List.map_nil] at hchildren ⊢
      cases hchildren
      exact .nil
  | cons child children ih =>
      simp only [List.map_cons] at hchildren ⊢
      cases hchildren with
      | cons hhead htail =>
          apply List.Forall₂.cons
          · refine ⟨child, ?_, rfl, hhead⟩
            exact hchildrenBound child (by simp)
          · apply ih
            · exact htail
            · intro tail htailMem
              exact hchildrenBound tail (by simp [htailMem])

/-- A nontrivial well-formed unary context has at most one reference-closed
fixed point, up to equality of regular unfoldings. -/
public theorem unaryLimit_unfoldingEquivalent_of_fixedPoint
    {ranks : List ℕ} {context term : RegularTerm}
    (hcontext : context.WellFormed ranks 1)
    (hnontrivial : context.nontrivialUnaryCode = true)
    (hterm : term.ReferenceClosed)
    (hfixed : (context.instantiate [term]).UnfoldingEquivalent term) :
    context.unaryLimit.UnfoldingEquivalent term := by
  let instantiated := context.instantiate [term]
  have hcontextClosed := referenceClosed_of_wellFormed hcontext
  obtain ⟨rootSymbol, rootChildren, hrootApplication⟩ :=
    root_application_of_nontrivial_unary_local hcontext hnontrivial
  refine ⟨context.UnaryFixedPointRelation term, ?_, ?_⟩
  · refine ⟨context.root, hcontextClosed.1, ?_, ?_⟩
    · simp
    · simpa [instantiated] using hfixed
  · intro leftIndex rightIndex hrelation
    obtain ⟨source, hsourceBound, hleftIndex, hbisimilar⟩ := hrelation
    have hnormalized :
        ∃ normalized, normalized < context.nodes.length ∧
          leftIndex = context.closeUnaryReference normalized ∧
          instantiated.BisimilarAt
            (context.resolveRHSRef [term] normalized) term rightIndex ∧
          ∃ symbol children,
            context.nodeAt? normalized =
              some (.inr (symbol, children)) := by
      cases hsourceNode : context.nodeAt? source with
      | none =>
          unfold nodeAt? at hsourceNode
          have hsome :
              context.nodes[source]? = some context.nodes[source] :=
            List.getElem?_eq_getElem hsourceBound
          rw [hsourceNode] at hsome
          contradiction
      | some sourceNode =>
          cases sourceNode with
          | inr app =>
              rcases app with ⟨symbol, children⟩
              exact ⟨source, hsourceBound, hleftIndex, by
                simpa [instantiated] using hbisimilar,
                symbol, children, hsourceNode⟩
          | inl x =>
              have hx : x < 1 :=
                variable_lt_of_wellFormed_local hcontext hsourceNode
              have hxzero : x = 0 := by omega
              subst x
              have hcopy : instantiated.BisimilarAt
                  (context.resolveRHSRef [term] source)
                  term term.root := by
                have hargument : [term][0]? = some term := by simp
                have hpointed := instantiate_unfoldingEquivalent_argument
                  (schema := context.withRoot source)
                  (arguments := [term])
                  (by simpa using hsourceNode) hargument hterm
                apply (withRoot_unfoldingEquivalent_iff_bisimilarAt
                  instantiated term
                  (context.resolveRHSRef [term] source) term.root).mp
                simpa [instantiated] using hpointed
              have htermRoot : term.BisimilarAt term.root term rightIndex :=
                hcopy.symm.trans (by
                  simpa [instantiated] using hbisimilar)
              have hrootFixed : instantiated.BisimilarAt
                  (context.resolveRHSRef [term] context.root)
                  term term.root := by
                simpa [instantiated] using hfixed
              have hrootBisimilar : instantiated.BisimilarAt
                  (context.resolveRHSRef [term] context.root)
                  term rightIndex :=
                hrootFixed.trans htermRoot
              refine ⟨context.root, hcontextClosed.1, ?_,
                hrootBisimilar, rootSymbol, rootChildren,
                  hrootApplication⟩
              calc
                leftIndex = context.root := by
                  simpa [closeUnaryReference, hsourceNode] using hleftIndex
                _ = context.closeUnaryReference context.root :=
                  (closeUnaryReference_root context).symm
    obtain ⟨normalized, hnormalizedBound, hleftNormalized,
      hbisimilarNormalized, symbol, children, hnormalizedNode⟩ := hnormalized
    have hresolve : context.resolveRHSRef [term] normalized = normalized := by
      simp [resolveRHSRef, hnormalizedNode]
    have hclose : context.closeUnaryReference normalized = normalized := by
      simp [closeUnaryReference, hnormalizedNode]
    have hpointed :
        (instantiated.withRoot normalized).UnfoldingEquivalent
          (term.withRoot rightIndex) := by
      apply (withRoot_unfoldingEquivalent_iff_bisimilarAt
        instantiated term normalized rightIndex).mpr
      simpa [hresolve] using hbisimilarNormalized
    have hinstantiatedNode : instantiated.nodeAt? normalized =
        some (.inr (symbol,
          children.map (context.resolveRHSRef [term]))) := by
      unfold instantiated
      rw [instantiate_nodeAt?_rhs context [term] hnormalizedBound,
        hnormalizedNode]
      rfl
    have hinstantiatedRootApplication :
        (instantiated.withRoot normalized).rootApplication? =
          some (symbol,
            children.map (context.resolveRHSRef [term])) := by
      change
        (match instantiated.nodeAt? normalized with
        | some (.inr app) => some app
        | _ => none) =
          some (symbol,
            children.map (context.resolveRHSRef [term]))
      rw [hinstantiatedNode]
    obtain ⟨rightChildren, hrightApplication, hchildren⟩ :=
      rootApplication?_of_unfoldingEquivalent hpointed
        hinstantiatedRootApplication
    have hrightNode : term.nodeAt? rightIndex =
        some (.inr (symbol, rightChildren)) := by
      change
        (match term.nodeAt? rightIndex with
        | some (.inr app) => some app
        | _ => none) = some (symbol, rightChildren)
        at hrightApplication
      cases hnode : term.nodeAt? rightIndex with
      | none => simp [hnode] at hrightApplication
      | some node =>
          cases node with
          | inl x => simp [hnode] at hrightApplication
          | inr app =>
              rcases app with ⟨rightSymbol, foundChildren⟩
              simp only [hnode, Option.some.injEq, Prod.mk.injEq]
                at hrightApplication
              rcases hrightApplication with
                ⟨hrightSymbol, hfoundChildren⟩
              subst rightSymbol
              subst foundChildren
              rfl
    unfold NodeCompatible
    rw [hleftNormalized, hclose, unaryLimit_nodeAt?,
      hnormalizedNode, hrightNode]
    simp only [Option.map_some, closeUnaryNode, RawCompatible]
    refine ⟨trivial, ?_⟩
    apply unaryFixedPointRelation_children hcontextClosed
      (parent := normalized) (symbol := symbol) (children := children)
    · exact hnormalizedNode
    · simpa [instantiated] using hchildren

/-- Closing the concrete unary specialization denotes exactly the concrete
instance of the bounded same-arity parametric tying.  This is the bridge
between the certificate calculus's unary limit and the schema retained by
tail elimination. -/
public theorem unarySpecialization_unaryLimit_unfoldingEquivalent_tiedInstance
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground ranks)
    (hnonvariable :
      ¬schema.UnfoldingEquivalent (variableTerm x)) :
    (unarySpecialization schema arguments x).unaryLimit.UnfoldingEquivalent
      ((schema.tieVariable x).instantiate arguments) := by
  let context := unarySpecialization schema arguments x
  let tiedInstance := (schema.tieVariable x).instantiate arguments
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact referenceClosed_of_ground (harguments argument hargument)
  have hcontext : context.WellFormed ranks 1 := by
    exact unarySpecialization_wellFormed hschema harguments
  have hnontrivial : context.nontrivialUnaryCode = true := by
    exact unarySpecialization_nontrivial_of_schema_not_variable
      hschema hx harguments hnonvariable
  have htiedClosed : tiedInstance.ReferenceClosed := by
    apply instantiate_referenceClosed
    · exact tieVariable_referenceClosed
        (referenceClosed_of_wellFormed hschema) x
    · exact hargumentsClosed
  have hfill : (context.instantiate [tiedInstance]).UnfoldingEquivalent
      (schema.instantiate
        (replaceArgument arguments x tiedInstance)) := by
    exact unarySpecialization_instantiate_focus hschema hx harguments
      htiedClosed
  have htiedFixed : tiedInstance.UnfoldingEquivalent
      (schema.instantiate
        (replaceArgument arguments x tiedInstance)) := by
    exact tieVariable_instance_fixedPoint hschema hx hargumentsClosed
  apply unaryLimit_unfoldingEquivalent_of_fixedPoint hcontext
    hnontrivial htiedClosed
  exact hfill.trans htiedFixed.symm

end RegularTerm

end DCFEquivalence
