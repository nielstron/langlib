module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GroundPreservation
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SufficientBasisReduction

@[expose]
public section

/-!
# Groundness preservation for first-order grammar steps

Runtime rule substitution has arbitrary finite arity.  This file extends the
unary graph-substitution result to an arbitrary tuple of ground arguments and
uses it to discharge `PreservesGroundSteps` from ordinary grammar
well-formedness.  Thus ground-step preservation is a theorem about the encoded
semantics, not an additional promise on grammar codes.
-/

namespace DCFEquivalence

namespace RegularTerm

private def HasRankArity (ranks : List ℕ) : RawNode → Prop
  | .inl _ => True
  | .inr (X, children) => ∃ rank, ranks[X]? = some rank ∧
      children.length = rank

private theorem hasRankArity_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound) :
    ∀ node ∈ term.nodes, HasRankArity ranks node := by
  intro node hnode
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hwell := (List.all_eq_true.mp hterm.2) node hnode
  cases node with
  | inl x => trivial
  | inr app =>
      rcases app with ⟨X, children⟩
      unfold nodeWellFormedCode at hwell
      cases hrank : ranks[X]? with
      | none => simp [hrank] at hwell
      | some rank =>
          simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hwell
          exact ⟨rank, hrank, hwell.1⟩

private theorem hasRankArity_of_shapeWellFormed
    {ranks : List ℕ} {term : RegularTerm}
    (hterm : term.ShapeWellFormed ranks) :
    ∀ node ∈ term.nodes, HasRankArity ranks node := by
  intro node hnode
  unfold ShapeWellFormed shapeWellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hwell := (List.all_eq_true.mp hterm.2) node hnode
  cases node with
  | inl x => trivial
  | inr app =>
      rcases app with ⟨X, children⟩
      unfold nodeShapeWellFormedCode at hwell
      cases hrank : ranks[X]? with
      | none => simp [hrank] at hwell
      | some rank =>
          simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hwell
          exact ⟨rank, hrank, hwell.1⟩

private theorem hasRankArity_shiftNode
    {ranks : List ℕ} {offset : ℕ} {node : RawNode}
    (hnode : HasRankArity ranks node) :
    HasRankArity ranks (shiftNode offset node) := by
  cases node with
  | inl x => trivial
  | inr app =>
      rcases app with ⟨X, children⟩
      rcases hnode with ⟨rank, hrank, hlength⟩
      exact ⟨rank, hrank, by simpa [shiftNode] using hlength⟩

private theorem appendArguments_hasRankArity
    {ranks : List ℕ} {arguments : List RegularTerm}
    (harguments : ∀ argument ∈ arguments,
      argument.ShapeWellFormed ranks) (offset : ℕ) :
    ∀ node ∈ appendArguments offset arguments,
      HasRankArity ranks node := by
  induction arguments generalizing offset with
  | nil => simp [appendArguments]
  | cons argument arguments ih =>
      rw [appendArguments_cons]
      intro node hnode
      rw [List.mem_append] at hnode
      rcases hnode with hhead | htail
      · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hhead
        apply hasRankArity_shiftNode
        exact hasRankArity_of_shapeWellFormed
          (harguments argument (by simp)) source hsource
      · exact ih (fun term hterm => harguments term (by simp [hterm]))
          (offset + argument.nodes.length) node htail

private theorem instantiate_hasRankArity
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ShapeWellFormed ranks) :
    ∀ node ∈ (schema.instantiate arguments).nodes,
      HasRankArity ranks node := by
  intro node hnode
  unfold instantiate nodes at hnode
  rw [List.mem_append] at hnode
  rcases hnode with hschemaNode | hargumentNode
  · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hschemaNode
    cases source with
    | inl x => trivial
    | inr app =>
        rcases app with ⟨X, children⟩
        obtain ⟨rank, hrank, hlength⟩ :=
          hasRankArity_of_wellFormed hschema _ hsource
        exact ⟨rank, hrank, by simpa [instantiateNode] using hlength⟩
  · exact appendArguments_hasRankArity harguments schema.nodes.length
      node hargumentNode

private theorem shapeWellFormed_of_referenceClosed_hasRankArity
    {ranks : List ℕ} {term : RegularTerm}
    (hclosed : term.ReferenceClosed)
    (hranked : ∀ node ∈ term.nodes, HasRankArity ranks node) :
    term.ShapeWellFormed ranks := by
  unfold ShapeWellFormed shapeWellFormedCode
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true hclosed.1, ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  cases node with
  | inl x => rfl
  | inr app =>
      rcases app with ⟨X, children⟩
      obtain ⟨rank, hrank, hlength⟩ := hranked _ hnode
      unfold nodeShapeWellFormedCode
      simp only [hrank, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hlength, ?_⟩
      apply List.all_eq_true.mpr
      intro child hchild
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hnode
      apply decide_eq_true
      apply hclosed.2 i X children
      · unfold nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hi, hget⟩
      · exact hchild

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

/-- Simultaneous substitution of any finite tuple of ground graphs into a
well-formed schema yields a ground graph. -/
public theorem instantiate_ground
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments, argument.Ground ranks) :
    (schema.instantiate arguments).Ground ranks := by
  classical
  let supportFor : RegularTerm → List ℕ := fun argument =>
    if hmem : argument ∈ arguments then
      Classical.choose (harguments argument hmem).2
    else []
  have supportFor_spec (argument : RegularTerm)
      (hmem : argument ∈ arguments) :
      supportFor argument ∈ (List.range argument.nodes.length).sublists' ∧
        argument.GroundWitness (supportFor argument) := by
    dsimp [supportFor]
    split
    · exact Classical.choose_spec (harguments argument hmem).2
    · contradiction
  let result := schema.instantiate arguments
  let Supported : ℕ → Prop := fun i =>
    (i < schema.nodes.length ∧
      ∃ X children, result.nodeAt? i = some (.inr (X, children))) ∨
    ∃ x argument j,
      arguments[x]? = some argument ∧
      j ∈ supportFor argument ∧
      i = argumentOffset schema.nodes.length arguments x + j
  let support := (List.range result.nodes.length).filter Supported
  have hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed := fun argument hmem =>
    referenceClosed_of_ground (harguments argument hmem)
  have hresultClosed : result.ReferenceClosed := by
    dsimp [result]
    exact instantiate_referenceClosed
      (referenceClosed_of_wellFormed hschema) hargumentsClosed
  have hresultShape : result.ShapeWellFormed ranks := by
    apply shapeWellFormed_of_referenceClosed_hasRankArity hresultClosed
    dsimp [result]
    apply instantiate_hasRankArity hschema
    exact fun argument hmem => (harguments argument hmem).1
  have resolve_supported {i : ℕ} (hi : i < schema.nodes.length) :
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
        have hx : x < arguments.length :=
          variable_lt_of_wellFormed hschema hvariable
        let argument : RegularTerm := arguments[x]
        have hargument : arguments[x]? = some argument := by
          unfold argument
          rw [List.getElem?_eq_some_iff]
          exact ⟨hx, rfl⟩
        have hargumentMem : argument ∈ arguments :=
          List.mem_of_getElem? hargument
        have hwitness := (supportFor_spec argument hargumentMem).2
        right
        refine ⟨x, argument, argument.root, hargument, hwitness.1, ?_⟩
        simp [resolveRHSRef, hvariable, argumentRoot?, hargument]
    | inr app =>
        rcases app with ⟨X, children⟩
        have happlication : schema.nodeAt? i =
            some (.inr (X, children)) := by
          simpa [hkind] using hsource
        have hresolve : schema.resolveRHSRef arguments i = i := by
          simp [resolveRHSRef, happlication]
        left
        refine ⟨by simpa [hresolve] using hi, X,
          children.map (schema.resolveRHSRef arguments), ?_⟩
        rw [hresolve]
        dsimp [result]
        rw [instantiate_nodeAt?_rhs schema arguments hi, happlication]
        rfl
  have hsupportSublist : List.Sublist support
      (List.range result.nodes.length) := by
    exact List.filter_sublist
  refine ⟨hresultShape, support,
    List.mem_sublists'.mpr hsupportSublist, ?_⟩
  constructor
  · apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hresultClosed.1, ?_⟩
    apply decide_eq_true
    change Supported (schema.resolveRHSRef arguments schema.root)
    exact resolve_supported (referenceClosed_of_wellFormed hschema).1
  · intro i hi
    have hiSupported : Supported i :=
      of_decide_eq_true (List.mem_filter.mp hi).2
    rcases hiSupported with hprefix | hsuffix
    · obtain ⟨hiPrefix, Y, sourceChildren, hiNode⟩ := hprefix
      dsimp [result] at hiNode
      rw [instantiate_nodeAt?_rhs schema arguments hiPrefix] at hiNode
      cases hsource : schema.nodeAt? i with
      | none => simp [hsource] at hiNode
      | some source =>
          rw [hsource] at hiNode
          cases source with
          | inl x => simp [instantiateNode] at hiNode
          | inr app =>
              rcases app with ⟨sourceX, children⟩
              simp only [Option.map_some, instantiateNode,
                Option.some.injEq,
                Sum.inr.injEq, Prod.mk.injEq] at hiNode
              rcases hiNode with ⟨rfl, rfl⟩
              have hresultNode : result.nodeAt? i = some (.inr
                  (sourceX,
                    children.map (schema.resolveRHSRef arguments))) := by
                dsimp [result]
                rw [instantiate_nodeAt?_rhs schema arguments hiPrefix,
                  hsource]
                rfl
              refine ⟨sourceX,
                children.map (schema.resolveRHSRef arguments),
                hresultNode, ?_⟩
              intro child hchild
              obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
                List.mem_map.mp hchild
              apply List.mem_filter.mpr
              refine ⟨List.mem_range.mpr
                (hresultClosed.2 i sourceX
                  (children.map (schema.resolveRHSRef arguments)) hresultNode
                  _ (List.mem_map.mpr
                    ⟨sourceChild, hsourceChild, rfl⟩)), ?_⟩
              exact decide_eq_true (resolve_supported
                ((referenceClosed_of_wellFormed hschema).2 i sourceX
                  children hsource sourceChild hsourceChild))
    · obtain ⟨x, argument, j, hargument, hj, rfl⟩ := hsuffix
      have hargumentMem : argument ∈ arguments :=
        List.mem_of_getElem? hargument
      have hwitness := (supportFor_spec argument hargumentMem).2
      obtain ⟨Y, sourceChildren, hsourceNode, hsourceChildren⟩ :=
        hwitness.2 j hj
      have hcopied := instantiate_nodeAt?_argument schema arguments
        hargument hsourceNode
      refine ⟨Y,
        sourceChildren.map
          (argumentOffset schema.nodes.length arguments x + ·), ?_, ?_⟩
      · simpa [shiftNode] using hcopied
      · intro child hchild
        obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
          List.mem_map.mp hchild
        apply List.mem_filter.mpr
        refine ⟨List.mem_range.mpr ?_, ?_⟩
        · apply hresultClosed.2
            (argumentOffset schema.nodes.length arguments x + j)
            Y
            (sourceChildren.map
              (argumentOffset schema.nodes.length arguments x + ·))
          · simpa [shiftNode] using hcopied
          · exact List.mem_map.mpr
              ⟨sourceChild, hsourceChild, rfl⟩
        · exact decide_eq_true (Or.inr
            ⟨x, argument, sourceChild, hargument,
              hsourceChildren sourceChild hsourceChild, rfl⟩)

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

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
  have hrow := (List.all_eq_true.mp hg.1) rule (findRule_mem hfind)
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

private theorem nodeAt_root_of_rootApplication?
    {term : RegularTerm} {X : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (X, children)) :
    term.nodeAt? term.root = some (.inr (X, children)) := by
  unfold RegularTerm.rootApplication? RegularTerm.rootNode? at hroot
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

private theorem Ground.withRoot_child
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks)
    {X : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (X, children))
    {child : ℕ} (hchild : child ∈ children) :
    (term.withRoot child).Ground ranks := by
  obtain ⟨hshape, support, hsupport, hwitness⟩ := hground
  have hrootNode := nodeAt_root_of_rootApplication? hroot
  obtain ⟨Y, rootChildren, hwitnessRoot, hchildren⟩ :=
    hwitness.2 term.root hwitness.1
  have happ : (Y, rootChildren) = (X, children) :=
    Sum.inr.inj (Option.some.inj (hwitnessRoot.symm.trans hrootNode))
  have hchildrenEq : rootChildren = children := congrArg Prod.snd happ
  subst rootChildren
  have hchildSupport := hchildren child hchild
  obtain ⟨childX, childChildren, hchildNode, _⟩ :=
    hwitness.2 child hchildSupport
  refine ⟨?_, support, ?_, ?_⟩
  · unfold RegularTerm.ShapeWellFormed
      RegularTerm.shapeWellFormedCode at hshape ⊢
    rw [Bool.and_eq_true] at hshape ⊢
    refine ⟨?_, ?_⟩
    · exact decide_eq_true (List.getElem?_eq_some_iff.mp hchildNode).1
    · simpa [RegularTerm.withRoot, RegularTerm.nodes] using hshape.2
  · simpa [RegularTerm.withRoot, RegularTerm.nodes] using hsupport
  · refine ⟨?_, ?_⟩
    · simpa [RegularTerm.withRoot, RegularTerm.root] using hchildSupport
    · intro i hi
      simpa [RegularTerm.withRoot, RegularTerm.nodeAt?,
        RegularTerm.nodes] using hwitness.2 i hi

private theorem root_rank_arity_of_ground
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks)
    {X : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (X, children)) :
    ∃ rank, ranks[X]? = some rank ∧ children.length = rank := by
  have hnode := nodeAt_root_of_rootApplication? hroot
  have hshape := hground.1
  unfold RegularTerm.ShapeWellFormed
    RegularTerm.shapeWellFormedCode at hshape
  rw [Bool.and_eq_true] at hshape
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hnodeShape := (List.all_eq_true.mp hshape.2) _ hmem
  unfold RegularTerm.nodeShapeWellFormedCode at hnodeShape
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hnodeShape
  | some rank =>
      simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hnodeShape
      exact ⟨rank, rfl, hnodeShape.1⟩

/-- Every step of a well-formed encoded first-order grammar preserves runtime
groundness. -/
public theorem preservesGroundSteps_of_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed) :
    g.PreservesGroundSteps := by
  intro label source target hsource hstep
  cases label with
  | inl action =>
      unfold step? rootRewrite? at hstep
      cases hroot : source.rootApplication? with
      | none => simp [hroot] at hstep
      | some app =>
          rcases app with ⟨X, children⟩
          simp only [hroot] at hstep
          obtain ⟨rhs, hrule, htarget⟩ := Option.map_eq_some_iff.mp hstep
          subst target
          obtain ⟨ruleRank, hruleRank, hrhs⟩ :=
            selected_rhs_wellFormed hg hrule
          obtain ⟨sourceRank, hsourceRank, hchildrenLength⟩ :=
            root_rank_arity_of_ground hsource hroot
          have hranks : ruleRank = sourceRank :=
            Option.some.inj (hruleRank.symm.trans hsourceRank)
          have hrhsArity : rhs.WellFormed g.ranks
              (children.map source.withRoot).length := by
            simpa [hchildrenLength, hranks] using hrhs
          apply RegularTerm.instantiate_ground hrhsArity
          intro argument hargument
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
          exact Ground.withRoot_child hsource hroot hchild
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

end EncodedFirstOrderGrammar

end DCFEquivalence
