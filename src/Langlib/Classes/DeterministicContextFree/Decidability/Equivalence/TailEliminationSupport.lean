module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationRuns

@[expose]
public section

/-!
# Reachable active-prefix support under tail elimination

`SupportedByPrefix` is extensional: it says that changing inactive arguments
does not change the denoted regular tree.  Tail elimination needs a finite
structural witness that is stable under graph substitution and parametric
tying.  The witness below records exactly the nodes reachable from the chosen
root that matter for this purpose.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- A finite reachable support whose variable nodes all lie in the active
argument prefix. -/
@[expose] public def PrefixWitness
    (term : RegularTerm) (width : ℕ) (support : List ℕ) : Prop :=
  term.root ∈ support ∧
    ∀ i ∈ support,
      (∃ x, term.nodeAt? i = some (.inl x) ∧ x < width) ∨
      ∃ X children,
        term.nodeAt? i = some (.inr (X, children)) ∧
          ∀ child ∈ children, child ∈ support

/-- A regular graph is structurally supported by its first `width`
parameters when it admits a finite reachable prefix witness. -/
@[expose] public def HasPrefixWitness
    (term : RegularTerm) (width : ℕ) : Prop :=
  ∃ support, term.PrefixWitness width support

public theorem PrefixWitness.node_lt
    {term : RegularTerm} {width : ℕ} {support : List ℕ}
    (hwitness : term.PrefixWitness width support)
    {i : ℕ} (hi : i ∈ support) :
    i < term.nodes.length := by
  rcases hwitness.2 i hi with hvariable | happlication
  · obtain ⟨x, hnode, _⟩ := hvariable
    exact (List.getElem?_eq_some_iff.mp hnode).1
  · obtain ⟨X, children, hnode, _⟩ := happlication
    exact (List.getElem?_eq_some_iff.mp hnode).1

/-- A single variable is supported exactly when its index is active. -/
public theorem variableTerm_hasPrefixWitness
    {x width : ℕ} (hx : x < width) :
    (variableTerm x).HasPrefixWitness width := by
  refine ⟨[0], ?_⟩
  constructor
  · simp [variableTerm, root]
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    left
    exact ⟨x, by simpa [rootNode?] using variableTerm_rootNode? x, hx⟩

/-- Global structural well-formedness supplies a prefix witness at the full
declared variable bound. -/
public theorem WellFormed.hasPrefixWitness
    {term : RegularTerm} {ranks : List ℕ} {width : ℕ}
    (hterm : term.WellFormed ranks width) :
    term.HasPrefixWitness width := by
  let support := List.range term.nodes.length
  have hwell := hterm
  unfold WellFormed wellFormedCode at hwell
  rw [Bool.and_eq_true] at hwell
  refine ⟨support, ?_⟩
  constructor
  · exact List.mem_range.mpr (of_decide_eq_true hwell.1)
  · intro i hi
    have hiBound : i < term.nodes.length := by
      simpa [support] using hi
    cases hnode : term.nodeAt? i with
    | none =>
        have : term.nodeAt? i ≠ none := by
          unfold nodeAt?
          simp [hiBound]
        contradiction
    | some node =>
        have hlocal := (List.all_eq_true.mp hwell.2) node
          (List.mem_of_getElem? hnode)
        cases node with
        | inl x =>
            left
            exact ⟨x, rfl,
              by simpa [nodeWellFormedCode] using
                of_decide_eq_true hlocal⟩
        | inr application =>
            rcases application with ⟨X, children⟩
            cases hrank : ranks[X]? with
            | none => simp [nodeWellFormedCode, hrank] at hlocal
            | some rank =>
                simp only [nodeWellFormedCode, hrank,
                  Bool.and_eq_true] at hlocal
                right
                refine ⟨X, children, rfl, ?_⟩
                intro child hchild
                have hchildBound :=
                  (List.all_eq_true.mp hlocal.2) child hchild
                exact List.mem_range.mpr
                  (of_decide_eq_true hchildBound)

/-- A variable root denotes the corresponding variable tree. -/
public theorem unfoldingEquivalent_variableTerm_of_rootNode
    {term : RegularTerm} {x : ℕ}
    (hroot : term.rootNode? = some (.inl x)) :
    term.UnfoldingEquivalent (variableTerm x) := by
  let R : ℕ → ℕ → Prop := fun i j =>
    i = term.root ∧ j = (variableTerm x).root
  refine ⟨R, ⟨rfl, rfl⟩, ?_⟩
  intro i j hij
  rcases hij with ⟨rfl, rfl⟩
  change RawCompatible R term.rootNode? (variableTerm x).rootNode?
  rw [hroot, variableTerm_rootNode?]
  simp [RawCompatible]

/-- Tying the last active variable makes every occurrence of that variable
recursive.  Removing the old variable nodes from the support leaves a witness
for the shorter active prefix. -/
public theorem PrefixWitness.tieVariable_last
    {term : RegularTerm} {width : ℕ} {support : List ℕ}
    (hwitness : term.PrefixWitness width support)
    (hwidth : 0 < width)
    (hroot : term.rootNode? ≠ some (.inl (width - 1))) :
    (term.tieVariable (width - 1)).HasPrefixWitness (width - 1) := by
  classical
  let x := width - 1
  let kept : ℕ → Prop := fun i =>
    term.nodeAt? i ≠ some (.inl x)
  let tiedSupport := support.filter kept
  have hx : x < width := by
    dsimp [x]
    omega
  have hrootKept : kept term.root := by
    simpa [kept, x, rootNode?] using hroot
  have hrootMem : term.root ∈ tiedSupport := by
    apply List.mem_filter.mpr
    exact ⟨hwitness.1, decide_eq_true hrootKept⟩
  have tieReference_mem
      {child : ℕ} (hchild : child ∈ support) :
      term.tieReference x child ∈ tiedSupport := by
    rcases hwitness.2 child hchild with hvariable | happlication
    · obtain ⟨y, hnode, hy⟩ := hvariable
      by_cases hyx : y = x
      · subst y
        simpa [tieReference, hnode] using hrootMem
      · apply List.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · simpa [tieReference, hnode, hyx] using hchild
        · apply decide_eq_true
          simp [kept, tieReference, hnode, hyx]
    · obtain ⟨X, children, hnode, hchildren⟩ := happlication
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simpa [tieReference, hnode] using hchild
      · apply decide_eq_true
        simp [kept, tieReference, hnode]
  refine ⟨tiedSupport, ?_⟩
  constructor
  · simpa using hrootMem
  · intro i hi
    have hiFilter := List.mem_filter.mp hi
    have hiSupport : i ∈ support := hiFilter.1
    have hiKept : kept i := of_decide_eq_true hiFilter.2
    rcases hwitness.2 i hiSupport with hvariable | happlication
    · obtain ⟨y, hnode, hy⟩ := hvariable
      have hyx : y ≠ x := by
        intro heq
        subst y
        exact hiKept hnode
      left
      refine ⟨y, ?_, ?_⟩
      · rw [tieVariable_nodeAt?, hnode]
        rfl
      · dsimp [x] at hyx
        omega
    · obtain ⟨X, children, hnode, hchildren⟩ := happlication
      right
      refine ⟨X, children.map (term.tieReference x), ?_, ?_⟩
      · rw [tieVariable_nodeAt?, hnode]
        rfl
      · intro child hchild
        obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hchild
        exact tieReference_mem (hchildren source hsource)

/-- Simultaneous substitution preserves reachable prefix support when every
argument actually reached through the schema support has the requested target
support.  Inactive raw arguments may be arbitrary. -/
public theorem PrefixWitness.instantiate
    {schema : RegularTerm} {sourceWidth targetWidth : ℕ}
    {schemaSupport : List ℕ} {arguments : List RegularTerm}
    (hschema : schema.PrefixWitness sourceWidth schemaSupport)
    (hschemaClosed : schema.ReferenceClosed)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed)
    (harguments :
      ∀ x, x < sourceWidth →
        ∃ argument,
          arguments[x]? = some argument ∧
            argument.HasPrefixWitness targetWidth) :
    (schema.instantiate arguments).HasPrefixWitness targetWidth := by
  classical
  let supportFor : RegularTerm → List ℕ := fun argument =>
    if h : argument.HasPrefixWitness targetWidth then
      Classical.choose h
    else []
  have supportFor_spec (argument : RegularTerm)
      (hwitness : argument.HasPrefixWitness targetWidth) :
      argument.PrefixWitness targetWidth (supportFor argument) := by
    dsimp [supportFor]
    split
    · exact Classical.choose_spec hwitness
    · contradiction
  let result := schema.instantiate arguments
  let Supported : ℕ → Prop := fun i =>
    (i ∈ schemaSupport ∧
      ∃ X children,
        result.nodeAt? i = some (.inr (X, children))) ∨
    ∃ x argument j,
      x < sourceWidth ∧
      arguments[x]? = some argument ∧
      argument.HasPrefixWitness targetWidth ∧
      j ∈ supportFor argument ∧
      i = argumentOffset schema.nodes.length arguments x + j
  let resultSupport :=
    (List.range result.nodes.length).filter Supported
  have hresultClosed : result.ReferenceClosed := by
    dsimp [result]
    exact instantiate_referenceClosed hschemaClosed hargumentsClosed
  have mem_resultSupport_of_supported {i : ℕ}
      (hi : i < result.nodes.length)
      (hsupported : Supported i) :
      i ∈ resultSupport := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr hi, decide_eq_true hsupported⟩
  have resolve_supported {i : ℕ}
      (hi : i ∈ schemaSupport) :
      Supported (schema.resolveRHSRef arguments i) := by
    rcases hschema.2 i hi with hvariable | happlication
    · obtain ⟨x, hnode, hx⟩ := hvariable
      obtain ⟨argument, hargument, hargumentWitness⟩ :=
        harguments x hx
      have hwitness := supportFor_spec argument hargumentWitness
      right
      refine ⟨x, argument, argument.root, hx, hargument,
        hargumentWitness, hwitness.1, ?_⟩
      simp [resolveRHSRef, hnode, argumentRoot?, hargument]
    · obtain ⟨X, children, hnode, hchildren⟩ := happlication
      have hresolve :
          schema.resolveRHSRef arguments i = i := by
        simp [resolveRHSRef, hnode]
      rw [hresolve]
      left
      refine ⟨hi, X,
        children.map (schema.resolveRHSRef arguments), ?_⟩
      dsimp [result]
      rw [instantiate_nodeAt?_rhs schema arguments
        (hschema.node_lt hi), hnode]
      rfl
  refine ⟨resultSupport, ?_⟩
  constructor
  · change schema.resolveRHSRef arguments schema.root ∈ resultSupport
    apply mem_resultSupport_of_supported hresultClosed.1
    exact resolve_supported hschema.1
  · intro i hi
    have hiFilter : Supported i :=
      of_decide_eq_true (List.mem_filter.mp hi).2
    rcases hiFilter with hprefix | hsuffix
    · obtain ⟨hiSchema, X, children, hnode⟩ := hprefix
      right
      refine ⟨X, children, hnode, ?_⟩
      rw [show result = schema.instantiate arguments by rfl,
        instantiate_nodeAt?_rhs schema arguments
          (hschema.node_lt hiSchema)] at hnode
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
              rcases hnode with ⟨hYX, hchildrenEq⟩
              subst Y
              subst children
              intro child hchild
              obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
                List.mem_map.mp hchild
              apply mem_resultSupport_of_supported
              · exact hresultClosed.2 i X
                  (sourceChildren.map
                    (schema.resolveRHSRef arguments))
                  (by
                    dsimp [result]
                    rw [instantiate_nodeAt?_rhs
                      schema arguments
                      (hschema.node_lt hiSchema), hsource]
                    rfl)
                  (schema.resolveRHSRef arguments sourceChild)
                  (List.mem_map.mpr
                    ⟨sourceChild, hsourceChild, rfl⟩)
              · rcases hschema.2 i hiSchema with
                  hvariable | happlication
                · obtain ⟨x, hvariableNode, _⟩ := hvariable
                  simp [hsource] at hvariableNode
                · obtain ⟨Z, witnessChildren, hwitnessNode,
                      hwitnessChildren⟩ := happlication
                  rw [hsource] at hwitnessNode
                  simp only [Option.some.injEq, Sum.inr.injEq,
                    Prod.mk.injEq] at hwitnessNode
                  rcases hwitnessNode with ⟨rfl, rfl⟩
                  exact resolve_supported
                    (hwitnessChildren sourceChild hsourceChild)
    · obtain ⟨x, argument, j, hx, hargument,
          hargumentWitness, hjSupport, rfl⟩ := hsuffix
      have hwitness := supportFor_spec argument hargumentWitness
      rcases hwitness.2 j hjSupport with hvariable | happlication
      · obtain ⟨y, hnode, hy⟩ := hvariable
        left
        refine ⟨y, ?_, hy⟩
        simpa [result, shiftNode] using
          instantiate_nodeAt?_argument schema arguments
            hargument hnode
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
          apply mem_resultSupport_of_supported
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
            exact ⟨x, argument, argumentChild, hx, hargument,
              hargumentWitness,
              hargumentChildren argumentChild hargumentChild, rfl⟩

private theorem swapIndex_lt_prefix
    {width x y i : ℕ}
    (hx : x < width) (hy : y < width) (hi : i < width) :
    Equiv.swap x y i < width := by
  rw [Equiv.swap_apply_def]
  split
  · exact hy
  · split
    · exact hx
    · exact hi

/-- Reindexing two active parameters preserves the structural prefix
witness. -/
public theorem HasPrefixWitness.swapParameters
    {schema : RegularTerm} {arity width x y : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hschemaClosed : schema.ReferenceClosed)
    (hwidthArity : width ≤ arity)
    (hx : x < width) (hy : y < width) :
    (RegularTerm.swapParameters schema arity x y)
      |>.HasPrefixWitness width := by
  obtain ⟨support, hsupport⟩ := hwitness
  unfold RegularTerm.swapParameters
  apply hsupport.instantiate hschemaClosed
    (swapIdentityArguments_referenceClosed
      (hx.trans_le hwidthArity) (hy.trans_le hwidthArity))
  intro i hi
  have hiArity : i < arity := hi.trans_le hwidthArity
  let target := Equiv.swap x y i
  refine ⟨variableTerm target, ?_, ?_⟩
  · simpa [target] using swapIdentityArguments_getElem?
      (hx.trans_le hwidthArity) (hy.trans_le hwidthArity) hiArity
  · exact variableTerm_hasPrefixWitness
      (swapIndex_lt_prefix hx hy hi)

public theorem HasPrefixWitness.moveParameterToActiveLast
    {schema : RegularTerm} {arity width x : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hschemaClosed : schema.ReferenceClosed)
    (hwidthArity : width ≤ arity)
    (hwidth : 0 < width) (hx : x < width) :
    (schema.moveParameterToActiveLast arity width x)
      |>.HasPrefixWitness width := by
  exact hwitness.swapParameters hschemaClosed hwidthArity hx (by omega)

/-- One ordinary grammar rewrite preserves the reachable active-prefix
witness. -/
public theorem HasPrefixWitness.stepAction
    {Action : Type} [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {arity width : ℕ} {action : Action}
    (hwitness : source.HasPrefixWitness width)
    (hsourceWellFormed : source.WellFormed g.ranks arity)
    (hstep : g.step? (.inl action) source = some target) :
    target.HasPrefixWitness width := by
  change g.rootRewrite? action source = some target at hstep
  unfold EncodedFirstOrderGrammar.rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ := Option.map_eq_some_iff.mp hstep
      subst target
      have hrootNode := nodeAt?_root_of_rootApplication? hroot
      obtain ⟨rank, hrank, hrhsWellFormed⟩ :=
        g.selected_rhs_wellFormed hg hrule
      obtain ⟨sourceRank, hsourceRank, hchildrenLength⟩ :=
        EncodedFirstOrderGrammar.rank_arity_of_wellFormed
          hsourceWellFormed hrootNode
      have hranksEqual : sourceRank = rank := by
        rw [hsourceRank] at hrank
        exact Option.some.inj hrank
      obtain ⟨support, hsourceWitness⟩ := hwitness
      have hchildren : ∀ child ∈ children, child ∈ support := by
        rcases hsourceWitness.2 source.root hsourceWitness.1 with
          hvariable | happlication
        · obtain ⟨x, hnode, _⟩ := hvariable
          rw [hrootNode] at hnode
          simp at hnode
        · obtain ⟨Y, witnessChildren, hnode,
              hwitnessChildren⟩ := happlication
          rw [hrootNode] at hnode
          simp only [Option.some.injEq, Sum.inr.injEq,
            Prod.mk.injEq] at hnode
          rcases hnode with ⟨rfl, rfl⟩
          exact hwitnessChildren
      have hsourceClosed := referenceClosed_of_wellFormed hsourceWellFormed
      have hargumentsClosed : ∀ argument ∈ children.map source.withRoot,
          argument.ReferenceClosed := by
        intro argument hargument
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
        exact withRoot_referenceClosed hsourceClosed
          (hsourceClosed.2 source.root X children hrootNode child hchild)
      obtain ⟨rhsSupport, hrhsWitness⟩ :=
        hrhsWellFormed.hasPrefixWitness
      apply hrhsWitness.instantiate
        (referenceClosed_of_wellFormed hrhsWellFormed)
        hargumentsClosed
      intro i hi
      have hiChildren : i < children.length := by
        rw [hchildrenLength, hranksEqual]
        exact hi
      let child := children[i]
      refine ⟨source.withRoot child, ?_, ?_⟩
      · simp [child, List.getElem?_map,
          List.getElem?_eq_getElem hiChildren]
      · refine ⟨support, ?_⟩
        constructor
        · exact hchildren child (List.getElem_mem hiChildren)
        · intro j hj
          simpa [RegularTerm.withRoot, RegularTerm.nodeAt?,
            RegularTerm.nodes] using hsourceWitness.2 j hj

/-- Finite ordinary execution preserves a reachable prefix witness. -/
public theorem HasPrefixWitness.runActions
    {Action : Type} [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema residual : RegularTerm} {arity width : ℕ}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hwitness : schema.HasPrefixWitness width)
    (hschemaWellFormed : schema.WellFormed g.ranks arity)
    {word : List Action}
    (hrun : g.runActions? word schema = some residual) :
    residual.HasPrefixWitness width := by
  induction word generalizing schema with
  | nil =>
      simp [EncodedFirstOrderGrammar.runActions?] at hrun
      subst residual
      exact hwitness
  | cons action word ih =>
      cases hstep : g.step? (.inl action) schema with
      | none =>
          simp [EncodedFirstOrderGrammar.runActions?, hstep] at hrun
      | some next =>
          have htail : g.runActions? word next = some residual := by
            simpa [EncodedFirstOrderGrammar.runActions?, hstep] using hrun
          have hnextWellFormed := g.stepAction_some_wellFormed_padded
            hg hpadding hschemaWellFormed hstep
          exact ih (hwitness.stepAction hg hschemaWellFormed hstep)
            hnextWellFormed htail

/-- Bisimulation relation for two instantiations which only follows schema
nodes in the finite prefix support and argument copies reached through active
variables. -/
@[expose] public def PrefixInstantiationRelation
    (schema : RegularTerm) (support : List ℕ) (width : ℕ)
    (leftArguments rightArguments : List RegularTerm)
    (i j : ℕ) : Prop :=
  (∃ source X children,
      source ∈ support ∧
      schema.nodeAt? source = some (.inr (X, children)) ∧
      i = source ∧ j = source) ∨
  ∃ x leftArgument rightArgument leftIndex rightIndex,
    x < width ∧
    leftArguments[x]? = some leftArgument ∧
    rightArguments[x]? = some rightArgument ∧
    leftIndex < leftArgument.nodes.length ∧
    rightIndex < rightArgument.nodes.length ∧
    leftArgument.BisimilarAt leftIndex rightArgument rightIndex ∧
    i = argumentOffset schema.nodes.length leftArguments x + leftIndex ∧
    j = argumentOffset schema.nodes.length rightArguments x + rightIndex

private theorem forall₂_map_same_prefix
    {R : ℕ → ℕ → Prop} (left right : ℕ → ℕ)
    (values : List ℕ)
    (h : ∀ value ∈ values, R (left value) (right value)) :
    List.Forall₂ R (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun child hchild => h child (by simp [hchild]))

private theorem forall₂_map_both_prefix
    {R S : ℕ → ℕ → Prop} {left right : List ℕ}
    (f g : ℕ → ℕ) (h : List.Forall₂ R left right)
    (hmap : ∀ i j, R i j → S (f i) (g j)) :
    List.Forall₂ S (left.map f) (right.map g) := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      exact .cons (hmap _ _ hhead) ih

private theorem forall₂_restrict_prefix
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop}
    {left right : List ℕ} (h : List.Forall₂ R left right)
    (hleft : ∀ i ∈ left, P i)
    (hright : ∀ j ∈ right, Q j) :
    List.Forall₂ (fun i j => R i j ∧ P i ∧ Q j) left right := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      refine .cons
        ⟨hhead, hleft _ (by simp), hright _ (by simp)⟩ ?_
      exact ih
        (fun i hi => hleft i (by simp [hi]))
        (fun j hj => hright j (by simp [hj]))

private theorem PrefixWitness.resolve_prefixInstantiationRelation
    {schema : RegularTerm} {support : List ℕ} {width : ℕ}
    {leftArguments rightArguments : List RegularTerm}
    (hwitness : schema.PrefixWitness width support)
    (hleftClosed :
      ∀ argument ∈ leftArguments, argument.ReferenceClosed)
    (hrightClosed :
      ∀ argument ∈ rightArguments, argument.ReferenceClosed)
    (harguments : ArgumentsEquivalentThrough width
      leftArguments rightArguments)
    {i : ℕ} (hi : i ∈ support) :
    PrefixInstantiationRelation schema support width
      leftArguments rightArguments
      (schema.resolveRHSRef leftArguments i)
      (schema.resolveRHSRef rightArguments i) := by
  rcases hwitness.2 i hi with hvariable | happlication
  · obtain ⟨x, hnode, hx⟩ := hvariable
    obtain ⟨leftArgument, rightArgument,
        hleftArgument, hrightArgument, hequivalent⟩ :=
      harguments x hx
    have hleftMem : leftArgument ∈ leftArguments :=
      List.mem_of_getElem? hleftArgument
    have hrightMem : rightArgument ∈ rightArguments :=
      List.mem_of_getElem? hrightArgument
    right
    refine ⟨x, leftArgument, rightArgument,
      leftArgument.root, rightArgument.root, hx,
      hleftArgument, hrightArgument,
      (hleftClosed leftArgument hleftMem).1,
      (hrightClosed rightArgument hrightMem).1,
      hequivalent, ?_, ?_⟩
    · simp [resolveRHSRef, hnode, argumentRoot?, hleftArgument]
    · simp [resolveRHSRef, hnode, argumentRoot?, hrightArgument]
  · obtain ⟨X, children, hnode, hchildren⟩ := happlication
    left
    refine ⟨i, X, children, hi, hnode, ?_, ?_⟩
    · simp [resolveRHSRef, hnode]
    · simp [resolveRHSRef, hnode]

private theorem PrefixWitness.instantiationRelation_isBisimulation
    {schema : RegularTerm} {support : List ℕ} {width : ℕ}
    {leftArguments rightArguments : List RegularTerm}
    (hwitness : schema.PrefixWitness width support)
    (hleftClosed :
      ∀ argument ∈ leftArguments, argument.ReferenceClosed)
    (hrightClosed :
      ∀ argument ∈ rightArguments, argument.ReferenceClosed)
    (harguments : ArgumentsEquivalentThrough width
      leftArguments rightArguments) :
    (schema.instantiate leftArguments).IsBisimulation
      (schema.instantiate rightArguments)
      (PrefixInstantiationRelation schema support width
        leftArguments rightArguments) := by
  intro i j hij
  rcases hij with hschema | hargument
  · obtain ⟨source, X, children, hsourceSupport,
        hsourceNode, hisource, hjsource⟩ := hschema
    subst i
    subst j
    unfold NodeCompatible
    rw [instantiate_nodeAt?_rhs schema leftArguments
        (hwitness.node_lt hsourceSupport),
      instantiate_nodeAt?_rhs schema rightArguments
        (hwitness.node_lt hsourceSupport),
      hsourceNode]
    simp only [Option.map_some, instantiateNode, RawCompatible]
    refine ⟨trivial, forall₂_map_same_prefix
      (schema.resolveRHSRef leftArguments)
      (schema.resolveRHSRef rightArguments) children ?_⟩
    intro child hchild
    rcases hwitness.2 source hsourceSupport with
        hvariable | happlication
    · obtain ⟨x, hvariableNode, _⟩ := hvariable
      rw [hsourceNode] at hvariableNode
      simp at hvariableNode
    · obtain ⟨Y, witnessChildren, hwitnessNode,
          hwitnessChildren⟩ := happlication
      rw [hsourceNode] at hwitnessNode
      simp only [Option.some.injEq, Sum.inr.injEq,
        Prod.mk.injEq] at hwitnessNode
      rcases hwitnessNode with ⟨rfl, rfl⟩
      exact hwitness.resolve_prefixInstantiationRelation
        hleftClosed hrightClosed harguments
        (hwitnessChildren child hchild)
  · obtain ⟨x, leftArgument, rightArgument, leftIndex, rightIndex,
        hx, hleftArgument, hrightArgument, hleftBound, hrightBound,
        hequivalent, rfl, rfl⟩ := hargument
    have hleftMem : leftArgument ∈ leftArguments :=
      List.mem_of_getElem? hleftArgument
    have hrightMem : rightArgument ∈ rightArguments :=
      List.mem_of_getElem? hrightArgument
    have hleftReferenceClosed :=
      hleftClosed leftArgument hleftMem
    have hrightReferenceClosed :=
      hrightClosed rightArgument hrightMem
    let leftNode : RawNode := leftArgument.nodes[leftIndex]
    let rightNode : RawNode := rightArgument.nodes[rightIndex]
    have hleftNode : leftArgument.nodeAt? leftIndex =
        some leftNode := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hleftBound, rfl⟩
    have hrightNode : rightArgument.nodeAt? rightIndex =
        some rightNode := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hrightBound, rfl⟩
    obtain ⟨R, hindex, hR⟩ := hequivalent
    have hlocal := hR leftIndex rightIndex hindex
    unfold NodeCompatible at hlocal ⊢
    rw [hleftNode, hrightNode] at hlocal
    rw [instantiate_nodeAt?_argument schema leftArguments
        hleftArgument hleftNode,
      instantiate_nodeAt?_argument schema rightArguments
        hrightArgument hrightNode]
    cases hleftKind : leftNode with
    | inl leftVariable =>
        cases hrightKind : rightNode with
        | inl rightVariable =>
            simpa [hleftKind, hrightKind, shiftNode,
              RawCompatible] using hlocal
        | inr rightApp =>
            simp [hleftKind, hrightKind, RawCompatible] at hlocal
    | inr leftApp =>
        cases hrightKind : rightNode with
        | inl rightVariable =>
            simp [hleftKind, hrightKind, RawCompatible] at hlocal
        | inr rightApp =>
            rcases leftApp with ⟨X, leftChildren⟩
            rcases rightApp with ⟨Y, rightChildren⟩
            have hleftAppNode : leftArgument.nodeAt? leftIndex =
                some (.inr (X, leftChildren)) :=
              hleftNode.trans (congrArg some hleftKind)
            have hrightAppNode : rightArgument.nodeAt? rightIndex =
                some (.inr (Y, rightChildren)) :=
              hrightNode.trans (congrArg some hrightKind)
            simp only [hleftKind, hrightKind, RawCompatible] at hlocal
            simp only [shiftNode, RawCompatible]
            have hchildren : List.Forall₂
                (fun leftChild rightChild =>
                  R leftChild rightChild ∧
                    leftChild < leftArgument.nodes.length ∧
                    rightChild < rightArgument.nodes.length)
                leftChildren rightChildren :=
              forall₂_restrict_prefix hlocal.2
                (fun child hchild =>
                  hleftReferenceClosed.2 leftIndex X leftChildren
                    hleftAppNode child hchild)
                (fun child hchild =>
                  hrightReferenceClosed.2 rightIndex Y rightChildren
                    hrightAppNode child hchild)
            refine ⟨hlocal.1, forall₂_map_both_prefix
              (argumentOffset schema.nodes.length leftArguments x + ·)
              (argumentOffset schema.nodes.length rightArguments x + ·)
              hchildren ?_⟩
            intro leftChild rightChild hchildren
            right
            exact ⟨x, leftArgument, rightArgument,
              leftChild, rightChild, hx,
              hleftArgument, hrightArgument,
              hchildren.2.1, hchildren.2.2,
              ⟨R, hchildren.1, hR⟩, rfl, rfl⟩

/-- A reachable prefix witness makes instantiation insensitive to argument
tuple length and contents beyond the witnessed prefix.  Unlike
`SupportedByPrefix`, this form does not require both tuples to have one
predeclared arity, so it can justify appending inactive padding arguments. -/
public theorem PrefixWitness.instantiate_unfoldingEquivalent_of_prefix
    {schema : RegularTerm} {support : List ℕ} {width : ℕ}
    {leftArguments rightArguments : List RegularTerm}
    (hwitness : schema.PrefixWitness width support)
    (hleftClosed :
      ∀ argument ∈ leftArguments, argument.ReferenceClosed)
    (hrightClosed :
      ∀ argument ∈ rightArguments, argument.ReferenceClosed)
    (harguments : ArgumentsEquivalentThrough width
      leftArguments rightArguments) :
    (schema.instantiate leftArguments).UnfoldingEquivalent
      (schema.instantiate rightArguments) := by
  refine ⟨PrefixInstantiationRelation schema support width
      leftArguments rightArguments, ?_,
    hwitness.instantiationRelation_isBisimulation
      hleftClosed hrightClosed harguments⟩
  change PrefixInstantiationRelation schema support width
    leftArguments rightArguments
    (schema.resolveRHSRef leftArguments schema.root)
    (schema.resolveRHSRef rightArguments schema.root)
  exact hwitness.resolve_prefixInstantiationRelation
    hleftClosed hrightClosed harguments hwitness.1

/-- Existential reachable-prefix form of argument-padding invariance. -/
public theorem HasPrefixWitness.instantiate_unfoldingEquivalent_of_prefix
    {schema : RegularTerm} {width : ℕ}
    {leftArguments rightArguments : List RegularTerm}
    (hwitness : schema.HasPrefixWitness width)
    (hleftClosed :
      ∀ argument ∈ leftArguments, argument.ReferenceClosed)
    (hrightClosed :
      ∀ argument ∈ rightArguments, argument.ReferenceClosed)
    (harguments : ArgumentsEquivalentThrough width
      leftArguments rightArguments) :
    (schema.instantiate leftArguments).UnfoldingEquivalent
      (schema.instantiate rightArguments) := by
  obtain ⟨support, hsupport⟩ := hwitness
  exact hsupport.instantiate_unfoldingEquivalent_of_prefix
    hleftClosed hrightClosed harguments

/-- A reachable prefix witness implies the extensional support invariant used
by active-schema coverages. -/
public theorem PrefixWitness.supportedByPrefix
    {schema : RegularTerm} {support : List ℕ}
    {ranks : List ℕ} {arity width : ℕ}
    (hwitness : schema.PrefixWitness width support)
    (hwellFormed : schema.WellFormed ranks arity)
    (hwidth : width ≤ arity) :
    schema.SupportedByPrefix ranks arity width := by
  refine ⟨hwellFormed, hwidth, ?_⟩
  intro leftArguments rightArguments hleftLength hrightLength
      hleftClosed hrightClosed harguments
  refine ⟨PrefixInstantiationRelation schema support width
      leftArguments rightArguments, ?_,
    hwitness.instantiationRelation_isBisimulation
      hleftClosed hrightClosed harguments⟩
  change PrefixInstantiationRelation schema support width
    leftArguments rightArguments
    (schema.resolveRHSRef leftArguments schema.root)
    (schema.resolveRHSRef rightArguments schema.root)
  exact hwitness.resolve_prefixInstantiationRelation
    hleftClosed hrightClosed harguments hwitness.1

public theorem HasPrefixWitness.supportedByPrefix
    {schema : RegularTerm} {ranks : List ℕ} {arity width : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hwellFormed : schema.WellFormed ranks arity)
    (hwidth : width ≤ arity) :
    schema.SupportedByPrefix ranks arity width := by
  obtain ⟨support, hsupport⟩ := hwitness
  exact hsupport.supportedByPrefix hwellFormed hwidth

/-- Semantic nontriviality excludes the degenerate case in which tying the
selected variable leaves that variable at the root. -/
public theorem rootNode_ne_variable_of_not_unfoldingEquivalent
    {term : RegularTerm} {x : ℕ}
    (hnonvariable :
      ¬term.UnfoldingEquivalent (variableTerm x)) :
    term.rootNode? ≠ some (.inl x) := by
  intro hroot
  exact hnonvariable
    (unfoldingEquivalent_variableTerm_of_rootNode hroot)

public theorem HasPrefixWitness.tieVariable_last
    {term : RegularTerm} {width : ℕ}
    (hwitness : term.HasPrefixWitness width)
    (hwidth : 0 < width)
    (hroot : term.rootNode? ≠ some (.inl (width - 1))) :
    (term.tieVariable (width - 1)).HasPrefixWitness (width - 1) := by
  obtain ⟨support, hsupport⟩ := hwitness
  exact hsupport.tieVariable_last hwidth hroot

/-- Parametric tying preserves the finite reachable-prefix invariant while
eliminating the last active variable. -/
public theorem HasPrefixWitness.tieInto_last
    {outer replacement : RegularTerm}
    {arity width : ℕ}
    (houter : outer.HasPrefixWitness width)
    (hreplacement : replacement.HasPrefixWitness width)
    (houterClosed : outer.ReferenceClosed)
    (hreplacementClosed : replacement.ReferenceClosed)
    (hwidth : 0 < width)
    (hwidthArity : width ≤ arity)
    (hreplacementRoot :
      replacement.rootNode? ≠ some (.inl (width - 1))) :
    (tieInto outer replacement arity (width - 1))
      |>.HasPrefixWitness (width - 1) := by
  obtain ⟨outerSupport, houterSupport⟩ := houter
  have hxArity : width - 1 < arity := by omega
  unfold tieInto
  apply houterSupport.instantiate houterClosed
  · exact tieArguments_referenceClosed
      hreplacementClosed hxArity
  · intro y hy
    by_cases hyx : y = width - 1
    · subst y
      refine ⟨replacement.tieVariable (width - 1), ?_, ?_⟩
      · exact tieArguments_getElem?_eq hxArity
      · exact hreplacement.tieVariable_last
          hwidth hreplacementRoot
    · have hyArity : y < arity := hy.trans_le hwidthArity
      refine ⟨variableTerm y, ?_, ?_⟩
      · exact tieArguments_getElem?_ne hyArity
          (fun hxy => hyx hxy.symm)
      · apply variableTerm_hasPrefixWitness
        omega

/-- The structural invariant gives the extensional reduced-width support
property for the tied schema. -/
public theorem tieInto_supportedByPrefix_last
    {outer replacement : RegularTerm}
    {ranks : List ℕ} {arity width : ℕ}
    (houterWellFormed : outer.WellFormed ranks arity)
    (hreplacementWellFormed : replacement.WellFormed ranks arity)
    (houterWitness : outer.HasPrefixWitness width)
    (hreplacementWitness : replacement.HasPrefixWitness width)
    (hwidth : 0 < width)
    (hwidthArity : width ≤ arity)
    (hreplacementNonvariable :
      ¬replacement.UnfoldingEquivalent
        (variableTerm (width - 1))) :
    (tieInto outer replacement arity (width - 1))
      |>.SupportedByPrefix ranks arity (width - 1) := by
  have hxArity : width - 1 < arity := by omega
  apply (houterWitness.tieInto_last hreplacementWitness
      (referenceClosed_of_wellFormed houterWellFormed)
      (referenceClosed_of_wellFormed hreplacementWellFormed)
      hwidth hwidthArity
      (rootNode_ne_variable_of_not_unfoldingEquivalent
        hreplacementNonvariable)).supportedByPrefix
  · exact tieInto_wellFormed
      houterWellFormed hreplacementWellFormed hxArity
  · omega

end RegularTerm

namespace RegularTerm

/-- The direct open symbol template is supported by all of its declared
parameters. -/
public theorem symbolTemplate_hasPrefixWitness
    (X arity : ℕ) :
    (symbolTemplate X arity).HasPrefixWitness arity := by
  let support := List.range (arity + 1)
  refine ⟨support, ?_⟩
  constructor
  · simp [support, symbolTemplate, root]
  · intro i hi
    have hiBound : i < arity + 1 := by
      simpa [support] using hi
    cases i with
    | zero =>
        right
        refine ⟨X, (List.range arity).map (fun j => j + 1), ?_, ?_⟩
        · simp [symbolTemplate, nodeAt?, nodes]
        · intro child hchild
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hchild
          simp [support] at hj ⊢
          omega
    | succ i =>
        have hi : i < arity := by omega
        left
        refine ⟨i, ?_, hi⟩
        exact symbolTemplate_variableNode X arity i hi

end RegularTerm

namespace FiniteHead

/-- Compiled finite heads carry the structural prefix witness corresponding to
their genuine boundary variables; unreachable compiler padding is ignored. -/
public theorem toRegularTerm_hasPrefixWitness
    {head : FiniteHead} {width : ℕ}
    (hactive : head.VariablesBelow width) :
    head.toRegularTerm.HasPrefixWitness width := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (∀ child ∈ heads, child.VariablesBelow width) →
      ∀ child ∈ heads,
        child.toRegularTerm.HasPrefixWitness width) with
  | var index =>
      simpa [toRegularTerm] using
        RegularTerm.variableTerm_hasPrefixWitness
          (by simpa [VariablesBelow] using hactive)
  | app symbol children ih =>
      have hchildren : ∀ child ∈ children,
          child.VariablesBelow width := by
        simpa [VariablesBelow] using hactive
      rw [toRegularTerm]
      apply (RegularTerm.symbolTemplate_hasPrefixWitness
        symbol children.length).choose_spec.instantiate
      · exact RegularTerm.symbolTemplate_referenceClosed
          symbol children.length
      · intro argument hargument
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
        exact toRegularTerm_referenceClosed child
      · intro x hx
        let child := children[x]
        refine ⟨child.toRegularTerm, ?_, ?_⟩
        · simp [child, List.getElem?_map,
            List.getElem?_eq_getElem hx]
        · exact ih hchildren child
            (List.getElem_mem hx)
  | nil => aesop
  | cons child children ihChild ihChildren => aesop

end FiniteHead

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- An active-schema coverage together with the finite structural invariant
needed to iterate tail elimination. -/
public structure WitnessedActiveSchemaCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (width : ℕ) (word : List (Label Action)) where
  coverage : ActiveSchemaCoverage g initialLeft initialRight width word
  left_witness :
    coverage.schema.left.HasPrefixWitness width
  right_witness :
    coverage.schema.right.HasPrefixWitness width

/-- A bounded active-schema presentation carrying the structural witnesses
needed by tail elimination. -/
public structure BoundedWitnessedActiveSchemaCoverage
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (bound width : ℕ) (arguments : List RegularTerm)
    (word : List (Label Action)) where
  witnessed : WitnessedActiveSchemaCoverage g initialLeft initialRight
    width word
  arguments_eq : witnessed.coverage.arguments = arguments
  arity_le : witnessed.coverage.schema.arity ≤ bound
  left_size_le : witnessed.coverage.schema.left.nodes.length ≤ bound
  right_size_le : witnessed.coverage.schema.right.nodes.length ≤ bound

/-- Forgetting the finite reachability witnesses recovers the ordinary
bounded regular-schema presentation. -/
public def BoundedWitnessedActiveSchemaCoverage.toBoundedActiveSchemaCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm} {word}
    (bounded : BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments word) :
    BoundedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments word :=
  { coverage := bounded.witnessed.coverage
    arguments_eq := bounded.arguments_eq
    arity_le := bounded.arity_le
    left_size_le := bounded.left_size_le
    right_size_le := bounded.right_size_le }

/-- A witnessed regular stair fixes one argument tuple and carries a finite
prefix witness at every selected level. -/
public structure WitnessedRegularActiveStairSequence
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (width : ℕ) (growth : ℕ → ℕ)
    (path : TracePath g initialLeft initialRight) where
  arguments : List RegularTerm
  levels : ℕ → ℕ
  levels_strictMono : StrictMono levels
  covered : ∀ j, Nonempty
    (BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
      (growth j) width arguments (path.word (levels j)))

/-- The witnessed stair-base property is the induction invariant for width
reduction. -/
@[expose] public def HasWitnessedRegularActiveStairBase
    (g : EncodedFirstOrderGrammar Action) (width : ℕ) : Prop :=
  ∃ growth : ℕ → ℕ,
    ∀ initialLeft initialRight,
      g.groundPairCode initialLeft initialRight = true →
      g.TraceEquivalent initialLeft initialRight →
      ∀ path : TracePath g initialLeft initialRight,
        g.EventuallyBoundedOpenSound initialLeft initialRight
          (growth 0) path ∨
        Nonempty (WitnessedRegularActiveStairSequence g
          initialLeft initialRight width growth path)

/-- Forgetting the witnesses gives an ordinary regular stair. -/
public def WitnessedRegularActiveStairSequence.toRegular
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath g initialLeft initialRight}
    (sequence : WitnessedRegularActiveStairSequence g
      initialLeft initialRight width growth path) :
    RegularActiveStairSequence g initialLeft initialRight
      width growth path :=
  { arguments := sequence.arguments
    levels := sequence.levels
    levels_strictMono := sequence.levels_strictMono
    covered := fun j => by
      obtain ⟨coverage⟩ := sequence.covered j
      exact ⟨coverage.toBoundedActiveSchemaCoverage⟩ }

/-- Forgetting witnesses at the property level. -/
public theorem HasWitnessedRegularActiveStairBase.toRegular
    {g : EncodedFirstOrderGrammar Action} {width : ℕ}
    (hstair : g.HasWitnessedRegularActiveStairBase width) :
    g.HasRegularActiveStairBase width := by
  obtain ⟨growth, hstair⟩ := hstair
  refine ⟨growth, ?_⟩
  intro initialLeft initialRight hground hequivalent path
  rcases hstair initialLeft initialRight hground hequivalent path with
    hbounded | hsequence
  · exact Or.inl hbounded
  · obtain ⟨sequence⟩ := hsequence
    exact Or.inr ⟨sequence.toRegular⟩

/-- Finite-head coverages initialize the witnessed regular-schema interface. -/
public def ActiveHeadCoverage.toWitnessedActiveSchemaCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight tails filler word}
    (coverage : ActiveHeadCoverage g initialLeft initialRight
      tails filler word) :
    WitnessedActiveSchemaCoverage g initialLeft initialRight
      tails.length word := by
  refine
    { coverage := coverage.toActiveSchemaCoverage
      left_witness := ?_
      right_witness := ?_ }
  · simpa [ActiveHeadCoverage.schema, activeHeadPair] using
      FiniteHead.toRegularTerm_hasPrefixWitness
        coverage.left_active
  · simpa [ActiveHeadCoverage.schema, activeHeadPair] using
      FiniteHead.toRegularTerm_hasPrefixWitness
        coverage.right_active

/-- A bounded finite-head coverage initializes a bounded witnessed regular
coverage without changing its numerical presentation bound. -/
public def BoundedActiveHeadCoverage.toBoundedWitnessedActiveSchemaCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight tails filler word bound}
    (coverage : BoundedActiveHeadCoverage g initialLeft initialRight
      bound tails filler word) :
    BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
      bound tails.length coverage.arguments word :=
  { witnessed := coverage.toActiveHeadCoverage
      |>.toWitnessedActiveSchemaCoverage
    arguments_eq := rfl
    arity_le := coverage.arity_le
    left_size_le := coverage.left_size_le
    right_size_le := coverage.right_size_le }

/-- Every finite-head stair sequence embeds into the witnessed regular
interface. -/
public def ActiveStairSequence.toWitnessedRegular
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight width growth path}
    (sequence : ActiveStairSequence g initialLeft initialRight
      width growth path) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      width growth path := by
  let arguments := g.activePaddedArguments sequence.tails sequence.filler
  refine
    { arguments := arguments
      levels := sequence.levels
      levels_strictMono := sequence.levels_strictMono
      covered := ?_ }
  intro j
  obtain ⟨coverage⟩ := sequence.covered j
  have hwidth : sequence.tails.length = width := sequence.active_width
  let source := coverage.toBoundedWitnessedActiveSchemaCoverage
  have htype :
      BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
          (growth j) sequence.tails.length arguments
            (path.word (sequence.levels j)) =
        BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
          (growth j) width arguments (path.word (sequence.levels j)) :=
    congrArg (fun activeWidth =>
      BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
        (growth j) activeWidth arguments (path.word (sequence.levels j)))
      hwidth
  exact ⟨htype.mp source⟩

/-- A finite-head active stair base supplies the witnessed induction
invariant at the same width. -/
public theorem HasActiveStairBase.toWitnessedRegular
    {g : EncodedFirstOrderGrammar Action} {width : ℕ}
    (hstair : g.HasActiveStairBase width) :
    g.HasWitnessedRegularActiveStairBase width := by
  obtain ⟨growth, hstair⟩ := hstair
  refine ⟨growth, ?_⟩
  intro initialLeft initialRight hground hequivalent path
  rcases hstair initialLeft initialRight hground hequivalent path with
    hbounded | hsequence
  · exact Or.inl hbounded
  · obtain ⟨sequence⟩ := hsequence
    exact Or.inr ⟨sequence.toWitnessedRegular⟩

/-- Enlarging the numerical presentation bound preserves a witnessed
coverage. -/
public def BoundedWitnessedActiveSchemaCoverage.mono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound bound' width : ℕ} {arguments : List RegularTerm} {word}
    (coverage : BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight bound width arguments word)
    (hbound : bound ≤ bound') :
    BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
      bound' width arguments word :=
  { coverage with
    arity_le := coverage.arity_le.trans hbound
    left_size_le := coverage.left_size_le.trans hbound
    right_size_le := coverage.right_size_le.trans hbound }

/-- Reindex a witnessed bounded coverage by the same active transposition on
its schemas and fixed argument tuple. -/
public def BoundedWitnessedActiveSchemaCoverage.moveParameterToActiveLast
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm} {word}
    (bounded : BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight bound width arguments word)
    (hwidth : 0 < width) (x : ℕ) (hx : x < width) :
    BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
      (bound + bound) width
      (RegularTerm.moveArgumentToActiveLast arguments width x) word := by
  let source := bounded.witnessed.coverage
  let movedOrdinary := bounded.toBoundedActiveSchemaCoverage
    |>.moveParameterToActiveLast hwidth x hx
  have hschemaWellFormed := source.schema_wellFormed
  unfold basisPairWellFormedCode at hschemaWellFormed
  rw [Bool.and_eq_true] at hschemaWellFormed
  have hwidthArity : width ≤ source.schema.arity :=
    source.left_supported.2.1
  let witnessed : WitnessedActiveSchemaCoverage g
      initialLeft initialRight width word :=
    { coverage := movedOrdinary.coverage
      left_witness := by
        change
          (source.schema.left.moveParameterToActiveLast
            source.schema.arity width x).HasPrefixWitness width
        exact bounded.witnessed.left_witness.moveParameterToActiveLast
          (RegularTerm.referenceClosed_of_wellFormed
            hschemaWellFormed.1)
          hwidthArity hwidth hx
      right_witness := by
        change
          (source.schema.right.moveParameterToActiveLast
            source.schema.arity width x).HasPrefixWitness width
        exact bounded.witnessed.right_witness.moveParameterToActiveLast
          (RegularTerm.referenceClosed_of_wellFormed
            hschemaWellFormed.2)
          hwidthArity hwidth hx }
  exact
    { witnessed := witnessed
      arguments_eq := movedOrdinary.arguments_eq
      arity_le := movedOrdinary.arity_le
      left_size_le := movedOrdinary.left_size_le
      right_size_le := movedOrdinary.right_size_le }

/-- Reindex every level of a witnessed stair by one common active
transposition. -/
public def WitnessedRegularActiveStairSequence.moveParameterToActiveLast
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath g initialLeft initialRight}
    (sequence : WitnessedRegularActiveStairSequence g
      initialLeft initialRight width growth path)
    (hwidth : 0 < width) (x : ℕ) (hx : x < width) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight width
      (fun j => growth j + growth j) path :=
  { arguments := RegularTerm.moveArgumentToActiveLast
      sequence.arguments width x
    levels := sequence.levels
    levels_strictMono := sequence.levels_strictMono
    covered := fun j => by
      obtain ⟨coverage⟩ := sequence.covered j
      exact ⟨coverage.moveParameterToActiveLast hwidth x hx⟩ }

/-- Discarding a fixed number of selected levels preserves the witnessed
stair invariant. -/
public def WitnessedRegularActiveStairSequence.dropLevels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath g initialLeft initialRight}
    (sequence : WitnessedRegularActiveStairSequence g
      initialLeft initialRight width growth path)
    (offset : ℕ) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight width
      (fun j => growth (offset + j)) path :=
  { arguments := sequence.arguments
    levels := fun j => sequence.levels (offset + j)
    levels_strictMono := by
      intro i j hij
      exact sequence.levels_strictMono (Nat.add_lt_add_left hij offset)
    covered := fun j => sequence.covered (offset + j) }

/-- Pointwise enlargement of a witnessed stair's growth function. -/
public def WitnessedRegularActiveStairSequence.rebound
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {growth growth' : ℕ → ℕ}
    {path : TracePath g initialLeft initialRight}
    (sequence : WitnessedRegularActiveStairSequence g
      initialLeft initialRight width growth path)
    (hbound : ∀ j, growth j ≤ growth' j) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight width
      growth' path :=
  { arguments := sequence.arguments
    levels := sequence.levels
    levels_strictMono := sequence.levels_strictMono
    covered := fun j => by
      obtain ⟨coverage⟩ := sequence.covered j
      exact ⟨coverage.mono (hbound j)⟩ }

namespace TailEliminatedPair

/-- One successful two-sided certificate replacement produces a witnessed
active-schema coverage at width `width - 1`. -/
public def toWitnessedActiveSchemaCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {word : List (Label Action)}
    {width : ℕ} {replacement : RegularTerm}
    (source : WitnessedActiveSchemaCoverage g initialLeft initialRight
      width word)
    (result : TailEliminatedPair g initialLeft initialRight [] word
      source.coverage.schema.left source.coverage.schema.right
      replacement source.coverage.arguments (width - 1))
    (hwidth : 0 < width)
    (hreplacementWellFormed :
      replacement.WellFormed g.ranks
        source.coverage.arguments.length)
    (hreplacementWitness :
      replacement.HasPrefixWitness width)
    (hreplacementNonvariable :
      ¬replacement.UnfoldingEquivalent
        (RegularTerm.variableTerm (width - 1))) :
    WitnessedActiveSchemaCoverage g initialLeft initialRight
      (width - 1) word := by
  let sourceCoverage := source.coverage
  let arity := sourceCoverage.arguments.length
  let leftSchema := sourceCoverage.schema.left
  let rightSchema := sourceCoverage.schema.right
  let x := width - 1
  let leftTied := RegularTerm.tieInto
    leftSchema replacement arity x
  let rightTied := RegularTerm.tieInto
    rightSchema replacement arity x
  have hsourceWellFormed := sourceCoverage.schema_wellFormed
  unfold basisPairWellFormedCode at hsourceWellFormed
  rw [Bool.and_eq_true] at hsourceWellFormed
  have hwidthArity : width ≤ arity := by
    dsimp [arity, sourceCoverage]
    rw [source.coverage.argument_count]
    exact source.coverage.left_supported.2.1
  have hxArity : x < arity := by
    dsimp [x]
    omega
  have hreplacementRoot :
      replacement.rootNode? ≠ some (.inl x) := by
    exact RegularTerm.rootNode_ne_variable_of_not_unfoldingEquivalent
      hreplacementNonvariable
  have hleftWitness : leftTied.HasPrefixWitness (width - 1) := by
    dsimp [leftTied, leftSchema, arity, x, sourceCoverage]
    exact source.left_witness.tieInto_last
      hreplacementWitness
      (RegularTerm.referenceClosed_of_wellFormed
        hsourceWellFormed.1)
      (RegularTerm.referenceClosed_of_wellFormed
        hreplacementWellFormed)
      hwidth hwidthArity hreplacementRoot
  have hrightWitness : rightTied.HasPrefixWitness (width - 1) := by
    dsimp [rightTied, rightSchema, arity, x, sourceCoverage]
    exact source.right_witness.tieInto_last
      hreplacementWitness
      (RegularTerm.referenceClosed_of_wellFormed
        hsourceWellFormed.2)
      (RegularTerm.referenceClosed_of_wellFormed
        hreplacementWellFormed)
      hwidth hwidthArity hreplacementRoot
  let targetCoverage :
      ActiveSchemaCoverage g initialLeft initialRight
        (width - 1) word :=
    { left := result.leftTarget
      right := result.rightTarget
      derivation := result.derivation
      schema := (arity, leftTied, rightTied)
      arguments := sourceCoverage.arguments
      word_nonempty := sourceCoverage.word_nonempty
      schema_wellFormed := by
        unfold basisPairWellFormedCode
        rw [Bool.and_eq_true]
        exact ⟨by simpa [leftTied, leftSchema, arity, x,
              sourceCoverage] using result.left_schema_wellFormed,
          by simpa [rightTied, rightSchema, arity, x,
              sourceCoverage] using result.right_schema_wellFormed⟩
      rank_padding := by
        dsimp [arity, sourceCoverage]
        rw [source.coverage.argument_count]
        exact source.coverage.rank_padding
      left_supported := by
        apply hleftWitness.supportedByPrefix
        · simpa [leftTied, leftSchema, arity, x,
            sourceCoverage] using result.left_schema_wellFormed
        · change width - 1 ≤ arity
          omega
      right_supported := by
        apply hrightWitness.supportedByPrefix
        · simpa [rightTied, rightSchema, arity, x,
            sourceCoverage] using result.right_schema_wellFormed
        · change width - 1 ≤ arity
          omega
      argument_count := rfl
      arguments_ground := sourceCoverage.arguments_ground
      left_matches :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by simpa [leftTied, leftSchema, arity, x,
              sourceCoverage] using result.left_matches)
      right_matches :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by simpa [rightTied, rightSchema, arity, x,
              sourceCoverage] using result.right_matches) }
  exact
    { coverage := targetCoverage
      left_witness := by
        simpa [targetCoverage] using hleftWitness
      right_witness := by
        simpa [targetCoverage] using hrightWitness }

end TailEliminatedPair

end EncodedFirstOrderGrammar

end DCFEquivalence
