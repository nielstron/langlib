module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteHeadPrefixes
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OffendingWords

@[expose]
public section

/-!
# Exposed equations from an unsound open pair

If two open schemas have an equivalent common ground instance but are not
themselves trace equivalent, a shortest open distinguishing word cannot fail
while both residual roots are applications: ordinary root rewriting commutes
with the common substitution.  Its first genuine discrepancy therefore
exposes a variable on one side and a different residual on the other.  This is
the exposed-equation argument used in the width-reduction step of Jančar's
finite-basis proof.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- An ordinary word reaches two residual schemas, exactly one orientation of
which exposes a variable different from the residual on the other side.  The
same common substitution still makes the reached residuals trace equivalent.

The residual graph rooted at the variable need not be the one-node canonical
`variableTerm`: root rewriting retains unreachable graph garbage.  The root
equation below is the representation-invariant fact needed by tail
elimination. -/
public structure ExposedEquation
    (g : EncodedFirstOrderGrammar Action)
    (left right : RegularTerm) (arguments : List RegularTerm) where
  word : List Action
  leftResidual : RegularTerm
  rightResidual : RegularTerm
  variableIndex : ℕ
  left_run : g.runActions? word left = some leftResidual
  right_run : g.runActions? word right = some rightResidual
  orientation :
    (leftResidual.rootNode? = some (.inl variableIndex) ∧
      ¬ rightResidual.UnfoldingEquivalent leftResidual) ∨
    (rightResidual.rootNode? = some (.inl variableIndex) ∧
      ¬ leftResidual.UnfoldingEquivalent rightResidual)
  instantiated_equivalent :
    g.TraceEquivalent (leftResidual.instantiate arguments)
      (rightResidual.instantiate arguments)

private def SomeWellFormed
    (g : EncodedFirstOrderGrammar Action) (term : RegularTerm) : Prop :=
  ∃ variableBound, term.WellFormed g.ranks variableBound

omit [DecidableEq Action] in
private theorem SomeWellFormed.referenceClosed
    {g : EncodedFirstOrderGrammar Action} {term : RegularTerm}
    (hterm : SomeWellFormed g term) : term.ReferenceClosed := by
  obtain ⟨variableBound, hterm⟩ := hterm
  exact RegularTerm.referenceClosed_of_wellFormed hterm

private theorem variable_lt_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound)
    {i x : ℕ} (hnode : term.nodeAt? i = some (.inl x)) :
    x < variableBound := by
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inl x : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  simpa [RegularTerm.nodeWellFormedCode] using of_decide_eq_true hwell

public theorem rank_arity_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound)
    {i X : ℕ} {children : List ℕ}
    (hnode : term.nodeAt? i = some (.inr (X, children))) :
    ∃ rank, ranks[X]? = some rank ∧ children.length = rank := by
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  unfold RegularTerm.nodeWellFormedCode at hwell
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
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨?_, ?_⟩
  · simpa [RegularTerm.withRoot, RegularTerm.root, RegularTerm.nodes] using
      decide_eq_true hi
  · simpa [RegularTerm.withRoot, RegularTerm.nodes] using hterm.2

public theorem selected_rhs_wellFormed
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

public theorem rootNode?_variable_of_unfoldingEquivalent
    {left right : RegularTerm} {x : ℕ}
    (hequivalent : left.UnfoldingEquivalent right)
    (hleft : left.rootNode? = some (.inl x)) :
    right.rootNode? = some (.inl x) := by
  obtain ⟨relation, hroot, hbisimulation⟩ := hequivalent
  have hcompatible := hbisimulation left.root right.root hroot
  unfold RegularTerm.NodeCompatible at hcompatible
  change left.nodeAt? left.root = some (.inl x) at hleft
  rw [hleft] at hcompatible
  cases hright : right.nodeAt? right.root with
  | none =>
      rw [hright] at hcompatible
      simp [RegularTerm.RawCompatible] at hcompatible
  | some node =>
      rw [hright] at hcompatible
      cases node with
      | inr application =>
          simp [RegularTerm.RawCompatible] at hcompatible
      | inl y =>
          have hxy : x = y := by
            simpa [RegularTerm.RawCompatible] using hcompatible
          subst y
          exact hright

/-- A graph whose reachable root is a variable denotes the corresponding
canonical one-node variable tree, regardless of unreachable graph garbage. -/
public theorem unfoldingEquivalent_variableTerm_of_rootNode?
    {schema : RegularTerm} {x : ℕ}
    (hroot : schema.rootNode? = some (.inl x)) :
    schema.UnfoldingEquivalent (RegularTerm.variableTerm x) := by
  let relation : ℕ → ℕ → Prop := fun i j =>
    i = schema.root ∧ j = 0
  refine ⟨relation, ⟨rfl, rfl⟩, ?_⟩
  intro i j hij
  rcases hij with ⟨rfl, rfl⟩
  change RegularTerm.RawCompatible relation schema.rootNode?
    (RegularTerm.variableTerm x).rootNode?
  rw [hroot, RegularTerm.variableTerm_rootNode?]
  simp [RegularTerm.RawCompatible]

public theorem instantiate_rootNode?_variable_none
    {schema : RegularTerm} {arguments : List RegularTerm} {x : ℕ}
    (hclosed : schema.ReferenceClosed)
    (hroot : schema.rootNode? = some (.inl x))
    (hargument : arguments[x]? = none) :
    (schema.instantiate arguments).rootNode? = some (.inl x) := by
  have hnode : schema.nodeAt? schema.root = some (.inl x) := hroot
  have hresolve : schema.resolveRHSRef arguments schema.root =
      schema.root := by
    simp [RegularTerm.resolveRHSRef, hnode,
      RegularTerm.argumentRoot?, hargument]
  unfold RegularTerm.rootNode?
  change (schema.instantiate arguments).nodeAt?
      (schema.resolveRHSRef arguments schema.root) = some (.inl x)
  rw [hresolve, RegularTerm.instantiate_nodeAt?_rhs schema arguments
    hclosed.1, hnode]
  rfl

private theorem privateStep_some_iff
    (g : EncodedFirstOrderGrammar Action) (x : ℕ)
    (source target : RegularTerm) :
    g.step? (.inr x) source = some target ↔
      source.rootNode? = some (.inl x) ∧ target = source := by
  unfold step?
  cases hroot : source.rootNode? with
  | none => simp
  | some node =>
      cases node with
      | inr application => simp
      | inl y =>
          by_cases hxy : x = y
          · subst y
            simp [eq_comm]
          · simp [hxy, Ne.symm hxy]

private theorem traceEquivalent_successors
    {g : EncodedFirstOrderGrammar Action}
    {left right left' right' : RegularTerm} {label : Label Action}
    (hequivalent : g.TraceEquivalent left right)
    (hleft : g.step? label left = some left')
    (hright : g.step? label right = some right') :
    g.TraceEquivalent left' right' := by
  apply Set.ext
  intro suffix
  change g.IsTrace left' suffix ↔ g.IsTrace right' suffix
  have hwhole : g.IsTrace left (label :: suffix) ↔
      g.IsTrace right (label :: suffix) := by
    change label :: suffix ∈ g.traceLanguage left ↔
      label :: suffix ∈ g.traceLanguage right
    rw [hequivalent]
  simpa [IsTrace, hleft, hright] using hwhole

private theorem traceEquivalent_of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {left right : RegularTerm}
    (hleft : left.ReferenceClosed) (hright : right.ReferenceClosed)
    (hequivalent : left.UnfoldingEquivalent right) :
    g.TraceEquivalent left right := by
  apply (g.traceEquivalent_iff_forall_traceApprox left right).mpr
  intro depth
  exact (guardedContextLaws_of_wellFormed hg).unfoldingApprox depth
    left right hleft hright hequivalent

private def residualContexts
    (schema : RegularTerm) (children : List ℕ) : List RegularTerm :=
  children.map schema.withRoot

private def pluggedResiduals
    (schema : RegularTerm) (arguments : List RegularTerm)
    (children : List ℕ) : List RegularTerm :=
  children.map fun child => (schema.withRoot child).instantiate arguments

private theorem residualContexts_referenceClosed
    {schema : RegularTerm} {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length) :
    ∀ context ∈ residualContexts schema children,
      context.ReferenceClosed := by
  intro context hcontext
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hcontext
  exact RegularTerm.withRoot_referenceClosed hschema
    (hchildren child hchild)

private theorem pluggedResiduals_referenceClosed
    {schema : RegularTerm} {arguments : List RegularTerm}
    {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    ∀ residual ∈ pluggedResiduals schema arguments children,
      residual.ReferenceClosed := by
  intro residual hresidual
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hresidual
  exact RegularTerm.instantiate_referenceClosed
    (RegularTerm.withRoot_referenceClosed hschema
      (hchildren child hchild)) harguments

private theorem stepAction_some_instantiation
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {action : Action}
    (hsource : SomeWellFormed g source)
    (hstep : g.step? (.inl action) source = some target)
    {arguments : List RegularTerm}
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    ∃ concreteTarget,
      g.step? (.inl action) (source.instantiate arguments) =
        some concreteTarget ∧
      (target.instantiate arguments).UnfoldingEquivalent concreteTarget ∧
      concreteTarget.ReferenceClosed := by
  obtain ⟨sourceBound, hsourceWellFormed⟩ := hsource
  have hsourceClosed := RegularTerm.referenceClosed_of_wellFormed
    hsourceWellFormed
  change g.rootRewrite? action source = some target at hstep
  unfold rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ := Option.map_eq_some_iff.mp hstep
      subst target
      have hrootInst := RegularTerm.instantiate_rootApplication?
        (arguments := arguments) hsourceClosed hroot
      let concreteTarget := rhs.instantiate
        (pluggedResiduals source arguments children)
      refine ⟨concreteTarget, ?_, ?_, ?_⟩
      · change g.rootRewrite? action (source.instantiate arguments) =
          some concreteTarget
        unfold rootRewrite?
        simp [hrootInst, hrule, concreteTarget, pluggedResiduals,
          List.map_map, Function.comp_def, RegularTerm.instantiate_withRoot]
      · obtain ⟨rank, hrank, hrhs⟩ := selected_rhs_wellFormed hg hrule
        have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
        obtain ⟨sourceRank, hsourceRank, hchildrenLength⟩ :=
          rank_arity_of_wellFormed hsourceWellFormed hrootNode
        have hrankEq : rank = sourceRank := by
          exact Option.some.inj (hrank.symm.trans hsourceRank)
        have hrhsChildren : rhs.WellFormed g.ranks children.length := by
          rw [hchildrenLength, ← hrankEq]
          exact hrhs
        have hchildren := RegularTerm.rootApplication_children_lt
          hsourceClosed hroot
        have hrhsContexts : rhs.WellFormed g.ranks
            (residualContexts source children).length := by
          simpa [residualContexts] using hrhsChildren
        have hcomposition := RegularTerm.instantiate_comp_unfoldingEquivalent
          (outer := rhs) (contexts := residualContexts source children)
          (arguments := arguments) hrhsContexts
          (residualContexts_referenceClosed hsourceClosed hchildren)
          harguments
        have hcontexts : RegularTerm.composedContexts
            (residualContexts source children) arguments =
            pluggedResiduals source arguments children := by
          simp [RegularTerm.composedContexts, residualContexts,
            pluggedResiduals, List.map_map]
        rw [hcontexts] at hcomposition
        simpa [residualContexts, concreteTarget] using hcomposition
      · obtain ⟨rank, hrank, hrhs⟩ := selected_rhs_wellFormed hg hrule
        have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
        obtain ⟨sourceRank, hsourceRank, hchildrenLength⟩ :=
          rank_arity_of_wellFormed hsourceWellFormed hrootNode
        have hrankEq : rank = sourceRank := by
          exact Option.some.inj (hrank.symm.trans hsourceRank)
        have hrhsChildren : rhs.WellFormed g.ranks children.length := by
          rw [hchildrenLength, ← hrankEq]
          exact hrhs
        have hchildren := RegularTerm.rootApplication_children_lt
          hsourceClosed hroot
        exact RegularTerm.instantiate_referenceClosed
          (RegularTerm.referenceClosed_of_wellFormed hrhsChildren)
          (pluggedResiduals_referenceClosed hsourceClosed hchildren harguments)

private theorem stepAction_some_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {action : Action}
    (hsource : SomeWellFormed g source)
    (hstep : g.step? (.inl action) source = some target) :
    SomeWellFormed g target := by
  obtain ⟨sourceBound, hsourceWellFormed⟩ := hsource
  have hsourceClosed := RegularTerm.referenceClosed_of_wellFormed
    hsourceWellFormed
  change g.rootRewrite? action source = some target at hstep
  unfold rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ := Option.map_eq_some_iff.mp hstep
      subst target
      obtain ⟨rank, hrank, hrhs⟩ := selected_rhs_wellFormed hg hrule
      have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
      obtain ⟨sourceRank, hsourceRank, hchildrenLength⟩ :=
        rank_arity_of_wellFormed hsourceWellFormed hrootNode
      have hrankEq : rank = sourceRank := by
        exact Option.some.inj (hrank.symm.trans hsourceRank)
      have hrhsChildren : rhs.WellFormed g.ranks children.length := by
        rw [hchildrenLength, ← hrankEq]
        exact hrhs
      have hchildren := RegularTerm.rootApplication_children_lt
        hsourceClosed hroot
      have hcontexts : ∀ context ∈ residualContexts source children,
          context.WellFormed g.ranks sourceBound := by
        intro context hcontext
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hcontext
        exact withRoot_wellFormed hsourceWellFormed
          (hchildren child hchild)
      refine ⟨max children.length sourceBound, ?_⟩
      have hrhsContexts : rhs.WellFormed g.ranks
          (residualContexts source children).length := by
        simpa [residualContexts] using hrhsChildren
      simpa [residualContexts] using
        (RegularTerm.instantiate_wellFormed_max hrhsContexts hcontexts)

/-- If the schema arity dominates every grammar rank, ordinary root rewriting
preserves that exact arity.  The padding absorbs the otherwise harmless RHS
variable nodes retained by graph substitution. -/
public theorem stepAction_some_wellFormed_padded
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity : ℕ} (hpadding : g.ranks.foldr max 0 ≤ arity)
    {source target : RegularTerm} {action : Action}
    (hsource : source.WellFormed g.ranks arity)
    (hstep : g.step? (.inl action) source = some target) :
    target.WellFormed g.ranks arity := by
  have hsourceClosed := RegularTerm.referenceClosed_of_wellFormed hsource
  change g.rootRewrite? action source = some target at hstep
  unfold rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ := Option.map_eq_some_iff.mp hstep
      subst target
      obtain ⟨rank, hrank, hrhs⟩ := selected_rhs_wellFormed hg hrule
      have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
      obtain ⟨sourceRank, hsourceRank, hchildrenLength⟩ :=
        rank_arity_of_wellFormed hsource hrootNode
      have hrankEq : rank = sourceRank := by
        exact Option.some.inj (hrank.symm.trans hsourceRank)
      have hrhsChildren : rhs.WellFormed g.ranks children.length := by
        rw [hchildrenLength, ← hrankEq]
        exact hrhs
      have hchildren := RegularTerm.rootApplication_children_lt
        hsourceClosed hroot
      have hcontexts : ∀ context ∈ residualContexts source children,
          context.WellFormed g.ranks arity := by
        intro context hcontext
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hcontext
        exact withRoot_wellFormed hsource (hchildren child hchild)
      have hrhsContexts : rhs.WellFormed g.ranks
          (residualContexts source children).length := by
        simpa [residualContexts] using hrhsChildren
      have hsourceRankMax : sourceRank ≤ g.ranks.foldr max 0 :=
        List.le_max_of_le (List.mem_of_getElem? hsourceRank) (le_refl _)
      have hchildrenArity : children.length ≤ arity := by
        rw [hchildrenLength]
        exact hsourceRankMax.trans hpadding
      have hresult := RegularTerm.instantiate_wellFormed_max
        hrhsContexts hcontexts
      simpa [residualContexts, Nat.max_eq_right hchildrenArity] using hresult

/-- Exact-arity version of padded ordinary symbolic execution. -/
public theorem runActions?_preserves_wellFormed_padded
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity : ℕ} (hpadding : g.ranks.foldr max 0 ≤ arity)
    {schema residual : RegularTerm} (word : List Action)
    (hschema : schema.WellFormed g.ranks arity)
    (hrun : g.runActions? word schema = some residual) :
    residual.WellFormed g.ranks arity := by
  induction word generalizing schema with
  | nil =>
      simp [runActions?] at hrun
      subst residual
      exact hschema
  | cons action word ih =>
      cases hstep : g.step? (.inl action) schema with
      | none => simp [runActions?, hstep] at hrun
      | some next =>
          have htail : g.runActions? word next = some residual := by
            simpa [runActions?, hstep] using hrun
          exact ih
            (stepAction_some_wellFormed_padded hg hpadding hschema hstep)
            htail

/-- Both residuals carried by an exposed equation retain the common padded
arity of its source schemas. -/
public theorem ExposedEquation.leftResidual_wellFormed_padded
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (equation : ExposedEquation g left right arguments)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hleft : left.WellFormed g.ranks arity) :
    equation.leftResidual.WellFormed g.ranks arity :=
  runActions?_preserves_wellFormed_padded g hg hpadding equation.word
    hleft equation.left_run

public theorem ExposedEquation.rightResidual_wellFormed_padded
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (equation : ExposedEquation g left right arguments)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hright : right.WellFormed g.ranks arity) :
    equation.rightResidual.WellFormed g.ranks arity :=
  runActions?_preserves_wellFormed_padded g hg hpadding equation.word
    hright equation.right_run

private theorem stepAction_preserves_referenceClosed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {action : Action} {source target : RegularTerm}
    (hsource : source.ReferenceClosed)
    (hstep : g.step? (.inl action) source = some target) :
    target.ReferenceClosed := by
  change g.rootRewrite? action source = some target at hstep
  unfold rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ := Option.map_eq_some_iff.mp hstep
      subst target
      apply RegularTerm.instantiate_referenceClosed
        (selected_rhs_referenceClosed hg hrule)
      intro argument hargument
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
      exact RegularTerm.withRoot_referenceClosed hsource
        (RegularTerm.rootApplication_children_lt hsource hroot
          child hchild)

private theorem runActions?_respects_unfoldingEquivalent
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (word : List Action) {left right : RegularTerm}
    (hleft : left.ReferenceClosed) (hright : right.ReferenceClosed)
    (hequivalent : left.UnfoldingEquivalent right) :
    Option.Rel RegularTerm.UnfoldingEquivalent
      (g.runActions? word left) (g.runActions? word right) := by
  induction word generalizing left right with
  | nil => exact .some hequivalent
  | cons action word ih =>
      have hstep := step?_respects_unfoldingEquivalent
        (label := (.inl action)) hequivalent
        hleft hright (fun X action rhs hrule =>
          selected_rhs_referenceClosed hg hrule)
      cases hleftStep : g.step? (.inl action) left with
      | none =>
          rw [hleftStep] at hstep
          cases hrightStep : g.step? (.inl action) right with
          | none =>
              simp [runActions?, hleftStep, hrightStep]
          | some right' =>
              rw [hrightStep] at hstep
              cases hstep
      | some left' =>
          rw [hleftStep] at hstep
          cases hrightStep : g.step? (.inl action) right with
          | none =>
              rw [hrightStep] at hstep
              cases hstep
          | some right' =>
              rw [hrightStep] at hstep
              cases hstep with
              | some htargets =>
                  simpa [runActions?, hleftStep, hrightStep] using
                    ih (stepAction_preserves_referenceClosed hg hleft
                        hleftStep)
                      (stepAction_preserves_referenceClosed hg hright
                        hrightStep) htargets

/-- Ordinary symbolic execution commutes with one common substitution up to
equality of the denoted regular tree.  The concrete target is existential
because graph substitution is associative only up to unfolding equivalence,
not raw graph-code equality. -/
public theorem runActions?_instantiate
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity : ℕ} {schema residual : RegularTerm}
    {arguments : List RegularTerm} (word : List Action)
    (hschema : schema.WellFormed g.ranks arity)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hrun : g.runActions? word schema = some residual) :
    ∃ concrete,
      g.runActions? word (schema.instantiate arguments) = some concrete ∧
      (residual.instantiate arguments).UnfoldingEquivalent concrete := by
  induction word generalizing schema residual arity with
  | nil =>
      have hresidual : residual = schema := by
        simpa [runActions?] using (Option.some.inj hrun).symm
      subst residual
      exact ⟨schema.instantiate arguments, rfl,
        RegularTerm.unfoldingEquivalent_refl _⟩
  | cons action word ih =>
      cases hstep : g.step? (.inl action) schema with
      | none => simp [runActions?, hstep] at hrun
      | some next =>
          have htail : g.runActions? word next = some residual := by
            simpa [runActions?, hstep] using hrun
          have hnext := stepAction_some_wellFormed hg
            ⟨arity, hschema⟩ hstep
          obtain ⟨nextBound, hnextWellFormed⟩ := hnext
          obtain ⟨symbolicConcrete, hsymbolicRun,
              hresidualEquivalent⟩ :=
            ih hnextWellFormed htail
          obtain ⟨firstConcrete, hfirstStep, hfirstEquivalent,
              hfirstClosed⟩ :=
            stepAction_some_instantiation hg ⟨arity, hschema⟩
              hstep harguments
          have hsymbolicClosed :
              (next.instantiate arguments).ReferenceClosed :=
            RegularTerm.instantiate_referenceClosed
              (RegularTerm.referenceClosed_of_wellFormed hnextWellFormed)
              harguments
          have hrunRelation := runActions?_respects_unfoldingEquivalent
            g hg word hsymbolicClosed hfirstClosed hfirstEquivalent
          rw [hsymbolicRun] at hrunRelation
          cases hconcreteRun : g.runActions? word firstConcrete with
          | none =>
              rw [hconcreteRun] at hrunRelation
              cases hrunRelation
          | some concrete =>
              rw [hconcreteRun] at hrunRelation
              cases hrunRelation with
              | some htargets =>
                  refine ⟨concrete, ?_, hresidualEquivalent.trans htargets⟩
                  simpa [runActions?, hfirstStep] using hconcreteRun

/-- Ordinary execution preserves reference closure in a well-formed grammar. -/
public theorem runActions?_preserves_referenceClosed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} (word : List Action)
    (hsource : source.ReferenceClosed)
    (hrun : g.runActions? word source = some target) :
    target.ReferenceClosed := by
  induction word generalizing source with
  | nil =>
      simp [runActions?] at hrun
      subst target
      exact hsource
  | cons action word ih =>
      simp only [runActions?, List.map_cons, run?_cons] at hrun
      cases hstep : g.step? (.inl action) source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep, Option.bind_some] at hrun
          exact ih (step?_preserves_referenceClosed hg hsource hstep) hrun

private theorem stepAction_none_instantiation_of_application
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {action : Action}
    (hsource : SomeWellFormed g source)
    (hroot : ∃ X children,
      source.rootApplication? = some (X, children))
    (hstep : g.step? (.inl action) source = none)
    (arguments : List RegularTerm) :
    g.step? (.inl action) (source.instantiate arguments) = none := by
  obtain ⟨X, children, hroot⟩ := hroot
  have hclosed := hsource.referenceClosed
  have hrootInst := RegularTerm.instantiate_rootApplication?
    (arguments := arguments) hclosed hroot
  change g.rootRewrite? action source = none at hstep
  unfold rootRewrite? at hstep
  rw [hroot] at hstep
  have hrule : g.ruleLookup X action = none := by
    simpa using hstep
  change g.rootRewrite? action (source.instantiate arguments) = none
  unfold rootRewrite?
  simp [hrootInst, hrule]

private theorem instantiated_successors_traceEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {left right left' right' : RegularTerm} {action : Action}
    {arguments : List RegularTerm}
    (hleft : SomeWellFormed g left)
    (hright : SomeWellFormed g right)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hequivalent : g.TraceEquivalent (left.instantiate arguments)
      (right.instantiate arguments))
    (hleftStep : g.step? (.inl action) left = some left')
    (hrightStep : g.step? (.inl action) right = some right') :
    g.TraceEquivalent (left'.instantiate arguments)
      (right'.instantiate arguments) := by
  obtain ⟨leftConcrete, hleftConcrete, hleftComposition,
      hleftConcreteClosed⟩ :=
    stepAction_some_instantiation hg hleft hleftStep harguments
  obtain ⟨rightConcrete, hrightConcrete, hrightComposition,
      hrightConcreteClosed⟩ :=
    stepAction_some_instantiation hg hright hrightStep harguments
  have hconcrete := traceEquivalent_successors hequivalent
    hleftConcrete hrightConcrete
  have hleftTargetClosed : (left'.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (stepAction_some_wellFormed hg hleft hleftStep).referenceClosed
      harguments
  have hrightTargetClosed : (right'.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (stepAction_some_wellFormed hg hright hrightStep).referenceClosed
      harguments
  exact (traceEquivalent_of_unfoldingEquivalent hg hleftTargetClosed
      hleftConcreteClosed hleftComposition).trans
    (hconcrete.trans
      (traceEquivalent_of_unfoldingEquivalent hg hrightTargetClosed
        hrightConcreteClosed hrightComposition).symm)

omit [DecidableEq Action] in
private theorem SomeWellFormed.rootNode?_exists
    {g : EncodedFirstOrderGrammar Action} {term : RegularTerm}
    (hterm : SomeWellFormed g term) : ∃ node, term.rootNode? = some node := by
  have hroot := hterm.referenceClosed.1
  exact ⟨term.nodes[term.root], by
    unfold RegularTerm.rootNode? RegularTerm.nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hroot, rfl⟩⟩

private theorem stepAction_some_rootApplication
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {action : Action}
    (hstep : g.step? (.inl action) source = some target) :
    ∃ X children, source.rootApplication? = some (X, children) := by
  change g.rootRewrite? action source = some target at hstep
  unfold rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      exact ⟨X, children, rfl⟩

private theorem not_unfoldingEquivalent_of_variable_root_ne
    {variableSide other : RegularTerm} {x : ℕ}
    (hvariable : variableSide.rootNode? = some (.inl x))
    (hother : other.rootNode? ≠ some (.inl x)) :
    ¬ other.UnfoldingEquivalent variableSide := by
  intro hequivalent
  exact hother (rootNode?_variable_of_unfoldingEquivalent
    hequivalent.symm hvariable)

private theorem traceEquivalent_isTrace_iff
    {g : EncodedFirstOrderGrammar Action} {left right : RegularTerm}
    (hequivalent : g.TraceEquivalent left right)
    (word : List (Label Action)) :
    g.IsTrace left word ↔ g.IsTrace right word := by
  change word ∈ g.traceLanguage left ↔ word ∈ g.traceLanguage right
  rw [hequivalent]

private def ExposedEquation.prepend
    {g : EncodedFirstOrderGrammar Action}
    {left right left' right' : RegularTerm} {action : Action}
    {arguments : List RegularTerm}
    (hleft : g.step? (.inl action) left = some left')
    (hright : g.step? (.inl action) right = some right')
    (equation : ExposedEquation g left' right' arguments) :
    ExposedEquation g left right arguments := by
  refine
    { word := action :: equation.word
      leftResidual := equation.leftResidual
      rightResidual := equation.rightResidual
      variableIndex := equation.variableIndex
      left_run := ?_
      right_run := ?_
      orientation := equation.orientation
      instantiated_equivalent := equation.instantiated_equivalent }
  · simpa [runActions?, hleft] using equation.left_run
  · simpa [runActions?, hright] using equation.right_run

/-- The finite presentation cost which width reduction has to absorb when an
exposed equation is tied into all later schemas. -/
@[expose] public def ExposedEquation.presentationCost
    {g : EncodedFirstOrderGrammar Action}
    {left right : RegularTerm} {arguments : List RegularTerm}
    (equation : ExposedEquation g left right arguments) : ℕ :=
  equation.word.length + equation.leftResidual.nodes.length +
    equation.rightResidual.nodes.length

@[simp] private theorem ExposedEquation.presentationCost_prepend
    {g : EncodedFirstOrderGrammar Action}
    {left right left' right' : RegularTerm} {action : Action}
    {arguments : List RegularTerm}
    (hleft : g.step? (.inl action) left = some left')
    (hright : g.step? (.inl action) right = some right')
    (equation : ExposedEquation g left' right' arguments) :
    (equation.prepend hleft hright).presentationCost =
      equation.presentationCost + 1 := by
  simp [ExposedEquation.presentationCost, ExposedEquation.prepend]
  omega

/-- A coarse bound obtained by following the two deterministic residuals
along a supplied label word.  It depends only on the open schema pair and the
word, never on the common ground substitution used by the exposure proof. -/
@[expose] public def exposedEquationBound
    (g : EncodedFirstOrderGrammar Action)
    (left right : RegularTerm) : List (Label Action) → ℕ
  | [] => left.nodes.length + right.nodes.length
  | label :: suffix =>
      left.nodes.length + right.nodes.length + 1 +
        match label with
        | .inr _ => 0
        | .inl action =>
            match g.step? (.inl action) left,
                g.step? (.inl action) right with
            | some left', some right' =>
                exposedEquationBound g left' right' suffix
            | _, _ => 0

private theorem exists_exposedEquation_of_offending
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {left right : RegularTerm} {arguments : List RegularTerm}
    (hleft : SomeWellFormed g left)
    (hright : SomeWellFormed g right)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hequivalent : g.TraceEquivalent (left.instantiate arguments)
      (right.instantiate arguments))
    (word : List (Label Action))
    (hoffending : g.OffendingWord left right word) :
    ∃ equation : ExposedEquation g left right arguments,
      equation.presentationCost ≤
        exposedEquationBound g left right word := by
  cases word with
  | nil => exact (hoffending.ne_nil rfl).elim
  | cons label suffix =>
      cases suffix with
      | nil =>
          have hdistinguishes :
              (g.step? label left).isSome ≠
                (g.step? label right).isSome := by
            simpa [DistinguishingWord, IsTrace] using hoffending.1
          cases label with
          | inr x =>
              cases hleftStep : g.step? (.inr x) left with
              | none =>
                  cases hrightStep : g.step? (.inr x) right with
                  | none => simp [hleftStep, hrightStep] at hdistinguishes
                  | some rightTarget =>
                      obtain ⟨hrightRoot, _⟩ :=
                        (privateStep_some_iff g x right rightTarget).mp
                          hrightStep
                      have hleftRootNe :
                          left.rootNode? ≠ some (.inl x) := by
                        intro hleftRoot
                        have : g.step? (.inr x) left = some left :=
                          (privateStep_some_iff g x left left).mpr
                            ⟨hleftRoot, rfl⟩
                        rw [hleftStep] at this
                        cases this
                      refine ⟨
                        { word := []
                          leftResidual := left
                          rightResidual := right
                          variableIndex := x
                          left_run := rfl
                          right_run := rfl
                          orientation := Or.inr
                            ⟨hrightRoot,
                              not_unfoldingEquivalent_of_variable_root_ne
                                hrightRoot hleftRootNe⟩
                          instantiated_equivalent := hequivalent }, ?_⟩
                      simp [ExposedEquation.presentationCost,
                        exposedEquationBound]
              | some leftTarget =>
                  cases hrightStep : g.step? (.inr x) right with
                  | some rightTarget =>
                      simp [hleftStep, hrightStep] at hdistinguishes
                  | none =>
                      obtain ⟨hleftRoot, _⟩ :=
                        (privateStep_some_iff g x left leftTarget).mp
                          hleftStep
                      have hrightRootNe :
                          right.rootNode? ≠ some (.inl x) := by
                        intro hrightRoot
                        have : g.step? (.inr x) right = some right :=
                          (privateStep_some_iff g x right right).mpr
                            ⟨hrightRoot, rfl⟩
                        rw [hrightStep] at this
                        cases this
                      refine ⟨
                        { word := []
                          leftResidual := left
                          rightResidual := right
                          variableIndex := x
                          left_run := rfl
                          right_run := rfl
                          orientation := Or.inl
                            ⟨hleftRoot,
                              not_unfoldingEquivalent_of_variable_root_ne
                                hleftRoot hrightRootNe⟩
                          instantiated_equivalent := hequivalent }, ?_⟩
                      simp [ExposedEquation.presentationCost,
                        exposedEquationBound]
          | inl action =>
              cases hleftStep : g.step? (.inl action) left with
              | none =>
                  cases hrightStep : g.step? (.inl action) right with
                  | none => simp [hleftStep, hrightStep] at hdistinguishes
                  | some rightTarget =>
                      obtain ⟨rightX, rightChildren, hrightApplication⟩ :=
                        stepAction_some_rootApplication hrightStep
                      obtain ⟨leftNode, hleftNode⟩ :=
                        hleft.rootNode?_exists
                      cases leftNode with
                      | inl x =>
                          have hrightRoot : ∃ node,
                              right.rootNode? = some node :=
                            hright.rootNode?_exists
                          obtain ⟨rightNode, hrightNode⟩ := hrightRoot
                          have hrightNotVariable :
                              right.rootNode? ≠ some (.inl x) := by
                            intro hrightVariable
                            unfold RegularTerm.rootApplication?
                              at hrightApplication
                            rw [hrightVariable] at hrightApplication
                            simp at hrightApplication
                          refine ⟨
                            { word := []
                              leftResidual := left
                              rightResidual := right
                              variableIndex := x
                              left_run := rfl
                              right_run := rfl
                              orientation := Or.inl
                                ⟨hleftNode,
                                  not_unfoldingEquivalent_of_variable_root_ne
                                    hleftNode hrightNotVariable⟩
                              instantiated_equivalent := hequivalent }, ?_⟩
                          simp [ExposedEquation.presentationCost,
                            exposedEquationBound, hleftStep, hrightStep]
                      | inr leftApplication =>
                          have hleftApplication : ∃ X children,
                              left.rootApplication? = some (X, children) := by
                            rcases leftApplication with ⟨leftX, leftChildren⟩
                            exact ⟨leftX, leftChildren, by
                              unfold RegularTerm.rootApplication?
                              rw [hleftNode]⟩
                          have hleftConcrete :=
                            stepAction_none_instantiation_of_application
                              hleft hleftApplication hleftStep arguments
                          obtain ⟨rightConcrete, hrightConcrete, _, _⟩ :=
                            stepAction_some_instantiation hg hright
                              hrightStep harguments
                          have htrace := traceEquivalent_isTrace_iff
                            hequivalent [Sum.inl action]
                          simp [IsTrace, hleftConcrete, hrightConcrete] at htrace
              | some leftTarget =>
                  cases hrightStep : g.step? (.inl action) right with
                  | some rightTarget =>
                      simp [hleftStep, hrightStep] at hdistinguishes
                  | none =>
                      obtain ⟨leftX, leftChildren, hleftApplication⟩ :=
                        stepAction_some_rootApplication hleftStep
                      obtain ⟨rightNode, hrightNode⟩ :=
                        hright.rootNode?_exists
                      cases rightNode with
                      | inl x =>
                          have hleftNotVariable :
                              left.rootNode? ≠ some (.inl x) := by
                            intro hleftVariable
                            unfold RegularTerm.rootApplication?
                              at hleftApplication
                            rw [hleftVariable] at hleftApplication
                            simp at hleftApplication
                          refine ⟨
                            { word := []
                              leftResidual := left
                              rightResidual := right
                              variableIndex := x
                              left_run := rfl
                              right_run := rfl
                              orientation := Or.inr
                                ⟨hrightNode,
                                  not_unfoldingEquivalent_of_variable_root_ne
                                    hrightNode hleftNotVariable⟩
                              instantiated_equivalent := hequivalent }, ?_⟩
                          simp [ExposedEquation.presentationCost,
                            exposedEquationBound, hleftStep, hrightStep]
                      | inr rightApplication =>
                          have hrightApplication' : ∃ X children,
                              right.rootApplication? = some (X, children) := by
                            rcases rightApplication with
                              ⟨rightX, rightChildren⟩
                            exact ⟨rightX, rightChildren, by
                              unfold RegularTerm.rootApplication?
                              rw [hrightNode]⟩
                          obtain ⟨leftConcrete, hleftConcrete, _, _⟩ :=
                            stepAction_some_instantiation hg hleft
                              hleftStep harguments
                          have hrightConcrete :=
                            stepAction_none_instantiation_of_application
                              hright hrightApplication' hrightStep arguments
                          have htrace := traceEquivalent_isTrace_iff
                            hequivalent [Sum.inl action]
                          simp [IsTrace, hleftConcrete, hrightConcrete] at htrace
      | cons next rest =>
          have hsuffix : next :: rest ≠ [] := by simp
          obtain ⟨left', right', hleftStep, hrightStep⟩ :=
            hoffending.exists_step_of_cons hsuffix
          have htail := hoffending.tail hleftStep hrightStep
          cases label with
          | inr x =>
              obtain ⟨hleftRoot, hleftEq⟩ :=
                (privateStep_some_iff g x left left').mp hleftStep
              obtain ⟨hrightRoot, hrightEq⟩ :=
                (privateStep_some_iff g x right right').mp hrightStep
              subst left'
              subst right'
              exact (hoffending.2 (next :: rest) (by simp) htail.1).elim
          | inl action =>
              have hleft' := stepAction_some_wellFormed hg hleft hleftStep
              have hright' := stepAction_some_wellFormed hg hright hrightStep
              have hequivalent' := instantiated_successors_traceEquivalent
                hg hleft hright harguments hequivalent hleftStep hrightStep
              obtain ⟨equation, hbound⟩ := exists_exposedEquation_of_offending
                g hg hleft' hright' harguments hequivalent'
                (next :: rest) htail
              refine ⟨equation.prepend hleftStep hrightStep, ?_⟩
              rw [ExposedEquation.presentationCost_prepend]
              have htop :
                  exposedEquationBound g left right
                      (.inl action :: next :: rest) =
                    left.nodes.length + right.nodes.length + 1 +
                      exposedEquationBound g left' right' (next :: rest) := by
                rw [exposedEquationBound, hleftStep, hrightStep]
              rw [htop]
              omega
termination_by word.length

/-- A supplied shortest distinguishing word yields an exposed equation whose
presentation cost is bounded independently of the common reference-closed
arguments.  Groundness is intentionally not required here: marker arguments
are ground only in the marker extension, while exposure itself takes place in
the original grammar. -/
public theorem exists_boundedExposedEquation_of_offending_referenceClosed
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hequivalent : g.TraceEquivalent (left.instantiate arguments)
      (right.instantiate arguments))
    (word : List (Label Action))
    (hoffending : g.OffendingWord left right word) :
    ∃ equation : ExposedEquation g left right arguments,
      equation.presentationCost ≤
        exposedEquationBound g left right word := by
  have hleft' : left.WellFormed g.ranks arguments.length := by
    simpa [hargumentsLength] using hleft
  have hright' : right.WellFormed g.ranks arguments.length := by
    simpa [hargumentsLength] using hright
  exact exists_exposedEquation_of_offending g hg
    ⟨arguments.length, hleft'⟩ ⟨arguments.length, hright'⟩
    hargumentsClosed hequivalent word hoffending

/-- Ground arguments are a common special case of the reference-closed
bounded exposure theorem. -/
public theorem exists_boundedExposedEquation_of_offending
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (hequivalent : g.TraceEquivalent (left.instantiate arguments)
      (right.instantiate arguments))
    (word : List (Label Action))
    (hoffending : g.OffendingWord left right word) :
    ∃ equation : ExposedEquation g left right arguments,
      equation.presentationCost ≤
        exposedEquationBound g left right word := by
  have hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  exact g.exists_boundedExposedEquation_of_offending_referenceClosed hg
    hleft hright hargumentsLength hargumentsClosed hequivalent word hoffending

/-- **Exposed-equation lemma.**  If an open pair is inequivalent although one
common ground substitution makes it equivalent, a finite ordinary prefix
exposes a variable equation.  The reached residual instance remains
equivalent, which is the equation used to eliminate one active tail. -/
public theorem exists_exposedEquation_of_not_traceEquivalent
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (hequivalent : g.TraceEquivalent (left.instantiate arguments)
      (right.instantiate arguments))
    (hinequivalent : ¬ g.TraceEquivalent left right) :
    Nonempty (ExposedEquation g left right arguments) := by
  have hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  obtain ⟨word, hword⟩ :=
    g.exists_offendingWord_of_not_traceEquivalent hinequivalent
  have hleft' : left.WellFormed g.ranks arguments.length := by
    simpa [hargumentsLength] using hleft
  have hright' : right.WellFormed g.ranks arguments.length := by
    simpa [hargumentsLength] using hright
  obtain ⟨equation, _⟩ := exists_exposedEquation_of_offending g hg
    ⟨arguments.length, hleft'⟩ ⟨arguments.length, hright'⟩
    hargumentsClosed hequivalent word hword
  exact ⟨equation⟩

private theorem variable_lt_of_run
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity : ℕ} {schema residual : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ} (word : List Action)
    (hschema : schema.WellFormed g.ranks arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (hrun : g.runActions? word schema = some residual)
    (hroot : residual.rootNode? = some (.inl x)) :
    x < arity := by
  by_contra hnot
  have hnone : arguments[x]? = none := by
    apply List.getElem?_eq_none
    omega
  have hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  obtain ⟨concrete, hconcreteRun, hresidualConcrete⟩ :=
    g.runActions?_instantiate hg word hschema hargumentsClosed hrun
  have hschema' : schema.WellFormed g.ranks arguments.length := by
    simpa [hargumentsLength] using hschema
  have hsourceGround := RegularTerm.instantiate_ground hschema'
    hargumentsGround
  have hconcreteGround : concrete.Ground g.ranks := by
    apply PreservesGroundSteps.ground_of_run
      (preservesGroundSteps_of_wellFormed hg) hsourceGround
    simpa [runActions?] using hconcreteRun
  have hresidualClosed := runActions?_preserves_referenceClosed
    hg word (RegularTerm.referenceClosed_of_wellFormed hschema) hrun
  have hinstantiatedRoot := instantiate_rootNode?_variable_none
    hresidualClosed hroot hnone
  have hconcreteRoot := rootNode?_variable_of_unfoldingEquivalent
    hresidualConcrete hinstantiatedRoot
  obtain ⟨symbol, children, happlication⟩ :=
    hconcreteGround.exists_rootApplication
  unfold RegularTerm.rootApplication? at happlication
  rw [hconcreteRoot] at happlication
  simp at happlication

/-- The variable exposed by an open equation is an actual position in the
common ground substitution, rather than an out-of-range variable retained as
unreachable graph data. -/
public theorem ExposedEquation.variableIndex_lt
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (equation : ExposedEquation g left right arguments) :
    equation.variableIndex < arity := by
  rcases equation.orientation with hleftOrientation | hrightOrientation
  · exact variable_lt_of_run g hg equation.word hleft
      hargumentsLength hargumentsGround equation.left_run hleftOrientation.1
  · exact variable_lt_of_run g hg equation.word hright
      hargumentsLength hargumentsGround equation.right_run hrightOrientation.1

end EncodedFirstOrderGrammar

end DCFEquivalence
