module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GrammarNormalForm
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalWorstInstance

@[expose]
public section

/-!
# Independence of unexposable successors

If no ordinary action word can expose a formal successor of a ranked symbol,
then the trace language of that symbol application is independent of the term
placed at that successor.  The proof follows residual open schemas: as long as
the distinguished variable has not been reached, root rewriting commutes with
both substitutions; reaching it would itself provide the forbidden exposing
word.
-/

namespace DCFEquivalence

namespace RegularTerm

private theorem variableTerm_referenceClosed (x : ℕ) :
    (variableTerm x).ReferenceClosed := by
  constructor
  · simp [variableTerm, nodes, root]
  · intro i X children hnode
    have hfalse : False := by
      have hmem : (.inr (X, children) : RawNode) ∈
          (variableTerm x).nodes := List.mem_of_getElem? hnode
      simpa [variableTerm, nodes] using hmem
    exact hfalse.elim

private theorem instantiate_rootNode?_variable_none
    {schema : RegularTerm} {arguments : List RegularTerm} {x : ℕ}
    (hclosed : schema.ReferenceClosed)
    (hroot : schema.nodeAt? schema.root = some (.inl x))
    (hargument : arguments[x]? = none) :
    (schema.instantiate arguments).rootNode? = some (.inl x) := by
  have hresolve : schema.resolveRHSRef arguments schema.root =
      schema.root := by
    simp [resolveRHSRef, hroot, argumentRoot?, hargument]
  unfold rootNode?
  change (schema.instantiate arguments).nodeAt?
      (schema.resolveRHSRef arguments schema.root) = some (.inl x)
  rw [hresolve, instantiate_nodeAt?_rhs schema arguments hclosed.1,
    hroot]
  rfl

private theorem instantiate_unfoldingEquivalent_parameter
    {schema : RegularTerm} {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.ReferenceClosed)
    (hroot : schema.nodeAt? schema.root = some (.inl x))
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    (schema.instantiate arguments).UnfoldingEquivalent
      ((arguments[x]?).getD (variableTerm x)) := by
  cases hargument : arguments[x]? with
  | some argument =>
      simpa [hargument] using
        instantiate_unfoldingEquivalent_argument hroot hargument
          (harguments argument (List.mem_of_getElem? hargument))
  | none =>
      simp only [hargument, Option.getD_none]
      have hsourceRoot := instantiate_rootNode?_variable_none
        hschema hroot hargument
      let R : ℕ → ℕ → Prop := fun i j =>
        i = (schema.instantiate arguments).root ∧ j = 0
      refine ⟨R, ⟨rfl, rfl⟩, ?_⟩
      intro i j hij
      rcases hij with ⟨rfl, rfl⟩
      change RawCompatible R (schema.instantiate arguments).rootNode?
        (variableTerm x).rootNode?
      rw [hsourceRoot, variableTerm_rootNode?]
      simp [RawCompatible]

private theorem unfoldingEquivalent_variableTerm_of_root
    {schema : RegularTerm} {x : ℕ}
    (hroot : schema.nodeAt? schema.root = some (.inl x)) :
    schema.UnfoldingEquivalent (variableTerm x) := by
  let R : ℕ → ℕ → Prop := fun i j => i = schema.root ∧ j = 0
  refine ⟨R, ⟨rfl, rfl⟩, ?_⟩
  intro i j hij
  rcases hij with ⟨rfl, rfl⟩
  change RawCompatible R schema.rootNode? (variableTerm x).rootNode?
  rw [show schema.rootNode? = some (.inl x) by
      simpa [rootNode?] using hroot,
    variableTerm_rootNode?]
  simp [RawCompatible]

/-- Every application node uses a symbol from the supplied rank table with its
declared arity.  Unreachable variables are intentionally irrelevant. -/
private def UsesGrammarSymbols (ranks : List ℕ)
    (term : RegularTerm) : Prop :=
  ∀ X children, (.inr (X, children) : RawNode) ∈ term.nodes →
    ∃ rank, ranks[X]? = some rank ∧ children.length = rank

private theorem usesGrammarSymbols_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound) :
    UsesGrammarSymbols ranks term := by
  intro X children hnode
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hwell := (List.all_eq_true.mp hterm.2) _ hnode
  unfold nodeWellFormedCode at hwell
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hwell
  | some rank =>
      simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hwell
      exact ⟨rank, rfl, hwell.1⟩

private theorem usesGrammarSymbols_withRoot
    {ranks : List ℕ} {term : RegularTerm}
    (hterm : UsesGrammarSymbols ranks term) (root : ℕ) :
    UsesGrammarSymbols ranks (term.withRoot root) := by
  intro X children hnode
  exact hterm X children hnode

private theorem appendArguments_usesGrammarSymbols
    {ranks : List ℕ} {arguments : List RegularTerm}
    (harguments : ∀ argument ∈ arguments,
      UsesGrammarSymbols ranks argument) (offset : ℕ) :
    ∀ X children,
      (.inr (X, children) : RawNode) ∈ appendArguments offset arguments →
      ∃ rank, ranks[X]? = some rank ∧ children.length = rank := by
  induction arguments generalizing offset with
  | nil => simp [appendArguments]
  | cons argument arguments ih =>
      rw [appendArguments_cons]
      intro X children hnode
      rw [List.mem_append] at hnode
      rcases hnode with hhead | htail
      · obtain ⟨source, hsource, hshift⟩ := List.mem_map.mp hhead
        cases hkind : source with
        | inl x => simp [hkind, shiftNode] at hshift
        | inr app =>
            rcases app with ⟨Y, sourceChildren⟩
            simp only [hkind, shiftNode, Sum.inr.injEq,
              Prod.mk.injEq] at hshift
            have hsource' :
                (.inr (Y, sourceChildren) : RawNode) ∈ argument.nodes := by
              simpa [hkind] using hsource
            obtain ⟨rank, hrank, hlength⟩ :=
              harguments argument (by simp) Y sourceChildren hsource'
            refine ⟨rank, ?_, ?_⟩
            · simpa [hshift.1] using hrank
            · rw [← hshift.2, List.length_map]
              exact hlength
      · exact ih
          (fun term hterm => harguments term (by simp [hterm]))
          (offset + argument.nodes.length) X children htail

private theorem usesGrammarSymbols_instantiate
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm}
    (hschema : UsesGrammarSymbols ranks schema)
    (harguments : ∀ argument ∈ arguments,
      UsesGrammarSymbols ranks argument) :
    UsesGrammarSymbols ranks (schema.instantiate arguments) := by
  intro X children hnode
  unfold instantiate nodes at hnode
  rw [List.mem_append] at hnode
  rcases hnode with hschemaNode | hargumentNode
  · obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hschemaNode
    cases hkind : source with
    | inl x => simp [hkind, instantiateNode] at hsourceEq
    | inr app =>
        rcases app with ⟨Y, sourceChildren⟩
        simp only [hkind, instantiateNode, Sum.inr.injEq,
          Prod.mk.injEq] at hsourceEq
        have hsource' :
            (.inr (Y, sourceChildren) : RawNode) ∈ schema.nodes := by
          simpa [hkind] using hsource
        obtain ⟨rank, hrank, hlength⟩ :=
          hschema Y sourceChildren hsource'
        refine ⟨rank, ?_, ?_⟩
        · simpa [hsourceEq.1] using hrank
        · rw [← hsourceEq.2, List.length_map]
          exact hlength
  · exact appendArguments_usesGrammarSymbols harguments
      schema.nodes.length X children hargumentNode

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private def residualContexts (schema : RegularTerm)
    (children : List ℕ) : List RegularTerm :=
  children.map schema.withRoot

private def pluggedResiduals (schema : RegularTerm)
    (arguments : List RegularTerm) (children : List ℕ) :
    List RegularTerm :=
  children.map fun child => (schema.withRoot child).instantiate arguments

private def residualSchema (rhs schema : RegularTerm)
    (children : List ℕ) : RegularTerm :=
  rhs.instantiate (residualContexts schema children)

private theorem step?_original_residual
    (g : EncodedFirstOrderGrammar Action) (action : Action)
    {schema : RegularTerm} {X : ℕ} {children : List ℕ}
    (hroot : schema.rootApplication? = some (X, children)) :
    g.step? (.inl action) schema =
      (g.ruleLookup X action).map fun rhs =>
        residualSchema rhs schema children := by
  change g.rootRewrite? action schema = _
  unfold rootRewrite?
  rw [hroot]
  rfl

private theorem resolvedChildren_eq_pluggedResiduals
    (schema : RegularTerm) (arguments : List RegularTerm)
    (children : List ℕ) :
    (children.map (schema.resolveRHSRef arguments)).map
        (schema.instantiate arguments).withRoot =
      pluggedResiduals schema arguments children := by
  simp [pluggedResiduals, List.map_map]

private theorem step?_instantiate_original
    (g : EncodedFirstOrderGrammar Action)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {X : ℕ} {children : List ℕ} (action : Action)
    (hschema : schema.ReferenceClosed)
    (hroot : schema.rootApplication? = some (X, children)) :
    g.step? (.inl action) (schema.instantiate arguments) =
      (g.ruleLookup X action).map fun rhs =>
        rhs.instantiate (pluggedResiduals schema arguments children) := by
  change g.rootRewrite? action (schema.instantiate arguments) = _
  unfold rootRewrite?
  rw [RegularTerm.instantiate_rootApplication? hschema hroot]
  simp only
  rw [resolvedChildren_eq_pluggedResiduals]

private theorem step?_instantiate_application_private
    (g : EncodedFirstOrderGrammar Action) (x : ℕ)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {X : ℕ} {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hroot : schema.rootApplication? = some (X, children)) :
    g.step? (.inr x) (schema.instantiate arguments) = none := by
  have hinstRoot := RegularTerm.instantiate_rootApplication?
    (arguments := arguments) hschema hroot
  have hnode := RegularTerm.nodeAt?_root_of_rootApplication? hinstRoot
  have hrootNode : (schema.instantiate arguments).rootNode? =
      some (.inr
        (X, children.map (schema.resolveRHSRef arguments))) := by
    simpa [RegularTerm.rootNode?] using hnode
  unfold step?
  rw [hrootNode]

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

private theorem residualContexts_usesGrammarSymbols
    {ranks : List ℕ} {schema : RegularTerm} {children : List ℕ}
    (hschema : RegularTerm.UsesGrammarSymbols ranks schema) :
    ∀ context ∈ residualContexts schema children,
      RegularTerm.UsesGrammarSymbols ranks context := by
  intro context hcontext
  obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hcontext
  exact RegularTerm.usesGrammarSymbols_withRoot hschema child

private theorem pluggedResiduals_referenceClosed
    {schema : RegularTerm} {arguments : List RegularTerm}
    {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    ∀ term ∈ pluggedResiduals schema arguments children,
      term.ReferenceClosed := by
  intro term hterm
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hterm
  exact RegularTerm.instantiate_referenceClosed
    (RegularTerm.withRoot_referenceClosed hschema
      (hchildren child hchild)) harguments

private theorem residualSchema_referenceClosed
    {rhs schema : RegularTerm} {children : List ℕ}
    (hrhs : rhs.ReferenceClosed)
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length) :
    (residualSchema rhs schema children).ReferenceClosed := by
  exact RegularTerm.instantiate_referenceClosed hrhs
    (residualContexts_referenceClosed hschema hchildren)

private theorem residualSchema_usesGrammarSymbols
    {ranks : List ℕ} {rhs schema : RegularTerm} {children : List ℕ}
    (hrhs : RegularTerm.UsesGrammarSymbols ranks rhs)
    (hschema : RegularTerm.UsesGrammarSymbols ranks schema) :
    RegularTerm.UsesGrammarSymbols ranks
      (residualSchema rhs schema children) := by
  exact RegularTerm.usesGrammarSymbols_instantiate hrhs
    (residualContexts_usesGrammarSymbols hschema)

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

private theorem parameter_instantiation_approx
    {g : EncodedFirstOrderGrammar Action}
    (laws : g.GuardedContextLaws) (depth : ℕ)
    {schema : RegularTerm} {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.ReferenceClosed)
    (hroot : schema.nodeAt? schema.root = some (.inl x))
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    g.TraceApprox depth (schema.instantiate arguments)
      ((arguments[x]?).getD (RegularTerm.variableTerm x)) := by
  apply laws.unfoldingApprox
  · exact RegularTerm.instantiate_referenceClosed hschema harguments
  · cases hargument : arguments[x]? with
    | none => exact RegularTerm.variableTerm_referenceClosed x
    | some argument =>
        exact harguments argument (List.mem_of_getElem? hargument)
  · exact RegularTerm.instantiate_unfoldingEquivalent_parameter
      hschema hroot harguments

private theorem residual_composition_approx
    {g : EncodedFirstOrderGrammar Action}
    (laws : g.GuardedContextLaws) (depth : ℕ)
    {ranks : List ℕ} {rhs schema : RegularTerm}
    {children : List ℕ} {arguments : List RegularTerm}
    (hrhs : rhs.WellFormed ranks children.length)
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    g.TraceApprox depth
      ((residualSchema rhs schema children).instantiate arguments)
      (rhs.instantiate (pluggedResiduals schema arguments children)) := by
  have hcontexts := residualContexts_referenceClosed hschema hchildren
  have hcomposition := RegularTerm.instantiate_comp_unfoldingEquivalent
    (outer := rhs) (contexts := residualContexts schema children)
    (arguments := arguments) (ranks := ranks) (by
      simpa [residualContexts] using hrhs) hcontexts harguments
  have hcomposed : RegularTerm.composedContexts
      (residualContexts schema children) arguments =
      pluggedResiduals schema arguments children := by
    simp [RegularTerm.composedContexts, residualContexts,
      pluggedResiduals, List.map_map]
  rw [hcomposed] at hcomposition
  apply laws.unfoldingApprox
  · exact RegularTerm.instantiate_referenceClosed
      (residualSchema_referenceClosed
        (RegularTerm.referenceClosed_of_wellFormed hrhs)
        hschema hchildren) harguments
  · exact RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed hrhs)
      (pluggedResiduals_referenceClosed hschema hchildren harguments)
  · simpa [residualSchema] using hcomposition

private theorem runActions?_append_singleton
    (g : EncodedFirstOrderGrammar Action)
    {initial schema target : RegularTerm} {stem : List Action}
    {action : Action}
    (hprefix : g.runActions? stem initial = some schema)
    (hstep : g.step? (.inl action) schema = some target) :
    g.runActions? (stem ++ [action]) initial = some target := by
  unfold runActions? at hprefix ⊢
  rw [List.map_append, run?_append, hprefix]
  simpa using hstep

private theorem instantiate_traceApprox_of_not_exposable_aux
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (position : g.SuccessorPosition)
    (hno : ¬ ∃ word, g.ExposesSuccessor position word)
    (laws : g.GuardedContextLaws)
    (leftArguments rightArguments : List RegularTerm)
    (hleftArguments : ∀ argument ∈ leftArguments,
      argument.ReferenceClosed)
    (hrightArguments : ∀ argument ∈ rightArguments,
      argument.ReferenceClosed)
    (hsame : ∀ j, j ≠ position.2.val →
      leftArguments[j]? = rightArguments[j]?) :
    ∀ (depth : ℕ) (stem : List Action) (schema : RegularTerm),
      g.runActions? stem
          (RegularTerm.symbolTemplate position.1
            (g.ranks.get position.1)) = some schema →
      schema.ReferenceClosed →
      RegularTerm.UsesGrammarSymbols g.ranks schema →
      g.TraceApprox depth (schema.instantiate leftArguments)
        (schema.instantiate rightArguments) := by
  intro depth
  induction depth with
  | zero =>
      intro stem schema hreach hclosed hsymbols
      trivial
  | succ n ih =>
      intro stem schema hreach hclosed hsymbols
      let rootNode : RawNode := schema.nodes[schema.root]'hclosed.1
      have hroot : schema.nodeAt? schema.root = some rootNode := by
        unfold RegularTerm.nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hclosed.1, rfl⟩
      cases hkind : rootNode with
      | inl x =>
          have hvariable : schema.nodeAt? schema.root = some (.inl x) := by
            simpa [hkind] using hroot
          by_cases hx : x = position.2.val
          · subst x
            have hexposes : g.ExposesSuccessor position stem := by
              refine ⟨schema, hreach, ?_⟩
              exact RegularTerm.unfoldingEquivalent_variableTerm_of_root
                hvariable
            exact (hno ⟨stem, hexposes⟩).elim
          · have hleftApprox := parameter_instantiation_approx laws (n + 1)
              hclosed hvariable hleftArguments
            have hrightApprox := parameter_instantiation_approx laws (n + 1)
              hclosed hvariable hrightArguments
            have htarget :
                ((leftArguments[x]?).getD
                    (RegularTerm.variableTerm x)) =
                  ((rightArguments[x]?).getD
                    (RegularTerm.variableTerm x)) := by
              rw [hsame x hx]
            rw [htarget] at hleftApprox
            exact hleftApprox.trans hrightApprox.symm
      | inr app =>
          rcases app with ⟨X, children⟩
          have happlicationNode : schema.nodeAt? schema.root =
              some (.inr (X, children)) := by
            simpa [hkind] using hroot
          have happlication : schema.rootApplication? =
              some (X, children) := by
            simp [RegularTerm.rootApplication?, RegularTerm.rootNode?,
              happlicationNode]
          intro label
          cases label with
          | inr x =>
              rw [step?_instantiate_application_private g x hclosed
                    happlication,
                step?_instantiate_application_private g x hclosed
                    happlication]
              exact .none
          | inl action =>
              rw [step?_instantiate_original g action hclosed happlication,
                step?_instantiate_original g action hclosed happlication]
              cases hrule : g.ruleLookup X action with
              | none => simp [hrule]
              | some rhs =>
                  simp only [hrule, Option.map_some]
                  obtain ⟨symbolRank, hsymbolRank, hchildrenLength⟩ :=
                    hsymbols X children
                      (List.mem_of_getElem? happlicationNode)
                  obtain ⟨ruleRank, hruleRank, hrhsWF⟩ :=
                    selected_rhs_wellFormed hg hrule
                  have hranks : ruleRank = symbolRank :=
                    Option.some.inj (hruleRank.symm.trans hsymbolRank)
                  have hrhsArity : rhs.WellFormed
                      g.ranks children.length := by
                    rw [hchildrenLength, ← hranks]
                    exact hrhsWF
                  have hchildren :=
                    RegularTerm.rootApplication_children_lt
                      hclosed happlication
                  have hresidualClosed := residualSchema_referenceClosed
                    (RegularTerm.referenceClosed_of_wellFormed hrhsArity)
                    hclosed hchildren
                  have hresidualSymbols :=
                    residualSchema_usesGrammarSymbols
                      (children := children)
                      (RegularTerm.usesGrammarSymbols_of_wellFormed
                        hrhsArity) hsymbols
                  have hopenStep : g.step? (.inl action) schema =
                      some (residualSchema rhs schema children) := by
                    rw [step?_original_residual g action happlication,
                      hrule]
                    rfl
                  have hresidualReach := runActions?_append_singleton g
                    hreach hopenStep
                  have hresidualApprox := ih (stem ++ [action])
                    (residualSchema rhs schema children) hresidualReach
                    hresidualClosed hresidualSymbols
                  have hleftComposition := residual_composition_approx
                    laws n hrhsArity hclosed hchildren hleftArguments
                  have hrightComposition := residual_composition_approx
                    laws n hrhsArity hclosed hchildren hrightArguments
                  exact .some (hleftComposition.symm.trans
                    (hresidualApprox.trans hrightComposition))

/-- Strong reference-closed form of unexposable-successor independence. -/
public theorem traceEquivalent_symbolTemplate_instances_of_not_exposable_referenceClosed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (position : g.SuccessorPosition)
    (hno : ¬ ∃ word, g.ExposesSuccessor position word)
    {leftArguments rightArguments : List RegularTerm}
    (hleftArguments : ∀ argument ∈ leftArguments,
      argument.ReferenceClosed)
    (hrightArguments : ∀ argument ∈ rightArguments,
      argument.ReferenceClosed)
    (hsame : ∀ j, j ≠ position.2.val →
      leftArguments[j]? = rightArguments[j]?) :
    g.TraceEquivalent
      ((RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate leftArguments)
      ((RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate rightArguments) := by
  let schema := RegularTerm.symbolTemplate position.1
    (g.ranks.get position.1)
  have hrank : g.ranks[position.1]? =
      some (g.ranks.get position.1) := by simp
  have hschemaWF : schema.WellFormed g.ranks
      (g.ranks.get position.1) := by
    exact RegularTerm.symbolTemplate_wellFormed hrank
  apply (g.traceEquivalent_iff_forall_traceApprox _ _).mpr
  intro depth
  apply instantiate_traceApprox_of_not_exposable_aux g hg position
    hno (guardedContextLaws_of_wellFormed hg)
    leftArguments rightArguments hleftArguments hrightArguments hsame
    depth [] schema
  · rfl
  · exact RegularTerm.referenceClosed_of_wellFormed hschemaWF
  · exact RegularTerm.usesGrammarSymbols_of_wellFormed hschemaWF

/-- Substituting arbitrary different reference-closed terms only at an
unexposable successor does not change the trace language of the enclosing
symbol application. -/
public theorem traceEquivalent_symbolTemplate_instances_of_not_exposable
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (position : g.SuccessorPosition)
    (hno : ¬ ∃ word, g.ExposesSuccessor position word)
    {leftArguments rightArguments : List RegularTerm}
    (_hlengths : leftArguments.length = g.ranks.get position.1 ∧
      rightArguments.length = g.ranks.get position.1)
    (hleftArguments : ∀ argument ∈ leftArguments,
      argument.ReferenceClosed)
    (hrightArguments : ∀ argument ∈ rightArguments,
      argument.ReferenceClosed)
    (hsame : ∀ j, j ≠ position.2.val →
      leftArguments[j]? = rightArguments[j]?) :
    g.TraceEquivalent
      ((RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate leftArguments)
      ((RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate rightArguments) :=
  traceEquivalent_symbolTemplate_instances_of_not_exposable_referenceClosed
    hg position hno hleftArguments hrightArguments hsame

/-- Ground arguments are a convenient sufficient condition for the reference
closure hypotheses of the main independence theorem. -/
public theorem traceEquivalent_symbolTemplate_instances_of_not_exposable_ground
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (position : g.SuccessorPosition)
    (hno : ¬ ∃ word, g.ExposesSuccessor position word)
    {leftArguments rightArguments : List RegularTerm}
    (hlengths : leftArguments.length = g.ranks.get position.1 ∧
      rightArguments.length = g.ranks.get position.1)
    (hleftArguments : ∀ argument ∈ leftArguments,
      argument.Ground g.ranks)
    (hrightArguments : ∀ argument ∈ rightArguments,
      argument.Ground g.ranks)
    (hsame : ∀ j, j ≠ position.2.val →
      leftArguments[j]? = rightArguments[j]?) :
    g.TraceEquivalent
      ((RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate leftArguments)
      ((RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate rightArguments) := by
  apply traceEquivalent_symbolTemplate_instances_of_not_exposable
    hg position hno hlengths
  · intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hleftArguments argument hargument)
  · intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hrightArguments argument hargument)
  · exact hsame

end EncodedFirstOrderGrammar

end DCFEquivalence
