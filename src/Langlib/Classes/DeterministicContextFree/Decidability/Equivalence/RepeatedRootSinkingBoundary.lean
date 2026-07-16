module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedRootSinking
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinkingBoundary

@[expose]
public section

/-!
# Reflecting repeated root sinking through a finite schema

An exact root-sinking step carries an open run to one fixed formal child.
Replaying the whole step word on an open schema therefore either crosses a
schema variable or descends to the literal child at the same ordered
position.  Iterating this observation gives a genuine symbolic run to a
variable, rather than only a concrete instance reaching one argument.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A prefix of `word` is an actual ordinary run of the open schema to a
residual denoting one of its active variables. -/
public structure SchemaVariableHitBy
    (g : EncodedFirstOrderGrammar Action)
    (schema : RegularTerm) (width : ℕ)
    (word : List (Label Action)) where
  actions : List Action
  remainder : List (Label Action)
  word_eq : word = actions.map Sum.inl ++ remainder
  index : ℕ
  index_lt : index < width
  target : RegularTerm
  run : g.runActions? actions schema = some target
  target_matches :
    target.UnfoldingEquivalent
      (RegularTerm.variableTerm index)

/-- Exact-index form of root-step replay.  Unlike the existential-child API,
this theorem exposes that the selected child is precisely the entry at the
formal parameter index stored in `step`. -/
public theorem RootSinkingStep.replay_selectedChild_of_root
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {rootSymbol : ℕ} {children : List ℕ}
    {actions : List Action}
    (step : RootSinkingStep
      g rootSymbol children.length actions)
    {schema : RegularTerm}
    (hschemaClosed : schema.ReferenceClosed)
    (hrank :
      g.ranks[rootSymbol]? = some children.length)
    (hroot :
      schema.rootApplication? = some (rootSymbol, children)) :
    ∃ target,
      g.runActions? actions schema = some target ∧
        target.UnfoldingEquivalent
          (schema.withRoot children[step.child.val]) := by
  let arguments := children.map schema.withRoot
  let child := children[step.child.val]
  have hchildrenBound :=
    RegularTerm.rootApplication_children_lt hschemaClosed hroot
  have hchildMem : child ∈ children :=
    List.getElem_mem step.child.isLt
  have hchildBound : child < schema.nodes.length :=
    hchildrenBound child hchildMem
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    obtain ⟨index, hindex, rfl⟩ :=
      List.mem_map.mp hargument
    exact RegularTerm.withRoot_referenceClosed hschemaClosed
      (hchildrenBound index hindex)
  have htemplateWellFormed :
      (RegularTerm.symbolTemplate rootSymbol children.length)
        |>.WellFormed g.ranks children.length :=
    RegularTerm.symbolTemplate_wellFormed hrank
  obtain ⟨templateTarget, htemplateRun,
      htargetInstantiation⟩ :=
    g.runActions?_instantiate hg actions htemplateWellFormed
      hargumentsClosed step.run
  have htemplateInstance :
      ((RegularTerm.symbolTemplate rootSymbol children.length)
          |>.instantiate arguments).UnfoldingEquivalent schema := by
    simpa [arguments] using
      RegularTerm.symbolTemplate_instantiate_unfoldingEquivalent
        hschemaClosed hroot
  have htemplateInstanceClosed :
      ((RegularTerm.symbolTemplate rootSymbol children.length)
          |>.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed
        htemplateWellFormed)
      hargumentsClosed
  obtain ⟨target, htargetRun, htargetTemplate⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      htemplateInstance.symm hschemaClosed
      htemplateInstanceClosed htemplateRun
  have hargument :
      arguments[step.child.val]? =
        some (schema.withRoot child) := by
    simp [arguments, child, step.child.isLt]
  have htargetNode :
      step.target.nodeAt? step.target.root =
        some (.inl step.child.val) := by
    simpa [RegularTerm.rootNode?] using step.target_root
  have htargetChild :
      (step.target.instantiate arguments).UnfoldingEquivalent
        (schema.withRoot child) :=
    RegularTerm.instantiate_unfoldingEquivalent_argument
      htargetNode hargument
      (RegularTerm.withRoot_referenceClosed
        hschemaClosed hchildBound)
  exact ⟨target, htargetRun,
    htargetTemplate.trans
      (htargetInstantiation.symm.trans htargetChild)⟩

/-- Before using a depth bound, repeated exact root sinking either produces
an actual open-schema run to an active variable or reflects to a literal
schema descendant of the same depth. -/
public theorem repeatedlyRootSinksBy_variableHit_or_schemaDescendant
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {support : List ℕ} {word : List (Label Action)}
    {depth : ℕ}
    (hwitness : schema.PrefixWitness width support)
    (hschemaClosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    (hsourceGround : source.Ground g.ranks)
    (hsourceSchema :
      source.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hsinks : g.RepeatedlyRootSinksBy source word depth) :
    Nonempty (SchemaVariableHitBy
      g schema width word) ∨
      ∃ index, schema.DescendantAt depth index := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  induction depth generalizing schema source support word with
  | zero =>
      exact Or.inr ⟨schema.root, .root⟩
  | succ depth ih =>
      cases hsinks with
      | @succ source word stem suffix target depth
          hword step hrest =>
          rcases hwitness.2 schema.root hwitness.1 with
            hvariable | happlication
          · obtain ⟨x, hrootVariable, hx⟩ := hvariable
            have hrootVariable' :
                schema.rootNode? = some (.inl x) := by
              simpa [RegularTerm.rootNode?] using hrootVariable
            exact Or.inl ⟨
              { actions := []
                remainder := word
                word_eq := by simp
                index := x
                index_lt := hx
                target := schema
                run := rfl
                target_matches :=
                  unfoldingEquivalent_variableTerm_of_rootNode?
                    hrootVariable' }⟩
          · obtain ⟨X, children, hrootNode,
                hchildrenSupport⟩ := happlication
            have hrootApplication :
                schema.rootApplication? = some (X, children) := by
              simp [RegularTerm.rootApplication?,
                RegularTerm.rootNode?, hrootNode]
            have hinstanceRoot :=
              RegularTerm.instantiate_rootApplication?
                (arguments := arguments)
                hschemaClosed hrootApplication
            obtain ⟨instanceChildren, hequivalentRoot,
                hchildrenEquivalent⟩ :=
              RegularTerm.rootApplication?_of_unfoldingEquivalent
                hsourceSchema step.source_root
            have happlications :
                (step.rootSymbol, instanceChildren) =
                  (X, children.map
                    (schema.resolveRHSRef arguments)) :=
              Option.some.inj
                (hequivalentRoot.symm.trans hinstanceRoot)
            have hsymbol : step.rootSymbol = X :=
              congrArg Prod.fst happlications
            have hinstanceChildren :
                instanceChildren =
                  children.map
                    (schema.resolveRHSRef arguments) :=
              congrArg Prod.snd happlications
            have hchildrenLength :
                step.children.length = children.length := by
              have hlength :=
                List.Forall₂.length_eq hchildrenEquivalent
              rw [hinstanceChildren, List.length_map] at hlength
              exact hlength
            have hiSchema :
                step.open_step.child.val < children.length := by
              simpa [hchildrenLength] using
                step.open_step.child.isLt
            let schemaChild :=
              children[step.open_step.child.val]
            let sourceChild :=
              step.children[step.open_step.child.val]
            have hschemaChild : schemaChild ∈ children :=
              List.getElem_mem hiSchema
            have hsourceChild :
                sourceChild ∈ step.children :=
              List.getElem_mem step.open_step.child.isLt
            have hchildBound :
                schemaChild < schema.nodes.length :=
              hschemaClosed.2 schema.root X children hrootNode
                schemaChild hschemaChild
            have hchildClosed :
                (schema.withRoot schemaChild).ReferenceClosed :=
              RegularTerm.withRoot_referenceClosed
                hschemaClosed hchildBound
            have hchildWitness :
                (schema.withRoot schemaChild)
                  |>.PrefixWitness width support :=
              hwitness.withRoot
                (hchildrenSupport schemaChild hschemaChild)
            let schemaPosition : Fin children.length :=
              ⟨step.open_step.child.val, hiSchema⟩
            let hopenSchema :
                RootSinkingStep g X children.length step.actions :=
              { child := schemaPosition
                target := step.open_step.target
                actions_nonempty :=
                  step.open_step.actions_nonempty
                run := by
                  simpa [hsymbol, hchildrenLength] using
                    step.open_step.run
                target_root := by
                  simpa [schemaPosition] using
                    step.open_step.target_root }
            have hrank :
                g.ranks[X]? = some children.length := by
              have hsourceRank :=
                hsourceGround.root_rank_arity step.source_root
              simpa [hsymbol, hchildrenLength] using hsourceRank
            obtain ⟨schemaTarget, hschemaRun,
                hschemaTarget⟩ :=
              hopenSchema.replay_selectedChild_of_root
                hg hschemaClosed hrank hrootApplication
            have hschemaChildVal :
                hopenSchema.child.val =
                  step.open_step.child.val := by
              simp [hopenSchema, schemaPosition]
            have hschemaTargetChild :
                schemaTarget.UnfoldingEquivalent
                  (schema.withRoot schemaChild) := by
              simpa [schemaChild, hschemaChildVal] using
                hschemaTarget
            have hsourceClosed :
                source.ReferenceClosed :=
              RegularTerm.referenceClosed_of_ground hsourceGround
            obtain ⟨sourceReplayTarget, hsourceReplayRun,
                hsourceReplayTarget⟩ :=
              step.open_step.replay_selectedChild_of_root
                hg hsourceClosed
                (hsourceGround.root_rank_arity step.source_root)
                step.source_root
            have hsourceRun :
                g.runActions? step.actions source = some target := by
              simpa [runActions?, step.actions_eq] using
                step.semantic.run
            have hsourceReplayEq : sourceReplayTarget = target :=
              Option.some.inj
                (hsourceReplayRun.symm.trans hsourceRun)
            subst sourceReplayTarget
            have hiInstance :
                step.open_step.child.val <
                  instanceChildren.length := by
              have hlength :=
                List.Forall₂.length_eq hchildrenEquivalent
              omega
            have hchildrenGet :=
              (List.forall₂_iff_get.mp hchildrenEquivalent).2
                step.open_step.child.val
                step.open_step.child.isLt hiInstance
            have hsourceGet :
                step.children.get
                    ⟨step.open_step.child.val,
                      step.open_step.child.isLt⟩ =
                  sourceChild := by
              rfl
            have hinstanceGet :
                instanceChildren.get
                    ⟨step.open_step.child.val, hiInstance⟩ =
                  schema.resolveRHSRef arguments schemaChild := by
              simp [hinstanceChildren, schemaChild]
            rw [hsourceGet, hinstanceGet] at hchildrenGet
            have hpointed :
                (source.withRoot sourceChild).UnfoldingEquivalent
                  ((schema.instantiate arguments).withRoot
                    (schema.resolveRHSRef arguments schemaChild)) :=
              (RegularTerm.withRoot_unfoldingEquivalent_iff_bisimilarAt
                source (schema.instantiate arguments)
                sourceChild
                (schema.resolveRHSRef arguments schemaChild)).2
                hchildrenGet
            have hinstanceChildEq :
                (schema.instantiate arguments).withRoot
                    (schema.resolveRHSRef arguments schemaChild) =
                  (schema.withRoot schemaChild).instantiate arguments :=
              schema.instantiate_withRoot arguments schemaChild
            rw [hinstanceChildEq] at hpointed
            have htargetChild :
                target.UnfoldingEquivalent
                  ((schema.withRoot schemaChild).instantiate
                    arguments) :=
              hsourceReplayTarget.trans hpointed
            have htargetGround : target.Ground g.ranks :=
              hgroundSteps.ground_of_run
                hsourceGround step.semantic.run
            rcases ih hchildWitness hchildClosed
                htargetGround htargetChild hrest with
              hhit | hschemaPath
            · obtain ⟨hit⟩ := hhit
              have hschemaTargetClosed :
                  schemaTarget.ReferenceClosed :=
                g.runActions?_preserves_referenceClosed
                  hg step.actions hschemaClosed hschemaRun
              obtain ⟨hitTarget, hhitRun, hhitTargetMatches⟩ :=
                exists_runActions_of_unfoldingEquivalent hg
                  hschemaTargetChild
                  hschemaTargetClosed hchildClosed hit.run
              exact Or.inl ⟨
                { actions := step.actions ++ hit.actions
                  remainder := hit.remainder
                  word_eq := by
                    calc
                      word = stem ++ suffix := hword
                      _ = step.actions.map Sum.inl ++ suffix :=
                        congrArg (· ++ suffix) step.actions_eq
                      _ = step.actions.map Sum.inl ++
                          (hit.actions.map Sum.inl ++
                            hit.remainder) :=
                        congrArg
                          (step.actions.map Sum.inl ++ ·)
                          hit.word_eq
                      _ =
                          (step.actions ++ hit.actions).map
                              Sum.inl ++ hit.remainder := by
                        simp [List.map_append, List.append_assoc]
                  index := hit.index
                  index_lt := hit.index_lt
                  target := hitTarget
                  run := by
                    unfold runActions?
                    rw [List.map_append, g.run?_append]
                    change
                      g.runActions? step.actions schema >>=
                          g.runActions? hit.actions =
                        some hitTarget
                    rw [hschemaRun]
                    exact hhitRun
                  target_matches :=
                    hhitTargetMatches.trans hit.target_matches }⟩
            · obtain ⟨finalIndex, hchildPath⟩ :=
                hschemaPath
              have hfirst :
                  schema.DescendantAt 1 schemaChild :=
                .child .root hrootNode hschemaChild
              have hfull :
                  schema.DescendantAt (depth + 1) finalIndex := by
                have := hfirst.trans hchildPath
                simpa [Nat.add_comm] using this
              exact Or.inr ⟨finalIndex, hfull⟩

/-- A root-sinking spine deeper than the schema's unfolding-depth bound must
contain a genuine symbolic run to an active variable. -/
public theorem exists_schemaVariableHit_of_repeatedlyRootSinksBy_of_depthBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {word : List (Label Action)} {bound depth : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hbound : schema.UnfoldingDepthAtMost bound)
    (hschemaClosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    (hsourceGround : source.Ground g.ranks)
    (hsourceSchema :
      source.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hdeep : bound < depth)
    (hsinks : g.RepeatedlyRootSinksBy source word depth) :
    Nonempty (SchemaVariableHitBy
      g schema width word) := by
  obtain ⟨support, hsupport⟩ := hwitness
  rcases repeatedlyRootSinksBy_variableHit_or_schemaDescendant
      hg hsupport hschemaClosed hwidth hsourceGround
      hsourceSchema hsinks with
    hhit | hschemaPath
  · exact hhit
  · obtain ⟨index, hdescendant⟩ := hschemaPath
    exact False.elim (by
      have hle := hbound hdescendant
      omega)

/-- Finite-schema specialization using the graph's node-count depth bound. -/
public theorem exists_schemaVariableHit_of_repeatedlyRootSinksBy
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {word : List (Label Action)} {depth : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hfinite : schema.UnfoldsFinite)
    (hschemaClosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    (hsourceGround : source.Ground g.ranks)
    (hsourceSchema :
      source.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hdeep : schema.nodes.length < depth)
    (hsinks : g.RepeatedlyRootSinksBy source word depth) :
    Nonempty (SchemaVariableHitBy
      g schema width word) :=
  g.exists_schemaVariableHit_of_repeatedlyRootSinksBy_of_depthBound
    hg hwitness hfinite.unfoldingDepthAtMost_nodes
      hschemaClosed hwidth hsourceGround hsourceSchema
      hdeep hsinks

end EncodedFirstOrderGrammar

end DCFEquivalence
