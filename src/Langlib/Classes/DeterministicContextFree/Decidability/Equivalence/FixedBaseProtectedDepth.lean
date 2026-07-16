module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.NonSinkingApplicationDepth
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteUnfoldingDepth

@[expose]
public section

/-!
# Protected depth from non-sinking at one fixed base

Local non-sinking of every intermediate symbolic residual is stronger than
the condition used in Proposition 49: contexts introduced above the fixed
base may be entered and later removed without the path ever sinking into an
immediate subterm of that base.

The correct proof observes the depth prefix one layer at a time.  Its outer
symbol template is instantiated by the compiled prefixes of the immediate
children.  A prefix that made the outer residual a variable would expose one
of those immediate concrete children and therefore sink from the fixed base.
Hence the outer residual remains application-rooted, adding one protected
layer above child schemas which already protect the remaining depth.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- A prefix witness is sufficient for application-depth preservation under
instantiation; unreachable garbage and a global syntactic variable bound are
irrelevant. -/
public theorem HasPrefixWitness.instantiate_applicationDepth
    {schema : RegularTerm} {arguments : List RegularTerm}
    {width depth : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hclosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    (hargumentsDepth : ∀ argument ∈ arguments,
      argument.ApplicationDepth depth)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    (schema.instantiate arguments).ApplicationDepth depth := by
  induction depth generalizing schema width with
  | zero => trivial
  | succ depth ih =>
      obtain ⟨support, hsupport⟩ := hwitness
      rcases hsupport.2 schema.root hsupport.1 with
        hvariable | happlication
      · obtain ⟨x, hnode, hx⟩ := hvariable
        have hxArguments : x < arguments.length := hx.trans_le hwidth
        let argument := arguments[x]
        have hargument : arguments[x]? = some argument :=
          List.getElem?_eq_getElem hxArguments
        have hrootNode :
            schema.nodeAt? schema.root = some (.inl x) := hnode
        have hinstance :
            (schema.instantiate arguments).UnfoldingEquivalent
              argument :=
          instantiate_unfoldingEquivalent_argument
            hrootNode hargument
            (hargumentsClosed argument
              (List.mem_of_getElem? hargument))
        exact hinstance.symm.applicationDepth
          (hargumentsDepth argument
            (List.mem_of_getElem? hargument))
      · obtain ⟨X, children, hnode, hchildren⟩ := happlication
        have hroot :
            schema.rootApplication? = some (X, children) := by
          unfold rootApplication? rootNode?
          rw [hnode]
        have hinstanceRoot :=
          instantiate_rootApplication?
            (arguments := arguments) hclosed hroot
        refine ⟨X,
          children.map (schema.resolveRHSRef arguments),
          hinstanceRoot, ?_⟩
        intro resolvedChild hresolvedChild
        obtain ⟨child, hchild, rfl⟩ :=
          List.mem_map.mp hresolvedChild
        have hchildBound :=
          hclosed.2 schema.root X children hnode child hchild
        have hchildWitness :
            (schema.withRoot child).HasPrefixWitness width := by
          refine ⟨support, ?_⟩
          constructor
          · exact hchildren child hchild
          · intro i hi
            simpa [withRoot, nodeAt?, nodes] using
              hsupport.2 i hi
        rw [instantiate_withRoot]
        apply ih hchildWitness
          (withRoot_referenceClosed hclosed hchildBound)
          hwidth
        · intro argument hargument
          exact (hargumentsDepth argument hargument).mono
            (Nat.le_succ depth)

/-- An application-rooted schema adds one protected layer above arguments
which already protect `depth` layers. -/
public theorem HasPrefixWitness.instantiate_applicationDepth_succ
    {schema : RegularTerm} {arguments : List RegularTerm}
    {width depth : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hclosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    {X : ℕ} {children : List ℕ}
    (hroot : schema.rootApplication? = some (X, children))
    (hargumentsDepth : ∀ argument ∈ arguments,
      argument.ApplicationDepth depth)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    (schema.instantiate arguments).ApplicationDepth (depth + 1) := by
  have hrootNode := nodeAt?_root_of_rootApplication? hroot
  have hinstanceRoot :=
    instantiate_rootApplication?
      (arguments := arguments) hclosed hroot
  refine ⟨X,
    children.map (schema.resolveRHSRef arguments),
    hinstanceRoot, ?_⟩
  obtain ⟨support, hsupport⟩ := hwitness
  intro resolvedChild hresolvedChild
  obtain ⟨child, hchild, rfl⟩ :=
    List.mem_map.mp hresolvedChild
  have hchildMem : child ∈ support := by
    rcases hsupport.2 schema.root hsupport.1 with
      hvariable | happlication
    · obtain ⟨x, hnode, _hx⟩ := hvariable
      rw [hrootNode] at hnode
      simp at hnode
    · obtain ⟨Y, witnessChildren, hnode,
          hwitnessChildren⟩ := happlication
      rw [hrootNode] at hnode
      simp only [Option.some.injEq, Sum.inr.injEq,
        Prod.mk.injEq] at hnode
      rcases hnode with ⟨rfl, rfl⟩
      exact hwitnessChildren child hchild
  have hchildBound :=
    hclosed.2 schema.root X children hrootNode child hchild
  have hchildWitness :
      (schema.withRoot child).HasPrefixWitness width := by
    refine ⟨support, ?_⟩
    constructor
    · exact hchildMem
    · intro i hi
      simpa [withRoot, nodeAt?, nodes] using
        hsupport.2 i hi
  rw [instantiate_withRoot]
  exact hchildWitness.instantiate_applicationDepth
    (withRoot_referenceClosed hclosed hchildBound)
    hwidth hargumentsDepth hargumentsClosed

/-- Root-variable indices of a witnessed schema belong to its active
prefix. -/
public theorem HasPrefixWitness.root_variable_lt
    {schema : RegularTerm} {width x : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hroot : schema.rootNode? = some (.inl x)) :
    x < width := by
  obtain ⟨support, hsupport⟩ := hwitness
  have hrootNode :
      schema.nodeAt? schema.root = some (.inl x) := by
    simpa [rootNode?] using hroot
  rcases hsupport.2 schema.root hsupport.1 with
    hvariable | happlication
  · obtain ⟨y, hnode, hy⟩ := hvariable
    have : y = x :=
      Sum.inl.inj (Option.some.inj (hnode.symm.trans hrootNode))
    simpa [this] using hy
  · obtain ⟨X, children, hnode, _hchildren⟩ := happlication
    rw [hrootNode] at hnode
    simp at hnode

private theorem collectHeads_applicationDepth
    (children : List DepthPrefix) (offset depth : ℕ)
    (hchildren : ∀ child ∈ children,
      child.head.ProtectedDepth depth) :
    ∀ head ∈ DepthPrefix.collectHeads children offset,
      head.toRegularTerm.ApplicationDepth depth := by
  induction children generalizing offset with
  | nil => simp [DepthPrefix.collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [DepthPrefix.collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | htail
      · exact FiniteHead.toRegularTerm_applicationDepth
          ((hchildren child (by simp)).shiftVariables)
      · exact ih (offset + child.tails.length)
          (fun tail htailMem =>
            hchildren tail (by simp [htailMem]))
          head htail

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- No prefix, including the complete word, reaches a symbolic variable
root. -/
@[expose] public def NoVariableAlong
    (g : EncodedFirstOrderGrammar Action)
    (schema : RegularTerm) (word : List Action) : Prop :=
  ∀ stem suffix,
    word = stem ++ suffix →
    ∀ residual x,
      g.runActions? stem schema = some residual →
      ¬residual.UnfoldingEquivalent (RegularTerm.variableTerm x)

/-- Inclusive absence of variables implies the proper-prefix form used by
symbolic reflection. -/
public theorem NoVariableAlong.noVariableBefore
    {g : EncodedFirstOrderGrammar Action}
    {schema : RegularTerm} {word : List Action}
    (hnoVariable : g.NoVariableAlong schema word) :
    g.NoVariableBefore schema word := by
  intro stem suffix hword _hsuffix residual x hrun
  exact hnoVariable stem suffix hword residual x hrun

private theorem HasPrefixWitness.runActions_of_someWellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema residual : RegularTerm} {width : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hschema : ∃ arity, schema.WellFormed g.ranks arity)
    {word : List Action}
    (hrun : g.runActions? word schema = some residual) :
    residual.HasPrefixWitness width := by
  induction word generalizing schema with
  | nil =>
      simp [runActions?] at hrun
      subst residual
      exact hwitness
  | cons action word ih =>
      cases hstep : g.step? (.inl action) schema with
      | none => simp [runActions?, hstep] at hrun
      | some next =>
          have htail :
              g.runActions? word next = some residual := by
            simpa [runActions?, hstep] using hrun
          have hnextWitness :=
            hwitness.stepAction hg
              (Classical.choose_spec hschema) hstep
          exact ih hnextWitness
            (stepAction_some_wellFormed hg hschema hstep)
            htail

private theorem runActions?_someWellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema residual : RegularTerm}
    (hschema : ∃ arity, schema.WellFormed g.ranks arity)
    {word : List Action}
    (hrun : g.runActions? word schema = some residual) :
    ∃ arity, residual.WellFormed g.ranks arity := by
  induction word generalizing schema with
  | nil =>
      simp [runActions?] at hrun
      subst residual
      exact hschema
  | cons action word ih =>
      cases hstep : g.step? (.inl action) schema with
      | none => simp [runActions?, hstep] at hrun
      | some next =>
          have htail :
              g.runActions? word next = some residual := by
            simpa [runActions?, hstep] using hrun
          exact ih
            (stepAction_some_wellFormed hg hschema hstep)
            htail

/-- Non-sinking from a fixed ground application excludes a variable residual
of its outer symbol template at every prefix. -/
public theorem symbolTemplate_noVariableAlong_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base : RegularTerm} (hbase : base.Ground g.ranks)
    {X : ℕ} {children : List ℕ}
    (hroot : base.rootApplication? = some (X, children))
    {word : List Action}
    (hnever : g.NeverSinksFromBase base word) :
    g.NoVariableAlong
      (RegularTerm.symbolTemplate X children.length) word := by
  let schema := RegularTerm.symbolTemplate X children.length
  let arguments := children.map base.withRoot
  have hrank : g.ranks[X]? = some children.length :=
    hbase.root_rank_arity hroot
  have hschemaWellFormed :
      schema.WellFormed g.ranks children.length := by
    simpa [schema] using
      RegularTerm.symbolTemplate_wellFormed hrank
  have hschemaWitness :
      schema.HasPrefixWitness children.length := by
    simpa [schema] using
      RegularTerm.symbolTemplate_hasPrefixWitness X children.length
  have hbaseClosed :=
    RegularTerm.referenceClosed_of_ground hbase
  have hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks := by
    intro argument hargument
    obtain ⟨child, hchild, rfl⟩ :=
      List.mem_map.mp hargument
    exact hbase.withRoot_descendant
      (.child .root
        (RegularTerm.nodeAt?_root_of_rootApplication? hroot)
        hchild)
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent base := by
    simpa [schema, arguments] using
      RegularTerm.symbolTemplate_instantiate_unfoldingEquivalent
        hbaseClosed hroot
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed
        hschemaWellFormed)
      hargumentsClosed
  intro stem suffix hword residual x hstemRun
  have hresidualWitness :=
    HasPrefixWitness.runActions_of_someWellFormed
      hg hschemaWitness ⟨_, hschemaWellFormed⟩ hstemRun
  intro hresidualVariable
  have hresidualRoot :
      residual.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hresidualVariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  have hxChildren : x < children.length :=
    hresidualWitness.root_variable_lt hresidualRoot
  have hxArguments : x < arguments.length := by
    simpa [arguments] using hxChildren
  let child := children[x]
  let argument := arguments[x]
  have hargument : arguments[x]? = some argument :=
    List.getElem?_eq_getElem hxArguments
  have hargumentEq :
      argument = base.withRoot child := by
    simp [argument, child, arguments]
  have hresidualNode :
      residual.nodeAt? residual.root = some (.inl x) := by
    simpa [RegularTerm.rootNode?] using hresidualRoot
  have hresidualInstance :
      (residual.instantiate arguments).UnfoldingEquivalent
        argument :=
    RegularTerm.instantiate_unfoldingEquivalent_argument
      hresidualNode hargument
      (hargumentsClosed argument
        (List.mem_of_getElem? hargument))
  obtain ⟨instanceTarget, hinstanceRun,
      hresidualInstantiation⟩ :=
    g.runActions?_instantiate hg stem hschemaWellFormed
      hargumentsClosed hstemRun
  obtain ⟨baseTarget, hbaseRun, hbaseTargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      hinstanceEquivalent.symm hbaseClosed hinstanceClosed
      hinstanceRun
  have hbaseTargetChild :
      baseTarget.UnfoldingEquivalent (base.withRoot child) := by
    simpa [hargumentEq] using
      hbaseTargetEquivalent.trans
        (hresidualInstantiation.symm.trans
          hresidualInstance)
  have hstemNonempty : stem ≠ [] := by
    intro hnil
    subst stem
    simp [runActions?] at hstemRun
    subst residual
    have hschemaRoot :=
      RegularTerm.symbolTemplate_rootApplication?
        X children.length
    unfold RegularTerm.rootApplication?
      RegularTerm.rootNode? at hschemaRoot
    rw [hresidualNode] at hschemaRoot
    simp at hschemaRoot
  apply hnever stem suffix hword
  apply sinksBy_of_exposesAtDepth
  · simpa using hstemNonempty
  · refine ⟨base.withRoot child, baseTarget, ?_, ?_, ?_⟩
    · exact ⟨child,
        .child .root
          (RegularTerm.nodeAt?_root_of_rootApplication? hroot)
          (List.getElem_mem hxChildren),
        rfl⟩
    · simpa [runActions?] using hbaseRun
    · exact hbaseTargetChild

/-- A residual of the compiled depth prefix retains the full prefix depth
whenever no prefix of the corresponding concrete run sinks from the fixed
ground base. -/
public theorem depthPrefix_residual_applicationDepth_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base residual : RegularTerm}
    (hbase : base.Ground g.ranks)
    (depth : ℕ) {word : List Action}
    (hrun :
      g.runActions? word
        (base.depthPrefix depth).head.toRegularTerm =
          some residual)
    (hnever : g.NeverSinksFromBase base word) :
    residual.ApplicationDepth depth := by
  cases depth with
  | zero => trivial
  | succ depth =>
      obtain ⟨X, children, hroot⟩ :=
        hbase.exists_rootApplication
      let childPrefixes :=
        children.map fun child =>
          (base.withRoot child).depthPrefix depth
      let heads := DepthPrefix.collectHeads childPrefixes 0
      let arguments := heads.map FiniteHead.toRegularTerm
      let outer := RegularTerm.symbolTemplate X children.length
      have hrootNode :=
        RegularTerm.nodeAt?_root_of_rootApplication? hroot
      have hchildrenGround :
          ∀ child ∈ children,
            (base.withRoot child).Ground g.ranks := by
        intro child hchild
        exact hbase.withRoot_descendant
          (.child .root hrootNode hchild)
      have hheadsDepth :
          ∀ head ∈ heads,
            head.toRegularTerm.ApplicationDepth depth := by
        apply RegularTerm.collectHeads_applicationDepth
        intro childPrefix hchildPrefix
        obtain ⟨child, hchild, rfl⟩ :=
          List.mem_map.mp hchildPrefix
        exact FiniteHead.depthPrefix_head_protectedDepth
          (hchildrenGround child hchild) depth
      have hargumentsDepth :
          ∀ argument ∈ arguments,
            argument.ApplicationDepth depth := by
        intro argument hargument
        obtain ⟨head, hhead, rfl⟩ :=
          List.mem_map.mp hargument
        exact hheadsDepth head hhead
      have hargumentsClosed :
          ∀ argument ∈ arguments,
            argument.ReferenceClosed := by
        intro argument hargument
        obtain ⟨head, _hhead, rfl⟩ :=
          List.mem_map.mp hargument
        exact FiniteHead.toRegularTerm_referenceClosed head
      have hargumentsLength :
          arguments.length = children.length := by
        simp [arguments, heads, childPrefixes]
      have hrank : g.ranks[X]? = some children.length :=
        hbase.root_rank_arity hroot
      have houterWellFormed :
          outer.WellFormed g.ranks arguments.length := by
        rw [hargumentsLength]
        simpa [outer] using
          RegularTerm.symbolTemplate_wellFormed hrank
      have houterWitness :
          outer.HasPrefixWitness arguments.length := by
        rw [hargumentsLength]
        simpa [outer] using
          RegularTerm.symbolTemplate_hasPrefixWitness X children.length
      have hsymbolicRun :
          g.runActions? word (outer.instantiate arguments) =
            some residual := by
        rw [RegularTerm.depthPrefix_succ_of_rootApplication hroot] at hrun
        simpa [DepthPrefix.assemble, childPrefixes, heads,
          arguments, outer, FiniteHead.toRegularTerm] using hrun
      have hnoVariable :
          g.NoVariableAlong outer word := by
        simpa [outer] using
          symbolTemplate_noVariableAlong_of_neverSinksFromBase
            hg hbase hroot hnever
      obtain ⟨outerResidual, houterRun, houterInstance⟩ :=
        runActions?_reflects_instantiation_of_noVariableBefore
          hg word ⟨_, houterWellFormed⟩ hargumentsClosed
          hsymbolicRun hnoVariable.noVariableBefore
      have houterResidualWitness :=
        HasPrefixWitness.runActions_of_someWellFormed
          hg houterWitness ⟨_, houterWellFormed⟩ houterRun
      have houterResidualClosed : outerResidual.ReferenceClosed := by
        obtain ⟨arity, hwellFormed⟩ :=
          runActions?_someWellFormed
            hg ⟨_, houterWellFormed⟩ houterRun
        exact RegularTerm.referenceClosed_of_wellFormed hwellFormed
      have houterResidualRoot :
          ∃ Y outerChildren,
            outerResidual.rootApplication? =
              some (Y, outerChildren) := by
        obtain ⟨support, hsupport⟩ := houterResidualWitness
        rcases hsupport.2 outerResidual.root hsupport.1 with
          hvariable | happlication
        · obtain ⟨x, hnode, _hx⟩ := hvariable
          have hrootVariable :
              outerResidual.rootNode? = some (.inl x) := by
            simpa [RegularTerm.rootNode?] using hnode
          have hequivalent :=
            unfoldingEquivalent_variableTerm_of_rootNode?
              hrootVariable
          exact False.elim
            ((hnoVariable word [] (by simp)
              outerResidual x houterRun) hequivalent)
        · obtain ⟨Y, outerChildren, hnode, _hchildren⟩ :=
            happlication
          exact ⟨Y, outerChildren, by
            unfold RegularTerm.rootApplication?
              RegularTerm.rootNode?
            rw [hnode]⟩
      obtain ⟨Y, outerChildren, houterRoot⟩ :=
        houterResidualRoot
      have houterDepth :
          (outerResidual.instantiate arguments)
            |>.ApplicationDepth (depth + 1) := by
        exact houterResidualWitness.instantiate_applicationDepth_succ
          houterResidualClosed (by omega) houterRoot
          hargumentsDepth hargumentsClosed
      exact houterInstance.applicationDepth houterDepth

/-- The concrete fixed-tail construction therefore produces a protected
residual from fixed-base non-sinking alone; no local-sink reflection premise
is required. -/
public theorem exists_protectedFixedTailResidual_of_fixedBaseNonSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler target : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) {word : List Action}
    (hrun : g.runActions? word term = some target)
    (hnoExposure : g.NoDepthExposureBefore term depth word)
    (hnever : g.NeverSinksFromBase term word) :
    Nonempty
      (ProtectedFixedTailResidual
        g term filler depth word target) := by
  obtain ⟨residual⟩ :=
    exists_fixedTailResidual hg hterm hfiller
      depth hrun hnoExposure
  exact ⟨
    { fixedTail := residual
      applicationDepth :=
        depthPrefix_residual_applicationDepth_of_neverSinksFromBase
          hg hterm depth residual.symbolic_run hnever }⟩

namespace FixedTailPivotPresentation

/-- Family-level Proposition-49 form: if no retained concrete pivot prefix
sinks from the fixed base, every residual schema over the common depth-prefix
tuple protects the full cutoff depth. -/
public theorem schemas_applicationDepth_of_fixedBaseNonSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (hnever : ∀ j,
      g.NeverSinksFromBase base (presentation.actions j)) :
    ∀ j, (presentation.schema j).ApplicationDepth
      presentation.depth := by
  intro j
  exact depthPrefix_residual_applicationDepth_of_neverSinksFromBase
    hg presentation.base_ground presentation.depth
    (presentation.residual j).symbolic_run (hnever j)

end FixedTailPivotPresentation

end EncodedFirstOrderGrammar

end DCFEquivalence
