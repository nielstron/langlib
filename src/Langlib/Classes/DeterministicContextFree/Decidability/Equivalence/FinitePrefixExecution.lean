module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ExposedEquations
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteHeadPrefixes

@[expose]
public section

/-!
# Bounded symbolic execution through finite prefixes

The structural invariant `ApplicationDepth d` says that no variable is
reachable in fewer than `d` child edges.  An ordinary root rewrite can lower
that depth by at most one, since right-hand-side variables select only
immediate arguments of the rewritten root.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Every node in the unfolding strictly above depth `depth` is an
application. -/
@[expose] public def ApplicationDepth : RegularTerm → ℕ → Prop
  | _, 0 => True
  | term, depth + 1 =>
      ∃ X children,
        term.rootApplication? = some (X, children) ∧
          ∀ child ∈ children,
            (term.withRoot child).ApplicationDepth depth

@[simp] public theorem applicationDepth_zero
    (term : RegularTerm) :
    term.ApplicationDepth 0 := trivial

public theorem ApplicationDepth.mono
    {term : RegularTerm} {small large : ℕ}
    (hdepth : term.ApplicationDepth large)
    (hle : small ≤ large) :
    term.ApplicationDepth small := by
  induction small generalizing term large with
  | zero => trivial
  | succ small ih =>
      cases large with
      | zero => omega
      | succ large =>
          obtain ⟨X, children, hroot, hchildren⟩ := hdepth
          refine ⟨X, children, hroot, ?_⟩
          intro child hchild
          exact ih (hchildren child hchild) (by omega)

public theorem UnfoldingEquivalent.applicationDepth
    {left right : RegularTerm} (hequivalent : left.UnfoldingEquivalent right)
    {depth : ℕ} (hleft : left.ApplicationDepth depth) :
    right.ApplicationDepth depth := by
  induction depth generalizing left right with
  | zero => trivial
  | succ depth ih =>
      obtain ⟨X, leftChildren, hleftRoot, hleftChildren⟩ := hleft
      obtain ⟨rightChildren, hrightRoot, hchildrenEquivalent⟩ :=
        rootApplication?_of_unfoldingEquivalent hequivalent hleftRoot
      refine ⟨X, rightChildren, hrightRoot, ?_⟩
      intro rightChild hrightChild
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrightChild
      have hlength := List.Forall₂.length_eq hchildrenEquivalent
      have hiRight : i < rightChildren.length :=
        (List.getElem?_eq_some_iff.mp hi).1
      have hiLeft : i < leftChildren.length := by omega
      let leftChild := leftChildren[i]
      have hleftChildMem : leftChild ∈ leftChildren :=
        List.getElem_mem hiLeft
      have hrightGet :
          rightChildren.get ⟨i, hiRight⟩ = rightChild := by
        exact Option.some.inj
          ((List.getElem?_eq_getElem hiRight).symm.trans hi)
      have hchildrenGet :=
        (List.forall₂_iff_get.mp hchildrenEquivalent).2
          i hiLeft hiRight
      rw [hrightGet] at hchildrenGet
      have hpointed :
          (left.withRoot leftChild).UnfoldingEquivalent
            (right.withRoot rightChild) :=
        (withRoot_unfoldingEquivalent_iff_bisimilarAt
          left right leftChild rightChild).2 hchildrenGet
      exact ih hpointed
        (hleftChildren leftChild hleftChildMem)

public theorem UnfoldingEquivalent.applicationDepth_iff
    {left right : RegularTerm} (hequivalent : left.UnfoldingEquivalent right)
    (depth : ℕ) :
    left.ApplicationDepth depth ↔ right.ApplicationDepth depth :=
  ⟨hequivalent.applicationDepth,
    hequivalent.symm.applicationDepth⟩

/-- A reachable-ground regular tree has applications at every finite depth. -/
public theorem Ground.applicationDepth
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    term.ApplicationDepth depth := by
  induction depth generalizing term with
  | zero => trivial
  | succ depth ih =>
      obtain ⟨X, children, hroot⟩ := hground.exists_rootApplication
      have hrootNode := nodeAt?_root_of_rootApplication? hroot
      refine ⟨X, children, hroot, ?_⟩
      intro child hchild
      exact ih (hground.withRoot_descendant
        (.child .root hrootNode hchild))

private theorem withRoot_wellFormed
    {ranks : List ℕ} {arity : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks arity)
    {i : ℕ} (hi : i < term.nodes.length) :
    (term.withRoot i).WellFormed ranks arity := by
  unfold WellFormed wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨?_, ?_⟩
  · simpa [withRoot, root, nodes] using decide_eq_true hi
  · simpa [withRoot, nodes] using hterm.2

private theorem variable_lt_of_wellFormed
    {ranks : List ℕ} {arity : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks arity)
    {i x : ℕ} (hnode : term.nodeAt? i = some (.inl x)) :
    x < arity := by
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inl x : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  simpa [nodeWellFormedCode] using of_decide_eq_true hwell

/-- Substitution by schemas of depth `d` preserves that depth. -/
public theorem instantiate_applicationDepth
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {depth : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ApplicationDepth depth)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    (schema.instantiate arguments).ApplicationDepth depth := by
  induction depth generalizing schema with
  | zero => trivial
  | succ depth ih =>
      have hschemaClosed := referenceClosed_of_wellFormed hschema
      cases hroot : schema.rootNode? with
      | none =>
          have := hschemaClosed.1
          unfold rootNode? nodeAt? at hroot
          rw [List.getElem?_eq_none_iff] at hroot
          omega
      | some node =>
          cases node with
          | inl x =>
              have hx : x < arguments.length :=
                variable_lt_of_wellFormed hschema
                  (by simpa [rootNode?] using hroot)
              let argument := arguments[x]
              have hargument : arguments[x]? = some argument :=
                List.getElem?_eq_getElem hx
              have hinstance :=
                instantiate_unfoldingEquivalent_argument
                  (by simpa [rootNode?] using hroot)
                  hargument
                  (hargumentsClosed argument
                    (List.mem_of_getElem? hargument))
              exact hinstance.symm.applicationDepth
                (harguments argument
                  (List.mem_of_getElem? hargument))
          | inr app =>
              rcases app with ⟨X, children⟩
              have hrootApplication :
                  schema.rootApplication? = some (X, children) := by
                simp [rootApplication?, hroot]
              have hinstRoot := instantiate_rootApplication?
                (arguments := arguments) hschemaClosed hrootApplication
              refine ⟨X,
                children.map (schema.resolveRHSRef arguments),
                hinstRoot, ?_⟩
              intro resolvedChild hresolvedChild
              obtain ⟨child, hchild, rfl⟩ :=
                List.mem_map.mp hresolvedChild
              rw [instantiate_withRoot]
              apply ih
              · exact withRoot_wellFormed hschema
                  (hschemaClosed.2 schema.root X children
                    (by simpa [rootNode?] using hroot)
                    child hchild)
              · intro argument hargument
                exact (harguments argument hargument).mono
                  (Nat.le_succ depth)

end RegularTerm

namespace RegularTerm

/-- Instantiating an application template by depth-`d` argument schemas adds
one protected application layer. -/
public theorem symbolTemplate_instantiate_applicationDepth
    {X arity depth : ℕ} {arguments : List RegularTerm}
    (hlength : arguments.length = arity)
    (harguments : ∀ argument ∈ arguments,
      argument.ApplicationDepth depth)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    ((symbolTemplate X arity).instantiate arguments)
      |>.ApplicationDepth (depth + 1) := by
  let template := symbolTemplate X arity
  have htemplateClosed := symbolTemplate_referenceClosed X arity
  have htemplateRoot :=
    symbolTemplate_rootApplication? X arity
  have hroot := instantiate_rootApplication?
    (arguments := arguments) htemplateClosed htemplateRoot
  refine ⟨X,
    ((List.range arity).map (fun i => i + 1)).map
      (template.resolveRHSRef arguments),
    by simpa [template] using hroot, ?_⟩
  intro resolvedChild hresolvedChild
  obtain ⟨templateChild, htemplateChild, rfl⟩ :=
    List.mem_map.mp hresolvedChild
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp htemplateChild
  have hiArity : i < arity := by
    simpa using hi
  have hiArguments : i < arguments.length := by
    simpa [hlength] using hiArity
  let argument := arguments[i]
  have hargument : arguments[i]? = some argument :=
    List.getElem?_eq_getElem hiArguments
  have hvariable :
      (template.withRoot (i + 1)).nodeAt?
        (template.withRoot (i + 1)).root =
          some (.inl i) := by
    simpa [template] using
      symbolTemplate_variableNode X arity i hiArity
  have hinstance :
      ((template.withRoot (i + 1)).instantiate arguments)
        |>.UnfoldingEquivalent argument := by
    exact instantiate_unfoldingEquivalent_argument
      hvariable hargument
      (hargumentsClosed argument
        (List.mem_of_getElem? hargument))
  change ((template.instantiate arguments).withRoot
    (template.resolveRHSRef arguments (i + 1)))
      |>.ApplicationDepth depth
  rw [instantiate_withRoot]
  exact hinstance.symm.applicationDepth
    (harguments argument
      (List.mem_of_getElem? hargument))

end RegularTerm

namespace FiniteHead

/-- Every boundary variable of a finite head occurs at depth at least
`depth`. -/
@[expose] public def ProtectedDepth : FiniteHead → ℕ → Prop
  | _, 0 => True
  | .var _, _ + 1 => False
  | .app _ children, depth + 1 =>
      ∀ child ∈ children, child.ProtectedDepth depth

public theorem ProtectedDepth.shiftVariables
    {head : FiniteHead} {depth offset : ℕ}
    (hdepth : head.ProtectedDepth depth) :
    (head.shiftVariables offset).ProtectedDepth depth := by
  induction depth generalizing head with
  | zero => trivial
  | succ depth ih =>
      cases head with
      | var x => contradiction
      | app X children =>
          simp only [ProtectedDepth] at hdepth
          simp only [FiniteHead.shiftVariables, ProtectedDepth]
          change ∀ shiftedChild : FiniteHead,
            shiftedChild ∈
              children.map (FiniteHead.shiftVariables offset) →
            shiftedChild.ProtectedDepth depth
          intro shiftedChild hshiftedChild
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp hshiftedChild
          exact ih (hdepth child hchild)

private theorem collectHeads_protectedDepth
    (children : List DepthPrefix) (offset depth : ℕ)
    (hchildren : ∀ child ∈ children,
      child.head.ProtectedDepth depth) :
    ∀ head ∈ DepthPrefix.collectHeads children offset,
      head.ProtectedDepth depth := by
  induction children generalizing offset with
  | nil => simp [DepthPrefix.collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [DepthPrefix.collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | htail
      · exact (hchildren child (by simp)).shiftVariables
      · exact ih (offset + child.tails.length)
          (fun tail htailMem =>
            hchildren tail (by simp [htailMem]))
          head htail

/-- The finite head extracted at depth `d` keeps every boundary variable at
depth at least `d`. -/
public theorem depthPrefix_head_protectedDepth
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    (term.depthPrefix depth).head.ProtectedDepth depth := by
  induction depth generalizing term with
  | zero => trivial
  | succ depth ih =>
      obtain ⟨X, children, hroot⟩ := hground.exists_rootApplication
      rw [RegularTerm.depthPrefix_succ_of_rootApplication hroot]
      unfold DepthPrefix.assemble
      simp only [ProtectedDepth]
      apply collectHeads_protectedDepth
      intro childPrefix hchildPrefix
      obtain ⟨child, hchild, rfl⟩ :=
        List.mem_map.mp hchildPrefix
      have hrootNode :=
        RegularTerm.nodeAt?_root_of_rootApplication? hroot
      exact ih (hground.withRoot_descendant
        (.child .root hrootNode hchild))

/-- Compiling a protected finite head preserves its protected application
depth in the regular graph semantics. -/
public theorem toRegularTerm_applicationDepth
    {head : FiniteHead} {depth : ℕ}
    (hdepth : head.ProtectedDepth depth) :
    head.toRegularTerm.ApplicationDepth depth := by
  induction depth generalizing head with
  | zero => trivial
  | succ depth ih =>
      cases head with
      | var x => contradiction
      | app X children =>
          simp only [ProtectedDepth] at hdepth
          rw [toRegularTerm]
          apply RegularTerm.symbolTemplate_instantiate_applicationDepth
          · simp
          · intro argument hargument
            obtain ⟨child, hchild, rfl⟩ :=
              List.mem_map.mp hargument
            exact ih (hdepth child hchild)
          · intro argument hargument
            obtain ⟨child, hchild, rfl⟩ :=
              List.mem_map.mp hargument
            exact toRegularTerm_referenceClosed child

/-- The compiled schema of a ground depth prefix protects its tails for the
full requested depth. -/
public theorem depthPrefix_schema_applicationDepth
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    (term.depthPrefix depth).head.toRegularTerm.ApplicationDepth depth :=
  toRegularTerm_applicationDepth
    (depthPrefix_head_protectedDepth hground depth)

end FiniteHead

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private theorem sum_withRoot_nodes_length
    (source : RegularTerm) (children : List ℕ) :
    ((children.map source.withRoot).map
      fun argument => argument.nodes.length).sum =
      children.length * source.nodes.length := by
  induction children with
  | nil => simp
  | cons child children ih =>
      simp only [List.map_cons, List.sum_cons,
        RegularTerm.withRoot_nodes, List.length_cons]
      rw [ih, Nat.succ_mul, Nat.add_comm]

/-- Maximum raw graph size of a grammar right-hand side. -/
@[expose] public def rhsNodeBound
    (g : EncodedFirstOrderGrammar Action) : ℕ :=
  (g.rawRules.map fun rule => rule.rhs.nodes.length).foldr max 0

/-- Uniform graph-size recurrence for an ordinary symbolic run. -/
@[expose] public def residualNodeBound
    (g : EncodedFirstOrderGrammar Action) : ℕ → ℕ → ℕ
  | 0, initial => initial
  | steps + 1, initial =>
      g.residualNodeBound steps
        (g.rhsNodeBound +
          (g.ranks.foldr max 0) * initial)

public theorem rhs_nodes_length_le_rhsNodeBound
    {g : EncodedFirstOrderGrammar Action}
    {X : ℕ} {action : Action} {rhs : RegularTerm}
    (hrule : g.ruleLookup X action = some rhs) :
    rhs.nodes.length ≤ g.rhsNodeBound := by
  unfold ruleLookup at hrule
  obtain ⟨rule, hfind, hrhs⟩ :=
    Option.map_eq_some_iff.mp hrule
  subst rhs
  unfold rhsNodeBound
  apply List.le_max_of_le
  · exact List.mem_map.mpr
      ⟨rule, g.findRule_mem hfind, rfl⟩
  · exact le_refl _

/-- One ordinary symbolic rewrite lowers the protected application depth by at
most one. -/
public theorem stepAction_preserves_applicationDepth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {action : Action} {depth : ℕ}
    (hsourceWellFormed :
      ∃ arity, source.WellFormed g.ranks arity)
    (hdepth : source.ApplicationDepth (depth + 1))
    (hstep : g.step? (.inl action) source = some target) :
    target.ApplicationDepth depth := by
  obtain ⟨sourceArity, hsourceWellFormed⟩ := hsourceWellFormed
  obtain ⟨X, children, hroot, hchildrenDepth⟩ := hdepth
  change g.rootRewrite? action source = some target at hstep
  unfold rootRewrite? at hstep
  rw [hroot] at hstep
  obtain ⟨rhs, hrule, rfl⟩ := Option.map_eq_some_iff.mp hstep
  obtain ⟨rank, hrank, hrhsWellFormed⟩ :=
    selected_rhs_wellFormed hg hrule
  have hrootNode :=
    RegularTerm.nodeAt?_root_of_rootApplication? hroot
  have hsourceNodeWellFormed := hsourceWellFormed
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hsourceNodeWellFormed
  rw [Bool.and_eq_true] at hsourceNodeWellFormed
  have hrootMem : (.inr (X, children) : RawNode) ∈ source.nodes :=
    List.mem_of_getElem? hrootNode
  have hrootWell :=
    (List.all_eq_true.mp hsourceNodeWellFormed.2) _ hrootMem
  unfold RegularTerm.nodeWellFormedCode at hrootWell
  cases hsourceRank : g.ranks[X]? with
  | none => simp [hsourceRank] at hrootWell
  | some sourceRank =>
      simp only [hsourceRank, Bool.and_eq_true,
        decide_eq_true_eq] at hrootWell
      have hrankEq : rank = sourceRank :=
        Option.some.inj (hrank.symm.trans hsourceRank)
      have hrhsChildren :
          rhs.WellFormed g.ranks children.length := by
        rw [hrootWell.1, ← hrankEq]
        exact hrhsWellFormed
      apply RegularTerm.instantiate_applicationDepth
        (arguments := children.map source.withRoot)
        (by simpa using hrhsChildren)
      · intro argument hargument
        obtain ⟨child, hchild, rfl⟩ :=
          List.mem_map.mp hargument
        exact hchildrenDepth child hchild
      · intro argument hargument
        obtain ⟨child, hchild, rfl⟩ :=
          List.mem_map.mp hargument
        exact RegularTerm.withRoot_referenceClosed
          (RegularTerm.referenceClosed_of_wellFormed
            hsourceWellFormed)
          ((RegularTerm.referenceClosed_of_wellFormed
            hsourceWellFormed).2 source.root X children
              hrootNode child hchild)

/-- Ordinary symbolic rewriting preserves some finite variable bound. -/
public theorem stepAction_some_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {action : Action}
    (hsource : ∃ arity, source.WellFormed g.ranks arity)
    (hstep : g.step? (.inl action) source = some target) :
    ∃ arity, target.WellFormed g.ranks arity := by
  obtain ⟨sourceArity, hsourceWellFormed⟩ := hsource
  change g.rootRewrite? action source = some target at hstep
  unfold rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, rfl⟩ :=
        Option.map_eq_some_iff.mp hstep
      obtain ⟨rank, hrank, hrhsWellFormed⟩ :=
        selected_rhs_wellFormed hg hrule
      have hrootNode :=
        RegularTerm.nodeAt?_root_of_rootApplication? hroot
      have hsourceNodeWellFormed := hsourceWellFormed
      unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hsourceNodeWellFormed
      rw [Bool.and_eq_true] at hsourceNodeWellFormed
      have hrootMem : (.inr (X, children) : RawNode) ∈ source.nodes :=
        List.mem_of_getElem? hrootNode
      have hrootWell :=
        (List.all_eq_true.mp hsourceNodeWellFormed.2) _ hrootMem
      unfold RegularTerm.nodeWellFormedCode at hrootWell
      cases hsourceRank : g.ranks[X]? with
      | none => simp [hsourceRank] at hrootWell
      | some sourceRank =>
          simp only [hsourceRank, Bool.and_eq_true,
            decide_eq_true_eq] at hrootWell
          have hrankEq : rank = sourceRank :=
            Option.some.inj (hrank.symm.trans hsourceRank)
          have hrhsChildren :
              rhs.WellFormed g.ranks children.length := by
            rw [hrootWell.1, ← hrankEq]
            exact hrhsWellFormed
          have hargumentsWellFormed :
              ∀ argument ∈ children.map source.withRoot,
                argument.WellFormed g.ranks sourceArity := by
            intro argument hargument
            obtain ⟨child, hchild, rfl⟩ :=
              List.mem_map.mp hargument
            apply RegularTerm.withRoot_wellFormed
              (ranks := g.ranks) (arity := sourceArity)
              hsourceWellFormed
            exact (RegularTerm.referenceClosed_of_wellFormed
              hsourceWellFormed).2 source.root X children
                hrootNode child hchild
          have hresult := RegularTerm.instantiate_wellFormed_max
            (schema := rhs)
            (arguments := children.map source.withRoot)
            (variableBound := sourceArity)
            (by simpa using hrhsChildren)
            hargumentsWellFormed
          exact ⟨max children.length sourceArity, by
            simpa using hresult⟩

/-- One ordinary rewrite obeys the grammar-uniform graph-size recurrence. -/
public theorem stepAction_nodes_length_le
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {action : Action}
    (hsource : ∃ arity, source.WellFormed g.ranks arity)
    (hstep : g.step? (.inl action) source = some target) :
    target.nodes.length ≤
      g.rhsNodeBound +
        (g.ranks.foldr max 0) * source.nodes.length := by
  obtain ⟨sourceArity, hsourceWellFormed⟩ := hsource
  have hsourceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hsourceWellFormed
  change g.rootRewrite? action source = some target at hstep
  unfold rootRewrite? at hstep
  cases hroot : source.rootApplication? with
  | none => simp [hroot] at hstep
  | some application =>
      rcases application with ⟨X, children⟩
      simp only [hroot] at hstep
      obtain ⟨rhs, hrule, htarget⟩ :=
        Option.map_eq_some_iff.mp hstep
      subst target
      rw [RegularTerm.instantiate_nodes_length]
      have hrootNode :=
        RegularTerm.nodeAt?_root_of_rootApplication? hroot
      obtain ⟨rank, hrank, hchildrenLength⟩ :=
        rank_arity_of_wellFormed hsourceWellFormed hrootNode
      have hrankMax : rank ≤ g.ranks.foldr max 0 :=
        List.le_max_of_le (List.mem_of_getElem? hrank) (le_refl _)
      have hargumentsLength :
          ((children.map source.withRoot).map
            fun argument => argument.nodes.length).sum =
            children.length * source.nodes.length := by
        exact sum_withRoot_nodes_length source children
      rw [hargumentsLength]
      apply Nat.add_le_add
      · exact rhs_nodes_length_le_rhsNodeBound hrule
      · apply Nat.mul_le_mul_right
        simpa [hchildrenLength] using hrankMax

/-- A finite ordinary symbolic run consumes at most its length from the
protected application depth. -/
public theorem runActions?_preserves_applicationDepth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {word : List Action} {depth : ℕ}
    (hsource : ∃ arity, source.WellFormed g.ranks arity)
    (hdepth : source.ApplicationDepth (word.length + depth))
    (hrun : g.runActions? word source = some target) :
    target.ApplicationDepth depth := by
  induction word generalizing source with
  | nil =>
      simp [runActions?] at hrun
      subst target
      simpa using hdepth
  | cons action word ih =>
      cases hstep : g.step? (.inl action) source with
      | none => simp [runActions?, hstep] at hrun
      | some next =>
          have htail : g.runActions? word next = some target := by
            simpa [runActions?, hstep] using hrun
          have hnextDepth : next.ApplicationDepth
              (word.length + depth) := by
            apply stepAction_preserves_applicationDepth hg hsource
              (depth := word.length + depth)
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hdepth
            · exact hstep
          exact ih (stepAction_some_wellFormed hg hsource hstep)
            hnextDepth htail

/-- The raw graph size after a finite ordinary run is bounded solely by its
length, the grammar, and a bound for the source graph. -/
public theorem runActions?_nodes_length_le
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {word : List Action} {initialBound : ℕ}
    (hsource : ∃ arity, source.WellFormed g.ranks arity)
    (hsourceSize : source.nodes.length ≤ initialBound)
    (hrun : g.runActions? word source = some target) :
    target.nodes.length ≤
      g.residualNodeBound word.length initialBound := by
  induction word generalizing source initialBound with
  | nil =>
      simp [runActions?] at hrun
      subst target
      simpa [residualNodeBound] using hsourceSize
  | cons action word ih =>
      cases hstep : g.step? (.inl action) source with
      | none => simp [runActions?, hstep] at hrun
      | some next =>
          have htail : g.runActions? word next = some target := by
            simpa [runActions?, hstep] using hrun
          have hnextWellFormed :=
            stepAction_some_wellFormed hg hsource hstep
          have hnextSize :
              next.nodes.length ≤
                g.rhsNodeBound +
                  (g.ranks.foldr max 0) * initialBound := by
            exact (stepAction_nodes_length_le hsource hstep).trans
              (Nat.add_le_add_left
                (Nat.mul_le_mul_left
                  (g.ranks.foldr max 0) hsourceSize)
                g.rhsNodeBound)
          simpa [residualNodeBound] using
            ih hnextWellFormed hnextSize htail

/-- Ordinary execution is congruent for equality of regular-tree
unfoldings. -/
public theorem runActions?_congr_unfoldingEquivalent
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
                    ih
                      (step?_preserves_referenceClosed hg hleft hleftStep)
                      (step?_preserves_referenceClosed hg hright hrightStep)
                      htargets

/-- If an instance of an application-root schema has an ordinary successor,
then the schema itself has a successor under the same action. -/
public theorem exists_stepAction_of_instantiate_step
    {g : EncodedFirstOrderGrammar Action}
    {source concreteTarget : RegularTerm} {action : Action}
    {arguments : List RegularTerm}
    (hsource : source.ReferenceClosed)
    (hdepth : source.ApplicationDepth 1)
    (hstep :
      g.step? (.inl action) (source.instantiate arguments) =
        some concreteTarget) :
    ∃ target, g.step? (.inl action) source = some target := by
  obtain ⟨X, children, hroot, _⟩ := hdepth
  have hrootInstance := RegularTerm.instantiate_rootApplication?
    (arguments := arguments) hsource hroot
  change g.rootRewrite? action (source.instantiate arguments) =
    some concreteTarget at hstep
  change ∃ target, g.rootRewrite? action source = some target
  unfold rootRewrite? at hstep ⊢
  rw [hrootInstance] at hstep
  rw [hroot]
  cases hrule : g.ruleLookup X action with
  | none => simp [hrule] at hstep
  | some rhs =>
      exact ⟨rhs.instantiate (children.map source.withRoot), by
        simp [hrule]⟩

/-- A concrete run of a sufficiently deep schema instance reflects to a
symbolic run of the open schema. -/
public theorem runActions?_reflects_instantiation
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema concrete : RegularTerm} {arguments : List RegularTerm}
    (word : List Action)
    (hschema : ∃ arity, schema.WellFormed g.ranks arity)
    (hdepth : schema.ApplicationDepth word.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hrun :
      g.runActions? word (schema.instantiate arguments) =
        some concrete) :
    ∃ residual, g.runActions? word schema = some residual := by
  induction word generalizing schema concrete with
  | nil =>
      exact ⟨schema, by simp [runActions?]⟩
  | cons action word ih =>
      cases hconcreteStep :
          g.step? (.inl action) (schema.instantiate arguments) with
      | none =>
          simp [runActions?, hconcreteStep] at hrun
      | some concreteNext =>
          have htail :
              g.runActions? word concreteNext = some concrete := by
            simpa [runActions?, hconcreteStep] using hrun
          have hschemaDepthOne :
              schema.ApplicationDepth 1 :=
            hdepth.mono (by simp)
          obtain ⟨next, hstep⟩ :=
            exists_stepAction_of_instantiate_step
              (RegularTerm.referenceClosed_of_wellFormed
                (Classical.choose_spec hschema))
              hschemaDepthOne hconcreteStep
          have hnextWellFormed :=
            stepAction_some_wellFormed hg hschema hstep
          have hnextDepth :
              next.ApplicationDepth word.length := by
            apply stepAction_preserves_applicationDepth hg hschema
              (depth := word.length)
            · simpa [Nat.add_comm] using hdepth
            · exact hstep
          have hsymbolicOne :
              g.runActions? [action] schema = some next := by
            simpa [runActions?] using hstep
          obtain ⟨concreteNext', hconcreteOne,
              hnextEquivalent⟩ :=
            g.runActions?_instantiate hg [action]
              (Classical.choose_spec hschema)
              harguments hsymbolicOne
          have hconcreteNextEq : concreteNext' = concreteNext := by
            have hconcreteOne' :
                g.runActions? [action]
                    (schema.instantiate arguments) =
                  some concreteNext := by
              simpa [runActions?] using hconcreteStep
            exact Option.some.inj (hconcreteOne.symm.trans hconcreteOne')
          subst concreteNext'
          have hnextInstanceClosed :
              (next.instantiate arguments).ReferenceClosed :=
            RegularTerm.instantiate_referenceClosed
              (RegularTerm.referenceClosed_of_wellFormed
                (Classical.choose_spec hnextWellFormed))
              harguments
          have hconcreteNextClosed :
              concreteNext.ReferenceClosed :=
            step?_preserves_referenceClosed hg
              (RegularTerm.instantiate_referenceClosed
                (RegularTerm.referenceClosed_of_wellFormed
                  (Classical.choose_spec hschema))
                harguments)
              hconcreteStep
          have htailRelation :=
            g.runActions?_congr_unfoldingEquivalent hg word
              hnextInstanceClosed hconcreteNextClosed hnextEquivalent
          rw [htail] at htailRelation
          cases hnextRun :
              g.runActions? word (next.instantiate arguments) with
          | none =>
              rw [hnextRun] at htailRelation
              cases htailRelation
          | some nextConcrete =>
              rw [hnextRun] at htailRelation
              obtain ⟨residual, hresidual⟩ :=
                ih hnextWellFormed hnextDepth hnextRun
              exact ⟨residual, by
                simpa [runActions?, hstep] using hresidual⟩

/-- Reflection also identifies the symbolic residual instance with the
concrete target up to equality of regular-tree unfoldings. -/
public theorem runActions?_reflects_instantiation_equivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema concrete : RegularTerm} {arguments : List RegularTerm}
    (word : List Action)
    (hschema : ∃ arity, schema.WellFormed g.ranks arity)
    (hdepth : schema.ApplicationDepth word.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hrun :
      g.runActions? word (schema.instantiate arguments) =
        some concrete) :
    ∃ residual,
      g.runActions? word schema = some residual ∧
      (residual.instantiate arguments).UnfoldingEquivalent concrete := by
  obtain ⟨residual, hsymbolic⟩ :=
    runActions?_reflects_instantiation hg word hschema hdepth
      harguments hrun
  obtain ⟨concrete', hconcrete',
      hequivalent⟩ :=
    g.runActions?_instantiate hg word
      (Classical.choose_spec hschema) harguments hsymbolic
  have hconcreteEq : concrete' = concrete :=
    Option.some.inj (hconcrete'.symm.trans hrun)
  subst concrete'
  exact ⟨residual, hsymbolic, hequivalent⟩

/-- Observation 20 for regular ground terms: every ordinary run shorter than
the chosen depth is represented by a run of the compiled finite-prefix
schema, and the resulting schema instance denotes the concrete target. -/
public theorem exists_depthPrefix_residual
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler target : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) {word : List Action}
    (hlength : word.length ≤ depth)
    (hrun : g.runActions? word term = some target) :
    ∃ residual,
      g.runActions? word
          (term.depthPrefix depth).head.toRegularTerm =
        some residual ∧
      RegularTerm.UnfoldingEquivalent
        (residual.instantiate
          ((term.depthPrefix depth).paddedArguments g.ranks filler))
        target := by
  let schema := (term.depthPrefix depth).head.toRegularTerm
  let arguments :=
    (term.depthPrefix depth).paddedArguments g.ranks filler
  have hschema :
      schema.WellFormed g.ranks
        ((term.depthPrefix depth).schemaArity g.ranks) := by
    apply DepthPrefix.head_wellFormed_schemaArity
    · exact RegularTerm.depthPrefix_valid term depth
    · exact RegularTerm.depthPrefix_head_rankedBy hterm depth
  have hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks := by
    exact RegularTerm.depthPrefix_paddedArguments_ground
      hterm hfiller depth
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent term := by
    exact RegularTerm.depthPrefix_compiled_unfoldingEquivalent
      hterm hfiller depth
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed hschema)
      hargumentsClosed
  have hrunRelation :=
    g.runActions?_congr_unfoldingEquivalent hg word
      hinstanceClosed
      (RegularTerm.referenceClosed_of_ground hterm)
      hinstanceEquivalent
  rw [hrun] at hrunRelation
  cases hinstanceRun :
      g.runActions? word (schema.instantiate arguments) with
  | none =>
      rw [hinstanceRun] at hrunRelation
      cases hrunRelation
  | some instanceTarget =>
      rw [hinstanceRun] at hrunRelation
      cases hrunRelation with
      | some htargets =>
          have hdepth :
              schema.ApplicationDepth word.length := by
            exact (FiniteHead.depthPrefix_schema_applicationDepth
              hterm depth).mono hlength
          obtain ⟨residual, hsymbolic,
              hresidualEquivalent⟩ :=
            runActions?_reflects_instantiation_equivalent
              hg word ⟨_, hschema⟩ hdepth hargumentsClosed
                hinstanceRun
          exact ⟨residual, hsymbolic,
            hresidualEquivalent.trans htargets⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
