module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinkingBoundary

@[expose]
public section

/-!
# Compact finite representatives of depth-bounded open schemas

Semantic unfolding depth does not bound the raw graph size of a
`RegularTerm`: root rewriting and repointing retain unreachable graph
garbage.  Proposition 49 needs the converse direction operationally: replace
a depth-bounded open schema by a semantically equivalent finite graph whose
size is controlled by its reachable unfolding.

`finiteUnfoldingHead` unfolds only the reachable rooted tree, retaining the
original variable indices.  Compiling that finite head discards all
unreachable graph nodes.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Canonical finite syntax obtained by unfolding a regular schema to the
supplied semantic depth.  At zero fuel a nullary application is retained;
the depth-bound theorem below rules out every non-nullary application in that
branch. -/
@[expose] public def finiteUnfoldingHead :
    ℕ → RegularTerm → FiniteHead
  | 0, term =>
      match term.rootNode? with
      | some (.inl x) => .var x
      | some (.inr (X, _children)) => .app X []
      | none => .var 0
  | fuel + 1, term =>
      match term.rootNode? with
      | some (.inl x) => .var x
      | some (.inr (X, children)) =>
          .app X
            (children.map fun child =>
              finiteUnfoldingHead fuel (term.withRoot child))
      | none => .var 0

/-- Repointing a well-formed graph at any in-bounds node preserves
well-formedness. -/
public theorem WellFormed.withRoot
    {term : RegularTerm} {ranks : List ℕ} {arity i : ℕ}
    (hterm : term.WellFormed ranks arity)
    (hi : i < term.nodes.length) :
    (term.withRoot i).WellFormed ranks arity := by
  unfold WellFormed wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨?_, ?_⟩
  · simpa [withRoot, root, nodes] using decide_eq_true hi
  · simpa [withRoot, nodes] using hterm.2

/-- The arity of every application node in a well-formed open schema agrees
with the grammar rank table. -/
public theorem WellFormed.application_rank
    {term : RegularTerm} {ranks : List ℕ} {arity i X : ℕ}
    {children : List ℕ}
    (hterm : term.WellFormed ranks arity)
    (hnode : term.nodeAt? i = some (.inr (X, children))) :
    ranks[X]? = some children.length := by
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hlocal := (List.all_eq_true.mp hterm.2) _ hmem
  unfold nodeWellFormedCode at hlocal
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hlocal
  | some rank =>
      simp only [hrank, Bool.and_eq_true,
        decide_eq_true_eq] at hlocal
      rw [hlocal.1]

/-- A prefix witness is preserved by the canonical finite unfolding. -/
public theorem PrefixWitness.finiteUnfoldingHead_variablesBelow
    {term : RegularTerm} {width : ℕ} {support : List ℕ}
    (hwitness : term.PrefixWitness width support)
    (fuel : ℕ) :
    (term.finiteUnfoldingHead fuel).VariablesBelow width := by
  induction fuel generalizing term support with
  | zero =>
      rcases hwitness.2 term.root hwitness.1 with
        hvariable | happlication
      · obtain ⟨x, hroot, hx⟩ := hvariable
        simpa [finiteUnfoldingHead, rootNode?, hroot,
          FiniteHead.VariablesBelow] using hx
      · obtain ⟨X, children, hroot, _hchildren⟩ := happlication
        simp [finiteUnfoldingHead, rootNode?, hroot,
          FiniteHead.VariablesBelow]
  | succ fuel ih =>
      rcases hwitness.2 term.root hwitness.1 with
        hvariable | happlication
      · obtain ⟨x, hroot, hx⟩ := hvariable
        simpa [finiteUnfoldingHead, rootNode?, hroot,
          FiniteHead.VariablesBelow] using hx
      · obtain ⟨X, children, hroot, hchildren⟩ := happlication
        simp only [finiteUnfoldingHead, rootNode?, hroot,
          FiniteHead.VariablesBelow, List.mem_map]
        rintro childHead ⟨child, hchild, rfl⟩
        exact ih (hwitness.withRoot (hchildren child hchild))

/-- The canonical finite unfolding is ranked by the same grammar table. -/
public theorem WellFormed.finiteUnfoldingHead_rankedBy
    {term : RegularTerm} {ranks : List ℕ} {arity : ℕ}
    (hterm : term.WellFormed ranks arity)
    {fuel : ℕ}
    (hdepth : term.UnfoldingDepthAtMost fuel) :
    (term.finiteUnfoldingHead fuel).RankedBy ranks := by
  induction fuel generalizing term with
  | zero =>
      cases hroot : term.rootNode? with
      | none =>
          simp [finiteUnfoldingHead, hroot, FiniteHead.RankedBy]
      | some node =>
          cases node with
          | inl x =>
              simp [finiteUnfoldingHead, hroot,
                FiniteHead.RankedBy]
          | inr application =>
              rcases application with ⟨X, children⟩
              have hnode :
                  term.nodeAt? term.root =
                    some (.inr (X, children)) := by
                simpa [rootNode?] using hroot
              have hrank := hterm.application_rank hnode
              have hchildrenNil : children = [] := by
                apply List.eq_nil_iff_forall_not_mem.mpr
                intro child hchild
                have hdescendant :
                    term.DescendantAt 1 child :=
                  .child .root hnode hchild
                have := hdepth hdescendant
                omega
              subst children
              simp [finiteUnfoldingHead, hroot,
                FiniteHead.RankedBy] at hrank ⊢
              exact hrank
  | succ fuel ih =>
      cases hroot : term.rootNode? with
      | none =>
          simp [finiteUnfoldingHead, hroot, FiniteHead.RankedBy]
      | some node =>
          cases node with
          | inl x =>
              simp [finiteUnfoldingHead, hroot,
                FiniteHead.RankedBy]
          | inr application =>
              rcases application with ⟨X, children⟩
              have hnode :
                  term.nodeAt? term.root =
                    some (.inr (X, children)) := by
                simpa [rootNode?] using hroot
              have hrank := hterm.application_rank hnode
              have hclosed :=
                referenceClosed_of_wellFormed hterm
              have hchildWellFormed : ∀ child ∈ children,
                  (term.withRoot child).WellFormed ranks arity := by
                intro child hchild
                exact hterm.withRoot
                  (hclosed.2 term.root X children hnode child hchild)
              have hchildDepth : ∀ child ∈ children,
                  (term.withRoot child).UnfoldingDepthAtMost fuel := by
                intro child hchild
                have hfirst :
                    term.DescendantAt 1 child :=
                  .child .root hnode hchild
                intro descendantDepth index hdescendant
                have hfull :=
                  hfirst.trans hdescendant
                have hle := hdepth hfull
                omega
              simp only [finiteUnfoldingHead, hroot,
                FiniteHead.RankedBy, List.length_map]
              constructor
              · exact hrank
              · intro childHead hchildHead
                obtain ⟨child, hchild, heq⟩ :=
                  List.mem_map.mp hchildHead
                rw [← heq]
                exact ih (hchildWellFormed child hchild)
                  (hchildDepth child hchild)

/-- The finite syntax has depth at most one more than its unfolding fuel.
The extra one is the finite-head convention that a nullary application has
depth one. -/
public theorem finiteUnfoldingHead_depth_le
    (term : RegularTerm) (fuel : ℕ) :
    (term.finiteUnfoldingHead fuel).depth ≤ fuel + 1 := by
  induction fuel generalizing term with
  | zero =>
      cases hroot : term.rootNode? <;>
        simp [finiteUnfoldingHead, hroot, FiniteHead.depth]
      case some node =>
        cases node <;>
          simp [FiniteHead.depth]
  | succ fuel ih =>
      cases hroot : term.rootNode? <;>
        simp [finiteUnfoldingHead, hroot, FiniteHead.depth]
      case some node =>
        cases node with
        | inl x =>
            simp [FiniteHead.depth]
        | inr application =>
            rcases application with ⟨X, children⟩
            simp only [FiniteHead.depth, List.map_map,
              Function.comp_def]
            have hmax :
                ((children.map fun child =>
                    (finiteUnfoldingHead fuel
                      (term.withRoot child)).depth).foldr max 0) ≤
                  fuel + 1 := by
              apply List.max_le_of_forall_le
              intro value hvalue
              obtain ⟨child, _hchild, rfl⟩ :=
                List.mem_map.mp hvalue
              exact ih (term.withRoot child)
            omega

private theorem forall₂_map_same_of_forall
    {A B C : Type} {R : B → C → Prop}
    (left : A → B) (right : A → C) (values : List A)
    (h : ∀ value ∈ values, R (left value) (right value)) :
    List.Forall₂ R (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun item hitem => h item (by simp [hitem]))

/-- Under the supplied semantic depth bound, compiling the canonical finite
unfolding preserves the regular tree denoted by the original schema. -/
public theorem WellFormed.finiteUnfoldingHead_unfoldingEquivalent
    {term : RegularTerm} {ranks : List ℕ} {arity fuel : ℕ}
    (hterm : term.WellFormed ranks arity)
    (hdepth : term.UnfoldingDepthAtMost fuel) :
    (term.finiteUnfoldingHead fuel).toRegularTerm
      |>.UnfoldingEquivalent term := by
  induction fuel generalizing term with
  | zero =>
      cases hroot : term.rootNode? with
      | none =>
          have hclosed := referenceClosed_of_wellFormed hterm
          have hrootLt := hclosed.1
          unfold rootNode? nodeAt? at hroot
          rw [List.getElem?_eq_none_iff] at hroot
          omega
      | some node =>
          cases node with
          | inl x =>
              simpa [finiteUnfoldingHead, hroot,
                FiniteHead.toRegularTerm] using
                (unfoldingEquivalent_variableTerm_of_rootNode hroot).symm
          | inr application =>
              rcases application with ⟨X, children⟩
              have hrootApplication :
                  term.rootApplication? = some (X, children) := by
                simp [rootApplication?, hroot]
              have hrootNode :=
                nodeAt?_root_of_rootApplication? hrootApplication
              have hchildrenNil : children = [] := by
                apply List.eq_nil_iff_forall_not_mem.mpr
                intro child hchild
                have hdescendant :
                    term.DescendantAt 1 child :=
                  .child .root hrootNode hchild
                have := hdepth hdescendant
                omega
              subst children
              simpa [finiteUnfoldingHead, hroot,
                FiniteHead.toRegularTerm] using
                symbolTemplate_instantiate_unfoldingEquivalent
                  (referenceClosed_of_wellFormed hterm)
                  hrootApplication
  | succ fuel ih =>
      cases hroot : term.rootNode? with
      | none =>
          have hclosed := referenceClosed_of_wellFormed hterm
          have hrootLt := hclosed.1
          unfold rootNode? nodeAt? at hroot
          rw [List.getElem?_eq_none_iff] at hroot
          omega
      | some node =>
          cases node with
          | inl x =>
              simpa [finiteUnfoldingHead, hroot,
                FiniteHead.toRegularTerm] using
                (unfoldingEquivalent_variableTerm_of_rootNode hroot).symm
          | inr application =>
              rcases application with ⟨X, children⟩
              have hrootApplication :
                  term.rootApplication? = some (X, children) := by
                simp [rootApplication?, hroot]
              have hrootNode :=
                nodeAt?_root_of_rootApplication? hrootApplication
              have hclosed := referenceClosed_of_wellFormed hterm
              have hchildBound : ∀ child ∈ children,
                  child < term.nodes.length := by
                intro child hchild
                exact hclosed.2 term.root X children
                  hrootNode child hchild
              have hchildWellFormed : ∀ child ∈ children,
                  (term.withRoot child).WellFormed ranks arity := by
                intro child hchild
                exact hterm.withRoot (hchildBound child hchild)
              have hchildDepth : ∀ child ∈ children,
                  (term.withRoot child).UnfoldingDepthAtMost fuel := by
                intro child hchild
                have hfirst :
                    term.DescendantAt 1 child :=
                  .child .root hrootNode hchild
                intro descendantDepth index hdescendant
                have hfull :=
                  hfirst.trans hdescendant
                have hle := hdepth hfull
                omega
              have hchildrenEquivalent :
                  List.Forall₂ UnfoldingEquivalent
                    (children.map fun child =>
                      (finiteUnfoldingHead fuel
                        (term.withRoot child)).toRegularTerm)
                    (children.map term.withRoot) := by
                apply forall₂_map_same_of_forall
                intro child hchild
                exact ih
                  (hchildWellFormed child hchild)
                  (hchildDepth child hchild)
              have hleftClosed :
                  ∀ argument ∈
                      (children.map fun child =>
                        (finiteUnfoldingHead fuel
                          (term.withRoot child)).toRegularTerm),
                    argument.ReferenceClosed := by
                intro argument hargument
                obtain ⟨child, hchild, rfl⟩ :=
                  List.mem_map.mp hargument
                exact FiniteHead.toRegularTerm_referenceClosed _
              have hrightClosed :
                  ∀ argument ∈ children.map term.withRoot,
                    argument.ReferenceClosed := by
                intro argument hargument
                obtain ⟨child, hchild, rfl⟩ :=
                  List.mem_map.mp hargument
                exact withRoot_referenceClosed hclosed
                  (hchildBound child hchild)
              have hchildrenInstance :=
                instantiate_unfoldingEquivalent
                  (symbolTemplate_referenceClosed X children.length)
                  hchildrenEquivalent hleftClosed hrightClosed
              have hrebuild :=
                symbolTemplate_instantiate_unfoldingEquivalent
                  hclosed hrootApplication
              simpa [finiteUnfoldingHead, hroot,
                FiniteHead.toRegularTerm] using
                  hchildrenInstance.trans hrebuild

/-- Grammar-uniform raw graph envelope for compacting a schema whose
semantic unfolding depth is at most `depth`. -/
@[expose] public def finiteSchemaNodeBound
    (ranks : List ℕ) (depth : ℕ) : ℕ :=
  FiniteHead.compiledDepthBound (ranks.foldr max 0) (depth + 1)

/-- The compiled canonical representative obeys the finite schema envelope. -/
public theorem WellFormed.finiteUnfoldingHead_nodes_length_le
    {term : RegularTerm} {ranks : List ℕ} {arity depth : ℕ}
    (hterm : term.WellFormed ranks arity)
    (hdepth : term.UnfoldingDepthAtMost depth) :
    (term.finiteUnfoldingHead depth).toRegularTerm.nodes.length ≤
      finiteSchemaNodeBound ranks depth := by
  rw [FiniteHead.toRegularTerm_nodes_length]
  exact FiniteHead.compiledNodeCount_le_depthBound
    (hterm.finiteUnfoldingHead_rankedBy hdepth)
    (finiteUnfoldingHead_depth_le term depth)

/-- A compact schema representative retaining semantic equivalence, the
active-prefix witness, well-formedness, and a grammar-uniform raw size bound. -/
public structure FiniteSchemaCompaction
    (ranks : List ℕ) (arity width depth : ℕ)
    (schema : RegularTerm) where
  compact : RegularTerm
  equivalent : compact.UnfoldingEquivalent schema
  wellFormed : compact.WellFormed ranks arity
  hasPrefixWitness : compact.HasPrefixWitness width
  supported : compact.SupportedByPrefix ranks arity width
  unfoldingDepthAtMost : compact.UnfoldingDepthAtMost depth
  nodes_length_le : compact.nodes.length ≤
    finiteSchemaNodeBound ranks depth

/-- Every well-formed, prefix-supported, semantically depth-bounded schema
admits a compact representative over the same declared variables. -/
public theorem exists_finiteSchemaCompaction
    {schema : RegularTerm} {ranks : List ℕ}
    {arity width depth : ℕ}
    (hwellFormed : schema.WellFormed ranks arity)
    (hwitness : schema.HasPrefixWitness width)
    (hwidth : width ≤ arity)
    (hrankMax : ranks.foldr max 0 ≤ arity)
    (hdepth : schema.UnfoldingDepthAtMost depth) :
    Nonempty (FiniteSchemaCompaction
      ranks arity width depth schema) := by
  let head := schema.finiteUnfoldingHead depth
  let compact := head.toRegularTerm
  obtain ⟨support, hsupport⟩ := hwitness
  have hactive : head.VariablesBelow width :=
    hsupport.finiteUnfoldingHead_variablesBelow depth
  have hranked : head.RankedBy ranks :=
    hwellFormed.finiteUnfoldingHead_rankedBy hdepth
  have hretained : head.retainedVariableBound ≤ arity := by
    exact (FiniteHead.retainedVariableBound_le hactive hranked).trans
      (max_le hwidth hrankMax)
  exact ⟨
    { compact := compact
      equivalent := by
        exact hwellFormed.finiteUnfoldingHead_unfoldingEquivalent hdepth
      wellFormed := by
        exact (FiniteHead.toRegularTerm_wellFormed hranked).mono
          hretained
      hasPrefixWitness := by
        exact FiniteHead.toRegularTerm_hasPrefixWitness hactive
      supported := by
        exact (FiniteHead.toRegularTerm_hasPrefixWitness hactive)
          |>.supportedByPrefix
            ((FiniteHead.toRegularTerm_wellFormed hranked).mono
              hretained)
            hwidth
      unfoldingDepthAtMost := by
        exact UnfoldingEquivalent.unfoldingDepthAtMost
          (hwellFormed.finiteUnfoldingHead_unfoldingEquivalent
            hdepth).symm
          hdepth
      nodes_length_le := by
        exact hwellFormed.finiteUnfoldingHead_nodes_length_le hdepth }⟩

end RegularTerm

end DCFEquivalence
