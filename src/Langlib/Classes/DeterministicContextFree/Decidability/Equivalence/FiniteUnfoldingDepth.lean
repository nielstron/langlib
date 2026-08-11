module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FinitePrefixExecution
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationSupport
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedSemanticReachability

@[expose]
public section

/-!
# Depth bounds for finite regular-term unfoldings

The executable `RegularTerm.UnfoldsFinite` check rejects every reachable
cycle.  Consequently, any path in the unfolding of a finite graph has length
at most the number of graph nodes.  This file exposes that semantic
consequence for the finite-context arguments used in Proposition 49.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- A graph has no unfolding occurrence deeper than `bound`. -/
@[expose] public def UnfoldingDepthAtMost
    (term : RegularTerm) (bound : ℕ) : Prop :=
  ∀ {depth index}, term.DescendantAt depth index → depth ≤ bound

/-- The fuel consumed by `unfoldsFiniteFrom` bounds every descendant path
starting at the checked root. -/
private theorem descendant_depth_lt_fuel_of_unfoldsFiniteFrom
    (term : RegularTerm)
    {fuel : ℕ} (visiting : List ℕ)
    {depth index : ℕ}
    (hfinite :
      unfoldsFiniteFrom term.nodes fuel visiting term.root = true)
    (hdescendant : term.DescendantAt depth index) :
    depth < fuel := by
  induction depth generalizing term fuel visiting index with
  | zero =>
      cases fuel with
      | zero => simp [unfoldsFiniteFrom] at hfinite
      | succ fuel => omega
  | succ depth ih =>
      obtain ⟨child, X, children, hroot, hchild, hrest⟩ :=
        hdescendant.succ_decompose
      cases fuel with
      | zero => simp [unfoldsFiniteFrom] at hfinite
      | succ fuel =>
          have hrootNode :
              term.nodes[term.root]? = some (.inr (X, children)) := by
            simpa [nodeAt?] using hroot
          by_cases hmem : term.root ∈ visiting
          · simp [unfoldsFiniteFrom, hmem] at hfinite
          · have hall :
                children.all (fun child =>
                  unfoldsFiniteFrom term.nodes fuel
                    (term.root :: visiting) child) = true := by
              simpa [unfoldsFiniteFrom, hmem, hrootNode] using hfinite
            have hchildFinite :=
              (List.all_eq_true.mp hall) child hchild
            have hlt := ih
              (term := term.withRoot child)
              (fuel := fuel)
              (visiting := term.root :: visiting)
              (index := index)
              (by
                simpa [withRoot, nodes, root] using hchildFinite)
              hrest
            omega

/-- Every descendant path in a finite unfolding has length at most the raw
graph-node count.  Unreachable garbage is harmless because both
`UnfoldsFinite` and `DescendantAt` start at the distinguished root. -/
public theorem UnfoldsFinite.descendant_depth_le_nodes
    {term : RegularTerm}
    (hfinite : term.UnfoldsFinite)
    {depth index : ℕ}
    (hdescendant : term.DescendantAt depth index) :
    depth ≤ term.nodes.length := by
  have hlt := descendant_depth_lt_fuel_of_unfoldsFiniteFrom
    term [] hfinite hdescendant
  change depth < term.nodes.length + 1 at hlt
  omega

/-- The node count is a semantic unfolding-depth bound for every finite
regular term. -/
public theorem UnfoldsFinite.unfoldingDepthAtMost_nodes
    {term : RegularTerm}
    (hfinite : term.UnfoldsFinite) :
    term.UnfoldingDepthAtMost term.nodes.length := by
  intro depth index hdescendant
  exact hfinite.descendant_depth_le_nodes hdescendant

/-- Any larger number is also an unfolding-depth bound. -/
public theorem UnfoldingDepthAtMost.mono
    {term : RegularTerm} {small large : ℕ}
    (hdepth : term.UnfoldingDepthAtMost small)
    (hle : small ≤ large) :
    term.UnfoldingDepthAtMost large := by
  intro depth index hdescendant
  exact (hdepth hdescendant).trans hle

/-- Semantic unfolding equivalence preserves every unfolding-depth bound. -/
public theorem UnfoldingEquivalent.unfoldingDepthAtMost
    {left right : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    {bound : ℕ}
    (hleft : left.UnfoldingDepthAtMost bound) :
    right.UnfoldingDepthAtMost bound := by
  intro depth index hdescendant
  let rightSubterm := right.withRoot index
  have hrightSubterm :
      right.SubtermAtDepth depth rightSubterm :=
    ⟨index, hdescendant, rfl⟩
  obtain ⟨leftSubterm, hleftSubterm, _hsubterms⟩ :=
    hequivalent.symm.exists_subtermAtDepth hrightSubterm
  obtain ⟨leftIndex, hleftDescendant, _hleftSubterm⟩ :=
    hleftSubterm
  exact hleft hleftDescendant

public theorem UnfoldingEquivalent.unfoldingDepthAtMost_iff
    {left right : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    (bound : ℕ) :
    left.UnfoldingDepthAtMost bound ↔
      right.UnfoldingDepthAtMost bound :=
  ⟨hequivalent.unfoldingDepthAtMost,
    hequivalent.symm.unfoldingDepthAtMost⟩

/-- Repointing at a descendant removes the consumed prefix from a semantic
unfolding-depth bound. -/
public theorem UnfoldingDepthAtMost.withRoot_of_descendant
    {term : RegularTerm} {bound offset child : ℕ}
    (hdepth : term.UnfoldingDepthAtMost bound)
    (hchild : term.DescendantAt offset child) :
    (term.withRoot child).UnfoldingDepthAtMost (bound - offset) := by
  intro depth index hdescendant
  have hfull : term.DescendantAt (offset + depth) index :=
    hchild.trans hdescendant
  have hle : offset + depth ≤ bound :=
    hdepth hfull
  omega

/-- The one-node variable graph is finite. -/
public theorem variableTerm_unfoldsFinite (x : ℕ) :
    (variableTerm x).UnfoldsFinite := by
  simp [UnfoldsFinite, unfoldsFiniteCode, unfoldsFiniteFrom,
    variableTerm, nodes, root]

/-- The open one-level symbol template has a finite unfolding. -/
public theorem symbolTemplate_unfoldsFinite (X rank : ℕ) :
    (symbolTemplate X rank).UnfoldsFinite := by
  simp [UnfoldsFinite, unfoldsFiniteCode, unfoldsFiniteFrom,
    symbolTemplate, nodes, root]
  intro x hx
  simp [hx]

/-- Instantiation maps every schema-side unfolding path to the corresponding
resolved path in the concrete instance.  A schema path can end at a variable,
but can never continue below it, so resolving only the endpoint is enough. -/
public theorem DescendantAt.instantiate_resolve
    {schema : RegularTerm} {arguments : List RegularTerm}
    {depth index : ℕ}
    (hdescendant : schema.DescendantAt depth index) :
    (schema.instantiate arguments).DescendantAt depth
      (schema.resolveRHSRef arguments index) := by
  induction hdescendant with
  | root => exact .root
  | @child depth parent X children child hparent hnode hchild ih =>
      have hparentBound : parent < schema.nodes.length :=
        (List.getElem?_eq_some_iff.mp hnode).1
      have hresolveParent :
          schema.resolveRHSRef arguments parent = parent := by
        simp [resolveRHSRef, hnode]
      have hinstanceNode :
          (schema.instantiate arguments).nodeAt?
              (schema.resolveRHSRef arguments parent) =
            some (.inr
              (X, children.map (schema.resolveRHSRef arguments))) := by
        rw [hresolveParent,
          instantiate_nodeAt?_rhs schema arguments hparentBound,
          hnode]
        rfl
      exact DescendantAt.child ih hinstanceNode
        (List.mem_map.mpr ⟨child, hchild, rfl⟩)

/-- Instantiation cannot hide a schema-side unfolding path: every such path
maps to a path of the same depth in the instantiated graph. -/
public theorem UnfoldingDepthAtMost.of_instantiate
    {schema : RegularTerm} {arguments : List RegularTerm}
    {bound : ℕ}
    (hinstance :
      (schema.instantiate arguments).UnfoldingDepthAtMost bound) :
    schema.UnfoldingDepthAtMost bound := by
  intro depth index hdescendant
  exact hinstance hdescendant.instantiate_resolve

/-- Following an instantiated unfolding path either crosses a schema
variable, or reflects to a path of the same length entirely inside the
schema. -/
public theorem instantiate_descendant_variable_or_schema
    {schema : RegularTerm} {arguments : List RegularTerm}
    (hclosed : schema.ReferenceClosed)
    {depth index : ℕ}
    (hdescendant :
      (schema.instantiate arguments).DescendantAt depth index) :
    (∃ occurrence source x,
        occurrence ≤ depth ∧
          schema.DescendantAt occurrence source ∧
          schema.nodeAt? source = some (.inl x)) ∨
      ∃ source, schema.DescendantAt depth source := by
  induction depth generalizing schema index with
  | zero => exact .inr ⟨schema.root, .root⟩
  | succ depth ih =>
      cases hroot : schema.rootNode? with
      | none =>
          have hrootBound := hclosed.1
          unfold rootNode? nodeAt? at hroot
          rw [List.getElem?_eq_none_iff] at hroot
          omega
      | some node =>
          cases node with
          | inl x =>
              exact .inl ⟨0, schema.root, x, by omega, .root,
                by simpa [rootNode?] using hroot⟩
          | inr application =>
              rcases application with ⟨X, children⟩
              have hschemaRoot :
                  schema.rootApplication? = some (X, children) := by
                simp [rootApplication?, hroot]
              have hschemaRootNode :
                  schema.nodeAt? schema.root =
                    some (.inr (X, children)) := by
                simpa [rootNode?] using hroot
              have hinstanceRoot :=
                instantiate_rootApplication?
                  (arguments := arguments) hclosed hschemaRoot
              have hinstanceRootNode :=
                nodeAt?_root_of_rootApplication? hinstanceRoot
              obtain ⟨instanceChild, Y, instanceChildren,
                  hdescendantRoot, hinstanceChild, hrest⟩ :=
                hdescendant.succ_decompose
              have happlication :
                  (Y, instanceChildren) =
                    (X, children.map
                      (schema.resolveRHSRef arguments)) := by
                exact Sum.inr.inj
                  (Option.some.inj
                    (hdescendantRoot.symm.trans hinstanceRootNode))
              have hchildren :
                  instanceChildren = children.map
                    (schema.resolveRHSRef arguments) :=
                congrArg Prod.snd happlication
              subst instanceChildren
              obtain ⟨child, hchild, hresolved⟩ :=
                List.mem_map.mp hinstanceChild
              subst instanceChild
              have hchildBound : child < schema.nodes.length :=
                hclosed.2 schema.root X children hschemaRootNode
                  child hchild
              have hchildClosed :
                  (schema.withRoot child).ReferenceClosed :=
                withRoot_referenceClosed hclosed hchildBound
              have hrest' :
                  ((schema.withRoot child).instantiate arguments)
                    |>.DescendantAt depth index := by
                simpa only [instantiate_withRoot] using hrest
              rcases ih hchildClosed hrest' with
                hvariable | hschemaPath
              · obtain ⟨occurrence, source, x, hoccurrence,
                    hpath, hnode⟩ := hvariable
                have hfirst : schema.DescendantAt 1 child :=
                  .child .root hschemaRootNode hchild
                have hfull :
                    schema.DescendantAt (occurrence + 1) source := by
                  have := hfirst.trans hpath
                  simpa [Nat.add_comm] using this
                exact .inl ⟨occurrence + 1, source, x, by omega,
                  hfull, by
                    simpa [withRoot, nodeAt?, nodes] using hnode⟩
              · obtain ⟨source, hpath⟩ := hschemaPath
                have hfirst : schema.DescendantAt 1 child :=
                  .child .root hschemaRootNode hchild
                have hfull :
                    schema.DescendantAt (depth + 1) source := by
                  have := hfirst.trans hpath
                  simpa [Nat.add_comm] using this
                exact .inr ⟨source, hfull⟩

/-- Factorized form of `instantiate_descendant_variable_or_schema`.  In the
variable case the remainder of the supplied concrete descendant path starts
exactly at the copied argument boundary. -/
public theorem instantiate_descendant_factor_variable_or_schema
    {schema : RegularTerm} {arguments : List RegularTerm}
    (hclosed : schema.ReferenceClosed)
    {depth index : ℕ}
    (hdescendant :
      (schema.instantiate arguments).DescendantAt depth index) :
    (∃ occurrence remaining source x,
        depth = occurrence + remaining ∧
          schema.DescendantAt occurrence source ∧
          schema.nodeAt? source = some (.inl x) ∧
          ((schema.instantiate arguments).withRoot
              (schema.resolveRHSRef arguments source)).DescendantAt
                remaining index) ∨
      ∃ source,
        schema.DescendantAt depth source ∧
          index = schema.resolveRHSRef arguments source := by
  induction depth generalizing schema index with
  | zero =>
      cases hdescendant
      exact .inr ⟨schema.root, .root, rfl⟩
  | succ depth ih =>
      cases hroot : schema.rootNode? with
      | none =>
          have hrootBound := hclosed.1
          unfold rootNode? nodeAt? at hroot
          rw [List.getElem?_eq_none_iff] at hroot
          omega
      | some node =>
          cases node with
          | inl x =>
              have hnode :
                  schema.nodeAt? schema.root = some (.inl x) := by
                simpa [rootNode?] using hroot
              have hresolve :
                  schema.resolveRHSRef arguments schema.root =
                    (schema.instantiate arguments).root := by
                rfl
              exact .inl ⟨0, depth + 1, schema.root, x,
                by simp, .root, hnode, by
                  rw [hresolve]
                  simpa [withRoot] using hdescendant⟩
          | inr application =>
              rcases application with ⟨X, children⟩
              have hschemaRoot :
                  schema.rootApplication? = some (X, children) := by
                simp [rootApplication?, hroot]
              have hschemaRootNode :
                  schema.nodeAt? schema.root =
                    some (.inr (X, children)) := by
                simpa [rootNode?] using hroot
              have hinstanceRoot :=
                instantiate_rootApplication?
                  (arguments := arguments) hclosed hschemaRoot
              have hinstanceRootNode :=
                nodeAt?_root_of_rootApplication? hinstanceRoot
              obtain ⟨instanceChild, Y, instanceChildren,
                  hdescendantRoot, hinstanceChild, hrest⟩ :=
                hdescendant.succ_decompose
              have happlication :
                  (Y, instanceChildren) =
                    (X, children.map
                      (schema.resolveRHSRef arguments)) := by
                exact Sum.inr.inj
                  (Option.some.inj
                    (hdescendantRoot.symm.trans hinstanceRootNode))
              have hchildren :
                  instanceChildren = children.map
                    (schema.resolveRHSRef arguments) :=
                congrArg Prod.snd happlication
              subst instanceChildren
              obtain ⟨child, hchild, hresolved⟩ :=
                List.mem_map.mp hinstanceChild
              subst instanceChild
              have hchildBound : child < schema.nodes.length :=
                hclosed.2 schema.root X children hschemaRootNode
                  child hchild
              have hchildClosed :
                  (schema.withRoot child).ReferenceClosed :=
                withRoot_referenceClosed hclosed hchildBound
              have hrest' :
                  ((schema.withRoot child).instantiate arguments)
                    |>.DescendantAt depth index := by
                simpa only [instantiate_withRoot] using hrest
              rcases ih hchildClosed hrest' with
                hvariable | hschemaPath
              · obtain ⟨occurrence, remaining, source, x,
                    hdepth, hpath, hnode, hfactor⟩ := hvariable
                have hfirst : schema.DescendantAt 1 child :=
                  .child .root hschemaRootNode hchild
                have hfull :
                    schema.DescendantAt (occurrence + 1) source := by
                  have := hfirst.trans hpath
                  simpa [Nat.add_comm] using this
                exact .inl ⟨occurrence + 1, remaining, source, x,
                  by omega, hfull, by
                    simpa [withRoot, nodeAt?, nodes] using hnode,
                  by
                    simpa [withRoot, nodes, root] using hfactor⟩
              · obtain ⟨source, hpath, hindex⟩ := hschemaPath
                have hfirst : schema.DescendantAt 1 child :=
                  .child .root hschemaRootNode hchild
                have hfull :
                    schema.DescendantAt (depth + 1) source := by
                  have := hfirst.trans hpath
                  simpa [Nat.add_comm] using this
                exact .inr ⟨source, hfull, by
                  simpa [withRoot, nodes, root] using hindex⟩

/-- Factorized finite-schema boundary crossing. -/
public theorem UnfoldsFinite.exists_variable_factor_on_instantiated_descendant
    {schema : RegularTerm} {arguments : List RegularTerm}
    (hfinite : schema.UnfoldsFinite)
    (hclosed : schema.ReferenceClosed)
    {depth index : ℕ}
    (hdeep : schema.nodes.length < depth)
    (hdescendant :
      (schema.instantiate arguments).DescendantAt depth index) :
    ∃ occurrence remaining source x,
      depth = occurrence + remaining ∧
        schema.DescendantAt occurrence source ∧
        schema.nodeAt? source = some (.inl x) ∧
        ((schema.instantiate arguments).withRoot
            (schema.resolveRHSRef arguments source)).DescendantAt
              remaining index := by
  rcases instantiate_descendant_factor_variable_or_schema
      hclosed hdescendant with hvariable | hschemaPath
  · exact hvariable
  · obtain ⟨source, hpath, _hindex⟩ := hschemaPath
    exact False.elim (by
      have := hfinite.descendant_depth_le_nodes hpath
      omega)

/-- A supplied semantic depth bound is enough for factorized boundary
crossing; executable finiteness is only one way to obtain such a bound. -/
public theorem UnfoldingDepthAtMost.exists_variable_factor_on_instantiated_descendant
    {schema : RegularTerm} {arguments : List RegularTerm}
    {bound depth index : ℕ}
    (hbound : schema.UnfoldingDepthAtMost bound)
    (hclosed : schema.ReferenceClosed)
    (hdeep : bound < depth)
    (hdescendant :
      (schema.instantiate arguments).DescendantAt depth index) :
    ∃ occurrence remaining source x,
      depth = occurrence + remaining ∧
        schema.DescendantAt occurrence source ∧
        schema.nodeAt? source = some (.inl x) ∧
        ((schema.instantiate arguments).withRoot
            (schema.resolveRHSRef arguments source)).DescendantAt
              remaining index := by
  rcases instantiate_descendant_factor_variable_or_schema
      hclosed hdescendant with hvariable | hschemaPath
  · exact hvariable
  · obtain ⟨source, hpath, _hindex⟩ := hschemaPath
    exact False.elim (by
      have := hbound hpath
      omega)

/-- A path longer than the whole finite schema must have entered one of its
substitution arguments. -/
public theorem UnfoldsFinite.exists_variable_on_instantiated_descendant
    {schema : RegularTerm} {arguments : List RegularTerm}
    (hfinite : schema.UnfoldsFinite)
    (hclosed : schema.ReferenceClosed)
    {depth index : ℕ}
    (hdeep : schema.nodes.length < depth)
    (hdescendant :
      (schema.instantiate arguments).DescendantAt depth index) :
    ∃ occurrence source x,
      occurrence ≤ depth ∧
        schema.DescendantAt occurrence source ∧
        schema.nodeAt? source = some (.inl x) := by
  rcases instantiate_descendant_variable_or_schema
      hclosed hdescendant with hvariable | hschemaPath
  · exact hvariable
  · obtain ⟨source, hpath⟩ := hschemaPath
    exact False.elim (by
      have := hfinite.descendant_depth_le_nodes hpath
      omega)

/-- Every descendant of a structural prefix witness remains inside its
finite support. -/
public theorem PrefixWitness.node_mem_of_descendant
    {term : RegularTerm} {width : ℕ} {support : List ℕ}
    (hwitness : term.PrefixWitness width support)
    {depth index : ℕ}
    (hdescendant : term.DescendantAt depth index) :
    index ∈ support := by
  induction hdescendant with
  | root => exact hwitness.1
  | @child depth parent X children child hparent hnode hchild ih =>
      rcases hwitness.2 parent ih with hvariable | happlication
      · obtain ⟨x, hparentNode, _hx⟩ := hvariable
        rw [hnode] at hparentNode
        simp at hparentNode
      · obtain ⟨Y, witnessChildren, hparentNode,
            hwitnessChildren⟩ := happlication
        rw [hnode] at hparentNode
        simp only [Option.some.injEq, Sum.inr.injEq,
          Prod.mk.injEq] at hparentNode
        rcases hparentNode with ⟨rfl, rfl⟩
        exact hwitnessChildren child hchild

/-- The variable reached on a prefix-witness path belongs to the active
argument prefix. -/
public theorem PrefixWitness.variable_lt_of_descendant
    {term : RegularTerm} {width : ℕ} {support : List ℕ}
    (hwitness : term.PrefixWitness width support)
    {depth index x : ℕ}
    (hdescendant : term.DescendantAt depth index)
    (hnode : term.nodeAt? index = some (.inl x)) :
    x < width := by
  have hmem := hwitness.node_mem_of_descendant hdescendant
  rcases hwitness.2 index hmem with hvariable | happlication
  · obtain ⟨y, hy, hyWidth⟩ := hvariable
    have : y = x := Sum.inl.inj (Option.some.inj (hy.symm.trans hnode))
    simpa [this] using hyWidth
  · obtain ⟨X, children, happlication, _⟩ := happlication
    rw [hnode] at happlication
    simp at happlication

/-- Every variable node in a well-formed schema lies below its declared
arity. -/
public theorem WellFormed.variable_lt_of_nodeAt
    {term : RegularTerm} {ranks : List ℕ} {arity index x : ℕ}
    (hterm : term.WellFormed ranks arity)
    (hnode : term.nodeAt? index = some (.inl x)) :
    x < arity := by
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inl x : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  simpa [nodeWellFormedCode] using of_decide_eq_true hwell

/-- Instantiating a finite-depth schema by uniformly finite-depth arguments
adds the two depth bounds. -/
public theorem UnfoldingDepthAtMost.instantiate
    {schema : RegularTerm} {arguments : List RegularTerm}
    {ranks : List ℕ} {arity schemaBound argumentBound : ℕ}
    (hschemaDepth : schema.UnfoldingDepthAtMost schemaBound)
    (hschema : schema.WellFormed ranks arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed)
    (hargumentsDepth :
      ∀ argument ∈ arguments,
        argument.UnfoldingDepthAtMost argumentBound) :
    (schema.instantiate arguments)
      |>.UnfoldingDepthAtMost (schemaBound + argumentBound) := by
  have hschemaClosed := referenceClosed_of_wellFormed hschema
  intro depth index hdescendant
  rcases instantiate_descendant_factor_variable_or_schema
      hschemaClosed hdescendant with hvariable | hschemaPath
  · obtain ⟨occurrence, remaining, source, x,
        hdepth, hpath, hnode, hfactor⟩ := hvariable
    have hxArity : x < arity := hschema.variable_lt_of_nodeAt hnode
    have hxArguments : x < arguments.length := by
      simpa [hargumentsLength] using hxArity
    let argument := arguments[x]
    have hargument : arguments[x]? = some argument :=
      List.getElem?_eq_getElem hxArguments
    let boundary :=
      (schema.instantiate arguments).withRoot
        (schema.resolveRHSRef arguments source)
    have hsourceRoot :
        (schema.withRoot source).nodeAt?
            (schema.withRoot source).root = some (.inl x) := by
      simpa [withRoot, nodeAt?, nodes, root] using hnode
    have hboundaryEquivalent :
        boundary.UnfoldingEquivalent argument := by
      change
        ((schema.withRoot source).instantiate arguments)
          |>.UnfoldingEquivalent argument
      exact instantiate_unfoldingEquivalent_argument
        hsourceRoot hargument
        (hargumentsClosed argument
          (List.mem_of_getElem? hargument))
    let boundaryTarget := boundary.withRoot index
    have hboundarySubterm :
        boundary.SubtermAtDepth remaining boundaryTarget :=
      ⟨index, hfactor, rfl⟩
    obtain ⟨argumentTarget, hargumentSubterm, _hequivalent⟩ :=
      hboundaryEquivalent.exists_subtermAtDepth hboundarySubterm
    obtain ⟨argumentIndex, hargumentPath, _htarget⟩ :=
      hargumentSubterm
    have hoccurrenceBound : occurrence ≤ schemaBound :=
      hschemaDepth hpath
    have hremainingBound : remaining ≤ argumentBound :=
      hargumentsDepth argument (List.mem_of_getElem? hargument)
        hargumentPath
    omega
  · obtain ⟨source, hpath, _hindex⟩ := hschemaPath
    exact (hschemaDepth hpath).trans (Nat.le_add_right _ _)

/-- Concrete boundary form: a sufficiently deep occurrence in an instance
crosses one active argument at a no-later unfolding depth. -/
public theorem HasPrefixWitness.exists_activeArgument_boundary_of_deep_descendant
    {schema : RegularTerm} {arguments : List RegularTerm}
    {width depth index : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hfinite : schema.UnfoldsFinite)
    (hclosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed)
    (hdeep : schema.nodes.length < depth)
    (hdescendant :
      (schema.instantiate arguments).DescendantAt depth index) :
    ∃ occurrence x argument boundary,
      occurrence ≤ depth ∧
        x < width ∧
        arguments[x]? = some argument ∧
        (schema.instantiate arguments).SubtermAtDepth
          occurrence boundary ∧
        boundary.UnfoldingEquivalent argument := by
  obtain ⟨support, hsupport⟩ := hwitness
  obtain ⟨occurrence, source, x, hoccurrence, hpath, hnode⟩ :=
    hfinite.exists_variable_on_instantiated_descendant
      hclosed hdeep hdescendant
  have hx : x < width :=
    hsupport.variable_lt_of_descendant hpath hnode
  have hxArguments : x < arguments.length := hx.trans_le hwidth
  let argument := arguments[x]
  have hargument : arguments[x]? = some argument :=
    List.getElem?_eq_getElem hxArguments
  let boundary :=
    (schema.instantiate arguments).withRoot
      (schema.resolveRHSRef arguments source)
  have hboundaryOccurrence :
      (schema.instantiate arguments).SubtermAtDepth
        occurrence boundary := by
    exact ⟨schema.resolveRHSRef arguments source,
      hpath.instantiate_resolve, rfl⟩
  have hsourceRoot :
      (schema.withRoot source).nodeAt?
          (schema.withRoot source).root = some (.inl x) := by
    simpa [withRoot, nodeAt?, nodes, root] using hnode
  have hboundaryEquivalent : boundary.UnfoldingEquivalent argument := by
    change
      ((schema.withRoot source).instantiate arguments)
        |>.UnfoldingEquivalent argument
    exact instantiate_unfoldingEquivalent_argument
      hsourceRoot hargument
      (hargumentsClosed argument
        (List.mem_of_getElem? hargument))
  exact ⟨occurrence, x, argument, boundary, hoccurrence, hx,
    hargument, hboundaryOccurrence, hboundaryEquivalent⟩

end RegularTerm

namespace FiniteHead

private theorem compiledNodeCount_le_sum_of_mem
    {child : FiniteHead} {children : List FiniteHead}
    (hchild : child ∈ children) :
    child.compiledNodeCount ≤
      (children.map compiledNodeCount).sum := by
  induction children with
  | nil => simp at hchild
  | cons head children ih =>
      simp only [List.mem_cons] at hchild
      simp only [List.map_cons, List.sum_cons]
      rcases hchild with rfl | htail
      · omega
      · have := ih htail
        omega

/-- The graph compiled from a genuinely finite head has unfolding depth at
most its exact compiled-node count.  This is a semantic bound: unreachable
template-variable nodes may remain in the graph, but they do not affect the
unfolding from the distinguished root. -/
public theorem toRegularTerm_unfoldingDepthAtMost
    {head : FiniteHead} {ranks : List ℕ}
    (hranked : head.RankedBy ranks) :
    head.toRegularTerm.UnfoldingDepthAtMost head.compiledNodeCount := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (∀ child ∈ heads, child.RankedBy ranks) →
      ∀ child ∈ heads,
        child.toRegularTerm.UnfoldingDepthAtMost
          child.compiledNodeCount) with
  | var index =>
      intro depth index' hdescendant
      have hdescendant' :
          (RegularTerm.variableTerm index).DescendantAt depth index' := by
        simpa [toRegularTerm] using hdescendant
      simpa [toRegularTerm, compiledNodeCount,
        RegularTerm.variableTerm, RegularTerm.nodes] using
        (RegularTerm.variableTerm_unfoldsFinite index)
          |>.descendant_depth_le_nodes hdescendant'
  | app symbol children ih =>
      have hranked' :
          ranks[symbol]? = some children.length ∧
            ∀ child ∈ children, child.RankedBy ranks := by
        simpa [RankedBy] using hranked
      have htemplateWellFormed :
          (RegularTerm.symbolTemplate symbol children.length).WellFormed
            ranks children.length :=
        RegularTerm.symbolTemplate_wellFormed hranked'.1
      have htemplateDepth :
          (RegularTerm.symbolTemplate symbol children.length)
            |>.UnfoldingDepthAtMost (1 + children.length) := by
        intro depth index hdescendant
        simpa [RegularTerm.symbolTemplate, RegularTerm.nodes,
          Nat.add_comm] using
          (RegularTerm.symbolTemplate_unfoldsFinite
            symbol children.length)
              |>.descendant_depth_le_nodes hdescendant
      have hargumentsClosed :
          ∀ argument ∈ children.map toRegularTerm,
            argument.ReferenceClosed := by
        intro argument hargument
        obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hargument
        exact child.toRegularTerm_referenceClosed
      have hargumentsDepth :
          ∀ argument ∈ children.map toRegularTerm,
            argument.UnfoldingDepthAtMost
              (children.map compiledNodeCount).sum := by
        intro argument hargument
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
        intro depth index hdescendant
        exact ((ih hranked'.2 child hchild) hdescendant).trans
          (compiledNodeCount_le_sum_of_mem hchild)
      intro depth index hdescendant
      have hdescendant' :
          ((RegularTerm.symbolTemplate symbol children.length).instantiate
            (children.map toRegularTerm)).DescendantAt depth index := by
        simpa [toRegularTerm] using hdescendant
      simpa [compiledNodeCount] using
        (htemplateDepth.instantiate htemplateWellFormed (by simp)
          hargumentsClosed hargumentsDepth hdescendant')
  | nil => aesop
  | cons child children ihChild ihChildren hranked item hitem =>
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        exact ihChild (hranked child (by simp))
      · exact ihChildren
          (fun tail htailMem => hranked tail (by simp [htailMem]))
          item htail

end FiniteHead

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Uniform semantic unfolding-depth recurrence for an ordinary symbolic
run.  A rewrite can add the depth of its finite right-hand side, but a single
unfolding path enters only one source argument, so no rank multiplier is
needed. -/
@[expose] public def residualUnfoldingDepthBound
    (g : EncodedFirstOrderGrammar Action) : ℕ → ℕ → ℕ
  | 0, initial => initial
  | steps + 1, initial =>
      g.residualUnfoldingDepthBound steps
        (g.rhsNodeBound + initial)

/-- A selected grammar right-hand side has a finite unfolding.  The ordinary
well-formedness accessor deliberately returns only rankedness, so the
finiteness half of the encoded row check is exposed separately here. -/
public theorem selected_rhs_unfoldsFinite
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {X : ℕ} {action : Action} {rhs : RegularTerm}
    (hrule : g.ruleLookup X action = some rhs) :
    rhs.UnfoldsFinite := by
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
      have hrhsEq : rule.rhs = rhs := by simpa using hrhs
      subst rhs
      exact hrow.2

/-- Every unfolding path inside a selected right-hand side is bounded by the
grammar-wide maximum RHS graph size. -/
public theorem selected_rhs_descendant_depth_le_rhsNodeBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {X : ℕ} {action : Action} {rhs : RegularTerm}
    (hrule : g.ruleLookup X action = some rhs)
    {depth index : ℕ}
    (hdescendant : rhs.DescendantAt depth index) :
    depth ≤ g.rhsNodeBound := by
  exact ((g.selected_rhs_unfoldsFinite hg hrule)
    |>.descendant_depth_le_nodes hdescendant).trans
      (g.rhs_nodes_length_le_rhsNodeBound hrule)

/-- One ordinary symbolic rewrite preserves a grammar-uniform semantic
unfolding-depth bound. -/
public theorem stepAction_preserves_unfoldingDepthAtMost
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {action : Action} {sourceBound : ℕ}
    (hsource : ∃ arity, source.WellFormed g.ranks arity)
    (hsourceDepth : source.UnfoldingDepthAtMost sourceBound)
    (hstep : g.step? (.inl action) source = some target) :
    target.UnfoldingDepthAtMost (g.rhsNodeBound + sourceBound) := by
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
      have hrootNode :=
        RegularTerm.nodeAt?_root_of_rootApplication? hroot
      obtain ⟨sourceRank, hsourceRank, hchildrenLength⟩ :=
        rank_arity_of_wellFormed hsourceWellFormed hrootNode
      obtain ⟨rhsRank, hrhsRank, hrhsWellFormed⟩ :=
        selected_rhs_wellFormed hg hrule
      have hrankEq : rhsRank = sourceRank :=
        Option.some.inj (hrhsRank.symm.trans hsourceRank)
      have hrhsChildren :
          rhs.WellFormed g.ranks children.length := by
        rw [hchildrenLength, ← hrankEq]
        exact hrhsWellFormed
      have hrhsDepth :
          rhs.UnfoldingDepthAtMost g.rhsNodeBound := by
        intro depth index hdescendant
        exact g.selected_rhs_descendant_depth_le_rhsNodeBound
          hg hrule hdescendant
      have hargumentsClosed :
          ∀ argument ∈ children.map source.withRoot,
            argument.ReferenceClosed := by
        intro argument hargument
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
        exact RegularTerm.withRoot_referenceClosed hsourceClosed
          (hsourceClosed.2 source.root X children hrootNode child hchild)
      have hargumentsDepth :
          ∀ argument ∈ children.map source.withRoot,
            argument.UnfoldingDepthAtMost sourceBound := by
        intro argument hargument depth index hdescendant
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
        have hfirst : source.DescendantAt 1 child :=
          .child .root hrootNode hchild
        have hfull : source.DescendantAt (depth + 1) index := by
          have := hfirst.trans hdescendant
          simpa [Nat.add_comm] using this
        have := hsourceDepth hfull
        omega
      intro depth index hdescendant
      exact hrhsDepth.instantiate hrhsChildren (by simp)
        hargumentsClosed hargumentsDepth hdescendant

/-- A finite ordinary symbolic run preserves a semantic depth bound depending
only on the grammar, the run length, and the source bound. -/
public theorem runActions?_preserves_unfoldingDepthAtMost
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {word : List Action} {initialBound : ℕ}
    (hsource : ∃ arity, source.WellFormed g.ranks arity)
    (hsourceDepth : source.UnfoldingDepthAtMost initialBound)
    (hrun : g.runActions? word source = some target) :
    target.UnfoldingDepthAtMost
      (g.residualUnfoldingDepthBound word.length initialBound) := by
  induction word generalizing source initialBound with
  | nil =>
      simp [runActions?] at hrun
      subst target
      intro depth index hdescendant
      simpa [residualUnfoldingDepthBound] using
        hsourceDepth hdescendant
  | cons action word ih =>
      cases hstep : g.step? (.inl action) source with
      | none => simp [runActions?, hstep] at hrun
      | some next =>
          have htail : g.runActions? word next = some target := by
            simpa [runActions?, hstep] using hrun
          have hnextWellFormed :=
            stepAction_some_wellFormed hg hsource hstep
          have hnextDepth :
              next.UnfoldingDepthAtMost
                (g.rhsNodeBound + initialBound) := by
            intro depth index hdescendant
            exact stepAction_preserves_unfoldingDepthAtMost
              hg hsource hsourceDepth hstep hdescendant
          intro depth index hdescendant
          simpa [residualUnfoldingDepthBound] using
            ih hnextWellFormed hnextDepth htail hdescendant

end EncodedFirstOrderGrammar

end DCFEquivalence
