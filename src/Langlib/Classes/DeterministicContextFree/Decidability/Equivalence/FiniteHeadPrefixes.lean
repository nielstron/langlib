module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingSegments
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SubstitutionWellFormed

@[expose]
public section

/-!
# Finite heads and depth-prefix decompositions

Jančar's balancing proof repeatedly writes a ground regular term as a finite
head over the ordered subterms at a fixed unfolding depth.  `FiniteHead` keeps
that genuinely finite tree separate from the cyclic graph presentation used
for runtime terms.  `depthPrefix` unfolds a graph for a bounded number of
levels, numbers boundary occurrences from left to right, and returns the
corresponding fixed tuple of ground tails.
-/

namespace DCFEquivalence

/-- A genuinely finite first-order term.  Variables name positions in the
associated tail tuple. -/
public inductive FiniteHead where
  | var (index : ℕ)
  | app (symbol : ℕ) (children : List FiniteHead)

namespace FiniteHead

/-- A global variable bound large enough for the direct graph compiler.  The
child-count term accounts for unreachable template variables retained by
nested substitution; the recursive term accounts for genuine boundary
variables and retained variables in child graphs. -/
@[expose] public def retainedVariableBound : FiniteHead → ℕ
  | .var index => index + 1
  | .app _ children =>
      max children.length
        ((children.map retainedVariableBound).foldr max 0)

/-- Exact raw graph size produced by the substitution-based compiler. -/
@[expose] public def compiledNodeCount : FiniteHead → ℕ
  | .var _ => 1
  | .app _ children =>
      1 + children.length + (children.map compiledNodeCount).sum

/-- Add an offset to every boundary-variable index. -/
@[expose] public def shiftVariables (offset : ℕ) : FiniteHead → FiniteHead
  | .var index => .var (offset + index)
  | .app symbol children =>
      .app symbol (children.map (shiftVariables offset))

/-- Number of syntax-tree nodes in a finite head. -/
@[expose] public def nodeCount : FiniteHead → ℕ
  | .var _ => 1
  | .app _ children => 1 + (children.map nodeCount).sum

/-- Maximum number of child edges from the root to a node. -/
@[expose] public def depth : FiniteHead → ℕ
  | .var _ => 0
  | .app _ children =>
      1 + (children.map depth).foldr max 0

/-- Every variable in the head lies below the supplied tuple bound. -/
@[expose] public def VariablesBelow (bound : ℕ) : FiniteHead → Prop
  | .var index => index < bound
  | .app _ children => ∀ child ∈ children, child.VariablesBelow bound

/-- Every application has the rank declared by the grammar table. -/
@[expose] public def RankedBy (ranks : List ℕ) : FiniteHead → Prop
  | .var _ => True
  | .app symbol children =>
      ranks[symbol]? = some children.length ∧
        ∀ child ∈ children, child.RankedBy ranks

/-- Compile finite syntax to the existing finite graph representation.
Application compilation uses the ordinary simultaneous-instantiation
constructor, leaving only harmless unreachable template-variable nodes. -/
@[expose] public def toRegularTerm : FiniteHead → RegularTerm
  | .var index => RegularTerm.variableTerm index
  | .app symbol children =>
      (RegularTerm.symbolTemplate symbol children.length).instantiate
        (children.map toRegularTerm)
termination_by head => head

/-- Interpret a finite head directly over a tuple of runtime tails.  This
semantic evaluator is convenient for proving the depth-prefix equation before
relating it to graph-level simultaneous instantiation. -/
@[expose] public def evaluate : FiniteHead → List RegularTerm → RegularTerm
  | .var index, tails =>
      (tails[index]?).getD (RegularTerm.variableTerm index)
  | .app symbol children, tails =>
      (RegularTerm.symbolTemplate symbol children.length).instantiate
        (children.map fun child => child.evaluate tails)
termination_by head _ => head

@[simp] public theorem evaluate_var
    (index : ℕ) (tails : List RegularTerm) :
    (FiniteHead.var index).evaluate tails =
      (tails[index]?).getD (RegularTerm.variableTerm index) := by
  rw [evaluate]

@[simp] public theorem evaluate_app
    (symbol : ℕ) (children : List FiniteHead)
    (tails : List RegularTerm) :
    (FiniteHead.app symbol children).evaluate tails =
      (RegularTerm.symbolTemplate symbol children.length).instantiate
        (children.map fun child => child.evaluate tails) := by
  rw [evaluate]

/-- Compilation of a finite head has no dangling graph references. -/
public theorem toRegularTerm_referenceClosed (head : FiniteHead) :
    head.toRegularTerm.ReferenceClosed := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      ∀ child ∈ heads, child.toRegularTerm.ReferenceClosed) with
  | var index =>
      constructor
      · simp [toRegularTerm, RegularTerm.variableTerm,
          RegularTerm.root, RegularTerm.nodes]
      · intro i symbol children hnode
        simp only [toRegularTerm, RegularTerm.variableTerm,
          RegularTerm.nodeAt?, RegularTerm.nodes] at hnode
        cases i <;> simp_all
  | app symbol children ih =>
      rw [toRegularTerm]
      apply RegularTerm.instantiate_referenceClosed
        (RegularTerm.symbolTemplate_referenceClosed symbol children.length)
      intro argument hargument
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
      exact ih child hchild
  | nil => aesop
  | cons child children ihChild ihChildren => aesop

/-- Compiling an application head preserves its application root. -/
public theorem toRegularTerm_app_rootApplication?
    (symbol : ℕ) (children : List FiniteHead) :
    ((FiniteHead.app symbol children).toRegularTerm).rootApplication? =
      some (symbol,
        ((List.range children.length).map (fun i => i + 1)).map
          ((RegularTerm.symbolTemplate symbol children.length).resolveRHSRef
            (children.map toRegularTerm))) := by
  rw [toRegularTerm]
  exact RegularTerm.instantiate_rootApplication?
    (RegularTerm.symbolTemplate_referenceClosed symbol children.length)
    (RegularTerm.symbolTemplate_rootApplication? symbol children.length)

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

/-- The compiled graph is structurally well formed at its explicit retained
variable bound. -/
public theorem toRegularTerm_wellFormed
    {head : FiniteHead} {ranks : List ℕ}
    (hranked : head.RankedBy ranks) :
    head.toRegularTerm.WellFormed ranks head.retainedVariableBound := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (∀ child ∈ heads, child.RankedBy ranks) →
      ∀ child ∈ heads,
        child.toRegularTerm.WellFormed ranks
          ((heads.map retainedVariableBound).foldr max 0)) with
  | var index =>
      unfold toRegularTerm retainedVariableBound
      unfold RegularTerm.WellFormed RegularTerm.wellFormedCode
      rw [Bool.and_eq_true]
      constructor
      · simp [RegularTerm.variableTerm, RegularTerm.root,
          RegularTerm.nodes]
      · apply List.all_eq_true.mpr
        intro node hnode
        have hnodeEq : node = (.inl index : RawNode) := by
          simpa [RegularTerm.variableTerm, RegularTerm.nodes] using hnode
        subst node
        simp [RegularTerm.nodeWellFormedCode]
  | app symbol children ih =>
      have hranked' : ranks[symbol]? = some children.length ∧
          ∀ child ∈ children, child.RankedBy ranks := by
        simpa [RankedBy] using hranked
      let childBound :=
        (children.map retainedVariableBound).foldr max 0
      have hchildrenWellFormed : ∀ argument ∈ children.map toRegularTerm,
          argument.WellFormed ranks childBound := by
        intro argument hargument
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
        exact ih hranked'.2 child hchild
      have htemplateWellFormed :
          (RegularTerm.symbolTemplate symbol children.length).WellFormed
            ranks (children.map toRegularTerm).length := by
        simpa using RegularTerm.symbolTemplate_wellFormed hranked'.1
      have hresult := RegularTerm.instantiate_wellFormed_max
        (schema := RegularTerm.symbolTemplate symbol children.length)
        (arguments := children.map toRegularTerm)
        htemplateWellFormed
        hchildrenWellFormed
      simpa [toRegularTerm, retainedVariableBound, childBound] using hresult
  | nil => aesop
  | cons child children ihChild ihChildren hranked item hitem =>
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        apply (ihChild (hranked child (by simp))).mono
        simp
      · apply (ihChildren
          (fun tail htail => hranked tail (by simp [htail]))
          item htail).mono
        simp

/-- Retained compiler variables are uniformly bounded by the actual boundary
width and the greatest rank in the grammar. -/
public theorem retainedVariableBound_le
    {head : FiniteHead} {ranks : List ℕ} {width : ℕ}
    (hbelow : head.VariablesBelow width)
    (hranked : head.RankedBy ranks) :
    head.retainedVariableBound ≤
      max width (ranks.foldr max 0) := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (∀ child ∈ heads,
        child.VariablesBelow width ∧ child.RankedBy ranks) →
      ∀ value ∈ heads.map retainedVariableBound,
        value ≤ max width (ranks.foldr max 0)) with
  | var index =>
      simp only [VariablesBelow] at hbelow
      simp only [retainedVariableBound]
      omega
  | app symbol children ih =>
      have hbelow' : ∀ child ∈ children,
          child.VariablesBelow width := by
        simpa [VariablesBelow] using hbelow
      have hranked' : ranks[symbol]? = some children.length ∧
          ∀ child ∈ children, child.RankedBy ranks := by
        simpa [RankedBy] using hranked
      simp only [retainedVariableBound]
      apply max_le
      · apply le_trans _ (Nat.le_max_right width _)
        exact List.le_max_of_le
          (List.mem_of_getElem? hranked'.1) (le_refl _)
      · apply List.max_le_of_forall_le
        intro value hvalue
        exact ih
          (fun child hchild =>
            ⟨hbelow' child hchild, hranked'.2 child hchild⟩)
          value hvalue
  | nil => aesop
  | cons child children ihChild ihChildren hproperties value hvalue =>
      obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hvalue
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        exact ihChild (hproperties child (by simp)).1
          (hproperties child (by simp)).2
      · exact ihChildren
          (fun item hitem => hproperties item (by simp [hitem]))
          item.retainedVariableBound
          (List.mem_map.mpr ⟨item, htail, rfl⟩)

@[simp] public theorem nodeCount_pos (head : FiniteHead) :
    0 < head.nodeCount := by
  cases head <;> simp [nodeCount]

private theorem length_le_nodeCount_sum (heads : List FiniteHead) :
    heads.length ≤ (heads.map nodeCount).sum := by
  induction heads with
  | nil => simp
  | cons head heads ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hpositive := nodeCount_pos head
      omega

/-- `compiledNodeCount` is the exact size of the compiled raw graph. -/
public theorem toRegularTerm_nodes_length (head : FiniteHead) :
    head.toRegularTerm.nodes.length = head.compiledNodeCount := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (heads.map fun child => child.toRegularTerm.nodes.length).sum =
        (heads.map compiledNodeCount).sum) with
  | var index =>
      simp [toRegularTerm, RegularTerm.variableTerm, RegularTerm.nodes,
        compiledNodeCount]
  | app symbol children ih =>
      rw [toRegularTerm, RegularTerm.instantiate_nodes_length]
      simp only [compiledNodeCount]
      have htemplate :
          (RegularTerm.symbolTemplate symbol children.length).nodes.length =
            1 + children.length := by
        simp [RegularTerm.symbolTemplate, RegularTerm.nodes, Nat.add_comm]
      have harguments :
          ((children.map toRegularTerm).map
            (fun argument => argument.nodes.length)).sum =
          (children.map
            (fun child => child.toRegularTerm.nodes.length)).sum := by
        simp [List.map_map, Function.comp_def]
      rw [htemplate, harguments, ih]
  | nil => rfl
  | cons child children ihChild ihChildren =>
      simp only [List.map_cons, List.sum_cons]
      rw [ihChild, ihChildren]

/-- Uniform compiled-graph bound for depth-`depth` heads over symbols of rank
at most `branching`. -/
@[expose] public def compiledDepthBound (branching : ℕ) : ℕ → ℕ
  | 0 => 1
  | depth + 1 => 1 + branching * (compiledDepthBound branching depth + 1)

private theorem sum_compiledNodeCount_le
    (heads : List FiniteHead) (bound : ℕ)
    (hbound : ∀ head ∈ heads, head.compiledNodeCount ≤ bound) :
    (heads.map compiledNodeCount).sum ≤ heads.length * bound := by
  induction heads with
  | nil => simp
  | cons head heads ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul]
      have hhead := hbound head (by simp)
      have htail := ih (fun item hitem => hbound item (by simp [hitem]))
      omega

private theorem compiledDepthBound_pos (branching depth : ℕ) :
    0 < compiledDepthBound branching depth := by
  cases depth <;> simp [compiledDepthBound]

/-- A ranked head of bounded depth has a grammar-uniform compiled graph size.
The greatest rank is read directly from the finite rank table. -/
public theorem compiledNodeCount_le_depthBound
    {head : FiniteHead} {ranks : List ℕ} {depth : ℕ}
    (hranked : head.RankedBy ranks)
    (hdepth : head.depth ≤ depth) :
    head.compiledNodeCount ≤
      compiledDepthBound (ranks.foldr max 0) depth := by
  induction depth generalizing head with
  | zero =>
      cases head with
      | var index => simp [compiledNodeCount, compiledDepthBound]
      | app symbol children =>
          simp [FiniteHead.depth] at hdepth
  | succ depth ih =>
      cases head with
      | var index =>
          simp [compiledNodeCount, compiledDepthBound]
      | app symbol children =>
          have hranked' : ranks[symbol]? = some children.length ∧
              ∀ child ∈ children, child.RankedBy ranks := by
            simpa [RankedBy] using hranked
          have hbranching : children.length ≤ ranks.foldr max 0 :=
            List.le_max_of_le (List.mem_of_getElem? hranked'.1) (le_refl _)
          have hmaxDepth :
              (children.map FiniteHead.depth).foldr max 0 ≤ depth := by
            simp only [FiniteHead.depth] at hdepth
            omega
          have hchildDepth : ∀ child ∈ children,
              child.depth ≤ depth := by
            intro child hchild
            exact le_trans
              (List.le_max_of_le
                (List.mem_map.mpr ⟨child, hchild, rfl⟩) (le_refl _))
              hmaxDepth
          have hsum : (children.map compiledNodeCount).sum ≤
              children.length *
                compiledDepthBound (ranks.foldr max 0) depth :=
            sum_compiledNodeCount_le children _
              (fun child hchild =>
                ih (hranked'.2 child hchild) (hchildDepth child hchild))
          simp only [compiledNodeCount, compiledDepthBound]
          calc
            1 + children.length + (children.map compiledNodeCount).sum ≤
                1 + children.length +
                  children.length *
                    compiledDepthBound (ranks.foldr max 0) depth :=
              Nat.add_le_add_left hsum _
            _ = 1 + children.length *
                (compiledDepthBound (ranks.foldr max 0) depth + 1) := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]
            _ ≤ 1 + (ranks.foldr max 0) *
                (compiledDepthBound (ranks.foldr max 0) depth + 1) := by
              exact Nat.add_le_add_left
                (Nat.mul_le_mul_right
                  (compiledDepthBound (ranks.foldr max 0) depth + 1)
                  hbranching) 1

@[simp] public theorem shiftVariables_zero (head : FiniteHead) :
    head.shiftVariables 0 = head := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads => heads.map (shiftVariables 0) = heads) with
  | var index => simp [shiftVariables]
  | app symbol children ih => simp [shiftVariables, ih]
  | nil => rfl
  | cons head tail ihHead ihTail => simp [ihHead, ihTail]

public theorem VariablesBelow.mono
    {head : FiniteHead} {m n : ℕ} (hmn : m ≤ n)
    (hbelow : head.VariablesBelow m) : head.VariablesBelow n := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads => ∀ {m n}, m ≤ n →
      (∀ child ∈ heads, child.VariablesBelow m) →
      ∀ child ∈ heads, child.VariablesBelow n)
      generalizing m n with
  | var index =>
      simp only [VariablesBelow] at hbelow ⊢
      omega
  | app symbol children ih =>
      simpa [VariablesBelow] using ih hmn (by
        simpa [VariablesBelow] using hbelow)
  | nil => aesop
  | cons child children ihChild ihChildren =>
      aesop

public theorem variablesBelow_shiftVariables
    {head : FiniteHead} {bound offset : ℕ}
    (hbelow : head.VariablesBelow bound) :
    (head.shiftVariables offset).VariablesBelow (offset + bound) := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads => ∀ {bound offset},
      (∀ child ∈ heads, child.VariablesBelow bound) →
      ∀ shifted ∈ heads.map (shiftVariables offset),
        shifted.VariablesBelow (offset + bound))
      generalizing bound offset with
  | var index =>
      simp only [VariablesBelow, shiftVariables] at hbelow ⊢
      omega
  | app symbol children ih =>
      simpa [shiftVariables, VariablesBelow] using ih (by
        simpa [VariablesBelow] using hbelow)
  | nil => aesop
  | cons child children ihChild ihChildren =>
      aesop

/-- Renumbering boundary variables does not affect application ranks. -/
public theorem rankedBy_shiftVariables
    {head : FiniteHead} {ranks : List ℕ} {offset : ℕ}
    (hranked : head.RankedBy ranks) :
    (head.shiftVariables offset).RankedBy ranks := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (∀ child ∈ heads, child.RankedBy ranks) →
      ∀ shifted ∈ heads.map (shiftVariables offset),
        shifted.RankedBy ranks) with
  | var index => simp [shiftVariables, RankedBy]
  | app symbol children ih =>
      have hranked' : ranks[symbol]? = some children.length ∧
          ∀ child ∈ children, child.RankedBy ranks := by
        simpa [RankedBy] using hranked
      simp only [shiftVariables, RankedBy, List.length_map]
      exact ⟨hranked'.1, ih hranked'.2⟩
  | nil => aesop
  | cons child children ihChild ihChildren => aesop

/-- Variable shifting is interpreted by dropping the same number of leading
tails. -/
public theorem evaluate_shiftVariables
    (head : FiniteHead) (offset : ℕ) (tails : List RegularTerm)
    (hbelow : head.VariablesBelow (tails.drop offset).length) :
    (head.shiftVariables offset).evaluate tails =
      head.evaluate (tails.drop offset) := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads => ∀ offset tails,
      (∀ head ∈ heads,
        head.VariablesBelow (tails.drop offset).length) →
      (heads.map fun head =>
        (head.shiftVariables offset).evaluate tails) =
      (heads.map fun head => head.evaluate (tails.drop offset)))
      generalizing offset tails with
  | var index =>
      have hbelow' : index < (tails.drop offset).length := by
        simpa [VariablesBelow] using hbelow
      have hdrop : (tails.drop offset)[index]? =
          some ((tails.drop offset)[index]'hbelow') := by
        exact List.getElem?_eq_getElem hbelow'
      have horiginal : tails[offset + index]? =
          some ((tails.drop offset)[index]'hbelow') := by
        rw [← List.getElem?_drop]
        exact hdrop
      simp [shiftVariables, hdrop, horiginal]
  | app symbol children ih =>
      have hchildren : ∀ child ∈ children,
          child.VariablesBelow (tails.drop offset).length := by
        simpa [VariablesBelow] using hbelow
      have hmaps := ih offset tails hchildren
      simpa [shiftVariables, evaluate_app, List.map_map] using
        congrArg (fun arguments =>
          (RegularTerm.symbolTemplate symbol children.length).instantiate
            arguments) hmaps
  | nil => aesop
  | cons child children ihChild ihChildren =>
      aesop

/-- Extra tails after all variables used by a head do not change its
interpretation. -/
public theorem evaluate_append_of_variablesBelow
    (head : FiniteHead) (tails extra : List RegularTerm)
    (hbelow : head.VariablesBelow tails.length) :
    head.evaluate (tails ++ extra) = head.evaluate tails := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads => ∀ tails extra,
      (∀ head ∈ heads, head.VariablesBelow tails.length) →
      (heads.map fun head => head.evaluate (tails ++ extra)) =
      (heads.map fun head => head.evaluate tails))
      generalizing tails extra with
  | var index =>
      have hindex : index < tails.length := by
        simpa [VariablesBelow] using hbelow
      simp [evaluate_var, List.getElem?_append_left hindex]
  | app symbol children ih =>
      have hchildren : ∀ child ∈ children,
          child.VariablesBelow tails.length := by
        simpa [VariablesBelow] using hbelow
      have hmaps := ih tails extra hchildren
      simpa [evaluate_app] using congrArg (fun arguments =>
        (RegularTerm.symbolTemplate symbol children.length).instantiate
          arguments) hmaps
  | nil => aesop
  | cons child children ihChild ihChildren =>
      aesop

/-- Evaluating a finite head over reference-closed tails produces a
reference-closed runtime graph.  Out-of-range variables are represented by a
closed one-node variable graph, so this fact does not require prefix
validity. -/
public theorem evaluate_referenceClosed
    (head : FiniteHead) (tails : List RegularTerm)
    (htails : ∀ tail ∈ tails, tail.ReferenceClosed) :
    (head.evaluate tails).ReferenceClosed := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      ∀ child ∈ heads, (child.evaluate tails).ReferenceClosed) with
  | var index =>
      cases htail : tails[index]? with
      | none =>
          rw [evaluate_var, htail]
          change (RegularTerm.variableTerm index).ReferenceClosed
          constructor
          · simp [RegularTerm.variableTerm, RegularTerm.root,
              RegularTerm.nodes]
          · intro i symbol children hnode
            change [(.inl index : RawNode)][i]? =
              some (.inr (symbol, children)) at hnode
            cases i <;> simp_all
      | some tail =>
          simpa [evaluate, htail] using
            htails tail (List.mem_of_getElem? htail)
  | app symbol children ih =>
      rw [evaluate_app]
      apply RegularTerm.instantiate_referenceClosed
        (RegularTerm.symbolTemplate_referenceClosed symbol children.length)
      intro argument hargument
      obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
      exact ih child hchild
  | nil => aesop
  | cons child children ihChild ihChildren => aesop

/-- Direct evaluation agrees with compiling the finite head as an open regular
term and applying ordinary simultaneous substitution. -/
public theorem toRegularTerm_instantiate_unfoldingEquivalent_evaluate
    (head : FiniteHead) {ranks : List ℕ} (tails : List RegularTerm)
    (hbelow : head.VariablesBelow tails.length)
    (hranked : head.RankedBy ranks)
    (htails : ∀ tail ∈ tails, tail.ReferenceClosed) :
    (head.toRegularTerm.instantiate tails).UnfoldingEquivalent
      (head.evaluate tails) := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      ∀ child ∈ heads,
        child.VariablesBelow tails.length →
        child.RankedBy ranks →
        (child.toRegularTerm.instantiate tails).UnfoldingEquivalent
          (child.evaluate tails)) with
  | var index =>
      have hi : index < tails.length := by
        simpa [VariablesBelow] using hbelow
      have htail : tails[index]? = some tails[index] :=
        List.getElem?_eq_getElem hi
      have hequivalent :=
        RegularTerm.instantiate_unfoldingEquivalent_argument
          (schema := RegularTerm.variableTerm index)
          (arguments := tails) (x := index)
          (argument := tails[index])
          (by simpa [RegularTerm.rootNode?] using
            RegularTerm.variableTerm_rootNode? index)
          htail
          (htails tails[index] (List.get_mem tails ⟨index, hi⟩))
      simpa [toRegularTerm, evaluate, htail] using hequivalent
  | app symbol children ih =>
      have hranked' : ranks[symbol]? = some children.length ∧
          ∀ child ∈ children, child.RankedBy ranks := by
        simpa [RankedBy] using hranked
      have hrank : ranks[symbol]? = some children.length := by
        exact hranked'.1
      have hchildrenBelow : ∀ child ∈ children,
          child.VariablesBelow tails.length := by
        simpa [VariablesBelow] using hbelow
      have hchildrenRanked : ∀ child ∈ children,
          child.RankedBy ranks := by
        exact hranked'.2
      let contexts := children.map toRegularTerm
      have hcontextsClosed : ∀ context ∈ contexts,
          context.ReferenceClosed := by
        intro context hcontext
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hcontext
        exact toRegularTerm_referenceClosed child
      have htemplateWellFormed :
          (RegularTerm.symbolTemplate symbol children.length).WellFormed
            ranks contexts.length := by
        simpa [contexts] using
          (RegularTerm.symbolTemplate_wellFormed hrank)
      have hcomposition :=
        RegularTerm.instantiate_comp_unfoldingEquivalent
          (outer := RegularTerm.symbolTemplate symbol children.length)
          (contexts := contexts) (arguments := tails)
          htemplateWellFormed
          hcontextsClosed htails
      have hchildrenEquivalent : List.Forall₂
          RegularTerm.UnfoldingEquivalent
          (children.map fun child => child.toRegularTerm.instantiate tails)
          (children.map fun child => child.evaluate tails) := by
        apply forall₂_map_same_of_forall
        intro child hchild
        exact ih child hchild (hchildrenBelow child hchild)
          (hchildrenRanked child hchild)
      have hinstantiation := RegularTerm.instantiate_unfoldingEquivalent
        (RegularTerm.symbolTemplate_referenceClosed symbol children.length)
        hchildrenEquivalent
        (by
          intro argument hargument
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
          exact RegularTerm.instantiate_referenceClosed
            (toRegularTerm_referenceClosed child) htails)
        (by
          intro argument hargument
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
          exact evaluate_referenceClosed child tails htails)
      have hcomposition' :
          RegularTerm.UnfoldingEquivalent
            (((RegularTerm.symbolTemplate symbol children.length).instantiate
              (children.map toRegularTerm)).instantiate tails)
            ((RegularTerm.symbolTemplate symbol children.length).instantiate
              (children.map fun child =>
                child.toRegularTerm.instantiate tails)) := by
        simpa [contexts, RegularTerm.composedContexts, List.map_map,
          Function.comp_def] using hcomposition
      have hresult := hcomposition'.trans hinstantiation
      simpa [toRegularTerm, evaluate, contexts,
        RegularTerm.composedContexts, List.map_map,
        Function.comp_def] using hresult
  | nil => aesop
  | cons child children ihChild ihChildren => aesop

@[simp] public theorem depth_shiftVariables
    (head : FiniteHead) (offset : ℕ) :
    (head.shiftVariables offset).depth = head.depth := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads => ∀ offset,
      (heads.map fun head => (head.shiftVariables offset).depth) =
      (heads.map FiniteHead.depth)) generalizing offset with
  | var index => simp [shiftVariables, depth]
  | app symbol children ih =>
      simp only [shiftVariables, depth]
      simpa [Function.comp_def] using
        congrArg (List.foldr max 0) (ih offset)
  | nil => simp
  | cons child children ihChild ihChildren => aesop

end FiniteHead

/-- One finite head together with the ordered runtime tails plugged into its
variables. -/
public structure DepthPrefix where
  head : FiniteHead
  tails : List RegularTerm

namespace DepthPrefix

/-- Every boundary variable of a prefix names an actual tail. -/
@[expose] public def Valid (decomposition : DepthPrefix) : Prop :=
  decomposition.head.VariablesBelow decomposition.tails.length

/-- Uniform schema arity: genuine boundary variables followed by enough
padding positions to validate all unreachable compiler variables. -/
@[expose] public def schemaArity
    (ranks : List ℕ) (decomposition : DepthPrefix) : ℕ :=
  max decomposition.tails.length (ranks.foldr max 0)

/-- Pad the genuine boundary tuple to `schemaArity` with one fixed ground
filler.  Padding variables are never reachable in the finite-head unfolding. -/
@[expose] public def paddedArguments
    (ranks : List ℕ) (decomposition : DepthPrefix)
    (filler : RegularTerm) : List RegularTerm :=
  decomposition.tails ++
    List.replicate
      (decomposition.schemaArity ranks - decomposition.tails.length) filler

@[simp] public theorem paddedArguments_length
    (ranks : List ℕ) (decomposition : DepthPrefix)
    (filler : RegularTerm) :
    (decomposition.paddedArguments ranks filler).length =
      decomposition.schemaArity ranks := by
  simp [paddedArguments, schemaArity]

/-- A valid ranked head compiles to a schema well formed at the padded arity. -/
public theorem head_wellFormed_schemaArity
    {ranks : List ℕ} {decomposition : DepthPrefix}
    (hvalid : decomposition.Valid)
    (hranked : decomposition.head.RankedBy ranks) :
    decomposition.head.toRegularTerm.WellFormed ranks
      (decomposition.schemaArity ranks) := by
  apply (FiniteHead.toRegularTerm_wellFormed hranked).mono
  exact FiniteHead.retainedVariableBound_le hvalid hranked

/-- Padding with a reference-closed filler preserves direct finite-head
semantics and gives an ordinary graph-substitution presentation. -/
public theorem compiled_unfoldingEquivalent_evaluate
    {ranks : List ℕ} {decomposition : DepthPrefix}
    (hvalid : decomposition.Valid)
    (hranked : decomposition.head.RankedBy ranks)
    {filler : RegularTerm}
    (htails : ∀ tail ∈ decomposition.tails, tail.ReferenceClosed)
    (hfiller : filler.ReferenceClosed) :
    (decomposition.head.toRegularTerm.instantiate
        (decomposition.paddedArguments ranks filler)).UnfoldingEquivalent
      (decomposition.head.evaluate decomposition.tails) := by
  have hpaddedClosed : ∀ argument ∈
      decomposition.paddedArguments ranks filler,
      argument.ReferenceClosed := by
    intro argument hargument
    simp only [paddedArguments, List.mem_append,
      List.mem_replicate] at hargument
    rcases hargument with htail | ⟨hcount, rfl⟩
    · exact htails argument htail
    · exact hfiller
  have hbelowPadded : decomposition.head.VariablesBelow
      (decomposition.paddedArguments ranks filler).length := by
    apply hvalid.mono
    simp [paddedArguments]
  have hequivalent :=
    FiniteHead.toRegularTerm_instantiate_unfoldingEquivalent_evaluate
      decomposition.head (decomposition.paddedArguments ranks filler)
      hbelowPadded hranked hpaddedClosed
  have hevaluate : decomposition.head.evaluate
      (decomposition.paddedArguments ranks filler) =
      decomposition.head.evaluate decomposition.tails := by
    apply FiniteHead.evaluate_append_of_variablesBelow
    exact hvalid
  simpa [hevaluate] using hequivalent

/-- Groundness of genuine tails and the filler gives a ground padded tuple. -/
public theorem paddedArguments_ground
    {ranks : List ℕ} {decomposition : DepthPrefix}
    {filler : RegularTerm}
    (htails : ∀ tail ∈ decomposition.tails, tail.Ground ranks)
    (hfiller : filler.Ground ranks) :
    ∀ argument ∈ decomposition.paddedArguments ranks filler,
      argument.Ground ranks := by
  intro argument hargument
  simp only [paddedArguments, List.mem_append,
    List.mem_replicate] at hargument
  rcases hargument with htail | ⟨hcount, rfl⟩
  · exact htails argument htail
  · exact hfiller

/-- Shift one child head past tails collected from its elder siblings. -/
@[expose] public def collectHeads : List DepthPrefix → ℕ → List FiniteHead
  | [], _ => []
  | child :: children, offset =>
      child.head.shiftVariables offset ::
        collectHeads children (offset + child.tails.length)

/-- Concatenate the tail tuples of child prefixes. -/
@[expose] public def collectTails (children : List DepthPrefix) : List RegularTerm :=
  children.flatMap DepthPrefix.tails

@[simp] public theorem collectHeads_length
    (children : List DepthPrefix) (offset : ℕ) :
    (collectHeads children offset).length = children.length := by
  induction children generalizing offset with
  | nil => rfl
  | cons child children ih =>
      simp [collectHeads, ih]

/-- Assemble the prefixes of all children below one application root. -/
@[expose] public def assemble
    (symbol : ℕ) (children : List DepthPrefix) : DepthPrefix :=
  { head := .app symbol (collectHeads children 0)
    tails := collectTails children }

@[simp] public theorem assemble_tails
    (symbol : ℕ) (children : List DepthPrefix) :
    (assemble symbol children).tails = children.flatMap DepthPrefix.tails :=
  rfl

private theorem collectHeads_variablesBelow
    (children : List DepthPrefix) (offset : ℕ)
    (hvalid : ∀ child ∈ children, child.Valid) :
    ∀ head ∈ collectHeads children offset,
      head.VariablesBelow (offset + (collectTails children).length) := by
  induction children generalizing offset with
  | nil => simp [collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | hhead
      · apply FiniteHead.VariablesBelow.mono
          (m := offset + child.tails.length)
          (n := offset + (collectTails (child :: children)).length)
        · simp [collectTails]
        · exact FiniteHead.variablesBelow_shiftVariables
            (hvalid child (by simp))
      · have htailValid : ∀ item ∈ children, item.Valid := by
          intro item hitem
          exact hvalid item (by simp [hitem])
        have hrest := ih (offset + child.tails.length) htailValid head hhead
        simpa [collectTails, Nat.add_assoc] using hrest

private theorem collectHeads_depth_le
    (children : List DepthPrefix) (offset bound : ℕ)
    (hdepth : ∀ child ∈ children, child.head.depth ≤ bound) :
    ∀ head ∈ collectHeads children offset, head.depth ≤ bound := by
  induction children generalizing offset with
  | nil => simp [collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | hhead
      · simpa using hdepth child (by simp)
      · exact ih (offset + child.tails.length)
          (fun item hitem => hdepth item (by simp [hitem]))
          head hhead

private theorem collectHeads_rankedBy
    (children : List DepthPrefix) (offset : ℕ) (ranks : List ℕ)
    (hranked : ∀ child ∈ children, child.head.RankedBy ranks) :
    ∀ head ∈ collectHeads children offset, head.RankedBy ranks := by
  induction children generalizing offset with
  | nil => simp [collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | hhead
      · exact FiniteHead.rankedBy_shiftVariables
          (hranked child (by simp))
      · apply ih (offset + child.tails.length)
        · intro item hitem
          exact hranked item (by simp [hitem])
        · exact hhead

private theorem evaluate_collectHeads
    (children : List DepthPrefix) (leading : List RegularTerm)
    (hvalid : ∀ child ∈ children, child.Valid) :
    (collectHeads children leading.length).map (fun head =>
      head.evaluate (leading ++ collectTails children)) =
    children.map fun child => child.head.evaluate child.tails := by
  induction children generalizing leading with
  | nil => simp [collectHeads, collectTails]
  | cons child children ih =>
      simp only [collectHeads, List.map_cons]
      apply congrArg₂ List.cons
      · let remainder := collectTails children
        have hdrop :
            (leading ++ collectTails (child :: children)).drop leading.length =
              child.tails ++ remainder := by
          simp [collectTails, remainder]
        have hbelowDrop : child.head.VariablesBelow
            ((leading ++ collectTails (child :: children)).drop
              leading.length).length := by
          rw [hdrop]
          apply FiniteHead.VariablesBelow.mono
              (m := child.tails.length)
          · simp
          · exact hvalid child (by simp)
        rw [FiniteHead.evaluate_shiftVariables child.head leading.length
          (leading ++ collectTails (child :: children)) hbelowDrop]
        rw [hdrop]
        exact FiniteHead.evaluate_append_of_variablesBelow
          child.head child.tails remainder (hvalid child (by simp))
      · have htailValid : ∀ item ∈ children, item.Valid := by
          intro item hitem
          exact hvalid item (by simp [hitem])
        have hrest := ih (leading ++ child.tails) htailValid
        simpa [collectTails, List.append_assoc] using hrest

/-- Assembling valid child prefixes preserves exact boundary numbering. -/
public theorem assemble_valid
    (symbol : ℕ) (children : List DepthPrefix)
    (hvalid : ∀ child ∈ children, child.Valid) :
    (assemble symbol children).Valid := by
  unfold Valid assemble
  simp only [FiniteHead.VariablesBelow]
  intro head hhead
  simpa [collectTails] using
    collectHeads_variablesBelow children 0 hvalid head hhead

/-- Evaluation of an assembled head is exactly application of the symbol to
the evaluations of its child prefixes. -/
public theorem evaluate_assemble
    (symbol : ℕ) (children : List DepthPrefix)
    (hvalid : ∀ child ∈ children, child.Valid) :
    (assemble symbol children).head.evaluate
        (assemble symbol children).tails =
      (RegularTerm.symbolTemplate symbol children.length).instantiate
        (children.map fun child => child.head.evaluate child.tails) := by
  unfold assemble
  rw [FiniteHead.evaluate_app]
  have hheads := evaluate_collectHeads children [] hvalid
  simpa [collectTails] using congrArg (fun arguments =>
    (RegularTerm.symbolTemplate symbol children.length).instantiate arguments)
    hheads

end DepthPrefix

namespace RegularTerm

private theorem rawCompatible_mono
    {S R : ℕ → ℕ → Prop}
    (hmono : ∀ i j, S i j → R i j)
    {left right : Option RawNode}
    (hcompatible : RawCompatible S left right) :
    RawCompatible R left right := by
  cases left with
  | none => cases right <;> simp_all [RawCompatible]
  | some leftNode =>
      cases right with
      | none => simp_all [RawCompatible]
      | some rightNode =>
          cases leftNode with
          | inl x =>
              cases rightNode <;> simp_all [RawCompatible]
          | inr leftApplication =>
              cases rightNode with
              | inl y => simp_all [RawCompatible]
              | inr rightApplication =>
                  rcases leftApplication with ⟨X, leftChildren⟩
                  rcases rightApplication with ⟨Y, rightChildren⟩
                  exact ⟨hcompatible.1,
                    hcompatible.2.imp (fun i j hij => hmono i j hij)⟩

private def RootClosureRelation
    (left right : RegularTerm) (i j : ℕ) : Prop :=
  (i = left.root ∧ j = right.root) ∨ left.BisimilarAt i right j

private theorem rootClosureRelation_isBisimulation
    {left right : RegularTerm} {symbol : ℕ}
    {leftChildren rightChildren : List ℕ}
    (hleft : left.rootApplication? = some (symbol, leftChildren))
    (hright : right.rootApplication? = some (symbol, rightChildren))
    (hchildren : List.Forall₂
      (fun i j => left.BisimilarAt i right j)
      leftChildren rightChildren) :
    left.IsBisimulation right (RootClosureRelation left right) := by
  intro i j hij
  rcases hij with hroot | hbisimilar
  · rcases hroot with ⟨rfl, rfl⟩
    unfold NodeCompatible
    rw [nodeAt?_root_of_rootApplication? hleft,
      nodeAt?_root_of_rootApplication? hright]
    exact ⟨rfl, hchildren.imp (fun i j hij => Or.inr hij)⟩
  · obtain ⟨relation, hij, hrelation⟩ := hbisimilar
    exact rawCompatible_mono
      (fun child child' hchild =>
        Or.inr ⟨relation, hchild, hrelation⟩)
      (hrelation i j hij)

/-- Two application roots with the same symbol are unfolding-equivalent when
their corresponding pointed children are unfolding-equivalent. -/
public theorem unfoldingEquivalent_of_rootApplications
    {left right : RegularTerm} {symbol : ℕ}
    {leftChildren rightChildren : List ℕ}
    (hleft : left.rootApplication? = some (symbol, leftChildren))
    (hright : right.rootApplication? = some (symbol, rightChildren))
    (hchildren : List.Forall₂
      (fun i j => left.BisimilarAt i right j)
      leftChildren rightChildren) :
    left.UnfoldingEquivalent right := by
  refine ⟨RootClosureRelation left right, Or.inl ⟨rfl, rfl⟩, ?_⟩
  exact rootClosureRelation_isBisimulation hleft hright hchildren

/-- Rebuilding an application from its ordered pointed children preserves the
regular tree denoted by the original pointed graph. -/
public theorem symbolTemplate_instantiate_unfoldingEquivalent
    {term : RegularTerm} {symbol : ℕ} {children : List ℕ}
    (hclosed : term.ReferenceClosed)
    (hroot : term.rootApplication? = some (symbol, children)) :
    ((symbolTemplate symbol children.length).instantiate
        (children.map term.withRoot)).UnfoldingEquivalent term := by
  let schema := symbolTemplate symbol children.length
  let arguments := children.map term.withRoot
  let expanded := schema.instantiate arguments
  have hschemaClosed : schema.ReferenceClosed := by
    exact symbolTemplate_referenceClosed symbol children.length
  have hexpandedRoot : expanded.rootApplication? =
      some (symbol,
        ((List.range children.length).map (fun i => i + 1)).map
          (schema.resolveRHSRef arguments)) := by
    exact instantiate_rootApplication? hschemaClosed
      (symbolTemplate_rootApplication? symbol children.length)
  apply unfoldingEquivalent_of_rootApplications hexpandedRoot hroot
  rw [List.forall₂_iff_get]
  constructor
  · simp
  · intro i hleft hright
    have hi : i < children.length := by simpa using hright
    have hvariable : (schema.withRoot (i + 1)).nodeAt?
        (schema.withRoot (i + 1)).root = some (.inl i) := by
      simpa [schema] using symbolTemplate_variableNode symbol children.length i hi
    have hargument : arguments[i]? = some (term.withRoot children[i]) := by
      simp [arguments, List.getElem?_map, List.getElem?_eq_getElem hi]
    have hargumentClosed : (term.withRoot children[i]).ReferenceClosed := by
      apply withRoot_referenceClosed hclosed
      exact rootApplication_children_lt hclosed hroot children[i]
        (List.get_mem children ⟨i, hi⟩)
    have hequivalent :
        ((schema.withRoot (i + 1)).instantiate arguments).UnfoldingEquivalent
          (term.withRoot children[i]) :=
      instantiate_unfoldingEquivalent_argument hvariable hargument
        hargumentClosed
    have hbisimilar :=
      (withRoot_unfoldingEquivalent_iff_bisimilarAt expanded term
        (schema.resolveRHSRef arguments (i + 1)) children[i]).1 (by
          simpa [expanded] using hequivalent)
    simpa using hbisimilar

/-- Unfold a pointed graph down to `depth`, replacing each ordered boundary
occurrence by a fresh variable and recording its pointed subterm as a tail.
Malformed or open nodes are conservatively treated as an immediate boundary;
the ground correctness theorems rule out that branch before the requested
depth. -/
@[expose] public def depthPrefix : ℕ → RegularTerm → DepthPrefix
  | 0, term =>
      { head := .var 0
        tails := [term] }
  | depth + 1, term =>
      match term.rootApplication? with
      | none =>
          { head := .var 0
            tails := [term] }
      | some (symbol, children) =>
          DepthPrefix.assemble symbol
            (children.map fun child => depthPrefix depth (term.withRoot child))

@[simp] public theorem depthPrefix_zero (term : RegularTerm) :
    term.depthPrefix 0 =
      { head := .var 0, tails := [term] } := rfl

public theorem depthPrefix_succ_of_rootApplication
    {term : RegularTerm} {symbol : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (symbol, children))
    (depth : ℕ) :
    term.depthPrefix (depth + 1) =
      DepthPrefix.assemble symbol
        (children.map fun child =>
          (term.withRoot child).depthPrefix depth) := by
  simp [depthPrefix, hroot]

/-- Boundary numbering in every depth prefix is total and in range, including
the conservative boundary used for malformed/open roots. -/
public theorem depthPrefix_valid (term : RegularTerm) (depth : ℕ) :
    (term.depthPrefix depth).Valid := by
  induction depth generalizing term with
  | zero =>
      simp [depthPrefix, DepthPrefix.Valid, FiniteHead.VariablesBelow]
  | succ depth ih =>
      cases hroot : term.rootApplication? with
      | none =>
          simp [depthPrefix, hroot, DepthPrefix.Valid,
            FiniteHead.VariablesBelow]
      | some application =>
          rcases application with ⟨symbol, children⟩
          rw [depthPrefix_succ_of_rootApplication hroot]
          apply DepthPrefix.assemble_valid
          intro childPrefix hchildPrefix
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hchildPrefix
          exact ih (term.withRoot child)

/-- The finite head never exceeds the requested unfolding depth. -/
public theorem depthPrefix_head_depth_le
    (term : RegularTerm) (depth : ℕ) :
    (term.depthPrefix depth).head.depth ≤ depth := by
  induction depth generalizing term with
  | zero => simp [depthPrefix, FiniteHead.depth]
  | succ depth ih =>
      cases hroot : term.rootApplication? with
      | none =>
          simp [depthPrefix, hroot, FiniteHead.depth]
      | some application =>
          rcases application with ⟨symbol, children⟩
          rw [depthPrefix_succ_of_rootApplication hroot]
          unfold DepthPrefix.assemble
          simp only [FiniteHead.depth]
          have hmax :
              ((DepthPrefix.collectHeads
                (children.map fun child =>
                  (term.withRoot child).depthPrefix depth) 0).map
                FiniteHead.depth).foldr max 0 ≤ depth := by
            apply List.max_le_of_forall_le
            intro value hvalue
            obtain ⟨head, hhead, rfl⟩ := List.mem_map.mp hvalue
            have hchildDepth : ∀ childPrefix ∈
                (children.map fun child =>
                  (term.withRoot child).depthPrefix depth),
                childPrefix.head.depth ≤ depth := by
              intro childPrefix hchildPrefix
              obtain ⟨child, hchild, rfl⟩ :=
                List.mem_map.mp hchildPrefix
              exact ih (term.withRoot child)
            exact DepthPrefix.collectHeads_depth_le
              (children.map fun child =>
                (term.withRoot child).depthPrefix depth) 0 depth
              hchildDepth _ hhead
          omega

/-- A ground application root has exactly the arity declared by the rank
table. -/
public theorem Ground.root_rank_arity
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks)
    {symbol : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (symbol, children)) :
    ranks[symbol]? = some children.length := by
  have hnode := nodeAt?_root_of_rootApplication? hroot
  have hshape := hground.1
  unfold ShapeWellFormed shapeWellFormedCode at hshape
  rw [Bool.and_eq_true] at hshape
  have hmem : (.inr (symbol, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hnodeShape := (List.all_eq_true.mp hshape.2) _ hmem
  unfold nodeShapeWellFormedCode at hnodeShape
  cases hrank : ranks[symbol]? with
  | none => simp [hrank] at hnodeShape
  | some rank =>
      simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hnodeShape
      simpa [hnodeShape.1] using hrank

/-- Every ground pointed graph has an application at its distinguished root. -/
public theorem Ground.exists_rootApplication
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) :
    ∃ symbol children,
      term.rootApplication? = some (symbol, children) := by
  obtain ⟨hshape, support, hsupport, hwitness⟩ := hground
  obtain ⟨symbol, children, hnode, hchildren⟩ :=
    hwitness.2 term.root hwitness.1
  refine ⟨symbol, children, ?_⟩
  simp [rootApplication?, rootNode?, hnode]

/-- The finite head extracted from a ground ranked term respects the same rank
table at every application. -/
public theorem depthPrefix_head_rankedBy
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    (term.depthPrefix depth).head.RankedBy ranks := by
  induction depth generalizing term with
  | zero => simp [depthPrefix, FiniteHead.RankedBy]
  | succ depth ih =>
      cases hroot : term.rootApplication? with
      | none => simp [depthPrefix, hroot, FiniteHead.RankedBy]
      | some application =>
          rcases application with ⟨symbol, children⟩
          rw [depthPrefix_succ_of_rootApplication hroot]
          unfold DepthPrefix.assemble
          simp only [FiniteHead.RankedBy,
            DepthPrefix.collectHeads_length, List.length_map]
          constructor
          · exact hground.root_rank_arity hroot
          · apply DepthPrefix.collectHeads_rankedBy
            intro childPrefix hchildPrefix
            obtain ⟨child, hchild, rfl⟩ :=
              List.mem_map.mp hchildPrefix
            have hrootNode := nodeAt?_root_of_rootApplication? hroot
            exact ih (hground.withRoot_descendant
              (.child .root hrootNode hchild))

/-- Grammar-uniform bound on the number of ordered boundary occurrences in a
depth prefix. -/
@[expose] public def depthPrefixTailBound (ranks : List ℕ) : ℕ → ℕ
  | 0 => 1
  | depth + 1 =>
      (ranks.foldr max 0) * depthPrefixTailBound ranks depth

private theorem sum_map_le_length_mul
    {A : Type} (values : List A) (weight : A → ℕ) (bound : ℕ)
    (hbound : ∀ value ∈ values, weight value ≤ bound) :
    (values.map weight).sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul]
      have hhead := hbound value (by simp)
      have htail := ih (fun item hitem => hbound item (by simp [hitem]))
      omega

/-- The tail tuple extracted at fixed depth is bounded solely by the finite
rank table and that depth. -/
public theorem depthPrefix_tails_length_le
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    (term.depthPrefix depth).tails.length ≤
      depthPrefixTailBound ranks depth := by
  induction depth generalizing term with
  | zero => simp [depthPrefix, depthPrefixTailBound]
  | succ depth ih =>
      obtain ⟨symbol, children, hroot⟩ := hground.exists_rootApplication
      rw [depthPrefix_succ_of_rootApplication hroot]
      simp only [DepthPrefix.assemble_tails, List.length_flatMap,
        List.map_map, Function.comp_def, depthPrefixTailBound]
      have hrootNode := nodeAt?_root_of_rootApplication? hroot
      have hchildren : ∀ child ∈ children,
          ((term.withRoot child).depthPrefix depth).tails.length ≤
            depthPrefixTailBound ranks depth := by
        intro child hchild
        exact ih (hground.withRoot_descendant
          (.child .root hrootNode hchild))
      apply le_trans
        (sum_map_le_length_mul children
          (fun child => ((term.withRoot child).depthPrefix depth).tails.length)
          (depthPrefixTailBound ranks depth) hchildren)
      apply Nat.mul_le_mul_right
      exact List.le_max_of_le
        (List.mem_of_getElem? (hground.root_rank_arity hroot))
        (le_refl _)

/-- Every tail generated from a ground term is itself ground. -/
public theorem depthPrefix_tails_ground
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    ∀ tail ∈ (term.depthPrefix depth).tails, tail.Ground ranks := by
  induction depth generalizing term with
  | zero =>
      intro tail htail
      simp [depthPrefix] at htail
      subst tail
      exact hground
  | succ depth ih =>
      cases hroot : term.rootApplication? with
      | none =>
          intro tail htail
          simp [depthPrefix, hroot] at htail
          subst tail
          exact hground
      | some application =>
          rcases application with ⟨symbol, children⟩
          rw [depthPrefix_succ_of_rootApplication hroot]
          simp only [DepthPrefix.assemble_tails, List.mem_flatMap,
            List.mem_map]
          rintro tail ⟨childPrefix, ⟨child, hchild, rfl⟩, htail⟩
          have hclosed := referenceClosed_of_ground hground
          have hchildBound := rootApplication_children_lt hclosed hroot
            child hchild
          have hrootNode : term.nodeAt? term.root =
              some (.inr (symbol, children)) := by
            unfold rootApplication? rootNode? at hroot
            cases hnode : term.nodeAt? term.root with
            | none => simp [hnode] at hroot
            | some node =>
                cases node with
                | inl x => simp [hnode] at hroot
                | inr app =>
                    simpa [hnode] using congrArg some hroot
          have hsupport : term.DescendantAt 1 child :=
            .child .root hrootNode hchild
          exact ih (hground.withRoot_descendant hsupport) tail htail

/-- Evaluating the finite head over the ordered tails of a depth prefix
reconstructs the original ground regular tree.  Equality is semantic because
the evaluator deliberately introduces graph sharing and unreachable template
nodes. -/
public theorem depthPrefix_evaluate_unfoldingEquivalent
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    ((term.depthPrefix depth).head.evaluate
      (term.depthPrefix depth).tails).UnfoldingEquivalent term := by
  induction depth generalizing term with
  | zero =>
      simpa [depthPrefix, FiniteHead.evaluate] using
        unfoldingEquivalent_refl term
  | succ depth ih =>
      cases hroot : term.rootApplication? with
      | none =>
          simpa [depthPrefix, hroot, FiniteHead.evaluate] using
            unfoldingEquivalent_refl term
      | some application =>
          rcases application with ⟨symbol, children⟩
          rw [depthPrefix_succ_of_rootApplication hroot]
          let childPrefixes := children.map fun child =>
            (term.withRoot child).depthPrefix depth
          have hclosed := referenceClosed_of_ground hground
          have hchildBound := rootApplication_children_lt hclosed hroot
          have hrootNode : term.nodeAt? term.root =
              some (.inr (symbol, children)) :=
            nodeAt?_root_of_rootApplication? hroot
          have hchildGround : ∀ child ∈ children,
              (term.withRoot child).Ground ranks := by
            intro child hchild
            exact hground.withRoot_descendant
              (.child .root hrootNode hchild)
          have hvalid : ∀ childPrefix ∈ childPrefixes,
              childPrefix.Valid := by
            intro childPrefix hchildPrefix
            obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hchildPrefix
            exact depthPrefix_valid (term.withRoot child) depth
          rw [DepthPrefix.evaluate_assemble symbol childPrefixes hvalid]
          have hchildrenEquivalent : List.Forall₂ UnfoldingEquivalent
              (children.map fun child =>
                (((term.withRoot child).depthPrefix depth).head.evaluate
                  ((term.withRoot child).depthPrefix depth).tails))
              (children.map term.withRoot) := by
            rw [List.forall₂_iff_get]
            constructor
            · simp
            · intro i hleft hright
              have hi : i < children.length := by simpa using hright
              simpa using ih (hchildGround children[i]
                (List.get_mem children ⟨i, hi⟩))
          have hleftClosed : ∀ argument ∈
              (children.map fun child =>
                (((term.withRoot child).depthPrefix depth).head.evaluate
                  ((term.withRoot child).depthPrefix depth).tails)),
              argument.ReferenceClosed := by
            intro argument hargument
            obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
            apply FiniteHead.evaluate_referenceClosed
            intro tail htail
            apply referenceClosed_of_ground
            exact depthPrefix_tails_ground
              (hchildGround child hchild) depth tail htail
          have hrightClosed : ∀ argument ∈ children.map term.withRoot,
              argument.ReferenceClosed := by
            intro argument hargument
            obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
            exact withRoot_referenceClosed hclosed
              (hchildBound child hchild)
          have hresult := (instantiate_unfoldingEquivalent
            (symbolTemplate_referenceClosed symbol children.length)
            hchildrenEquivalent hleftClosed hrightClosed).trans
              (symbolTemplate_instantiate_unfoldingEquivalent hclosed hroot)
          simpa [childPrefixes] using hresult

/-- The compiled padded depth-prefix schema denotes the original ground term. -/
public theorem depthPrefix_compiled_unfoldingEquivalent
    {ranks : List ℕ} {term filler : RegularTerm}
    (hground : term.Ground ranks) (hfiller : filler.Ground ranks)
    (depth : ℕ) :
    RegularTerm.UnfoldingEquivalent
      ((term.depthPrefix depth).head.toRegularTerm.instantiate
        ((term.depthPrefix depth).paddedArguments ranks filler)) term := by
  have hcompiled := DepthPrefix.compiled_unfoldingEquivalent_evaluate
    (depthPrefix_valid term depth)
    (depthPrefix_head_rankedBy hground depth)
    (filler := filler)
    (fun tail htail => referenceClosed_of_ground
      (depthPrefix_tails_ground hground depth tail htail))
    (referenceClosed_of_ground hfiller)
  exact hcompiled.trans
    (depthPrefix_evaluate_unfoldingEquivalent hground depth)

/-- Uniform arity bound for every depth-prefix schema at a fixed depth. -/
public theorem depthPrefix_schemaArity_le
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    (term.depthPrefix depth).schemaArity ranks ≤
      max (depthPrefixTailBound ranks depth) (ranks.foldr max 0) := by
  unfold DepthPrefix.schemaArity
  exact max_le_max_right _ (depthPrefix_tails_length_le hground depth)

/-- Uniform raw graph-size bound for every compiled depth-prefix head at a
fixed depth. -/
public theorem depthPrefix_schema_nodes_length_le
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    (term.depthPrefix depth).head.toRegularTerm.nodes.length ≤
      FiniteHead.compiledDepthBound (ranks.foldr max 0) depth := by
  rw [FiniteHead.toRegularTerm_nodes_length]
  exact FiniteHead.compiledNodeCount_le_depthBound
    (depthPrefix_head_rankedBy hground depth)
    (depthPrefix_head_depth_le term depth)

/-- The padded tuple attached to a ground prefix is ground. -/
public theorem depthPrefix_paddedArguments_ground
    {ranks : List ℕ} {term filler : RegularTerm}
    (hground : term.Ground ranks) (hfiller : filler.Ground ranks)
    (depth : ℕ) :
    ∀ argument ∈ (term.depthPrefix depth).paddedArguments ranks filler,
      argument.Ground ranks := by
  apply DepthPrefix.paddedArguments_ground
  · exact depthPrefix_tails_ground hground depth
  · exact hfiller

end RegularTerm

end DCFEquivalence
