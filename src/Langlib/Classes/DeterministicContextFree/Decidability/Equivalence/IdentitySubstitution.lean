module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GrammarNormalForm

@[expose]
public section

/-!
# Positional identity substitutions

The positional identity tuple of arity `n` sends formal parameter `i` to the
one-node open term denoting that same parameter.  Instantiating a well-formed
regular-term schema by this tuple preserves its unfolding.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- The positional identity tuple
`[variableTerm 0, ..., variableTerm (arity - 1)]`. -/
@[expose] public def identityArguments (arity : ℕ) : List RegularTerm :=
  (List.range arity).map variableTerm

@[simp] public theorem identityArguments_length (arity : ℕ) :
    (identityArguments arity).length = arity := by
  simp [identityArguments]

public theorem identityArguments_getElem?
    {arity i : ℕ} (hi : i < arity) :
    (identityArguments arity)[i]? = some (variableTerm i) := by
  simp [identityArguments, hi]

private theorem variableTerm_referenceClosed_for_identity (x : ℕ) :
    (variableTerm x).ReferenceClosed := by
  constructor
  · simp [variableTerm, nodes, root]
  · intro i X children hnode
    have hfalse : False := by
      have hmem : (.inr (X, children) : RawNode) ∈
          (variableTerm x).nodes := List.mem_of_getElem? hnode
      simp [variableTerm, nodes] at hmem
    exact hfalse.elim

/-- Every component of the positional identity tuple is reference closed. -/
public theorem identityArguments_referenceClosed (arity : ℕ) :
    ∀ argument ∈ identityArguments arity, argument.ReferenceClosed := by
  intro argument hargument
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hargument
  exact variableTerm_referenceClosed_for_identity i

private theorem variable_lt_of_wellFormed
    {ranks : List ℕ} {arity : ℕ} {schema : RegularTerm}
    (hschema : schema.WellFormed ranks arity)
    {i x : ℕ} (hnode : schema.nodeAt? i = some (.inl x)) :
    x < arity := by
  unfold WellFormed wellFormedCode at hschema
  rw [Bool.and_eq_true] at hschema
  have hmem : (.inl x : RawNode) ∈ schema.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hschema.2) _ hmem
  simpa [nodeWellFormedCode] using of_decide_eq_true hwell

private def IdentityInstantiationRelation
    (schema : RegularTerm) (arity : ℕ) (i j : ℕ) : Prop :=
  j < schema.nodes.length ∧
    i = schema.resolveRHSRef (identityArguments arity) j

private theorem forall₂_map_identityRelation
    (schema : RegularTerm) (arity : ℕ) (children : List ℕ)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length) :
    List.Forall₂ (IdentityInstantiationRelation schema arity)
      (children.map
        (schema.resolveRHSRef (identityArguments arity)))
      children := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
      exact .cons
        ⟨hchildren child (by simp), rfl⟩
        (ih fun tail htail => hchildren tail (by simp [htail]))

private theorem identityInstantiationRelation_isBisimulation
    {ranks : List ℕ} {arity : ℕ} {schema : RegularTerm}
    (hschema : schema.WellFormed ranks arity) :
    (schema.instantiate (identityArguments arity)).IsBisimulation schema
      (IdentityInstantiationRelation schema arity) := by
  intro i j hij
  rcases hij with ⟨hj, rfl⟩
  let node : RawNode := schema.nodes[j]
  have hnode : schema.nodeAt? j = some node := by
    unfold nodeAt?
    rw [List.getElem?_eq_some_iff]
    exact ⟨hj, rfl⟩
  unfold NodeCompatible
  cases hkind : node with
  | inl x =>
      have hvariable : schema.nodeAt? j = some (.inl x) := by
        simpa [hkind] using hnode
      have hx : x < arity :=
        variable_lt_of_wellFormed hschema hvariable
      have hargument :
          (identityArguments arity)[x]? = some (variableTerm x) :=
        identityArguments_getElem? hx
      have hargumentNode :
          (variableTerm x).nodeAt? 0 = some (.inl x) := by
        simpa [rootNode?] using variableTerm_rootNode? x
      have hcopied := instantiate_nodeAt?_argument
        schema (identityArguments arity) hargument hargumentNode
      have hresolve :
          schema.resolveRHSRef (identityArguments arity) j =
            argumentOffset schema.nodes.length
              (identityArguments arity) x := by
        simp [resolveRHSRef, hvariable, argumentRoot?, hargument]
      have hcopied' :
          (schema.instantiate (identityArguments arity)).nodeAt?
              (argumentOffset schema.nodes.length
                (identityArguments arity) x) =
            some (.inl x) := by
        simpa [shiftNode] using hcopied
      rw [hresolve, hcopied', hvariable]
      simp [RawCompatible]
  | inr app =>
      rcases app with ⟨X, children⟩
      have happlication :
          schema.nodeAt? j = some (.inr (X, children)) := by
        simpa [hkind] using hnode
      have hresolve :
          schema.resolveRHSRef (identityArguments arity) j = j := by
        simp [resolveRHSRef, happlication]
      rw [hresolve,
        instantiate_nodeAt?_rhs schema (identityArguments arity) hj,
        happlication]
      simp only [Option.map_some, instantiateNode, RawCompatible]
      refine ⟨trivial, forall₂_map_identityRelation schema arity children ?_⟩
      exact (referenceClosed_of_wellFormed hschema).2
        j X children happlication

/-- Instantiating a well-formed schema with its positional identity tuple
preserves the regular tree denoted by the schema. -/
public theorem instantiate_identity_unfoldingEquivalent
    {ranks : List ℕ} {arity : ℕ} {schema : RegularTerm}
    (hschema : schema.WellFormed ranks arity) :
    (schema.instantiate (identityArguments arity)).UnfoldingEquivalent
      schema := by
  refine ⟨IdentityInstantiationRelation schema arity, ?_,
    identityInstantiationRelation_isBisimulation hschema⟩
  exact ⟨(referenceClosed_of_wellFormed hschema).1, rfl⟩

end RegularTerm

end DCFEquivalence
