module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SubstitutionComposition

@[expose]
public section

/-!
# Well-formedness of simultaneous substitution

Substitution retains the schema's variable nodes as unreachable graph nodes.
Consequently the correct global variable bound for an instantiated graph is
the maximum of the schema arity and the variable bound of the copied argument
graphs.  This module records that structural invariant independently of
groundness.
-/

namespace DCFEquivalence

namespace RegularTerm

@[simp] public theorem instantiate_nodes_length
    (schema : RegularTerm) (arguments : List RegularTerm) :
    (schema.instantiate arguments).nodes.length =
      schema.nodes.length +
        (arguments.map fun argument => argument.nodes.length).sum := by
  simp [instantiate, nodes, appendArguments_length]

/-- Rank and variable-index validity of a node, leaving reference bounds to a
separate `ReferenceClosed` invariant. -/
private def LocallyWellFormed
    (ranks : List ℕ) (variableBound : ℕ) : RawNode → Prop
  | .inl x => x < variableBound
  | .inr (X, children) =>
      ∃ rank, ranks[X]? = some rank ∧ children.length = rank

private theorem locallyWellFormed_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound) :
    ∀ node ∈ term.nodes, LocallyWellFormed ranks variableBound node := by
  intro node hnode
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hlocal := (List.all_eq_true.mp hterm.2) node hnode
  cases node with
  | inl x =>
      simpa [LocallyWellFormed, nodeWellFormedCode] using
        of_decide_eq_true hlocal
  | inr application =>
      rcases application with ⟨X, children⟩
      unfold nodeWellFormedCode at hlocal
      cases hrank : ranks[X]? with
      | none => simp [hrank] at hlocal
      | some rank =>
          simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hlocal
          exact ⟨rank, hrank, hlocal.1⟩

private theorem LocallyWellFormed.mono
    {ranks : List ℕ} {small large : ℕ} {node : RawNode}
    (hbound : small ≤ large)
    (hnode : LocallyWellFormed ranks small node) :
    LocallyWellFormed ranks large node := by
  cases node with
  | inl x =>
      simp only [LocallyWellFormed] at hnode ⊢
      omega
  | inr application => exact hnode

private theorem locallyWellFormed_shiftNode
    {ranks : List ℕ} {variableBound offset : ℕ} {node : RawNode}
    (hnode : LocallyWellFormed ranks variableBound node) :
    LocallyWellFormed ranks variableBound (shiftNode offset node) := by
  cases node with
  | inl x => exact hnode
  | inr application =>
      rcases application with ⟨X, children⟩
      obtain ⟨rank, hrank, hlength⟩ := hnode
      exact ⟨rank, hrank, by simpa [shiftNode] using hlength⟩

private theorem appendArguments_locallyWellFormed
    {ranks : List ℕ} {variableBound : ℕ}
    {arguments : List RegularTerm}
    (harguments : ∀ argument ∈ arguments,
      argument.WellFormed ranks variableBound) (offset : ℕ) :
    ∀ node ∈ appendArguments offset arguments,
      LocallyWellFormed ranks variableBound node := by
  induction arguments generalizing offset with
  | nil => simp [appendArguments]
  | cons argument arguments ih =>
      rw [appendArguments_cons]
      intro node hnode
      rw [List.mem_append] at hnode
      rcases hnode with hargumentNode | hrestNode
      · obtain ⟨source, hsource, rfl⟩ :=
          List.mem_map.mp hargumentNode
        apply locallyWellFormed_shiftNode
        exact locallyWellFormed_of_wellFormed
          (harguments argument (by simp)) source hsource
      · exact ih
          (fun item hitem => harguments item (by simp [hitem]))
          (offset + argument.nodes.length) node hrestNode

private theorem instantiate_locallyWellFormed
    {ranks : List ℕ} {variableBound : ℕ}
    {schema : RegularTerm} {arguments : List RegularTerm}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.WellFormed ranks variableBound) :
    ∀ node ∈ (schema.instantiate arguments).nodes,
      LocallyWellFormed ranks (max arguments.length variableBound) node := by
  intro node hnode
  unfold instantiate nodes at hnode
  rw [List.mem_append] at hnode
  rcases hnode with hschemaNode | hargumentNode
  · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hschemaNode
    have hsourceLocal := locallyWellFormed_of_wellFormed hschema
      source hsource
    cases source with
    | inl x =>
        apply LocallyWellFormed.mono (Nat.le_max_left _ _)
        exact hsourceLocal
    | inr application =>
        rcases application with ⟨X, children⟩
        obtain ⟨rank, hrank, hlength⟩ := hsourceLocal
        exact ⟨rank, hrank, by
          simpa [instantiateNode] using hlength⟩
  · apply LocallyWellFormed.mono (Nat.le_max_right _ _)
    exact appendArguments_locallyWellFormed harguments
      schema.nodes.length node hargumentNode

/-- Increasing only the admitted variable-index bound preserves structural
well-formedness. -/
public theorem WellFormed.mono
    {ranks : List ℕ} {small large : ℕ} {term : RegularTerm}
    (hbound : small ≤ large)
    (hterm : term.WellFormed ranks small) :
    term.WellFormed ranks large := by
  have hclosed := referenceClosed_of_wellFormed hterm
  unfold WellFormed wellFormedCode
  rw [Bool.and_eq_true]
  constructor
  · exact decide_eq_true hclosed.1
  · apply List.all_eq_true.mpr
    intro node hnode
    have hlocal := (locallyWellFormed_of_wellFormed hterm node hnode).mono
      hbound
    cases node with
    | inl x => exact decide_eq_true hlocal
    | inr application =>
        rcases application with ⟨X, children⟩
        obtain ⟨rank, hrank, hlength⟩ := hlocal
        unfold nodeWellFormedCode
        simp only [hrank, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨hlength, ?_⟩
        apply List.all_eq_true.mpr
        intro child hchild
        apply decide_eq_true
        obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hnode
        exact hclosed.2 i X children (by
          unfold nodeAt?
          rw [List.getElem?_eq_some_iff]
          exact ⟨hi, hget⟩) child hchild

/-- Simultaneous substitution preserves ranked graph well-formedness.  The
maximum is necessary because unreachable variable nodes from both the schema
and copied arguments remain in the raw presentation. -/
public theorem instantiate_wellFormed_max
    {ranks : List ℕ} {variableBound : ℕ}
    {schema : RegularTerm} {arguments : List RegularTerm}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.WellFormed ranks variableBound) :
    (schema.instantiate arguments).WellFormed ranks
      (max arguments.length variableBound) := by
  have hschemaClosed := referenceClosed_of_wellFormed hschema
  have hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed := by
    intro argument hargument
    exact referenceClosed_of_wellFormed
      (harguments argument hargument)
  have hclosed := instantiate_referenceClosed hschemaClosed hargumentsClosed
  unfold WellFormed wellFormedCode
  rw [Bool.and_eq_true]
  constructor
  · exact decide_eq_true hclosed.1
  · apply List.all_eq_true.mpr
    intro node hnode
    have hlocal := instantiate_locallyWellFormed hschema harguments
      node hnode
    cases node with
    | inl x =>
        exact decide_eq_true hlocal
    | inr application =>
        rcases application with ⟨X, children⟩
        obtain ⟨rank, hrank, hlength⟩ := hlocal
        unfold nodeWellFormedCode
        simp only [hrank, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨hlength, ?_⟩
        apply List.all_eq_true.mpr
        intro child hchild
        apply decide_eq_true
        obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hnode
        apply hclosed.2 i X children
        · unfold nodeAt?
          rw [List.getElem?_eq_some_iff]
          exact ⟨hi, hget⟩
        · exact hchild

end RegularTerm

end DCFEquivalence
