module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveExposure

@[expose]
public section

/-!
# Variable roots of prefix-supported schemas

Semantic prefix support rules out a reachable padding variable.  If a
supported schema has a variable at its root, changing that variable while
leaving every active argument fixed would change the denoted tree unless the
variable lies inside the active prefix.
-/

namespace DCFEquivalence

namespace RegularTerm

private theorem root_variable_lt_of_wellFormed
    {ranks : List ℕ} {arity x : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks arity)
    (hroot : term.rootNode? = some (.inl x)) :
    x < arity := by
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hnode : term.nodeAt? term.root = some (.inl x) := by
    simpa [rootNode?] using hroot
  have hmem : (.inl x : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  simpa [nodeWellFormedCode] using of_decide_eq_true hwell

private theorem identity_freshened_agree_through
    {arity width x : ℕ} (hx : x < arity)
    (hinactive : width ≤ x) :
    ArgumentsEquivalentThrough width
      (identityArguments arity)
      (freshenedIdentityArguments arity x) := by
  intro i hi
  have hiArity : i < arity := by omega
  have hix : i ≠ x := by omega
  exact ⟨variableTerm i, variableTerm i,
    identityArguments_getElem? hiArity,
    freshenedIdentityArguments_getElem?_ne hiArity hix,
    unfoldingEquivalent_refl _⟩

/-- A reachable variable at the root of a prefix-supported schema necessarily
names one of its active arguments. -/
public theorem SupportedByPrefix.variableIndex_lt_width_of_root
    {ranks : List ℕ} {arity width x : ℕ} {residual : RegularTerm}
    (hsupported : SupportedByPrefix ranks arity width residual)
    (hroot : residual.rootNode? = some (.inl x)) :
    x < width := by
  have hxArity : x < arity :=
    root_variable_lt_of_wellFormed hsupported.1 hroot
  by_contra hxWidth
  have hinactive : width ≤ x := Nat.le_of_not_gt hxWidth
  have hequivalent := hsupported.2.2
    (identityArguments arity)
    (freshenedIdentityArguments arity x)
    (identityArguments_length arity)
    (freshenedIdentityArguments_length arity x)
    (identityArguments_referenceClosed arity)
    (freshenedIdentityArguments_referenceClosed hxArity)
    (identity_freshened_agree_through hxArity hinactive)
  have hrootNode : residual.nodeAt? residual.root = some (.inl x) := by
    simpa [rootNode?] using hroot
  have hidentity := instantiate_unfoldingEquivalent_argument
    hrootNode (identityArguments_getElem? hxArity)
    (variableTerm_referenceClosed x)
  have hfreshened := instantiate_unfoldingEquivalent_argument
    hrootNode (freshenedIdentityArguments_getElem?_eq hxArity)
    (variableTerm_referenceClosed arity)
  have hvariables :
      (variableTerm x).UnfoldingEquivalent (variableTerm arity) :=
    hidentity.symm.trans (hequivalent.trans hfreshened)
  have hrootEquality :=
    EncodedFirstOrderGrammar.rootNode?_variable_of_unfoldingEquivalent
    hvariables (variableTerm_rootNode? x)
  rw [variableTerm_rootNode? arity] at hrootEquality
  have hxa : x = arity := by simpa using hrootEquality.symm
  omega

end RegularTerm

end DCFEquivalence
