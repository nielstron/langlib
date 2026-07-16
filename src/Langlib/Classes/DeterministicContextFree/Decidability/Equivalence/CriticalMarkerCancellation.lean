module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalWorstInstance
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteUnfoldingDepth

@[expose]
public section

/-!
# Cancellation of the critical-marker substitution

The canonical critical tuple substitutes pairwise distinct fresh nullary
symbols for the formal parameters of an open schema.  Consequently this
substitution is faithful for unfolding equality: an application node still
has an original symbol, while a substituted variable has its uniquely
assigned fresh marker symbol.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private theorem forall₂_of_forall₂_map
    {A B C D : Type} {R : C → D → Prop}
    {P : A → Prop} {Q : B → Prop}
    (f : A → C) (g : B → D)
    {left : List A} {right : List B}
    (hrel : List.Forall₂ R (left.map f) (right.map g))
    (hleft : ∀ value ∈ left, P value)
    (hright : ∀ value ∈ right, Q value) :
    List.Forall₂
      (fun x y => P x ∧ Q y ∧ R (f x) (g y))
      left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons value right => cases hrel
  | cons value left ih =>
      cases right with
      | nil => cases hrel
      | cons value' right =>
          cases hrel with
          | cons hhead htail =>
              exact .cons
                ⟨hleft value (by simp),
                  hright value' (by simp), hhead⟩
                (ih htail
                  (fun item hitem => hleft item (by simp [hitem]))
                  (fun item hitem => hright item (by simp [hitem])))

private theorem RegularTerm.WellFormed.symbol_lt_of_nodeAt
    {term : RegularTerm} {ranks : List ℕ} {arity i X : ℕ}
    {children : List ℕ}
    (hterm : term.WellFormed ranks arity)
    (hnode : term.nodeAt? i = some (.inr (X, children))) :
    X < ranks.length := by
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  unfold RegularTerm.nodeWellFormedCode at hwell
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hwell
  | some rank => exact (List.getElem?_eq_some_iff.mp hrank).1

private theorem criticalInstantiation_nodeAt_resolved_variable
    (g : EncodedFirstOrderGrammar Action)
    {schema : RegularTerm} {arity i x : ℕ}
    (hnode : schema.nodeAt? i = some (.inl x))
    (hx : x < arity) :
    (schema.instantiate (g.criticalArguments arity)).nodeAt?
        (schema.resolveRHSRef (g.criticalArguments arity) i) =
      some (.inr (g.criticalMarkerSymbol x, [])) := by
  have hargument := g.criticalArguments_getElem? hx
  have hmarkerNode :
      (g.criticalMarker x).nodeAt? 0 =
        some (.inr (g.criticalMarkerSymbol x, [])) := by
    simp [criticalMarker, RegularTerm.nodeAt?, RegularTerm.nodes]
  have hinstantiated :=
    RegularTerm.instantiate_nodeAt?_argument schema
      (g.criticalArguments arity) hargument hmarkerNode
  unfold RegularTerm.resolveRHSRef
  rw [hnode]
  simp only [RegularTerm.argumentRoot?, hargument,
    Option.map_some, Option.getD_some, criticalMarker_root,
    Nat.add_zero]
  simpa [RegularTerm.shiftNode] using hinstantiated

private theorem criticalInstantiation_nodeAt_resolved_application
    (g : EncodedFirstOrderGrammar Action)
    {schema : RegularTerm} {arity i X : ℕ}
    {children : List ℕ}
    (hnode : schema.nodeAt? i = some (.inr (X, children))) :
    (schema.instantiate (g.criticalArguments arity)).nodeAt?
        (schema.resolveRHSRef (g.criticalArguments arity) i) =
      some (.inr (X,
        children.map
          (schema.resolveRHSRef (g.criticalArguments arity)))) := by
  have hi : i < schema.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hinstantiated :=
    RegularTerm.instantiate_nodeAt?_rhs schema
      (g.criticalArguments arity) hi
  unfold RegularTerm.resolveRHSRef
  rw [hnode]
  simpa [RegularTerm.instantiateNode, hnode] using hinstantiated

/-- Instantiation by the full tuple of pairwise distinct critical markers
reflects unfolding equality of well-formed open schemas. -/
public theorem unfoldingEquivalent_of_criticalInstantiation
    (g : EncodedFirstOrderGrammar Action)
    {arity : ℕ} {left right : RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hcritical :
      (left.instantiate (g.criticalArguments arity))
        |>.UnfoldingEquivalent
          (right.instantiate (g.criticalArguments arity))) :
    left.UnfoldingEquivalent right := by
  obtain ⟨R, hroots, hR⟩ := hcritical
  let S : ℕ → ℕ → Prop := fun i j =>
    i < left.nodes.length ∧ j < right.nodes.length ∧
      R (left.resolveRHSRef (g.criticalArguments arity) i)
        (right.resolveRHSRef (g.criticalArguments arity) j)
  have hleftClosed :=
    RegularTerm.referenceClosed_of_wellFormed hleft
  have hrightClosed :=
    RegularTerm.referenceClosed_of_wellFormed hright
  refine ⟨S, ?_, ?_⟩
  · refine ⟨hleftClosed.1, hrightClosed.1, ?_⟩
    simpa [RegularTerm.instantiate, RegularTerm.root] using hroots
  · intro i j hij
    rcases hij with ⟨hi, hj, hij⟩
    let leftNode : RawNode := left.nodes[i]
    let rightNode : RawNode := right.nodes[j]
    have hleftNode : left.nodeAt? i = some leftNode := by
      unfold RegularTerm.nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hi, rfl⟩
    have hrightNode : right.nodeAt? j = some rightNode := by
      unfold RegularTerm.nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hj, rfl⟩
    have hlocal := hR _ _ hij
    unfold RegularTerm.NodeCompatible at hlocal ⊢
    cases hleftKind : leftNode with
    | inl x =>
        have hleftVariable :
            left.nodeAt? i = some (.inl x) :=
          hleftNode.trans (congrArg some hleftKind)
        have hx := hleft.variable_lt_of_nodeAt hleftVariable
        rw [criticalInstantiation_nodeAt_resolved_variable
          g hleftVariable hx] at hlocal
        cases hrightKind : rightNode with
        | inl y =>
            have hrightVariable :
                right.nodeAt? j = some (.inl y) :=
              hrightNode.trans (congrArg some hrightKind)
            have hy := hright.variable_lt_of_nodeAt hrightVariable
            rw [criticalInstantiation_nodeAt_resolved_variable
              g hrightVariable hy] at hlocal
            simp only [RegularTerm.RawCompatible] at hlocal
            have hxy : x = y := by
              unfold criticalMarkerSymbol at hlocal
              omega
            simpa [hleftNode, hrightNode, hleftKind,
              hrightKind, RegularTerm.RawCompatible] using hxy
        | inr rightApplication =>
            rcases rightApplication with ⟨Y, rightChildren⟩
            have hrightApplication :
                right.nodeAt? j =
                  some (.inr (Y, rightChildren)) :=
              hrightNode.trans (congrArg some hrightKind)
            have hY :=
              RegularTerm.WellFormed.symbol_lt_of_nodeAt
                hright hrightApplication
            rw [criticalInstantiation_nodeAt_resolved_application
              g hrightApplication] at hlocal
            simp only [RegularTerm.RawCompatible] at hlocal
            unfold criticalMarkerSymbol at hlocal
            omega
    | inr leftApplication =>
        rcases leftApplication with ⟨X, leftChildren⟩
        have hleftApplication :
            left.nodeAt? i = some (.inr (X, leftChildren)) :=
          hleftNode.trans (congrArg some hleftKind)
        have hX :=
          RegularTerm.WellFormed.symbol_lt_of_nodeAt
            hleft hleftApplication
        rw [criticalInstantiation_nodeAt_resolved_application
          g hleftApplication] at hlocal
        cases hrightKind : rightNode with
        | inl y =>
            have hrightVariable :
                right.nodeAt? j = some (.inl y) :=
              hrightNode.trans (congrArg some hrightKind)
            have hy := hright.variable_lt_of_nodeAt hrightVariable
            rw [criticalInstantiation_nodeAt_resolved_variable
              g hrightVariable hy] at hlocal
            simp only [RegularTerm.RawCompatible] at hlocal
            unfold criticalMarkerSymbol at hlocal
            omega
        | inr rightApplication =>
            rcases rightApplication with ⟨Y, rightChildren⟩
            have hrightApplication :
                right.nodeAt? j =
                  some (.inr (Y, rightChildren)) :=
              hrightNode.trans (congrArg some hrightKind)
            rw [criticalInstantiation_nodeAt_resolved_application
              g hrightApplication] at hlocal
            simp only [RegularTerm.RawCompatible] at hlocal
            rw [hleftApplication, hrightApplication]
            simp only [RegularTerm.RawCompatible]
            refine ⟨hlocal.1, ?_⟩
            apply forall₂_of_forall₂_map
              (left.resolveRHSRef (g.criticalArguments arity))
              (right.resolveRHSRef (g.criticalArguments arity))
              hlocal.2
            · intro child hchild
              exact hleftClosed.2 i X leftChildren
                hleftApplication child hchild
            · intro child hchild
              exact hrightClosed.2 j Y rightChildren
                hrightApplication child hchild

end EncodedFirstOrderGrammar

end DCFEquivalence
