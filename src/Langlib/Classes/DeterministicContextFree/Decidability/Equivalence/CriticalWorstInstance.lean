module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkers
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SubstitutionComposition

@[expose]
public section

/-!
# Critical substitutions are worst instances

The fresh nullary markers expose the first formal parameter reached by an
execution.  Consequently, two open terms which agree through a fixed depth
after the marker substitution also agree through that depth after every
ground substitution.  This file proves the operational statement used by
`CriticalInstanceFamily.worst`.

Symbolic root rewriting leaves unreachable variable nodes in graph codes.
Residual schemas therefore need not remain globally `WellFormed` at their
original arity.  The proof tracks the two invariants actually preserved by
rewriting: reference closure and the fact that every application symbol is an
original grammar symbol.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- A closed one-node presentation of a free variable.  It is used only as a
semantic representative when a raw substitution leaves an unbound variable
unchanged. -/
private def variableTerm (x : ℕ) : RegularTerm :=
  ([.inl x], 0)

private theorem variableTerm_referenceClosed (x : ℕ) :
    (variableTerm x).ReferenceClosed := by
  constructor
  · simp [variableTerm, nodes, root]
  · intro i X children hnode
    have hfalse : False := by
      have hmem : (.inr (X, children) : RawNode) ∈
          (variableTerm x).nodes := List.mem_of_getElem? hnode
      simpa [variableTerm, nodes] using hmem
    exact hfalse.elim

private theorem variableTerm_rootNode? (x : ℕ) :
    (variableTerm x).rootNode? = some (.inl x) := by
  simp [variableTerm, rootNode?, nodeAt?, nodes, root]

private theorem variableTerm_rootApplication? (x : ℕ) :
    (variableTerm x).rootApplication? = none := by
  simp [rootApplication?, variableTerm_rootNode?]

private theorem instantiate_rootNode?_variable_none
    {schema : RegularTerm} {arguments : List RegularTerm} {x : ℕ}
    (hclosed : schema.ReferenceClosed)
    (hroot : schema.nodeAt? schema.root = some (.inl x))
    (hargument : arguments[x]? = none) :
    (schema.instantiate arguments).rootNode? = some (.inl x) := by
  have hresolve : schema.resolveRHSRef arguments schema.root =
      schema.root := by
    simp [resolveRHSRef, hroot, argumentRoot?, hargument]
  unfold rootNode?
  change (schema.instantiate arguments).nodeAt?
      (schema.resolveRHSRef arguments schema.root) = some (.inl x)
  rw [hresolve, instantiate_nodeAt?_rhs schema arguments hclosed.1,
    hroot]
  rfl

/-- Instantiating a schema whose root is variable `x` denotes either the
supplied `x`th argument or, when `x` is unbound, the canonical free-variable
representative. -/
private theorem instantiate_unfoldingEquivalent_parameter
    {schema : RegularTerm} {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.ReferenceClosed)
    (hroot : schema.nodeAt? schema.root = some (.inl x))
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    (schema.instantiate arguments).UnfoldingEquivalent
      ((arguments[x]?).getD (variableTerm x)) := by
  cases hargument : arguments[x]? with
  | some argument =>
      simpa [hargument] using
        instantiate_unfoldingEquivalent_argument hroot hargument
          (harguments argument (List.mem_of_getElem? hargument))
  | none =>
      simp only [hargument, Option.getD_none]
      have hsourceRoot := instantiate_rootNode?_variable_none
        hschema hroot hargument
      let R : ℕ → ℕ → Prop := fun i j =>
        i = (schema.instantiate arguments).root ∧ j = 0
      refine ⟨R, ⟨rfl, rfl⟩, ?_⟩
      intro i j hij
      rcases hij with ⟨rfl, rfl⟩
      change RawCompatible R (schema.instantiate arguments).rootNode?
        (variableTerm x).rootNode?
      rw [hsourceRoot, variableTerm_rootNode?]
      simp [RawCompatible]

/-- Every application node of `term` uses a symbol from the original rank
table with its declared arity.  Variables and reachability are deliberately
irrelevant. -/
@[expose] public def UsesOriginalSymbols
    (ranks : List ℕ) (term : RegularTerm) : Prop :=
  ∀ X children, (.inr (X, children) : RawNode) ∈ term.nodes →
    ∃ rank, ranks[X]? = some rank ∧ children.length = rank

public theorem usesOriginalSymbols_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound) :
    UsesOriginalSymbols ranks term := by
  intro X children hnode
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hwell := (List.all_eq_true.mp hterm.2) _ hnode
  unfold nodeWellFormedCode at hwell
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hwell
  | some rank =>
      simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hwell
      exact ⟨rank, rfl, hwell.1⟩

public theorem usesOriginalSymbols_withRoot
    {ranks : List ℕ} {term : RegularTerm}
    (hterm : UsesOriginalSymbols ranks term) (root : ℕ) :
    UsesOriginalSymbols ranks (term.withRoot root) := by
  intro X children hnode
  exact hterm X children hnode

private theorem appendArguments_usesOriginalSymbols
    {ranks : List ℕ} {arguments : List RegularTerm}
    (harguments : ∀ argument ∈ arguments,
      UsesOriginalSymbols ranks argument) (offset : ℕ) :
    ∀ X children,
      (.inr (X, children) : RawNode) ∈ appendArguments offset arguments →
      ∃ rank, ranks[X]? = some rank ∧ children.length = rank := by
  induction arguments generalizing offset with
  | nil => simp [appendArguments]
  | cons argument arguments ih =>
      rw [appendArguments_cons]
      intro X children hnode
      rw [List.mem_append] at hnode
      rcases hnode with hhead | htail
      · obtain ⟨source, hsource, hshift⟩ := List.mem_map.mp hhead
        cases hkind : source with
        | inl x => simp [hkind, shiftNode] at hshift
        | inr app =>
            rcases app with ⟨Y, sourceChildren⟩
            simp only [hkind, shiftNode, Sum.inr.injEq,
              Prod.mk.injEq] at hshift
            have hsource' :
                (.inr (Y, sourceChildren) : RawNode) ∈ argument.nodes := by
              simpa [hkind] using hsource
            obtain ⟨rank, hrank, hlength⟩ :=
              harguments argument (by simp) Y sourceChildren hsource'
            refine ⟨rank, ?_, ?_⟩
            · simpa [hshift.1] using hrank
            · rw [← hshift.2, List.length_map]
              exact hlength
      · exact ih
          (fun term hterm => harguments term (by simp [hterm]))
          (offset + argument.nodes.length) X children htail

public theorem usesOriginalSymbols_instantiate
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm}
    (hschema : UsesOriginalSymbols ranks schema)
    (harguments : ∀ argument ∈ arguments,
      UsesOriginalSymbols ranks argument) :
    UsesOriginalSymbols ranks (schema.instantiate arguments) := by
  intro X children hnode
  unfold instantiate nodes at hnode
  rw [List.mem_append] at hnode
  rcases hnode with hschemaNode | hargumentNode
  · obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hschemaNode
    cases hkind : source with
    | inl x => simp [hkind, instantiateNode] at hsourceEq
    | inr app =>
        rcases app with ⟨Y, sourceChildren⟩
        simp only [hkind, instantiateNode, Sum.inr.injEq,
          Prod.mk.injEq] at hsourceEq
        have hsource' :
            (.inr (Y, sourceChildren) : RawNode) ∈ schema.nodes := by
          simpa [hkind] using hsource
        obtain ⟨rank, hrank, hlength⟩ :=
          hschema Y sourceChildren hsource'
        refine ⟨rank, ?_, ?_⟩
        · simpa [hsourceEq.1] using hrank
        · rw [← hsourceEq.2, List.length_map]
          exact hlength
  · exact appendArguments_usesOriginalSymbols harguments
      schema.nodes.length X children hargumentNode

private theorem rootApplication?_of_root_node
    {term : RegularTerm} {X : ℕ} {children : List ℕ}
    (hroot : term.nodeAt? term.root = some (.inr (X, children))) :
    term.rootApplication? = some (X, children) := by
  simp [rootApplication?, rootNode?, hroot]

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The critical substitution of arity `arity`: formal parameter `i` is sent
to fresh marker `i`. -/
@[expose] public def criticalArguments
    (g : EncodedFirstOrderGrammar Action) (arity : ℕ) :
    List RegularTerm :=
  (List.range arity).map g.criticalMarker

private def criticalParameterTerm
    (g : EncodedFirstOrderGrammar Action) (arity x : ℕ) : RegularTerm :=
  if x < arity then g.criticalMarker x else RegularTerm.variableTerm x

private def criticalParameterLabel (arity x : ℕ) : Label (Action ⊕ ℕ) :=
  if x < arity then .inl (.inr x) else .inr x

@[simp] public theorem criticalArguments_length
    (g : EncodedFirstOrderGrammar Action) (arity : ℕ) :
    (g.criticalArguments arity).length = arity := by
  simp [criticalArguments]

public theorem criticalArguments_getElem?
    (g : EncodedFirstOrderGrammar Action) {arity i : ℕ}
    (hi : i < arity) :
    (g.criticalArguments arity)[i]? = some (g.criticalMarker i) := by
  simp [criticalArguments, List.getElem?_map, hi]

public theorem criticalArguments_ground
    (g : EncodedFirstOrderGrammar Action) (arity : ℕ) :
    ∀ argument ∈ g.criticalArguments arity,
      argument.Ground (g.withCriticalMarkers arity).ranks := by
  intro argument hargument
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hargument
  exact g.criticalMarker_ground (by simpa using hi)

/-- The arity-sized critical tuple is ground in every marker extension large
enough to contain it. -/
public theorem criticalArguments_ground_of_le
    (g : EncodedFirstOrderGrammar Action) {arity count : ℕ}
    (hcount : arity ≤ count) :
    ∀ argument ∈ g.criticalArguments arity,
      argument.Ground (g.withCriticalMarkers count).ranks := by
  intro argument hargument
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hargument
  apply g.criticalMarker_ground
  exact lt_of_lt_of_le (by simpa using hi) hcount

private theorem criticalArguments_referenceClosed
    (g : EncodedFirstOrderGrammar Action) (arity : ℕ) :
    ∀ argument ∈ g.criticalArguments arity,
      argument.ReferenceClosed := by
  intro argument hargument
  exact RegularTerm.referenceClosed_of_ground
    (criticalArguments_ground g arity argument hargument)

private theorem criticalParameterTerm_referenceClosed
    (g : EncodedFirstOrderGrammar Action) (arity x : ℕ) :
    (criticalParameterTerm g arity x).ReferenceClosed := by
  unfold criticalParameterTerm
  split
  · exact RegularTerm.referenceClosed_of_ground (g.criticalMarker_ground ‹_›)
  · exact RegularTerm.variableTerm_referenceClosed x

private theorem criticalArguments_parameter
    (g : EncodedFirstOrderGrammar Action) (arity x : ℕ) :
    ((g.criticalArguments arity)[x]?).getD
        (RegularTerm.variableTerm x) =
      criticalParameterTerm g arity x := by
  unfold criticalParameterTerm
  split <;> rename_i hx
  · rw [criticalArguments_getElem? g hx]
    rfl
  · rw [List.getElem?_eq_none]
    · rfl
    · simpa using Nat.le_of_not_gt hx

private theorem selected_rhs_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {X : ℕ} {action : Action} {rhs : RegularTerm}
    (hrule : g.ruleLookup X action = some rhs) :
    ∃ rank, g.ranks[X]? = some rank ∧
      rhs.WellFormed g.ranks rank := by
  unfold WellFormed wellFormedCode at hg
  rw [Bool.and_eq_true] at hg
  unfold ruleLookup at hrule
  obtain ⟨rule, hfind, hrhs⟩ := Option.map_eq_some_iff.mp hrule
  have hrow := (List.all_eq_true.mp hg.1) rule (findRule_mem hfind)
  unfold ruleWellFormedCode at hrow
  cases hrank : g.ranks[rule.lhs]? with
  | none => simp [hrank] at hrow
  | some rank =>
      rw [hrank, Bool.and_eq_true] at hrow
      have hkey := findRule_key hfind
      have hX : rule.lhs = X := hkey.1
      subst X
      have hrhsEq : rule.rhs = rhs := by simpa using hrhs
      subst rhs
      exact ⟨rank, hrank, hrow.1⟩

private theorem rank_arity_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound)
    {i X : ℕ} {children : List ℕ}
    (hnode : term.nodeAt? i = some (.inr (X, children))) :
    ∃ rank, ranks[X]? = some rank ∧ children.length = rank := by
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  unfold RegularTerm.nodeWellFormedCode at hwell
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hwell
  | some rank =>
      simp only [hrank, Bool.and_eq_true, decide_eq_true_eq] at hwell
      exact ⟨rank, rfl, hwell.1⟩

private theorem withRoot_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound)
    {i : ℕ} (hi : i < term.nodes.length) :
    (term.withRoot i).WellFormed ranks variableBound := by
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨?_, ?_⟩
  · simpa [RegularTerm.withRoot, RegularTerm.root,
      RegularTerm.nodes] using decide_eq_true hi
  · simpa [RegularTerm.withRoot, RegularTerm.nodes] using hterm.2

private theorem ruleLookup_markerAction_of_originalSymbol
    (g : EncodedFirstOrderGrammar Action) (count X i : ℕ)
    (hX : X < g.ranks.length) :
    (g.withCriticalMarkers count).ruleLookup X (.inr i) = none := by
  unfold ruleLookup findRule
  change Option.map RawRule.rhs
      (List.find? (fun rule : RawRule (Action ⊕ ℕ) =>
          rule.lhs = X ∧ rule.action = .inr i)
        (g.rawRules.map liftCriticalRule ++
          (List.range count).map g.criticalMarkerRule)) = none
  rw [List.find?_append, List.find?_map, List.find?_map]
  have horiginal : List.find?
      ((fun rule : RawRule (Action ⊕ ℕ) =>
          decide (rule.lhs = X ∧ rule.action = .inr i)) ∘
        liftCriticalRule) g.rawRules = none := by
    apply List.find?_eq_none.mpr
    intro rule hrule
    simp [liftCriticalRule, RawRule.lhs, RawRule.action]
  have hmarkers : List.find?
      ((fun rule : RawRule (Action ⊕ ℕ) =>
          decide (rule.lhs = X ∧ rule.action = .inr i)) ∘
        g.criticalMarkerRule) (List.range count) = none := by
    apply List.find?_eq_none.mpr
    intro j hj
    have hjcount : j < count := by simpa using hj
    simp [criticalMarkerRule, criticalMarkerSymbol,
      RawRule.lhs, RawRule.action]
    omega
  rw [horiginal, hmarkers]
  rfl

private theorem ruleLookup_wrongMarker
    (g : EncodedFirstOrderGrammar Action) {count i j : ℕ}
    (hj : j < count) (hne : i ≠ j) :
    (g.withCriticalMarkers count).ruleLookup
      (g.criticalMarkerSymbol j) (.inr i) = none := by
  unfold ruleLookup findRule
  change Option.map RawRule.rhs
      (List.find? (fun rule : RawRule (Action ⊕ ℕ) =>
          rule.lhs = g.criticalMarkerSymbol j ∧ rule.action = .inr i)
        (g.rawRules.map liftCriticalRule ++
          (List.range count).map g.criticalMarkerRule)) = none
  rw [List.find?_append, List.find?_map, List.find?_map]
  have horiginal : List.find?
      ((fun rule : RawRule (Action ⊕ ℕ) => decide
          (rule.lhs = g.criticalMarkerSymbol j ∧ rule.action = .inr i)) ∘
        liftCriticalRule) g.rawRules = none := by
    apply List.find?_eq_none.mpr
    intro rule hrule
    simp [liftCriticalRule, RawRule.lhs, RawRule.action]
  have hmarkers : List.find?
      ((fun rule : RawRule (Action ⊕ ℕ) => decide
          (rule.lhs = g.criticalMarkerSymbol j ∧ rule.action = .inr i)) ∘
        g.criticalMarkerRule) (List.range count) = none := by
    apply List.find?_eq_none.mpr
    intro k hk
    simp [criticalMarkerRule, criticalMarkerSymbol,
      RawRule.lhs, RawRule.action]
    intro hki
    subst k
    exact fun hij => hne hij.symm
  rw [horiginal, hmarkers]
  rfl

private theorem step?_wrongMarker
    (g : EncodedFirstOrderGrammar Action) {count i j : ℕ}
    (hj : j < count) (hne : i ≠ j) :
    (g.withCriticalMarkers count).step? (.inl (.inr i))
      (g.criticalMarker j) = none := by
  change (g.withCriticalMarkers count).rootRewrite? (.inr i)
      (g.criticalMarker j) = none
  unfold rootRewrite?
  rw [criticalMarker_rootApplication?]
  simp [ruleLookup_wrongMarker g hj hne]

private theorem criticalParameter_step_self
    (g : EncodedFirstOrderGrammar Action) (count arity : ℕ)
    (hcount : arity ≤ count) (x : ℕ) :
    (g.withCriticalMarkers count).step?
        (criticalParameterLabel (Action := Action) arity x)
        (criticalParameterTerm g arity x) =
      some (criticalParameterTerm g arity x) := by
  unfold criticalParameterLabel criticalParameterTerm
  split <;> rename_i hx
  · simpa [hx] using g.withCriticalMarkers_step_marker
      (lt_of_lt_of_le hx hcount)
  · simp [hx, step?, RegularTerm.variableTerm_rootNode?]

private theorem criticalParameter_step_ne
    (g : EncodedFirstOrderGrammar Action) (count arity : ℕ)
    (hcount : arity ≤ count) {x y : ℕ}
    (hne : x ≠ y) :
    (g.withCriticalMarkers count).step?
        (criticalParameterLabel (Action := Action) arity x)
        (criticalParameterTerm g arity y) = none := by
  unfold criticalParameterLabel criticalParameterTerm
  by_cases hx : x < arity <;> by_cases hy : y < arity
  · simp only [if_pos hx, if_pos hy]
    exact step?_wrongMarker g (lt_of_lt_of_le hy hcount) hne
  · simp only [if_pos hx, if_neg hy]
    change (g.withCriticalMarkers count).rootRewrite? (.inr x)
      (RegularTerm.variableTerm y) = none
    unfold rootRewrite?
    rw [RegularTerm.variableTerm_rootApplication?]
  · simp only [if_neg hx, if_pos hy]
    unfold step?
    have hroot : (g.criticalMarker y).rootNode? =
        some (.inr (g.criticalMarkerSymbol y, [])) := by
      simp [RegularTerm.rootNode?, RegularTerm.nodeAt?, criticalMarker,
        RegularTerm.nodes, RegularTerm.root]
    rw [hroot]
  · simp [hx, hy, step?, RegularTerm.variableTerm_rootNode?, hne]

private def residualContexts (schema : RegularTerm)
    (children : List ℕ) : List RegularTerm :=
  children.map schema.withRoot

private def pluggedResiduals (schema : RegularTerm)
    (arguments : List RegularTerm) (children : List ℕ) :
    List RegularTerm :=
  children.map fun child => (schema.withRoot child).instantiate arguments

private def residualSchema (rhs schema : RegularTerm)
    (children : List ℕ) : RegularTerm :=
  rhs.instantiate (residualContexts schema children)

private theorem step?_original_residual
    (g : EncodedFirstOrderGrammar Action) (action : Action)
    {schema : RegularTerm} {X : ℕ} {children : List ℕ}
    (hroot : schema.rootApplication? = some (X, children)) :
    g.step? (.inl action) schema =
      (g.ruleLookup X action).map fun rhs =>
        residualSchema rhs schema children := by
  change g.rootRewrite? action schema = _
  unfold rootRewrite?
  rw [hroot]
  rfl

private theorem resolvedChildren_eq_pluggedResiduals
    (schema : RegularTerm) (arguments : List RegularTerm)
    (children : List ℕ) :
    (children.map (schema.resolveRHSRef arguments)).map
        (schema.instantiate arguments).withRoot =
      pluggedResiduals schema arguments children := by
  simp [pluggedResiduals, List.map_map]

private theorem step?_instantiate_original
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {X : ℕ} {children : List ℕ} (action : Action)
    (hschema : schema.ReferenceClosed)
    (hroot : schema.rootApplication? = some (X, children)) :
    (g.withCriticalMarkers count).step? (.inl (.inl action))
        (schema.instantiate arguments) =
      (g.ruleLookup X action).map fun rhs =>
        rhs.instantiate (pluggedResiduals schema arguments children) := by
  change (g.withCriticalMarkers count).rootRewrite? (.inl action)
      (schema.instantiate arguments) = _
  unfold rootRewrite?
  rw [RegularTerm.instantiate_rootApplication? hschema hroot]
  simp only
  rw [withCriticalMarkers_ruleLookup_original,
    resolvedChildren_eq_pluggedResiduals]

private theorem step?_instantiate_application_exposure
    (g : EncodedFirstOrderGrammar Action) (count arity x : ℕ)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {X : ℕ} {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hsymbols : RegularTerm.UsesOriginalSymbols g.ranks schema)
    (hroot : schema.rootApplication? = some (X, children)) :
    (g.withCriticalMarkers count).step?
        (criticalParameterLabel (Action := Action) arity x)
        (schema.instantiate arguments) = none := by
  have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
  obtain ⟨rank, hXrank, _⟩ :=
    hsymbols X children (List.mem_of_getElem? hrootNode)
  have hX : X < g.ranks.length :=
    (List.getElem?_eq_some_iff.mp hXrank).1
  have hinstRoot := RegularTerm.instantiate_rootApplication?
    (arguments := arguments) hschema hroot
  unfold criticalParameterLabel
  split <;> rename_i hx
  · change (g.withCriticalMarkers count).rootRewrite? (.inr x)
      (schema.instantiate arguments) = none
    unfold rootRewrite?
    rw [hinstRoot]
    simp only
    rw [ruleLookup_markerAction_of_originalSymbol g count X x hX]
    rfl
  · unfold step?
    have hnode := RegularTerm.nodeAt?_root_of_rootApplication? hinstRoot
    have hrootNode : (schema.instantiate arguments).rootNode? =
        some (.inr
          (X, children.map (schema.resolveRHSRef arguments))) := by
      simpa [RegularTerm.rootNode?] using hnode
    rw [hrootNode]

private theorem step?_instantiate_application_marker
    (g : EncodedFirstOrderGrammar Action) (count i : ℕ)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {X : ℕ} {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hsymbols : RegularTerm.UsesOriginalSymbols g.ranks schema)
    (hroot : schema.rootApplication? = some (X, children)) :
    (g.withCriticalMarkers count).step? (.inl (.inr i))
        (schema.instantiate arguments) = none := by
  have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
  obtain ⟨rank, hXrank, _⟩ :=
    hsymbols X children (List.mem_of_getElem? hrootNode)
  have hX : X < g.ranks.length :=
    (List.getElem?_eq_some_iff.mp hXrank).1
  have hinstRoot := RegularTerm.instantiate_rootApplication?
    (arguments := arguments) hschema hroot
  change (g.withCriticalMarkers count).rootRewrite? (.inr i)
    (schema.instantiate arguments) = none
  unfold rootRewrite?
  rw [hinstRoot]
  simp only
  rw [ruleLookup_markerAction_of_originalSymbol g count X i hX]
  rfl

private theorem step?_instantiate_application_private
    (g : EncodedFirstOrderGrammar Action) (count i : ℕ)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {X : ℕ} {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hroot : schema.rootApplication? = some (X, children)) :
    (g.withCriticalMarkers count).step? (.inr i)
        (schema.instantiate arguments) = none := by
  have hinstRoot := RegularTerm.instantiate_rootApplication?
    (arguments := arguments) hschema hroot
  have hnode := RegularTerm.nodeAt?_root_of_rootApplication? hinstRoot
  have hrootNode : (schema.instantiate arguments).rootNode? =
      some (.inr
        (X, children.map (schema.resolveRHSRef arguments))) := by
    simpa [RegularTerm.rootNode?] using hnode
  unfold step?
  rw [hrootNode]

private theorem residualContexts_referenceClosed
    {schema : RegularTerm} {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length) :
    ∀ context ∈ residualContexts schema children,
      context.ReferenceClosed := by
  intro context hcontext
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hcontext
  exact RegularTerm.withRoot_referenceClosed hschema
    (hchildren child hchild)

private theorem residualContexts_originalSymbols
    {ranks : List ℕ} {schema : RegularTerm} {children : List ℕ}
    (hschema : RegularTerm.UsesOriginalSymbols ranks schema) :
    ∀ context ∈ residualContexts schema children,
      RegularTerm.UsesOriginalSymbols ranks context := by
  intro context hcontext
  obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hcontext
  exact RegularTerm.usesOriginalSymbols_withRoot hschema child

private theorem pluggedResiduals_referenceClosed
    {schema : RegularTerm} {arguments : List RegularTerm}
    {children : List ℕ}
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    ∀ term ∈ pluggedResiduals schema arguments children,
      term.ReferenceClosed := by
  intro term hterm
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hterm
  exact RegularTerm.instantiate_referenceClosed
    (RegularTerm.withRoot_referenceClosed hschema
      (hchildren child hchild)) harguments

private theorem residualSchema_referenceClosed
    {rhs schema : RegularTerm} {children : List ℕ}
    (hrhs : rhs.ReferenceClosed)
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length) :
    (residualSchema rhs schema children).ReferenceClosed := by
  exact RegularTerm.instantiate_referenceClosed hrhs
    (residualContexts_referenceClosed hschema hchildren)

private theorem residualSchema_originalSymbols
    {ranks : List ℕ} {rhs schema : RegularTerm} {children : List ℕ}
    (hrhs : RegularTerm.UsesOriginalSymbols ranks rhs)
    (hschema : RegularTerm.UsesOriginalSymbols ranks schema) :
    RegularTerm.UsesOriginalSymbols ranks
      (residualSchema rhs schema children) := by
  exact RegularTerm.usesOriginalSymbols_instantiate hrhs
    (residualContexts_originalSymbols hschema)

private theorem parameter_instantiation_approx
    {g' : EncodedFirstOrderGrammar (Action ⊕ ℕ)}
    (laws : g'.GuardedContextLaws) (depth : ℕ)
    {schema : RegularTerm} {arguments : List RegularTerm} {x : ℕ}
    (hschema : schema.ReferenceClosed)
    (hroot : schema.nodeAt? schema.root = some (.inl x))
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    g'.TraceApprox depth (schema.instantiate arguments)
      ((arguments[x]?).getD (RegularTerm.variableTerm x)) := by
  apply laws.unfoldingApprox
  · exact RegularTerm.instantiate_referenceClosed hschema harguments
  · cases hargument : arguments[x]? with
    | none => exact RegularTerm.variableTerm_referenceClosed x
    | some argument =>
        exact harguments argument (List.mem_of_getElem? hargument)
  · exact RegularTerm.instantiate_unfoldingEquivalent_parameter
      hschema hroot harguments

private theorem residual_composition_approx
    {g' : EncodedFirstOrderGrammar (Action ⊕ ℕ)}
    (laws : g'.GuardedContextLaws) (depth : ℕ)
    {ranks : List ℕ} {rhs schema : RegularTerm}
    {children : List ℕ} {arguments : List RegularTerm}
    (hrhs : rhs.WellFormed ranks children.length)
    (hschema : schema.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < schema.nodes.length)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    g'.TraceApprox depth
      ((residualSchema rhs schema children).instantiate arguments)
      (rhs.instantiate (pluggedResiduals schema arguments children)) := by
  have hcontexts := residualContexts_referenceClosed hschema hchildren
  have hcomposition := RegularTerm.instantiate_comp_unfoldingEquivalent
    (outer := rhs) (contexts := residualContexts schema children)
    (arguments := arguments) (ranks := ranks) (by
      simpa [residualContexts] using hrhs) hcontexts harguments
  have hcomposed : RegularTerm.composedContexts
      (residualContexts schema children) arguments =
      pluggedResiduals schema arguments children := by
    simp [RegularTerm.composedContexts, residualContexts,
      pluggedResiduals, List.map_map]
  rw [hcomposed] at hcomposition
  apply laws.unfoldingApprox
  · exact RegularTerm.instantiate_referenceClosed
      (residualSchema_referenceClosed
        (RegularTerm.referenceClosed_of_wellFormed hrhs)
        hschema hchildren) harguments
  · exact RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed hrhs)
      (pluggedResiduals_referenceClosed hschema hchildren harguments)
  · simpa [residualSchema] using hcomposition

/-- Core critical-instance theorem for residual open terms.  The final
substitution need only consist of reference-closed graphs; groundness is used
by the public family constructor below to supply that hypothesis. -/
private theorem critical_worst_aux
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count arity : ℕ) (hcount : arity ≤ count)
    (laws : (g.withCriticalMarkers count).GuardedContextLaws)
    (other : List RegularTerm)
    (hother : ∀ argument ∈ other, argument.ReferenceClosed) :
    ∀ (depth : ℕ) (left right : RegularTerm),
      left.ReferenceClosed →
      right.ReferenceClosed →
      RegularTerm.UsesOriginalSymbols g.ranks left →
      RegularTerm.UsesOriginalSymbols g.ranks right →
      (g.withCriticalMarkers count).TraceApprox depth
          (left.instantiate (g.criticalArguments arity))
          (right.instantiate (g.criticalArguments arity)) →
        (g.withCriticalMarkers count).TraceApprox depth
          (left.instantiate other) (right.instantiate other) := by
  intro depth
  induction depth with
  | zero =>
      intro left right hleft hright hleftSymbols hrightSymbols hcritical
      trivial
  | succ n ih =>
      intro left right hleft hright hleftSymbols hrightSymbols hcritical
      let leftRootNode : RawNode := left.nodes[left.root]'hleft.1
      let rightRootNode : RawNode := right.nodes[right.root]'hright.1
      have hleftRoot : left.nodeAt? left.root = some leftRootNode := by
        unfold RegularTerm.nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hleft.1, rfl⟩
      have hrightRoot : right.nodeAt? right.root = some rightRootNode := by
        unfold RegularTerm.nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hright.1, rfl⟩
      cases hleftKind : leftRootNode with
      | inl x =>
          have hleftVariable : left.nodeAt? left.root = some (.inl x) := by
            simpa [hleftKind] using hleftRoot
          have hleftCritical := parameter_instantiation_approx laws (n + 1)
            hleft hleftVariable (criticalArguments_referenceClosed g arity)
          rw [criticalArguments_parameter] at hleftCritical
          cases hrightKind : rightRootNode with
          | inl y =>
              have hrightVariable : right.nodeAt? right.root =
                  some (.inl y) := by
                simpa [hrightKind] using hrightRoot
              have hrightCritical := parameter_instantiation_approx laws
                (n + 1) hright hrightVariable
                  (criticalArguments_referenceClosed g arity)
              rw [criticalArguments_parameter] at hrightCritical
              by_cases hxy : x = y
              · subst y
                have hleftOther := parameter_instantiation_approx laws
                  (n + 1) hleft hleftVariable hother
                have hrightOther := parameter_instantiation_approx laws
                  (n + 1) hright hrightVariable hother
                exact hleftOther.trans hrightOther.symm
              · have hparameters :
                    (g.withCriticalMarkers count).TraceApprox (n + 1)
                      (criticalParameterTerm g arity x)
                      (criticalParameterTerm g arity y) :=
                  hleftCritical.symm.trans
                    (hcritical.trans hrightCritical)
                have hrel := hparameters
                  (criticalParameterLabel (Action := Action) arity x)
                rw [criticalParameter_step_self g count arity hcount,
                  criticalParameter_step_ne g count arity hcount hxy] at hrel
                cases hrel
          | inr app =>
              rcases app with ⟨Y, children⟩
              have hrightApplicationNode : right.nodeAt? right.root =
                  some (.inr (Y, children)) := by
                simpa [hrightKind] using hrightRoot
              have hrightApplication :=
                RegularTerm.rootApplication?_of_root_node
                  hrightApplicationNode
              have hparameterApplication :
                  (g.withCriticalMarkers count).TraceApprox (n + 1)
                    (criticalParameterTerm g arity x)
                    (right.instantiate (g.criticalArguments arity)) :=
                hleftCritical.symm.trans hcritical
              have hrel := hparameterApplication
                (criticalParameterLabel (Action := Action) arity x)
              rw [criticalParameter_step_self g count arity hcount,
                step?_instantiate_application_exposure g count arity x hright
                  hrightSymbols hrightApplication] at hrel
              cases hrel
      | inr leftApp =>
          rcases leftApp with ⟨X, leftChildren⟩
          have hleftApplicationNode : left.nodeAt? left.root =
              some (.inr (X, leftChildren)) := by
            simpa [hleftKind] using hleftRoot
          have hleftApplication := RegularTerm.rootApplication?_of_root_node
            hleftApplicationNode
          cases hrightKind : rightRootNode with
          | inl y =>
              have hrightVariable : right.nodeAt? right.root =
                  some (.inl y) := by
                simpa [hrightKind] using hrightRoot
              have hrightCritical := parameter_instantiation_approx laws
                (n + 1) hright hrightVariable
                  (criticalArguments_referenceClosed g arity)
              rw [criticalArguments_parameter] at hrightCritical
              have happlicationParameter :
                  (g.withCriticalMarkers count).TraceApprox (n + 1)
                    (left.instantiate (g.criticalArguments arity))
                    (criticalParameterTerm g arity y) :=
                hcritical.trans hrightCritical
              have hrel := happlicationParameter
                (criticalParameterLabel (Action := Action) arity y)
              rw [step?_instantiate_application_exposure g count arity y hleft
                  hleftSymbols hleftApplication,
                criticalParameter_step_self g count arity hcount] at hrel
              cases hrel
          | inr rightApp =>
              rcases rightApp with ⟨Y, rightChildren⟩
              have hrightApplicationNode : right.nodeAt? right.root =
                  some (.inr (Y, rightChildren)) := by
                simpa [hrightKind] using hrightRoot
              have hrightApplication := RegularTerm.rootApplication?_of_root_node
                hrightApplicationNode
              intro label
              cases label with
              | inr i =>
                  rw [step?_instantiate_application_private g count i hleft
                      hleftApplication,
                    step?_instantiate_application_private g count i hright
                      hrightApplication]
                  exact .none
              | inl extendedAction =>
                  cases extendedAction with
                  | inr i =>
                      rw [step?_instantiate_application_marker g count i
                          hleft hleftSymbols hleftApplication,
                        step?_instantiate_application_marker g count i
                          hright hrightSymbols hrightApplication]
                      exact .none
                  | inl action =>
                      have hcriticalStep := hcritical (.inl (.inl action))
                      rw [step?_instantiate_original g count action hleft
                            hleftApplication,
                          step?_instantiate_original g count action hright
                            hrightApplication] at hcriticalStep
                      rw [step?_instantiate_original g count action hleft
                            hleftApplication,
                          step?_instantiate_original g count action hright
                            hrightApplication]
                      cases hleftRule : g.ruleLookup X action with
                      | none =>
                          cases hrightRule : g.ruleLookup Y action with
                          | none => simp [hleftRule, hrightRule]
                          | some rightRhs =>
                              simp [hleftRule, hrightRule] at hcriticalStep
                      | some leftRhs =>
                          cases hrightRule : g.ruleLookup Y action with
                          | none =>
                              simp [hleftRule, hrightRule] at hcriticalStep
                          | some rightRhs =>
                              simp only [hleftRule, hrightRule,
                                Option.map_some] at hcriticalStep ⊢
                              cases hcriticalStep with
                              | some hcriticalTargets =>
                                  obtain ⟨leftRank, hleftRank,
                                      hleftArity⟩ :=
                                    hleftSymbols X leftChildren
                                      (List.mem_of_getElem?
                                        hleftApplicationNode)
                                  obtain ⟨rightRank, hrightRank,
                                      hrightArity⟩ :=
                                    hrightSymbols Y rightChildren
                                      (List.mem_of_getElem?
                                        hrightApplicationNode)
                                  obtain ⟨leftRuleRank, hleftRuleRank,
                                      hleftRhsWF⟩ :=
                                    selected_rhs_wellFormed hg hleftRule
                                  obtain ⟨rightRuleRank, hrightRuleRank,
                                      hrightRhsWF⟩ :=
                                    selected_rhs_wellFormed hg hrightRule
                                  have hleftRanks : leftRuleRank = leftRank :=
                                    Option.some.inj
                                      (hleftRuleRank.symm.trans hleftRank)
                                  have hrightRanks :
                                      rightRuleRank = rightRank :=
                                    Option.some.inj
                                      (hrightRuleRank.symm.trans hrightRank)
                                  have hleftRhsArity : leftRhs.WellFormed
                                      g.ranks leftChildren.length := by
                                    rw [hleftArity, ← hleftRanks]
                                    exact hleftRhsWF
                                  have hrightRhsArity : rightRhs.WellFormed
                                      g.ranks rightChildren.length := by
                                    rw [hrightArity, ← hrightRanks]
                                    exact hrightRhsWF
                                  have hleftChildren :=
                                    RegularTerm.rootApplication_children_lt
                                      hleft hleftApplication
                                  have hrightChildren :=
                                    RegularTerm.rootApplication_children_lt
                                      hright hrightApplication
                                  have hleftResidualClosed :=
                                    residualSchema_referenceClosed
                                      (RegularTerm.referenceClosed_of_wellFormed
                                        hleftRhsArity) hleft hleftChildren
                                  have hrightResidualClosed :=
                                    residualSchema_referenceClosed
                                      (RegularTerm.referenceClosed_of_wellFormed
                                        hrightRhsArity) hright hrightChildren
                                  have hleftResidualSymbols :=
                                    residualSchema_originalSymbols
                                      (children := leftChildren)
                                      (RegularTerm.usesOriginalSymbols_of_wellFormed
                                        hleftRhsArity) hleftSymbols
                                  have hrightResidualSymbols :=
                                    residualSchema_originalSymbols
                                      (children := rightChildren)
                                      (RegularTerm.usesOriginalSymbols_of_wellFormed
                                        hrightRhsArity) hrightSymbols
                                  have hleftCriticalComposition :=
                                    residual_composition_approx laws n
                                      hleftRhsArity hleft hleftChildren
                                      (criticalArguments_referenceClosed
                                        g arity)
                                  have hrightCriticalComposition :=
                                    residual_composition_approx laws n
                                      hrightRhsArity hright hrightChildren
                                      (criticalArguments_referenceClosed
                                        g arity)
                                  have hsymbolicCritical :
                                      (g.withCriticalMarkers count).TraceApprox n
                                        ((residualSchema leftRhs left
                                            leftChildren).instantiate
                                          (g.criticalArguments arity))
                                        ((residualSchema rightRhs right
                                            rightChildren).instantiate
                                          (g.criticalArguments arity)) :=
                                    hleftCriticalComposition.trans
                                      (hcriticalTargets.trans
                                        hrightCriticalComposition.symm)
                                  have hsymbolicOther := ih
                                    (residualSchema leftRhs left leftChildren)
                                    (residualSchema rightRhs right rightChildren)
                                    hleftResidualClosed hrightResidualClosed
                                    hleftResidualSymbols hrightResidualSymbols
                                    hsymbolicCritical
                                  have hleftOtherComposition :=
                                    residual_composition_approx laws n
                                      hleftRhsArity hleft hleftChildren hother
                                  have hrightOtherComposition :=
                                    residual_composition_approx laws n
                                      hrightRhsArity hright hrightChildren hother
                                  exact .some
                                    (hleftOtherComposition.symm.trans
                                      (hsymbolicOther.trans
                                        hrightOtherComposition))

/- The marker substitution also reflects the open transition tree.  This is
the converse direction needed for completeness: private variable labels in
the corrected open semantics become the corresponding public marker labels,
while original actions are merely lifted into the extended alphabet. -/
private theorem critical_of_open_aux
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count arity : ℕ)
    (laws : (g.withCriticalMarkers count).GuardedContextLaws) :
    ∀ (depth : ℕ) (left right : RegularTerm),
      left.ReferenceClosed →
      right.ReferenceClosed →
      RegularTerm.UsesOriginalSymbols g.ranks left →
      RegularTerm.UsesOriginalSymbols g.ranks right →
      g.TraceApprox depth left right →
        (g.withCriticalMarkers count).TraceApprox depth
          (left.instantiate (g.criticalArguments arity))
          (right.instantiate (g.criticalArguments arity)) := by
  intro depth
  induction depth with
  | zero =>
      intro left right hleft hright hleftSymbols hrightSymbols hopen
      trivial
  | succ n ih =>
      intro left right hleft hright hleftSymbols hrightSymbols hopen
      let leftRootNode : RawNode := left.nodes[left.root]'hleft.1
      let rightRootNode : RawNode := right.nodes[right.root]'hright.1
      have hleftRoot : left.nodeAt? left.root = some leftRootNode := by
        unfold RegularTerm.nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hleft.1, rfl⟩
      have hrightRoot : right.nodeAt? right.root = some rightRootNode := by
        unfold RegularTerm.nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hright.1, rfl⟩
      cases hleftKind : leftRootNode with
      | inl x =>
          have hleftVariable : left.nodeAt? left.root = some (.inl x) := by
            simpa [hleftKind] using hleftRoot
          have hleftRootNode : left.rootNode? = some (.inl x) := by
            simpa [RegularTerm.rootNode?] using hleftVariable
          cases hrightKind : rightRootNode with
          | inl y =>
              have hrightVariable : right.nodeAt? right.root =
                  some (.inl y) := by
                simpa [hrightKind] using hrightRoot
              have hrightRootNode : right.rootNode? = some (.inl y) := by
                simpa [RegularTerm.rootNode?] using hrightVariable
              have hxy : x = y := by
                by_contra hne
                have hrel := hopen (.inr x)
                unfold step? at hrel
                rw [hleftRootNode, hrightRootNode] at hrel
                simp [hne] at hrel
              subst y
              have hleftCritical := parameter_instantiation_approx laws
                (n + 1) hleft hleftVariable
                  (criticalArguments_referenceClosed g arity)
              have hrightCritical := parameter_instantiation_approx laws
                (n + 1) hright hrightVariable
                  (criticalArguments_referenceClosed g arity)
              rw [criticalArguments_parameter] at hleftCritical
              rw [criticalArguments_parameter] at hrightCritical
              exact hleftCritical.trans hrightCritical.symm
          | inr app =>
              rcases app with ⟨Y, children⟩
              have hrightApplicationNode : right.nodeAt? right.root =
                  some (.inr (Y, children)) := by
                simpa [hrightKind] using hrightRoot
              have hrightRootNode : right.rootNode? =
                  some (.inr (Y, children)) := by
                simpa [RegularTerm.rootNode?] using hrightApplicationNode
              have hrel := hopen (.inr x)
              unfold step? at hrel
              rw [hleftRootNode, hrightRootNode] at hrel
              simp at hrel
      | inr leftApp =>
          rcases leftApp with ⟨X, leftChildren⟩
          have hleftApplicationNode : left.nodeAt? left.root =
              some (.inr (X, leftChildren)) := by
            simpa [hleftKind] using hleftRoot
          have hleftApplication := RegularTerm.rootApplication?_of_root_node
            hleftApplicationNode
          have hleftRootNode : left.rootNode? =
              some (.inr (X, leftChildren)) := by
            simpa [RegularTerm.rootNode?] using hleftApplicationNode
          cases hrightKind : rightRootNode with
          | inl y =>
              have hrightVariable : right.nodeAt? right.root =
                  some (.inl y) := by
                simpa [hrightKind] using hrightRoot
              have hrightRootNode : right.rootNode? = some (.inl y) := by
                simpa [RegularTerm.rootNode?] using hrightVariable
              have hrel := hopen (.inr y)
              unfold step? at hrel
              rw [hleftRootNode, hrightRootNode] at hrel
              simp at hrel
          | inr rightApp =>
              rcases rightApp with ⟨Y, rightChildren⟩
              have hrightApplicationNode : right.nodeAt? right.root =
                  some (.inr (Y, rightChildren)) := by
                simpa [hrightKind] using hrightRoot
              have hrightApplication :=
                RegularTerm.rootApplication?_of_root_node
                  hrightApplicationNode
              intro label
              cases label with
              | inr i =>
                  rw [step?_instantiate_application_private g count i hleft
                      hleftApplication,
                    step?_instantiate_application_private g count i hright
                      hrightApplication]
                  exact .none
              | inl extendedAction =>
                  cases extendedAction with
                  | inr i =>
                      rw [step?_instantiate_application_marker g count i
                          hleft hleftSymbols hleftApplication,
                        step?_instantiate_application_marker g count i
                          hright hrightSymbols hrightApplication]
                      exact .none
                  | inl action =>
                      have hopenStep := hopen (.inl action)
                      rw [step?_original_residual g action hleftApplication,
                        step?_original_residual g action hrightApplication]
                        at hopenStep
                      rw [step?_instantiate_original g count action hleft
                            hleftApplication,
                          step?_instantiate_original g count action hright
                            hrightApplication]
                      cases hleftRule : g.ruleLookup X action with
                      | none =>
                          cases hrightRule : g.ruleLookup Y action with
                          | none => simp [hleftRule, hrightRule]
                          | some rightRhs =>
                              simp [hleftRule, hrightRule] at hopenStep
                      | some leftRhs =>
                          cases hrightRule : g.ruleLookup Y action with
                          | none =>
                              simp [hleftRule, hrightRule] at hopenStep
                          | some rightRhs =>
                              simp only [hleftRule, hrightRule,
                                Option.map_some] at hopenStep ⊢
                              cases hopenStep with
                              | some hopenTargets =>
                                  obtain ⟨leftRank, hleftRank,
                                      hleftArity⟩ :=
                                    hleftSymbols X leftChildren
                                      (List.mem_of_getElem?
                                        hleftApplicationNode)
                                  obtain ⟨rightRank, hrightRank,
                                      hrightArity⟩ :=
                                    hrightSymbols Y rightChildren
                                      (List.mem_of_getElem?
                                        hrightApplicationNode)
                                  obtain ⟨leftRuleRank, hleftRuleRank,
                                      hleftRhsWF⟩ :=
                                    selected_rhs_wellFormed hg hleftRule
                                  obtain ⟨rightRuleRank, hrightRuleRank,
                                      hrightRhsWF⟩ :=
                                    selected_rhs_wellFormed hg hrightRule
                                  have hleftRanks : leftRuleRank = leftRank :=
                                    Option.some.inj
                                      (hleftRuleRank.symm.trans hleftRank)
                                  have hrightRanks :
                                      rightRuleRank = rightRank :=
                                    Option.some.inj
                                      (hrightRuleRank.symm.trans hrightRank)
                                  have hleftRhsArity : leftRhs.WellFormed
                                      g.ranks leftChildren.length := by
                                    rw [hleftArity, ← hleftRanks]
                                    exact hleftRhsWF
                                  have hrightRhsArity : rightRhs.WellFormed
                                      g.ranks rightChildren.length := by
                                    rw [hrightArity, ← hrightRanks]
                                    exact hrightRhsWF
                                  have hleftChildren :=
                                    RegularTerm.rootApplication_children_lt
                                      hleft hleftApplication
                                  have hrightChildren :=
                                    RegularTerm.rootApplication_children_lt
                                      hright hrightApplication
                                  have hleftResidualClosed :=
                                    residualSchema_referenceClosed
                                      (RegularTerm.referenceClosed_of_wellFormed
                                        hleftRhsArity) hleft hleftChildren
                                  have hrightResidualClosed :=
                                    residualSchema_referenceClosed
                                      (RegularTerm.referenceClosed_of_wellFormed
                                        hrightRhsArity) hright hrightChildren
                                  have hleftResidualSymbols :=
                                    residualSchema_originalSymbols
                                      (children := leftChildren)
                                      (RegularTerm.usesOriginalSymbols_of_wellFormed
                                        hleftRhsArity) hleftSymbols
                                  have hrightResidualSymbols :=
                                    residualSchema_originalSymbols
                                      (children := rightChildren)
                                      (RegularTerm.usesOriginalSymbols_of_wellFormed
                                        hrightRhsArity) hrightSymbols
                                  have hopenCritical := ih
                                    (residualSchema leftRhs left leftChildren)
                                    (residualSchema rightRhs right rightChildren)
                                    hleftResidualClosed hrightResidualClosed
                                    hleftResidualSymbols hrightResidualSymbols
                                    hopenTargets
                                  have hleftComposition :=
                                    residual_composition_approx laws n
                                      hleftRhsArity hleft hleftChildren
                                      (criticalArguments_referenceClosed
                                        g arity)
                                  have hrightComposition :=
                                    residual_composition_approx laws n
                                      hrightRhsArity hright hrightChildren
                                      (criticalArguments_referenceClosed
                                        g arity)
                                  exact .some
                                    (hleftComposition.symm.trans
                                      (hopenCritical.trans
                                        hrightComposition))

/-- Open finite-depth equivalence is preserved by the canonical marker
substitution.  The arity bound ensures that every substituted marker belongs
to the chosen finite extension. -/
public theorem critical_traceApprox_of_open
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity depth : ℕ} (_hcount : arity ≤ count)
    {left right : RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hopen : g.TraceApprox depth left right) :
    (g.withCriticalMarkers count).TraceApprox depth
      (left.instantiate (g.criticalArguments arity))
      (right.instantiate (g.criticalArguments arity)) := by
  apply critical_of_open_aux g hg count arity
    (guardedContextLaws_of_wellFormed
      (g.withCriticalMarkers_wellFormed hg count))
  · exact RegularTerm.referenceClosed_of_wellFormed hleft
  · exact RegularTerm.referenceClosed_of_wellFormed hright
  · exact RegularTerm.usesOriginalSymbols_of_wellFormed hleft
  · exact RegularTerm.usesOriginalSymbols_of_wellFormed hright
  · exact hopen

/-- Open trace equivalence is preserved by the canonical marker
substitution in every sufficiently large marker extension. -/
public theorem critical_traceEquivalent_of_open
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity : ℕ} (hcount : arity ≤ count)
    {left right : RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hopen : g.TraceEquivalent left right) :
    (g.withCriticalMarkers count).TraceEquivalent
      (left.instantiate (g.criticalArguments arity))
      (right.instantiate (g.criticalArguments arity)) := by
  apply ((g.withCriticalMarkers count).traceEquivalent_iff_forall_traceApprox
    _ _).mpr
  intro depth
  exact critical_traceApprox_of_open hg hcount hleft hright
    ((g.traceEquivalent_iff_forall_traceApprox left right).mp hopen depth)

/-- An equivalent open pair gives an equivalent canonical ground instance in
the critical extension. -/
public theorem openTraceEquivalent_criticalInstantiation_in_criticalExtension
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity : ℕ} (hcount : arity ≤ count)
    {left right : RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hopen : g.TraceEquivalent left right) :
    (g.withCriticalMarkers count).TraceEquivalent
      (left.instantiate (g.criticalArguments arity))
      (right.instantiate (g.criticalArguments arity)) :=
  critical_traceEquivalent_of_open hg hcount hleft hright hopen

/-- The fresh-marker substitution is a worst ground instance at every finite
trace depth.  The theorem is uniform in the arity and in the chosen ground
arguments. -/
public theorem critical_traceApprox_worst
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity depth : ℕ} (hcount : arity ≤ count)
    {left right : RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    {other : List RegularTerm} (_hcount : other.length = arity)
    (hother : ∀ argument ∈ other,
      argument.Ground (g.withCriticalMarkers count).ranks)
    (hcritical : (g.withCriticalMarkers count).TraceApprox depth
      (left.instantiate (g.criticalArguments arity))
      (right.instantiate (g.criticalArguments arity))) :
    (g.withCriticalMarkers count).TraceApprox depth
      (left.instantiate other) (right.instantiate other) := by
  apply critical_worst_aux g hg count arity hcount
    (guardedContextLaws_of_wellFormed
      (g.withCriticalMarkers_wellFormed hg count)) other
  · intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hother argument hargument)
  · exact RegularTerm.referenceClosed_of_wellFormed hleft
  · exact RegularTerm.referenceClosed_of_wellFormed hright
  · exact RegularTerm.usesOriginalSymbols_of_wellFormed hleft
  · exact RegularTerm.usesOriginalSymbols_of_wellFormed hright
  · exact hcritical

/-- Combined bridge used by sufficient-basis completeness.  Open equivalence
first survives the canonical critical substitution; worst-instantiation then
transfers it to every arity-correct ground substitution in the same marker
extension. -/
public theorem openTraceEquivalent_instantiation_in_criticalExtension
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count arity : ℕ} (hcount : arity ≤ count)
    {left right : RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hopen : g.TraceEquivalent left right)
    {arguments : List RegularTerm} (hargumentsLength : arguments.length = arity)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground (g.withCriticalMarkers count).ranks) :
    (g.withCriticalMarkers count).TraceEquivalent
      (left.instantiate arguments) (right.instantiate arguments) := by
  have hcritical := critical_traceEquivalent_of_open
    hg hcount hleft hright hopen
  apply ((g.withCriticalMarkers count).traceEquivalent_iff_forall_traceApprox
    _ _).mpr
  intro depth
  apply critical_traceApprox_worst hg hcount hleft hright
    hargumentsLength harguments
  exact ((g.withCriticalMarkers count).traceEquivalent_iff_forall_traceApprox
    _ _).mp hcritical depth

public theorem wellFormed_extendedRanks
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed g.ranks variableBound) :
    term.WellFormed (g.withCriticalMarkers count).ranks variableBound := by
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨hterm.1, ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  have hwell := (List.all_eq_true.mp hterm.2) node hnode
  cases node with
  | inl x => simpa [RegularTerm.nodeWellFormedCode] using hwell
  | inr app =>
      rcases app with ⟨X, children⟩
      unfold RegularTerm.nodeWellFormedCode at hwell ⊢
      cases hrank : g.ranks[X]? with
      | none => simp [hrank] at hwell
      | some rank =>
          have hX : X < g.ranks.length :=
            (List.getElem?_eq_some_iff.mp hrank).1
          change (match g.ranks[X]? with
            | none => false
            | some rank => decide (children.length = rank) &&
                children.all fun child =>
                  decide (child < term.nodes.length)) = true at hwell
          change (match (g.ranks ++ List.replicate count 0)[X]? with
            | none => false
            | some rank => decide (children.length = rank) &&
                children.all fun child =>
                  decide (child < term.nodes.length)) = true
          rw [List.getElem?_append_left hX]
          exact hwell

private theorem groundArguments_of_code
    {g' : EncodedFirstOrderGrammar (Action ⊕ ℕ)}
    {arguments : List RegularTerm}
    (harguments : g'.groundArgumentsCode arguments = true) :
    ∀ argument ∈ arguments, argument.Ground g'.ranks := by
  unfold groundArgumentsCode at harguments
  have hall := List.all_eq_true.mp harguments
  intro argument hargument
  exact (RegularTerm.groundCode_eq_true_iff g'.ranks argument).mp
    (hall argument hargument)

/-- The canonical critical family for a finite original-rank basis.  Each
schema receives exactly its arity-many fresh markers; a single extension count
may serve all rows as long as it bounds every basis arity. -/
public def criticalInstanceFamily_of_originalBasis
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (basis : List BasisPair) (count : ℕ)
    (hbasis : ∀ schema ∈ basis,
      schema.left.WellFormed g.ranks schema.arity ∧
        schema.right.WellFormed g.ranks schema.arity)
    (hcount : ∀ schema ∈ basis, schema.arity ≤ count) :
    CriticalInstanceFamily (g.withCriticalMarkers count) basis where
  arguments := fun schema => g.criticalArguments schema.arity
  schema_wellformed := by
    intro schema hschema
    unfold basisPairWellFormedCode
    rw [Bool.and_eq_true]
    exact ⟨wellFormed_extendedRanks g count (hbasis schema hschema).1,
      wellFormed_extendedRanks g count (hbasis schema hschema).2⟩
  argument_count := by
    intro schema hschema
    exact criticalArguments_length g schema.arity
  arguments_ground := by
    intro schema hschema
    unfold groundArgumentsCode
    apply List.all_eq_true.mpr
    intro argument hargument
    apply (RegularTerm.groundCode_eq_true_iff
      (g.withCriticalMarkers count).ranks argument).mpr
    exact criticalArguments_ground_of_le g (hcount schema hschema)
      argument hargument
  critical_ground := by
    intro schema hschema
    have hleft := wellFormed_extendedRanks g count
      (hbasis schema hschema).1
    have hright := wellFormed_extendedRanks g count
      (hbasis schema hschema).2
    have harguments := criticalArguments_ground_of_le g
      (hcount schema hschema)
    have hleftArity : schema.left.WellFormed
        (g.withCriticalMarkers count).ranks
        (g.criticalArguments schema.arity).length := by
      simpa using hleft
    have hrightArity : schema.right.WellFormed
        (g.withCriticalMarkers count).ranks
        (g.criticalArguments schema.arity).length := by
      simpa using hright
    have hleftGround := RegularTerm.instantiate_ground
      hleftArity harguments
    have hrightGround := RegularTerm.instantiate_ground
      hrightArity harguments
    unfold groundPairCode
    rw [Bool.and_eq_true]
    exact ⟨(RegularTerm.groundCode_eq_true_iff
        (g.withCriticalMarkers count).ranks _).mpr hleftGround,
      (RegularTerm.groundCode_eq_true_iff
        (g.withCriticalMarkers count).ranks _).mpr hrightGround⟩
  worst := by
    intro schema hschema other hotherCount hotherCode depth hcritical
    apply critical_traceApprox_worst hg (hcount schema hschema)
      (hbasis schema hschema).1 (hbasis schema hschema).2 hotherCount
      (groundArguments_of_code hotherCode)
    exact hcritical

end EncodedFirstOrderGrammar

end DCFEquivalence
