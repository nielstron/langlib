module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalBasisSoundness
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GroundStepPreservation

@[expose]
public section

/-!
# Fresh ground markers for critical basis instances

For a finite candidate basis we conservatively extend the grammar by finitely
many fresh nullary symbols.  Marker `i` has the single private ordinary action
`inr i`, looping to itself.  Original actions are injected through `inl`.
These are the finite, executable version of the `L_i` terms in the critical
instance argument.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The fresh nullary symbol assigned to marker `i`. -/
@[expose] public def criticalMarkerSymbol
    (g : EncodedFirstOrderGrammar Action) (i : ℕ) : ℕ :=
  g.ranks.length + i

/-- The one-node ground graph for fresh marker `i`. -/
@[expose] public def criticalMarker
    (g : EncodedFirstOrderGrammar Action) (i : ℕ) : RegularTerm :=
  ([.inr (g.criticalMarkerSymbol i, [])], 0)

/-- Lift an original rule into the left summand of the extended action type. -/
@[expose] public def liftCriticalRule (rule : RawRule Action) :
    RawRule (Action ⊕ ℕ) :=
  (rule.lhs, .inl rule.action, rule.rhs)

/-- The self-loop rule for a fresh marker. -/
@[expose] public def criticalMarkerRule
    (g : EncodedFirstOrderGrammar Action) (i : ℕ) :
    RawRule (Action ⊕ ℕ) :=
  (g.criticalMarkerSymbol i, .inr i, g.criticalMarker i)

/-- Conservatively add `count` fresh critical markers to a grammar. -/
@[expose] public def withCriticalMarkers
    (g : EncodedFirstOrderGrammar Action) (count : ℕ) :
    EncodedFirstOrderGrammar (Action ⊕ ℕ) :=
  (g.ranks ++ List.replicate count 0,
    g.rawRules.map liftCriticalRule ++
      (List.range count).map g.criticalMarkerRule)

/-- Embed an original observable label into the marker extension. -/
@[expose] public def liftCriticalLabel : Label Action → Label (Action ⊕ ℕ)
  | .inl action => .inl (.inl action)
  | .inr x => .inr x

@[simp] public theorem withCriticalMarkers_ranks
    (g : EncodedFirstOrderGrammar Action) (count : ℕ) :
    (g.withCriticalMarkers count).ranks =
      g.ranks ++ List.replicate count 0 := rfl

@[simp] public theorem withCriticalMarkers_rawRules
    (g : EncodedFirstOrderGrammar Action) (count : ℕ) :
    (g.withCriticalMarkers count).rawRules =
      g.rawRules.map liftCriticalRule ++
        (List.range count).map g.criticalMarkerRule := rfl

@[simp] public theorem criticalMarker_nodes
    (g : EncodedFirstOrderGrammar Action) (i : ℕ) :
    (g.criticalMarker i).nodes =
      [.inr (g.criticalMarkerSymbol i, [])] := rfl

@[simp] public theorem criticalMarker_root
    (g : EncodedFirstOrderGrammar Action) (i : ℕ) :
    (g.criticalMarker i).root = 0 := rfl

@[simp] public theorem criticalMarker_rootApplication?
    (g : EncodedFirstOrderGrammar Action) (i : ℕ) :
    (g.criticalMarker i).rootApplication? =
      some (g.criticalMarkerSymbol i, []) := by
  simp [criticalMarker, RegularTerm.rootApplication?,
    RegularTerm.rootNode?, RegularTerm.nodeAt?, RegularTerm.nodes,
    RegularTerm.root]

private theorem getElem?_append_left_of_lt
    {A : Type} (left right : List A) {i : ℕ} (hi : i < left.length) :
    (left ++ right)[i]? = left[i]? := by
  rw [List.getElem?_append_left hi]

private theorem getElem?_replicate_add
    {A : Type} (left : List A) (count : ℕ) (value : A)
    {i : ℕ} (hi : i < count) :
    (left ++ List.replicate count value)[left.length + i]? = some value := by
  rw [List.getElem?_append_right (by omega)]
  simp [hi]

/-- Every marker below the chosen count is a well-formed ground term in the
extended rank table. -/
public theorem criticalMarker_ground
    (g : EncodedFirstOrderGrammar Action) {count i : ℕ} (hi : i < count) :
    (g.criticalMarker i).Ground (g.withCriticalMarkers count).ranks := by
  have hrank : (g.withCriticalMarkers count).ranks[
      g.criticalMarkerSymbol i]? = some 0 := by
    exact getElem?_replicate_add g.ranks count 0 hi
  have hrankRaw : (g.ranks ++ List.replicate count 0)[
      g.criticalMarkerSymbol i]? = some 0 := by
    simpa only [withCriticalMarkers_ranks] using hrank
  refine ⟨?_, [0], ?_, ?_⟩
  · unfold RegularTerm.ShapeWellFormed
      RegularTerm.shapeWellFormedCode
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp [criticalMarker, RegularTerm.root, RegularTerm.nodes]
    · apply List.all_eq_true.mpr
      intro node hnode
      have hnodeEq : node =
          (.inr (g.criticalMarkerSymbol i, []) : RawNode) := by
        simpa [criticalMarker, RegularTerm.nodes] using hnode
      subst node
      simp [RegularTerm.nodeShapeWellFormedCode, hrankRaw]
  · simp [criticalMarker, RegularTerm.nodes]
  · constructor
    · simp [criticalMarker, RegularTerm.root]
    · intro j hj
      have hjzero : j = 0 := by simpa using hj
      subst j
      refine ⟨g.criticalMarkerSymbol i, [], ?_, by simp⟩
      simp [criticalMarker, RegularTerm.nodeAt?, RegularTerm.nodes]

/-- Looking up an original action in the extension selects exactly the
original right-hand side. -/
public theorem withCriticalMarkers_ruleLookup_original
    (g : EncodedFirstOrderGrammar Action) (count X : ℕ) (action : Action) :
    (g.withCriticalMarkers count).ruleLookup X (.inl action) =
      g.ruleLookup X action := by
  unfold ruleLookup findRule
  change Option.map RawRule.rhs
      (List.find? (fun rule : RawRule (Action ⊕ ℕ) =>
          rule.lhs = X ∧ rule.action = .inl action)
        (g.rawRules.map liftCriticalRule ++
          (List.range count).map g.criticalMarkerRule)) =
    Option.map RawRule.rhs
      (List.find? (fun rule : RawRule Action =>
        rule.lhs = X ∧ rule.action = action) g.rawRules)
  rw [List.find?_append, List.find?_map, List.find?_map]
  let extendedTest : RawRule (Action ⊕ ℕ) → Bool := fun rule =>
    decide (rule.lhs = X ∧ rule.action = .inl action)
  let originalTest : RawRule Action → Bool := fun rule =>
    decide (rule.lhs = X ∧ rule.action = action)
  change Option.map RawRule.rhs
      ((Option.map liftCriticalRule
        (List.find? (extendedTest ∘ liftCriticalRule) g.rawRules)).or
      (Option.map g.criticalMarkerRule
        (List.find? (extendedTest ∘ g.criticalMarkerRule)
          (List.range count)))) =
    Option.map RawRule.rhs (List.find? originalTest g.rawRules)
  have horiginal : List.find? (extendedTest ∘ liftCriticalRule)
      g.rawRules = List.find? originalTest g.rawRules := by
    congr 1
    funext rule
    simp [extendedTest, originalTest, liftCriticalRule, RawRule.lhs,
      RawRule.action]
  have hmarkers : List.find? (extendedTest ∘ g.criticalMarkerRule)
      (List.range count) = none := by
    apply List.find?_eq_none.mpr
    intro i hi
    simp [extendedTest, criticalMarkerRule, RawRule.lhs,
      RawRule.action]
  rw [horiginal, hmarkers]
  cases List.find? originalTest g.rawRules <;>
    simp [liftCriticalRule, RawRule.rhs]

private theorem find?_range_eq {count i : ℕ} (hi : i < count) :
    List.find? (fun j => decide (j = i)) (List.range count) = some i := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, by simpa, ?_, ?_⟩
  · simp
  · intro j hj
    have hjcount : j < count := lt_trans hj hi
    simp [List.getElem_range, hjcount, Nat.ne_of_lt hj]

/-- Marker `i` has its designated self-loop rule whenever it lies below the
extension count. -/
public theorem withCriticalMarkers_ruleLookup_marker
    (g : EncodedFirstOrderGrammar Action) {count i : ℕ} (hi : i < count) :
    (g.withCriticalMarkers count).ruleLookup
      (g.criticalMarkerSymbol i) (.inr i) = some (g.criticalMarker i) := by
  unfold ruleLookup findRule
  change Option.map RawRule.rhs
      (List.find? (fun rule : RawRule (Action ⊕ ℕ) =>
          rule.lhs = g.criticalMarkerSymbol i ∧ rule.action = .inr i)
        (g.rawRules.map liftCriticalRule ++
          (List.range count).map g.criticalMarkerRule)) =
    some (g.criticalMarker i)
  rw [List.find?_append, List.find?_map, List.find?_map]
  let markerTest : RawRule (Action ⊕ ℕ) → Bool := fun rule =>
    decide (rule.lhs = g.criticalMarkerSymbol i ∧ rule.action = .inr i)
  change Option.map RawRule.rhs
      ((Option.map liftCriticalRule
        (List.find? (markerTest ∘ liftCriticalRule) g.rawRules)).or
      (Option.map g.criticalMarkerRule
        (List.find? (markerTest ∘ g.criticalMarkerRule)
          (List.range count)))) = some (g.criticalMarker i)
  have horiginal : List.find? (markerTest ∘ liftCriticalRule)
      g.rawRules = none := by
    apply List.find?_eq_none.mpr
    intro rule hrule
    simp [markerTest, liftCriticalRule, RawRule.lhs, RawRule.action]
  have hmarkerFunction : (markerTest ∘ g.criticalMarkerRule) =
      (fun j => decide (j = i)) := by
    funext j
    simp [markerTest, criticalMarkerRule, RawRule.lhs, RawRule.action,
      criticalMarkerSymbol]
  rw [horiginal, hmarkerFunction, find?_range_eq hi]
  simp [criticalMarkerRule, RawRule.rhs]

/-- The designated marker action executes one self-loop. -/
public theorem withCriticalMarkers_step_marker
    (g : EncodedFirstOrderGrammar Action) {count i : ℕ} (hi : i < count) :
    (g.withCriticalMarkers count).step? (.inl (.inr i))
      (g.criticalMarker i) = some (g.criticalMarker i) := by
  change (g.withCriticalMarkers count).rootRewrite? (.inr i)
    (g.criticalMarker i) = some (g.criticalMarker i)
  unfold rootRewrite?
  rw [criticalMarker_rootApplication?]
  simp only
  rw [withCriticalMarkers_ruleLookup_marker g hi]
  simp [criticalMarker, RegularTerm.instantiate,
    RegularTerm.nodes, RegularTerm.root, RegularTerm.nodeAt?,
    RegularTerm.instantiateNode,
    RegularTerm.appendArguments, RegularTerm.resolveRHSRef]

private theorem RegularTerm.wellFormed_appendRanks
    {ranks extra : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks variableBound) :
    term.WellFormed (ranks ++ extra) variableBound := by
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
      cases hrank : ranks[X]? with
      | none => simp [hrank] at hwell
      | some rank =>
          have hX : X < ranks.length :=
            (List.getElem?_eq_some_iff.mp hrank).1
          change (match ranks[X]? with
            | none => false
            | some rank => decide (children.length = rank) &&
                children.all fun child =>
                  decide (child < term.nodes.length)) = true at hwell
          change (match (ranks ++ extra)[X]? with
            | none => false
            | some rank => decide (children.length = rank) &&
                children.all fun child =>
                  decide (child < term.nodes.length)) = true
          rw [List.getElem?_append_left hX]
          exact hwell

private theorem criticalMarker_wellFormed
    (g : EncodedFirstOrderGrammar Action) {count i : ℕ} (hi : i < count) :
    (g.criticalMarker i).WellFormed
      (g.withCriticalMarkers count).ranks 0 := by
  have hrank : (g.withCriticalMarkers count).ranks[
      g.criticalMarkerSymbol i]? = some 0 :=
    getElem?_replicate_add g.ranks count 0 hi
  have hrankRaw : (g.ranks ++ List.replicate count 0)[
      g.criticalMarkerSymbol i]? = some 0 := by
    simpa only [withCriticalMarkers_ranks] using hrank
  unfold RegularTerm.WellFormed RegularTerm.wellFormedCode
  rw [Bool.and_eq_true]
  refine ⟨by simp [criticalMarker, RegularTerm.root,
    RegularTerm.nodes], ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  have hnodeEq : node =
      (.inr (g.criticalMarkerSymbol i, []) : RawNode) := by
    simpa [criticalMarker, RegularTerm.nodes] using hnode
  subst node
  unfold RegularTerm.nodeWellFormedCode
  simp only [List.length_nil, List.all_nil, Bool.and_true]
  rw [hrank]
  decide

private theorem criticalMarker_unfoldsFinite
    (g : EncodedFirstOrderGrammar Action) (i : ℕ) :
    (g.criticalMarker i).UnfoldsFinite := by
  simp [RegularTerm.UnfoldsFinite, RegularTerm.unfoldsFiniteCode,
    RegularTerm.unfoldsFiniteFrom, criticalMarker, RegularTerm.nodes,
    RegularTerm.root, RegularTerm.nodeAt?]

private theorem liftedRule_wellFormed
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {rule : RawRule Action}
    (hrule : g.ruleWellFormedCode rule = true) :
    (g.withCriticalMarkers count).ruleWellFormedCode
      (liftCriticalRule rule) = true := by
  unfold ruleWellFormedCode at hrule ⊢
  cases hrank : g.ranks[rule.lhs]? with
  | none => simp [hrank] at hrule
  | some rank =>
      have hX : rule.lhs < g.ranks.length :=
        (List.getElem?_eq_some_iff.mp hrank).1
      have hextendedRank : (g.withCriticalMarkers count).ranks[rule.lhs]? =
          some rank := by
        change (g.ranks ++ List.replicate count 0)[rule.lhs]? = some rank
        rw [List.getElem?_append_left hX]
        exact hrank
      change (match (g.withCriticalMarkers count).ranks[rule.lhs]? with
        | none => false
        | some rank => rule.rhs.wellFormedCode
            (g.withCriticalMarkers count).ranks rank &&
              rule.rhs.unfoldsFiniteCode) = true
      rw [hextendedRank]
      simp only
      rw [hrank] at hrule
      simp only at hrule
      rw [Bool.and_eq_true] at hrule ⊢
      exact ⟨RegularTerm.wellFormed_appendRanks hrule.1, hrule.2⟩

private theorem markerRule_wellFormed
    (g : EncodedFirstOrderGrammar Action) {count i : ℕ} (hi : i < count) :
    (g.withCriticalMarkers count).ruleWellFormedCode
      (g.criticalMarkerRule i) = true := by
  unfold ruleWellFormedCode
  have hrank : (g.withCriticalMarkers count).ranks[
      g.criticalMarkerSymbol i]? = some 0 :=
    getElem?_replicate_add g.ranks count 0 hi
  rw [show (g.criticalMarkerRule i).lhs =
      g.criticalMarkerSymbol i by rfl, hrank, Bool.and_eq_true]
  exact ⟨criticalMarker_wellFormed g hi,
    criticalMarker_unfoldsFinite g i⟩

private theorem actionDeterministicRulesCode_eq_true_iff
    {A : Type} [DecidableEq A] (rules : List (RawRule A)) :
    actionDeterministicRulesCode rules = true ↔
      rules.Pairwise fun left right =>
        left.lhs ≠ right.lhs ∨ left.action ≠ right.action := by
  induction rules with
  | nil => simp [actionDeterministicRulesCode]
  | cons rule rules ih =>
      simp only [actionDeterministicRulesCode, Bool.and_eq_true,
        List.pairwise_cons, ih, List.all_eq_true, decide_eq_true_eq]

/-- Adding critical markers preserves structural well-formedness and action
determinism. -/
public theorem withCriticalMarkers_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (count : ℕ) :
    (g.withCriticalMarkers count).WellFormed := by
  unfold WellFormed wellFormedCode at hg ⊢
  rw [Bool.and_eq_true] at hg ⊢
  constructor
  · apply List.all_eq_true.mpr
    intro rule hrule
    rw [withCriticalMarkers_rawRules, List.mem_append] at hrule
    rcases hrule with horiginal | hmarker
    · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp horiginal
      exact liftedRule_wellFormed
        ((List.all_eq_true.mp hg.1) source hsource)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmarker
      exact markerRule_wellFormed g (List.mem_range.mp hi)
  · apply (actionDeterministicRulesCode_eq_true_iff _).mpr
    rw [withCriticalMarkers_rawRules, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      have horiginal :=
        (actionDeterministicRulesCode_eq_true_iff g.rawRules).mp hg.2
      apply horiginal.imp
      intro left right hapart
      rcases hapart with hlhs | haction
      · left
        simpa [liftCriticalRule, RawRule.lhs] using hlhs
      · right
        simpa [liftCriticalRule, RawRule.action] using haction
    · rw [List.pairwise_map]
      have hrange : (List.range count).Pairwise fun i j => i ≠ j :=
        List.nodup_iff_pairwise_ne.mp List.nodup_range
      apply hrange.imp
      intro i j hij
      right
      simpa [criticalMarkerRule, RawRule.action] using hij
    · intro original horiginal marker hmarker
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp horiginal
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmarker
      right
      simp [liftCriticalRule, criticalMarkerRule, RawRule.action]

/-- Exact lookup table for fresh marker symbols and marker actions. -/
public theorem withCriticalMarkers_ruleLookup_fresh
    (g : EncodedFirstOrderGrammar Action) (count i j : ℕ) :
    (g.withCriticalMarkers count).ruleLookup
        (g.criticalMarkerSymbol i) (.inr j) =
      if i = j ∧ i < count then some (g.criticalMarker i) else none := by
  by_cases hvalid : i = j ∧ i < count
  · rw [if_pos hvalid]
    rw [← hvalid.1]
    exact withCriticalMarkers_ruleLookup_marker g hvalid.2
  · rw [if_neg hvalid]
    unfold ruleLookup findRule
    change Option.map RawRule.rhs
        (List.find? (fun rule : RawRule (Action ⊕ ℕ) =>
            rule.lhs = g.criticalMarkerSymbol i ∧ rule.action = .inr j)
          (g.rawRules.map liftCriticalRule ++
            (List.range count).map g.criticalMarkerRule)) = none
    rw [List.find?_append, List.find?_map, List.find?_map]
    let markerTest : RawRule (Action ⊕ ℕ) → Bool := fun rule =>
      decide (rule.lhs = g.criticalMarkerSymbol i ∧ rule.action = .inr j)
    change Option.map RawRule.rhs
        ((Option.map liftCriticalRule
          (List.find? (markerTest ∘ liftCriticalRule) g.rawRules)).or
        (Option.map g.criticalMarkerRule
          (List.find? (markerTest ∘ g.criticalMarkerRule)
            (List.range count)))) = none
    have horiginal : List.find? (markerTest ∘ liftCriticalRule)
        g.rawRules = none := by
      apply List.find?_eq_none.mpr
      intro rule hrule
      simp [markerTest, liftCriticalRule, RawRule.lhs, RawRule.action]
    have hmarkers : List.find? (markerTest ∘ g.criticalMarkerRule)
        (List.range count) = none := by
      apply List.find?_eq_none.mpr
      intro k hk htest
      have hparts :
          (g.criticalMarkerRule k).lhs = g.criticalMarkerSymbol i ∧
            (g.criticalMarkerRule k).action = (.inr j : Action ⊕ ℕ) :=
        of_decide_eq_true htest
      have hki : k = i := by
        have hsum : g.ranks.length + k = g.ranks.length + i := by
          simpa [criticalMarkerRule, criticalMarkerSymbol,
            RawRule.lhs] using hparts.1
        omega
      have hkj : k = j := by
        simpa [criticalMarkerRule, RawRule.action] using hparts.2
      apply hvalid
      exact ⟨hki.symm.trans hkj, hki ▸ List.mem_range.mp hk⟩
    rw [horiginal, hmarkers]
    rfl

/-- Fresh marker actions are disabled at every original ranked symbol. -/
public theorem withCriticalMarkers_ruleLookup_markerAction_originalSymbol
    (g : EncodedFirstOrderGrammar Action) (count j X : ℕ)
    (hX : X < g.ranks.length) :
    (g.withCriticalMarkers count).ruleLookup X (.inr j) = none := by
  unfold ruleLookup findRule
  change Option.map RawRule.rhs
      (List.find? (fun rule : RawRule (Action ⊕ ℕ) =>
          rule.lhs = X ∧ rule.action = .inr j)
        (g.rawRules.map liftCriticalRule ++
          (List.range count).map g.criticalMarkerRule)) = none
  rw [List.find?_append, List.find?_map, List.find?_map]
  let markerTest : RawRule (Action ⊕ ℕ) → Bool := fun rule =>
    decide (rule.lhs = X ∧ rule.action = .inr j)
  change Option.map RawRule.rhs
      ((Option.map liftCriticalRule
        (List.find? (markerTest ∘ liftCriticalRule) g.rawRules)).or
      (Option.map g.criticalMarkerRule
        (List.find? (markerTest ∘ g.criticalMarkerRule)
          (List.range count)))) = none
  have horiginal : List.find? (markerTest ∘ liftCriticalRule)
      g.rawRules = none := by
    apply List.find?_eq_none.mpr
    intro rule hrule
    simp [markerTest, liftCriticalRule, RawRule.lhs, RawRule.action]
  have hmarkers : List.find? (markerTest ∘ g.criticalMarkerRule)
      (List.range count) = none := by
    apply List.find?_eq_none.mpr
    intro k hk htest
    have hsymbol : g.criticalMarkerSymbol k = X :=
      (of_decide_eq_true htest).1
    unfold criticalMarkerSymbol at hsymbol
    omega
  rw [horiginal, hmarkers]
  rfl

/-- Every original labelled step is preserved literally by the conservative
marker extension. -/
public theorem withCriticalMarkers_step?_lift
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (label : Label Action) (term : RegularTerm) :
    (g.withCriticalMarkers count).step? (liftCriticalLabel label) term =
      g.step? label term := by
  cases label with
  | inl action =>
      change (g.withCriticalMarkers count).rootRewrite? (.inl action) term =
        g.rootRewrite? action term
      unfold rootRewrite?
      cases hroot : term.rootApplication? with
      | none => rfl
      | some app =>
          rcases app with ⟨X, children⟩
          simp only
          rw [withCriticalMarkers_ruleLookup_original]
  | inr x =>
      change (g.withCriticalMarkers count).step? (.inr x) term =
        g.step? (.inr x) term
      unfold step?
      rfl

/-- Running a lifted original word in the extension gives exactly the original
run, including the raw target graph. -/
public theorem withCriticalMarkers_run?_lift
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (word : List (Label Action)) (term : RegularTerm) :
    (g.withCriticalMarkers count).run? (word.map liftCriticalLabel) term =
      g.run? word term := by
  induction word generalizing term with
  | nil => rfl
  | cons label word ih =>
      simp only [List.map_cons, run?_cons]
      rw [withCriticalMarkers_step?_lift]
      cases hstep : g.step? label term with
      | none => simp [hstep]
      | some target => simp [hstep, ih]

/-- Equality of extended trace languages implies equality of the original
trace languages by restricting to lifted words. -/
public theorem traceEquivalent_of_withCriticalMarkers
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    {left right : RegularTerm}
    (hequivalent :
      (g.withCriticalMarkers count).TraceEquivalent left right) :
    g.TraceEquivalent left right := by
  apply Set.ext
  intro word
  have hlifted := Set.ext_iff.mp hequivalent
    (word.map liftCriticalLabel)
  unfold traceLanguage IsTrace at hlifted ⊢
  simpa [withCriticalMarkers_run?_lift] using hlifted

end EncodedFirstOrderGrammar

end DCFEquivalence
