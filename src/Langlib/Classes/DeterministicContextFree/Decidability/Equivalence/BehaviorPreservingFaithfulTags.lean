module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FaithfulSchemaArguments

@[expose]
public section

/-!
# Behavior-preserving faithful argument tags

Critical nullary markers make substitution cancellable, but discard the
ordinary behavior of the argument they replace.  Here argument `i` instead
gets one fresh application root whose children are exactly the children of
the original root.  The fresh root symbol identifies the parameter, while
copied grammar rules can make its ordinary actions behave like the original
root symbol.

This file first isolates the semantic core: tagged substitution is
cancellable for schemas over the original rank table.  The executable copied
rule extension is defined afterwards.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The fresh root symbol reserved for tagged argument `i`. -/
@[expose] public def behaviorTagSymbol
    (g : EncodedFirstOrderGrammar Action) (i : ℕ) : ℕ :=
  g.ranks.length + i

/-- The original children retained below a fresh tagged root. -/
@[expose] public def behaviorTagChildren (argument : RegularTerm) :
    List ℕ :=
  match argument.rootApplication? with
  | some (_, children) => children
  | none => []

/-- Rank required by the fresh tagged root of one argument. -/
@[expose] public def behaviorTagRank (argument : RegularTerm) : ℕ :=
  (behaviorTagChildren argument).length

/-- Add one fresh application root above an argument, retaining the original
graph unchanged below it. -/
@[expose] public def behaviorTagArgument
    (g : EncodedFirstOrderGrammar Action)
  (i : ℕ) (argument : RegularTerm) : RegularTerm :=
  (argument.nodes ++
      [.inr (g.behaviorTagSymbol i, behaviorTagChildren argument)],
    argument.nodes.length)

/-- Tag every argument by its tuple position. -/
@[expose] public def behaviorTaggedArguments
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm) : List RegularTerm :=
  arguments.mapIdx fun i argument =>
    g.behaviorTagArgument i argument

/-- Rank table obtained by appending the ranks of all fresh wrapper roots. -/
@[expose] public def behaviorTaggedRanks
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm) : List ℕ :=
  g.ranks ++ arguments.map behaviorTagRank

@[simp] public theorem behaviorTagArgument_nodes
    (g : EncodedFirstOrderGrammar Action)
    (i : ℕ) (argument : RegularTerm) :
    (g.behaviorTagArgument i argument).nodes =
      argument.nodes ++
        [.inr (g.behaviorTagSymbol i,
          behaviorTagChildren argument)] := rfl

@[simp] public theorem behaviorTagArgument_root
    (g : EncodedFirstOrderGrammar Action)
    (i : ℕ) (argument : RegularTerm) :
    (g.behaviorTagArgument i argument).root =
      argument.nodes.length := rfl

@[simp] public theorem behaviorTagArgument_rootApplication?
    (g : EncodedFirstOrderGrammar Action)
    (i : ℕ) (argument : RegularTerm) :
    (g.behaviorTagArgument i argument).rootApplication? =
      some (g.behaviorTagSymbol i,
        behaviorTagChildren argument) := by
  simp [behaviorTagArgument, RegularTerm.rootApplication?,
    RegularTerm.rootNode?, RegularTerm.nodeAt?, RegularTerm.nodes,
    RegularTerm.root]

@[simp] public theorem behaviorTaggedArguments_length
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm) :
    (g.behaviorTaggedArguments arguments).length =
      arguments.length := by
  simp [behaviorTaggedArguments]

public theorem behaviorTaggedArguments_getElem?
    (g : EncodedFirstOrderGrammar Action)
    {arguments : List RegularTerm} {i : ℕ}
    {argument : RegularTerm}
    (hargument : arguments[i]? = some argument) :
    (g.behaviorTaggedArguments arguments)[i]? =
      some (g.behaviorTagArgument i argument) := by
  simp [behaviorTaggedArguments, hargument]

public theorem behaviorTaggedRanks_original
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm)
    {X : ℕ} (hX : X < g.ranks.length) :
    (g.behaviorTaggedRanks arguments)[X]? = g.ranks[X]? := by
  exact List.getElem?_append_left hX

public theorem behaviorTaggedRanks_tag
    (g : EncodedFirstOrderGrammar Action)
    {arguments : List RegularTerm} {i : ℕ}
    (hi : i < arguments.length) :
    (g.behaviorTaggedRanks arguments)[g.behaviorTagSymbol i]? =
      some (behaviorTagRank arguments[i]) := by
  unfold behaviorTaggedRanks behaviorTagSymbol
  rw [List.getElem?_append_right (by omega)]
  simp [hi]

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

private theorem behaviorTaggedInstantiation_nodeAt_resolved_variable
    (g : EncodedFirstOrderGrammar Action)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {i x : ℕ}
    (hnode : schema.nodeAt? i = some (.inl x))
    (hx : x < arguments.length) :
    ∃ children,
      (schema.instantiate (g.behaviorTaggedArguments arguments)).nodeAt?
          (schema.resolveRHSRef
            (g.behaviorTaggedArguments arguments) i) =
        some (.inr (g.behaviorTagSymbol x, children)) := by
  let argument := arguments[x]
  have hargument : arguments[x]? = some argument :=
    List.getElem?_eq_getElem hx
  have htaggedArgument :
      (g.behaviorTaggedArguments arguments)[x]? =
        some (g.behaviorTagArgument x argument) :=
    g.behaviorTaggedArguments_getElem? hargument
  have htaggedRoot :
      (g.behaviorTagArgument x argument).nodeAt?
          (g.behaviorTagArgument x argument).root =
        some (.inr (g.behaviorTagSymbol x,
          behaviorTagChildren argument)) := by
    simp [behaviorTagArgument, RegularTerm.nodeAt?,
      RegularTerm.nodes, RegularTerm.root]
  have hinstantiated :=
    RegularTerm.instantiate_nodeAt?_argument schema
      (g.behaviorTaggedArguments arguments)
      htaggedArgument htaggedRoot
  unfold RegularTerm.resolveRHSRef
  rw [hnode]
  simp only [RegularTerm.argumentRoot?, htaggedArgument,
    Option.map_some, Option.getD_some]
  rw [hinstantiated]
  exact ⟨(behaviorTagChildren argument).map
      (RegularTerm.argumentOffset schema.nodes.length
        (g.behaviorTaggedArguments arguments) x + ·), by
    simp [RegularTerm.shiftNode]⟩

private theorem behaviorTaggedInstantiation_nodeAt_resolved_application
    (g : EncodedFirstOrderGrammar Action)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {i X : ℕ} {children : List ℕ}
    (hnode : schema.nodeAt? i = some (.inr (X, children))) :
    (schema.instantiate (g.behaviorTaggedArguments arguments)).nodeAt?
        (schema.resolveRHSRef
          (g.behaviorTaggedArguments arguments) i) =
      some (.inr (X,
        children.map
          (schema.resolveRHSRef
            (g.behaviorTaggedArguments arguments)))) := by
  have hi : i < schema.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hinstantiated :=
    RegularTerm.instantiate_nodeAt?_rhs schema
      (g.behaviorTaggedArguments arguments) hi
  unfold RegularTerm.resolveRHSRef
  rw [hnode]
  simpa [RegularTerm.instantiateNode, hnode] using hinstantiated

/-- Fresh non-nullary root tags reflect unfolding equality of schemas over
the original rank table.  Unlike critical nullary markers, the tagged
arguments retain their original children and can therefore be equipped with
copied ordinary behavior. -/
public theorem unfoldingEquivalent_of_behaviorTaggedInstantiation
    (g : EncodedFirstOrderGrammar Action)
    {arity : ℕ} {arguments : List RegularTerm}
    (hargumentsLength : arguments.length = arity)
    {left right : RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (htagged :
      (left.instantiate (g.behaviorTaggedArguments arguments))
        |>.UnfoldingEquivalent
          (right.instantiate
            (g.behaviorTaggedArguments arguments))) :
    left.UnfoldingEquivalent right := by
  obtain ⟨R, hroots, hR⟩ := htagged
  let S : ℕ → ℕ → Prop := fun i j =>
    i < left.nodes.length ∧ j < right.nodes.length ∧
      R (left.resolveRHSRef
          (g.behaviorTaggedArguments arguments) i)
        (right.resolveRHSRef
          (g.behaviorTaggedArguments arguments) j)
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
        have hx : x < arguments.length := by
          rw [hargumentsLength]
          exact hleft.variable_lt_of_nodeAt hleftVariable
        obtain ⟨leftChildren, hleftTagged⟩ :=
          behaviorTaggedInstantiation_nodeAt_resolved_variable
            g hleftVariable hx
        rw [hleftTagged] at hlocal
        cases hrightKind : rightNode with
        | inl y =>
            have hrightVariable :
                right.nodeAt? j = some (.inl y) :=
              hrightNode.trans (congrArg some hrightKind)
            have hy : y < arguments.length := by
              rw [hargumentsLength]
              exact hright.variable_lt_of_nodeAt hrightVariable
            obtain ⟨rightChildren, hrightTagged⟩ :=
              behaviorTaggedInstantiation_nodeAt_resolved_variable
                g hrightVariable hy
            rw [hrightTagged] at hlocal
            simp only [RegularTerm.RawCompatible] at hlocal
            have hxy : x = y := by
              unfold behaviorTagSymbol at hlocal
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
            rw [behaviorTaggedInstantiation_nodeAt_resolved_application
              g hrightApplication] at hlocal
            simp only [RegularTerm.RawCompatible] at hlocal
            unfold behaviorTagSymbol at hlocal
            omega
    | inr leftApplication =>
        rcases leftApplication with ⟨X, leftChildren⟩
        have hleftApplication :
            left.nodeAt? i =
              some (.inr (X, leftChildren)) :=
          hleftNode.trans (congrArg some hleftKind)
        have hX :=
          RegularTerm.WellFormed.symbol_lt_of_nodeAt
            hleft hleftApplication
        rw [behaviorTaggedInstantiation_nodeAt_resolved_application
          g hleftApplication] at hlocal
        cases hrightKind : rightNode with
        | inl y =>
            have hrightVariable :
                right.nodeAt? j = some (.inl y) :=
              hrightNode.trans (congrArg some hrightKind)
            have hy : y < arguments.length := by
              rw [hargumentsLength]
              exact hright.variable_lt_of_nodeAt hrightVariable
            obtain ⟨rightChildren, hrightTagged⟩ :=
              behaviorTaggedInstantiation_nodeAt_resolved_variable
                g hrightVariable hy
            rw [hrightTagged] at hlocal
            simp only [RegularTerm.RawCompatible] at hlocal
            unfold behaviorTagSymbol at hlocal
            omega
        | inr rightApplication =>
            rcases rightApplication with ⟨Y, rightChildren⟩
            have hrightApplication :
                right.nodeAt? j =
                  some (.inr (Y, rightChildren)) :=
              hrightNode.trans (congrArg some hrightKind)
            rw [behaviorTaggedInstantiation_nodeAt_resolved_application
              g hrightApplication] at hlocal
            simp only [RegularTerm.RawCompatible] at hlocal
            rw [hleftApplication, hrightApplication]
            simp only [RegularTerm.RawCompatible]
            refine ⟨hlocal.1, ?_⟩
            apply forall₂_of_forall₂_map
              (left.resolveRHSRef
                (g.behaviorTaggedArguments arguments))
              (right.resolveRHSRef
                (g.behaviorTaggedArguments arguments))
              hlocal.2
            · intro child hchild
              exact hleftClosed.2 i X leftChildren
                hleftApplication child hchild
            · intro child hchild
              exact hrightClosed.2 j Y rightChildren
                hrightApplication child hchild

/-- Original root symbol whose ordinary rules are copied to a fresh tag. -/
@[expose] public def behaviorTagSourceSymbol
    (argument : RegularTerm) : ℕ :=
  match argument.rootApplication? with
  | some (X, _) => X
  | none => 0

/-- Lift an original grammar rule to the ordinary-action summand. -/
@[expose] public def liftBehaviorTagRule
    (rule : RawRule Action) : RawRule (Action ⊕ ℕ) :=
  (rule.lhs, .inl rule.action, rule.rhs)

/-- Copy one original rule to fresh tagged root `i`. -/
@[expose] public def copyBehaviorTagRule
    (g : EncodedFirstOrderGrammar Action)
    (i : ℕ) (rule : RawRule Action) :
    RawRule (Action ⊕ ℕ) :=
  (g.behaviorTagSymbol i, .inl rule.action, rule.rhs)

/-- All ordinary rules of the original argument-root symbol, copied in their
original table order to fresh root `i`. -/
@[expose] public def behaviorTagCopiedRules
    (g : EncodedFirstOrderGrammar Action)
    (i : ℕ) (argument : RegularTerm) :
    List (RawRule (Action ⊕ ℕ)) :=
  (g.rawRules.filter fun rule =>
    rule.lhs = behaviorTagSourceSymbol argument).map
      (g.copyBehaviorTagRule i)

/-- The unique discriminator action for fresh tagged root `i`.  Its RHS
reconstructs the same tagged root over the current children. -/
@[expose] public def behaviorTagDiscriminatorRule
    (g : EncodedFirstOrderGrammar Action)
    (i : ℕ) (argument : RegularTerm) :
    RawRule (Action ⊕ ℕ) :=
  (g.behaviorTagSymbol i, .inr i,
    RegularTerm.symbolTemplate
      (g.behaviorTagSymbol i) (behaviorTagRank argument))

/-- Complete copied/discriminator rule block of one tagged argument. -/
@[expose] public def behaviorTagRules
    (g : EncodedFirstOrderGrammar Action)
    (i : ℕ) (argument : RegularTerm) :
    List (RawRule (Action ⊕ ℕ)) :=
  g.behaviorTagCopiedRules i argument ++
    [g.behaviorTagDiscriminatorRule i argument]

/-- Conservatively extend a grammar by behavior-preserving fresh root tags
for the supplied argument tuple. -/
@[expose] public def withBehaviorTags
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm) :
    EncodedFirstOrderGrammar (Action ⊕ ℕ) :=
  (g.behaviorTaggedRanks arguments,
    g.rawRules.map liftBehaviorTagRule ++
      (arguments.mapIdx fun i argument =>
        g.behaviorTagRules i argument).flatten)

@[simp] public theorem withBehaviorTags_ranks
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm) :
    (g.withBehaviorTags arguments).ranks =
      g.behaviorTaggedRanks arguments := rfl

@[simp] public theorem withBehaviorTags_rawRules
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm) :
    (g.withBehaviorTags arguments).rawRules =
      g.rawRules.map liftBehaviorTagRule ++
        (arguments.mapIdx fun i argument =>
          g.behaviorTagRules i argument).flatten := rfl

private theorem mem_behaviorTagCopiedRules
    {g : EncodedFirstOrderGrammar Action}
    {i : ℕ} {argument : RegularTerm}
    {copied : RawRule (Action ⊕ ℕ)}
    (hcopied : copied ∈ g.behaviorTagCopiedRules i argument) :
    ∃ original ∈ g.rawRules,
      original.lhs = behaviorTagSourceSymbol argument ∧
      copied = g.copyBehaviorTagRule i original := by
  unfold behaviorTagCopiedRules at hcopied
  obtain ⟨original, horiginal, rfl⟩ :=
    List.mem_map.mp hcopied
  obtain ⟨horiginalRules, horiginalLhs⟩ :=
    List.mem_filter.mp horiginal
  exact ⟨original, horiginalRules,
    of_decide_eq_true horiginalLhs, rfl⟩

private theorem mem_behaviorTagRules_lhs
    {g : EncodedFirstOrderGrammar Action}
    {i : ℕ} {argument : RegularTerm}
    {rule : RawRule (Action ⊕ ℕ)}
    (hrule : rule ∈ g.behaviorTagRules i argument) :
    rule.lhs = g.behaviorTagSymbol i := by
  unfold behaviorTagRules at hrule
  rw [List.mem_append] at hrule
  rcases hrule with hcopied | hdiscriminator
  · obtain ⟨original, _horiginal, _hlhs, rfl⟩ :=
      mem_behaviorTagCopiedRules hcopied
    rfl
  · have hruleEq :
        rule = g.behaviorTagDiscriminatorRule i argument := by
      simpa using hdiscriminator
    subst rule
    rfl

/-- Every newly added row belongs to one fresh tagged root. -/
public theorem mem_flatten_behaviorTagRules_lhs
    {g : EncodedFirstOrderGrammar Action}
    {arguments : List RegularTerm}
    {rule : RawRule (Action ⊕ ℕ)}
    (hrule :
      rule ∈ (arguments.mapIdx fun i argument =>
        g.behaviorTagRules i argument).flatten) :
    ∃ i, i < arguments.length ∧
      rule.lhs = g.behaviorTagSymbol i := by
  obtain ⟨rules, hrules, hruleRules⟩ :=
    List.mem_flatten.mp hrule
  obtain ⟨i, hi, hrulesEq⟩ :=
    List.mem_mapIdx.mp hrules
  subst rules
  exact ⟨i, hi,
    mem_behaviorTagRules_lhs hruleRules⟩

/-- Original action lookup is unchanged at every original symbol. -/
public theorem withBehaviorTags_ruleLookup_original
    (g : EncodedFirstOrderGrammar Action)
    (arguments : List RegularTerm)
    (X : ℕ) (action : Action)
    (hX : X < g.ranks.length) :
    (g.withBehaviorTags arguments).ruleLookup X (.inl action) =
      g.ruleLookup X action := by
  unfold ruleLookup findRule
  change Option.map RawRule.rhs
      (List.find? (fun rule : RawRule (Action ⊕ ℕ) =>
          rule.lhs = X ∧ rule.action = .inl action)
        (g.rawRules.map liftBehaviorTagRule ++
          (arguments.mapIdx fun i argument =>
            g.behaviorTagRules i argument).flatten)) =
    Option.map RawRule.rhs
      (List.find? (fun rule : RawRule Action =>
        rule.lhs = X ∧ rule.action = action) g.rawRules)
  rw [List.find?_append, List.find?_map]
  let extendedTest : RawRule (Action ⊕ ℕ) → Bool := fun rule =>
    decide (rule.lhs = X ∧ rule.action = .inl action)
  let originalTest : RawRule Action → Bool := fun rule =>
    decide (rule.lhs = X ∧ rule.action = action)
  change Option.map RawRule.rhs
      ((Option.map liftBehaviorTagRule
        (List.find? (extendedTest ∘ liftBehaviorTagRule)
          g.rawRules)).or
        (List.find? extendedTest
          (arguments.mapIdx fun i argument =>
            g.behaviorTagRules i argument).flatten)) =
    Option.map RawRule.rhs (List.find? originalTest g.rawRules)
  have horiginal :
      List.find? (extendedTest ∘ liftBehaviorTagRule) g.rawRules =
        List.find? originalTest g.rawRules := by
    congr 1
    funext rule
    simp [extendedTest, originalTest, liftBehaviorTagRule,
      RawRule.lhs, RawRule.action]
  have htags :
      List.find? extendedTest
          (arguments.mapIdx fun i argument =>
            g.behaviorTagRules i argument).flatten = none := by
    apply List.find?_eq_none.mpr
    intro rule hrule
    obtain ⟨i, _hi, hlhs⟩ :=
      mem_flatten_behaviorTagRules_lhs hrule
    simp [extendedTest, hlhs, behaviorTagSymbol]
    omega
  rw [horiginal, htags]
  cases List.find? originalTest g.rawRules <;>
    simp [liftBehaviorTagRule, RawRule.rhs]

/-- Adding a fresh wrapper root preserves reference closure. -/
public theorem behaviorTagArgument_referenceClosed
    (g : EncodedFirstOrderGrammar Action)
    (i : ℕ) {argument : RegularTerm}
    (hclosed : argument.ReferenceClosed) :
    (g.behaviorTagArgument i argument).ReferenceClosed := by
  constructor
  · simp [behaviorTagArgument, RegularTerm.nodes, RegularTerm.root]
  · intro index X children hnode child hchild
    have hindexBound :
        index < argument.nodes.length + 1 := by
      have :=
        (List.getElem?_eq_some_iff.mp hnode).1
      simpa [behaviorTagArgument, RegularTerm.nodes] using this
    by_cases hindex : index < argument.nodes.length
    · have hnodeOriginal :
          argument.nodeAt? index = some (.inr (X, children)) := by
        unfold RegularTerm.nodeAt? at hnode ⊢
        rw [behaviorTagArgument_nodes,
          List.getElem?_append_left hindex] at hnode
        exact hnode
      have hchildBound :=
        hclosed.2 index X children hnodeOriginal child hchild
      change child <
        (g.behaviorTagArgument i argument).nodes.length
      rw [behaviorTagArgument_nodes, List.length_append]
      simpa using Nat.lt_succ_of_lt hchildBound
    · have hindexEq : index = argument.nodes.length := by
        omega
      subst index
      simp [behaviorTagArgument, RegularTerm.nodeAt?,
        RegularTerm.nodes] at hnode
      rcases hnode with ⟨rfl, rfl⟩
      cases hroot : argument.rootApplication? with
      | none =>
          simp [behaviorTagChildren, hroot] at hchild
      | some application =>
          rcases application with ⟨Y, rootChildren⟩
          have hchildren :
              behaviorTagChildren argument = rootChildren := by
            simp [behaviorTagChildren, hroot]
          rw [hchildren] at hchild
          have hrootNode :=
            RegularTerm.nodeAt?_root_of_rootApplication? hroot
          have hchildBound :=
            hclosed.2 argument.root Y rootChildren
              hrootNode child hchild
          change child <
            (g.behaviorTagArgument i argument).nodes.length
          rw [behaviorTagArgument_nodes, List.length_append]
          simpa using Nat.lt_succ_of_lt hchildBound

/-- Below the newly appended root, the tagged graph denotes exactly the
original argument graph. -/
public theorem behaviorTagArgument_withRoot_unfoldingEquivalent
    (g : EncodedFirstOrderGrammar Action)
    (tag : ℕ) {argument : RegularTerm}
    (hclosed : argument.ReferenceClosed)
    {index : ℕ} (hindex : index < argument.nodes.length) :
    (g.behaviorTagArgument tag argument).withRoot index
      |>.UnfoldingEquivalent (argument.withRoot index) := by
  let R : ℕ → ℕ → Prop := fun left right =>
    left = right ∧ left < argument.nodes.length
  refine ⟨R, ⟨rfl, hindex⟩, ?_⟩
  intro left right hrel
  rcases hrel with ⟨rfl, hleft⟩
  unfold RegularTerm.NodeCompatible
  have hnode :
      (g.behaviorTagArgument tag argument).nodeAt? left =
        argument.nodeAt? left := by
    unfold RegularTerm.nodeAt?
    rw [behaviorTagArgument_nodes,
      List.getElem?_append_left hleft]
  rw [RegularTerm.withRoot_nodeAt?,
    RegularTerm.withRoot_nodeAt?, hnode]
  cases hcurrent : argument.nodeAt? left with
  | none => trivial
  | some node =>
      cases node with
      | inl x => rfl
      | inr application =>
          rcases application with ⟨X, children⟩
          refine ⟨rfl, ?_⟩
          have relate :
              ∀ items : List ℕ,
                (∀ item ∈ items,
                  item < argument.nodes.length) →
                List.Forall₂ R items items := by
            intro items hall
            induction items with
            | nil => exact .nil
            | cons item items ih =>
                exact .cons ⟨rfl, hall item (by simp)⟩
                  (ih (fun next hnext =>
                    hall next (by simp [hnext])))
          exact relate children fun child hchild =>
            hclosed.2 left X children hcurrent child hchild

/-- One ordinary step of a tagged root mirrors the original argument-root
step whenever the surrounding extension supplies the copied lookup table. -/
public theorem behaviorTagArgument_step_original_of_lookup
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {extended : EncodedFirstOrderGrammar (Action ⊕ ℕ)}
    {i : ℕ} {argument : RegularTerm}
    (hargument : argument.Ground g.ranks)
    {X : ℕ} {children : List ℕ}
    (hroot : argument.rootApplication? = some (X, children))
    (action : Action)
    (hlookup :
      extended.ruleLookup (g.behaviorTagSymbol i) (.inl action) =
        g.ruleLookup X action) :
    match g.step? (.inl action) argument with
    | none =>
        extended.step? (.inl (.inl action))
          (g.behaviorTagArgument i argument) = none
    | some target =>
        ∃ taggedTarget,
          extended.step? (.inl (.inl action))
              (g.behaviorTagArgument i argument) =
            some taggedTarget ∧
          taggedTarget.UnfoldingEquivalent target := by
  have hclosed : argument.ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground hargument
  have htagChildren :
      behaviorTagChildren argument = children := by
    simp [behaviorTagChildren, hroot]
  simp only [step?, rootRewrite?, hroot,
    behaviorTagArgument_rootApplication?, htagChildren, hlookup]
  cases hrule : g.ruleLookup X action with
  | none => simp
  | some rhs =>
      simp only [Option.map_some]
      refine ⟨rhs.instantiate
          (children.map
            (g.behaviorTagArgument i argument).withRoot),
        rfl, ?_⟩
      apply RegularTerm.instantiate_unfoldingEquivalent
        (selected_rhs_referenceClosed hg hrule)
      · have hrootNode :=
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
        have hall :
            ∀ child ∈ children,
              child < argument.nodes.length :=
          hclosed.2 argument.root X children hrootNode
        have relate :
            ∀ items : List ℕ,
              (∀ child ∈ items,
                child < argument.nodes.length) →
              List.Forall₂ RegularTerm.UnfoldingEquivalent
                (items.map
                  (g.behaviorTagArgument i argument).withRoot)
                (items.map argument.withRoot) := by
          intro items hitems
          induction items with
          | nil => exact .nil
          | cons child items ih =>
              exact .cons
                (g.behaviorTagArgument_withRoot_unfoldingEquivalent
                  i hclosed (hitems child (by simp)))
                (ih (fun rest hrest =>
                  hitems rest (by simp [hrest])))
        exact relate children hall
      · intro taggedChild htaggedChild
        obtain ⟨child, hchild, rfl⟩ :=
          List.mem_map.mp htaggedChild
        exact RegularTerm.withRoot_referenceClosed
          (g.behaviorTagArgument_referenceClosed i hclosed)
          (by
            have hrootNode :=
              RegularTerm.nodeAt?_root_of_rootApplication? hroot
            have hchildBound := hclosed.2 argument.root X children
              hrootNode child hchild
            change child <
              (g.behaviorTagArgument i argument).nodes.length
            rw [behaviorTagArgument_nodes, List.length_append]
            simpa using Nat.lt_succ_of_lt hchildBound)
      · intro childTerm hchildTerm
        obtain ⟨child, hchild, rfl⟩ :=
          List.mem_map.mp hchildTerm
        exact RegularTerm.withRoot_referenceClosed hclosed
          (hclosed.2 argument.root X children
            (RegularTerm.nodeAt?_root_of_rootApplication? hroot)
            child hchild)

end EncodedFirstOrderGrammar

end DCFEquivalence
