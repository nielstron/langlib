module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FirstOrderGrammar
public import Langlib.Utilities.PromiseComputability

@[expose]
public section

/-!
# Semi-deciding trace inequivalence of deterministic first-order grammars

This is the easy half of the equivalence procedure.  Root rewriting along a
given finite label word is uniformly computable from the raw finite grammar and
term graphs.  Consequently, inequivalence is recursively enumerable: enumerate
finite words and stop at the first word enabled by exactly one of the two terms.

The search is total on a distinguishing witness and makes no appeal to the
corrected Jančar completeness argument.  The converse semidecision (recognizing
equivalence) is deliberately kept in a separate module.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [Primcodable Action] [DecidableEq Action]

/-! ## Primitive-recursive graph operations -/

/-- `List.getElem?` is primitive recursive.  Mapping into `Option` lets us use
the library's total `getD` combinator without assuming that the element type is
inhabited. -/
private theorem list_getElem?_primrec {A : Type} [Primcodable A] :
    Primrec₂ (fun (xs : List A) (i : ℕ) => xs[i]?) := by
  apply Primrec₂.mk
  have hmap : Primrec (fun xs : List A => xs.map some) := by
    exact Primrec.list_map Primrec.id
      (Primrec₂.mk (Primrec.option_some.comp Primrec.snd))
  have hget : Primrec (fun p : List A × ℕ =>
      (p.1.map some).getD p.2 (none : Option A)) :=
    (Primrec.list_getD (none : Option A)).comp
      (hmap.comp Primrec.fst) Primrec.snd
  apply hget.of_eq
  intro p
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases p.1[p.2]? <;> rfl

private theorem nodes_primrec :
    Primrec (RegularTerm.nodes : RegularTerm → List RawNode) :=
  Primrec.fst

private theorem root_primrec :
    Primrec (RegularTerm.root : RegularTerm → ℕ) :=
  Primrec.snd

private theorem nodeAt?_primrec :
    Primrec₂ (RegularTerm.nodeAt? : RegularTerm → ℕ → Option RawNode) := by
  apply Primrec₂.mk
  exact list_getElem?_primrec.comp
    (nodes_primrec.comp Primrec.fst) Primrec.snd

private theorem rootNode?_primrec :
    Primrec (RegularTerm.rootNode? : RegularTerm → Option RawNode) :=
  nodeAt?_primrec.comp Primrec.id root_primrec

private theorem withRoot_primrec :
    Primrec₂ (RegularTerm.withRoot : RegularTerm → ℕ → RegularTerm) := by
  apply Primrec₂.mk
  exact Primrec.pair (nodes_primrec.comp Primrec.fst) Primrec.snd

private def applicationOfNode : RawNode → Option (ℕ × List ℕ)
  | .inl _ => none
  | .inr app => some app

private theorem applicationOfNode_primrec : Primrec applicationOfNode := by
  refine (Primrec.sumCasesOn (f := id)
    (g := fun _ (_ : ℕ) => (none : Option (ℕ × List ℕ)))
    (h := fun _ app => some app)
    Primrec.id ?_ ?_).of_eq ?_
  · exact Primrec₂.mk (Primrec.const none)
  · exact Primrec₂.mk (Primrec.option_some.comp Primrec.snd)
  · intro node
    cases node <;> rfl

private theorem rootApplication?_primrec :
    Primrec (RegularTerm.rootApplication? :
      RegularTerm → Option (ℕ × List ℕ)) := by
  refine (Primrec.option_casesOn
    (o := RegularTerm.rootNode?)
    (f := fun _ => none)
    (g := fun _ node => applicationOfNode node)
    rootNode?_primrec (Primrec.const none) ?_).of_eq ?_
  · show Primrec₂ (fun (_ : RegularTerm) (node : RawNode) =>
      applicationOfNode node)
    apply Primrec₂.mk
    exact applicationOfNode_primrec.comp Primrec.snd
  · intro term
    cases h : term.rootNode? with
    | none => simp [RegularTerm.rootApplication?, h]
    | some node =>
        cases node <;> simp [RegularTerm.rootApplication?, h, applicationOfNode]

private theorem shiftNode_primrec :
    Primrec₂ (RegularTerm.shiftNode : ℕ → RawNode → RawNode) := by
  apply Primrec₂.mk
  refine (Primrec.sumCasesOn
    (f := fun p : ℕ × RawNode => p.2)
    (g := fun _ x => (Sum.inl x : RawNode))
    (h := fun p app =>
      (Sum.inr (app.1, app.2.map (p.1 + ·)) : RawNode))
    Primrec.snd ?_ ?_).of_eq ?_
  · exact Primrec₂.mk (Primrec.sumInl.comp Primrec.snd)
  · apply Primrec₂.mk
    have hchildren : Primrec (fun q : (ℕ × RawNode) × (ℕ × List ℕ) =>
        q.2.2.map (q.1.1 + ·)) := by
      refine Primrec.list_map (Primrec.snd.comp Primrec.snd) ?_
      apply Primrec₂.mk
      exact Primrec.nat_add.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
    exact Primrec.sumInr.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) hchildren)
  · intro p
    cases p.2 <;> rfl

private theorem advanceArgumentOffset_primrec :
    Primrec RegularTerm.advanceArgumentOffset := by
  have hhead : Primrec (fun state : ℕ × List RegularTerm => state.2.head?) :=
    Primrec.list_head?.comp Primrec.snd
  refine (Primrec.option_casesOn
    (o := fun state : ℕ × List RegularTerm => state.2.head?)
    (f := id)
    (g := fun state term =>
      (state.1 + term.nodes.length, state.2.tail))
    hhead Primrec.id ?_).of_eq ?_
  · apply Primrec₂.mk
    exact Primrec.pair
      (Primrec.nat_add.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.list_length.comp (nodes_primrec.comp Primrec.snd)))
      (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst))
  · intro state
    rcases state with ⟨base, _ | ⟨term, terms⟩⟩ <;> rfl

private theorem argumentOffset_primrec :
    Primrec (fun p : (ℕ × List RegularTerm) × ℕ =>
      RegularTerm.argumentOffset p.1.1 p.1.2 p.2) := by
  have hstep : Primrec₂
      (fun (_ : (ℕ × List RegularTerm) × ℕ)
        (q : ℕ × (ℕ × List RegularTerm)) =>
          RegularTerm.advanceArgumentOffset q.2) := by
    apply Primrec₂.mk
    exact advanceArgumentOffset_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hiterate : Primrec (fun p : (ℕ × List RegularTerm) × ℕ =>
      Nat.rec (motive := fun _ => ℕ × List RegularTerm) p.1
        (fun _ state => RegularTerm.advanceArgumentOffset state) p.2) := by
    exact (Primrec.nat_rec' Primrec.snd Primrec.fst hstep).of_eq fun _ => rfl
  exact Primrec.fst.comp hiterate

private abbrev SubstitutionContext := RegularTerm × List RegularTerm

private abbrev ReferenceContext := SubstitutionContext × ℕ

private theorem argumentRoot?_primrec :
    Primrec (fun p : ReferenceContext =>
      p.1.1.argumentRoot? p.1.2 p.2) := by
  have hargument : Primrec (fun p : ReferenceContext => p.1.2[p.2]?) :=
    list_getElem?_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hoffset : Primrec (fun p : ReferenceContext =>
      RegularTerm.argumentOffset p.1.1.nodes.length p.1.2 p.2) :=
    argumentOffset_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.list_length.comp (nodes_primrec.comp
            (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have hroot : Primrec₂ (fun (p : ReferenceContext) (argument : RegularTerm) =>
      RegularTerm.argumentOffset p.1.1.nodes.length p.1.2 p.2 +
        argument.root) := by
    apply Primrec₂.mk
    exact Primrec.nat_add.comp (hoffset.comp Primrec.fst)
      (root_primrec.comp Primrec.snd)
  exact (Primrec.option_map hargument hroot).of_eq fun _ => rfl

private def resolveVariable (p : ReferenceContext) (x : ℕ) : ℕ :=
  (p.1.1.argumentRoot? p.1.2 x).getD p.2

private theorem resolveVariable_primrec : Primrec₂ resolveVariable := by
  apply Primrec₂.mk
  exact Primrec.option_getD.comp
    (argumentRoot?_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
    (Primrec.snd.comp Primrec.fst)

private def resolveNode (p : ReferenceContext) : RawNode → ℕ
  | .inl x => resolveVariable p x
  | .inr _ => p.2

private theorem resolveNode_primrec : Primrec₂ resolveNode := by
  apply Primrec₂.mk
  refine (Primrec.sumCasesOn
    (f := fun q : ReferenceContext × RawNode => q.2)
    (g := fun q x => resolveVariable q.1 x)
    (h := fun q _ => q.1.2)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact resolveVariable_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · apply Primrec₂.mk
    exact Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  · intro q
    cases q.2 <;> rfl

private theorem resolveRHSRef_primrec :
    Primrec (fun p : ReferenceContext =>
      p.1.1.resolveRHSRef p.1.2 p.2) := by
  have hnode : Primrec (fun p : ReferenceContext => p.1.1.nodeAt? p.2) :=
    nodeAt?_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  refine (Primrec.option_casesOn
    (o := fun p : ReferenceContext => p.1.1.nodeAt? p.2)
    (f := fun p => p.2)
    (g := resolveNode)
    hnode Primrec.snd resolveNode_primrec).of_eq ?_
  intro p
  cases h : p.1.1.nodeAt? p.2 with
  | none => simp [RegularTerm.resolveRHSRef, h]
  | some node =>
      cases node <;>
        simp [RegularTerm.resolveRHSRef, resolveNode, resolveVariable, h]

private def instantiateApplication (p : SubstitutionContext)
    (app : ℕ × List ℕ) : RawNode :=
  .inr (app.1, app.2.map (p.1.resolveRHSRef p.2))

private theorem instantiateApplication_primrec :
    Primrec₂ instantiateApplication := by
  apply Primrec₂.mk
  have hchildren : Primrec (fun p : SubstitutionContext × (ℕ × List ℕ) =>
      p.2.2.map (p.1.1.resolveRHSRef p.1.2)) := by
    refine Primrec.list_map (Primrec.snd.comp Primrec.snd) ?_
    apply Primrec₂.mk
    exact resolveRHSRef_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.sumInr.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd) hchildren)

private theorem instantiateNode_primrec :
    Primrec (fun p : SubstitutionContext × RawNode =>
      p.1.1.instantiateNode p.1.2 p.2) := by
  refine (Primrec.sumCasesOn
    (f := fun p : SubstitutionContext × RawNode => p.2)
    (g := fun _ x => (Sum.inl x : RawNode))
    (h := fun p app => instantiateApplication p.1 app)
    Primrec.snd ?_ ?_).of_eq ?_
  · exact Primrec₂.mk (Primrec.sumInl.comp Primrec.snd)
  · apply Primrec₂.mk
    exact instantiateApplication_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · intro p
    cases p.2 <;> rfl

private def shiftedArgumentNodes (state : ℕ × List RawNode)
    (argument : RegularTerm) : List RawNode :=
  argument.nodes.map (RegularTerm.shiftNode state.1)

private theorem shiftedArgumentNodes_primrec :
    Primrec₂ shiftedArgumentNodes := by
  apply Primrec₂.mk
  refine Primrec.list_map (nodes_primrec.comp Primrec.snd) ?_
  apply Primrec₂.mk
  exact shiftNode_primrec.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd

private theorem appendArgumentNodes_primrec :
    Primrec₂ RegularTerm.appendArgumentNodes := by
  apply Primrec₂.mk
  exact Primrec.pair
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_length.comp (nodes_primrec.comp Primrec.snd)))
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      (shiftedArgumentNodes_primrec.comp Primrec.fst Primrec.snd))

private theorem appendArguments_primrec :
    Primrec₂ RegularTerm.appendArguments := by
  apply Primrec₂.mk
  have hfold : Primrec (fun p : ℕ × List RegularTerm =>
      p.2.foldl RegularTerm.appendArgumentNodes (p.1, [])) := by
    refine Primrec.list_foldl
      (f := fun p : ℕ × List RegularTerm => p.2)
      (g := fun p => (p.1, ([] : List RawNode)))
      (h := fun (_ : ℕ × List RegularTerm)
        (q : (ℕ × List RawNode) × RegularTerm) =>
          RegularTerm.appendArgumentNodes q.1 q.2)
      Primrec.snd
      (Primrec.pair Primrec.fst (Primrec.const ([] : List RawNode))) ?_
    show Primrec₂ (fun (_ : ℕ × List RegularTerm)
      (q : (ℕ × List RawNode) × RegularTerm) =>
        RegularTerm.appendArgumentNodes q.1 q.2)
    apply Primrec₂.mk
    exact appendArgumentNodes_primrec.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.snd.comp hfold

private theorem instantiate_primrec :
    Primrec₂ RegularTerm.instantiate := by
  apply Primrec₂.mk
  have hmapped : Primrec (fun p : SubstitutionContext =>
      p.1.nodes.map (p.1.instantiateNode p.2)) := by
    refine Primrec.list_map (nodes_primrec.comp Primrec.fst) ?_
    apply Primrec₂.mk
    exact instantiateNode_primrec.comp
      (Primrec.pair Primrec.fst Primrec.snd)
  have happended : Primrec (fun p : SubstitutionContext =>
      RegularTerm.appendArguments p.1.nodes.length p.2) :=
    appendArguments_primrec.comp
      (Primrec.list_length.comp (nodes_primrec.comp Primrec.fst)) Primrec.snd
  have hnodes : Primrec (fun p : SubstitutionContext =>
      p.1.nodes.map (p.1.instantiateNode p.2) ++
        RegularTerm.appendArguments p.1.nodes.length p.2) :=
    Primrec.list_append.comp hmapped happended
  have hroot : Primrec (fun p : SubstitutionContext =>
      p.1.resolveRHSRef p.2 p.1.root) :=
    resolveRHSRef_primrec.comp
      (Primrec.pair Primrec.id (root_primrec.comp Primrec.fst))
  exact Primrec.pair hnodes hroot

/-! ## Primitive-recursive rule lookup and one-step execution -/

private theorem list_find?_primrec
    {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) := by
  have hguard : Primrec₂ (fun a b =>
      bif p a b then some b else none) := by
    show Primrec (fun q : A × B =>
      bif p q.1 q.2 then some q.2 else none)
    exact Primrec.cond
      (hp.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)
  have hhead := Primrec.list_head?.comp (Primrec.listFilterMap hf hguard)
  apply hhead.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih =>
      cases h : p a b <;> simp [h, ih]

omit [DecidableEq Action] in
private theorem rawRules_primrec :
    Primrec (rawRules : EncodedFirstOrderGrammar Action →
      List (RawRule Action)) :=
  Primrec.snd

omit [DecidableEq Action] in
private theorem rawRule_rhs_primrec :
    Primrec (RawRule.rhs : RawRule Action → RegularTerm) :=
  Primrec.snd.comp Primrec.snd

private abbrev RuleLookupContext (Action : Type) :=
  (EncodedFirstOrderGrammar Action × ℕ) × Action

private def ruleKeyMatches (p : RuleLookupContext Action)
    (rule : RawRule Action) : Bool :=
  decide (rule.lhs = p.1.2 ∧ rule.action = p.2)

private theorem ruleKeyMatches_primrec :
    Primrec₂ (ruleKeyMatches (Action := Action)) := by
  apply Primrec₂.mk
  have hlhs : Primrec (fun q : RuleLookupContext Action × RawRule Action =>
      decide (q.2.lhs = q.1.1.2)) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have haction : Primrec (fun q : RuleLookupContext Action × RawRule Action =>
      decide (q.2.action = q.1.2)) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.and.comp hlhs haction).of_eq fun _ => by
    simp [ruleKeyMatches]

private theorem findRule_primrec :
    Primrec (fun p : RuleLookupContext Action => p.1.1.findRule p.1.2 p.2) := by
  exact (list_find?_primrec
    (rawRules_primrec.comp (Primrec.fst.comp Primrec.fst))
    (ruleKeyMatches_primrec (Action := Action))).of_eq fun _ => rfl

private theorem ruleLookup_primrec :
    Primrec (fun p : RuleLookupContext Action => p.1.1.ruleLookup p.1.2 p.2) := by
  have hrhs : Primrec₂
      (fun (_ : RuleLookupContext Action) (rule : RawRule Action) => rule.rhs) := by
    apply Primrec₂.mk
    exact rawRule_rhs_primrec.comp Primrec.snd
  exact (Primrec.option_map findRule_primrec hrhs).of_eq fun _ => rfl

private abbrev RootRewriteContext (Action : Type) :=
  (EncodedFirstOrderGrammar Action × Action) × RegularTerm

private def rewriteApplication (p : RootRewriteContext Action)
    (app : ℕ × List ℕ) : Option RegularTerm :=
  (p.1.1.ruleLookup app.1 p.1.2).map fun rhs =>
    rhs.instantiate (app.2.map p.2.withRoot)

private theorem rewriteArguments_primrec :
    Primrec₂ (fun (source : RegularTerm) (children : List ℕ) =>
      children.map source.withRoot) := by
  apply Primrec₂.mk
  refine Primrec.list_map Primrec.snd ?_
  apply Primrec₂.mk
  exact withRoot_primrec.comp
    (Primrec.fst.comp Primrec.fst) Primrec.snd

private theorem rewriteApplication_primrec :
    Primrec₂ (rewriteApplication (Action := Action)) := by
  apply Primrec₂.mk
  have hlookup : Primrec
      (fun q : RootRewriteContext Action × (ℕ × List ℕ) =>
        q.1.1.1.ruleLookup q.2.1 q.1.1.2) :=
    ruleLookup_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have harguments : Primrec
      (fun q : RootRewriteContext Action × (ℕ × List ℕ) =>
        q.2.2.map q.1.2.withRoot) :=
    rewriteArguments_primrec.comp
      (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have hinstantiate : Primrec₂
      (fun (q : RootRewriteContext Action × (ℕ × List ℕ))
        (rhs : RegularTerm) => rhs.instantiate (q.2.2.map q.1.2.withRoot)) := by
    apply Primrec₂.mk
    exact instantiate_primrec.comp Primrec.snd
      (harguments.comp Primrec.fst)
  exact (Primrec.option_map hlookup hinstantiate).of_eq fun _ => rfl

private theorem rootRewrite?_primrec :
    Primrec (fun p : RootRewriteContext Action => p.1.1.rootRewrite? p.1.2 p.2) := by
  have happ : Primrec (fun p : RootRewriteContext Action => p.2.rootApplication?) :=
    rootApplication?_primrec.comp Primrec.snd
  exact (Primrec.option_casesOn
    (o := fun p : RootRewriteContext Action => p.2.rootApplication?)
    (f := fun _ => none)
    (g := rewriteApplication (Action := Action))
    happ (Primrec.const none)
      (rewriteApplication_primrec (Action := Action))).of_eq fun p => by
      cases h : p.2.rootApplication? with
      | none => simp [rootRewrite?, h]
      | some app => simp [rootRewrite?, rewriteApplication, h]

private def matchingVariableResult (p : ℕ × RegularTerm) (y : ℕ) :
    Option RegularTerm :=
  if p.1 = y then some p.2 else none

private theorem matchingVariableResult_primrec :
    Primrec₂ matchingVariableResult := by
  apply Primrec₂.mk
  exact Primrec.ite
    ((Primrec.eq : PrimrecRel fun x y : ℕ => x = y).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.const none)

private def variableNodeStep? (p : ℕ × RegularTerm) :
    RawNode → Option RegularTerm
  | .inl y => matchingVariableResult p y
  | .inr _ => none

private theorem variableNodeStep?_primrec :
    Primrec₂ variableNodeStep? := by
  apply Primrec₂.mk
  refine (Primrec.sumCasesOn
    (f := fun q : (ℕ × RegularTerm) × RawNode => q.2)
    (g := fun q y => matchingVariableResult q.1 y)
    (h := fun _ _ => (none : Option RegularTerm))
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact matchingVariableResult_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · exact Primrec₂.mk (Primrec.const none)
  · intro q
    cases q.2 <;> rfl

private def variableStep? (x : ℕ) (source : RegularTerm) :
    Option RegularTerm :=
  match source.rootNode? with
  | none => none
  | some node => variableNodeStep? (x, source) node

private theorem variableStep?_primrec : Primrec₂ variableStep? := by
  apply Primrec₂.mk
  have hroot : Primrec (fun p : ℕ × RegularTerm => p.2.rootNode?) :=
    rootNode?_primrec.comp Primrec.snd
  have hnode : Primrec₂
      (fun (p : ℕ × RegularTerm) (node : RawNode) =>
        variableNodeStep? p node) :=
    variableNodeStep?_primrec
  exact (Primrec.option_casesOn
    (o := fun p : ℕ × RegularTerm => p.2.rootNode?)
    (f := fun _ => none)
    (g := fun p node => variableNodeStep? p node)
    hroot (Primrec.const none) hnode).of_eq fun p => by
      cases h : p.2.rootNode? <;> simp [variableStep?, h]

/-- Packed raw input to the one-step first-order-grammar interpreter. -/
public abbrev StepInput (Action : Type) :=
  (EncodedFirstOrderGrammar Action × Label Action) × RegularTerm

private def ordinaryLabelStep (p : StepInput Action)
    (a : Action) : Option RegularTerm :=
  p.1.1.rootRewrite? a p.2

private theorem ordinaryLabelStep_primrec :
    Primrec₂ (ordinaryLabelStep (Action := Action)) := by
  apply Primrec₂.mk
  exact rootRewrite?_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      (Primrec.snd.comp Primrec.fst))

private def privateLabelStep (p : StepInput Action)
    (x : ℕ) : Option RegularTerm :=
  variableStep? x p.2

omit [DecidableEq Action] in
private theorem privateLabelStep_primrec :
    Primrec₂ (privateLabelStep (Action := Action)) := by
  apply Primrec₂.mk
  exact variableStep?_primrec.comp Primrec.snd
    (Primrec.snd.comp Primrec.fst)

omit [Primcodable Action] in
private theorem variableStep?_eq_private_step
    (g : EncodedFirstOrderGrammar Action) (x : ℕ) (source : RegularTerm) :
    variableStep? x source = g.step? (.inr x) source := by
  unfold variableStep? step?
  cases h : source.rootNode? with
  | none => rfl
  | some node =>
      cases node with
      | inl y =>
          by_cases hxy : x = y <;>
            simp [variableNodeStep?, matchingVariableResult, hxy]
      | inr app => rfl

/-- One-step execution is primitive recursive uniformly in the raw grammar,
observable label, and source graph. -/
public theorem step?_primrec :
    Primrec (fun p : StepInput Action =>
      p.1.1.step? p.1.2 p.2) := by
  refine (Primrec.sumCasesOn
    (f := fun p : StepInput Action => p.1.2)
    (g := ordinaryLabelStep (Action := Action))
    (h := privateLabelStep (Action := Action))
    (Primrec.snd.comp Primrec.fst)
    (ordinaryLabelStep_primrec (Action := Action))
    (privateLabelStep_primrec (Action := Action))).of_eq ?_
  intro p
  cases p.1.2 with
  | inl a => rfl
  | inr x => exact variableStep?_eq_private_step p.1.1 x p.2

/-! ## Primitive-recursive finite-word execution -/

private def advanceRun (g : EncodedFirstOrderGrammar Action)
    (stateAndLabel : Option RegularTerm × Label Action) :
    Option RegularTerm :=
  stateAndLabel.1.bind fun source => g.step? stateAndLabel.2 source

private theorem advanceRun_primrec : Primrec₂ (advanceRun (Action := Action)) := by
  apply Primrec₂.mk
  have hstate : Primrec (fun p : EncodedFirstOrderGrammar Action ×
      (Option RegularTerm × Label Action) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hstep : Primrec₂
      (fun (p : EncodedFirstOrderGrammar Action ×
          (Option RegularTerm × Label Action)) (source : RegularTerm) =>
        p.1.step? p.2.2 source) := by
    apply Primrec₂.mk
    exact step?_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        Primrec.snd)
  exact (Primrec.option_bind hstate hstep).of_eq fun _ => rfl

/-- Packed raw input to the finite-word first-order-grammar interpreter. -/
public abbrev RunInput (Action : Type) :=
  (EncodedFirstOrderGrammar Action × List (Label Action)) × RegularTerm

private def runFold? (p : RunInput Action) : Option RegularTerm :=
  p.1.2.foldl (fun state label => advanceRun p.1.1 (state, label)) (some p.2)

private theorem runFold?_primrec :
    Primrec (runFold? (Action := Action)) := by
  refine Primrec.list_foldl
    (f := fun p : RunInput Action => p.1.2)
    (g := fun p => some p.2)
    (h := fun p q => advanceRun p.1.1 q)
    (Primrec.snd.comp Primrec.fst)
    (Primrec.option_some.comp Primrec.snd) ?_
  show Primrec₂ (fun (p : RunInput Action)
    (q : Option RegularTerm × Label Action) => advanceRun p.1.1 q)
  apply Primrec₂.mk
  exact advanceRun_primrec.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd

omit [Primcodable Action] in
private theorem foldl_advanceRun_none
    (g : EncodedFirstOrderGrammar Action) (word : List (Label Action)) :
    word.foldl (fun state label => advanceRun g (state, label)) none = none := by
  induction word with
  | nil => rfl
  | cons label word ih =>
      simpa [advanceRun] using ih

omit [Primcodable Action] in
private theorem run?_eq_runFold? (g : EncodedFirstOrderGrammar Action)
    (word : List (Label Action)) (source : RegularTerm) :
    g.run? word source = runFold? ((g, word), source) := by
  induction word generalizing source with
  | nil => rfl
  | cons label word ih =>
      simp only [run?_cons, runFold?, List.foldl_cons]
      cases h : g.step? label source with
      | none =>
          rw [show advanceRun g (some source, label) =
            g.step? label source from rfl, h]
          simp only [Option.bind_none]
          exact (foldl_advanceRun_none g word).symm
      | some target =>
          rw [show advanceRun g (some source, label) =
            g.step? label source from rfl, h]
          simp only [Option.bind_some]
          exact ih target

/-- Finite-word trace execution is primitive recursive uniformly in the raw
grammar, word, and source term graph. -/
public theorem run?_primrec :
    Primrec (fun p : RunInput Action => p.1.1.run? p.1.2 p.2) :=
  runFold?_primrec.of_eq fun p => (run?_eq_runFold? p.1.1 p.1.2 p.2).symm

/-- The raw finite-word interpreter is a total computable function. -/
public theorem run?_computable :
    Computable (fun p : RunInput Action => p.1.1.run? p.1.2 p.2) :=
  run?_primrec.to_comp

/-! ## Enumerating distinguishing words -/

/-- A grammar and two pointed term graphs whose traces are to be compared. -/
public abbrev TracePair (Action : Type) :=
  EncodedFirstOrderGrammar Action × RegularTerm × RegularTerm

/-- The syntactic promise used by the first-order-grammar equivalence problem.
`WellFormed` already checks key uniqueness; `ActionDeterministic` is repeated
here to keep the public promise explicit. -/
@[expose] public def ValidTracePair (p : TracePair Action) : Prop :=
  p.1.WellFormed ∧ p.1.ActionDeterministic ∧
    p.2.1.Ground p.1.ranks ∧ p.2.2.Ground p.1.ranks

/-- A finite label word distinguishes a pair when it is enabled from exactly
one of the two pointed terms. -/
@[expose] public def distinguishes (p : TracePair Action)
    (word : List (Label Action)) : Bool :=
  decide ((p.1.run? word p.2.1).isSome ≠ (p.1.run? word p.2.2).isSome)

/-- Testing a supplied distinguishing word is primitive recursive. -/
public theorem distinguishes_primrec :
    Primrec₂ (distinguishes (Action := Action)) := by
  apply Primrec₂.mk
  have hleftRun : Primrec
      (fun q : TracePair Action × List (Label Action) =>
        q.1.1.run? q.2 q.1.2.1) :=
    run?_primrec.comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  have hrightRun : Primrec
      (fun q : TracePair Action × List (Label Action) =>
        q.1.1.run? q.2 q.1.2.2) :=
    run?_primrec.comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hleft : Primrec
      (fun q : TracePair Action × List (Label Action) =>
        (q.1.1.run? q.2 q.1.2.1).isSome) :=
    Primrec.option_isSome.comp hleftRun
  have hright : Primrec
      (fun q : TracePair Action × List (Label Action) =>
        (q.1.1.run? q.2 q.1.2.2).isSome) :=
    Primrec.option_isSome.comp hrightRun
  exact (Primrec.not.comp (Primrec.beq.comp hleft hright)).of_eq fun q => by
    cases hleft : (q.1.1.run? q.2 q.1.2.1).isSome <;>
      cases hright : (q.1.1.run? q.2 q.1.2.2).isSome <;>
        simp [distinguishes, hleft, hright]

omit [Primcodable Action] in
/-- Boolean distinction agrees exactly with unequal trace membership. -/
public theorem distinguishes_eq_true_iff (p : TracePair Action)
    (word : List (Label Action)) :
    distinguishes p word = true ↔
      (word ∈ p.1.traceLanguage p.2.1) ≠
        (word ∈ p.1.traceLanguage p.2.2) := by
  simp [distinguishes, traceLanguage, IsTrace]

omit [Primcodable Action] in
/-- In a deterministic labelled transition system, trace inequivalence has a
finite distinguishing word. -/
public theorem not_traceEquivalent_iff_exists_distinguishes
    (p : TracePair Action) :
    ¬p.1.TraceEquivalent p.2.1 p.2.2 ↔
      ∃ word, distinguishes p word = true := by
  change p.1.traceLanguage p.2.1 ≠ p.1.traceLanguage p.2.2 ↔ _
  rw [Function.ne_iff]
  constructor
  · rintro ⟨word, hword⟩
    exact ⟨word, (distinguishes_eq_true_iff p word).2 hword⟩
  · rintro ⟨word, hword⟩
    exact ⟨word, (distinguishes_eq_true_iff p word).1 hword⟩

/-- Decode the `k`th candidate word and test it. -/
@[expose] public def distinguishingIndexTest (p : TracePair Action)
    (k : ℕ) : Bool :=
  ((Encodable.decode (α := List (Label Action)) k).map
    (distinguishes p)).getD false

/-- Unbounded search for the first encoded distinguishing word. -/
@[expose] public def findDistinguishingIndex (p : TracePair Action) : Part ℕ :=
  Nat.rfind fun k => Part.some (distinguishingIndexTest p k)

private theorem distinguishingIndexTest_computable₂ :
    Computable₂ (distinguishingIndexTest (Action := Action)) := by
  have hmap : Computable (fun q : (TracePair Action × ℕ) =>
      (Encodable.decode (α := List (Label Action)) q.2).map
        (fun word => distinguishes q.1 word)) := by
    exact Computable.option_map
      (Computable.decode.comp Computable.snd)
      (Computable₂.mk
        (distinguishes_primrec.to_comp.comp
          (Computable.fst.comp Computable.fst) Computable.snd))
  apply Computable₂.mk
  exact (Computable.option_getD hmap (Computable.const false)).of_eq fun _ => rfl

/-- The distinguishing-index search is one uniform partial-recursive program. -/
public theorem findDistinguishingIndex_partrec :
    Partrec (findDistinguishingIndex (Action := Action)) := by
  exact Partrec.rfind distinguishingIndexTest_computable₂.partrec₂

/-- The search terminates exactly when some finite word distinguishes the pair. -/
public theorem findDistinguishingIndex_dom_iff (p : TracePair Action) :
    (findDistinguishingIndex p).Dom ↔
      ∃ word, distinguishes p word = true := by
  simp only [findDistinguishingIndex, Nat.rfind_dom, Part.some_dom]
  constructor
  · rintro ⟨k, hk⟩
    cases hdecode : Encodable.decode (α := List (Label Action)) k with
    | none => simp [distinguishingIndexTest, hdecode] at hk
    | some word =>
        exact ⟨word, by simpa [distinguishingIndexTest, hdecode] using hk⟩
  · rintro ⟨word, hword⟩
    refine ⟨Encodable.encode word, ?_⟩
    simpa [distinguishingIndexTest] using hword

/-- On explicitly well-formed action-deterministic codes, the raw search has
exactly the intended trace-inequivalence domain. -/
public theorem valid_findDistinguishingIndex_dom_iff
    (p : TracePair Action) (_hp : ValidTracePair p) :
    (findDistinguishingIndex p).Dom ↔
      ¬p.1.TraceEquivalent p.2.1 p.2.2 := by
  rw [findDistinguishingIndex_dom_iff,
    not_traceEquivalent_iff_exists_distinguishes]

/-- Trace inequivalence of raw encoded deterministic first-order grammars is
recursively enumerable, uniformly in the grammar and both pointed graphs. -/
public theorem traceInequivalence_re :
    REPred (fun p : TracePair Action =>
      ¬p.1.TraceEquivalent p.2.1 p.2.2) := by
  exact findDistinguishingIndex_partrec.dom_re.of_eq fun p =>
    (findDistinguishingIndex_dom_iff p).trans
      (not_traceEquivalent_iff_exists_distinguishes p).symm

end EncodedFirstOrderGrammar

end DCFEquivalence
