module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisCalculus

@[expose]
public section

/-!
# Semantic laws for the finite-basis calculus

This file supplies the semantic facts which are not part of finite certificate
checking.  The first boundary is the graph-theoretic fixed-point law for a
regular unary limit.  It is proved on finite graph presentations, so later
trace arguments may use `F(Fᵒᵐᵐ¹) = Fᵒᵐᵐ¹` semantically without ever identifying
two graph codes.
-/

namespace DCFEquivalence

namespace RegularTerm

@[simp] public theorem unaryLimit_nodes (context : RegularTerm) :
    context.unaryLimit.nodes = context.nodes.map context.closeUnaryNode := rfl

@[simp] public theorem unaryLimit_root (context : RegularTerm) :
    context.unaryLimit.root = context.closeUnaryReference context.root := rfl

public theorem unaryLimit_nodeAt? (context : RegularTerm) (i : ℕ) :
    context.unaryLimit.nodeAt? i =
      (context.nodeAt? i).map context.closeUnaryNode := by
  simp [unaryLimit, nodeAt?, nodes, List.getElem?_map]

@[simp] public theorem closeUnaryReference_root (context : RegularTerm) :
    context.closeUnaryReference context.root = context.root := by
  unfold closeUnaryReference
  cases hnode : context.nodeAt? context.root with
  | none => rfl
  | some node =>
      cases node with
      | inl x => cases x <;> rfl
      | inr app => rfl

/-- The two copies of the context graph occurring in `F(Fᵒᵐᵐ¹)` are both
related to the single tied graph representing `Fᵒᵐᵐ¹`. -/
@[expose] public def UnaryLimitRelation (context : RegularTerm)
    (i j : ℕ) : Prop :=
  i < context.nodes.length ∧
    (j = i ∨ j = context.nodes.length + i)

private theorem closeUnaryReference_lt
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {i : ℕ} (hi : i < context.nodes.length) :
    context.closeUnaryReference i < context.nodes.length := by
  unfold closeUnaryReference
  cases hnode : context.nodeAt? i with
  | none => exact hi
  | some node =>
      cases node with
      | inr app => exact hi
      | inl x =>
          cases x with
          | zero => exact hclosed.1
          | succ x => exact hi

private theorem close_resolve_unaryLimitRelation
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {i : ℕ} (hi : i < context.nodes.length) :
    context.UnaryLimitRelation
      (context.closeUnaryReference i)
      (context.resolveRHSRef [context.unaryLimit] i) := by
  refine ⟨closeUnaryReference_lt hclosed hi, ?_⟩
  unfold closeUnaryReference resolveRHSRef
  cases hnode : context.nodeAt? i with
  | none => exact Or.inl rfl
  | some node =>
      cases node with
      | inr app => exact Or.inl rfl
      | inl x =>
          cases x with
          | zero =>
              right
              simp [argumentRoot?]
          | succ x =>
              left
              simp [argumentRoot?]

private theorem forall₂_map_same_local
    {A B C : Type} {R : B → C → Prop}
    (left : A → B) (right : A → C) (values : List A)
    (h : ∀ value ∈ values, R (left value) (right value)) :
    List.Forall₂ R (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun tail htail => h tail (by simp [htail]))

private theorem unaryLimitRelation_original_children
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {i X : ℕ} {children : List ℕ}
    (hnode : context.nodeAt? i = some (.inr (X, children))) :
    List.Forall₂ context.UnaryLimitRelation
      (children.map context.closeUnaryReference)
      (children.map (context.resolveRHSRef [context.unaryLimit])) := by
  apply forall₂_map_same_local
  intro child hchild
  apply close_resolve_unaryLimitRelation hclosed
  exact hclosed.2 i X children hnode child hchild

private theorem unaryLimitRelation_shifted_children
    {context : RegularTerm} (hclosed : context.ReferenceClosed)
    {children : List ℕ}
    (hchildren : ∀ child ∈ children, child < context.nodes.length) :
    List.Forall₂ context.UnaryLimitRelation
      (children.map context.closeUnaryReference)
      ((children.map context.closeUnaryReference).map
        (context.nodes.length + ·)) := by
  induction children with
  | nil => exact .nil
  | cons child children ih =>
      simp only [List.map_cons]
      apply List.Forall₂.cons
      · exact ⟨closeUnaryReference_lt hclosed (hchildren child (by simp)),
          Or.inr rfl⟩
      · exact ih fun tail htail => hchildren tail (by simp [htail])

private theorem unaryLimitRelation_isBisimulation
    {context : RegularTerm} (hclosed : context.ReferenceClosed) :
    context.unaryLimit.IsBisimulation
      (context.instantiate [context.unaryLimit])
      context.UnaryLimitRelation := by
  intro i j hij
  rcases hij with ⟨hi, hsame | hshift⟩
  · unfold NodeCompatible
    subst j
    rw [unaryLimit_nodeAt?, instantiate_nodeAt?_rhs context _ hi]
    cases hnode : context.nodeAt? i with
    | none => simp [RawCompatible]
    | some node =>
        cases node with
        | inl x => simp [closeUnaryNode, instantiateNode, RawCompatible]
        | inr app =>
            rcases app with ⟨X, children⟩
            simp only [Option.map_some, closeUnaryNode, instantiateNode,
              RawCompatible]
            exact ⟨trivial,
              unaryLimitRelation_original_children hclosed hnode⟩
  · unfold NodeCompatible
    subst j
    rw [unaryLimit_nodeAt?]
    let node : RawNode := context.nodes[i]
    have hnode : context.nodeAt? i = some node := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hi, rfl⟩
    have hlimitNode : context.unaryLimit.nodeAt? i =
        some (context.closeUnaryNode node) := by
      simp [unaryLimit_nodeAt?, hnode]
    have hinst : (context.instantiate [context.unaryLimit]).nodeAt?
          (context.nodes.length + i) =
        some (shiftNode context.nodes.length (context.closeUnaryNode node)) := by
      simpa using instantiate_nodeAt?_argument context [context.unaryLimit]
        (x := 0) (argument := context.unaryLimit)
        (i := i) (node := context.closeUnaryNode node)
        (by simp) hlimitNode
    rw [hnode, hinst]
    cases hkind : node with
    | inl x => simp [closeUnaryNode, shiftNode, RawCompatible]
    | inr app =>
        rcases app with ⟨X, children⟩
        simp only [closeUnaryNode, shiftNode, RawCompatible]
        refine ⟨rfl, unaryLimitRelation_shifted_children hclosed ?_⟩
        intro child hchild
        have happ : context.nodeAt? i = some (.inr (X, children)) := by
          simpa [hkind] using hnode
        exact hclosed.2 i X children happ child hchild

/-- Closing a unary context gives a semantic fixed point: the tied graph and
one further unfolding of the context denote the same regular term. -/
public theorem unaryLimit_unfoldingEquivalent_instantiate
    {context : RegularTerm} (hclosed : context.ReferenceClosed) :
    context.unaryLimit.UnfoldingEquivalent
      (context.instantiate [context.unaryLimit]) := by
  refine ⟨context.UnaryLimitRelation, ?_,
    unaryLimitRelation_isBisimulation hclosed⟩
  change context.UnaryLimitRelation
    (context.closeUnaryReference context.root)
    (context.resolveRHSRef [context.unaryLimit] context.root)
  exact close_resolve_unaryLimitRelation hclosed hclosed.1

/-- Tying variable edges preserves reference closure. -/
public theorem unaryLimit_referenceClosed
    {context : RegularTerm} (hclosed : context.ReferenceClosed) :
    context.unaryLimit.ReferenceClosed := by
  constructor
  · simpa using closeUnaryReference_lt hclosed hclosed.1
  · intro i X children hnode child hchild
    rw [unaryLimit_nodeAt?] at hnode
    cases hsource : context.nodeAt? i with
    | none => simp [hsource] at hnode
    | some sourceNode =>
        rw [hsource] at hnode
        cases sourceNode with
        | inl x => simp [closeUnaryNode] at hnode
        | inr app =>
            rcases app with ⟨Y, sourceChildren⟩
            simp only [Option.map_some, closeUnaryNode, Option.some.injEq,
              Sum.inr.injEq, Prod.mk.injEq] at hnode
            rcases hnode with ⟨hYX, hchildren⟩
            subst Y
            subst children
            obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
              List.mem_map.mp hchild
            rw [unaryLimit_nodes, List.length_map]
            apply closeUnaryReference_lt hclosed
            exact hclosed.2 i X sourceChildren hsource sourceChild hsourceChild

/-! ## Reference closure of unary instantiation -/

@[simp] public theorem instantiate_singleton_nodes_length
  (context argument : RegularTerm) :
    (context.instantiate [argument]).nodes.length =
      context.nodes.length + argument.nodes.length := by
  simp [instantiate, appendArguments, appendArgumentNodes, nodes]

private theorem resolveRHSRef_singleton_lt
    {context argument : RegularTerm}
    (hargument : argument.ReferenceClosed)
    {i : ℕ} (hi : i < context.nodes.length) :
    context.resolveRHSRef [argument] i <
      context.nodes.length + argument.nodes.length := by
  unfold resolveRHSRef
  cases hnode : context.nodeAt? i with
  | none => simp; omega
  | some node =>
      cases node with
      | inr app => simp; omega
      | inl x =>
          cases x with
          | zero =>
              simpa [argumentRoot?] using
                Nat.add_lt_add_left hargument.1 context.nodes.length
          | succ x =>
              simp [argumentRoot?]
              omega

/-- Instantiating a reference-closed unary context by a reference-closed graph
produces a reference-closed graph. -/
public theorem instantiate_singleton_referenceClosed
    {context argument : RegularTerm}
    (hcontext : context.ReferenceClosed)
    (hargument : argument.ReferenceClosed) :
    (context.instantiate [argument]).ReferenceClosed := by
  constructor
  · change context.resolveRHSRef [argument] context.root <
      (context.instantiate [argument]).nodes.length
    rw [instantiate_singleton_nodes_length]
    exact resolveRHSRef_singleton_lt hargument hcontext.1
  · intro i X children hnode child hchild
    have hi : i < (context.instantiate [argument]).nodes.length :=
      (List.getElem?_eq_some_iff.mp hnode).choose
    by_cases hprefix : i < context.nodes.length
    · rw [instantiate_nodeAt?_rhs context [argument] hprefix] at hnode
      cases hsource : context.nodeAt? i with
      | none => simp [hsource] at hnode
      | some sourceNode =>
          rw [hsource] at hnode
          cases sourceNode with
          | inl x => simp [instantiateNode] at hnode
          | inr app =>
              rcases app with ⟨Y, sourceChildren⟩
              simp only [Option.map_some, instantiateNode,
                Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at hnode
              rcases hnode with ⟨hYX, hchildren⟩
              subst Y
              subst children
              obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
                List.mem_map.mp hchild
              rw [instantiate_singleton_nodes_length]
              apply resolveRHSRef_singleton_lt hargument
              exact hcontext.2 i X sourceChildren hsource sourceChild
                hsourceChild
    · have htotal : i < context.nodes.length + argument.nodes.length := by
        simpa using hi
      let argumentIndex := i - context.nodes.length
      have hargumentIndex : argumentIndex < argument.nodes.length := by
        dsimp [argumentIndex]
        omega
      have hiSplit : i = context.nodes.length + argumentIndex := by
        dsimp [argumentIndex]
        omega
      let sourceNode : RawNode := argument.nodes[argumentIndex]
      have hsource : argument.nodeAt? argumentIndex = some sourceNode := by
        unfold nodeAt?
        rw [List.getElem?_eq_some_iff]
        exact ⟨hargumentIndex, rfl⟩
      have hcopied : (context.instantiate [argument]).nodeAt? i =
          some (shiftNode context.nodes.length sourceNode) := by
        rw [hiSplit]
        simpa using instantiate_nodeAt?_argument context [argument]
          (x := 0) (argument := argument) (i := argumentIndex)
          (node := sourceNode) (by simp) hsource
      rw [hcopied] at hnode
      cases hkind : sourceNode with
      | inl x => simp [hkind, shiftNode] at hnode
      | inr app =>
          rcases app with ⟨Y, sourceChildren⟩
          simp only [hkind, shiftNode, Option.some.injEq, Sum.inr.injEq,
            Prod.mk.injEq] at hnode
          rcases hnode with ⟨hYX, hchildren⟩
          subst Y
          subst children
          obtain ⟨sourceChild, hsourceChild, rfl⟩ :=
            List.mem_map.mp hchild
          have hsourceApp : argument.nodeAt? argumentIndex =
              some (.inr (X, sourceChildren)) := by
            simpa [hkind] using hsource
          have hbound := hargument.2 argumentIndex X sourceChildren
            hsourceApp sourceChild hsourceChild
          simpa using Nat.add_lt_add_left hbound context.nodes.length

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-! ## The guarded-context interface

The following structure names, rather than hides, the two remaining operational
congruence obligations.  They are properties of the concrete root-rewriting
semantics, not certificate assumptions.  Keeping them explicit lets the
finite-basis soundness proof proceed independently while the operational proof
is discharged below/alongside grammar normalization.
-/

/-- Trace approximants respect semantic equality of closed regular graphs, and
a nontrivial unary context delays observation of its argument by one action. -/
public structure GuardedContextLaws
    (g : EncodedFirstOrderGrammar Action) : Prop where
  unfoldingApprox : ∀ (n : ℕ) (left right : RegularTerm),
    left.ReferenceClosed → right.ReferenceClosed →
    left.UnfoldingEquivalent right → g.TraceApprox n left right
  congruent : ∀ (n : ℕ) (context left right : RegularTerm),
    context.WellFormed g.ranks 1 →
    left.ReferenceClosed → right.ReferenceClosed →
    g.TraceApprox n left right →
    g.TraceApprox n
      (context.instantiate [left]) (context.instantiate [right])
  guarded : ∀ (n : ℕ) (context left right : RegularTerm),
    context.WellFormed g.ranks 1 →
    context.nontrivialUnaryCode = true →
    left.ReferenceClosed → right.ReferenceClosed →
    g.TraceApprox n left right →
    g.TraceApprox (n + 1)
      (context.instantiate [left]) (context.instantiate [right])

public theorem GuardedContextLaws.traceApprox_of_unfoldingEquivalentCode
    {g : EncodedFirstOrderGrammar Action} (laws : GuardedContextLaws g)
    (n : ℕ) {left right : RegularTerm}
    (hleft : left.ReferenceClosed) (hright : right.ReferenceClosed)
    (hcode : left.unfoldingEquivalentCode right = true) :
    g.TraceApprox n left right := by
  apply laws.unfoldingApprox n left right hleft hright
  exact (RegularTerm.unfoldingEquivalentCode_eq_true_iff left right).mp hcode

/-- The graph fixed-point theorem gives trace equality at every finite depth
once unfolding equality is known to be operationally sound. -/
public theorem GuardedContextLaws.unaryLimit_fixedPointApprox
    {g : EncodedFirstOrderGrammar Action} (laws : GuardedContextLaws g)
    (n : ℕ) {context : RegularTerm}
    (hcontext : context.ReferenceClosed) :
    g.TraceApprox n (context.instantiate [context.unaryLimit])
      context.unaryLimit := by
  apply laws.unfoldingApprox
  · exact RegularTerm.instantiate_singleton_referenceClosed hcontext
      (RegularTerm.unaryLimit_referenceClosed hcontext)
  · exact RegularTerm.unaryLimit_referenceClosed hcontext
  · exact (RegularTerm.unaryLimit_unfoldingEquivalent_instantiate
      hcontext).symm

/-- Proposition 22 of arXiv:1010.4760v4, isolated from the later basis
argument: if `T` agrees through depth `k` with one unfolding `F(T)`, then it
agrees through the same depth with the tied regular limit `Fᵒᵐᵐ¹`. -/
public theorem GuardedContextLaws.traceApprox_unaryLimit
    {g : EncodedFirstOrderGrammar Action} (laws : GuardedContextLaws g)
    {context focus : RegularTerm}
    (hcontextCode : context.WellFormed g.ranks 1)
    (hnontrivial : context.nontrivialUnaryCode = true)
    (hfocus : focus.ReferenceClosed) :
    ∀ n, g.TraceApprox n focus (context.instantiate [focus]) →
      g.TraceApprox n focus context.unaryLimit := by
  have hcontext : context.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hcontextCode
  intro n
  induction n with
  | zero =>
      intro _
      exact g.traceApprox_refl 0 focus
  | succ n ih =>
      intro hstep
      have hprevious : g.TraceApprox n focus
          (context.instantiate [focus]) :=
        g.traceApprox_anti (Nat.le_succ n) hstep
      have hfocusLimit : g.TraceApprox n focus context.unaryLimit :=
        ih hprevious
      have hcontexts : g.TraceApprox (n + 1)
          (context.instantiate [focus])
          (context.instantiate [context.unaryLimit]) :=
        laws.guarded n context focus context.unaryLimit hcontextCode hnontrivial
          hfocus (RegularTerm.unaryLimit_referenceClosed hcontext) hfocusLimit
      exact hstep.trans (hcontexts.trans
        (laws.unaryLimit_fixedPointApprox (n + 1) hcontext))

/-! ## The approximant invariant for pair labels -/

omit [DecidableEq Action] in
public theorem referenceClosed_of_groundPairCode_left
    (g : EncodedFirstOrderGrammar Action) {left right : RegularTerm}
    (hground : g.groundPairCode left right = true) :
    left.ReferenceClosed := by
  rw [groundPairCode, Bool.and_eq_true] at hground
  apply RegularTerm.referenceClosed_of_ground
  exact (RegularTerm.groundCode_eq_true_iff g.ranks left).mp hground.1

omit [DecidableEq Action] in
public theorem referenceClosed_of_groundPairCode_right
    (g : EncodedFirstOrderGrammar Action) {left right : RegularTerm}
    (hground : g.groundPairCode left right = true) :
    right.ReferenceClosed := by
  rw [groundPairCode, Bool.and_eq_true] at hground
  apply RegularTerm.referenceClosed_of_ground
  exact (RegularTerm.groundCode_eq_true_iff g.ranks right).mp hground.2

private def GroundJudgment
    (g : EncodedFirstOrderGrammar Action) :
    CertificateJudgment Action → Prop
  | .pair _ left right => g.groundPairCode left right = true
  | .nop _ => True
  | .fail => True

private theorem groundJudgment_of_derivable
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment) :
    GroundJudgment g judgment := by
  induction h with
  | «axiom» hground => exact hground
  | transition _ _ _ _ hground => exact hground
  | limit _ _ _ _ _ _ _ _ _ _ hground => exact hground
  | symmetry hpair ih =>
      simp only [GroundJudgment] at ih ⊢
      unfold groundPairCode at ih ⊢
      rw [Bool.and_eq_true] at ih ⊢
      exact ⟨ih.2, ih.1⟩
  | basis => trivial
  | progression => trivial
  | rejection => trivial

/-- Every pair judgment in a checked derivation consists of structurally closed
ground terms. -/
public theorem groundPairCode_of_pair_derivable
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word : List (Label Action)} {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right)) :
    g.groundPairCode left right = true :=
  groundJudgment_of_derivable h

private def PairApproxProperty
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm) :
    CertificateJudgment Action → Prop
  | .pair word left right =>
      ∀ k, g.TraceApprox (word.length + k) initialLeft initialRight →
        g.TraceApprox k left right
  | .nop _ => True
  | .fail => True

private theorem pairApproxProperty_of_derivable
    {g : EncodedFirstOrderGrammar Action} (laws : GuardedContextLaws g)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment) :
    PairApproxProperty g initialLeft initialRight judgment := by
  induction h with
  | «axiom» hground =>
      intro k hinitial
      simpa using hinitial
  | @transition word left right left' right' label hpair happrox
      hleft hright hground ih =>
      intro k hinitial
      have hsource : g.TraceApprox (k + 1) left right := by
        apply ih (k + 1)
        apply g.traceApprox_anti (m := word.length + (k + 1))
          (n := (word ++ [label]).length + k) ?_ hinitial
        simp
        omega
      have hrel := hsource label
      rw [hleft, hright] at hrel
      cases hrel with
      | some hnext => exact hnext
  | @limit word shorterWord outerLeft outerRight shorterLeft shorterRight
      outerContext replacementContext focus houter hshorter
      houterContextCode hreplacementContextCode hfocusCode hnontrivial
      hlength houterMatchCode hshorterLeftCode hshorterRightCode hground
      ihOuter ihShorter =>
      intro k hinitial
      have houterApprox : g.TraceApprox k outerLeft outerRight :=
        ihOuter k hinitial
      have hshorterInitial :
          g.TraceApprox (shorterWord.length + k)
            initialLeft initialRight :=
        g.traceApprox_anti
          (Nat.add_le_add_right (Nat.le_of_lt hlength) k) hinitial
      have hshorterApprox :
          g.TraceApprox k shorterLeft shorterRight :=
        ihShorter k hshorterInitial
      have houterGround := groundPairCode_of_pair_derivable houter
      have hshorterGround := groundPairCode_of_pair_derivable hshorter
      have houterLeftClosed :=
        referenceClosed_of_groundPairCode_left g houterGround
      have hshorterLeftClosed :=
        referenceClosed_of_groundPairCode_left g hshorterGround
      have hshorterRightClosed :=
        referenceClosed_of_groundPairCode_right g hshorterGround
      have houterContext : outerContext.ReferenceClosed :=
        RegularTerm.referenceClosed_of_wellFormed houterContextCode
      have hreplacementContext : replacementContext.ReferenceClosed :=
        RegularTerm.referenceClosed_of_wellFormed hreplacementContextCode
      have hfocus : focus.ReferenceClosed :=
        RegularTerm.referenceClosed_of_ground
          ((RegularTerm.groundCode_eq_true_iff g.ranks focus).mp hfocusCode)
      have hreplacementFocus :
          (replacementContext.instantiate [focus]).ReferenceClosed :=
        RegularTerm.instantiate_singleton_referenceClosed
          hreplacementContext hfocus
      have houterFocus :
          (outerContext.instantiate [focus]).ReferenceClosed :=
        RegularTerm.instantiate_singleton_referenceClosed houterContext hfocus
      have houterMatch : g.TraceApprox k outerLeft
          (outerContext.instantiate [focus]) :=
        laws.traceApprox_of_unfoldingEquivalentCode k houterLeftClosed
          houterFocus houterMatchCode
      have hshorterLeft : g.TraceApprox k shorterLeft focus :=
        laws.traceApprox_of_unfoldingEquivalentCode k hshorterLeftClosed
          hfocus hshorterLeftCode
      have hshorterRight : g.TraceApprox k shorterRight
          (replacementContext.instantiate [focus]) :=
        laws.traceApprox_of_unfoldingEquivalentCode k hshorterRightClosed
          hreplacementFocus hshorterRightCode
      have hfocusUnfolding : g.TraceApprox k focus
          (replacementContext.instantiate [focus]) :=
        hshorterLeft.symm.trans (hshorterApprox.trans hshorterRight)
      have hfocusLimit :
          g.TraceApprox k focus replacementContext.unaryLimit :=
        laws.traceApprox_unaryLimit hreplacementContextCode hnontrivial hfocus k
          hfocusUnfolding
      have hcontexts : g.TraceApprox k
          (outerContext.instantiate [focus])
          (outerContext.instantiate [replacementContext.unaryLimit]) :=
        laws.congruent k outerContext focus replacementContext.unaryLimit
          houterContextCode hfocus
          (RegularTerm.unaryLimit_referenceClosed hreplacementContext)
          hfocusLimit
      exact hcontexts.symm.trans
        (houterMatch.symm.trans houterApprox)
  | @symmetry word left right hpair ih =>
      intro k hinitial
      exact (ih k hinitial).symm
  | basis => trivial
  | progression => trivial
  | rejection => trivial

/-- A pair label at word `u` cannot lose more than `|u|` levels of finite trace
agreement relative to the initial pair (Proposition 31(1)). -/
public theorem CertificateDerivable.pairApproxInvariant
    {g : EncodedFirstOrderGrammar Action} (laws : GuardedContextLaws g)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word : List (Label Action)} {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right)) :
    ∀ k, g.TraceApprox (word.length + k) initialLeft initialRight →
      g.TraceApprox k left right :=
  pairApproxProperty_of_derivable laws h

/-- In particular, every pair label derived from an equivalent initial pair is
itself trace equivalent. -/
public theorem CertificateDerivable.pair_traceEquivalent_of_initial
    {g : EncodedFirstOrderGrammar Action} (laws : GuardedContextLaws g)
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word : List (Label Action)} {left right : RegularTerm}
    (h : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right))
    (hinitial : g.TraceEquivalent initialLeft initialRight) :
    g.TraceEquivalent left right := by
  apply (g.traceEquivalent_iff_forall_traceApprox left right).mpr
  intro k
  apply h.pairApproxInvariant laws k
  exact (g.traceEquivalent_iff_forall_traceApprox initialLeft initialRight).mp
    hinitial (word.length + k)

end EncodedFirstOrderGrammar

end DCFEquivalence
