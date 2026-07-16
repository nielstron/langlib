module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteBasisCalculus
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TraceInequivalence
public import Mathlib.Data.List.Sublists

@[expose]
public section

/-!
# Effective finite-basis certificates

This file gives the finite-basis judgment and row syntax honest primitive
encodings, proves that the executable certificate checker is computable
uniformly in the raw grammar, initial terms, basis, and row list, and packages
unbounded certificate enumeration as an RE predicate.

No semantic equivalence fact is used here: this is solely the effective bridge
from finite row objects to the positive semidecision.
-/

namespace DCFEquivalence

/-! ## Primitive encodings of certificate syntax -/

public abbrev CertificateJudgmentCode (Action : Type) :=
  (List (Label Action) × RegularTerm × RegularTerm) ⊕
    (List (Label Action) ⊕ Unit)

public def certificateJudgmentEquiv (Action : Type) :
    CertificateJudgment Action ≃ CertificateJudgmentCode Action where
  toFun
    | .pair word left right => .inl (word, left, right)
    | .nop word => .inr (.inl word)
    | .fail => .inr (.inr ())
  invFun
    | .inl (word, left, right) => .pair word left right
    | .inr (.inl word) => .nop word
    | .inr (.inr _) => .fail
  left_inv judgment := by cases judgment <;> rfl
  right_inv code := by
    rcases code with code | code
    · rcases code with ⟨word, left, right⟩
      rfl
    · rcases code with word | inhabitant
      · rfl
      · rcases inhabitant
        rfl

public instance certificateJudgmentPrimcodable
    (Action : Type) [Primcodable Action] :
    Primcodable (CertificateJudgment Action) :=
  Primcodable.ofEquiv (CertificateJudgmentCode Action)
    (certificateJudgmentEquiv Action)

public abbrev LimitRowCode :=
  ℕ × ℕ × RegularTerm × RegularTerm × RegularTerm

public abbrev BasisRowCode :=
  ℕ × ℕ × List RegularTerm

public abbrev ProgressionRowCode :=
  ℕ × List ℕ

public abbrev CertificateRowCode (Action : Type) :=
  Unit ⊕ ((ℕ × Label Action) ⊕
    (LimitRowCode ⊕ (ℕ ⊕
      (BasisRowCode ⊕ (ProgressionRowCode ⊕ ℕ)))))

public def certificateRowEquiv (Action : Type) :
    CertificateRow Action ≃ CertificateRowCode Action where
  toFun
    | .axiom => .inl ()
    | .transition pairRef label => .inr (.inl (pairRef, label))
    | .limit outerRef shorterRef outerContext replacementContext focus =>
        .inr (.inr (.inl
          (outerRef, shorterRef, outerContext, replacementContext, focus)))
    | .symmetry pairRef => .inr (.inr (.inr (.inl pairRef)))
    | .basis pairRef basisRef arguments =>
        .inr (.inr (.inr (.inr (.inl (pairRef, basisRef, arguments)))))
    | .progression pairRef childRefs =>
        .inr (.inr (.inr (.inr (.inr (.inl (pairRef, childRefs))))))
    | .rejection pairRef =>
        .inr (.inr (.inr (.inr (.inr (.inr pairRef)))))
  invFun
    | .inl _ => .axiom
    | .inr (.inl (pairRef, label)) => .transition pairRef label
    | .inr (.inr (.inl
        (outerRef, shorterRef, outerContext, replacementContext, focus))) =>
        .limit outerRef shorterRef outerContext replacementContext focus
    | .inr (.inr (.inr (.inl pairRef))) => .symmetry pairRef
    | .inr (.inr (.inr (.inr (.inl (pairRef, basisRef, arguments))))) =>
        .basis pairRef basisRef arguments
    | .inr (.inr (.inr (.inr (.inr (.inl (pairRef, childRefs)))))) =>
        .progression pairRef childRefs
    | .inr (.inr (.inr (.inr (.inr (.inr pairRef))))) =>
        .rejection pairRef
  left_inv row := by cases row <;> rfl
  right_inv code := by
    rcases code with inhabitant | code
    · rcases inhabitant
      rfl
    · rcases code with transition | code
      · rfl
      · rcases code with limit | code
        · rfl
        · rcases code with symmetry | code
          · rfl
          · rcases code with basis | code
            · rfl
            · rcases code with progression | rejection
              · rfl
              · rfl

public instance certificateRowPrimcodable
    (Action : Type) [Primcodable Action] :
    Primcodable (CertificateRow Action) :=
  Primcodable.ofEquiv (CertificateRowCode Action)
    (certificateRowEquiv Action)

namespace EncodedFirstOrderGrammar

variable {Action : Type} [Primcodable Action] [DecidableEq Action]

private theorem judgmentPair_primrec :
    Primrec (fun input :
        List (Label Action) × RegularTerm × RegularTerm =>
      CertificateJudgment.pair input.1 input.2.1 input.2.2) := by
  apply (Primrec.of_equiv_iff
    (certificateJudgmentEquiv Action)).mp
  exact Primrec.sumInl

private theorem judgmentNop_primrec :
    Primrec (fun word : List (Label Action) =>
      (CertificateJudgment.nop word :
        CertificateJudgment Action)) := by
  apply (Primrec.of_equiv_iff
    (certificateJudgmentEquiv Action)).mp
  exact Primrec.sumInr.comp (Primrec.sumInl.comp Primrec.id)

private theorem judgmentFail_primrec :
    Primrec (fun (_ : Unit) =>
      (CertificateJudgment.fail :
        CertificateJudgment Action)) := by
  apply (Primrec.of_equiv_iff
    (certificateJudgmentEquiv Action)).mp
  exact Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.id)

/-! ## Small primitive-recursive list combinators -/

public theorem list_all_primrec
    {Input Element : Type} [Primcodable Input] [Primcodable Element]
    {items : Input → List Element} {test : Input → Element → Bool}
    (hitems : Primrec items) (htest : Primrec₂ test) :
    Primrec fun input => (items input).all (test input) := by
  have hstep : Primrec₂ fun (input : Input) (state : Element × Bool) =>
      test input state.1 && state.2 := by
    apply Primrec₂.mk
    exact Primrec.and.comp
      (htest.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr hitems (Primrec.const true) hstep).of_eq
  intro input
  induction items input with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem list_any_primrec
    {Input Element : Type} [Primcodable Input] [Primcodable Element]
    {items : Input → List Element} {test : Input → Element → Bool}
    (hitems : Primrec items) (htest : Primrec₂ test) :
    Primrec fun input => (items input).any (test input) := by
  have hstep : Primrec₂ fun (input : Input) (state : Element × Bool) =>
      test input state.1 || state.2 := by
    apply Primrec₂.mk
    exact Primrec.or.comp
      (htest.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr hitems (Primrec.const false) hstep).of_eq
  intro input
  induction items input with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem list_sublists_primrec {Element : Type} [Primcodable Element] :
    Primrec (List.sublists' : List Element → List (List Element)) := by
  let step : List Element →
      Element × List Element × List (List Element) → List (List Element) :=
    fun _ state => state.2.2 ++ state.2.2.map (state.1 :: ·)
  have hstep : Primrec₂ step := by
    apply Primrec₂.mk
    have htail : Primrec (fun p : List Element ×
        (Element × List Element × List (List Element)) => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hmap : Primrec (fun p : List Element ×
        (Element × List Element × List (List Element)) =>
          p.2.2.2.map (p.2.1 :: ·)) := by
      apply Primrec.list_map htail
      apply Primrec₂.mk
      exact Primrec.list_cons.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    exact Primrec.list_append.comp htail hmap
  apply (Primrec.list_rec Primrec.id (Primrec.const [[]]) hstep).of_eq
  intro items
  induction items with
  | nil => simp [List.sublists'_nil]
  | cons head tail ih =>
      change step (head :: tail) (head, tail,
        List.recOn tail [[]] fun b l IH => step tail (b, l, IH)) =
          (head :: tail).sublists'
      have ih' : (List.recOn tail [[]] fun b l IH =>
          step tail (b, l, IH)) = tail.sublists' := by
        simpa using ih
      rw [ih', List.sublists'_cons]

private theorem list_mem_primrec {Element : Type}
    [Primcodable Element] [DecidableEq Element] :
    Primrec₂ fun (items : List Element) (value : Element) =>
      decide (value ∈ items) := by
  apply Primrec₂.mk
  have htest : Primrec₂ fun (input : List Element × Element)
      (candidate : Element) => decide (candidate = input.2) := by
    apply Primrec₂.mk
    exact Primrec.eq.decide.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  have hany : Primrec fun input : List Element × Element =>
      input.1.any fun candidate => decide (candidate = input.2) :=
    list_any_primrec Primrec.fst htest
  apply hany.of_eq
  rintro ⟨items, value⟩
  induction items with
  | nil => simp
  | cons head tail ih =>
      have ih' : (tail.any fun candidate => decide (value = candidate)) =
          decide (value ∈ tail) := by
        simpa [eq_comm] using ih
      simp [ih', eq_comm]

private theorem list_filter_primrec
    {Input Element : Type} [Primcodable Input] [Primcodable Element]
    {items : Input → List Element} {test : Input → Element → Bool}
    (hitems : Primrec items) (htest : Primrec₂ test) :
    Primrec fun input => (items input).filter (test input) := by
  have hguard : Primrec₂ fun input element =>
      bif test input element then some element else none := by
    show Primrec fun p : Input × Element =>
      bif test p.1 p.2 then some p.2 else none
    exact Primrec.cond
      (htest.comp Primrec.fst Primrec.snd)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)
  exact (Primrec.listFilterMap hitems hguard).of_eq fun input => by
    induction items input with
    | nil => rfl
    | cons head tail ih =>
        cases h : test input head <;> simp [h, ih]

private theorem list_dedup_primrec
    {Element : Type} [Primcodable Element] [DecidableEq Element] :
    Primrec (List.dedup : List Element → List Element) := by
  let step : List Element →
      Element × List Element × List Element → List Element :=
    fun _ state =>
      if state.1 ∈ state.2.1 then state.2.2 else state.1 :: state.2.2
  have hstep : Primrec₂ step := by
    apply Primrec₂.mk
    exact (Primrec.cond
      (list_mem_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).of_eq fun input => by
          simp [step]
  apply (Primrec.list_rec Primrec.id (Primrec.const []) hstep).of_eq
  intro items
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change step (head :: tail)
        (head, tail, List.recOn tail [] fun b l IH => step tail (b, l, IH)) =
          (head :: tail).dedup
      rw [show (List.recOn tail [] fun b l IH => step tail (b, l, IH)) =
        tail.dedup by simpa using ih]
      simp only [step, List.dedup_cons]

private theorem list_product_primrec
    {Left Right : Type} [Primcodable Left] [Primcodable Right] :
    Primrec₂ (List.product : List Left → List Right → List (Left × Right)) := by
  apply Primrec₂.mk
  have hrows : Primrec fun input : List Left × List Right =>
      input.1.map fun left => input.2.map fun right => (left, right) := by
    apply Primrec.list_map Primrec.fst
    apply Primrec₂.mk
    exact Primrec.list_map
      (Primrec.snd.comp Primrec.fst)
      (Primrec₂.mk (Primrec.pair
        (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact (Primrec.list_flatten.comp hrows).of_eq fun input => by
    rfl

public theorem list_all₂_primrec
    {Input Left Right : Type}
    [Primcodable Input] [Primcodable Left] [Primcodable Right]
    {left : Input → List Left} {right : Input → List Right}
    {test : Input → Left → Right → Bool}
    (hleft : Primrec left) (hright : Primrec right)
    (htest : Primrec fun p : ((Input × Left) × Right) =>
      test p.1.1 p.1.2 p.2) :
    Primrec fun input => List.all₂ (test input) (left input) (right input) := by
  let step : Input → (List Right × Bool) × Left → List Right × Bool :=
    fun input state =>
      match state.1.1 with
      | [] => ([], false)
      | head :: tail =>
          (tail, state.1.2 && test input state.2 head)
  have hstep : Primrec₂ step := by
    apply Primrec₂.mk
    let FoldInput := Input × ((List Right × Bool) × Left)
    have hhead : Primrec fun p : FoldInput => p.2.1.1.head? :=
      Primrec.list_head?.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    refine (Primrec.option_casesOn
      (o := fun p : FoldInput => p.2.1.1.head?)
      (f := fun _ => (([] : List Right), false))
      (g := fun p head =>
        (p.2.1.1.tail, p.2.1.2 && test p.1 p.2.2 head))
      hhead (Primrec.const ([], false)) ?_).of_eq ?_
    · apply Primrec₂.mk
      exact Primrec.pair
        (Primrec.list_tail.comp
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.and.comp
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
          (htest.comp
            (Primrec.pair
              (Primrec.pair
                (Primrec.fst.comp Primrec.fst)
                (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
              Primrec.snd)))
    · intro p
      rcases p with ⟨input, ⟨⟨_ | ⟨head, tail⟩, ok⟩, leftHead⟩⟩ <;> rfl
  let foldResult := fun input =>
    (left input).foldl (fun state element => step input (state, element))
      (right input, true)
  have hfold : Primrec foldResult := by
    exact Primrec.list_foldl
      (f := left)
      (g := fun input => (right input, true))
      (h := step)
      hleft (Primrec.pair hright (Primrec.const true)) hstep
  have hremainingEmpty : Primrec fun input =>
      decide ((foldResult input).1.length = 0) := by
    exact Primrec.eq.decide.comp
      (Primrec.list_length.comp (Primrec.fst.comp hfold))
      (Primrec.const 0)
  have hresult : Primrec fun input =>
      (foldResult input).2 &&
        decide ((foldResult input).1.length = 0) :=
    Primrec.and.comp (Primrec.snd.comp hfold) hremainingEmpty
  apply hresult.of_eq
  intro input
  have hspec : ∀ (leftList : List Left) (rightList : List Right) (ok : Bool),
      ((leftList.foldl (fun state element => step input (state, element))
          (rightList, ok)).2 &&
        decide ((leftList.foldl
          (fun state element => step input (state, element))
          (rightList, ok)).1.length = 0)) =
        (ok && List.all₂ (test input) leftList rightList) := by
    intro leftList
    induction leftList with
    | nil =>
        intro rightList ok
        cases rightList <;> cases ok <;> rfl
    | cons head tail ih =>
        intro rightList ok
        cases rightList with
        | nil =>
            simpa [step, List.all₂] using ih [] false
        | cons rightHead rightTail =>
            cases htestValue : test input head rightHead <;>
              simpa [step, List.all₂, htestValue] using
                ih rightTail (ok && test input head rightHead)
  simpa using hspec (left input) (right input) true

/-! ## Primitive-recursive regular-term operations used by rows -/

private theorem nodes_primrec :
    Primrec (RegularTerm.nodes : RegularTerm → List RawNode) :=
  Primrec.fst

private theorem root_primrec :
    Primrec (RegularTerm.root : RegularTerm → ℕ) :=
  Primrec.snd

private theorem nodeAt?_primrec :
    Primrec₂ (RegularTerm.nodeAt? : RegularTerm → ℕ → Option RawNode) := by
  apply Primrec₂.mk
  exact Primrec.list_getElem?.comp
    (nodes_primrec.comp Primrec.fst) Primrec.snd

private theorem rootNode?_primrec :
    Primrec (RegularTerm.rootNode? : RegularTerm → Option RawNode) :=
  nodeAt?_primrec.comp Primrec.id root_primrec

private theorem withRoot_primrec :
    Primrec₂ (RegularTerm.withRoot : RegularTerm → ℕ → RegularTerm) := by
  apply Primrec₂.mk
  exact Primrec.pair (nodes_primrec.comp Primrec.fst) Primrec.snd

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
    Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
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

public theorem instantiate_primrec :
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

/-! ## Unary limits and finite graph equality -/

private def closeReferenceNode
    (input : RegularTerm × ℕ) : RawNode → ℕ
  | .inl 0 => input.1.root
  | _ => input.2

private theorem closeReferenceNode_primrec :
    Primrec₂ closeReferenceNode := by
  apply Primrec₂.mk
  refine (Primrec.sumCasesOn
    (f := fun p : (RegularTerm × ℕ) × RawNode => p.2)
    (g := fun p x => if x = 0 then p.1.1.root else p.1.2)
    (h := fun p _ => p.1.2)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact Primrec.ite
      ((Primrec.eq : PrimrecRel fun x y : ℕ => x = y).comp
        Primrec.snd (Primrec.const 0))
      (root_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  · apply Primrec₂.mk
    exact Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  · intro p
    cases p.2 with
    | inl x => cases x <;> rfl
    | inr app => rfl

private theorem closeUnaryReference_primrec :
    Primrec₂ RegularTerm.closeUnaryReference := by
  apply Primrec₂.mk
  let Input := RegularTerm × ℕ
  have hnode : Primrec fun input : Input => input.1.nodeAt? input.2 :=
    nodeAt?_primrec.comp Primrec.fst Primrec.snd
  refine (Primrec.option_casesOn
    (o := fun input : Input => input.1.nodeAt? input.2)
    (f := fun input => input.2)
    (g := closeReferenceNode)
    hnode Primrec.snd closeReferenceNode_primrec).of_eq ?_
  intro input
  cases h : input.1.nodeAt? input.2 with
  | none => simp [RegularTerm.closeUnaryReference, h]
  | some node =>
      cases node with
      | inl x =>
          cases x <;>
            simp [RegularTerm.closeUnaryReference, closeReferenceNode, h]
      | inr app =>
          simp [RegularTerm.closeUnaryReference, closeReferenceNode, h]

private def closeApplication (context : RegularTerm)
    (app : ℕ × List ℕ) : RawNode :=
  .inr (app.1, app.2.map context.closeUnaryReference)

private theorem closeApplication_primrec :
    Primrec₂ closeApplication := by
  apply Primrec₂.mk
  have hchildren : Primrec fun p : RegularTerm × (ℕ × List ℕ) =>
      p.2.2.map p.1.closeUnaryReference := by
    refine Primrec.list_map (Primrec.snd.comp Primrec.snd) ?_
    apply Primrec₂.mk
    exact closeUnaryReference_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.sumInr.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd) hchildren)

private theorem closeUnaryNode_primrec :
    Primrec₂ RegularTerm.closeUnaryNode := by
  apply Primrec₂.mk
  refine (Primrec.sumCasesOn
    (f := fun p : RegularTerm × RawNode => p.2)
    (g := fun _ x => (Sum.inl x : RawNode))
    (h := fun p app => closeApplication p.1 app)
    Primrec.snd ?_ ?_).of_eq ?_
  · exact Primrec₂.mk (Primrec.sumInl.comp Primrec.snd)
  · apply Primrec₂.mk
    exact closeApplication_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · intro p
    cases p.2 <;> rfl

private theorem unaryLimit_primrec :
    Primrec RegularTerm.unaryLimit := by
  have hnodes : Primrec fun context : RegularTerm =>
      context.nodes.map context.closeUnaryNode := by
    refine Primrec.list_map nodes_primrec ?_
    exact closeUnaryNode_primrec
  have hroot : Primrec fun context : RegularTerm =>
      context.closeUnaryReference context.root :=
    closeUnaryReference_primrec.comp Primrec.id root_primrec
  exact Primrec.pair hnodes hroot

private def nontrivialRootNode : Option RawNode → Bool
  | some (.inl 0) => false
  | _ => true

private theorem nontrivialRootNode_primrec :
    Primrec nontrivialRootNode := by
  refine (Primrec.option_casesOn
    (o := id)
    (f := fun _ => true)
    (g := fun _ node =>
      match node with
      | .inl x => decide (x ≠ 0)
      | .inr _ => true)
    Primrec.id (Primrec.const true) ?_).of_eq ?_
  · apply Primrec₂.mk
    refine (Primrec.sumCasesOn
      (f := fun p : Option RawNode × RawNode => p.2)
      (g := fun _ x => decide (x ≠ 0))
      (h := fun _ _ => true)
      Primrec.snd ?_ (Primrec₂.mk (Primrec.const true))).of_eq ?_
    · apply Primrec₂.mk
      exact (Primrec.eq : PrimrecRel fun x y : ℕ => x = y).not.decide.comp
        Primrec.snd (Primrec.const 0)
    · intro p
      cases p.2 <;> rfl
  · intro root
    cases root with
    | none => rfl
    | some node =>
        cases node with
        | inl x => cases x <;> rfl
        | inr app => rfl

private theorem nontrivialUnaryCode_primrec :
    Primrec RegularTerm.nontrivialUnaryCode :=
  nontrivialRootNode_primrec.comp rootNode?_primrec

private def rawNodeChildren : RawNode → List ℕ
  | .inl _ => []
  | .inr (_, children) => children

private theorem rawNodeChildren_primrec :
    Primrec rawNodeChildren := by
  refine (Primrec.sumCasesOn
    (f := id)
    (g := fun _ (_ : ℕ) => ([] : List ℕ))
    (h := fun _ app => app.2)
    Primrec.id (Primrec₂.mk (Primrec.const []))
    (Primrec₂.mk (Primrec.snd.comp Primrec.snd))).of_eq ?_
  intro node
  cases node <;> rfl

private theorem references_primrec :
    Primrec RegularTerm.references := by
  have hchildren : Primrec fun term : RegularTerm =>
      term.nodes.flatMap fun node => rawNodeChildren node := by
    exact Primrec.list_flatMap nodes_primrec
      (Primrec₂.mk (rawNodeChildren_primrec.comp Primrec.snd))
  exact (Primrec.list_cons.comp root_primrec hchildren).of_eq fun term => by
    rfl

private theorem referencePairs_primrec :
    Primrec₂ RegularTerm.referencePairs := by
  apply Primrec₂.mk
  exact list_product_primrec.comp
    (references_primrec.comp Primrec.fst)
    (references_primrec.comp Primrec.snd)

private def optionRawNodeKind : Option RawNode → ℕ
  | none => 0
  | some (.inl _) => 1
  | some (.inr _) => 2

private def rawNodeKind : RawNode → ℕ
  | .inl _ => 1
  | .inr _ => 2

private theorem rawNodeKind_primrec :
    Primrec rawNodeKind := by
  refine (Primrec.sumCasesOn
    (f := id)
    (g := fun _ (_ : ℕ) => 1)
    (h := fun _ (_ : ℕ × List ℕ) => 2)
    Primrec.id (Primrec₂.mk (Primrec.const 1))
    (Primrec₂.mk (Primrec.const 2))).of_eq ?_
  intro node
  cases node <;> rfl

private theorem optionRawNodeKind_primrec :
    Primrec optionRawNodeKind := by
  refine (Primrec.option_casesOn
    (o := id)
    (f := fun _ => 0)
    (g := fun _ node => rawNodeKind node)
    Primrec.id (Primrec.const 0)
    (Primrec₂.mk (rawNodeKind_primrec.comp Primrec.snd))).of_eq ?_
  intro node
  cases node with
  | none => rfl
  | some node => cases node <;> rfl

private def optionRawVariable : Option RawNode → ℕ
  | some (.inl x) => x
  | _ => 0

private def rawVariable : RawNode → ℕ
  | .inl x => x
  | .inr _ => 0

private theorem rawVariable_primrec :
    Primrec rawVariable := by
  refine (Primrec.sumCasesOn
    (f := id)
    (g := fun _ x => x)
    (h := fun _ (_ : ℕ × List ℕ) => 0)
    Primrec.id (Primrec₂.mk Primrec.snd)
    (Primrec₂.mk (Primrec.const 0))).of_eq ?_
  intro node
  cases node <;> rfl

private theorem optionRawVariable_primrec :
    Primrec optionRawVariable := by
  refine (Primrec.option_casesOn
    (o := id)
    (f := fun _ => 0)
    (g := fun _ node => rawVariable node)
    Primrec.id (Primrec.const 0)
    (Primrec₂.mk (rawVariable_primrec.comp Primrec.snd))).of_eq ?_
  intro node
  cases node with
  | none => rfl
  | some node => cases node <;> rfl

private def optionRawApplication :
    Option RawNode → ℕ × List ℕ
  | some (.inr app) => app
  | _ => (0, [])

private def rawApplication : RawNode → ℕ × List ℕ
  | .inl _ => (0, [])
  | .inr app => app

private theorem rawApplication_primrec :
    Primrec rawApplication := by
  refine (Primrec.sumCasesOn
    (f := id)
    (g := fun _ (_ : ℕ) => (0, ([] : List ℕ)))
    (h := fun _ app => app)
    Primrec.id (Primrec₂.mk (Primrec.const (0, [])))
    (Primrec₂.mk Primrec.snd)).of_eq ?_
  intro node
  cases node <;> rfl

private theorem optionRawApplication_primrec :
    Primrec optionRawApplication := by
  refine (Primrec.option_casesOn
    (o := id)
    (f := fun _ => (0, ([] : List ℕ)))
    (g := fun _ node => rawApplication node)
    Primrec.id (Primrec.const (0, []))
    (Primrec₂.mk (rawApplication_primrec.comp Primrec.snd))).of_eq ?_
  intro node
  cases node with
  | none => rfl
  | some node => cases node <;> rfl

private abbrev ApplicationCompatibilityInput :=
  List (ℕ × ℕ) × (ℕ × List ℕ) × (ℕ × List ℕ)

private def applicationCompatibleCode
    (input : ApplicationCompatibilityInput) : Bool :=
  decide (input.2.1.1 = input.2.2.1) &&
    List.all₂
      (fun left right => decide ((left, right) ∈ input.1))
      input.2.1.2 input.2.2.2

private theorem applicationCompatibleCode_primrec :
    Primrec applicationCompatibleCode := by
  have hsymbols : Primrec fun input : ApplicationCompatibilityInput =>
      decide (input.2.1.1 = input.2.2.1) :=
    Primrec.eq.decide.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hchildren : Primrec fun input : ApplicationCompatibilityInput =>
      List.all₂
        (fun left right => decide ((left, right) ∈ input.1))
        input.2.1.2 input.2.2.2 := by
    apply list_all₂_primrec
      (hleft := Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (hright := Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    show Primrec fun p : ((ApplicationCompatibilityInput × ℕ) × ℕ) =>
      decide ((p.1.2, p.2) ∈ p.1.1.1)
    have hrelation : Primrec fun
        p : ((ApplicationCompatibilityInput × ℕ) × ℕ) => p.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hpair : Primrec fun
        p : ((ApplicationCompatibilityInput × ℕ) × ℕ) =>
          (p.1.2, p.2) :=
      Primrec.pair
        (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact ((list_mem_primrec (Element := ℕ × ℕ)).comp
      hrelation hpair).of_eq fun _ => by simp
  exact Primrec.and.comp hsymbols hchildren

private abbrev RawCompatibilityInput :=
  List (ℕ × ℕ) × Option RawNode × Option RawNode

private theorem rawCompatibleCode_primrec :
    Primrec fun input : RawCompatibilityInput =>
      RegularTerm.rawCompatibleCode input.1 input.2.1 input.2.2 := by
  have hleftKind : Primrec fun input : RawCompatibilityInput =>
      optionRawNodeKind input.2.1 :=
    optionRawNodeKind_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have hrightKind : Primrec fun input : RawCompatibilityInput =>
      optionRawNodeKind input.2.2 :=
    optionRawNodeKind_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  have hsameKind : Primrec fun input : RawCompatibilityInput =>
      decide (optionRawNodeKind input.2.1 =
        optionRawNodeKind input.2.2) :=
    Primrec.eq.decide.comp hleftKind hrightKind
  have hnone : Primrec fun input : RawCompatibilityInput =>
      decide (optionRawNodeKind input.2.1 = 0) :=
    Primrec.eq.decide.comp hleftKind (Primrec.const 0)
  have hvariable : Primrec fun input : RawCompatibilityInput =>
      decide (optionRawNodeKind input.2.1 = 1) :=
    Primrec.eq.decide.comp hleftKind (Primrec.const 1)
  have hvariablesEqual : Primrec fun input : RawCompatibilityInput =>
      decide (optionRawVariable input.2.1 =
        optionRawVariable input.2.2) :=
    Primrec.eq.decide.comp
      (optionRawVariable_primrec.comp
        (Primrec.fst.comp Primrec.snd))
      (optionRawVariable_primrec.comp
        (Primrec.snd.comp Primrec.snd))
  have happlications : Primrec fun input : RawCompatibilityInput =>
      applicationCompatibleCode
        (input.1, optionRawApplication input.2.1,
          optionRawApplication input.2.2) :=
    applicationCompatibleCode_primrec.comp
      (Primrec.pair
        Primrec.fst
        (Primrec.pair
          (optionRawApplication_primrec.comp
            (Primrec.fst.comp Primrec.snd))
          (optionRawApplication_primrec.comp
            (Primrec.snd.comp Primrec.snd))))
  have hcode : Primrec fun input : RawCompatibilityInput =>
      bif decide (optionRawNodeKind input.2.1 =
          optionRawNodeKind input.2.2) then
        bif decide (optionRawNodeKind input.2.1 = 0) then true
        else bif decide (optionRawNodeKind input.2.1 = 1) then
          decide (optionRawVariable input.2.1 =
            optionRawVariable input.2.2)
        else applicationCompatibleCode
          (input.1, optionRawApplication input.2.1,
            optionRawApplication input.2.2)
      else false :=
    Primrec.cond hsameKind
      (Primrec.cond hnone (Primrec.const true)
        (Primrec.cond hvariable hvariablesEqual happlications))
      (Primrec.const false)
  apply hcode.of_eq
  intro input
  rcases input with ⟨relation, left, right⟩
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right =>
          cases right <;> rfl
  | some left =>
      cases right with
      | none =>
          cases left <;> rfl
      | some right =>
          cases left <;> cases right <;>
            simp [RegularTerm.rawCompatibleCode, optionRawNodeKind,
              optionRawVariable, optionRawApplication,
              applicationCompatibleCode]

private abbrev NodeCompatibilityInput :=
  RegularTerm × RegularTerm × List (ℕ × ℕ) × ℕ × ℕ

private theorem nodeCompatibleCode_primrec :
    Primrec fun input : NodeCompatibilityInput =>
      input.1.nodeCompatibleCode input.2.1 input.2.2.1
        input.2.2.2.1 input.2.2.2.2 := by
  have hrelation : Primrec fun input : NodeCompatibilityInput =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hleftNode : Primrec fun input : NodeCompatibilityInput =>
      input.1.nodeAt? input.2.2.2.1 :=
    nodeAt?_primrec.comp Primrec.fst
      (Primrec.fst.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hrightNode : Primrec fun input : NodeCompatibilityInput =>
      input.2.1.nodeAt? input.2.2.2.2 :=
    nodeAt?_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact rawCompatibleCode_primrec.comp
    (Primrec.pair hrelation (Primrec.pair hleftNode hrightNode))

private abbrev BisimulationInput :=
  RegularTerm × RegularTerm × List (ℕ × ℕ)

private theorem bisimulationCode_primrec :
    Primrec fun input : BisimulationInput =>
      input.1.bisimulationCode input.2.1 input.2.2 := by
  apply list_all_primrec
    (hitems := Primrec.snd.comp Primrec.snd)
  apply Primrec₂.mk
  let RowInput := BisimulationInput × (ℕ × ℕ)
  have hleft : Primrec fun input : RowInput => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hright : Primrec fun input : RowInput => input.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hrelation : Primrec fun input : RowInput => input.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec fun input : RowInput => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hj : Primrec fun input : RowInput => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  exact nodeCompatibleCode_primrec.comp
    (Primrec.pair hleft
      (Primrec.pair hright
        (Primrec.pair hrelation (Primrec.pair hi hj))))

/-- The finite graph-unfolding-equivalence test used by certificate rows is
primitive recursive. -/
public theorem unfoldingEquivalentCode_primrec :
    Primrec₂ RegularTerm.unfoldingEquivalentCode := by
  apply Primrec₂.mk
  let Input := RegularTerm × RegularTerm
  have hpairs : Primrec fun input : Input =>
      input.1.referencePairs input.2 :=
    referencePairs_primrec.comp Primrec.fst Primrec.snd
  have hrelations : Primrec fun input : Input =>
      (input.1.referencePairs input.2).sublists := by
    have hreverse : Primrec₂ fun (_ : Input)
        (relation : List (ℕ × ℕ)) => relation.reverse :=
      Primrec₂.mk (Primrec.list_reverse.comp Primrec.snd)
    exact (Primrec.list_map
      (list_sublists_primrec.comp
        (Primrec.list_reverse.comp hpairs))
      hreverse).of_eq fun input =>
        (List.sublists_eq_sublists'
          (input.1.referencePairs input.2)).symm
  have htest : Primrec₂ fun (input : Input)
      (relation : List (ℕ × ℕ)) =>
      decide ((input.1.root, input.2.root) ∈ relation) &&
        input.1.bisimulationCode input.2 relation := by
    apply Primrec₂.mk
    have hrootPair : Primrec fun p : Input × List (ℕ × ℕ) =>
        (p.1.1.root, p.1.2.root) :=
      Primrec.pair
        (root_primrec.comp (Primrec.fst.comp Primrec.fst))
        (root_primrec.comp (Primrec.snd.comp Primrec.fst))
    have hrootMem : Primrec fun p : Input × List (ℕ × ℕ) =>
        decide ((p.1.1.root, p.1.2.root) ∈ p.2) :=
      ((list_mem_primrec (Element := ℕ × ℕ)).comp
        Primrec.snd hrootPair).of_eq fun _ => by simp
    exact Primrec.and.comp hrootMem
      (bisimulationCode_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.pair
            (Primrec.snd.comp Primrec.fst)
            Primrec.snd)))
  exact list_any_primrec hrelations htest

/-! ## Structural checks and one-step trace agreement -/

private abbrev NodeWellFormedInput :=
  List ℕ × ℕ × ℕ × RawNode

private def applicationWellFormedCode
    (input : List ℕ × ℕ × (ℕ × List ℕ)) : Bool :=
  match input.1[input.2.2.1]? with
  | none => false
  | some rank =>
      decide (input.2.2.2.length = rank) &&
        input.2.2.2.all fun child => decide (child < input.2.1)

private theorem applicationWellFormedCode_primrec :
    Primrec applicationWellFormedCode := by
  let Input := List ℕ × ℕ × (ℕ × List ℕ)
  have hrank : Primrec fun input : Input =>
      input.1[input.2.2.1]? :=
    Primrec.list_getElem?.comp Primrec.fst
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hchildrenBound : Primrec fun input : Input =>
      input.2.2.2.all fun child => decide (child < input.2.1) := by
    apply list_all_primrec
      (hitems := Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    apply Primrec₂.mk
    exact Primrec.nat_lt.decide.comp Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  refine (Primrec.option_casesOn
    (o := fun input : Input => input.1[input.2.2.1]?)
    (f := fun _ => false)
    (g := fun input rank =>
      decide (input.2.2.2.length = rank) &&
        input.2.2.2.all fun child => decide (child < input.2.1))
    hrank (Primrec.const false) ?_).of_eq ?_
  · apply Primrec₂.mk
    exact Primrec.and.comp
      (Primrec.eq.decide.comp
        (Primrec.list_length.comp
          (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.fst))))
        Primrec.snd)
      (hchildrenBound.comp Primrec.fst)
  · intro input
    cases h : input.1[input.2.2.1]? <;>
      simp [applicationWellFormedCode, h]

private theorem nodeWellFormedCode_primrec :
    Primrec fun input : NodeWellFormedInput =>
      RegularTerm.nodeWellFormedCode input.1 input.2.1 input.2.2.1
        input.2.2.2 := by
  refine (Primrec.sumCasesOn
    (f := fun input : NodeWellFormedInput => input.2.2.2)
    (g := fun input x => decide (x < input.2.1))
    (h := fun input app =>
      applicationWellFormedCode (input.1, input.2.2.1, app))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact Primrec.nat_lt.decide.comp Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  · apply Primrec₂.mk
    exact applicationWellFormedCode_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          Primrec.snd))
  · intro input
    cases input.2.2.2 <;> rfl

/-- Structural well-formedness of a regular-term graph is primitive recursive. -/
public theorem wellFormedCode_primrec :
    Primrec fun input : List ℕ × ℕ × RegularTerm =>
      input.2.2.wellFormedCode input.1 input.2.1 := by
  let Input := List ℕ × ℕ × RegularTerm
  have hnodeCount : Primrec fun input : Input =>
      input.2.2.nodes.length :=
    Primrec.list_length.comp
      (nodes_primrec.comp (Primrec.snd.comp Primrec.snd))
  have hrootBound : Primrec fun input : Input =>
      decide (input.2.2.root < input.2.2.nodes.length) :=
    Primrec.nat_lt.decide.comp
      (root_primrec.comp (Primrec.snd.comp Primrec.snd))
      hnodeCount
  have hnodes : Primrec fun input : Input =>
      input.2.2.nodes.all
        (RegularTerm.nodeWellFormedCode input.1 input.2.1
          input.2.2.nodes.length) := by
    apply list_all_primrec
      (hitems := nodes_primrec.comp (Primrec.snd.comp Primrec.snd))
    apply Primrec₂.mk
    exact nodeWellFormedCode_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (hnodeCount.comp Primrec.fst)
            Primrec.snd)))
  exact Primrec.and.comp hrootBound hnodes

private theorem ranks_primrec :
    Primrec (ranks : EncodedFirstOrderGrammar Action → List ℕ) :=
  Primrec.fst

private theorem rawRules_primrec :
    Primrec (rawRules : EncodedFirstOrderGrammar Action →
      List (RawRule Action)) :=
  Primrec.snd

private theorem rawRuleAction_primrec :
    Primrec (RawRule.action : RawRule Action → Action) :=
  Primrec.fst.comp Primrec.snd

private theorem ordinaryCandidateLabels_primrec :
    Primrec fun g : EncodedFirstOrderGrammar Action =>
      g.rawRules.map fun rule => (Sum.inl rule.action : Label Action) := by
  apply Primrec.list_map rawRules_primrec
  apply Primrec₂.mk
  exact Primrec.sumInl.comp
    (rawRuleAction_primrec.comp Primrec.snd)

private def privateRootLabels (root : Option RawNode) :
    List (Label Action) :=
  match root with
  | some (.inl x) => [.inr x]
  | _ => []

private def privateNodeLabels : RawNode → List (Label Action)
  | .inl x => [.inr x]
  | .inr _ => []

private theorem privateNodeLabels_primrec :
    Primrec (privateNodeLabels (Action := Action)) := by
  refine (Primrec.sumCasesOn
    (f := id)
    (g := fun _ x => [(Sum.inr x : Label Action)])
    (h := fun _ (_ : ℕ × List ℕ) => [])
    Primrec.id ?_ (Primrec₂.mk (Primrec.const []))).of_eq ?_
  · apply Primrec₂.mk
    exact Primrec.list_cons.comp
      (Primrec.sumInr.comp Primrec.snd)
      (Primrec.const [])
  · intro node
    cases node <;> rfl

private theorem privateRootLabels_primrec :
    Primrec (privateRootLabels (Action := Action)) := by
  refine (Primrec.option_casesOn
    (o := id)
    (f := fun _ => [])
    (g := fun _ node => privateNodeLabels node)
    Primrec.id (Primrec.const [])
    (Primrec₂.mk
      (privateNodeLabels_primrec.comp Primrec.snd))).of_eq ?_
  intro root
  cases root with
  | none => rfl
  | some node => cases node <;> rfl

private theorem candidateLabels_primrec :
    Primrec₂ (EncodedFirstOrderGrammar.candidateLabels (Action := Action)) := by
  apply Primrec₂.mk
  exact Primrec.list_append.comp
    (ordinaryCandidateLabels_primrec.comp Primrec.fst)
    (privateRootLabels_primrec.comp
      (rootNode?_primrec.comp Primrec.snd))

private theorem enabledLabels_primrec :
    Primrec₂ (EncodedFirstOrderGrammar.enabledLabels (Action := Action)) := by
  apply Primrec₂.mk
  let Input := EncodedFirstOrderGrammar Action × RegularTerm
  have hcandidates : Primrec fun input : Input =>
      input.1.candidateLabels input.2 :=
    candidateLabels_primrec.comp Primrec.fst Primrec.snd
  have hdedup : Primrec fun input : Input =>
      (input.1.candidateLabels input.2).dedup :=
    list_dedup_primrec.comp hcandidates
  have htest : Primrec₂ fun (input : Input) (label : Label Action) =>
      (input.1.step? label input.2).isSome := by
    apply Primrec₂.mk
    exact Primrec.option_isSome.comp
      (step?_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            Primrec.snd)
          (Primrec.snd.comp Primrec.fst)))
  exact list_filter_primrec hdedup htest

private def sameOptionPresence {Element : Type}
    (left right : Option Element) : Bool :=
  left.isSome == right.isSome

private theorem sameOptionPresence_primrec
    {Element : Type} [Primcodable Element] :
    Primrec₂ (sameOptionPresence : Option Element → Option Element → Bool) := by
  apply Primrec₂.mk
  exact Primrec.beq.comp
    (Primrec.option_isSome.comp Primrec.fst)
    (Primrec.option_isSome.comp Primrec.snd)

public abbrev TraceApproxOneInput :=
  EncodedFirstOrderGrammar Action × RegularTerm × RegularTerm

/-- The only trace approximant queried by certificate rows, depth one, is
primitive recursive. -/
public theorem traceApproxOneCode_primrec :
    Primrec fun input : TraceApproxOneInput (Action := Action) =>
      input.1.traceApproxCode 1 input.2.1 input.2.2 := by
  have hlabels : Primrec fun input : TraceApproxOneInput (Action := Action) =>
      input.1.candidateLabels input.2.1 ++
        input.1.candidateLabels input.2.2 :=
    Primrec.list_append.comp
      (candidateLabels_primrec.comp Primrec.fst
        (Primrec.fst.comp Primrec.snd))
      (candidateLabels_primrec.comp Primrec.fst
        (Primrec.snd.comp Primrec.snd))
  have htest : Primrec₂ fun
      (input : TraceApproxOneInput (Action := Action))
      (label : Label Action) =>
      sameOptionPresence (input.1.step? label input.2.1)
        (input.1.step? label input.2.2) := by
    apply Primrec₂.mk
    let TestInput :=
      TraceApproxOneInput (Action := Action) × Label Action
    have hleft : Primrec fun p : TestInput =>
        p.1.1.step? p.2 p.1.2.1 :=
      step?_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    have hright : Primrec fun p : TestInput =>
        p.1.1.step? p.2 p.1.2.2 :=
      step?_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    exact sameOptionPresence_primrec.comp hleft hright
  have hall : Primrec fun input :
      TraceApproxOneInput (Action := Action) =>
      (input.1.candidateLabels input.2.1 ++
        input.1.candidateLabels input.2.2).all fun label =>
          sameOptionPresence (input.1.step? label input.2.1)
            (input.1.step? label input.2.2) :=
    list_all_primrec hlabels htest
  apply hall.of_eq
  intro input
  unfold traceApproxCode sameOptionPresence
  apply congrArg (List.all
    (input.1.candidateLabels input.2.1 ++
      input.1.candidateLabels input.2.2))
  funext label
  cases input.1.step? label input.2.1 <;>
    cases input.1.step? label input.2.2 <;> rfl

/-! ## Primitive-recursive certificate-side conditions -/

private theorem lookupPrior_primrec :
    Primrec₂ (lookupPrior :
      List (CertificateJudgment Action) → ℕ →
        Option (CertificateJudgment Action)) := by
  apply Primrec₂.mk
  exact Primrec.list_getElem?.comp
    (Primrec.list_reverse.comp Primrec.fst) Primrec.snd

private theorem list_mapM_option_primrec
    {Input Source Target : Type}
    [Primcodable Input] [Primcodable Source] [Primcodable Target]
    {items : Input → List Source}
    {transform : Input → Source → Option Target}
    (hitems : Primrec items) (htransform : Primrec₂ transform) :
    Primrec fun input => (items input).mapM (transform input) := by
  have hstep : Primrec₂ fun (input : Input)
      (state : Source × Option (List Target)) =>
      (transform input state.1).bind fun head =>
        state.2.map fun tail => head :: tail := by
    apply Primrec₂.mk
    let StepInput := Input × (Source × Option (List Target))
    have hhead : Primrec fun p : StepInput =>
        transform p.1 p.2.1 :=
      htransform.comp Primrec.fst
        (Primrec.fst.comp Primrec.snd)
    have htail : Primrec₂ fun (p : StepInput) (head : Target) =>
        p.2.2.map fun tail => head :: tail := by
      apply Primrec₂.mk
      exact Primrec.option_map
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec₂.mk (Primrec.list_cons.comp
          (Primrec.snd.comp Primrec.fst)
          Primrec.snd))
    exact Primrec.option_bind hhead htail
  apply (Primrec.list_foldr hitems (Primrec.const (some [])) hstep).of_eq
  intro input
  induction items input with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mapM_cons, List.foldr_cons]
      cases hhead : transform input head with
      | none => simp [hhead]
      | some value =>
          cases htail : tail.mapM (transform input) <;>
            simp [hhead, ih, htail]

private theorem lookupPriorRefs_primrec :
    Primrec fun input :
        List (CertificateJudgment Action) × List ℕ =>
      input.2.mapM (lookupPrior input.1) := by
  apply list_mapM_option_primrec Primrec.snd
  apply Primrec₂.mk
  exact lookupPrior_primrec.comp
    (Primrec.fst.comp Primrec.fst) Primrec.snd

private abbrev GroundPairInput :=
  EncodedFirstOrderGrammar Action × RegularTerm × RegularTerm

private theorem groundPairCode_primrec :
    Primrec fun input : GroundPairInput (Action := Action) =>
      input.1.groundPairCode input.2.1 input.2.2 := by
  exact Primrec.and.comp
    (RegularTerm.groundCode_primrec.comp
      (ranks_primrec.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (RegularTerm.groundCode_primrec.comp
      (ranks_primrec.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

private theorem groundArgumentsCode_primrec :
    Primrec₂ (EncodedFirstOrderGrammar.groundArgumentsCode
      (Action := Action)) := by
  apply Primrec₂.mk
  let Input := EncodedFirstOrderGrammar Action × List RegularTerm
  apply list_all_primrec
    (hitems := Primrec.snd)
  apply Primrec₂.mk
  exact RegularTerm.groundCode_primrec.comp
    (ranks_primrec.comp (Primrec.fst.comp Primrec.fst))
    Primrec.snd

public theorem basisPairWellFormedCode_primrec :
    Primrec₂ (EncodedFirstOrderGrammar.basisPairWellFormedCode
      (Action := Action)) := by
  apply Primrec₂.mk
  let Input := EncodedFirstOrderGrammar Action × BasisPair
  have hleft : Primrec fun input : Input =>
      input.2.left.wellFormedCode input.1.ranks input.2.arity :=
    wellFormedCode_primrec.comp
      (Primrec.pair
        (ranks_primrec.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hright : Primrec fun input : Input =>
      input.2.right.wellFormedCode input.1.ranks input.2.arity :=
    wellFormedCode_primrec.comp
      (Primrec.pair
        (ranks_primrec.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec.and.comp hleft hright

private theorem checkCondition_primrec :
    Primrec (checkCondition : Bool → Option Unit) := by
  exact (Primrec.cond Primrec.id
    (Primrec.const (some ()))
    (Primrec.const none)).of_eq fun condition => by
      cases condition <;> rfl

private abbrev LimitConditionsInput :=
  EncodedFirstOrderGrammar Action ×
    ((List (Label Action) × List (Label Action)) ×
      ((RegularTerm × RegularTerm) ×
        ((RegularTerm × RegularTerm) ×
          (RegularTerm × RegularTerm × RegularTerm))))

private theorem limitRowConditionsCode_primrec :
    Primrec fun input : LimitConditionsInput (Action := Action) =>
      input.1.limitRowConditionsCode
        input.2.1.1 input.2.1.2
        input.2.2.1.1 input.2.2.1.2
        input.2.2.2.1.1 input.2.2.2.1.2
        input.2.2.2.2.1 input.2.2.2.2.2.1
        input.2.2.2.2.2.2 := by
  let Input := LimitConditionsInput (Action := Action)
  have hg : Primrec fun input : Input => input.1 :=
    Primrec.fst
  have hword : Primrec fun input : Input => input.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hshorterWord : Primrec fun input : Input => input.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have houterLeft : Primrec fun input : Input => input.2.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have houterRight : Primrec fun input : Input => input.2.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hshorterLeft : Primrec fun input : Input => input.2.2.2.1.1 :=
    Primrec.fst.comp
      (Primrec.fst.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hshorterRight : Primrec fun input : Input => input.2.2.2.1.2 :=
    Primrec.snd.comp
      (Primrec.fst.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have houterContext : Primrec fun input : Input => input.2.2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hreplacementContext : Primrec fun input : Input =>
      input.2.2.2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp
        (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hfocus : Primrec fun input : Input => input.2.2.2.2.2.2 :=
    Primrec.snd.comp
      (Primrec.snd.comp
        (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have houterWellFormed : Primrec fun input : Input =>
      input.2.2.2.2.1.wellFormedCode input.1.ranks 1 :=
    wellFormedCode_primrec.comp
      (Primrec.pair
        (ranks_primrec.comp hg)
        (Primrec.pair (Primrec.const 1) houterContext))
  have hreplacementWellFormed : Primrec fun input : Input =>
      input.2.2.2.2.2.1.wellFormedCode input.1.ranks 1 :=
    wellFormedCode_primrec.comp
      (Primrec.pair
        (ranks_primrec.comp hg)
        (Primrec.pair (Primrec.const 1) hreplacementContext))
  have hfocusGround : Primrec fun input : Input =>
      input.2.2.2.2.2.2.groundCode input.1.ranks :=
    RegularTerm.groundCode_primrec.comp
      (ranks_primrec.comp hg) hfocus
  have hnontrivial : Primrec fun input : Input =>
      input.2.2.2.2.2.1.nontrivialUnaryCode :=
    nontrivialUnaryCode_primrec.comp hreplacementContext
  have hlength : Primrec fun input : Input =>
      decide (input.2.1.2.length < input.2.1.1.length) :=
    Primrec.nat_lt.decide.comp
      (Primrec.list_length.comp hshorterWord)
      (Primrec.list_length.comp hword)
  have hfocusSingleton : Primrec fun input : Input =>
      [input.2.2.2.2.2.2] :=
    Primrec.list_cons.comp hfocus (Primrec.const [])
  have houterFocus : Primrec fun input : Input =>
      input.2.2.2.2.1.instantiate [input.2.2.2.2.2.2] :=
    instantiate_primrec.comp houterContext hfocusSingleton
  have hreplacementFocus : Primrec fun input : Input =>
      input.2.2.2.2.2.1.instantiate [input.2.2.2.2.2.2] :=
    instantiate_primrec.comp hreplacementContext hfocusSingleton
  have houterMatch : Primrec fun input : Input =>
      input.2.2.1.1.unfoldingEquivalentCode
        (input.2.2.2.2.1.instantiate [input.2.2.2.2.2.2]) :=
    unfoldingEquivalentCode_primrec.comp houterLeft houterFocus
  have hshorterLeftMatch : Primrec fun input : Input =>
      input.2.2.2.1.1.unfoldingEquivalentCode input.2.2.2.2.2.2 :=
    unfoldingEquivalentCode_primrec.comp hshorterLeft hfocus
  have hshorterRightMatch : Primrec fun input : Input =>
      input.2.2.2.1.2.unfoldingEquivalentCode
        (input.2.2.2.2.2.1.instantiate [input.2.2.2.2.2.2]) :=
    unfoldingEquivalentCode_primrec.comp hshorterRight hreplacementFocus
  have hlimit : Primrec fun input : Input =>
      input.2.2.2.2.2.1.unaryLimit :=
    unaryLimit_primrec.comp hreplacementContext
  have hlimitSingleton : Primrec fun input : Input =>
      [input.2.2.2.2.2.1.unaryLimit] :=
    Primrec.list_cons.comp hlimit (Primrec.const [])
  have hresult : Primrec fun input : Input =>
      input.2.2.2.2.1.instantiate
        [input.2.2.2.2.2.1.unaryLimit] :=
    instantiate_primrec.comp houterContext hlimitSingleton
  have hgroundResult : Primrec fun input : Input =>
      input.1.groundPairCode
        (input.2.2.2.2.1.instantiate
          [input.2.2.2.2.2.1.unaryLimit])
        input.2.2.1.2 :=
    groundPairCode_primrec.comp
      (Primrec.pair hg (Primrec.pair hresult houterRight))
  have h₁ := Primrec.and.comp houterWellFormed hreplacementWellFormed
  have h₂ := Primrec.and.comp h₁ hfocusGround
  have h₃ := Primrec.and.comp h₂ hnontrivial
  have h₄ := Primrec.and.comp h₃ hlength
  have h₅ := Primrec.and.comp h₄ houterMatch
  have h₆ := Primrec.and.comp h₅ hshorterLeftMatch
  have h₇ := Primrec.and.comp h₆ hshorterRightMatch
  exact Primrec.and.comp h₇ hgroundResult

private abbrev BasisConditionsInput :=
  EncodedFirstOrderGrammar Action ×
    (List (Label Action) ×
      ((RegularTerm × RegularTerm) × (BasisPair × List RegularTerm)))

private theorem basisRowConditionsCode_primrec :
    Primrec fun input : BasisConditionsInput (Action := Action) =>
      input.1.basisRowConditionsCode input.2.1
        input.2.2.1.1 input.2.2.1.2
        input.2.2.2.1 input.2.2.2.2 := by
  let Input := BasisConditionsInput (Action := Action)
  have hg : Primrec fun input : Input => input.1 := Primrec.fst
  have hword : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hleft : Primrec fun input : Input => input.2.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hright : Primrec fun input : Input => input.2.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hschema : Primrec fun input : Input => input.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have harguments : Primrec fun input : Input => input.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hnonempty : Primrec fun input : Input =>
      decide (input.2.1 ≠ []) := by
    have hcode : Primrec fun input : Input =>
        !(input.2.1.length == 0) :=
      Primrec.not.comp
        (Primrec.beq.comp
          (Primrec.list_length.comp hword)
          (Primrec.const 0))
    apply hcode.of_eq
    intro input
    cases input.2.1 <;> simp
  have hschemaWellFormed : Primrec fun input : Input =>
      input.1.basisPairWellFormedCode input.2.2.2.1 :=
    basisPairWellFormedCode_primrec.comp hg hschema
  have hargumentCount : Primrec fun input : Input =>
      decide (input.2.2.2.2.length = input.2.2.2.1.arity) :=
    Primrec.eq.decide.comp
      (Primrec.list_length.comp harguments)
      (Primrec.fst.comp hschema)
  have hargumentsGround : Primrec fun input : Input =>
      input.1.groundArgumentsCode input.2.2.2.2 :=
    groundArgumentsCode_primrec.comp hg harguments
  have hinstLeft : Primrec fun input : Input =>
      input.2.2.2.1.left.instantiate input.2.2.2.2 :=
    instantiate_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp hschema)) harguments
  have hinstRight : Primrec fun input : Input =>
      input.2.2.2.1.right.instantiate input.2.2.2.2 :=
    instantiate_primrec.comp
      (Primrec.snd.comp (Primrec.snd.comp hschema)) harguments
  have hleftMatch : Primrec fun input : Input =>
      input.2.2.1.1.unfoldingEquivalentCode
        (input.2.2.2.1.left.instantiate input.2.2.2.2) :=
    unfoldingEquivalentCode_primrec.comp hleft hinstLeft
  have hrightMatch : Primrec fun input : Input =>
      input.2.2.1.2.unfoldingEquivalentCode
        (input.2.2.2.1.right.instantiate input.2.2.2.2) :=
    unfoldingEquivalentCode_primrec.comp hright hinstRight
  have h₁ := Primrec.and.comp hnonempty hschemaWellFormed
  have h₂ := Primrec.and.comp h₁ hargumentCount
  have h₃ := Primrec.and.comp h₂ hargumentsGround
  have h₄ := Primrec.and.comp h₃ hleftMatch
  exact Primrec.and.comp h₄ hrightMatch

private abbrev ProgressionConditionsInput :=
  EncodedFirstOrderGrammar Action ×
    (List (CertificateJudgment Action) ×
      (List (Label Action) × (RegularTerm × List ℕ)))

private theorem progressionChildrenCode_primrec :
    Primrec fun input : ProgressionConditionsInput (Action := Action) =>
      input.1.progressionChildrenCode input.2.1 input.2.2.1
        input.2.2.2.1 input.2.2.2.2 := by
  let Input := ProgressionConditionsInput (Action := Action)
  have hg : Primrec fun input : Input => input.1 := Primrec.fst
  have hprior : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hword : Primrec fun input : Input => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hleft : Primrec fun input : Input => input.2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrefs : Primrec fun input : Input => input.2.2.2.2 :=
    Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  let lookupResults := fun input : Input =>
    input.2.2.2.2.mapM (lookupPrior input.2.1)
  have hlookups : Primrec lookupResults :=
    lookupPriorRefs_primrec.comp
      (Primrec.pair hprior hrefs)
  have hlabels : Primrec fun input : Input =>
      input.1.enabledLabels input.2.2.2.1 :=
    enabledLabels_primrec.comp hg hleft
  have htargets : Primrec fun input : Input =>
      (input.1.enabledLabels input.2.2.2.1).map fun label =>
        CertificateJudgment.nop (input.2.2.1 ++ [label]) := by
    apply Primrec.list_map hlabels
    apply Primrec₂.mk
    have htargetWord : Primrec fun p : Input × Label Action =>
        p.1.2.2.1 ++ [p.2] :=
      Primrec.list_append.comp
        (hword.comp Primrec.fst)
        (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    exact judgmentNop_primrec.comp htargetWord
  let targetResults := fun input : Input =>
    some ((input.1.enabledLabels input.2.2.2.1).map fun label =>
      CertificateJudgment.nop (input.2.2.1 ++ [label]))
  have htargetOption : Primrec targetResults :=
    Primrec.option_some.comp htargets
  have hencodedEquality : Primrec fun input : Input =>
      decide (Encodable.encode (lookupResults input) =
        Encodable.encode (targetResults input)) :=
    Primrec.eq.decide.comp
      (Primrec.encode.comp hlookups)
      (Primrec.encode.comp htargetOption)
  apply hencodedEquality.of_eq
  intro input
  change decide (Encodable.encode (lookupResults input) =
      Encodable.encode (targetResults input)) =
    decide (lookupResults input = targetResults input)
  by_cases h : lookupResults input = targetResults input
  · have hencode : Encodable.encode (lookupResults input) =
        Encodable.encode (targetResults input) :=
      congrArg Encodable.encode h
    simp [h, hencode]
  · have hencode : Encodable.encode (lookupResults input) ≠
        Encodable.encode (targetResults input) :=
      fun heq => h (Encodable.encode_injective heq)
    simp [h, hencode]

/-! ## Primitive-recursive local row checking -/

public abbrev CertificateCheckContext (Action : Type) :=
  EncodedFirstOrderGrammar Action ×
    ((RegularTerm × RegularTerm) ×
      (List BasisPair × List (CertificateJudgment Action)))

private abbrev PairJudgmentData (Action : Type) :=
  List (Label Action) × RegularTerm × RegularTerm

private def judgmentPairData? :
    CertificateJudgment Action → Option (PairJudgmentData Action)
  | .pair word left right => some (word, left, right)
  | .nop _ => none
  | .fail => none

private theorem judgmentPairData?_primrec :
    Primrec (judgmentPairData? (Action := Action)) := by
  have hcode : Primrec (certificateJudgmentEquiv Action) :=
    Primrec.of_equiv
  refine (Primrec.sumCasesOn
    (f := certificateJudgmentEquiv Action)
    (g := fun _ data => some data)
    (h := fun _ _ => none)
    hcode
    (Primrec₂.mk (Primrec.option_some.comp Primrec.snd))
    (Primrec₂.mk (Primrec.const none))).of_eq ?_
  intro judgment
  cases judgment <;> rfl

private theorem checkContextGrammar_primrec :
    Primrec fun context : CertificateCheckContext Action => context.1 :=
  Primrec.fst

private theorem checkContextInitialLeft_primrec :
    Primrec fun context : CertificateCheckContext Action =>
      context.2.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.snd)

private theorem checkContextInitialRight_primrec :
    Primrec fun context : CertificateCheckContext Action =>
      context.2.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)

private theorem checkContextBasis_primrec :
    Primrec fun context : CertificateCheckContext Action =>
      context.2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem checkContextPrior_primrec :
    Primrec fun context : CertificateCheckContext Action =>
      context.2.2.2 :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

private def lookupPair?
    (context : CertificateCheckContext Action) (back : ℕ) :
    Option (PairJudgmentData Action) :=
  (lookupPrior context.2.2.2 back).bind judgmentPairData?

private theorem lookupPair?_primrec :
    Primrec₂ (lookupPair? (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × ℕ
  have hlookup : Primrec fun input : Input =>
      lookupPrior input.1.2.2.2 input.2 :=
    lookupPrior_primrec.comp
      (checkContextPrior_primrec.comp Primrec.fst)
      Primrec.snd
  exact Primrec.option_bind hlookup
    (Primrec₂.mk
      (judgmentPairData?_primrec.comp Primrec.snd))

private def checkAxiomRow
    (context : CertificateCheckContext Action) :
    Option (CertificateJudgment Action) :=
  context.1.checkCertificateRow context.2.1.1 context.2.1.2
    context.2.2.1 context.2.2.2 .axiom

private theorem checkAxiomRow_primrec :
    Primrec (checkAxiomRow (Action := Action)) := by
  have hground : Primrec fun context : CertificateCheckContext Action =>
      context.1.groundPairCode context.2.1.1 context.2.1.2 :=
    groundPairCode_primrec.comp
      (Primrec.pair checkContextGrammar_primrec
        (Primrec.pair checkContextInitialLeft_primrec
          checkContextInitialRight_primrec))
  have hpair : Primrec fun context : CertificateCheckContext Action =>
      (CertificateJudgment.pair [] context.2.1.1 context.2.1.2 :
        CertificateJudgment Action) :=
    judgmentPair_primrec.comp
      (Primrec.pair (Primrec.const [])
        (Primrec.pair checkContextInitialLeft_primrec
          checkContextInitialRight_primrec))
  exact (Primrec.cond hground
    (Primrec.option_some.comp hpair)
    (Primrec.const none)).of_eq fun context => by
      unfold checkAxiomRow checkCertificateRow checkCondition
      cases context.1.groundPairCode context.2.1.1 context.2.1.2 <;> rfl

private def checkSymmetryRow
    (context : CertificateCheckContext Action) (pairRef : ℕ) :
    Option (CertificateJudgment Action) :=
  context.1.checkCertificateRow context.2.1.1 context.2.1.2
    context.2.2.1 context.2.2.2 (.symmetry pairRef)

private theorem checkSymmetryRow_primrec :
    Primrec₂ (checkSymmetryRow (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × ℕ
  have hpair : Primrec fun input : Input =>
      lookupPair? input.1 input.2 :=
    lookupPair?_primrec.comp Primrec.fst Primrec.snd
  have hswap : Primrec₂ fun (_ : Input)
      (data : PairJudgmentData Action) =>
      (CertificateJudgment.pair data.1 data.2.2 data.2.1 :
        CertificateJudgment Action) := by
    apply Primrec₂.mk
    exact judgmentPair_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.snd)
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.option_bind hpair
    (Primrec₂.option_some_iff.2 hswap)).of_eq fun input => by
      unfold checkSymmetryRow checkCertificateRow lookupPair?
      cases hlookup : lookupPrior input.1.2.2.2 input.2 with
      | none => simp [hlookup]
      | some judgment =>
          cases judgment <;> simp [hlookup, judgmentPairData?]

private def checkRejectionRow
    (context : CertificateCheckContext Action) (pairRef : ℕ) :
    Option (CertificateJudgment Action) :=
  context.1.checkCertificateRow context.2.1.1 context.2.1.2
    context.2.2.1 context.2.2.2 (.rejection pairRef)

private theorem checkRejectionRow_primrec :
    Primrec₂ (checkRejectionRow (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × ℕ
  have hpair : Primrec fun input : Input =>
      lookupPair? input.1 input.2 :=
    lookupPair?_primrec.comp Primrec.fst Primrec.snd
  have hprocess : Primrec₂ fun (input : Input)
      (data : PairJudgmentData Action) =>
      if !input.1.1.traceApproxCode 1 data.2.1 data.2.2 then
        some (CertificateJudgment.fail : CertificateJudgment Action)
      else none := by
    apply Primrec₂.mk
    let ProcessInput := Input × PairJudgmentData Action
    have hg : Primrec fun p : ProcessInput => p.1.1.1 :=
      checkContextGrammar_primrec.comp
        (Primrec.fst.comp Primrec.fst)
    have hleft : Primrec fun p : ProcessInput => p.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have happrox : Primrec fun p : ProcessInput =>
        p.1.1.1.traceApproxCode 1 p.2.2.1 p.2.2.2 :=
      traceApproxOneCode_primrec.comp
        (Primrec.pair hg
          (Primrec.pair hleft
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    exact (Primrec.cond (Primrec.not.comp happrox)
      (Primrec.option_some.comp
        (judgmentFail_primrec.comp (Primrec.const ())))
      (Primrec.const none)).of_eq fun p => by
        cases p.1.1.1.traceApproxCode 1 p.2.2.1 p.2.2.2 <;> rfl
  exact (Primrec.option_bind hpair hprocess).of_eq fun input => by
    unfold checkRejectionRow checkCertificateRow lookupPair?
    cases hlookup : lookupPrior input.1.2.2.2 input.2 with
    | none => simp [hlookup]
    | some judgment =>
        cases judgment with
        | nop word => simp [hlookup, judgmentPairData?]
        | fail => simp [hlookup, judgmentPairData?]
        | pair word left right =>
            cases happrox : input.1.1.traceApproxCode 1 left right <;>
              simp [hlookup, judgmentPairData?, checkCondition, happrox]

private def checkProgressionRow
    (context : CertificateCheckContext Action)
    (payload : ProgressionRowCode) :
    Option (CertificateJudgment Action) :=
  context.1.checkCertificateRow context.2.1.1 context.2.1.2
    context.2.2.1 context.2.2.2
    (.progression payload.1 payload.2)

private theorem checkProgressionRow_primrec :
    Primrec₂ (checkProgressionRow (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × ProgressionRowCode
  have hpair : Primrec fun input : Input =>
      lookupPair? input.1 input.2.1 :=
    lookupPair?_primrec.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  have hprocess : Primrec₂ fun (input : Input)
      (data : PairJudgmentData Action) =>
      if input.1.1.traceApproxCode 1 data.2.1 data.2.2 &&
          input.1.1.progressionChildrenCode input.1.2.2.2
            data.1 data.2.1 input.2.2 then
        some (CertificateJudgment.nop data.1)
      else none := by
    apply Primrec₂.mk
    let ProcessInput := Input × PairJudgmentData Action
    have hg : Primrec fun p : ProcessInput => p.1.1.1 :=
      checkContextGrammar_primrec.comp
        (Primrec.fst.comp Primrec.fst)
    have hprior : Primrec fun p : ProcessInput => p.1.1.2.2.2 :=
      checkContextPrior_primrec.comp
        (Primrec.fst.comp Primrec.fst)
    have hword : Primrec fun p : ProcessInput => p.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hleft : Primrec fun p : ProcessInput => p.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hrefs : Primrec fun p : ProcessInput => p.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hright : Primrec fun p : ProcessInput => p.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have happroxInput : Primrec fun p : ProcessInput =>
        (p.1.1.1, p.2.2.1, p.2.2.2) :=
      Primrec.pair hg (Primrec.pair hleft hright)
    have happrox : Primrec fun p : ProcessInput =>
        p.1.1.1.traceApproxCode 1 p.2.2.1 p.2.2.2 :=
      traceApproxOneCode_primrec.comp happroxInput
    let packProgression := fun p : ProcessInput =>
        (p.1.1.1, (p.1.1.2.2.2,
          (p.2.1, (p.2.2.1, p.1.2.2))))
    have hprogressionInput : Primrec packProgression :=
      Primrec.pair hg
        (Primrec.pair hprior
          (Primrec.pair hword
            (Primrec.pair hleft hrefs)))
    have hpackedProgression :=
      progressionChildrenCode_primrec.comp hprogressionInput
    have hprogression : Primrec fun p : ProcessInput =>
        p.1.1.1.progressionChildrenCode p.1.1.2.2.2
          p.2.1 p.2.2.1 p.1.2.2 := by
      exact hpackedProgression.of_eq fun _ => rfl
    have hout : Primrec fun p : ProcessInput =>
        (CertificateJudgment.nop p.2.1 :
          CertificateJudgment Action) :=
      judgmentNop_primrec.comp
        (Primrec.fst.comp Primrec.snd)
    exact (Primrec.cond
      (Primrec.and.comp happrox hprogression)
      (Primrec.option_some.comp hout)
      (Primrec.const none)).of_eq fun p => by
        cases p.1.1.1.traceApproxCode 1 p.2.2.1 p.2.2.2 <;>
          cases p.1.1.1.progressionChildrenCode p.1.1.2.2.2
            p.2.1 p.2.2.1 p.1.2.2 <;> rfl
  exact (Primrec.option_bind hpair hprocess).of_eq fun input => by
    unfold checkProgressionRow checkCertificateRow lookupPair?
    cases hlookup : lookupPrior input.1.2.2.2 input.2.1 with
    | none => simp [hlookup]
    | some judgment =>
        cases judgment with
        | nop word => simp [hlookup, judgmentPairData?]
        | fail => simp [hlookup, judgmentPairData?]
        | pair word left right =>
            cases happrox : input.1.1.traceApproxCode 1 left right <;>
              cases hprogression :
                input.1.1.progressionChildrenCode input.1.2.2.2
                  word left input.2.2 <;>
                simp [hlookup, judgmentPairData?, checkCondition,
                  happrox, hprogression]

private abbrev TransitionProcessInput (Action : Type) :=
  EncodedFirstOrderGrammar Action ×
    (Label Action × PairJudgmentData Action)

private theorem transitionGrammar_primrec :
    Primrec fun input : TransitionProcessInput Action => input.1 :=
  Primrec.fst

private theorem transitionLabel_primrec :
    Primrec fun input : TransitionProcessInput Action => input.2.1 :=
  Primrec.fst.comp Primrec.snd

private theorem transitionWord_primrec :
    Primrec fun input : TransitionProcessInput Action => input.2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem transitionLeft_primrec :
    Primrec fun input : TransitionProcessInput Action => input.2.2.2.1 :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem transitionRight_primrec :
    Primrec fun input : TransitionProcessInput Action => input.2.2.2.2 :=
  Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private def finishTransition
    (input : TransitionProcessInput Action) :
    Option (CertificateJudgment Action) :=
  if input.1.groundPairCode input.2.2.2.1 input.2.2.2.2 then
    some (.pair (input.2.2.1 ++ [input.2.1])
      input.2.2.2.1 input.2.2.2.2)
  else none

private theorem finishTransition_primrec :
    Primrec (finishTransition (Action := Action)) := by
  have hground : Primrec fun input : TransitionProcessInput Action =>
      input.1.groundPairCode input.2.2.2.1 input.2.2.2.2 :=
    groundPairCode_primrec.comp
      (Primrec.pair transitionGrammar_primrec
        (Primrec.pair transitionLeft_primrec transitionRight_primrec))
  have hword : Primrec fun input : TransitionProcessInput Action =>
      input.2.2.1 ++ [input.2.1] :=
    Primrec.list_append.comp transitionWord_primrec
      (Primrec.list_cons.comp transitionLabel_primrec
        (Primrec.const []))
  have hout : Primrec fun input : TransitionProcessInput Action =>
      (CertificateJudgment.pair (input.2.2.1 ++ [input.2.1])
        input.2.2.2.1 input.2.2.2.2 : CertificateJudgment Action) :=
    judgmentPair_primrec.comp
      (Primrec.pair hword
        (Primrec.pair transitionLeft_primrec transitionRight_primrec))
  exact (Primrec.cond hground
    (Primrec.option_some.comp hout)
    (Primrec.const none)).of_eq fun input => by
      unfold finishTransition
      cases input.1.groundPairCode input.2.2.2.1 input.2.2.2.2 <;> rfl

private def transitionPairData
    (input : TransitionProcessInput Action) :
    Option (CertificateJudgment Action) :=
  if input.1.traceApproxCode 1 input.2.2.2.1 input.2.2.2.2 then do
    let left' ← input.1.step? input.2.1 input.2.2.2.1
    let right' ← input.1.step? input.2.1 input.2.2.2.2
    finishTransition (input.1,
      input.2.1, input.2.2.1, left', right')
  else none

private theorem transitionPairData_primrec :
    Primrec (transitionPairData (Action := Action)) := by
  let Input := TransitionProcessInput Action
  have happrox : Primrec fun input : Input =>
      input.1.traceApproxCode 1 input.2.2.2.1 input.2.2.2.2 :=
    traceApproxOneCode_primrec.comp
      (Primrec.pair transitionGrammar_primrec
        (Primrec.pair transitionLeft_primrec transitionRight_primrec))
  have hleftStep : Primrec fun input : Input =>
      input.1.step? input.2.1 input.2.2.2.1 :=
    step?_primrec.comp
      (Primrec.pair
        (Primrec.pair transitionGrammar_primrec transitionLabel_primrec)
        transitionLeft_primrec)
  have hrightStep : Primrec fun input : Input =>
      input.1.step? input.2.1 input.2.2.2.2 :=
    step?_primrec.comp
      (Primrec.pair
        (Primrec.pair transitionGrammar_primrec transitionLabel_primrec)
        transitionRight_primrec)
  have hafterLeft : Primrec₂ fun (input : Input) (left' : RegularTerm) =>
      (input.1.step? input.2.1 input.2.2.2.2).bind fun right' =>
        finishTransition (input.1,
          input.2.1, input.2.2.1, left', right') := by
    apply Primrec₂.mk
    let LeftInput := Input × RegularTerm
    have hrightStep' : Primrec fun input : LeftInput =>
        input.1.1.step? input.1.2.1 input.1.2.2.2.2 :=
      hrightStep.comp Primrec.fst
    have hfinish : Primrec₂ fun (input : LeftInput)
        (right' : RegularTerm) =>
        finishTransition (input.1.1,
          input.1.2.1, input.1.2.2.1, input.2, right') := by
      apply Primrec₂.mk
      let FinishInput := LeftInput × RegularTerm
      have hbase : Primrec fun input : FinishInput => input.1.1 :=
        Primrec.fst.comp Primrec.fst
      have hleft' : Primrec fun input : FinishInput => input.1.2 :=
        Primrec.snd.comp Primrec.fst
      have hright' : Primrec fun input : FinishInput => input.2 :=
        Primrec.snd
      exact finishTransition_primrec.comp
        (Primrec.pair
          (transitionGrammar_primrec.comp hbase)
          (Primrec.pair
            (transitionLabel_primrec.comp hbase)
            (Primrec.pair
              (transitionWord_primrec.comp hbase)
              (Primrec.pair hleft' hright'))))
    exact Primrec.option_bind hrightStep' hfinish
  have hsteps : Primrec fun input : Input =>
      (input.1.step? input.2.1 input.2.2.2.1).bind fun left' =>
        (input.1.step? input.2.1 input.2.2.2.2).bind fun right' =>
          finishTransition (input.1,
            input.2.1, input.2.2.1, left', right') :=
    Primrec.option_bind hleftStep hafterLeft
  exact (Primrec.cond happrox hsteps
    (Primrec.const none)).of_eq fun input => by
      unfold transitionPairData
      cases input.1.traceApproxCode 1 input.2.2.2.1 input.2.2.2.2 <;> rfl

private def checkTransitionRow
    (context : CertificateCheckContext Action)
    (payload : ℕ × Label Action) :
    Option (CertificateJudgment Action) :=
  context.1.checkCertificateRow context.2.1.1 context.2.1.2
    context.2.2.1 context.2.2.2
    (.transition payload.1 payload.2)

private theorem checkTransitionRow_primrec :
    Primrec₂ (checkTransitionRow (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × (ℕ × Label Action)
  have hpair : Primrec fun input : Input =>
      lookupPair? input.1 input.2.1 :=
    lookupPair?_primrec.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  have hprocess : Primrec₂ fun (input : Input)
      (data : PairJudgmentData Action) =>
      transitionPairData (input.1.1, input.2.2, data) := by
    apply Primrec₂.mk
    exact transitionPairData_primrec.comp
      (Primrec.pair
        (checkContextGrammar_primrec.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd))
  exact (Primrec.option_bind hpair hprocess).of_eq fun input => by
    unfold checkTransitionRow checkCertificateRow lookupPair?
    cases hlookup : lookupPrior input.1.2.2.2 input.2.1 with
    | none => simp [hlookup]
    | some judgment =>
        cases judgment with
        | nop word => simp [hlookup, judgmentPairData?]
        | fail => simp [hlookup, judgmentPairData?]
        | pair word left right =>
            simp only [hlookup, judgmentPairData?, Option.bind_some,
              transitionPairData]
            cases happrox : input.1.1.traceApproxCode 1 left right with
            | false => simp [checkCondition, happrox]
            | true =>
                cases hleft : input.1.1.step? input.2.2 left with
                | none => simp [checkCondition, happrox, hleft]
                | some left' =>
                    cases hright : input.1.1.step? input.2.2 right with
                    | none => simp [checkCondition, happrox, hleft, hright]
                    | some right' =>
                        cases hground :
                            input.1.1.groundPairCode left' right' <;>
                          simp [finishTransition, checkCondition, happrox,
                            hleft, hright, hground]

private abbrev LimitProcessInput (Action : Type) :=
  LimitConditionsInput (Action := Action)

private def finishLimit
    (input : LimitProcessInput Action) :
    Option (CertificateJudgment Action) :=
  if input.1.limitRowConditionsCode
      input.2.1.1 input.2.1.2
      input.2.2.1.1 input.2.2.1.2
      input.2.2.2.1.1 input.2.2.2.1.2
      input.2.2.2.2.1 input.2.2.2.2.2.1 input.2.2.2.2.2.2 then
    some (.pair input.2.1.1
      (input.2.2.2.2.1.instantiate
        [input.2.2.2.2.2.1.unaryLimit])
      input.2.2.1.2)
  else none

private theorem finishLimit_primrec :
    Primrec (finishLimit (Action := Action)) := by
  let Input := LimitProcessInput Action
  have houterWord : Primrec fun input : Input => input.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have houterRight : Primrec fun input : Input => input.2.2.1.2 :=
    Primrec.snd.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have houterContext : Primrec fun input : Input => input.2.2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hreplacementContext : Primrec fun input : Input =>
      input.2.2.2.2.2.1 :=
    Primrec.fst.comp
      (Primrec.snd.comp
        (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hlimit : Primrec fun input : Input =>
      input.2.2.2.2.2.1.unaryLimit :=
    unaryLimit_primrec.comp hreplacementContext
  have hresult : Primrec fun input : Input =>
      input.2.2.2.2.1.instantiate
        [input.2.2.2.2.2.1.unaryLimit] :=
    instantiate_primrec.comp houterContext
      (Primrec.list_cons.comp hlimit (Primrec.const []))
  have hout : Primrec fun input : Input =>
      (CertificateJudgment.pair input.2.1.1
        (input.2.2.2.2.1.instantiate
          [input.2.2.2.2.2.1.unaryLimit])
        input.2.2.1.2 : CertificateJudgment Action) :=
    judgmentPair_primrec.comp
      (Primrec.pair houterWord (Primrec.pair hresult houterRight))
  exact (Primrec.cond limitRowConditionsCode_primrec
    (Primrec.option_some.comp hout)
    (Primrec.const none)).of_eq fun input => by
      unfold finishLimit
      cases input.1.limitRowConditionsCode
          input.2.1.1 input.2.1.2
          input.2.2.1.1 input.2.2.1.2
          input.2.2.2.1.1 input.2.2.2.1.2
          input.2.2.2.2.1 input.2.2.2.2.2.1
          input.2.2.2.2.2.2 <;> rfl

private def checkLimitRow
    (context : CertificateCheckContext Action)
    (payload : LimitRowCode) :
    Option (CertificateJudgment Action) :=
  context.1.checkCertificateRow context.2.1.1 context.2.1.2
    context.2.2.1 context.2.2.2
    (.limit payload.1 payload.2.1 payload.2.2.1
      payload.2.2.2.1 payload.2.2.2.2)

private theorem checkLimitRow_primrec :
    Primrec₂ (checkLimitRow (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × LimitRowCode
  have houter : Primrec fun input : Input =>
      lookupPair? input.1 input.2.1 :=
    lookupPair?_primrec.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  have hafterOuter : Primrec₂ fun (input : Input)
      (outer : PairJudgmentData Action) =>
      (lookupPair? input.1 input.2.2.1).bind fun shorter =>
        finishLimit (input.1.1,
          (outer.1, shorter.1),
          (outer.2.1, outer.2.2),
          (shorter.2.1, shorter.2.2),
          input.2.2.2.1, input.2.2.2.2.1, input.2.2.2.2.2) := by
    apply Primrec₂.mk
    let OuterInput := Input × PairJudgmentData Action
    have hshorter : Primrec fun input : OuterInput =>
        lookupPair? input.1.1 input.1.2.2.1 :=
      lookupPair?_primrec.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    have hfinish : Primrec₂ fun (input : OuterInput)
        (shorter : PairJudgmentData Action) =>
        finishLimit (input.1.1.1,
          (input.2.1, shorter.1),
          (input.2.2.1, input.2.2.2),
          (shorter.2.1, shorter.2.2),
          input.1.2.2.2.1,
          input.1.2.2.2.2.1,
          input.1.2.2.2.2.2) := by
      apply Primrec₂.mk
      let FinishInput := OuterInput × PairJudgmentData Action
      have hbase : Primrec fun input : FinishInput => input.1.1 :=
        Primrec.fst.comp Primrec.fst
      have houterData : Primrec fun input : FinishInput => input.1.2 :=
        Primrec.snd.comp Primrec.fst
      have hshorterData : Primrec fun input : FinishInput => input.2 :=
        Primrec.snd
      have hcontext : Primrec fun input : FinishInput => input.1.1.1 :=
        Primrec.fst.comp hbase
      have hpayload : Primrec fun input : FinishInput => input.1.1.2 :=
        Primrec.snd.comp hbase
      have houterWord : Primrec fun input : FinishInput => input.1.2.1 :=
        Primrec.fst.comp houterData
      have houterLeft : Primrec fun input : FinishInput => input.1.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp houterData)
      have houterRight : Primrec fun input : FinishInput => input.1.2.2.2 :=
        Primrec.snd.comp (Primrec.snd.comp houterData)
      have hshorterWord : Primrec fun input : FinishInput => input.2.1 :=
        Primrec.fst.comp hshorterData
      have hshorterLeft : Primrec fun input : FinishInput => input.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp hshorterData)
      have hshorterRight : Primrec fun input : FinishInput => input.2.2.2 :=
        Primrec.snd.comp (Primrec.snd.comp hshorterData)
      have houterContext : Primrec fun input : FinishInput =>
          input.1.1.2.2.2.1 :=
        Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp hpayload))
      have hreplacementContext : Primrec fun input : FinishInput =>
          input.1.1.2.2.2.2.1 :=
        Primrec.fst.comp
          (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp hpayload)))
      have hfocus : Primrec fun input : FinishInput =>
          input.1.1.2.2.2.2.2 :=
        Primrec.snd.comp
          (Primrec.snd.comp
            (Primrec.snd.comp (Primrec.snd.comp hpayload)))
      exact finishLimit_primrec.comp
        (Primrec.pair
          (checkContextGrammar_primrec.comp hcontext)
          (Primrec.pair
            (Primrec.pair houterWord hshorterWord)
            (Primrec.pair
              (Primrec.pair houterLeft houterRight)
              (Primrec.pair
                (Primrec.pair hshorterLeft hshorterRight)
                (Primrec.pair
                  houterContext
                  (Primrec.pair hreplacementContext hfocus))))))
    exact Primrec.option_bind hshorter hfinish
  exact (Primrec.option_bind houter hafterOuter).of_eq fun input => by
    unfold checkLimitRow checkCertificateRow lookupPair?
    cases houterLookup : lookupPrior input.1.2.2.2 input.2.1 with
    | none => simp [houterLookup]
    | some outerJudgment =>
        cases outerJudgment with
        | nop word => simp [houterLookup, judgmentPairData?]
        | fail => simp [houterLookup, judgmentPairData?]
        | pair word outerLeft outerRight =>
            simp only [houterLookup, judgmentPairData?, Option.bind_some]
            cases hshorterLookup :
                lookupPrior input.1.2.2.2 input.2.2.1 with
            | none => simp [hshorterLookup]
            | some shorterJudgment =>
                cases shorterJudgment with
                | nop shorterWord =>
                    simp [hshorterLookup, judgmentPairData?]
                | fail => simp [hshorterLookup, judgmentPairData?]
                | pair shorterWord shorterLeft shorterRight =>
                    simp only [hshorterLookup, judgmentPairData?,
                      Option.bind_some]
                    cases hcondition : input.1.1.limitRowConditionsCode
                        word shorterWord outerLeft outerRight
                        shorterLeft shorterRight input.2.2.2.1
                        input.2.2.2.2.1 input.2.2.2.2.2 <;>
                      simp [finishLimit, checkCondition, hcondition]

private abbrev BasisProcessInput (Action : Type) :=
  BasisConditionsInput (Action := Action)

private def finishBasis
    (input : BasisProcessInput Action) :
    Option (CertificateJudgment Action) :=
  if input.1.basisRowConditionsCode input.2.1
      input.2.2.1.1 input.2.2.1.2
      input.2.2.2.1 input.2.2.2.2 then
    some (.nop input.2.1)
  else none

private theorem finishBasis_primrec :
    Primrec (finishBasis (Action := Action)) := by
  have hword : Primrec fun input : BasisProcessInput Action => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hout : Primrec fun input : BasisProcessInput Action =>
      (CertificateJudgment.nop input.2.1 : CertificateJudgment Action) :=
    judgmentNop_primrec.comp hword
  exact (Primrec.cond basisRowConditionsCode_primrec
    (Primrec.option_some.comp hout)
    (Primrec.const none)).of_eq fun input => by
      unfold finishBasis
      cases input.1.basisRowConditionsCode input.2.1
          input.2.2.1.1 input.2.2.1.2
          input.2.2.2.1 input.2.2.2.2 <;> rfl

private def checkBasisRow
    (context : CertificateCheckContext Action)
    (payload : BasisRowCode) :
    Option (CertificateJudgment Action) :=
  context.1.checkCertificateRow context.2.1.1 context.2.1.2
    context.2.2.1 context.2.2.2
    (.basis payload.1 payload.2.1 payload.2.2)

private theorem checkBasisRow_primrec :
    Primrec₂ (checkBasisRow (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × BasisRowCode
  have hpair : Primrec fun input : Input =>
      lookupPair? input.1 input.2.1 :=
    lookupPair?_primrec.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  have hafterPair : Primrec₂ fun (input : Input)
      (data : PairJudgmentData Action) =>
      (input.1.2.2.1[input.2.2.1]?).bind fun schema =>
        finishBasis (input.1.1,
          (data.1, ((data.2.1, data.2.2),
            (schema, input.2.2.2)))) := by
    apply Primrec₂.mk
    let PairInput := Input × PairJudgmentData Action
    have hschema : Primrec fun input : PairInput =>
        input.1.1.2.2.1[input.1.2.2.1]? :=
      Primrec.list_getElem?.comp
        (checkContextBasis_primrec.comp
          (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    have hfinish : Primrec₂ fun (input : PairInput)
        (schema : BasisPair) =>
        finishBasis (input.1.1.1,
          (input.2.1, ((input.2.2.1, input.2.2.2),
            (schema, input.1.2.2.2)))) := by
      apply Primrec₂.mk
      let FinishInput := PairInput × BasisPair
      have hbase : Primrec fun input : FinishInput => input.1.1 :=
        Primrec.fst.comp Primrec.fst
      have hdata : Primrec fun input : FinishInput => input.1.2 :=
        Primrec.snd.comp Primrec.fst
      have hcontext : Primrec fun input : FinishInput => input.1.1.1 :=
        Primrec.fst.comp hbase
      have hpayload : Primrec fun input : FinishInput => input.1.1.2 :=
        Primrec.snd.comp hbase
      exact finishBasis_primrec.comp
        (Primrec.pair
          (checkContextGrammar_primrec.comp hcontext)
          (Primrec.pair
            (Primrec.fst.comp hdata)
            (Primrec.pair
              (Primrec.pair
                (Primrec.fst.comp (Primrec.snd.comp hdata))
                (Primrec.snd.comp (Primrec.snd.comp hdata)))
              (Primrec.pair Primrec.snd
                (Primrec.snd.comp
                  (Primrec.snd.comp hpayload))))))
    exact Primrec.option_bind hschema hfinish
  exact (Primrec.option_bind hpair hafterPair).of_eq fun input => by
    unfold checkBasisRow checkCertificateRow lookupPair?
    cases hlookup : lookupPrior input.1.2.2.2 input.2.1 with
    | none => simp [hlookup]
    | some judgment =>
        cases judgment with
        | nop word => simp [hlookup, judgmentPairData?]
        | fail => simp [hlookup, judgmentPairData?]
        | pair word left right =>
            simp only [hlookup, judgmentPairData?, Option.bind_some]
            cases hschema : input.1.2.2.1[input.2.2.1]? with
            | none => simp [hschema]
            | some schema =>
                simp only [hschema, Option.bind_some]
                cases hcondition : input.1.1.basisRowConditionsCode
                    word left right schema input.2.2.2 <;>
                  simp [finishBasis, checkCondition, hcondition]

/-! ## Dispatch through the primitive row encoding -/

private abbrev CertificateRowCodeTail₅ (Action : Type) :=
  ProgressionRowCode ⊕ ℕ

private abbrev CertificateRowCodeTail₄ (Action : Type) :=
  BasisRowCode ⊕ CertificateRowCodeTail₅ Action

private abbrev CertificateRowCodeTail₃ (Action : Type) :=
  ℕ ⊕ CertificateRowCodeTail₄ Action

private abbrev CertificateRowCodeTail₂ (Action : Type) :=
  LimitRowCode ⊕ CertificateRowCodeTail₃ Action

private abbrev CertificateRowCodeTail₁ (Action : Type) :=
  (ℕ × Label Action) ⊕ CertificateRowCodeTail₂ Action

private def checkCertificateRowCodeTail₅
    (context : CertificateCheckContext Action) :
    CertificateRowCodeTail₅ Action →
      Option (CertificateJudgment Action)
  | .inl payload => checkProgressionRow context payload
  | .inr pairRef => checkRejectionRow context pairRef

private theorem checkCertificateRowCodeTail₅_primrec :
    Primrec₂ (checkCertificateRowCodeTail₅ (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action ×
    CertificateRowCodeTail₅ Action
  refine (Primrec.sumCasesOn
    (f := fun input : Input => input.2)
    (g := fun input payload => checkProgressionRow input.1 payload)
    (h := fun input pairRef => checkRejectionRow input.1 pairRef)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact checkProgressionRow_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · apply Primrec₂.mk
    exact checkRejectionRow_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · intro input
    cases input.2 <;> rfl

private def checkCertificateRowCodeTail₄
    (context : CertificateCheckContext Action) :
    CertificateRowCodeTail₄ Action →
      Option (CertificateJudgment Action)
  | .inl payload => checkBasisRow context payload
  | .inr tail => checkCertificateRowCodeTail₅ context tail

private theorem checkCertificateRowCodeTail₄_primrec :
    Primrec₂ (checkCertificateRowCodeTail₄ (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action ×
    CertificateRowCodeTail₄ Action
  refine (Primrec.sumCasesOn
    (f := fun input : Input => input.2)
    (g := fun input payload => checkBasisRow input.1 payload)
    (h := fun input tail => checkCertificateRowCodeTail₅ input.1 tail)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact checkBasisRow_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · apply Primrec₂.mk
    exact checkCertificateRowCodeTail₅_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · intro input
    cases input.2 <;> rfl

private def checkCertificateRowCodeTail₃
    (context : CertificateCheckContext Action) :
    CertificateRowCodeTail₃ Action →
      Option (CertificateJudgment Action)
  | .inl pairRef => checkSymmetryRow context pairRef
  | .inr tail => checkCertificateRowCodeTail₄ context tail

private theorem checkCertificateRowCodeTail₃_primrec :
    Primrec₂ (checkCertificateRowCodeTail₃ (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action ×
    CertificateRowCodeTail₃ Action
  refine (Primrec.sumCasesOn
    (f := fun input : Input => input.2)
    (g := fun input pairRef => checkSymmetryRow input.1 pairRef)
    (h := fun input tail => checkCertificateRowCodeTail₄ input.1 tail)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact checkSymmetryRow_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · apply Primrec₂.mk
    exact checkCertificateRowCodeTail₄_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · intro input
    cases input.2 <;> rfl

private def checkCertificateRowCodeTail₂
    (context : CertificateCheckContext Action) :
    CertificateRowCodeTail₂ Action →
      Option (CertificateJudgment Action)
  | .inl payload => checkLimitRow context payload
  | .inr tail => checkCertificateRowCodeTail₃ context tail

private theorem checkCertificateRowCodeTail₂_primrec :
    Primrec₂ (checkCertificateRowCodeTail₂ (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action ×
    CertificateRowCodeTail₂ Action
  refine (Primrec.sumCasesOn
    (f := fun input : Input => input.2)
    (g := fun input payload => checkLimitRow input.1 payload)
    (h := fun input tail => checkCertificateRowCodeTail₃ input.1 tail)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact checkLimitRow_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · apply Primrec₂.mk
    exact checkCertificateRowCodeTail₃_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · intro input
    cases input.2 <;> rfl

private def checkCertificateRowCodeTail₁
    (context : CertificateCheckContext Action) :
    CertificateRowCodeTail₁ Action →
      Option (CertificateJudgment Action)
  | .inl payload => checkTransitionRow context payload
  | .inr tail => checkCertificateRowCodeTail₂ context tail

private theorem checkCertificateRowCodeTail₁_primrec :
    Primrec₂ (checkCertificateRowCodeTail₁ (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action ×
    CertificateRowCodeTail₁ Action
  refine (Primrec.sumCasesOn
    (f := fun input : Input => input.2)
    (g := fun input payload => checkTransitionRow input.1 payload)
    (h := fun input tail => checkCertificateRowCodeTail₂ input.1 tail)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact checkTransitionRow_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · apply Primrec₂.mk
    exact checkCertificateRowCodeTail₂_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · intro input
    cases input.2 <;> rfl

private def checkCertificateRowCode
    (context : CertificateCheckContext Action) :
    CertificateRowCode Action → Option (CertificateJudgment Action)
  | .inl _ => checkAxiomRow context
  | .inr tail => checkCertificateRowCodeTail₁ context tail

private theorem checkCertificateRowCode_primrec :
    Primrec₂ (checkCertificateRowCode (Action := Action)) := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × CertificateRowCode Action
  refine (Primrec.sumCasesOn
    (f := fun input : Input => input.2)
    (g := fun input (_ : Unit) => checkAxiomRow input.1)
    (h := fun input tail => checkCertificateRowCodeTail₁ input.1 tail)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact checkAxiomRow_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  · apply Primrec₂.mk
    exact checkCertificateRowCodeTail₁_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  · intro input
    cases input.2 <;> rfl

/-- Checking one certificate row is primitive recursive, uniformly in the raw
grammar, endpoints, basis, prior judgments, and row. -/
public theorem checkCertificateRow_primrec :
    Primrec₂ fun (context : CertificateCheckContext Action)
      (row : CertificateRow Action) =>
      context.1.checkCertificateRow context.2.1.1 context.2.1.2
        context.2.2.1 context.2.2.2 row := by
  apply Primrec₂.mk
  let Input := CertificateCheckContext Action × CertificateRow Action
  have hencode : Primrec fun input : Input =>
      certificateRowEquiv Action input.2 :=
    (Primrec.of_equiv : Primrec (certificateRowEquiv Action)).comp Primrec.snd
  exact (checkCertificateRowCode_primrec.comp Primrec.fst hencode).of_eq
    fun input => by
      cases input.2 <;> rfl

/-! ## Primitive-recursive checking of row lists -/

/-- The fixed data against which a certificate row list is checked. -/
public abbrev EquivalenceCertificateInstance (Action : Type) :=
  EncodedFirstOrderGrammar Action ×
    ((RegularTerm × RegularTerm) × List BasisPair)

private theorem certificateInstanceGrammar_primrec :
    Primrec fun input : EquivalenceCertificateInstance Action => input.1 :=
  Primrec.fst

private theorem certificateInstanceLeft_primrec :
    Primrec fun input : EquivalenceCertificateInstance Action =>
      input.2.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.snd)

private theorem certificateInstanceRight_primrec :
    Primrec fun input : EquivalenceCertificateInstance Action =>
      input.2.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)

private theorem certificateInstanceBasis_primrec :
    Primrec fun input : EquivalenceCertificateInstance Action =>
      input.2.2 :=
  Primrec.snd.comp Primrec.snd

private def advanceCertificateRows
    (base : EquivalenceCertificateInstance Action)
    (state : Option (List (CertificateJudgment Action)) ×
      CertificateRow Action) :
    Option (List (CertificateJudgment Action)) :=
  state.1.bind fun prior =>
    (base.1.checkCertificateRow base.2.1.1 base.2.1.2
      base.2.2 prior state.2).bind fun result =>
        some (prior ++ [result])

private theorem advanceCertificateRows_primrec :
    Primrec₂ (advanceCertificateRows (Action := Action)) := by
  apply Primrec₂.mk
  let Input := EquivalenceCertificateInstance Action ×
    (Option (List (CertificateJudgment Action)) × CertificateRow Action)
  have hprior : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hafterPrior : Primrec₂ fun (input : Input)
      (prior : List (CertificateJudgment Action)) =>
      (checkCertificateRowCode
        (input.1.1,
          ((input.1.2.1.1, input.1.2.1.2),
            (input.1.2.2, prior)))
        (certificateRowEquiv Action input.2.2)).bind
        fun result => some (prior ++ [result]) := by
    apply Primrec₂.mk
    let PriorInput := Input × List (CertificateJudgment Action)
    have hbase : Primrec fun input : PriorInput => input.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hrow : Primrec fun input : PriorInput =>
        input.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hrowCode : Primrec fun input : PriorInput =>
        certificateRowEquiv Action input.1.2.2 :=
      (Primrec.of_equiv : Primrec (certificateRowEquiv Action)).comp hrow
    have hprior' : Primrec fun input : PriorInput => input.2 :=
      Primrec.snd
    have hcontext : Primrec fun input : PriorInput =>
        (input.1.1.1,
          ((input.1.1.2.1.1, input.1.1.2.1.2),
            (input.1.1.2.2, input.2))) :=
      Primrec.pair
        (certificateInstanceGrammar_primrec.comp hbase)
        (Primrec.pair
          (Primrec.pair
            (certificateInstanceLeft_primrec.comp hbase)
            (certificateInstanceRight_primrec.comp hbase))
          (Primrec.pair
            (certificateInstanceBasis_primrec.comp hbase)
            hprior'))
    have hchecked : Primrec fun input : PriorInput =>
        checkCertificateRowCode
          (input.1.1.1,
            ((input.1.1.2.1.1, input.1.1.2.1.2),
              (input.1.1.2.2, input.2)))
          (certificateRowEquiv Action input.1.2.2) :=
      checkCertificateRowCode_primrec.comp hcontext hrowCode
    have hafterResult : Primrec₂ fun (input : PriorInput)
        (result : CertificateJudgment Action) =>
        some (input.2 ++ [result]) := by
      apply Primrec₂.mk
      exact Primrec.option_some.comp
        (Primrec.list_append.comp
          (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
    exact Primrec.option_bind hchecked hafterResult
  exact (Primrec.option_bind hprior hafterPrior).of_eq fun input => by
    unfold advanceCertificateRows
    cases input.2.1 with
    | none => rfl
    | some prior =>
        simp only [Option.bind_some]
        cases input.2.2 <;> rfl

private def checkCertificateRowsFold
    (base : EquivalenceCertificateInstance Action)
    (prior : List (CertificateJudgment Action))
    (rows : List (CertificateRow Action)) :
    Option (List (CertificateJudgment Action)) :=
  rows.foldl (fun state row =>
    advanceCertificateRows base (state, row)) (some prior)

private theorem checkCertificateRowsFold_primrec :
    Primrec fun input : EquivalenceCertificateInstance Action ×
        (List (CertificateJudgment Action) × List (CertificateRow Action)) =>
      checkCertificateRowsFold input.1 input.2.1 input.2.2 := by
  let Input := EquivalenceCertificateInstance Action ×
    (List (CertificateJudgment Action) × List (CertificateRow Action))
  have hrows : Primrec fun input : Input => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hinitial : Primrec fun input : Input =>
      some input.2.1 :=
    Primrec.option_some.comp
      (Primrec.fst.comp Primrec.snd)
  have hstep : Primrec₂ fun (input : Input)
      (state : Option (List (CertificateJudgment Action)) ×
        CertificateRow Action) =>
      advanceCertificateRows input.1 state := by
    apply Primrec₂.mk
    exact advanceCertificateRows_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.list_foldl hrows hinitial hstep).of_eq fun input => by
    unfold checkCertificateRowsFold
    rfl

private theorem checkCertificateRowsFold_none
    (base : EquivalenceCertificateInstance Action)
    (rows : List (CertificateRow Action)) :
    rows.foldl (fun state row =>
      advanceCertificateRows base (state, row)) none = none := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change rows.foldl (fun state row =>
        advanceCertificateRows base (state, row))
          (advanceCertificateRows base (none, row)) = none
      change rows.foldl (fun state row =>
        advanceCertificateRows base (state, row)) none = none
      exact ih

private theorem checkCertificateRows_eq_fold
    (base : EquivalenceCertificateInstance Action)
    (prior : List (CertificateJudgment Action))
    (rows : List (CertificateRow Action)) :
    base.1.checkCertificateRows base.2.1.1 base.2.1.2 base.2.2
        prior rows =
      checkCertificateRowsFold base prior rows := by
  induction rows generalizing prior with
  | nil => rfl
  | cons row rows ih =>
      unfold checkCertificateRows checkCertificateRowsFold
      cases hrow : base.1.checkCertificateRow base.2.1.1
          base.2.1.2 base.2.2 prior row with
      | none =>
          change none = rows.foldl (fun state row =>
            advanceCertificateRows base (state, row))
              (advanceCertificateRows base (some prior, row))
          rw [show advanceCertificateRows base (some prior, row) = none by
            simp [advanceCertificateRows, hrow]]
          exact (checkCertificateRowsFold_none base rows).symm
      | some result =>
          simp [advanceCertificateRows, hrow]
          exact ih (prior ++ [result])

/-- Checking a bottom-up list of certificate rows is primitive recursive,
uniformly in all fixed instance data and the initial prior list. -/
public theorem checkCertificateRows_primrec :
    Primrec fun input : EquivalenceCertificateInstance Action ×
        (List (CertificateJudgment Action) × List (CertificateRow Action)) =>
      input.1.1.checkCertificateRows
        input.1.2.1.1 input.1.2.1.2 input.1.2.2
        input.2.1 input.2.2 :=
  checkCertificateRowsFold_primrec.of_eq fun input =>
    (checkCertificateRows_eq_fold input.1 input.2.1 input.2.2).symm

private theorem list_getLast?_primrec
    {Element : Type} [Primcodable Element] :
    Primrec (List.getLast? : List Element → Option Element) := by
  exact (Primrec.list_head?.comp Primrec.list_reverse).of_eq fun items => by
    induction items with
    | nil => rfl
    | cons head tail ih =>
        cases tail with
        | nil => rfl
        | cons next rest =>
            simpa using ih

/-- Verifying a complete finite certificate and returning its final judgment
is primitive recursive in the raw instance and row list. -/
public theorem checkCertificate_primrec :
    Primrec fun input : EquivalenceCertificateInstance Action ×
        List (CertificateRow Action) =>
      input.1.1.checkCertificate
        input.1.2.1.1 input.1.2.1.2 input.1.2.2 input.2 := by
  let Input := EquivalenceCertificateInstance Action ×
    List (CertificateRow Action)
  have hrows : Primrec fun input : Input =>
      input.1.1.checkCertificateRows
        input.1.2.1.1 input.1.2.1.2 input.1.2.2 [] input.2 :=
    checkCertificateRows_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.const []) Primrec.snd))
  have hlast : Primrec₂ fun (_ : Input)
      (results : List (CertificateJudgment Action)) =>
      results.getLast? := by
    apply Primrec₂.mk
    exact list_getLast?_primrec.comp Primrec.snd
  exact (Primrec.option_bind hrows hlast).of_eq fun input => by
    unfold checkCertificate
    rfl

/-- The executable acceptance Boolean for a finite equivalence certificate is
primitive recursive in the complete raw input. -/
public theorem acceptsEquivalenceCertificateCode_primrec :
    Primrec fun input : EquivalenceCertificateInstance Action ×
        List (CertificateRow Action) =>
      input.1.1.acceptsEquivalenceCertificateCode
        input.1.2.1.1 input.1.2.1.2 input.1.2.2 input.2 := by
  have htarget : Primrec fun (_ : EquivalenceCertificateInstance Action ×
      List (CertificateRow Action)) =>
      (some (.nop []) : Option (CertificateJudgment Action)) :=
    Primrec.const _
  exact (Primrec.eq.decide.comp checkCertificate_primrec htarget).of_eq
    fun input => by
      unfold acceptsEquivalenceCertificateCode
      rfl

private theorem acceptsEquivalenceCertificateCode_primrec₂ :
    Primrec₂ fun (base : EquivalenceCertificateInstance Action)
      (rows : List (CertificateRow Action)) =>
      base.1.acceptsEquivalenceCertificateCode
        base.2.1.1 base.2.1.2 base.2.2 rows :=
  acceptsEquivalenceCertificateCode_primrec

/-! ## Unbounded enumeration of finite certificates -/

/-- Raw existence of a finite accepted certificate for the supplied encoded
grammar, endpoints, and finite basis. -/
@[expose] public def HasEquivalenceCertificate
    (base : EquivalenceCertificateInstance Action) : Prop :=
  ∃ rows, base.1.acceptsEquivalenceCertificateCode
    base.2.1.1 base.2.1.2 base.2.2 rows = true

/-- Decode the `k`th candidate row list and run the total checker. -/
@[expose] public def acceptingCertificateIndexTest
    (base : EquivalenceCertificateInstance Action) (k : ℕ) : Bool :=
  ((Encodable.decode (α := List (CertificateRow Action)) k).map fun rows =>
    base.1.acceptsEquivalenceCertificateCode
      base.2.1.1 base.2.1.2 base.2.2 rows).getD false

/-- Unbounded search for the first encoded accepted certificate. -/
@[expose] public def findAcceptingCertificateIndex
    (base : EquivalenceCertificateInstance Action) : Part ℕ :=
  Nat.rfind fun k => Part.some (acceptingCertificateIndexTest base k)

private theorem acceptingCertificateIndexTest_computable₂ :
    Computable₂ (acceptingCertificateIndexTest (Action := Action)) := by
  have hmap : Computable fun input :
      EquivalenceCertificateInstance Action × ℕ =>
      (Encodable.decode (α := List (CertificateRow Action)) input.2).map
        fun rows => input.1.1.acceptsEquivalenceCertificateCode
          input.1.2.1.1 input.1.2.1.2 input.1.2.2 rows := by
    exact Computable.option_map
      (Computable.decode.comp Computable.snd)
      (Computable₂.mk
        (acceptsEquivalenceCertificateCode_primrec₂.to_comp.comp
          (Computable.fst.comp Computable.fst) Computable.snd))
  apply Computable₂.mk
  exact (Computable.option_getD hmap
    (Computable.const false)).of_eq fun _ => rfl

/-- Searching the enumerable row codes is one uniform partial-recursive
program. -/
public theorem findAcceptingCertificateIndex_partrec :
    Partrec (findAcceptingCertificateIndex (Action := Action)) := by
  exact Partrec.rfind acceptingCertificateIndexTest_computable₂.partrec₂

/-- The raw certificate search terminates exactly when some finite row list is
accepted. -/
public theorem findAcceptingCertificateIndex_dom_iff
    (base : EquivalenceCertificateInstance Action) :
    (findAcceptingCertificateIndex base).Dom ↔
      HasEquivalenceCertificate base := by
  simp only [findAcceptingCertificateIndex, Nat.rfind_dom, Part.some_dom]
  constructor
  · rintro ⟨k, hk⟩
    cases hdecode : Encodable.decode
        (α := List (CertificateRow Action)) k with
    | none =>
        simp [acceptingCertificateIndexTest, hdecode] at hk
    | some rows =>
        exact ⟨rows, by
          simpa [acceptingCertificateIndexTest, hdecode] using hk⟩
  · rintro ⟨rows, hrows⟩
    refine ⟨Encodable.encode rows, ?_⟩
    simpa [acceptingCertificateIndexTest] using hrows

/-- Existence of an accepted finite equivalence certificate is recursively
enumerable uniformly in the completely raw encoded instance. -/
public theorem hasEquivalenceCertificate_re :
    REPred (HasEquivalenceCertificate (Action := Action)) := by
  exact findAcceptingCertificateIndex_partrec.dom_re.of_eq fun base =>
    findAcceptingCertificateIndex_dom_iff base

end EncodedFirstOrderGrammar

end DCFEquivalence
