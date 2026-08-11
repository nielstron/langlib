module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FirstOrderGrammar
public import Mathlib.Data.List.Sublists

@[expose]
public section

/-!
# Primitive-recursive runtime-groundness

The finite support checker for reachable ground regular terms is primitive
recursive.  This is kept separate from the syntax file so the semantic
definition of `Ground` does not depend on computability proof machinery beyond
its executable Boolean code.
-/

namespace DCFEquivalence

namespace RegularTerm

private theorem list_all_primrec
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

private theorem nodes_primrec :
    Primrec (RegularTerm.nodes : RegularTerm → List RawNode) :=
  Primrec.fst

private theorem root_primrec :
    Primrec (RegularTerm.root : RegularTerm → ℕ) :=
  Primrec.snd

private theorem nodeAt?_primrec :
    Primrec₂ (RegularTerm.nodeAt? : RegularTerm → ℕ → Option RawNode) :=
  by
    apply Primrec₂.mk
    exact Primrec.list_getElem?.comp
      (nodes_primrec.comp Primrec.fst) Primrec.snd

private theorem nat_mem_list_primrec :
    Primrec₂ fun (support : List ℕ) (value : ℕ) =>
      decide (value ∈ support) := by
  apply Primrec₂.mk
  have htest : Primrec₂ fun (input : List ℕ × ℕ) (candidate : ℕ) =>
      decide (candidate = input.2) := by
    apply Primrec₂.mk
    exact Primrec.eq.decide.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  have hany : Primrec fun input : List ℕ × ℕ =>
      input.1.any fun candidate => decide (candidate = input.2) :=
    list_any_primrec Primrec.fst htest
  apply hany.of_eq
  rintro ⟨support, value⟩
  induction support with
  | nil => simp
  | cons head tail ih =>
      have ih' : (tail.any fun candidate => decide (candidate = value)) =
          decide (value ∈ tail) := by simpa using ih
      have ih'' : (tail.any fun candidate => decide (value = candidate)) =
          decide (value ∈ tail) := by simpa [eq_comm] using ih'
      simp [ih'', eq_comm]

private theorem childrenBoundCode_primrec :
    Primrec₂ fun (children : List ℕ) (bound : ℕ) =>
      children.all fun child => decide (child < bound) := by
  apply Primrec₂.mk
  have htest : Primrec₂ fun (input : List ℕ × ℕ) (child : ℕ) =>
      decide (child < input.2) := by
    apply Primrec₂.mk
    exact Primrec.nat_lt.decide.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  exact list_all_primrec Primrec.fst htest

private theorem childrenInSupportCode_primrec :
    Primrec₂ fun (children support : List ℕ) =>
      children.all fun child => decide (child ∈ support) := by
  apply Primrec₂.mk
  have htest : Primrec₂ fun (input : List ℕ × List ℕ) (child : ℕ) =>
      decide (child ∈ input.2) := by
    apply Primrec₂.mk
    exact nat_mem_list_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact list_all_primrec Primrec.fst htest

private abbrev ShapeContext := List ℕ × ℕ

private theorem applicationShapeWellFormedCode_primrec :
    Primrec₂ fun (context : ShapeContext) (app : ℕ × List ℕ) =>
      match context.1[app.1]? with
      | none => false
      | some rank =>
          decide (app.2.length = rank) &&
            app.2.all fun child => decide (child < context.2) := by
  apply Primrec₂.mk
  let Input := ShapeContext × (ℕ × List ℕ)
  have hrank : Primrec fun input : Input => input.1.1[input.2.1]? :=
    Primrec.list_getElem?.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hbound : Primrec fun input : Input =>
      input.2.2.all fun child => decide (child < input.1.2) :=
    childrenBoundCode_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  have hsome : Primrec₂ fun (input : Input) (rank : ℕ) =>
      decide (input.2.2.length = rank) &&
        input.2.2.all fun child => decide (child < input.1.2) := by
    apply Primrec₂.mk
    have hlength : Primrec (fun input : Input × ℕ =>
        input.1.2.2.length) :=
      Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact Primrec.and.comp
      (Primrec.eq.decide.comp hlength Primrec.snd)
      (hbound.comp Primrec.fst)
  refine (Primrec.option_casesOn
    (o := fun input : Input => input.1.1[input.2.1]?)
    (f := fun _ => false)
    (g := fun input rank =>
      decide (input.2.2.length = rank) &&
        input.2.2.all fun child => decide (child < input.1.2))
    hrank (Primrec.const false) hsome).of_eq ?_
  intro input
  cases input.1.1[input.2.1]? <;> rfl

private theorem nodeShapeWellFormedCode_primrec :
    Primrec₂ fun (context : ShapeContext) (node : RawNode) =>
      RegularTerm.nodeShapeWellFormedCode context.1 context.2 node := by
  apply Primrec₂.mk
  refine (Primrec.sumCasesOn
    (f := fun input : ShapeContext × RawNode => input.2)
    (g := fun _ (_ : ℕ) => true)
    (h := fun input app =>
      match input.1.1[app.1]? with
      | none => false
      | some rank =>
          decide (app.2.length = rank) &&
            app.2.all fun child => decide (child < input.1.2))
    Primrec.snd (Primrec₂.mk (Primrec.const true)) (by
      apply Primrec₂.mk
      exact applicationShapeWellFormedCode_primrec.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd)).of_eq ?_
  intro input
  cases input.2 <;> rfl

/-- Global runtime shape checking is primitive recursive. -/
public theorem shapeWellFormedCode_primrec :
    Primrec₂ fun (ranks : List ℕ) (term : RegularTerm) =>
      term.shapeWellFormedCode ranks := by
  apply Primrec₂.mk
  let Input := List ℕ × RegularTerm
  have hnodeCount : Primrec fun input : Input => input.2.nodes.length :=
    Primrec.list_length.comp (nodes_primrec.comp Primrec.snd)
  have hrootBound : Primrec fun input : Input =>
      decide (input.2.root < input.2.nodes.length) :=
    Primrec.nat_lt.decide.comp
      (root_primrec.comp Primrec.snd) hnodeCount
  have htest : Primrec₂ fun (input : Input) (node : RawNode) =>
      nodeShapeWellFormedCode input.1 input.2.nodes.length node := by
    apply Primrec₂.mk
    exact nodeShapeWellFormedCode_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (hnodeCount.comp Primrec.fst))
      Primrec.snd
  have hnodes : Primrec fun input : Input =>
      input.2.nodes.all
        (nodeShapeWellFormedCode input.1 input.2.nodes.length) :=
    list_all_primrec (nodes_primrec.comp Primrec.snd) htest
  exact Primrec.and.comp hrootBound hnodes

private def groundNodeInSupportCode
    (input : RegularTerm × List ℕ) (i : ℕ) : Bool :=
  match input.1.nodeAt? i with
  | some (.inr (_, children)) =>
      children.all fun child => decide (child ∈ input.2)
  | _ => false

private def applicationGroundInSupportCode
    (input : RegularTerm × List ℕ) (app : ℕ × List ℕ) : Bool :=
  app.2.all fun child => decide (child ∈ input.2)

private theorem applicationGroundInSupportCode_primrec :
    Primrec₂ applicationGroundInSupportCode := by
  apply Primrec₂.mk
  exact childrenInSupportCode_primrec.comp
    (Primrec.snd.comp Primrec.snd)
    (Primrec.snd.comp Primrec.fst)

private def rawNodeGroundInSupportCode
    (input : RegularTerm × List ℕ) : RawNode → Bool
  | .inl _ => false
  | .inr app => applicationGroundInSupportCode input app

private theorem rawNodeGroundInSupportCode_primrec :
    Primrec₂ rawNodeGroundInSupportCode := by
  apply Primrec₂.mk
  refine (Primrec.sumCasesOn
    (f := fun input : (RegularTerm × List ℕ) × RawNode => input.2)
    (g := fun _ (_ : ℕ) => false)
    (h := fun input app => applicationGroundInSupportCode input.1 app)
    Primrec.snd (Primrec₂.mk (Primrec.const false)) (by
      apply Primrec₂.mk
      exact applicationGroundInSupportCode_primrec.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd)).of_eq ?_
  intro input
  cases input.2 <;> rfl

private theorem groundNodeInSupportCode_primrec :
    Primrec₂ groundNodeInSupportCode := by
  apply Primrec₂.mk
  let Input := (RegularTerm × List ℕ) × ℕ
  have hnode : Primrec fun input : Input => input.1.1.nodeAt? input.2 :=
    nodeAt?_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  refine (Primrec.option_casesOn
    (o := fun input : Input => input.1.1.nodeAt? input.2)
    (f := fun _ => false)
    (g := fun input node => rawNodeGroundInSupportCode input.1 node)
    hnode (Primrec.const false) (by
      apply Primrec₂.mk
      exact rawNodeGroundInSupportCode_primrec.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd)).of_eq ?_
  intro input
  cases h : input.1.1.nodeAt? input.2 with
  | none => simp [groundNodeInSupportCode, h]
  | some node =>
      cases node <;> simp [groundNodeInSupportCode,
        rawNodeGroundInSupportCode, h, applicationGroundInSupportCode]

/-- Checking a proposed finite ground support is primitive recursive. -/
public theorem groundWitnessCode_primrec :
    Primrec₂ (RegularTerm.groundWitnessCode :
      RegularTerm → List ℕ → Bool) := by
  apply Primrec₂.mk
  let Input := RegularTerm × List ℕ
  have hrootMem : Primrec fun input : Input =>
      decide (input.1.root ∈ input.2) :=
    nat_mem_list_primrec.comp Primrec.snd
      (root_primrec.comp Primrec.fst)
  have hnodes : Primrec fun input : Input =>
      input.2.all (groundNodeInSupportCode input) :=
    list_all_primrec Primrec.snd groundNodeInSupportCode_primrec
  exact Primrec.and.comp hrootMem hnodes

/-- The executable reachable-groundness test is primitive recursive. -/
public theorem groundCode_primrec :
    Primrec₂ fun (ranks : List ℕ) (term : RegularTerm) =>
      term.groundCode ranks := by
  apply Primrec₂.mk
  let Input := List ℕ × RegularTerm
  have hshape : Primrec fun input : Input =>
      input.2.shapeWellFormedCode input.1 := by
    exact shapeWellFormedCode_primrec.comp Primrec.fst Primrec.snd
  have hrange : Primrec fun input : Input =>
      List.range input.2.nodes.length := by
    exact Primrec.list_range.comp
      (Primrec.list_length.comp (nodes_primrec.comp Primrec.snd))
  have hsublists : Primrec fun input : Input =>
      (List.range input.2.nodes.length).sublists' :=
    list_sublists_primrec.comp hrange
  have hwitness : Primrec₂ fun (input : Input) (support : List ℕ) =>
      input.2.groundWitnessCode support := by
    apply Primrec₂.mk
    exact groundWitnessCode_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hany : Primrec fun input : Input =>
      (List.range input.2.nodes.length).sublists'.any
        input.2.groundWitnessCode :=
    list_any_primrec hsublists hwitness
  exact Primrec.and.comp hshape hany

end RegularTerm

end DCFEquivalence
