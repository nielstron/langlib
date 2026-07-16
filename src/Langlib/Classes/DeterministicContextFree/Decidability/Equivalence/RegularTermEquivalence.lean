module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FirstOrderGrammar
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Sublists

@[expose]
public section

/-!
# Equality of regular terms represented by finite graphs

`RegularTerm` has a deliberately intensional `DecidableEq` instance: it compares
the two finite graph codes.  The first-order-grammar equivalence proof instead
needs equality of the (possibly infinite) trees denoted by those codes.  This
file keeps the two notions separate.

`UnfoldingEquivalent` is pointed graph bisimilarity.  Variables must have the
same index, applications must have the same symbol, and their ordered child
lists must be related pointwise.  A missing node is observable as a stuck node;
this makes the definition total on raw codes.  The intended grammar layer uses
only well-formed terms, where missing nodes are unreachable.
-/

namespace DCFEquivalence

namespace RegularTerm

@[expose] public def RawCompatible (R : ℕ → ℕ → Prop) :
    Option RawNode → Option RawNode → Prop
  | none, none => True
  | some (.inl x), some (.inl y) => x = y
  | some (.inr (X, children)), some (.inr (Y, children')) =>
      X = Y ∧ List.Forall₂ R children children'
  | _, _ => False

/-- Local compatibility of two graph nodes with respect to a proposed relation
between their child references. -/
@[expose] public def NodeCompatible (left right : RegularTerm)
    (R : ℕ → ℕ → Prop) (i j : ℕ) : Prop :=
  RawCompatible R (left.nodeAt? i) (right.nodeAt? j)

/-- A relation on node references is a bisimulation when every related pair has
the same variable/application observation and ordered related children. -/
@[expose] public def IsBisimulation (left right : RegularTerm)
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ i j, R i j → left.NodeCompatible right R i j

/-- Two references in two finite graphs denote the same regular tree. -/
@[expose] public def BisimilarAt (left : RegularTerm) (i : ℕ)
    (right : RegularTerm) (j : ℕ) : Prop :=
  ∃ R : ℕ → ℕ → Prop, R i j ∧ left.IsBisimulation right R

/-- Semantic equality of pointed regular terms.  This ignores graph layout and
unreachable garbage. -/
@[expose] public def UnfoldingEquivalent (left right : RegularTerm) : Prop :=
  left.BisimilarAt left.root right right.root

private theorem forall₂_comp
    {R S : ℕ → ℕ → Prop} {xs ys zs : List ℕ}
    (hxy : List.Forall₂ R xs ys) (hyz : List.Forall₂ S ys zs) :
    List.Forall₂ (fun x z => ∃ y, R x y ∧ S y z) xs zs := by
  induction hxy generalizing zs with
  | nil =>
      cases hyz
      exact .nil
  | cons hhead htail ih =>
      cases hyz with
      | cons hhead' htail' =>
          exact .cons ⟨_, hhead, hhead'⟩ (ih htail')

private theorem nodeCompatible_refl (term : RegularTerm) (i : ℕ) :
    term.NodeCompatible term (fun x y => x = y) i i := by
  unfold NodeCompatible
  cases hnode : term.nodeAt? i with
  | none => simp [RawCompatible]
  | some node =>
      cases node with
      | inl x => simp [RawCompatible]
      | inr app =>
          cases app with
          | mk X children =>
              exact ⟨rfl, List.forall₂_refl _⟩

private theorem rawCompatible_flip
    {R : ℕ → ℕ → Prop} {left right : Option RawNode}
    (h : RawCompatible R left right) :
    RawCompatible (fun y x => R x y) right left := by
  cases left with
  | none =>
      cases right <;> simp_all [RawCompatible]
  | some leftNode =>
      cases right with
      | none => simp_all [RawCompatible]
      | some rightNode =>
          cases leftNode with
          | inl x =>
              cases rightNode with
              | inl y => simpa [RawCompatible] using h.symm
              | inr app => simp_all [RawCompatible]
          | inr leftApp =>
              cases rightNode with
              | inl y => simp_all [RawCompatible]
              | inr rightApp =>
                  exact ⟨h.1.symm, h.2.flip⟩

private theorem nodeCompatible_flip
    {left right : RegularTerm} {R : ℕ → ℕ → Prop} {i j : ℕ}
    (h : left.NodeCompatible right R i j) :
    right.NodeCompatible left (fun y x => R x y) j i := by
  exact rawCompatible_flip h

private theorem rawCompatible_comp
    {R S : ℕ → ℕ → Prop}
    {left middle right : Option RawNode}
    (hleft : RawCompatible R left middle)
    (hright : RawCompatible S middle right) :
    RawCompatible (fun x z => ∃ y, R x y ∧ S y z) left right := by
  cases left with
  | none =>
      cases middle with
      | none => cases right <;> simp_all [RawCompatible]
      | some middleNode => simp_all [RawCompatible]
  | some leftNode =>
      cases middle with
      | none => simp_all [RawCompatible]
      | some middleNode =>
          cases right with
          | none => simp_all [RawCompatible]
          | some rightNode =>
              cases leftNode with
              | inl x =>
                  cases middleNode with
                  | inl y =>
                      cases rightNode with
                      | inl z => exact hleft.trans hright
                      | inr app => simp_all [RawCompatible]
                  | inr app => simp_all [RawCompatible]
              | inr leftApp =>
                  cases middleNode with
                  | inl y => simp_all [RawCompatible]
                  | inr middleApp =>
                      cases rightNode with
                      | inl z => simp_all [RawCompatible]
                      | inr rightApp =>
                          exact ⟨hleft.1.trans hright.1,
                            forall₂_comp hleft.2 hright.2⟩

private theorem nodeCompatible_comp
    {left middle right : RegularTerm} {R S : ℕ → ℕ → Prop}
    {i j k : ℕ}
    (hleft : left.NodeCompatible middle R i j)
    (hright : middle.NodeCompatible right S j k) :
    left.NodeCompatible right (fun x z => ∃ y, R x y ∧ S y z) i k := by
  exact rawCompatible_comp hleft hright

/-- Bisimilarity at arbitrary graph references is reflexive. -/
public theorem bisimilarAt_refl (term : RegularTerm) (i : ℕ) :
    term.BisimilarAt i term i := by
  refine ⟨fun left right => left = right, rfl, ?_⟩
  intro left right h
  subst right
  exact nodeCompatible_refl term left

/-- Bisimilarity at arbitrary graph references is symmetric. -/
public theorem BisimilarAt.symm
    {left right : RegularTerm} {i j : ℕ}
    (h : left.BisimilarAt i right j) :
    right.BisimilarAt j left i := by
  obtain ⟨R, hij, hR⟩ := h
  refine ⟨fun rightIndex leftIndex => R leftIndex rightIndex, hij, ?_⟩
  intro rightIndex leftIndex hrel
  exact nodeCompatible_flip (hR leftIndex rightIndex hrel)

/-- Bisimilarity at arbitrary graph references is transitive. -/
public theorem BisimilarAt.trans
    {left middle right : RegularTerm} {i j k : ℕ}
    (hlm : left.BisimilarAt i middle j)
    (hmr : middle.BisimilarAt j right k) :
    left.BisimilarAt i right k := by
  obtain ⟨R, hij, hR⟩ := hlm
  obtain ⟨S, hjk, hS⟩ := hmr
  refine ⟨fun leftIndex rightIndex =>
    ∃ middleIndex, R leftIndex middleIndex ∧ S middleIndex rightIndex,
    ⟨j, hij, hjk⟩, ?_⟩
  rintro leftIndex rightIndex ⟨middleIndex, hleft, hright⟩
  exact nodeCompatible_comp
    (hR leftIndex middleIndex hleft)
    (hS middleIndex rightIndex hright)

/-- Pointed unfolding equivalence is reflexive. -/
@[refl] public theorem unfoldingEquivalent_refl (term : RegularTerm) :
    term.UnfoldingEquivalent term :=
  bisimilarAt_refl term term.root

/-- Pointed unfolding equivalence is symmetric. -/
@[symm] public theorem UnfoldingEquivalent.symm
    {left right : RegularTerm} (h : left.UnfoldingEquivalent right) :
    right.UnfoldingEquivalent left :=
  BisimilarAt.symm h

/-- Pointed unfolding equivalence is transitive. -/
@[trans] public theorem UnfoldingEquivalent.trans
    {left middle right : RegularTerm}
    (hlm : left.UnfoldingEquivalent middle)
    (hmr : middle.UnfoldingEquivalent right) :
    left.UnfoldingEquivalent right :=
  BisimilarAt.trans hlm hmr

/-- `UnfoldingEquivalent` is an equivalence relation independently of raw graph
code equality. -/
public theorem unfoldingEquivalent_equivalence :
    Equivalence UnfoldingEquivalent :=
  ⟨unfoldingEquivalent_refl, UnfoldingEquivalent.symm,
    UnfoldingEquivalent.trans⟩

@[simp] public theorem withRoot_nodes (term : RegularTerm) (i : ℕ) :
    (term.withRoot i).nodes = term.nodes := rfl

@[simp] public theorem withRoot_root (term : RegularTerm) (i : ℕ) :
    (term.withRoot i).root = i := rfl

@[simp] public theorem withRoot_nodeAt? (term : RegularTerm) (i j : ℕ) :
    (term.withRoot i).nodeAt? j = term.nodeAt? j := rfl

/-- Changing the two distinguished roots exposes precisely bisimilarity at the
chosen references. -/
public theorem withRoot_unfoldingEquivalent_iff_bisimilarAt
    (left right : RegularTerm) (i j : ℕ) :
    (left.withRoot i).UnfoldingEquivalent (right.withRoot j) ↔
      left.BisimilarAt i right j := by
  simp only [UnfoldingEquivalent, withRoot_root]
  constructor <;> rintro ⟨R, hroot, hR⟩
  · refine ⟨R, hroot, ?_⟩
    intro leftIndex rightIndex hrel
    simpa only [NodeCompatible, withRoot_nodeAt?] using
      hR leftIndex rightIndex hrel
  · refine ⟨R, hroot, ?_⟩
    intro leftIndex rightIndex hrel
    simpa only [NodeCompatible, withRoot_nodeAt?] using
      hR leftIndex rightIndex hrel

/-- Equivalent application roots have the same symbol and pairwise equivalent
ordered children. -/
public theorem rootApplication?_of_unfoldingEquivalent
    {left right : RegularTerm} (h : left.UnfoldingEquivalent right)
    {X : ℕ} {children : List ℕ}
    (hleft : left.rootApplication? = some (X, children)) :
    ∃ children', right.rootApplication? = some (X, children') ∧
      List.Forall₂ (fun i j => left.BisimilarAt i right j)
        children children' := by
  obtain ⟨R, hroot, hR⟩ := h
  have hlocal := hR left.root right.root hroot
  unfold rootApplication? at hleft
  cases hleftNode : left.rootNode? with
  | none => simp [hleftNode] at hleft
  | some leftNode =>
      cases leftNode with
      | inl x => simp [hleftNode] at hleft
      | inr leftApp =>
          rcases leftApp with ⟨Y, childrenLeft⟩
          simp only [hleftNode, Option.some.injEq, Prod.mk.injEq] at hleft
          rcases hleft with ⟨hYX, hchildren⟩
          subst Y
          subst childrenLeft
          unfold NodeCompatible at hlocal
          have hleftAt : left.nodeAt? left.root =
              some (.inr (X, children)) := by
            simpa only [rootNode?] using hleftNode
          rw [hleftAt] at hlocal
          cases hrightNode : right.nodeAt? right.root with
          | none =>
              simp [RawCompatible, hrightNode] at hlocal
          | some rightNode =>
              rw [hrightNode] at hlocal
              cases rightNode with
              | inl y =>
                  simp [RawCompatible] at hlocal
              | inr rightApp =>
                  rcases rightApp with ⟨Z, childrenRight⟩
                  change X = Z ∧ List.Forall₂ R children childrenRight at hlocal
                  have hsymbol : X = Z := hlocal.1
                  subst Z
                  refine ⟨childrenRight, ?_, hlocal.2.imp ?_⟩
                  · unfold rootApplication? rootNode?
                    simp [hrightNode]
                  · intro i j hij
                    exact ⟨R, hij, hR⟩

/-! ## A finite executable bisimulation test -/

/-- Every reference that can be encountered by starting at the root and
following a graph edge.  Duplicates are harmless and deliberately retained. -/
@[expose] public def references (term : RegularTerm) : List ℕ :=
  term.root :: term.nodes.flatMap fun node =>
    match node with
    | .inl _ => []
    | .inr (_, children) => children

/-- The finite universe of reference pairs relevant to two pointed graphs. -/
@[expose] public def referencePairs (left right : RegularTerm) :
    List (ℕ × ℕ) :=
  left.references.product right.references

/-- Check local compatibility using membership in a finite relation list. -/
@[expose] public def rawCompatibleCode (relation : List (ℕ × ℕ)) :
    Option RawNode → Option RawNode → Bool
  | none, none => true
  | some (.inl x), some (.inl y) => decide (x = y)
  | some (.inr (X, children)), some (.inr (Y, children')) =>
      decide (X = Y) && List.all₂
        (fun child child' => decide ((child, child') ∈ relation))
        children children'
  | _, _ => false

@[expose] public def nodeCompatibleCode (left right : RegularTerm)
    (relation : List (ℕ × ℕ)) (i j : ℕ) : Bool :=
  rawCompatibleCode relation (left.nodeAt? i) (right.nodeAt? j)

/-- Check that every pair stored in a finite relation is locally compatible. -/
@[expose] public def bisimulationCode (left right : RegularTerm)
    (relation : List (ℕ × ℕ)) : Bool :=
  relation.all fun pair =>
    left.nodeCompatibleCode right relation pair.1 pair.2

/-- Brute-force finite decision procedure for pointed graph bisimilarity.

The powerset search is intentionally simple: this layer only needs a transparent
uniform decision procedure, while the substantially harder first-order-grammar
algorithm is developed separately. -/
@[expose] public def unfoldingEquivalentCode
    (left right : RegularTerm) : Bool :=
  (left.referencePairs right).sublists.any fun relation =>
    decide ((left.root, right.root) ∈ relation) &&
      left.bisimulationCode right relation

public theorem nodeCompatibleCode_eq_true_iff
    (left right : RegularTerm) (relation : List (ℕ × ℕ)) (i j : ℕ) :
    left.nodeCompatibleCode right relation i j = true ↔
      left.NodeCompatible right
        (fun child child' => (child, child') ∈ relation) i j := by
  unfold nodeCompatibleCode NodeCompatible
  cases left.nodeAt? i with
  | none => cases right.nodeAt? j <;> simp [rawCompatibleCode, RawCompatible]
  | some leftNode =>
      cases right.nodeAt? j with
      | none => simp [rawCompatibleCode, RawCompatible]
      | some rightNode =>
          cases leftNode with
          | inl x =>
              cases rightNode <;> simp [rawCompatibleCode, RawCompatible]
          | inr leftApp =>
              cases rightNode with
              | inl y => simp [rawCompatibleCode, RawCompatible]
              | inr rightApp =>
                  simp [rawCompatibleCode, RawCompatible, List.all₂_eq_true]

public theorem bisimulationCode_eq_true_iff
    (left right : RegularTerm) (relation : List (ℕ × ℕ)) :
    left.bisimulationCode right relation = true ↔
      left.IsBisimulation right
        (fun i j => (i, j) ∈ relation) := by
  simp only [bisimulationCode, List.all_eq_true,
    nodeCompatibleCode_eq_true_iff, IsBisimulation]
  constructor
  · intro h i j hij
    exact h (i, j) hij
  · intro h pair hpair
    exact h pair.1 pair.2 hpair

public theorem unfoldingEquivalentCode_eq_true_iff_exists_relation
    (left right : RegularTerm) :
    left.unfoldingEquivalentCode right = true ↔
      ∃ relation ∈ (left.referencePairs right).sublists,
        (left.root, right.root) ∈ relation ∧
          left.IsBisimulation right
            (fun i j => (i, j) ∈ relation) := by
  simp [unfoldingEquivalentCode, bisimulationCode_eq_true_iff]

@[simp] public theorem root_mem_references (term : RegularTerm) :
    term.root ∈ term.references := by
  simp [references]

public theorem child_mem_references
    {term : RegularTerm} {i X : ℕ} {children : List ℕ} {child : ℕ}
    (hnode : term.nodeAt? i = some (.inr (X, children)))
    (hchild : child ∈ children) :
    child ∈ term.references := by
  have happ : (.inr (X, children) : RawNode) ∈ term.nodes := by
    exact List.mem_of_getElem? hnode
  simp only [references, List.mem_cons]
  right
  simp only [List.mem_flatMap]
  exact ⟨.inr (X, children), happ, by simpa using hchild⟩

private theorem forall₂_restrict_of_mem
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop}
    {xs ys : List ℕ} (h : List.Forall₂ R xs ys)
    (hleft : ∀ x ∈ xs, P x) (hright : ∀ y ∈ ys, Q y) :
    List.Forall₂ (fun x y => R x y ∧ P x ∧ Q y) xs ys := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      refine .cons ⟨hhead, hleft _ (by simp), hright _ (by simp)⟩ ?_
      exact ih (fun x hx => hleft x (by simp [hx]))
        (fun y hy => hright y (by simp [hy]))

private theorem rawCompatible_mono
    {R S : ℕ → ℕ → Prop} {left right : Option RawNode}
    (hRS : ∀ i j, R i j → S i j)
    (h : RawCompatible R left right) :
    RawCompatible S left right := by
  cases left with
  | none => cases right <;> simp_all [RawCompatible]
  | some leftNode =>
      cases right with
      | none => simp_all [RawCompatible]
      | some rightNode =>
          cases leftNode with
          | inl x => cases rightNode <;> simp_all [RawCompatible]
          | inr leftApp =>
              cases rightNode with
              | inl y => simp_all [RawCompatible]
              | inr rightApp => exact ⟨h.1, h.2.imp hRS⟩

private theorem nodeCompatible_mono
    {left right : RegularTerm} {R S : ℕ → ℕ → Prop} {i j : ℕ}
    (hRS : ∀ i j, R i j → S i j)
    (h : left.NodeCompatible right R i j) :
    left.NodeCompatible right S i j :=
  rawCompatible_mono hRS h

private theorem rawCompatible_restrict_of_children
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop}
    {left right : Option RawNode}
    (h : RawCompatible R left right)
    (hleft : ∀ X children, left = some (.inr (X, children)) →
      ∀ child ∈ children, P child)
    (hright : ∀ X children, right = some (.inr (X, children)) →
      ∀ child ∈ children, Q child) :
    RawCompatible (fun child child' =>
      R child child' ∧ P child ∧ Q child') left right := by
  cases left with
  | none => cases right <;> simp_all [RawCompatible]
  | some leftNode =>
      cases right with
      | none => simp_all [RawCompatible]
      | some rightNode =>
          cases leftNode with
          | inl x => cases rightNode <;> simp_all [RawCompatible]
          | inr leftApp =>
              cases rightNode with
              | inl y => simp_all [RawCompatible]
              | inr rightApp =>
                  rcases leftApp with ⟨X, children⟩
                  rcases rightApp with ⟨Y, children'⟩
                  refine ⟨h.1, forall₂_restrict_of_mem h.2 ?_ ?_⟩
                  · exact hleft X children rfl
                  · exact hright Y children' rfl

private theorem nodeCompatible_restrict
    {left right : RegularTerm} {R : ℕ → ℕ → Prop} {i j : ℕ}
    (h : left.NodeCompatible right R i j) :
    left.NodeCompatible right
      (fun child child' =>
        R child child' ∧ child ∈ left.references ∧
          child' ∈ right.references) i j := by
  apply rawCompatible_restrict_of_children h
  · intro X children hnode child hchild
    exact child_mem_references hnode hchild
  · intro X children hnode child hchild
    exact child_mem_references hnode hchild

/-- The finite checker decides semantic pointed unfolding equivalence, not raw
graph-code equality. -/
public theorem unfoldingEquivalentCode_eq_true_iff
    (left right : RegularTerm) :
    left.unfoldingEquivalentCode right = true ↔
      left.UnfoldingEquivalent right := by
  rw [unfoldingEquivalentCode_eq_true_iff_exists_relation]
  constructor
  · rintro ⟨relation, _hrelation, hroot, hbisim⟩
    exact ⟨fun i j => (i, j) ∈ relation, hroot, hbisim⟩
  · rintro ⟨R, hroot, hbisim⟩
    classical
    let relation := (left.referencePairs right).filter fun pair =>
      R pair.1 pair.2
    refine ⟨relation, List.mem_sublists.mpr (List.filter_sublist), ?_, ?_⟩
    · simp [relation, referencePairs, hroot]
    · intro i j hij
      have hijR : R i j := of_decide_eq_true (List.mem_filter.mp hij).2
      have hlocal := nodeCompatible_restrict (hbisim i j hijR)
      apply nodeCompatible_mono (h := hlocal)
      intro child child' hchild
      exact List.mem_filter.mpr ⟨by
        simpa [referencePairs] using ⟨hchild.2.1, hchild.2.2⟩,
        decide_eq_true hchild.1⟩

/-- Semantic equality of regular terms is decidable by a finite search over
relations on their graph references. -/
public instance unfoldingEquivalentDecidable (left right : RegularTerm) :
    Decidable (left.UnfoldingEquivalent right) :=
  decidable_of_iff (left.unfoldingEquivalentCode right = true)
    (unfoldingEquivalentCode_eq_true_iff left right)

/-! ## Congruence of graph substitution -/

private theorem foldl_appendArgumentNodes_output
    (arguments : List RegularTerm) (offset : ℕ) (out : List RawNode) :
    (arguments.foldl appendArgumentNodes (offset, out)).2 =
      out ++ (arguments.foldl appendArgumentNodes (offset, [])).2 := by
  induction arguments generalizing offset out with
  | nil => simp
  | cons argument arguments ih =>
      simp only [List.foldl_cons, appendArgumentNodes]
      rw [ih]
      simp only [List.nil_append]
      rw [ih (out := argument.nodes.map (shiftNode offset))]
      simp [List.append_assoc]

public theorem appendArguments_cons (offset : ℕ)
    (argument : RegularTerm) (arguments : List RegularTerm) :
    appendArguments offset (argument :: arguments) =
      argument.nodes.map (shiftNode offset) ++
        appendArguments (offset + argument.nodes.length) arguments := by
  unfold appendArguments
  simp only [List.foldl_cons, appendArgumentNodes]
  rw [foldl_appendArgumentNodes_output]
  simp

@[simp] public theorem argumentOffset_zero (base : ℕ)
    (arguments : List RegularTerm) :
    argumentOffset base arguments 0 = base := rfl

private theorem natRec_const_succ_initial {State : Type}
    (step : State → State) (initial : State) (n : ℕ) :
    Nat.rec (motive := fun _ => State) initial
        (fun _ state => step state) (n + 1) =
      Nat.rec (motive := fun _ => State) (step initial)
        (fun _ state => step state) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step (Nat.rec (motive := fun _ => State) initial
          (fun _ state => step state) (n + 1)) =
        step (Nat.rec (motive := fun _ => State) (step initial)
          (fun _ state => step state) n)
      exact congrArg step ih

public theorem argumentOffset_cons_succ (base x : ℕ)
    (argument : RegularTerm) (arguments : List RegularTerm) :
    argumentOffset base (argument :: arguments) (x + 1) =
      argumentOffset (base + argument.nodes.length) arguments x := by
  unfold argumentOffset
  rw [natRec_const_succ_initial]
  rfl

private theorem appendArguments_getElem?_of_getElem?
    (arguments : List RegularTerm) (base : ℕ) (out : List RawNode)
    (hout : out.length = base) {x : ℕ} {argument : RegularTerm}
    {i : ℕ} {node : RawNode}
    (hargument : arguments[x]? = some argument)
    (hnode : argument.nodes[i]? = some node) :
    (out ++ appendArguments base arguments)[
        argumentOffset base arguments x + i]? =
      some (shiftNode (argumentOffset base arguments x) node) := by
  induction arguments generalizing base out x with
  | nil => simp at hargument
  | cons first rest ih =>
      cases x with
      | zero =>
          have hfirst : first = argument := by simpa using hargument
          subst first
          rw [argumentOffset_zero, appendArguments_cons,
            ← List.append_assoc]
          have hi : i < argument.nodes.length :=
            (List.getElem?_eq_some_iff.mp hnode).choose
          rw [List.getElem?_append_left (by simp [hout]; omega),
            List.getElem?_append_right (by simp [hout])]
          simp [hout, List.getElem?_map, hnode]
      | succ x =>
          have hrest : rest[x]? = some argument := by
            simpa using hargument
          rw [argumentOffset_cons_succ, appendArguments_cons,
            ← List.append_assoc]
          apply ih (base := base + first.nodes.length)
            (out := out ++ first.nodes.map (shiftNode base))
              (x := x) (hargument := hrest)
          simp [hout]

/-- The root and every application edge of a raw term graph are in range. -/
@[expose] public def ReferenceClosed (term : RegularTerm) : Prop :=
  term.root < term.nodes.length ∧
    ∀ i X children, term.nodeAt? i = some (.inr (X, children)) →
      ∀ child ∈ children, child < term.nodes.length

/-- Reachable-ground runtime graphs are globally reference closed because the
runtime shape check validates every application edge, including unreachable
garbage retained by substitution. -/
public theorem referenceClosed_of_ground
    {ranks : List ℕ} {term : RegularTerm} (h : term.Ground ranks) :
    term.ReferenceClosed := by
  have hshape := h.1
  unfold ShapeWellFormed shapeWellFormedCode at hshape
  rw [Bool.and_eq_true] at hshape
  refine ⟨of_decide_eq_true hshape.1, ?_⟩
  intro i X children hnode child hchild
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hnodeShape := (List.all_eq_true.mp hshape.2) _ hmem
  unfold nodeShapeWellFormedCode at hnodeShape
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hnodeShape
  | some rank =>
      simp only [hrank] at hnodeShape
      rw [Bool.and_eq_true] at hnodeShape
      exact of_decide_eq_true
        ((List.all_eq_true.mp hnodeShape.2) child hchild)

/-- Ranked well-formedness implies that every reference reachable through the
raw graph table is in range. -/
public theorem referenceClosed_of_wellFormed
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (h : term.WellFormed ranks variableBound) :
    term.ReferenceClosed := by
  unfold WellFormed wellFormedCode at h
  rw [Bool.and_eq_true] at h
  have hparts := h
  refine ⟨of_decide_eq_true hparts.1, ?_⟩
  intro i X children hnode child hchild
  have hmem : (.inr (X, children) : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hnodeWellFormed :=
    (List.all_eq_true.mp hparts.2) _ hmem
  unfold nodeWellFormedCode at hnodeWellFormed
  cases hrank : ranks[X]? with
  | none => simp [hrank] at hnodeWellFormed
  | some rank =>
      simp only [hrank] at hnodeWellFormed
      rw [Bool.and_eq_true] at hnodeWellFormed
      have hchildren := hnodeWellFormed.2
      exact of_decide_eq_true ((List.all_eq_true.mp hchildren) child hchild)

public theorem withRoot_referenceClosed
    {term : RegularTerm} (hterm : term.ReferenceClosed) {i : ℕ}
    (hi : i < term.nodes.length) :
    (term.withRoot i).ReferenceClosed := by
  refine ⟨by simpa using hi, ?_⟩
  intro j X children hnode child hchild
  apply hterm.2 j X children (by simpa using hnode) child hchild

public theorem rootApplication_children_lt
    {term : RegularTerm} (hterm : term.ReferenceClosed)
    {X : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (X, children)) :
    ∀ child ∈ children, child < term.nodes.length := by
  unfold rootApplication? at hroot
  cases hnode : term.rootNode? with
  | none => simp [hnode] at hroot
  | some node =>
      cases node with
      | inl x => simp [hnode] at hroot
      | inr app =>
          rcases app with ⟨Y, children'⟩
          simp only [hnode, Option.some.injEq, Prod.mk.injEq] at hroot
          rcases hroot with ⟨hYX, hchildren⟩
          subst Y
          subst children'
          apply hterm.2 term.root X children
          simpa only [rootNode?] using hnode

private theorem forall₂_getElem?_some
    {R : RegularTerm → RegularTerm → Prop}
    {left right : List RegularTerm} (h : List.Forall₂ R left right)
    {x : ℕ} {leftArgument : RegularTerm}
    (hleft : left[x]? = some leftArgument) :
    ∃ rightArgument, right[x]? = some rightArgument ∧
      R leftArgument rightArgument := by
  induction h generalizing x with
  | nil => simp at hleft
  | cons hhead htail ih =>
      cases x with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hleft
          subst leftArgument
          exact ⟨_, rfl, hhead⟩
      | succ x =>
          exact ih (by simpa using hleft)

private theorem forall₂_getElem?_none
    {R : RegularTerm → RegularTerm → Prop}
    {left right : List RegularTerm} (h : List.Forall₂ R left right)
    {x : ℕ} (hleft : left[x]? = none) :
    right[x]? = none := by
  induction h generalizing x with
  | nil => simp
  | cons hhead htail ih =>
      cases x with
      | zero => simp at hleft
      | succ x => exact ih (by simpa using hleft)

public theorem instantiate_nodeAt?_rhs (rhs : RegularTerm)
    (arguments : List RegularTerm) {i : ℕ}
    (hi : i < rhs.nodes.length) :
    (rhs.instantiate arguments).nodeAt? i =
      (rhs.nodeAt? i).map (rhs.instantiateNode arguments) := by
  unfold instantiate nodeAt? nodes
  rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map]

public theorem instantiate_nodeAt?_argument (rhs : RegularTerm)
    (arguments : List RegularTerm) {x : ℕ} {argument : RegularTerm}
    {i : ℕ} {node : RawNode}
    (hargument : arguments[x]? = some argument)
    (hnode : argument.nodeAt? i = some node) :
    (rhs.instantiate arguments).nodeAt?
        (argumentOffset rhs.nodes.length arguments x + i) =
      some (shiftNode
        (argumentOffset rhs.nodes.length arguments x) node) := by
  unfold instantiate nodeAt? nodes at ⊢
  apply appendArguments_getElem?_of_getElem?
    (arguments := arguments) (base := rhs.nodes.length)
    (out := rhs.nodes.map (rhs.instantiateNode arguments))
      (x := x) (hout := by simp) (hargument := hargument)
      (hnode := hnode)

/-- Candidate bisimulation used for two instantiations of the same RHS.  RHS
nodes are related identically; copied argument nodes are related through their
own unfolding semantics, with independently computed offsets. -/
@[expose] public def InstantiationRelation (rhs : RegularTerm)
    (leftArguments rightArguments : List RegularTerm) (i j : ℕ) : Prop :=
  (i < rhs.nodes.length ∧ j = i) ∨
    ∃ x leftArgument rightArgument leftIndex rightIndex,
      leftArguments[x]? = some leftArgument ∧
      rightArguments[x]? = some rightArgument ∧
      leftIndex < leftArgument.nodes.length ∧
      rightIndex < rightArgument.nodes.length ∧
      leftArgument.BisimilarAt leftIndex rightArgument rightIndex ∧
      i = argumentOffset rhs.nodes.length leftArguments x + leftIndex ∧
      j = argumentOffset rhs.nodes.length rightArguments x + rightIndex

private theorem resolveRHSRef_instantiationRelation
    {rhs : RegularTerm} {leftArguments rightArguments : List RegularTerm}
    (harguments : List.Forall₂ UnfoldingEquivalent
      leftArguments rightArguments)
    (hleftClosed : ∀ argument ∈ leftArguments, argument.ReferenceClosed)
    (hrightClosed : ∀ argument ∈ rightArguments, argument.ReferenceClosed)
    {i : ℕ} (hi : i < rhs.nodes.length) :
    InstantiationRelation rhs leftArguments rightArguments
      (rhs.resolveRHSRef leftArguments i)
      (rhs.resolveRHSRef rightArguments i) := by
  unfold resolveRHSRef
  cases hnode : rhs.nodeAt? i with
  | none =>
      exact Or.inl ⟨hi, rfl⟩
  | some node =>
      cases node with
      | inr app =>
          exact Or.inl ⟨hi, rfl⟩
      | inl x =>
          cases hleftArgument : leftArguments[x]? with
          | none =>
              have hrightArgument : rightArguments[x]? = none :=
                forall₂_getElem?_none harguments hleftArgument
              simp only [argumentRoot?, hleftArgument, hrightArgument,
                Option.map_none, Option.getD_none]
              exact Or.inl ⟨hi, rfl⟩
          | some leftArgument =>
              obtain ⟨rightArgument, hrightArgument, hequivalent⟩ :=
                forall₂_getElem?_some harguments hleftArgument
              have hleftMem : leftArgument ∈ leftArguments :=
                List.mem_of_getElem? hleftArgument
              have hrightMem : rightArgument ∈ rightArguments :=
                List.mem_of_getElem? hrightArgument
              have hleftRoot := (hleftClosed leftArgument hleftMem).1
              have hrightRoot := (hrightClosed rightArgument hrightMem).1
              right
              refine ⟨x, leftArgument, rightArgument,
                leftArgument.root, rightArgument.root,
                hleftArgument, hrightArgument, hleftRoot, hrightRoot,
                hequivalent, ?_, ?_⟩
              · simp [argumentRoot?, hleftArgument]
              · simp [argumentRoot?, hrightArgument]

private theorem forall₂_map_both
    {R S : ℕ → ℕ → Prop} {left right : List ℕ}
    (f g : ℕ → ℕ) (h : List.Forall₂ R left right)
    (hmap : ∀ i j, R i j → S (f i) (g j)) :
    List.Forall₂ S (left.map f) (right.map g) := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih => exact .cons (hmap _ _ hhead) ih

private theorem forall₂_map_same
    {R : ℕ → ℕ → Prop} (f g : ℕ → ℕ)
    (values : List ℕ) (h : ∀ value ∈ values, R (f value) (g value)) :
    List.Forall₂ R (values.map f) (values.map g) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun child hchild => h child (by simp [hchild]))

private theorem instantiationRelation_isBisimulation
    {rhs : RegularTerm} {leftArguments rightArguments : List RegularTerm}
    (hrhsClosed : rhs.ReferenceClosed)
    (harguments : List.Forall₂ UnfoldingEquivalent
      leftArguments rightArguments)
    (hleftClosed : ∀ argument ∈ leftArguments, argument.ReferenceClosed)
    (hrightClosed : ∀ argument ∈ rightArguments, argument.ReferenceClosed) :
    (rhs.instantiate leftArguments).IsBisimulation
      (rhs.instantiate rightArguments)
      (InstantiationRelation rhs leftArguments rightArguments) := by
  intro i j hij
  rcases hij with hrhs | hargument
  · rcases hrhs with ⟨hi, hji⟩
    subst j
    unfold NodeCompatible
    rw [instantiate_nodeAt?_rhs rhs leftArguments hi,
      instantiate_nodeAt?_rhs rhs rightArguments hi]
    cases hnode : rhs.nodeAt? i with
    | none =>
        trivial
    | some node =>
        cases node with
        | inl x => simp [instantiateNode, RawCompatible]
        | inr app =>
            rcases app with ⟨X, children⟩
            simp only [Option.map_some, instantiateNode, RawCompatible]
            refine ⟨True.intro, forall₂_map_same
              (rhs.resolveRHSRef leftArguments)
              (rhs.resolveRHSRef rightArguments) children ?_⟩
            intro child hchild
            exact resolveRHSRef_instantiationRelation harguments
              hleftClosed hrightClosed
              (hrhsClosed.2 i X children hnode child hchild)
  · rcases hargument with
      ⟨x, leftArgument, rightArgument, leftIndex, rightIndex,
        hleftArgument, hrightArgument, hleftBound, hrightBound,
        hequivalent, rfl, rfl⟩
    have hleftMem : leftArgument ∈ leftArguments :=
      List.mem_of_getElem? hleftArgument
    have hrightMem : rightArgument ∈ rightArguments :=
      List.mem_of_getElem? hrightArgument
    have hleftReferenceClosed := hleftClosed leftArgument hleftMem
    have hrightReferenceClosed := hrightClosed rightArgument hrightMem
    let leftNode : RawNode := leftArgument.nodes[leftIndex]
    let rightNode : RawNode := rightArgument.nodes[rightIndex]
    have hleftNode : leftArgument.nodeAt? leftIndex = some leftNode := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hleftBound, rfl⟩
    have hrightNode : rightArgument.nodeAt? rightIndex = some rightNode := by
      unfold nodeAt?
      rw [List.getElem?_eq_some_iff]
      exact ⟨hrightBound, rfl⟩
    obtain ⟨R, hindex, hR⟩ := hequivalent
    have hlocal := hR leftIndex rightIndex hindex
    unfold NodeCompatible at hlocal ⊢
    rw [hleftNode, hrightNode] at hlocal
    rw [instantiate_nodeAt?_argument rhs leftArguments
        hleftArgument hleftNode,
      instantiate_nodeAt?_argument rhs rightArguments
        hrightArgument hrightNode]
    cases hleftKind : leftNode with
    | inl leftVariable =>
        cases hrightKind : rightNode with
        | inl rightVariable =>
            simpa [hleftKind, hrightKind, shiftNode, RawCompatible] using hlocal
        | inr rightApp =>
            simp [hleftKind, hrightKind, RawCompatible] at hlocal
    | inr leftApp =>
        cases hrightKind : rightNode with
        | inl rightVariable =>
            simp [hleftKind, hrightKind, RawCompatible] at hlocal
        | inr rightApp =>
            rcases leftApp with ⟨X, leftChildren⟩
            rcases rightApp with ⟨Y, rightChildren⟩
            have hleftAppNode : leftArgument.nodeAt? leftIndex =
                some (.inr (X, leftChildren)) :=
              hleftNode.trans (congrArg some hleftKind)
            have hrightAppNode : rightArgument.nodeAt? rightIndex =
                some (.inr (Y, rightChildren)) :=
              hrightNode.trans (congrArg some hrightKind)
            simp only [hleftKind, hrightKind, RawCompatible] at hlocal
            simp only [shiftNode, RawCompatible]
            have hchildren : List.Forall₂
                (fun leftChild rightChild =>
                  R leftChild rightChild ∧
                    leftChild < leftArgument.nodes.length ∧
                    rightChild < rightArgument.nodes.length)
                leftChildren rightChildren :=
              forall₂_restrict_of_mem
                (P := fun child => child < leftArgument.nodes.length)
                (Q := fun child => child < rightArgument.nodes.length)
                hlocal.2
                (fun child hchild =>
                  hleftReferenceClosed.2 leftIndex X leftChildren
                    hleftAppNode child hchild)
                (fun child hchild =>
                  hrightReferenceClosed.2 rightIndex Y rightChildren
                    hrightAppNode child hchild)
            refine ⟨hlocal.1, forall₂_map_both
              (argumentOffset rhs.nodes.length leftArguments x + ·)
              (argumentOffset rhs.nodes.length rightArguments x + ·)
              hchildren ?_⟩
            intro leftChild rightChild hchildren
            right
            exact ⟨x, leftArgument, rightArgument,
              leftChild, rightChild, hleftArgument, hrightArgument,
              hchildren.2.1, hchildren.2.2,
              ⟨R, hchildren.1, hR⟩, rfl, rfl⟩

/-- Instantiating one reference-closed RHS by pointwise equivalent,
reference-closed argument graphs preserves the denoted regular term, even when
corresponding argument graph codes have different sizes. -/
public theorem instantiate_unfoldingEquivalent
    {rhs : RegularTerm} {leftArguments rightArguments : List RegularTerm}
    (hrhsClosed : rhs.ReferenceClosed)
    (harguments : List.Forall₂ UnfoldingEquivalent
      leftArguments rightArguments)
    (hleftClosed : ∀ argument ∈ leftArguments, argument.ReferenceClosed)
    (hrightClosed : ∀ argument ∈ rightArguments, argument.ReferenceClosed) :
    (rhs.instantiate leftArguments).UnfoldingEquivalent
      (rhs.instantiate rightArguments) := by
  refine ⟨InstantiationRelation rhs leftArguments rightArguments, ?_,
    instantiationRelation_isBisimulation hrhsClosed harguments
      hleftClosed hrightClosed⟩
  change InstantiationRelation rhs leftArguments rightArguments
    (rhs.resolveRHSRef leftArguments rhs.root)
    (rhs.resolveRHSRef rightArguments rhs.root)
  exact resolveRHSRef_instantiationRelation harguments
    hleftClosed hrightClosed hrhsClosed.1

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private theorem map_withRoot_forall₂
    {left right : RegularTerm} {children children' : List ℕ}
    (h : List.Forall₂ (fun i j => left.BisimilarAt i right j)
      children children') :
    List.Forall₂ RegularTerm.UnfoldingEquivalent
      (children.map left.withRoot) (children'.map right.withRoot) := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      exact .cons
        ((RegularTerm.withRoot_unfoldingEquivalent_iff_bisimilarAt
          left right _ _).2 hhead) ih

private theorem map_withRoot_referenceClosed
    {term : RegularTerm} {children : List ℕ}
    (hterm : term.ReferenceClosed)
    (hchildren : ∀ child ∈ children, child < term.nodes.length) :
    ∀ argument ∈ children.map term.withRoot, argument.ReferenceClosed := by
  intro argument hargument
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hargument
  exact RegularTerm.withRoot_referenceClosed hterm
    (hchildren child hchild)

/-- Ordinary root rewriting respects unfolding equivalence on
reference-closed source graphs when selected rule RHSs are reference closed. -/
public theorem rootRewrite?_respects_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} {a : Action}
    {left right : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    (hleftClosed : left.ReferenceClosed)
    (hrightClosed : right.ReferenceClosed)
    (hrulesClosed : ∀ X action rhs,
      g.ruleLookup X action = some rhs → rhs.ReferenceClosed) :
    Option.Rel RegularTerm.UnfoldingEquivalent
      (g.rootRewrite? a left) (g.rootRewrite? a right) := by
  cases hleftRoot : left.rootApplication? with
  | none =>
      have hrightRoot : right.rootApplication? = none := by
        cases hright : right.rootApplication? with
        | none => rfl
        | some app =>
            rcases app with ⟨X, children⟩
            obtain ⟨children', hleftSome, _⟩ :=
              RegularTerm.rootApplication?_of_unfoldingEquivalent
                hequivalent.symm hright
            simp [hleftRoot] at hleftSome
      unfold rootRewrite?
      rw [hleftRoot, hrightRoot]
      exact .none
  | some app =>
      rcases app with ⟨X, children⟩
      obtain ⟨children', hrightRoot, hchildren⟩ :=
        RegularTerm.rootApplication?_of_unfoldingEquivalent
          hequivalent hleftRoot
      unfold rootRewrite?
      rw [hleftRoot, hrightRoot]
      change Option.Rel RegularTerm.UnfoldingEquivalent
        ((g.ruleLookup X a).map fun rhs =>
          rhs.instantiate (children.map left.withRoot))
        ((g.ruleLookup X a).map fun rhs =>
          rhs.instantiate (children'.map right.withRoot))
      cases hrule : g.ruleLookup X a with
      | none => exact .none
      | some rhs =>
          apply Option.Rel.some
          apply RegularTerm.instantiate_unfoldingEquivalent
            (hrulesClosed X a rhs hrule)
            (map_withRoot_forall₂ hchildren)
          · exact map_withRoot_referenceClosed hleftClosed
              (RegularTerm.rootApplication_children_lt hleftClosed hleftRoot)
          · exact map_withRoot_referenceClosed hrightClosed
              (RegularTerm.rootApplication_children_lt hrightClosed hrightRoot)

private theorem privateStep?_respects_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} {x : ℕ}
    {left right : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right) :
    Option.Rel RegularTerm.UnfoldingEquivalent
      (g.step? (.inr x) left) (g.step? (.inr x) right) := by
  obtain ⟨R, hroot, hR⟩ := hequivalent
  have hequivalent' : left.UnfoldingEquivalent right := ⟨R, hroot, hR⟩
  have hlocal := hR left.root right.root hroot
  unfold RegularTerm.NodeCompatible at hlocal
  change RegularTerm.RawCompatible R left.rootNode? right.rootNode? at hlocal
  unfold step?
  cases hleft : left.rootNode? with
  | none =>
      cases hright : right.rootNode? with
      | none => exact .none
      | some rightNode =>
          simp [hleft, hright, RegularTerm.RawCompatible] at hlocal
  | some leftNode =>
      cases hright : right.rootNode? with
      | none =>
          simp [hleft, hright, RegularTerm.RawCompatible] at hlocal
      | some rightNode =>
          cases hleftKind : leftNode with
          | inl leftVariable =>
              cases hrightKind : rightNode with
              | inl rightVariable =>
                  have hvariable : leftVariable = rightVariable := by
                    simpa [hleft, hright, hleftKind, hrightKind,
                      RegularTerm.RawCompatible] using hlocal
                  subst rightVariable
                  by_cases hx : x = leftVariable
                  · simpa [hx] using hequivalent'
                  · simp [hx]
              | inr rightApp =>
                  simp [hleft, hright, hleftKind, hrightKind,
                    RegularTerm.RawCompatible] at hlocal
          | inr leftApp =>
              cases hrightKind : rightNode with
              | inl rightVariable =>
                  simp [hleft, hright, hleftKind, hrightKind,
                    RegularTerm.RawCompatible] at hlocal
              | inr rightApp =>
                  simp

/-- One labelled grammar step is congruent for semantic regular-term equality.
The closure hypotheses exclude malformed offset aliasing in ordinary RHS
substitution; private variable-label steps need no additional assumption. -/
public theorem step?_respects_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} {label : Label Action}
    {left right : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    (hleftClosed : left.ReferenceClosed)
    (hrightClosed : right.ReferenceClosed)
    (hrulesClosed : ∀ X action rhs,
      g.ruleLookup X action = some rhs → rhs.ReferenceClosed) :
    Option.Rel RegularTerm.UnfoldingEquivalent
      (g.step? label left) (g.step? label right) := by
  cases label with
  | inl action =>
      exact rootRewrite?_respects_unfoldingEquivalent hequivalent
        hleftClosed hrightClosed hrulesClosed
  | inr x =>
      exact privateStep?_respects_unfoldingEquivalent hequivalent

end EncodedFirstOrderGrammar

end DCFEquivalence
