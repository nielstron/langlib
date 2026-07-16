module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StairBases

@[expose]
public section

/-!
# Subterm depth, exposure, and sinking

These are the graph-level versions of the notions preceding Definition 41 in
Jančar's arXiv:1010.4760v4.  Depth counts edges in the unfolding, so sharing
and cycles in a regular-term presentation cause no ambiguity.  A word exposes
a depth-`d` subterm when some prefix reaches a graph presentation of that
subterm; depth one is the paper's notion of sinking.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- A node reference reached by exactly `depth` child edges from the pointed
root.  This is a path in the unfolding, not merely graph reachability. -/
public inductive DescendantAt (term : RegularTerm) : ℕ → ℕ → Prop
  | root : DescendantAt term 0 term.root
  | child {depth parent X children child}
      (hparent : DescendantAt term depth parent)
      (hnode : term.nodeAt? parent = some (.inr (X, children)))
      (hchild : child ∈ children) :
      DescendantAt term (depth + 1) child

/-- Unfolding-depth paths concatenate after changing the distinguished root
to the intermediate occurrence. -/
public theorem DescendantAt.trans
    {term : RegularTerm} {firstDepth secondDepth middle target : ℕ}
    (hfirst : term.DescendantAt firstDepth middle)
    (hsecond : (term.withRoot middle).DescendantAt secondDepth target) :
    term.DescendantAt (firstDepth + secondDepth) target := by
  induction hsecond with
  | root => simpa using hfirst
  | @child depth parent X children child hparent hnode hchild ih =>
      have hnode' : term.nodeAt? parent = some (.inr (X, children)) := by
        simpa using hnode
      simpa [Nat.add_assoc] using
        (DescendantAt.child ih hnode' hchild)

/-- A positive-depth occurrence factors through one immediate child of the
root, followed by the remaining unfolding path. -/
public theorem DescendantAt.succ_decompose
    {term : RegularTerm} {depth target : ℕ}
    (hdescendant : term.DescendantAt (depth + 1) target) :
    ∃ child X children,
      term.nodeAt? term.root = some (.inr (X, children)) ∧
        child ∈ children ∧
        (term.withRoot child).DescendantAt depth target := by
  induction depth generalizing target with
  | zero =>
      cases hdescendant with
      | @child _ parent X children _ hparent hnode hchild =>
          cases hparent
          exact ⟨target, X, children, hnode, hchild, .root⟩
  | succ depth ih =>
      cases hdescendant with
      | @child _ parent X children _ hparent hnode hchild =>
          obtain ⟨first, Y, firstChildren, hroot, hfirst, hrest⟩ :=
            ih hparent
          refine ⟨first, Y, firstChildren, hroot, hfirst, ?_⟩
          exact DescendantAt.child hrest (by simpa using hnode) hchild

/-- A pointed graph presents a subterm occurring at the specified unfolding
depth. -/
@[expose] public def SubtermAtDepth
    (term : RegularTerm) (depth : ℕ) (subterm : RegularTerm) : Prop :=
  ∃ index, term.DescendantAt depth index ∧ subterm = term.withRoot index

@[simp] public theorem subtermAtDepth_zero_iff
    (term subterm : RegularTerm) :
    term.SubtermAtDepth 0 subterm ↔ subterm = term := by
  constructor
  · rintro ⟨index, hindex, rfl⟩
    cases hindex
    rfl
  · intro heq
    subst subterm
    exact ⟨RegularTerm.root term, .root, rfl⟩

/-- Exact unfolding subterm occurrences compose additively in depth. -/
public theorem SubtermAtDepth.trans
    {term middle target : RegularTerm} {firstDepth secondDepth : ℕ}
    (hfirst : term.SubtermAtDepth firstDepth middle)
    (hsecond : middle.SubtermAtDepth secondDepth target) :
    term.SubtermAtDepth (firstDepth + secondDepth) target := by
  obtain ⟨middleIndex, hmiddle, rfl⟩ := hfirst
  obtain ⟨targetIndex, htarget, rfl⟩ := hsecond
  exact ⟨targetIndex, hmiddle.trans htarget, rfl⟩

/-- A positive-depth subterm factors through an immediate subterm. -/
public theorem SubtermAtDepth.succ_decompose
    {term target : RegularTerm} {depth : ℕ}
    (hsubterm : term.SubtermAtDepth (depth + 1) target) :
    ∃ childTerm,
      term.SubtermAtDepth 1 childTerm ∧
        childTerm.SubtermAtDepth depth target := by
  obtain ⟨targetIndex, htarget, rfl⟩ := hsubterm
  obtain ⟨child, X, children, hroot, hchild, hrest⟩ :=
    htarget.succ_decompose
  refine ⟨term.withRoot child, ?_, ?_⟩
  · exact ⟨child, .child .root hroot hchild, rfl⟩
  · exact ⟨targetIndex, hrest, rfl⟩

public theorem DescendantAt.node_mem_support
    {term : RegularTerm} {support : List ℕ}
    (hwitness : term.GroundWitness support)
    {depth index : ℕ} (hindex : term.DescendantAt depth index) :
    index ∈ support := by
  induction hindex with
  | root => exact hwitness.1
  | @child depth parent X children child hparent hnode hchild ih =>
      obtain ⟨Y, parentChildren, hparentNode, hchildren⟩ :=
        hwitness.2 _ ih
      have happs : (Y, parentChildren) = (X, children) := by
        exact Sum.inr.inj (Option.some.inj (hparentNode.symm.trans hnode))
      have hsame : parentChildren = children := congrArg Prod.snd happs
      subst parentChildren
      exact hchildren _ hchild

/-- Every unfolding subterm of a ground regular term is ground; the original
finite support can be reused after changing the distinguished root. -/
public theorem Ground.withRoot_descendant
    {ranks : List ℕ} {term : RegularTerm} (hground : term.Ground ranks)
    {depth index : ℕ} (hindex : term.DescendantAt depth index) :
    (term.withRoot index).Ground ranks := by
  obtain ⟨hshape, support, hsupport, hwitness⟩ := hground
  have hindexSupport := hindex.node_mem_support hwitness
  refine ⟨?_, support, ?_, ?_⟩
  · unfold ShapeWellFormed shapeWellFormedCode at hshape ⊢
    rw [Bool.and_eq_true] at hshape ⊢
    refine ⟨?_, ?_⟩
    · obtain ⟨X, children, hnode, _⟩ := hwitness.2 index hindexSupport
      exact decide_eq_true (List.getElem?_eq_some_iff.mp hnode).1
    · simpa [withRoot, nodes] using hshape.2
  · simpa [withRoot, nodes] using hsupport
  · refine ⟨?_, ?_⟩
    · simpa [withRoot, root] using hindexSupport
    · intro i hi
      simpa [withRoot, nodeAt?, nodes] using hwitness.2 i hi

public theorem Ground.subtermAtDepth
    {ranks : List ℕ} {term subterm : RegularTerm}
    (hground : term.Ground ranks) {depth : ℕ}
    (hsubterm : term.SubtermAtDepth depth subterm) :
    subterm.Ground ranks := by
  obtain ⟨index, hindex, rfl⟩ := hsubterm
  exact hground.withRoot_descendant hindex

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A word reaches a particular occurrence at an exact depth.  Equality is
semantic unfolding equality, so harmless graph-layout changes made by root
rewriting are ignored. -/
@[expose] public def ExposesAtDepth
    (g : EncodedFirstOrderGrammar Action)
    (term : RegularTerm) (word : List (Label Action)) (depth : ℕ) : Prop :=
  ∃ subterm target,
    term.SubtermAtDepth depth subterm ∧
    g.run? word term = some target ∧
    target.UnfoldingEquivalent subterm

/-- Some prefix of the supplied word exposes a depth-`d` subterm. -/
@[expose] public def ExposesBy
    (g : EncodedFirstOrderGrammar Action)
    (term : RegularTerm) (word : List (Label Action)) (depth : ℕ) : Prop :=
  ∃ initialSegment suffix,
    word = initialSegment ++ suffix ∧
      g.ExposesAtDepth term initialSegment depth

/-- A term sinks by a word when a nonempty prefix exposes one of its
immediate successors.  Requiring progress is essential for regular cyclic
terms: semantic equality with one of their own immediate subterms must not
make the empty word an exposing computation.  This matches exposure through
the finite depth-one prefix in Jančar's definition. -/
@[expose] public def SinksBy
    (g : EncodedFirstOrderGrammar Action)
    (term : RegularTerm) (word : List (Label Action)) : Prop :=
  ∃ initialSegment suffix,
    word = initialSegment ++ suffix ∧
      initialSegment ≠ [] ∧
      g.ExposesAtDepth term initialSegment 1

/-- Sinking always consumes at least one label. -/
public theorem not_sinksBy_nil
    (g : EncodedFirstOrderGrammar Action) (term : RegularTerm) :
    ¬g.SinksBy term [] := by
  rintro ⟨initialSegment, suffix, hword, hnonempty, _hexposes⟩
  have : initialSegment = [] := by
    simpa using congrArg (List.take initialSegment.length) hword
  exact hnonempty this

/-- The empty prefix exposes the term itself at depth zero. -/
public theorem exposesBy_zero
    (g : EncodedFirstOrderGrammar Action) (term : RegularTerm)
    (word : List (Label Action)) :
    g.ExposesBy term word 0 := by
  refine ⟨[], word, by simp, ?_⟩
  refine ⟨term, term, ?_, rfl, ?_⟩
  · simp
  · exact RegularTerm.unfoldingEquivalent_refl term

/-- Exposure is retained when more labels are appended after the witnessing
prefix. -/
public theorem ExposesBy.append
    {g : EncodedFirstOrderGrammar Action} {term : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hexposes : g.ExposesBy term word depth)
    (suffix : List (Label Action)) :
    g.ExposesBy term (word ++ suffix) depth := by
  obtain ⟨initialSegment, remainder, hword, hexact⟩ := hexposes
  refine ⟨initialSegment, remainder ++ suffix, ?_, hexact⟩
  rw [hword, List.append_assoc]

public theorem SinksBy.append
    {g : EncodedFirstOrderGrammar Action} {term : RegularTerm}
    {word : List (Label Action)}
    (hsinks : g.SinksBy term word)
    (suffix : List (Label Action)) :
    g.SinksBy term (word ++ suffix) := by
  obtain ⟨initialSegment, remainder, hword, hnonempty, hexact⟩ := hsinks
  refine ⟨initialSegment, remainder ++ suffix, ?_, hnonempty, hexact⟩
  rw [hword, List.append_assoc]

/-- Exact positive exposure gives sinking by taking the whole word. -/
public theorem sinksBy_of_exposesAtDepth
    {g : EncodedFirstOrderGrammar Action} {term : RegularTerm}
    {word : List (Label Action)}
    (hnonempty : word ≠ [])
    (hexposes : g.ExposesAtDepth term word 1) :
    g.SinksBy term word :=
  ⟨word, [], by simp, hnonempty, hexposes⟩

/-- Exact exposure gives prefix exposure by taking the whole word. -/
public theorem exposesBy_of_exposesAtDepth
    {g : EncodedFirstOrderGrammar Action} {term : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hexposes : g.ExposesAtDepth term word depth) :
    g.ExposesBy term word depth :=
  ⟨word, [], by simp, hexposes⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
