module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.NonSinkingReflection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DepthExposure

@[expose]
public section

/-!
# Boundary tails occur at the advertised unfolding depth

The finite depth-prefix compiler records one pointed tail for every boundary
occurrence.  This file connects that compiler invariant to `SubtermAtDepth`,
which is needed to turn a symbolic variable exposure back into a concrete
depth exposure of the original pivot.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Extend a descendant path rooted at a pointed subgraph by a descendant path
inside that pointed subgraph. -/
public theorem DescendantAt.append_withRoot
    {term : RegularTerm} {baseDepth depth root index : ℕ}
    (hbase : term.DescendantAt baseDepth root)
    (hinside : (term.withRoot root).DescendantAt depth index) :
    term.DescendantAt (baseDepth + depth) index := by
  induction hinside with
  | root =>
      simpa [withRoot, RegularTerm.root] using hbase
  | @child depth parent X children child hparent hnode hchild ih =>
      have hparent' :
          term.DescendantAt (baseDepth + depth) parent := ih
      have hnode' : term.nodeAt? parent = some (.inr (X, children)) := by
        simpa [withRoot, nodeAt?, nodes] using hnode
      have hresult := DescendantAt.child hparent' hnode' hchild
      simpa [Nat.add_assoc] using hresult

/-- A subterm occurrence inside a pointed child lifts to an occurrence one
level deeper in the original pointed graph. -/
public theorem SubtermAtDepth.of_child
    {term subterm : RegularTerm} {depth X : ℕ}
    {children : List ℕ} {child : ℕ}
    (hroot : term.rootApplication? = some (X, children))
    (hchild : child ∈ children)
    (hinside : (term.withRoot child).SubtermAtDepth depth subterm) :
    term.SubtermAtDepth (depth + 1) subterm := by
  obtain ⟨index, hindex, hsubterm⟩ := hinside
  have hrootNode := nodeAt?_root_of_rootApplication? hroot
  have hchildDescendant :
      term.DescendantAt 1 child := by
    simpa using DescendantAt.child DescendantAt.root hrootNode hchild
  refine ⟨index, ?_, ?_⟩
  · have happended :=
      hchildDescendant.append_withRoot hindex
    simpa [Nat.add_comm] using happended
  · simpa [withRoot] using hsubterm

/-- Every boundary term emitted by a ground depth prefix is an actual subterm
occurrence at exactly that depth. -/
public theorem depthPrefix_tails_subtermAtDepth
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) (depth : ℕ) :
    ∀ tail ∈ (term.depthPrefix depth).tails,
      term.SubtermAtDepth depth tail := by
  induction depth generalizing term with
  | zero =>
      intro tail htail
      simp only [depthPrefix_zero, List.mem_singleton] at htail
      subst tail
      simp
  | succ depth ih =>
      obtain ⟨X, children, hroot⟩ :=
        hground.exists_rootApplication
      rw [depthPrefix_succ_of_rootApplication hroot]
      simp only [DepthPrefix.assemble_tails]
      intro tail htail
      obtain ⟨childPrefix, hchildPrefix, htailChild⟩ :=
        List.mem_flatMap.mp htail
      obtain ⟨child, hchild, hprefixEq⟩ :=
        List.mem_map.mp hchildPrefix
      subst childPrefix
      have hrootNode := nodeAt?_root_of_rootApplication? hroot
      have hchildGround : (term.withRoot child).Ground ranks :=
        hground.withRoot_descendant
          (.child .root hrootNode hchild)
      have hinside :=
        ih hchildGround tail htailChild
      exact hinside.of_child hroot hchild

end RegularTerm

end DCFEquivalence
