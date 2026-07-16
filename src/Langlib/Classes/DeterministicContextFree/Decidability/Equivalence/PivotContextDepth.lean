module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailPivotSubsequence

@[expose]
public section

/-!
# Protected variable depth in pivot contexts

In the last paragraph of the proof of Jančar's Proposition 49, the pivot
suffix starts at a deepest exposed subterm `V₁` and never sinks from `V₁`.
Every later pivot is reached along that non-sinking suffix.  Consequently,
when the pivots are written over the tails of the `M₀`-prefix of `V₁`, every
occurrence of a tail variable remains at depth at least `M₀`.

`RegularTerm.ApplicationDepth M₀` is the unfolding-level formulation of
that variable-depth conclusion.  It is independent of the finite graph
presentation and also makes sense for regular contexts.  Finiteness and the
graph-size bound used later in Proposition 49 are separate properties.

The least-missing-depth premise in `FixedTailPivotSubsequence` only produces
one common tuple of tails.  It does not by itself provide the non-sinking
pivot-suffix invariant, so the protected-depth property is named explicitly
below rather than being silently inferred from that weaker premise.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- A variable occurrence reached by exactly `depth` child edges in the
unfolding of a regular term. -/
@[expose] public def HasVariableAtDepth
    (term : RegularTerm) (depth : ℕ) : Prop :=
  ∃ index x,
    term.DescendantAt depth index ∧
      term.nodeAt? index = some (.inl x)

/-- Every occurrence strictly above a protected application depth is an
application node. -/
public theorem ApplicationDepth.descendant_isApplication
    {term : RegularTerm} {guardDepth depth index : ℕ}
    (hprotected : term.ApplicationDepth guardDepth)
    (hdepth : depth < guardDepth)
    (hdescendant : term.DescendantAt depth index) :
    ∃ X children,
      term.nodeAt? index = some (.inr (X, children)) := by
  induction depth generalizing term guardDepth index with
  | zero =>
      cases hdescendant
      cases guardDepth with
      | zero => omega
      | succ guardDepth =>
          obtain ⟨X, children, hroot, _hchildren⟩ := hprotected
          exact ⟨X, children,
            nodeAt?_root_of_rootApplication? hroot⟩
  | succ depth ih =>
      cases guardDepth with
      | zero => omega
      | succ guardDepth =>
          obtain ⟨X, protectedChildren, hroot, hchildren⟩ :=
            hprotected
          obtain ⟨child, Y, descendantChildren, hdescendantRoot,
              hchild, hrest⟩ :=
            hdescendant.succ_decompose
          have hrootNode :
              term.nodeAt? term.root =
                some (.inr (X, protectedChildren)) := by
            exact nodeAt?_root_of_rootApplication? hroot
          have happlication :
              (X, protectedChildren) = (Y, descendantChildren) := by
            exact Sum.inr.inj
              (Option.some.inj
                (hrootNode.symm.trans hdescendantRoot))
          have hchildrenEq :
              protectedChildren = descendantChildren :=
            congrArg Prod.snd happlication
          subst descendantChildren
          exact ih
            (term := term.withRoot child)
            (guardDepth := guardDepth)
            (index := index)
            (hchildren child hchild)
            (by omega)
            hrest

/-- `ApplicationDepth protected` entails exactly the lower-bound direction
needed in Proposition 49: every variable occurrence has unfolding depth at
least `protected`. -/
public theorem ApplicationDepth.le_of_hasVariableAtDepth
    {term : RegularTerm} {guardDepth depth : ℕ}
    (hprotected : term.ApplicationDepth guardDepth)
    (hvariable : term.HasVariableAtDepth depth) :
    guardDepth ≤ depth := by
  by_contra hnot
  have hdepth : depth < guardDepth := by omega
  obtain ⟨index, x, hdescendant, hnode⟩ := hvariable
  obtain ⟨X, children, happlication⟩ :=
    hprotected.descendant_isApplication hdepth hdescendant
  simp [hnode] at happlication

/-- Pointwise form of the protected-variable conclusion. -/
public theorem ApplicationDepth.variableOccurrence_depth_ge
    {term : RegularTerm} {guardDepth depth index x : ℕ}
    (hprotected : term.ApplicationDepth guardDepth)
    (hdescendant : term.DescendantAt depth index)
    (hvariable : term.nodeAt? index = some (.inl x)) :
    guardDepth ≤ depth :=
  hprotected.le_of_hasVariableAtDepth
    ⟨index, x, hdescendant, hvariable⟩

/-- On a reference-closed graph, the variable-occurrence lower bound also
implies `ApplicationDepth`.  Thus for the well-formed pivot schemas used in
the equivalence proof, `ApplicationDepth M₀` is exactly the paper's claim,
not merely a sufficient strengthening of it. -/
public theorem applicationDepth_of_variableOccurrence_depth_ge
    {term : RegularTerm} {guardDepth : ℕ}
    (hclosed : term.ReferenceClosed)
    (hvariables :
      ∀ {depth}, term.HasVariableAtDepth depth →
        guardDepth ≤ depth) :
    term.ApplicationDepth guardDepth := by
  induction guardDepth generalizing term with
  | zero => trivial
  | succ guardDepth ih =>
      cases hroot : term.rootNode? with
      | none =>
          have hrootBound := hclosed.1
          unfold rootNode? nodeAt? at hroot
          rw [List.getElem?_eq_none_iff] at hroot
          omega
      | some node =>
          cases node with
          | inl x =>
              have hoccurrence : term.HasVariableAtDepth 0 :=
                ⟨term.root, x, .root, by
                  simpa [rootNode?] using hroot⟩
              have := hvariables hoccurrence
              omega
          | inr application =>
              rcases application with ⟨X, children⟩
              have hrootApplication :
                  term.rootApplication? = some (X, children) := by
                simp [rootApplication?, hroot]
              have hrootNode :
                  term.nodeAt? term.root =
                    some (.inr (X, children)) := by
                simpa [rootNode?] using hroot
              refine ⟨X, children, hrootApplication, ?_⟩
              intro child hchild
              have hchildBound : child < term.nodes.length :=
                rootApplication_children_lt hclosed
                  hrootApplication child hchild
              apply ih
                (withRoot_referenceClosed hclosed hchildBound)
              intro depth hvariable
              obtain ⟨index, x, hdescendant, hnode⟩ := hvariable
              have hfirst :
                  term.DescendantAt 1 child :=
                .child .root hrootNode hchild
              have hfull :
                  term.DescendantAt (depth + 1) index := by
                have := hfirst.trans hdescendant
                simpa [Nat.add_comm] using this
              have hnode' :
                  term.nodeAt? index = some (.inl x) := by
                simpa [withRoot, nodeAt?, nodes] using hnode
              have hbound :=
                hvariables
                  ⟨index, x, hfull, hnode'⟩
              omega

/-- Characterization of protected application depth by unfolding variable
occurrences, for every reference-closed regular graph. -/
public theorem applicationDepth_iff_variableOccurrence_depth_ge
    {term : RegularTerm} (hclosed : term.ReferenceClosed)
    (guardDepth : ℕ) :
    term.ApplicationDepth guardDepth ↔
      ∀ {depth}, term.HasVariableAtDepth depth →
        guardDepth ≤ depth := by
  constructor
  · intro hprotected depth hvariable
    exact hprotected.le_of_hasVariableAtDepth hvariable
  · exact applicationDepth_of_variableOccurrence_depth_ge hclosed

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace FixedTailPivotPresentation

/-- The explicit pivot-context invariant used by Proposition 49: every
schema over the common tail tuple protects the requested application depth.

For the paper's construction `depth = M₀`; the premise is supplied by the
non-sinking suffix starting at the deepest exposed subterm. -/
@[expose] public def ProtectsDepth
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (depth : ℕ) : Prop :=
  ∀ j, (presentation.schema j).ApplicationDepth depth

public theorem ProtectsDepth.schema
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    {presentation :
      FixedTailPivotPresentation g base filler labels pivots}
    {depth : ℕ}
    (hprotected : presentation.ProtectsDepth depth)
    (j : ℕ) :
    (presentation.schema j).ApplicationDepth depth :=
  hprotected j

/-- Every variable occurrence in every protected pivot schema has at least
the advertised unfolding depth. -/
public theorem ProtectsDepth.variableOccurrence_depth_ge
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    {presentation :
      FixedTailPivotPresentation g base filler labels pivots}
    {guardDepth occurrence index x : ℕ}
    (hprotected : presentation.ProtectsDepth guardDepth)
    (j : ℕ)
    (hdescendant :
      (presentation.schema j).DescendantAt occurrence index)
    (hvariable :
      (presentation.schema j).nodeAt? index = some (.inl x)) :
    guardDepth ≤ occurrence :=
  (hprotected.schema j).variableOccurrence_depth_ge
    hdescendant hvariable

end FixedTailPivotPresentation

end EncodedFirstOrderGrammar

end DCFEquivalence
