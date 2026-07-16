module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OrdinaryGroundRuns

@[expose]
public section

/-!
# Finite representatives for bounded semantic reachability

The operational system is finitely branching at every regular term.  Thus all
targets of runs of bounded length from a fixed finite source list have a
finite explicit list of representatives.  This is the pigeonhole component
used in the no-next-balancing-segment case.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- All successful one-step targets from one source. -/
@[expose] public def stepTargets
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) : List RegularTerm :=
  (g.candidateLabels source).filterMap fun label =>
    g.step? label source

public theorem mem_stepTargets_of_step
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {label : Label Action}
    (hstep : g.step? label source = some target) :
    target ∈ g.stepTargets source := by
  unfold stepTargets
  rw [List.mem_filterMap]
  exact ⟨label, mem_candidateLabels_of_step?_eq_some hstep, hstep⟩

/-- Exact-length bounded reachability from a finite list of sources. -/
@[expose] public def reachableExactly
    (g : EncodedFirstOrderGrammar Action) :
    ℕ → List RegularTerm → List RegularTerm
  | 0, sources => sources
  | length + 1, sources =>
      g.reachableExactly length
        (sources.flatMap g.stepTargets)

public theorem mem_reachableExactly_of_run
    {g : EncodedFirstOrderGrammar Action}
    {sources : List RegularTerm} {source target : RegularTerm}
    {labels : List (Label Action)}
    (hsource : source ∈ sources)
    (hrun : g.run? labels source = some target) :
    target ∈ g.reachableExactly labels.length sources := by
  induction labels generalizing source sources with
  | nil =>
      simp [run?] at hrun
      subst target
      simpa [reachableExactly] using hsource
  | cons label labels ih =>
      simp only [run?_cons] at hrun
      cases hstep : g.step? label source with
      | none => simp [hstep] at hrun
      | some next =>
          have htail : g.run? labels next = some target := by
            simpa [hstep] using hrun
          apply ih (sources := sources.flatMap g.stepTargets)
            (source := next)
          · exact List.mem_flatMap.mpr
              ⟨source, hsource, mem_stepTargets_of_step hstep⟩
          · exact htail

/-- Targets reachable in at most `bound` steps. -/
@[expose] public def reachableWithin
    (g : EncodedFirstOrderGrammar Action)
    (bound : ℕ) (sources : List RegularTerm) : List RegularTerm :=
  (List.range (bound + 1)).flatMap fun length =>
    g.reachableExactly length sources

public theorem mem_reachableWithin_of_run
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {sources : List RegularTerm}
    {source target : RegularTerm} {labels : List (Label Action)}
    (hsource : source ∈ sources)
    (hlength : labels.length ≤ bound)
    (hrun : g.run? labels source = some target) :
    target ∈ g.reachableWithin bound sources := by
  unfold reachableWithin
  apply List.mem_flatMap.mpr
  exact ⟨labels.length, by simp; omega,
    mem_reachableExactly_of_run hsource hrun⟩

/-- Every semantically transported bounded run has a representative in the
finite bounded-reachability list. -/
public theorem exists_mem_reachableWithin_of_semantic_run
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {sources : List RegularTerm}
    {source target : RegularTerm} {labels : List (Label Action)}
    (hsource : source ∈ sources)
    (hlength : labels.length ≤ bound)
    {reached : RegularTerm}
    (hrun : g.run? labels source = some reached)
    (hequivalent : target.UnfoldingEquivalent reached) :
    ∃ representative ∈ g.reachableWithin bound sources,
      target.UnfoldingEquivalent representative :=
  ⟨reached, mem_reachableWithin_of_run hsource hlength hrun,
    hequivalent⟩

end EncodedFirstOrderGrammar

namespace RegularTerm

/-- Semantic equality transports an immediate unfolding subterm to a
semantically equal immediate subterm on the other side. -/
public theorem UnfoldingEquivalent.exists_subtermAtDepth_one
    {left right subterm : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    (hsubterm : left.SubtermAtDepth 1 subterm) :
    ∃ rightSubterm,
      right.SubtermAtDepth 1 rightSubterm ∧
      subterm.UnfoldingEquivalent rightSubterm := by
  obtain ⟨leftChild, hleftChild, rfl⟩ := hsubterm
  cases hleftChild with
  | @child depth parent X leftChildren child
      hparent hleftNode hchild =>
      cases hparent
      have hleftRoot :
          left.rootApplication? = some (X, leftChildren) := by
        simp [rootApplication?, rootNode?, hleftNode]
      obtain ⟨rightChildren, hrightRoot, hchildren⟩ :=
        rootApplication?_of_unfoldingEquivalent
          hequivalent hleftRoot
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hchild
      have hiLeft : i < leftChildren.length :=
        (List.getElem?_eq_some_iff.mp hi).1
      have hiRight : i < rightChildren.length := by
        have hlength := List.Forall₂.length_eq hchildren
        omega
      let rightChild := rightChildren[i]
      have hrightChild : rightChild ∈ rightChildren :=
        List.getElem_mem hiRight
      have hleftGet :
          leftChildren.get ⟨i, hiLeft⟩ = leftChild := by
        exact Option.some.inj
          ((List.getElem?_eq_getElem hiLeft).symm.trans hi)
      have hchildrenGet :=
        (List.forall₂_iff_get.mp hchildren).2
          i hiLeft hiRight
      rw [hleftGet] at hchildrenGet
      have hpointed :
          (left.withRoot leftChild).UnfoldingEquivalent
            (right.withRoot rightChild) :=
        (withRoot_unfoldingEquivalent_iff_bisimilarAt
          left right leftChild rightChild).2 hchildrenGet
      have hrightNode :=
        nodeAt?_root_of_rootApplication? hrightRoot
      exact ⟨right.withRoot rightChild,
        ⟨rightChild, .child .root hrightNode hrightChild, rfl⟩,
        hpointed⟩

/-- Semantic equality transports an occurrence at every unfolding depth,
preserving the selected subterm up to semantic equality. -/
public theorem UnfoldingEquivalent.exists_subtermAtDepth
    {left right subterm : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    {depth : ℕ} (hsubterm : left.SubtermAtDepth depth subterm) :
    ∃ rightSubterm,
      right.SubtermAtDepth depth rightSubterm ∧
        subterm.UnfoldingEquivalent rightSubterm := by
  induction depth generalizing left right subterm with
  | zero =>
      have hleft : subterm = left :=
        (subtermAtDepth_zero_iff left subterm).mp hsubterm
      subst subterm
      exact ⟨right, (subtermAtDepth_zero_iff right right).mpr rfl,
        hequivalent⟩
  | succ depth ih =>
      obtain ⟨leftChild, hleftChild, hleftRest⟩ :=
        SubtermAtDepth.succ_decompose hsubterm
      obtain ⟨rightChild, hrightChild, hchildren⟩ :=
        hequivalent.exists_subtermAtDepth_one hleftChild
      obtain ⟨rightSubterm, hrightRest, hsubterms⟩ :=
        ih hchildren hleftRest
      exact ⟨rightSubterm,
        by simpa [Nat.add_comm] using
          (SubtermAtDepth.trans hrightChild hrightRest),
        hsubterms⟩

/-- All pointed subgraphs of one finite regular graph. -/
@[expose] public def pointedSubterms
    (term : RegularTerm) : List RegularTerm :=
  (List.range term.nodes.length).map term.withRoot

public theorem withRoot_mem_pointedSubterms
    (term : RegularTerm) {i : ℕ}
    (hi : i < term.nodes.length) :
    term.withRoot i ∈ term.pointedSubterms := by
  unfold pointedSubterms
  exact List.mem_map.mpr
    ⟨i, List.mem_range.mpr hi, rfl⟩

/-- Every unfolding subterm has an exact representative among the finitely
many pointed subgraphs. -/
public theorem exists_mem_pointedSubterms_of_subtermAtDepth
    {term subterm : RegularTerm} {depth : ℕ}
    (hclosed : term.ReferenceClosed)
    (hsubterm : term.SubtermAtDepth depth subterm) :
    ∃ representative ∈ term.pointedSubterms,
      subterm.UnfoldingEquivalent representative := by
  obtain ⟨i, hi, rfl⟩ := hsubterm
  have hbound : i < term.nodes.length := by
    induction hi with
    | root => exact hclosed.1
    | @child depth parent X children child hparent hnode hchild ih =>
        exact hclosed.2 parent X children hnode child hchild
  exact ⟨term.withRoot i,
    term.withRoot_mem_pointedSubterms hbound,
    unfoldingEquivalent_refl _⟩

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Continue an exact depth exposure by an exposure from its reached
representative.  The two unfolding depths add. -/
public theorem ExposesAtDepth.append_of_run
    {g : EncodedFirstOrderGrammar Action}
    {source sourceSubterm intermediate : RegularTerm}
    {first second : List (Label Action)}
    {firstDepth secondDepth : ℕ}
    (hsourceSubterm : source.SubtermAtDepth firstDepth sourceSubterm)
    (hfirstRun : g.run? first source = some intermediate)
    (hintermediate : intermediate.UnfoldingEquivalent sourceSubterm)
    (hsecond : g.ExposesAtDepth intermediate second secondDepth) :
    g.ExposesAtDepth source (first ++ second)
      (firstDepth + secondDepth) := by
  obtain ⟨intermediateSubterm, final, hintermediateSubterm,
      hsecondRun, hfinal⟩ := hsecond
  obtain ⟨sourceSubterm', hsourceSubterm', hsubterms⟩ :=
    hintermediate.exists_subtermAtDepth hintermediateSubterm
  refine ⟨sourceSubterm', final,
    RegularTerm.SubtermAtDepth.trans hsourceSubterm hsourceSubterm', ?_,
    hfinal.trans hsubterms⟩
  rw [g.run?_append, hfirstRun]
  exact hsecondRun

/-- Once a depth-`d` occurrence has been reached, one later sinking block
exposes a depth-`d+1` occurrence of the original source. -/
public theorem exposesBy_succ_of_run_sinksBy
    {g : EncodedFirstOrderGrammar Action}
    {source sourceSubterm intermediate : RegularTerm}
    {first word : List (Label Action)} {depth : ℕ}
    (hsourceSubterm : source.SubtermAtDepth depth sourceSubterm)
    (hfirstRun : g.run? first source = some intermediate)
    (hintermediate : intermediate.UnfoldingEquivalent sourceSubterm)
    (hsinks : g.SinksBy intermediate word) :
    g.ExposesBy source (first ++ word) (depth + 1) := by
  obtain ⟨initialSegment, suffix, hword, _hnonempty, hexposes⟩ := hsinks
  refine ⟨first ++ initialSegment, suffix, ?_, ?_⟩
  · rw [hword, List.append_assoc]
  · exact ExposesAtDepth.append_of_run hsourceSubterm hfirstRun
      hintermediate hexposes

end EncodedFirstOrderGrammar

end DCFEquivalence
