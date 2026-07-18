module

public import Langlib.Automata.LinearBounded.FiniteAcyclicRank
public import Langlib.Automata.LinearBounded.Functional
public import Langlib.Automata.LinearBounded.PartialBijectionDecomposition
public import Langlib.Automata.LinearBounded.TwoMatchingChoiceBound
public import Langlib.Automata.LinearBounded.AcyclicBoundedDegree
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic

@[expose]
public section

/-!
# Alternating matching criterion for finite directed relations

A partial function can be split into two directed matchings under two additional local
conditions.  Every vertex may have at most two predecessors, a vertex with two distinct
predecessors must be a sink, and every edge must flip a supplied two-valued phase.  These
hypotheses make the undirected graph bipartite of maximum degree two, hence a disjoint union of
paths and even cycles.  Global acyclicity is an alternative sufficient premise: it makes the
undirected graph a forest and supplies the phase by its standard bipartite coloring.

The construction below uses the supplied two-coloring (or the one induced by the forest in the
acyclic corollary).  It then reorients every non-antiparallel edge from vertex-color zero to
vertex-color one and applies the existing optimal decomposition
of a degree-two bipartite relation into two partial bijections.  Pulling those colors back to the
original direction makes every color class a directed matching: no two same-colored edges share
an endpoint, so in particular no two of them are composable.

The final theorem packages the criterion uniformly over all raw tape widths as
`LBA.Machine.HasTwoMatchingStepPartition`.
-/

open Classical Relation Set

namespace AlternatingMatchingCriterion

variable {V : Type*}

/-- A merge of two genuinely distinct incoming edges is terminal. -/
public def DoublePredecessorSink (edge : V → V → Prop) : Prop :=
  ∀ ⦃left right target⦄, edge left target → edge right target → left ≠ right →
    ∀ next, ¬ edge target next

/-- The undirected neighbors of a vertex in the symmetrization of a relation. -/
public def undirectedNeighbors (edge : V → V → Prop) (vertex : V) : Set V :=
  {other | (SimpleGraph.fromRel edge).Adj vertex other}

/-- Functionality, indegree at most two, and terminal double merges bound the undirected degree
by two.  The proof separates a genuine double merge (where there is no successor) from the
remaining case (at most one predecessor and at most one successor). -/
public theorem encard_undirectedNeighbors_le_two
    (edge : V → V → Prop)
    (hfunctional : Relator.RightUnique edge)
    (hindegree : ∀ target, {source | edge source target}.encard ≤ 2)
    (hmerge : DoublePredecessorSink edge)
    (vertex : V) :
    (undirectedNeighbors edge vertex).encard ≤ 2 := by
  by_cases hdouble : ∃ left right, edge left vertex ∧ edge right vertex ∧ left ≠ right
  · obtain ⟨left, right, hleft, hright, hne⟩ := hdouble
    have hsink : ∀ next, ¬ edge vertex next := hmerge hleft hright hne
    apply (Set.encard_mono ?_).trans (hindegree vertex)
    intro other hother
    rcases hother.2 with hout | hin
    · exact (hsink other hout).elim
    · exact hin
  · have hpred : {source | edge source vertex}.encard ≤ 1 := by
      apply Set.encard_le_one_iff.mpr
      intro left right hleft hright
      by_contra hne
      exact hdouble ⟨left, right, hleft, hright, hne⟩
    have hsucc : {target | edge vertex target}.encard ≤ 1 := by
      apply Set.encard_le_one_iff.mpr
      intro left right hleft hright
      exact hfunctional hleft hright
    have hsubset :
        undirectedNeighbors edge vertex ⊆
          {source | edge source vertex} ∪ {target | edge vertex target} := by
      intro other hother
      rcases hother.2 with hout | hin
      · exact Or.inr hout
      · exact Or.inl hin
    calc
      (undirectedNeighbors edge vertex).encard ≤
          ({source | edge source vertex} ∪ {target | edge vertex target}).encard :=
        Set.encard_mono hsubset
      _ ≤ {source | edge source vertex}.encard +
          {target | edge vertex target}.encard :=
        Set.encard_union_le _ _
      _ ≤ 1 + 1 := add_le_add hpred hsucc
      _ = 2 := rfl

/-- An edge-alternating phase is a proper two-coloring of the relation's undirected
symmetrization.  In particular every undirected cycle is even. -/
public def fromRelColoringOfAlternating
    (edge : V → V → Prop) (phase : V → Fin 2)
    (halternating : ∀ ⦃source target⦄, edge source target →
      phase source ≠ phase target) :
    (SimpleGraph.fromRel edge).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk phase fun {_ _} hadj ↦ by
    rcases hadj.2 with hforward | hbackward
    · exact halternating hforward
    · exact (halternating hbackward).symm

/-- Edge alternation makes the undirected symmetrization bipartite. -/
public theorem fromRel_isBipartite_of_alternating
    (edge : V → V → Prop) (phase : V → Fin 2)
    (halternating : ∀ ⦃source target⦄, edge source target →
      phase source ≠ phase target) :
    (SimpleGraph.fromRel edge).IsBipartite :=
  ⟨fromRelColoringOfAlternating edge phase halternating⟩

/-- Every closed walk in the symmetrization has even length under an alternating phase. -/
public theorem fromRel_closedWalk_even_of_alternating
    (edge : V → V → Prop) (phase : V → Fin 2)
    (halternating : ∀ ⦃source target⦄, edge source target →
      phase source ≠ phase target)
    {base : V} (walk : (SimpleGraph.fromRel edge).Walk base base) :
    Even walk.length := by
  let boolColor : (SimpleGraph.fromRel edge).Coloring Bool :=
    (SimpleGraph.fromRel edge).recolorOfEquiv finTwoEquiv
      (fromRelColoringOfAlternating edge phase halternating)
  exact (boolColor.even_length_iff_congr walk).2 Iff.rfl

/-- A strict rank on a functional directed relation makes its undirected symmetrization a
forest.  At a minimum-rank vertex of an undirected cycle, both incident cycle edges would point
outward, contradicting right-uniqueness. -/
public theorem fromRel_isAcyclic_of_strictRank
    (edge : V → V → Prop)
    (hfunctional : Relator.RightUnique edge)
    (rank : V → ℕ)
    (hstrict : ∀ ⦃source target⦄, edge source target → rank source < rank target) :
    (SimpleGraph.fromRel edge).IsAcyclic := by
  classical
  intro base cycle hcycle
  have hargSome : (cycle.support.argmin rank).isSome := by
    apply Option.isSome_iff_ne_none.mpr
    intro hnone
    exact cycle.support_ne_nil (List.argmin_eq_none.mp hnone)
  let pivot : V := (cycle.support.argmin rank).get hargSome
  have hpivotArg : pivot ∈ cycle.support.argmin rank := by
    exact Option.get_mem hargSome
  have hpivotMem : pivot ∈ cycle.support :=
    List.argmin_mem hpivotArg
  have hpivotMin : ∀ {other}, other ∈ cycle.support → rank pivot ≤ rank other := by
    intro other hother
    exact List.le_of_mem_argmin hother hpivotArg
  let rotated := cycle.rotate hpivotMem
  have hrotatedCycle : rotated.IsCycle := hcycle.rotate hpivotMem
  have hsndMem : rotated.snd ∈ cycle.support := by
    rw [← cycle.mem_support_rotate_iff hpivotMem]
    exact rotated.getVert_mem_support 1
  have hpenultimateMem : rotated.penultimate ∈ cycle.support := by
    rw [← cycle.mem_support_rotate_iff hpivotMem]
    exact rotated.getVert_mem_support (rotated.length - 1)
  have hsndAdj : (SimpleGraph.fromRel edge).Adj pivot rotated.snd :=
    rotated.adj_snd hrotatedCycle.not_nil
  have hpenultimateAdj :
      (SimpleGraph.fromRel edge).Adj pivot rotated.penultimate :=
    (rotated.adj_penultimate hrotatedCycle.not_nil).symm
  have hsndEdge : edge pivot rotated.snd := by
    rcases hsndAdj.2 with hforward | hbackward
    · exact hforward
    · exact False.elim
        ((not_lt_of_ge (hpivotMin hsndMem)) (hstrict hbackward))
  have hpenultimateEdge : edge pivot rotated.penultimate := by
    rcases hpenultimateAdj.2 with hforward | hbackward
    · exact hforward
    · exact False.elim
        ((not_lt_of_ge (hpivotMin hpenultimateMem)) (hstrict hbackward))
  exact hrotatedCycle.snd_ne_penultimate
    (hfunctional hsndEdge hpenultimateEdge)

/-- A finite acyclic functional relation has an undirected forest as its symmetrization. -/
public theorem fromRel_isAcyclic
    [Fintype V]
    (edge : V → V → Prop)
    (hfunctional : Relator.RightUnique edge)
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex) :
    (SimpleGraph.fromRel edge).IsAcyclic := by
  exact fromRel_isAcyclic_of_strictRank edge hfunctional
    (FiniteAcyclicRank.rank edge)
    (fun {_ _} hstep ↦ FiniteAcyclicRank.rank_lt_of_edge hacyclic hstep)

section Finite

variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem ne_of_edge_of_alternating
    {edge : V → V → Prop} {phase : V → Fin 2}
    (halternating : ∀ ⦃source target⦄, edge source target → phase source ≠ phase target)
    {source target : V} (hstep : edge source target) :
    source ≠ target := by
  intro heq
  exact halternating hstep (congrArg phase heq)

omit [Fintype V] in
/-- The parity-form criterion.  Directed cycles are allowed: it is enough that every edge flips
an explicit two-valued phase.  Opposite edges between the same endpoints are handled as isolated
directed two-cycles and receive their source phases as opposite colors. -/
public theorem exists_two_directedMatching_partition_of_alternating
    (edge : V → V → Prop)
    (hfunctional : Relator.RightUnique edge)
    (hindegree : ∀ target, {source | edge source target}.encard ≤ 2)
    (hmerge : DoublePredecessorSink edge)
    (phase : V → Fin 2)
    (halternating : ∀ ⦃source target⦄, edge source target →
      phase source ≠ phase target) :
    ∃ layer : Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target, layer color source target → edge source target) ∧
        (∀ color, Relator.BiUnique (layer color)) ∧
        ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne (layer color) := by
  classical
  let G : SimpleGraph V := SimpleGraph.fromRel edge
  /- Remove antiparallel pairs before treating the relation as a simple undirected graph. -/
  let oriented : V → V → Prop := fun left right ↦
    G.Adj left right ∧ phase left = 0 ∧
      ¬ (edge left right ∧ edge right left)
  have horientedOut : ∀ left, {right | oriented left right}.encard ≤ 2 := by
    intro left
    apply (Set.encard_mono ?_).trans
      (encard_undirectedNeighbors_le_two edge hfunctional hindegree hmerge left)
    intro right hright
    exact hright.1
  have horientedIn : ∀ right, {left | oriented left right}.encard ≤ 2 := by
    intro right
    apply (Set.encard_mono ?_).trans
      (encard_undirectedNeighbors_le_two edge hfunctional hindegree hmerge right)
    intro left hleft
    exact hleft.1.symm
  obtain ⟨orientedLayer, horientedCover, _horientedSub, horientedBiUnique⟩ :=
    PartialBijectionDecomposition.exists_two_biUnique_partition
      oriented horientedOut horientedIn
  /- Mutual edges use the source phase directly.  Every other edge uses the color of its
  phase-zero-to-phase-one undirected orientation. -/
  let layer : Fin 2 → V → V → Prop := fun color source target ↦
    edge source target ∧
      if edge target source then
        color = phase source
      else if phase source = 0 then
        orientedLayer color source target
      else
        orientedLayer color target source
  have hadj_of_edge : ∀ {source target}, edge source target → G.Adj source target := by
    intro source target hstep
    exact ⟨ne_of_edge_of_alternating halternating hstep, Or.inl hstep⟩
  have htarget_ne_zero_of_source_zero :
      ∀ {source target}, edge source target → phase source = 0 →
        phase target ≠ 0 := by
    intro source target hstep hsource htarget
    exact halternating hstep (hsource.trans htarget.symm)
  have hsource_ne_zero_of_target_zero :
      ∀ {source target}, edge source target → phase target = 0 →
        phase source ≠ 0 := by
    intro source target hstep htarget hsource
    exact halternating hstep (hsource.trans htarget.symm)
  have hsource_zero_of_target_ne_zero :
      ∀ {source target}, edge source target → phase target ≠ 0 →
        phase source = 0 := by
    intro source target hstep htarget
    have hne := halternating hstep
    have hsourceCases : phase source = 0 ∨ phase source = 1 := by omega
    have htargetCases : phase target = 0 ∨ phase target = 1 := by omega
    rcases hsourceCases with hsource | hsource
    · exact hsource
    · rcases htargetCases with htargetZero | htargetOne
      · exact (htarget htargetZero).elim
      · exact (hne (hsource.trans htargetOne.symm)).elim
  have htarget_zero_of_source_ne_zero :
      ∀ {source target}, edge source target → phase source ≠ 0 →
        phase target = 0 := by
    intro source target hstep hsource
    have hne := halternating hstep
    have hsourceCases : phase source = 0 ∨ phase source = 1 := by omega
    have htargetCases : phase target = 0 ∨ phase target = 1 := by omega
    rcases htargetCases with htarget | htarget
    · exact htarget
    · rcases hsourceCases with hsourceZero | hsourceOne
      · exact (hsource hsourceZero).elim
      · exact (hne (hsourceOne.trans htarget.symm)).elim
  refine ⟨layer, ?_, ?_, ?_, ?_⟩
  · intro source target
    constructor
    · intro hstep
      by_cases hreverse : edge target source
      · refine ⟨phase source, ⟨hstep, by simp [hreverse]⟩, ?_⟩
        intro other hother
        have hother' : edge source target ∧ other = phase source := by
          simpa [layer, hreverse] using hother
        exact hother'.2
      · by_cases hsource : phase source = 0
        · have horiented : oriented source target :=
            ⟨hadj_of_edge hstep, hsource, by simp [hstep, hreverse]⟩
          obtain ⟨color, hcolor, hunique⟩ :=
            (horientedCover source target).mp horiented
          refine ⟨color, ⟨hstep, by simp [hreverse, hsource, hcolor]⟩, ?_⟩
          intro other hother
          exact hunique other
            (by simpa [layer, hreverse, hsource] using hother.2)
        · have htarget : phase target = 0 :=
            htarget_zero_of_source_ne_zero hstep hsource
          have horiented : oriented target source :=
            ⟨(hadj_of_edge hstep).symm, htarget, by simp [hstep, hreverse]⟩
          obtain ⟨color, hcolor, hunique⟩ :=
            (horientedCover target source).mp horiented
          refine ⟨color, ⟨hstep, by simp [hreverse, hsource, hcolor]⟩, ?_⟩
          intro other hother
          exact hunique other
            (by simpa [layer, hreverse, hsource] using hother.2)
    · rintro ⟨color, hcolor, _⟩
      exact hcolor.1
  · intro color source target hcolor
    exact hcolor.1
  · intro color
    constructor
    · intro left right target hleft hright
      by_cases hleftReverse : edge target left
      · by_contra hne
        exact hmerge hleft.1 hright.1 hne left hleftReverse
      · by_cases hrightReverse : edge target right
        · by_contra hne
          exact hmerge hright.1 hleft.1 (Ne.symm hne) right hrightReverse
        · by_cases htarget : phase target = 0
          · have hleftSource : phase left ≠ 0 :=
              hsource_ne_zero_of_target_zero hleft.1 htarget
            have hrightSource : phase right ≠ 0 :=
              hsource_ne_zero_of_target_zero hright.1 htarget
            exact horientedBiUnique color |>.2
              (by simpa [layer, hleftReverse, hleftSource] using hleft.2)
              (by simpa [layer, hrightReverse, hrightSource] using hright.2)
          · have hleftSource : phase left = 0 :=
              hsource_zero_of_target_ne_zero hleft.1 htarget
            have hrightSource : phase right = 0 :=
              hsource_zero_of_target_ne_zero hright.1 htarget
            exact horientedBiUnique color |>.1
              (by simpa [layer, hleftReverse, hleftSource] using hleft.2)
              (by simpa [layer, hrightReverse, hrightSource] using hright.2)
    · intro source left right hleft hright
      exact hfunctional hleft.1 hright.1
  · intro color first middle last hfirst hlast
    have hfirstEdge := hfirst.1
    have hlastEdge := hlast.1
    by_cases hfirstReverse : edge middle first
    · have heq : first = last := hfunctional hfirstReverse hlastEdge
      subst last
      have hfirstColor : color = phase first := by
        simpa [layer, hfirstReverse] using hfirst.2
      have hlastColor : color = phase middle := by
        simpa [layer, hfirstEdge] using hlast.2
      exact halternating hfirstEdge (hfirstColor.symm.trans hlastColor)
    · by_cases hlastReverse : edge last middle
      · by_cases heq : first = last
        · subst last
          exact hfirstReverse hlastEdge
        · exact hmerge hfirstEdge hlastReverse heq last hlastEdge
      · have heq : first = last := by
          by_cases hmiddle : phase middle = 0
          · have hfirstSource : phase first ≠ 0 :=
              hsource_ne_zero_of_target_zero hfirstEdge hmiddle
            exact horientedBiUnique color |>.2
              (by simpa [layer, hfirstReverse, hfirstSource] using hfirst.2)
              (by simpa [layer, hlastReverse, hmiddle] using hlast.2)
          · have hfirstSource : phase first = 0 :=
              hsource_zero_of_target_ne_zero hfirstEdge hmiddle
            exact horientedBiUnique color |>.1
              (by simpa [layer, hfirstReverse, hfirstSource] using hfirst.2)
              (by simpa [layer, hlastReverse, hmiddle] using hlast.2)
        subst last
        exact hfirstReverse hlastEdge

omit [Fintype V] in
/-- The strict-rank form is a corollary: the functional relation's undirected graph is a forest,
whose standard two-coloring supplies the alternating phase. -/
public theorem exists_two_directedMatching_partition_of_strictRank
    (edge : V → V → Prop)
    (hfunctional : Relator.RightUnique edge)
    (hindegree : ∀ target, {source | edge source target}.encard ≤ 2)
    (hmerge : DoublePredecessorSink edge)
    (rank : V → ℕ)
    (hstrict : ∀ ⦃source target⦄, edge source target → rank source < rank target) :
    ∃ layer : Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target, layer color source target → edge source target) ∧
        (∀ color, Relator.BiUnique (layer color)) ∧
        ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne (layer color) := by
  let G : SimpleGraph V := SimpleGraph.fromRel edge
  have hforest : G.IsAcyclic :=
    fromRel_isAcyclic_of_strictRank edge hfunctional rank hstrict
  let phase : G.Coloring (Fin 2) := hforest.coloringTwo
  apply exists_two_directedMatching_partition_of_alternating
    edge hfunctional hindegree hmerge phase
  intro source target hstep
  exact phase.valid
    ⟨fun heq ↦ by
        subst target
        exact (Nat.lt_irrefl _) (hstrict hstep),
      Or.inl hstep⟩

/-- The acyclicity-form criterion. -/
public theorem exists_two_directedMatching_partition
    (edge : V → V → Prop)
    (hfunctional : Relator.RightUnique edge)
    (hindegree : ∀ target, {source | edge source target}.encard ≤ 2)
    (hmerge : DoublePredecessorSink edge)
    (hacyclic : ∀ vertex, ¬ TransGen edge vertex vertex) :
    ∃ layer : Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target, layer color source target → edge source target) ∧
        (∀ color, Relator.BiUnique (layer color)) ∧
        ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne (layer color) := by
  exact exists_two_directedMatching_partition_of_strictRank edge hfunctional hindegree hmerge
    (FiniteAcyclicRank.rank edge)
    (fun {_ _} hstep ↦ FiniteAcyclicRank.rank_lt_of_edge hacyclic hstep)

end Finite

end AlternatingMatchingCriterion

namespace LBA

variable {Γ Λ : Type*}

/-- Width-uniform parity form of the alternating-matching criterion.  This version permits raw
configuration cycles, provided every raw step flips the supplied phase. -/
public theorem Machine.hasTwoMatchingStepPartition_of_alternating
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : ∀ n, Relator.RightUnique (@Step Γ Λ n M))
    (hindegree : M.ConfigurationIndegreeAtMostTwo)
    (hmerge : ∀ n, AlternatingMatchingCriterion.DoublePredecessorSink (@Step Γ Λ n M))
    (phase : (n : ℕ) → DLBA.Cfg Γ Λ n → Fin 2)
    (halternating : ∀ n {source target}, Step M source target →
      phase n source ≠ phase n target) :
    M.HasTwoMatchingStepPartition := by
  classical
  choose layer hcover hsub hbiUnique hshort using fun n ↦
    AlternatingMatchingCriterion.exists_two_directedMatching_partition_of_alternating
      (@Step Γ Λ n M) (hfunctional n) (hindegree n) (hmerge n) (phase n)
        (fun {source target : DLBA.Cfg Γ Λ n} hstep ↦ halternating n hstep)
  exact ⟨layer, hcover, hsub, hbiUnique, hshort⟩

/-- Local transition functionality discharges the configuration-functionality premise of the
width-uniform parity criterion. -/
public theorem Machine.hasTwoMatchingStepPartition_of_localFunctional_alternating
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : M.Functional)
    (hindegree : M.ConfigurationIndegreeAtMostTwo)
    (hmerge : ∀ n, AlternatingMatchingCriterion.DoublePredecessorSink (@Step Γ Λ n M))
    (phase : (n : ℕ) → DLBA.Cfg Γ Λ n → Fin 2)
    (halternating : ∀ n {source target}, Step M source target →
      phase n source ≠ phase n target) :
    M.HasTwoMatchingStepPartition := by
  apply M.hasTwoMatchingStepPartition_of_alternating
    (hindegree := hindegree) (hmerge := hmerge) (phase := phase)
      (halternating := halternating)
  intro n source left right hleft hright
  rcases hleft with ⟨leftState, leftWrite, leftDir, hleftEnabled, rfl⟩
  rcases hright with ⟨rightState, rightWrite, rightDir, hrightEnabled, rfl⟩
  have hmove : (leftState, leftWrite, leftDir) =
      (rightState, rightWrite, rightDir) :=
    hfunctional source.state source.tape.read hleftEnabled hrightEnabled
  cases hmove
  rfl

/-- Width-uniform machine form of the alternating-matching criterion. -/
public theorem Machine.hasTwoMatchingStepPartition_of_functional_indegree_mergeSink_acyclic
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : ∀ n, Relator.RightUnique (@Step Γ Λ n M))
    (hindegree : M.ConfigurationIndegreeAtMostTwo)
    (hmerge : ∀ n, AlternatingMatchingCriterion.DoublePredecessorSink (@Step Γ Λ n M))
    (hacyclic : M.ConfigurationAcyclic) :
    M.HasTwoMatchingStepPartition := by
  classical
  choose layer hcover hsub hbiUnique hshort using fun n ↦
    AlternatingMatchingCriterion.exists_two_directedMatching_partition
      (@Step Γ Λ n M) (hfunctional n) (hindegree n) (hmerge n) (hacyclic n)
  exact ⟨layer, hcover, hsub, hbiUnique, hshort⟩

/-- Local transition functionality is sufficient for the right-uniqueness premise in the
machine criterion, including on clamped raw tapes. -/
public theorem Machine.hasTwoMatchingStepPartition_of_localFunctional_indegree_mergeSink_acyclic
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ)
    (hfunctional : M.Functional)
    (hindegree : M.ConfigurationIndegreeAtMostTwo)
    (hmerge : ∀ n, AlternatingMatchingCriterion.DoublePredecessorSink (@Step Γ Λ n M))
    (hacyclic : M.ConfigurationAcyclic) :
    M.HasTwoMatchingStepPartition := by
  apply M.hasTwoMatchingStepPartition_of_functional_indegree_mergeSink_acyclic
    (hindegree := hindegree) (hmerge := hmerge) (hacyclic := hacyclic)
  intro n source left right hleft hright
  rcases hleft with ⟨leftState, leftWrite, leftDir, hleftEnabled, rfl⟩
  rcases hright with ⟨rightState, rightWrite, rightDir, hrightEnabled, rfl⟩
  have hmove : (leftState, leftWrite, leftDir) =
      (rightState, rightWrite, rightDir) :=
    hfunctional source.state source.tape.read hleftEnabled hrightEnabled
  cases hmove
  rfl

end LBA

end
