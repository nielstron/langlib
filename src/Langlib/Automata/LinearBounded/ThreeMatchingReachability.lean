module

public import Langlib.Automata.LinearBounded.ExplicitDegreeTwoReachability
public import Langlib.Automata.LinearBounded.LinearTwoDiforestReachability
import Mathlib.Tactic

@[expose]
public section

/-!
# Splitting two partial-bijection layers into three directed matchings

Suppose a directed relation is partitioned exactly into two partial bijections.  Replace every
old vertex `v` by an input copy and an output copy.  The internal edge from the input copy to the
output copy receives a fresh third color, while an old edge from `u` to `v` goes from the output
copy of `u` to the input copy of `v` and retains its old color.

Every new color is a directed matching: no two edges of one color share a source or target, and
no two edges of one color are composable.  Reachability is preserved exactly from `input source`
to `output target`; in particular a reflexive old path is represented by the one internal edge.
The construction doubles the vertex set, preserves a directed degree-two bound, and preserves
ranked acyclicity.

The final corollary applies the construction to the explicit padded-clock serializer.  Its use
of `Fintype.equivFin` is intentionally noncomputable, so it is a finite structural normal form
and not a formally mechanized effective or logspace reduction.
-/

namespace ThreeMatchingReachability

open Relation Set

variable {V : Type*}

/-- Input and output copies of an old vertex. -/
public inductive Vertex (V : Type*) where
  | input (vertex : V)
  | output (vertex : V)
  deriving DecidableEq, Fintype

private def vertexEquiv (V : Type*) : Equiv (Vertex V) (V ⊕ V) where
  toFun
    | .input vertex => .inl vertex
    | .output vertex => .inr vertex
  invFun
    | .inl vertex => .input vertex
    | .inr vertex => .output vertex
  left_inv := by intro vertex; cases vertex <;> rfl
  right_inv := by intro vertex; cases vertex <;> rfl

/-- The split construction has exactly twice as many vertices. -/
public theorem card_vertex (V : Type*) [Fintype V] :
    Fintype.card (Vertex V) = Nat.mul 2 (Fintype.card V) := by
  rw [Fintype.card_congr (vertexEquiv V), Fintype.card_sum]
  exact (Nat.two_mul _).symm

/-- Forget whether a split vertex is an input or output copy. -/
@[expose]
public def project : Vertex V → V
  | .input vertex => vertex
  | .output vertex => vertex

/-- The new edge relation.  Internal edges go from input to output; old edges go from output to
input. -/
@[expose]
public def Edge (edge : V → V → Prop) : Vertex V → Vertex V → Prop
  | .input source, .output target => source = target
  | .output source, .input target => edge source target
  | _, _ => False

/-- Embed either old color into the first two of three new colors. -/
@[expose]
public def oldColor (color : Fin 2) : Fin 3 :=
  ⟨color.val, by omega⟩

public theorem oldColor_injective : Function.Injective oldColor := by
  intro left right heq
  apply Fin.ext
  exact Fin.mk.inj heq

/-- Neither embedded old color is the fresh third color. -/
public theorem oldColor_ne_two (color : Fin 2) : oldColor color ≠ (2 : Fin 3) := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [oldColor] at hval
  omega

/-- The three supplied layers.  Old colors zero and one label external edges; color two labels
all internal input-to-output edges. -/
@[expose]
public def Layer (layer : Fin 2 → V → V → Prop)
    (color : Fin 3) : Vertex V → Vertex V → Prop
  | .input source, .output target => source = target ∧ color = 2
  | .output source, .input target =>
      ∃ old, layer old source target ∧ oldColor old = color
  | _, _ => False

/-- The internal edge associated with an old vertex. -/
public theorem edge_internal (edge : V → V → Prop) (vertex : V) :
    Edge edge (.input vertex) (.output vertex) := by
  simp [Edge]

/-- An old edge gives the corresponding external split edge. -/
public theorem edge_external {edge : V → V → Prop} {source target : V}
    (h : edge source target) :
    Edge edge (.output source) (.input target) := by
  simpa [Edge] using h

/-- An old colored edge gives the corresponding new colored external edge. -/
public theorem layer_external {layer : Fin 2 → V → V → Prop}
    {color : Fin 2} {source target : V} (h : layer color source target) :
    Layer layer (oldColor color) (.output source) (.input target) := by
  exact ⟨color, h, rfl⟩

/-- Every internal edge belongs to the fresh matching color. -/
public theorem layer_internal (layer : Fin 2 → V → V → Prop) (vertex : V) :
    Layer layer 2 (.input vertex) (.output vertex) := by
  simp [Layer]

/-- Every new edge has exactly one supplied color, assuming the old relation has an exact
two-color cover. -/
public theorem edge_iff_existsUnique_layer
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (oldCover : ∀ source target, edge source target ↔
      ∃! color, layer color source target)
    (oldLayerSubEdge : ∀ color source target,
      layer color source target → edge source target)
    (source target : Vertex V) :
    Edge edge source target ↔ ∃! color, Layer layer color source target := by
  constructor
  · intro hedge
    rcases source with source | source
    · rcases target with target | target
      · exact False.elim hedge
      · change source = target at hedge
        subst target
        refine ⟨2, ⟨rfl, rfl⟩, ?_⟩
        intro color hcolor
        exact hcolor.2
    · rcases target with target | target
      · change edge source target at hedge
        obtain ⟨old, hold, hunique⟩ := (oldCover source target).mp hedge
        refine ⟨oldColor old, ⟨old, hold, rfl⟩, ?_⟩
        intro color hcolor
        obtain ⟨other, hother, hotherColor⟩ := hcolor
        have : other = old := hunique other hother
        simpa [this] using hotherColor.symm
      · exact False.elim hedge
  · rintro ⟨color, hcolor, _⟩
    rcases source with source | source
    · rcases target with target | target
      · exact False.elim hcolor
      · exact hcolor.1
    · rcases target with target | target
      · obtain ⟨old, hold, _⟩ := hcolor
        exact oldLayerSubEdge old source target hold
      · exact False.elim hcolor

/-- A new layer contains no spurious edges. -/
public theorem layer_sub_edge
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (oldLayerSubEdge : ∀ color source target,
      layer color source target → edge source target)
    {color : Fin 3} {source target : Vertex V}
    (h : Layer layer color source target) : Edge edge source target := by
  rcases source with source | source
  · rcases target with target | target
    · exact False.elim h
    · exact h.1
  · rcases target with target | target
    · obtain ⟨old, hold, _⟩ := h
      exact oldLayerSubEdge old source target hold
    · exact False.elim h

/-- Each new color is functional if both old colors are functional. -/
private theorem layer_rightUnique
    {layer : Fin 2 → V → V → Prop}
    (oldBiUnique : ∀ color, Relator.BiUnique (layer color))
    (color : Fin 3) : Relator.RightUnique (Layer layer color) := by
  intro source left right hleft hright
  rcases source with source | source <;>
    rcases left with left | left <;> rcases right with right | right <;>
    simp only [Layer] at hleft hright
  · exact congrArg Vertex.output (hleft.1.symm.trans hright.1)
  · obtain ⟨leftColor, hleftLayer, hleftColor⟩ := hleft
    obtain ⟨rightColor, hrightLayer, hrightColor⟩ := hright
    have hcolors : leftColor = rightColor :=
      oldColor_injective (hleftColor.trans hrightColor.symm)
    subst rightColor
    exact congrArg Vertex.input ((oldBiUnique leftColor).2 hleftLayer hrightLayer)

/-- Each new color is cofunctional if both old colors are cofunctional. -/
private theorem layer_leftUnique
    {layer : Fin 2 → V → V → Prop}
    (oldBiUnique : ∀ color, Relator.BiUnique (layer color))
    (color : Fin 3) : Relator.LeftUnique (Layer layer color) := by
  intro left right target hleft hright
  rcases target with target | target <;>
    rcases left with left | left <;> rcases right with right | right <;>
    simp only [Layer] at hleft hright
  · obtain ⟨leftColor, hleftLayer, hleftColor⟩ := hleft
    obtain ⟨rightColor, hrightLayer, hrightColor⟩ := hright
    have hcolors : leftColor = rightColor :=
      oldColor_injective (hleftColor.trans hrightColor.symm)
    subst rightColor
    exact congrArg Vertex.output ((oldBiUnique leftColor).1 hleftLayer hrightLayer)
  · exact congrArg Vertex.input (hleft.1.trans hright.1.symm)

/-- Each of the three new layers is a partial bijection. -/
public theorem layer_biUnique
    {layer : Fin 2 → V → V → Prop}
    (oldBiUnique : ∀ color, Relator.BiUnique (layer color))
    (color : Fin 3) : Relator.BiUnique (Layer layer color) :=
  ⟨layer_leftUnique oldBiUnique color, layer_rightUnique oldBiUnique color⟩

/-- No two edges of one new layer are composable: every layer is a directed matching. -/
public theorem layer_pathLengthAtMostOne
    (layer : Fin 2 → V → V → Prop) (color : Fin 3) :
    LinearTwoDiforestReachability.PathLengthAtMostOne (Layer layer color) := by
  intro first middle last hfirst hlast
  rcases first with first | first <;> rcases middle with middle | middle <;>
    rcases last with last | last <;> simp only [Layer] at hfirst hlast
  · obtain ⟨old, _, hold⟩ := hlast
    exact oldColor_ne_two old (hold.trans hfirst.2)
  · obtain ⟨old, _, hold⟩ := hfirst
    exact oldColor_ne_two old (hold.trans hlast.2)

/-! ## The contrasting two-matching boundary

For an exact union of only two directed matchings, an incoming edge consumes one color at its
target.  The no-composition condition forbids every outgoing edge from using that color, so all
outgoing edges use the one remaining color.  Functionality then makes the successor unique.
Consequently a genuine branch has no predecessor, and a branch encountered on a path rooted at
`source` must be `source` itself.  These are purely relational statements; no decision procedure
or complexity upper bound is asserted here.
-/

/-- A vertex is a genuine branch when it has two distinct immediate successors. -/
public def Branches (edge : V → V → Prop) (vertex : V) : Prop :=
  ∃ left right, edge vertex left ∧ edge vertex right ∧ left ≠ right

/-- In an exact union of two directed matchings, a vertex with a predecessor has a unique
successor whenever it has one. -/
public theorem successor_eq_of_incoming
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {predecessor vertex left right : V}
    (hincoming : edge predecessor vertex)
    (hleft : edge vertex left) (hright : edge vertex right) :
    left = right := by
  obtain ⟨incomingColor, hincomingLayer, _⟩ :=
    (cover predecessor vertex).mp hincoming
  obtain ⟨leftColor, hleftLayer, _⟩ := (cover vertex left).mp hleft
  obtain ⟨rightColor, hrightLayer, _⟩ := (cover vertex right).mp hright
  have hleftNe : leftColor ≠ incomingColor := by
    intro heq
    subst leftColor
    exact short incomingColor hincomingLayer hleftLayer
  have hrightNe : rightColor ≠ incomingColor := by
    intro heq
    subst rightColor
    exact short incomingColor hincomingLayer hrightLayer
  have hcolors : leftColor = rightColor := by
    fin_cases incomingColor <;> fin_cases leftColor <;> fin_cases rightColor <;>
      simp_all
  subst rightColor
  exact (biUnique leftColor).2 hleftLayer hrightLayer

/-- Fiber-cardinality form of `successor_eq_of_incoming`: every vertex with an incoming edge has
at most one distinct outgoing successor. -/
public theorem outdegreeAtMostOne_of_incoming
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {predecessor vertex : V} (hincoming : edge predecessor vertex) :
    Set.encard {target | edge vertex target} ≤ 1 := by
  apply Set.encard_le_one_iff.mpr
  intro left right hleft hright
  exact successor_eq_of_incoming cover biUnique short hincoming hleft hright

/-- A genuine branch in an exact union of two directed matchings has no predecessor. -/
public theorem no_predecessor_of_branches
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {vertex : V} (hbranch : Branches edge vertex) (predecessor : V) :
    ¬ edge predecessor vertex := by
  intro hincoming
  obtain ⟨left, right, hleft, hright, hne⟩ := hbranch
  exact hne (successor_eq_of_incoming cover biUnique short hincoming hleft hright)

/-- Along a path rooted at `source`, a genuine branch can occur only at the initial vertex. -/
public theorem eq_source_of_reaches_of_branches
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {source vertex : V} (hreach : ReflTransGen edge source vertex)
    (hbranch : Branches edge vertex) : vertex = source := by
  rcases ReflTransGen.cases_tail hreach with heq | ⟨predecessor, _, hlast⟩
  · exact heq
  · exact False.elim
      (no_predecessor_of_branches cover biUnique short hbranch predecessor hlast)

/-- Equivalently, every reachable noninitial vertex is nonbranching. -/
public theorem not_branches_of_reaches_of_ne_source
    {edge : V → V → Prop} {layer : Fin 2 → V → V → Prop}
    (cover : ∀ source target, edge source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {source vertex : V} (hreach : ReflTransGen edge source vertex)
    (hne : vertex ≠ source) : ¬ Branches edge vertex := by
  intro hbranch
  exact hne (eq_source_of_reaches_of_branches cover biUnique short hreach hbranch)

/-! ## Exact reachability preservation -/

/-- One old edge expands to an external edge followed by the target's internal edge. -/
public theorem reaches_output_of_edge
    {edge : V → V → Prop} {source target : V} (h : edge source target) :
    ReflTransGen (Edge edge) (.output source) (.output target) :=
  (ReflTransGen.single (edge_external h)).tail (edge_internal edge target)

/-- An old path lifts from the input copy of its source to the output copy of its target.  The
reflexive case is the single internal edge. -/
public theorem reaches_output_of_reaches
    {edge : V → V → Prop} {source target : V}
    (h : ReflTransGen edge source target) :
    ReflTransGen (Edge edge) (.input source) (.output target) := by
  induction h with
  | refl => exact ReflTransGen.single (edge_internal edge source)
  | tail _ hstep ih => exact ih.trans (reaches_output_of_edge hstep)

/-- A split edge either stutters under projection or projects to one old edge. -/
public theorem project_edge
    {edge : V → V → Prop} {source target : Vertex V}
    (h : Edge edge source target) :
    project source = project target ∨ edge (project source) (project target) := by
  rcases source with source | source <;> rcases target with target | target <;>
    simp only [Edge, project] at h ⊢
  all_goals aesop

/-- Projecting a split path deletes internal edges and retains external old edges. -/
public theorem reaches_project_of_reaches
    {edge : V → V → Prop} {source target : Vertex V}
    (h : ReflTransGen (Edge edge) source target) :
    ReflTransGen edge (project source) (project target) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases project_edge hstep with heq | hedge
      · simpa only [heq] using ih
      · exact ih.tail hedge

/-- Old reachability is exactly split reachability from an input copy to an output copy. -/
public theorem reaches_iff (edge : V → V → Prop) (source target : V) :
    ReflTransGen edge source target ↔
      ReflTransGen (Edge edge) (.input source) (.output target) := by
  constructor
  · exact reaches_output_of_reaches
  · intro h
    simpa [project] using reaches_project_of_reaches h

/-! ## Degree and ranked acyclicity -/

/-- Splitting preserves a directed degree-two bound.  Input copies have one outgoing internal
edge and inherit old indegree; output copies have one incoming internal edge and inherit old
outdegree. -/
public theorem directedDegreeAtMostTwo
    {edge : V → V → Prop}
    (hdegree : LayeredReachability.DirectedDegreeAtMost 2 edge) :
    LayeredReachability.DirectedDegreeAtMost 2 (Edge edge) := by
  constructor
  · intro source
    rcases source with source | source
    · calc
        Set.encard {target | Edge edge (.input source) target} ≤ 1 := by
          apply Set.encard_le_one_iff.mpr
          intro left right hleft hright
          rcases left with left | left <;> rcases right with right | right <;>
            simp only [Edge] at hleft hright
          all_goals try contradiction
          exact congrArg Vertex.output (hleft.symm.trans hright)
        _ ≤ 2 := by norm_num
    · calc
        Set.encard {target | Edge edge (.output source) target} ≤
            Set.encard {target | edge source target} := by
          apply Set.encard_le_encard_of_injOn (f := project)
          · intro target htarget
            rcases target with target | target <;> simp only [Edge, project] at htarget ⊢
            · exact htarget
            · contradiction
          · intro left hleft right hright heq
            rcases left with left | left <;> rcases right with right | right <;>
              simp only [Edge, project] at hleft hright heq
            all_goals try contradiction
            exact congrArg Vertex.input heq
        _ ≤ 2 := hdegree.1 source
  · intro target
    rcases target with target | target
    · calc
        Set.encard {source | Edge edge source (.input target)} ≤
            Set.encard {source | edge source target} := by
          apply Set.encard_le_encard_of_injOn (f := project)
          · intro source hsource
            rcases source with source | source <;> simp only [Edge, project] at hsource ⊢
            · contradiction
            · exact hsource
          · intro left hleft right hright heq
            rcases left with left | left <;> rcases right with right | right <;>
              simp only [Edge, project] at hleft hright heq
            all_goals try contradiction
            exact congrArg Vertex.output heq
        _ ≤ 2 := hdegree.2 target
    · calc
        Set.encard {source | Edge edge source (.output target)} ≤ 1 := by
          apply Set.encard_le_one_iff.mpr
          intro left right hleft hright
          rcases left with left | left <;> rcases right with right | right <;>
            simp only [Edge] at hleft hright
          all_goals try contradiction
          exact congrArg Vertex.input (hleft.trans hright.symm)
        _ ≤ 2 := by norm_num

/-- Lift an old rank by placing the input copy just below the output copy. -/
@[expose]
public def liftedRank (rank : V → ℕ) : Vertex V → ℕ
  | .input vertex => Nat.mul 2 (rank vertex)
  | .output vertex => Nat.mul 2 (rank vertex) + 1

/-- Every split edge raises the lifted rank when every old edge raises the old rank. -/
public theorem liftedRank_lt_of_edge
    {edge : V → V → Prop} (rank : V → ℕ)
    (hrank : ∀ {source target}, edge source target → rank source < rank target)
    {source target : Vertex V} (h : Edge edge source target) :
    liftedRank rank source < liftedRank rank target := by
  rcases source with source | source <;> rcases target with target | target <;>
    simp only [Edge, liftedRank] at h ⊢
  · subst target
    exact Nat.lt_succ_self _
  · calc
      Nat.mul 2 (rank source) + 1 < Nat.mul 2 (rank source + 1) := by
        have hmul : Nat.mul 2 (Nat.succ (rank source)) =
            Nat.mul 2 (rank source) + 2 := Nat.mul_succ 2 (rank source)
        rw [show rank source + 1 = Nat.succ (rank source) by omega, hmul]
        omega
      _ ≤ Nat.mul 2 (rank target) :=
        Nat.mul_le_mul_left 2 (Nat.succ_le_iff.mpr (hrank h))

/-- Every nonempty split path raises the lifted rank. -/
public theorem liftedRank_lt_of_transGen
    {edge : V → V → Prop} (rank : V → ℕ)
    (hrank : ∀ {source target}, edge source target → rank source < rank target)
    {source target : Vertex V} (h : TransGen (Edge edge) source target) :
    liftedRank rank source < liftedRank rank target := by
  induction h with
  | single hstep => exact liftedRank_lt_of_edge rank hrank hstep
  | tail _ hstep ih => exact ih.trans (liftedRank_lt_of_edge rank hrank hstep)

/-- A ranked old relation yields an acyclic split relation. -/
public theorem acyclic_of_rank
    {edge : V → V → Prop} (rank : V → ℕ)
    (hrank : ∀ {source target}, edge source target → rank source < rank target)
    (vertex : Vertex V) : ¬ TransGen (Edge edge) vertex vertex := by
  intro hcycle
  exact (Nat.lt_irrefl _) (liftedRank_lt_of_transGen rank hrank hcycle)

/-! ## Three-matching normal form for arbitrary finite reachability -/

/-- Split vertices over the degree-serialized padded clock graph. -/
public abbrev ClockSplitVertex (V : Type*) [Fintype V] :=
  Vertex (ExplicitDegreeTwoReachability.ClockSerializedVertex V)

/-- The three-matching relation obtained from the degree-serialized padded clock graph. -/
public noncomputable def clockSplitEdge {V : Type*} [Fintype V]
    (edge : V → V → Prop) : ClockSplitVertex V → ClockSplitVertex V → Prop :=
  Edge (ExplicitDegreeTwoReachability.clockSerializedEdge edge)

/-- One of the three supplied matching layers. -/
public noncomputable def clockSplitLayer {V : Type*} [Fintype V]
    (edge : V → V → Prop) (color : Fin 3) :
    ClockSplitVertex V → ClockSplitVertex V → Prop :=
  Layer (ExplicitDegreeTwoReachability.clockSerializedLayer edge) color

/-- The designated split source. -/
public noncomputable def clockSplitSource {V : Type*} [Fintype V]
    (source : V) : ClockSplitVertex V :=
  .input (ExplicitDegreeTwoReachability.clockSerializedSource source)

/-- The designated split target. -/
public noncomputable def clockSplitTarget {V : Type*} [Fintype V]
    (target : V) : ClockSplitVertex V :=
  .output (ExplicitDegreeTwoReachability.clockSerializedTarget target)

/-- A strict natural rank on the degree-serialized padded clock graph. -/
private noncomputable def clockSerializedRank (V : Type*) [Fintype V] :
    ExplicitDegreeTwoReachability.ClockSerializedVertex V → ℕ :=
  ExplicitDegreeTwoReachability.liftedRank
    (fun index => ((ExplicitDegreeTwoReachability.clockNumbering V).symm index).2.val)

private theorem clockSerializedRank_lt
    {V : Type*} [Fintype V] {edge : V → V → Prop}
    {source target : ExplicitDegreeTwoReachability.ClockSerializedVertex V}
    (h : ExplicitDegreeTwoReachability.clockSerializedEdge edge source target) :
    clockSerializedRank V source < clockSerializedRank V target := by
  apply ExplicitDegreeTwoReachability.liftedRank_lt_of_edge
    (edge := ExplicitDegreeTwoReachability.numberedClockEdge edge)
  · intro old new hstep
    exact LayeredReachability.edge_layer_lt (edge := edge) hstep
  · exact h

/-- Arbitrary finite reachability has an acyclic directed-degree-two presentation whose edges
are partitioned exactly into three supplied directed matchings.  The source and target are
designated vertices.  The structural numbering is noncomputable, so this theorem asserts no
complexity bound for constructing the presentation. -/
public theorem finiteReachability_designated_threeMatchings
    {V : Type*} [Fintype V]
    (edge : V → V → Prop) (source target : V) :
    (ReflTransGen edge source target ↔
      ReflTransGen (clockSplitEdge edge)
        (clockSplitSource source) (clockSplitTarget target)) ∧
      (∀ vertex, ¬ TransGen (clockSplitEdge edge) vertex vertex) ∧
      LayeredReachability.DirectedDegreeAtMost 2 (clockSplitEdge edge) ∧
      (∀ old new, clockSplitEdge edge old new ↔
        ∃! color, clockSplitLayer edge color old new) ∧
      (∀ color old new, clockSplitLayer edge color old new →
        clockSplitEdge edge old new) ∧
      (∀ color, Relator.BiUnique (clockSplitLayer edge color)) ∧
      ∀ color, LinearTwoDiforestReachability.PathLengthAtMostOne
        (clockSplitLayer edge color) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ExplicitDegreeTwoReachability.reaches_iff_clockSerialized edge source target).trans
      (reaches_iff (ExplicitDegreeTwoReachability.clockSerializedEdge edge)
        (ExplicitDegreeTwoReachability.clockSerializedSource source)
        (ExplicitDegreeTwoReachability.clockSerializedTarget target))
  · exact acyclic_of_rank (clockSerializedRank V)
      (@clockSerializedRank_lt V _ edge)
  · exact directedDegreeAtMostTwo
      (ExplicitDegreeTwoReachability.clockSerialized_directedDegreeAtMostTwo edge)
  · exact edge_iff_existsUnique_layer
      (ExplicitDegreeTwoReachability.clockSerialized_edge_iff_existsUnique_layer edge)
      (ExplicitDegreeTwoReachability.clockSerialized_layer_sub_edge edge)
  · intro color old new h
    exact layer_sub_edge
      (ExplicitDegreeTwoReachability.clockSerialized_layer_sub_edge edge) h
  · exact layer_biUnique
      (ExplicitDegreeTwoReachability.clockSerialized_layer_biUnique edge)
  · exact layer_pathLengthAtMostOne _

end ThreeMatchingReachability

end
