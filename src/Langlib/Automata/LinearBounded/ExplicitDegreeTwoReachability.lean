module

public import Langlib.Automata.LinearBounded.LayeredReachability
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relator
import Mathlib.Tactic

@[expose]
public section

/-!
# An explicit degree-two serializer for finite reachability

This module replaces every edge of a relation on `Fin n` by a path through two finite
scans.  An outgoing scan selects the target, a bridge records the selected original edge, and an
incoming merge scan leads to the target core vertex.  The construction has one distinguished
core vertex for every original vertex and preserves core-to-core reachability exactly.

The serialized relation has a syntactic two-coloring.  Scan edges have color zero and bridge
edges have color one; each color is both functional and cofunctional.  Consequently both
directed degrees are at most two.  A ranked input relation yields a ranked, hence acyclic,
serialized relation.

The final corollary first applies ordinary padded clock layering and then this serializer.  It
therefore turns arbitrary finite directed reachability into reachability between one designated
source and one designated target in an acyclic degree-two graph with an explicit
two-partial-bijection partition.
-/

namespace ExplicitDegreeTwoReachability

open Relation Set

/-- Vertices of the degree serializer for a graph with `n` numbered vertices.

The two scan indices range over `Fin (n + 1)`.  The final outgoing position is a dead end, while
the final merge position exits to the target core. -/
public inductive Vertex (n : ℕ) where
  | core (vertex : Fin n)
  | outScan (source : Fin n) (index : Fin (n + 1))
  | bridge (source target : Fin n)
  | mergeScan (target : Fin n) (index : Fin (n + 1))
  deriving DecidableEq, Fintype

private def vertexEquiv (n : ℕ) :
    Vertex n ≃
      Fin n ⊕ (Fin n × Fin (n + 1)) ⊕
        (Fin n × Fin n) ⊕ (Fin n × Fin (n + 1)) where
  toFun
    | .core vertex => .inl vertex
    | .outScan source index => .inr (.inl (source, index))
    | .bridge source target => .inr (.inr (.inl (source, target)))
    | .mergeScan target index => .inr (.inr (.inr (target, index)))
  invFun
    | .inl vertex => .core vertex
    | .inr (.inl (source, index)) => .outScan source index
    | .inr (.inr (.inl (source, target))) => .bridge source target
    | .inr (.inr (.inr (target, index))) => .mergeScan target index
  left_inv := by intro vertex; cases vertex <;> rfl
  right_inv := by rintro (vertex | vertex | vertex | vertex) <;> rfl

/-- The serializer has exactly `3 * n ^ 2 + 3 * n` vertices. -/
public theorem card_vertex (n : ℕ) :
    Fintype.card (Vertex n) =
      Nat.mul (Nat.mul 3 n) n + Nat.mul 3 n := by
  rw [Fintype.card_congr (vertexEquiv n)]
  simp
  ring

/-- The serialized edge relation.

The two scans use the natural order on `Fin (n + 1)`.  A bridge is traversable exactly when its
pair of indices is an original edge. -/
@[expose]
public def Edge {n : ℕ} (edge : Fin n → Fin n → Prop) :
    Vertex n → Vertex n → Prop
  | .core source, .outScan source' index =>
      source = source' ∧ index = 0
  | .outScan source index, .outScan source' index' =>
      source = source' ∧ index.val < n ∧ index'.val = index.val + 1
  | .outScan source index, .bridge source' target =>
      source = source' ∧ index = target.castSucc ∧ edge source target
  | .bridge source target, .mergeScan target' index =>
      target = target' ∧ index = source.castSucc ∧ edge source target
  | .mergeScan target index, .mergeScan target' index' =>
      target = target' ∧ index.val < n ∧ index'.val = index.val + 1
  | .mergeScan target index, .core target' =>
      target = target' ∧ index = Fin.last n
  | _, _ => False

/-- Enter the outgoing scan at its zero position. -/
private theorem edge_enter {n : ℕ} (edge : Fin n → Fin n → Prop)
    (source : Fin n) :
    Edge edge (.core source) (.outScan source 0) := by
  simp [Edge]

/-- Advance an outgoing scan by one position. -/
private theorem edge_outSkip {n : ℕ} (edge : Fin n → Fin n → Prop)
    (source index : Fin n) :
    Edge edge (.outScan source index.castSucc) (.outScan source index.succ) := by
  simp [Edge]

/-- Select an enabled original edge at its outgoing scan position. -/
private theorem edge_choose {n : ℕ} {edge : Fin n → Fin n → Prop}
    {source target : Fin n} (h : edge source target) :
    Edge edge (.outScan source target.castSucc) (.bridge source target) := by
  simp [Edge, h]

/-- Commit a selected original edge to its target merge scan. -/
private theorem edge_commit {n : ℕ} {edge : Fin n → Fin n → Prop}
    {source target : Fin n} (h : edge source target) :
    Edge edge (.bridge source target) (.mergeScan target source.castSucc) := by
  simp [Edge, h]

/-- Advance an incoming merge scan by one position. -/
private theorem edge_mergeSkip {n : ℕ} (edge : Fin n → Fin n → Prop)
    (target index : Fin n) :
    Edge edge (.mergeScan target index.castSucc) (.mergeScan target index.succ) := by
  simp [Edge]

/-- Exit the final incoming merge position at its target core. -/
private theorem edge_exit {n : ℕ} (edge : Fin n → Fin n → Prop)
    (target : Fin n) :
    Edge edge (.mergeScan target (Fin.last n)) (.core target) := by
  simp [Edge]

/-- Project every serializer phase to the original vertex whose macrostep is currently being
executed.  The projection changes only on a bridge-to-merge edge. -/
@[expose]
public def project {n : ℕ} : Vertex n → Fin n
  | .core vertex => vertex
  | .outScan source _ => source
  | .bridge source _ => source
  | .mergeScan target _ => target

/-- The two syntactic edge colors.  The two bridge phases have color one; all scan and core
phases have color zero. -/
@[expose]
public def edgeColor {n : ℕ} : Vertex n → Vertex n → Fin 2
  | .outScan _ _, .bridge _ _ => 1
  | .bridge _ _, .mergeScan _ _ => 1
  | _, _ => 0

/-- One syntactic layer of the serialized relation. -/
@[expose]
public def Layer {n : ℕ} (edge : Fin n → Fin n → Prop)
    (color : Fin 2) (old new : Vertex n) : Prop :=
  Edge edge old new ∧ edgeColor old new = color

/-- Every serialized edge has exactly one syntactic color. -/
public theorem edge_iff_existsUnique_layer {n : ℕ}
    (edge : Fin n → Fin n → Prop) (old new : Vertex n) :
    Edge edge old new ↔ ∃! color, Layer edge color old new := by
  constructor
  · intro hedge
    refine ⟨edgeColor old new, ⟨hedge, rfl⟩, ?_⟩
    intro color hcolor
    exact hcolor.2.symm
  · rintro ⟨_, hcolor, _⟩
    exact hcolor.1

/-- A syntactic layer contains no nonedges. -/
public theorem layer_sub_edge {n : ℕ}
    (edge : Fin n → Fin n → Prop)
    (color : Fin 2) (old new : Vertex n)
    (hlayer : Layer edge color old new) :
    Edge edge old new :=
  hlayer.1

private theorem layer_rightUnique {n : ℕ}
    (edge : Fin n → Fin n → Prop) (color : Fin 2) :
    Relator.RightUnique (Layer edge color) := by
  intro source left right hleft hright
  rcases hleft with ⟨hleft, hleftColor⟩
  rcases hright with ⟨hright, hrightColor⟩
  rcases source with source | ⟨source, index⟩ | ⟨source, target⟩ | ⟨target, index⟩ <;>
    rcases left with left | ⟨leftSource, leftIndex⟩ | ⟨leftSource, leftTarget⟩ |
      ⟨leftTarget, leftIndex⟩ <;>
    rcases right with right | ⟨rightSource, rightIndex⟩ |
      ⟨rightSource, rightTarget⟩ | ⟨rightTarget, rightIndex⟩ <;>
    simp only [Edge] at hleft hright
  all_goals fin_cases color <;> simp_all [edgeColor]
  all_goals (apply Fin.ext; omega)

private theorem layer_leftUnique {n : ℕ}
    (edge : Fin n → Fin n → Prop) (color : Fin 2) :
    Relator.LeftUnique (Layer edge color) := by
  intro left right target hleft hright
  rcases hleft with ⟨hleft, hleftColor⟩
  rcases hright with ⟨hright, hrightColor⟩
  rcases target with target | ⟨targetSource, targetIndex⟩ |
      ⟨targetSource, targetTarget⟩ | ⟨targetTarget, targetIndex⟩ <;>
    rcases left with left | ⟨leftSource, leftIndex⟩ | ⟨leftSource, leftTarget⟩ |
      ⟨leftTarget, leftIndex⟩ <;>
    rcases right with right | ⟨rightSource, rightIndex⟩ |
      ⟨rightSource, rightTarget⟩ | ⟨rightTarget, rightIndex⟩ <;>
    simp only [Edge] at hleft hright
  all_goals fin_cases color <;> simp_all [edgeColor]
  all_goals (apply Fin.ext; omega)

/-- Each syntactic layer is both functional and cofunctional. -/
public theorem layer_biUnique {n : ℕ}
    (edge : Fin n → Fin n → Prop) (color : Fin 2) :
    Relator.BiUnique (Layer edge color) :=
  ⟨layer_leftUnique edge color, layer_rightUnique edge color⟩

/-- The two functional layers bound every successor fiber by two. -/
public theorem outdegreeAtMostTwo {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    LayeredReachability.OutdegreeAtMost 2 (Edge edge) := by
  intro old
  calc
    Set.encard {new | Edge edge old new} ≤
        Set.encard (Set.univ : Set (Fin 2)) := by
      apply Set.encard_le_encard_of_injOn (f := fun new => edgeColor old new)
      · intro new _
        exact Set.mem_univ _
      · intro left hleft right hright hcolor
        exact (layer_biUnique edge (edgeColor old left)).2
          ⟨hleft, rfl⟩ ⟨hright, hcolor.symm⟩
    _ = 2 := by
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      norm_num

/-- The two cofunctional layers bound every predecessor fiber by two. -/
public theorem indegreeAtMostTwo {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    LayeredReachability.IndegreeAtMost 2 (Edge edge) := by
  intro new
  calc
    Set.encard {old | Edge edge old new} ≤
        Set.encard (Set.univ : Set (Fin 2)) := by
      apply Set.encard_le_encard_of_injOn (f := fun old => edgeColor old new)
      · intro old _
        exact Set.mem_univ _
      · intro left hleft right hright hcolor
        exact (layer_biUnique edge (edgeColor left new)).1
          ⟨hleft, rfl⟩ ⟨hright, hcolor.symm⟩
    _ = 2 := by
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      norm_num

/-- Both directed degrees of the serialized relation are at most two. -/
public theorem directedDegreeAtMostTwo {n : ℕ}
    (edge : Fin n → Fin n → Prop) :
    LayeredReachability.DirectedDegreeAtMost 2 (Edge edge) :=
  ⟨outdegreeAtMostTwo edge, indegreeAtMostTwo edge⟩

/-! ## Exact preservation of core reachability -/

/-- Every outgoing scan position is reachable from position zero. -/
public theorem reaches_outScan {n : ℕ} (edge : Fin n → Fin n → Prop)
    (source : Fin n) (index : Fin (n + 1)) :
    ReflTransGen (Edge edge) (.outScan source 0) (.outScan source index) := by
  induction index using Fin.induction with
  | zero => exact .refl
  | succ index ih => exact ih.tail (edge_outSkip edge source index)

/-- Every merge scan position reaches its target core. -/
public theorem reaches_core_of_mergeScan {n : ℕ} (edge : Fin n → Fin n → Prop)
    (target : Fin n) (index : Fin (n + 1)) :
    ReflTransGen (Edge edge) (.mergeScan target index) (.core target) := by
  induction hremaining : n - index.val using Nat.strong_induction_on generalizing index with
  | h remaining ih =>
      by_cases hnext : index.val < n
      · let current : Fin n := ⟨index.val, hnext⟩
        let next : Fin (n + 1) := ⟨index.val + 1, by omega⟩
        have hsmaller : n - next.val < remaining := by
          dsimp [next]
          omega
        have htail := ih (n - next.val) hsmaller next rfl
        have hstep :
            Edge edge (.mergeScan target index) (.mergeScan target next) := by
          simpa [current, next] using edge_mergeSkip edge target current
        exact ReflTransGen.head hstep htail
      · have hlast : index = Fin.last n := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst index
        exact ReflTransGen.single (edge_exit edge target)

/-- One original edge expands to a complete path between its core endpoints. -/
public theorem reaches_core_of_edge {n : ℕ} {edge : Fin n → Fin n → Prop}
    {source target : Fin n} (h : edge source target) :
    ReflTransGen (Edge edge) (.core source) (.core target) := by
  exact
    (ReflTransGen.single (edge_enter edge source)).trans
      ((reaches_outScan edge source target.castSucc).trans
        ((ReflTransGen.single (edge_choose h)).trans
          ((ReflTransGen.single (edge_commit h)).trans
            (reaches_core_of_mergeScan edge target source.castSucc))))

/-- Every original path lifts to a path between the corresponding core vertices. -/
public theorem reaches_core_of_reaches {n : ℕ} {edge : Fin n → Fin n → Prop}
    {source target : Fin n} (h : ReflTransGen edge source target) :
    ReflTransGen (Edge edge) (.core source) (.core target) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans (reaches_core_of_edge hstep)

/-- A serializer edge either stutters under projection or performs one original edge. -/
public theorem project_edge {n : ℕ} {edge : Fin n → Fin n → Prop}
    {old new : Vertex n} (h : Edge edge old new) :
    project old = project new ∨ edge (project old) (project new) := by
  rcases old with old | ⟨oldSource, oldIndex⟩ | ⟨oldSource, oldTarget⟩ |
      ⟨oldTarget, oldIndex⟩ <;>
    rcases new with new | ⟨newSource, newIndex⟩ | ⟨newSource, newTarget⟩ |
      ⟨newTarget, newIndex⟩ <;>
    simp only [Edge, project] at h ⊢
  all_goals aesop

/-- Projecting a serialized path deletes its scan stutters and retains its committed original
edges. -/
public theorem reaches_project_of_reaches {n : ℕ} {edge : Fin n → Fin n → Prop}
    {old new : Vertex n} (h : ReflTransGen (Edge edge) old new) :
    ReflTransGen edge (project old) (project new) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases project_edge hstep with heq | hedge
      · simpa only [heq] using ih
      · exact ih.tail hedge

/-- Exact source-to-target reachability equivalence for the degree serializer. -/
public theorem reaches_iff {n : ℕ} (edge : Fin n → Fin n → Prop)
    (source target : Fin n) :
    ReflTransGen edge source target ↔
      ReflTransGen (Edge edge) (.core source) (.core target) := by
  constructor
  · exact reaches_core_of_reaches
  · intro h
    simpa [project] using reaches_project_of_reaches h

/-! ## Preservation of ranks and acyclicity -/

/-- Number of serializer phases reserved inside one original rank. -/
@[expose]
public def phaseStride (n : ℕ) : ℕ :=
  n + n + 4

/-- Position of a serializer vertex inside the rank block of its projection. -/
@[expose]
public def phase {n : ℕ} : Vertex n → ℕ
  | .mergeScan _ index => index.val
  | .core _ => n + 1
  | .outScan _ index => n + 2 + index.val
  | .bridge _ _ => n + n + 3

/-- Every serializer phase fits strictly below the block stride. -/
public theorem phase_lt_stride {n : ℕ} (vertex : Vertex n) :
    phase vertex < phaseStride n := by
  cases vertex with
  | core vertex =>
      simp only [phase, phaseStride]
      omega
  | outScan source index =>
      have hindex := index.isLt
      simp only [phase, phaseStride]
      omega
  | bridge source target =>
      simp only [phase, phaseStride]
      omega
  | mergeScan target index =>
      have hindex := index.isLt
      simp only [phase, phaseStride]
      omega

/-- Lift an original natural-valued rank to the serializer. -/
@[expose]
public def liftedRank {n : ℕ} (rank : Fin n → ℕ) (vertex : Vertex n) : ℕ :=
  Nat.mul (rank (project vertex)) (phaseStride n) + phase vertex

/-- A lower major rank dominates any reset of the bounded serializer phase. -/
private theorem lexPhase_lt
    {major major' phase phase' stride : ℕ}
    (hmajor : major < major') (hphase : phase < stride) :
    Nat.mul major stride + phase < Nat.mul major' stride + phase' := by
  calc
    Nat.mul major stride + phase < Nat.mul major stride + stride :=
      Nat.add_lt_add_left hphase _
    _ = Nat.mul (major + 1) stride := by simp [Nat.add_mul]
    _ ≤ Nat.mul major' stride :=
      Nat.mul_le_mul_right stride (Nat.succ_le_iff.mpr hmajor)
    _ ≤ Nat.mul major' stride + phase' := Nat.le_add_right _ _

/-- A serializer edge either advances within one projected rank block or commits one original
edge. -/
private theorem phase_lt_or_project_edge {n : ℕ} {edge : Fin n → Fin n → Prop}
    {old new : Vertex n} (h : Edge edge old new) :
    (project old = project new ∧ phase old < phase new) ∨
      edge (project old) (project new) := by
  rcases old with old | ⟨oldSource, oldIndex⟩ | ⟨oldSource, oldTarget⟩ |
      ⟨oldTarget, oldIndex⟩ <;>
    rcases new with new | ⟨newSource, newIndex⟩ | ⟨newSource, newTarget⟩ |
      ⟨newTarget, newIndex⟩ <;>
    simp only [Edge, project, phase] at h ⊢
  case bridge.mergeScan =>
    exact Or.inr (by simpa [h.1] using h.2.2)
  all_goals simp_all
  all_goals omega

/-- If every original edge strictly raises `rank`, every serialized edge strictly raises the
lifted rank. -/
public theorem liftedRank_lt_of_edge {n : ℕ} {edge : Fin n → Fin n → Prop}
    (rank : Fin n → ℕ)
    (hrank : ∀ {old new}, edge old new → rank old < rank new)
    {old new : Vertex n} (h : Edge edge old new) :
    liftedRank rank old < liftedRank rank new := by
  rcases phase_lt_or_project_edge h with ⟨hproject, hphase⟩ | hedge
  · simp only [liftedRank, hproject]
    exact Nat.add_lt_add_left hphase _
  · exact lexPhase_lt (hrank hedge) (phase_lt_stride old)

/-- Every nonempty serialized path strictly raises the lifted rank. -/
public theorem liftedRank_lt_of_transGen {n : ℕ} {edge : Fin n → Fin n → Prop}
    (rank : Fin n → ℕ)
    (hrank : ∀ {old new}, edge old new → rank old < rank new)
    {old new : Vertex n} (h : TransGen (Edge edge) old new) :
    liftedRank rank old < liftedRank rank new := by
  induction h with
  | single hstep => exact liftedRank_lt_of_edge rank hrank hstep
  | tail _ hstep ih => exact ih.trans (liftedRank_lt_of_edge rank hrank hstep)

/-- A ranked input relation has an acyclic serialized relation. -/
public theorem acyclic_of_rank {n : ℕ} {edge : Fin n → Fin n → Prop}
    (rank : Fin n → ℕ)
    (hrank : ∀ {old new}, edge old new → rank old < rank new)
    (vertex : Vertex n) :
    ¬ TransGen (Edge edge) vertex vertex := by
  intro hcycle
  exact (Nat.lt_irrefl _) (liftedRank_lt_of_transGen rank hrank hcycle)

/-- One original edge expands to a genuinely nonempty serialized path. -/
public theorem transGen_core_of_edge {n : ℕ} {edge : Fin n → Fin n → Prop}
    {source target : Fin n} (h : edge source target) :
    TransGen (Edge edge) (.core source) (.core target) := by
  apply TransGen.head' (edge_enter edge source)
  exact
    (reaches_outScan edge source target.castSucc).trans
      ((ReflTransGen.single (edge_choose h)).trans
        ((ReflTransGen.single (edge_commit h)).trans
          (reaches_core_of_mergeScan edge target source.castSucc)))

/-- Every nonempty original path lifts to a nonempty serialized path. -/
public theorem transGen_core_of_transGen {n : ℕ} {edge : Fin n → Fin n → Prop}
    {source target : Fin n} (h : TransGen edge source target) :
    TransGen (Edge edge) (.core source) (.core target) := by
  induction h with
  | single hstep => exact transGen_core_of_edge hstep
  | tail _ hstep ih => exact ih.trans (transGen_core_of_edge hstep)

/-- A nonempty serialized path either strictly advances inside one projection fiber or projects
to a genuinely nonempty original path. -/
public theorem phase_lt_or_project_transGen {n : ℕ}
    {edge : Fin n → Fin n → Prop} {old new : Vertex n}
    (h : TransGen (Edge edge) old new) :
    (project old = project new ∧ phase old < phase new) ∨
      TransGen edge (project old) (project new) := by
  induction h with
  | single hstep =>
      rcases phase_lt_or_project_edge hstep with hstutter | hproject
      · exact Or.inl hstutter
      · exact Or.inr (.single hproject)
  | @tail middle new hpath hstep ih =>
      rcases ih with ⟨hprojectPath, hphasePath⟩ | hprojectPath
      · rcases phase_lt_or_project_edge hstep with
          ⟨hprojectStep, hphaseStep⟩ | hprojectStep
        · exact Or.inl ⟨hprojectPath.trans hprojectStep,
            hphasePath.trans hphaseStep⟩
        · apply Or.inr
          rw [hprojectPath]
          exact .single hprojectStep
      · rcases phase_lt_or_project_edge hstep with
          ⟨hprojectStep, _hphaseStep⟩ | hprojectStep
        · apply Or.inr
          rw [hprojectStep] at hprojectPath
          exact hprojectPath
        · exact Or.inr (hprojectPath.tail hprojectStep)

/-- Every serialized cycle reflects to an original cycle at its projected vertex. -/
public theorem transGen_cycle_project {n : ℕ} {edge : Fin n → Fin n → Prop}
    {vertex : Vertex n} (h : TransGen (Edge edge) vertex vertex) :
    TransGen edge (project vertex) (project vertex) := by
  rcases phase_lt_or_project_transGen h with ⟨_, hphase⟩ | hproject
  · exact False.elim ((Nat.lt_irrefl _) hphase)
  · exact hproject

/-- Serialization preserves and reflects acyclicity exactly. -/
public theorem acyclic_iff {n : ℕ} (edge : Fin n → Fin n → Prop) :
    (∀ vertex, ¬ TransGen (Edge edge) vertex vertex) ↔
      ∀ vertex, ¬ TransGen edge vertex vertex := by
  constructor
  · intro hserialized vertex hcycle
    exact hserialized (.core vertex) (transGen_core_of_transGen hcycle)
  · intro horiginal vertex hcycle
    exact horiginal (project vertex) (transGen_cycle_project hcycle)

/-! ## Arbitrary finite reachability with one designated target -/

/-- The padded clock graph of an arbitrary finite vertex type. -/
public abbrev ClockVertex (V : Type*) [Fintype V] :=
  LayeredReachability.Vertex V

/-- A structural numbering of all padded clock vertices.

This uses `Fintype.equivFin` and is intentionally noncomputable.  The corollaries below therefore
assert a finite structural reduction, not an effective or logspace graph encoding. -/
public noncomputable def clockNumbering (V : Type*) [Fintype V] :
    ClockVertex V ≃ Fin (Fintype.card (ClockVertex V)) :=
  Fintype.equivFin _

/-- The padded clock relation transported to its finite numbering. -/
public noncomputable def numberedClockEdge {V : Type*} [Fintype V]
    (edge : V → V → Prop) :
    Fin (Fintype.card (ClockVertex V)) →
      Fin (Fintype.card (ClockVertex V)) → Prop :=
  fun old new => LayeredReachability.Edge edge
    ((clockNumbering V).symm old) ((clockNumbering V).symm new)

/-- Vertices of the degree-serialized padded clock graph. -/
public abbrev ClockSerializedVertex (V : Type*) [Fintype V] :=
  Vertex (Fintype.card (ClockVertex V))

/-- The degree-serialized padded clock relation. -/
public noncomputable def clockSerializedEdge {V : Type*} [Fintype V]
    (edge : V → V → Prop) :
    ClockSerializedVertex V → ClockSerializedVertex V → Prop :=
  Edge (numberedClockEdge edge)

/-- One explicit syntactic layer of the degree-serialized padded clock relation. -/
public noncomputable def clockSerializedLayer {V : Type*} [Fintype V]
    (edge : V → V → Prop) (color : Fin 2) :
    ClockSerializedVertex V → ClockSerializedVertex V → Prop :=
  Layer (numberedClockEdge edge) color

/-- The designated source core corresponding to the bottom clock copy of `source`. -/
public noncomputable def clockSerializedSource {V : Type*} [Fintype V]
    (source : V) : ClockSerializedVertex V :=
  .core (clockNumbering V (LayeredReachability.bottom source))

/-- The designated target core corresponding to the top clock copy of `target`. -/
public noncomputable def clockSerializedTarget {V : Type*} [Fintype V]
    (target : V) : ClockSerializedVertex V :=
  .core (clockNumbering V (LayeredReachability.top target))

/-- Numbering the padded clock graph preserves reachability exactly. -/
private theorem numberedClock_reaches_iff {V : Type*} [Fintype V]
    (edge : V → V → Prop) (source target : ClockVertex V) :
    ReflTransGen (numberedClockEdge edge)
        (clockNumbering V source) (clockNumbering V target) ↔
      ReflTransGen (LayeredReachability.Edge edge) source target := by
  constructor
  · intro h
    have hdecoded :
        ReflTransGen (LayeredReachability.Edge edge)
          ((clockNumbering V).symm (clockNumbering V source))
          ((clockNumbering V).symm (clockNumbering V target)) :=
      h.lift (clockNumbering V).symm (by
      intro old new hstep
      exact hstep)
    simpa using hdecoded
  · intro h
    have hencoded :
        ReflTransGen (numberedClockEdge edge)
          (clockNumbering V source) (clockNumbering V target) :=
      h.lift (clockNumbering V) (by
      intro old new hstep
      change LayeredReachability.Edge edge
        ((clockNumbering V).symm (clockNumbering V old))
        ((clockNumbering V).symm (clockNumbering V new))
      simpa using hstep)
    exact hencoded

/-- Arbitrary finite reachability is exactly reachability between the two designated cores of
the serialized padded clock graph. -/
public theorem reaches_iff_clockSerialized {V : Type*} [Fintype V]
    (edge : V → V → Prop) (source target : V) :
    ReflTransGen edge source target ↔
      ReflTransGen (clockSerializedEdge edge)
        (clockSerializedSource source) (clockSerializedTarget target) := by
  calc
    ReflTransGen edge source target ↔
        ReflTransGen (LayeredReachability.Edge edge)
          (LayeredReachability.bottom source)
          (LayeredReachability.top target) :=
      LayeredReachability.reaches_iff_layered_reaches edge source target
    _ ↔ ReflTransGen (numberedClockEdge edge)
          (clockNumbering V (LayeredReachability.bottom source))
          (clockNumbering V (LayeredReachability.top target)) :=
      (numberedClock_reaches_iff edge _ _).symm
    _ ↔ ReflTransGen (clockSerializedEdge edge)
          (clockSerializedSource source) (clockSerializedTarget target) := by
      simpa only [clockSerializedEdge, clockSerializedSource,
        clockSerializedTarget] using
        reaches_iff (numberedClockEdge edge)
          (clockNumbering V (LayeredReachability.bottom source))
          (clockNumbering V (LayeredReachability.top target))

/-- The serialized padded clock graph is acyclic for every original relation. -/
public theorem clockSerialized_acyclic {V : Type*} [Fintype V]
    (edge : V → V → Prop) (vertex : ClockSerializedVertex V) :
    ¬ TransGen (clockSerializedEdge edge) vertex vertex := by
  apply acyclic_of_rank
    (fun index => ((clockNumbering V).symm index).2.val)
  intro old new hstep
  exact LayeredReachability.edge_layer_lt hstep

/-- Both directed degrees of the serialized padded clock graph are at most two. -/
public theorem clockSerialized_directedDegreeAtMostTwo
    {V : Type*} [Fintype V] (edge : V → V → Prop) :
    LayeredReachability.DirectedDegreeAtMost 2 (clockSerializedEdge edge) :=
  directedDegreeAtMostTwo (numberedClockEdge edge)

/-- Every serialized padded-clock edge has exactly one syntactic layer color. -/
public theorem clockSerialized_edge_iff_existsUnique_layer
    {V : Type*} [Fintype V] (edge : V → V → Prop)
    (old new : ClockSerializedVertex V) :
    clockSerializedEdge edge old new ↔
      ∃! color, clockSerializedLayer edge color old new :=
  edge_iff_existsUnique_layer (numberedClockEdge edge) old new

/-- Padded-clock layers contain only genuine serialized edges. -/
public theorem clockSerialized_layer_sub_edge
    {V : Type*} [Fintype V] (edge : V → V → Prop)
    (color : Fin 2) (old new : ClockSerializedVertex V)
    (hlayer : clockSerializedLayer edge color old new) :
    clockSerializedEdge edge old new :=
  layer_sub_edge (numberedClockEdge edge) color old new hlayer

/-- Each syntactic padded-clock layer is a partial bijection. -/
public theorem clockSerialized_layer_biUnique
    {V : Type*} [Fintype V] (edge : V → V → Prop) (color : Fin 2) :
    Relator.BiUnique (clockSerializedLayer edge color) :=
  layer_biUnique (numberedClockEdge edge) color

/-- Complete single-designated-target normal form for arbitrary finite directed reachability.

The result is an acyclic relation of directed degree at most two with an exact supplied
two-partial-bijection partition.  `clockSerializedTarget target` is one distinguished target
vertex; the theorem does not claim that it is the graph's unique sink.  The finite numbering is
chosen noncomputably, so no complexity bound for constructing the graph is asserted. -/
public theorem finiteReachability_singleTarget_twoBiUnique
    {V : Type*} [Fintype V]
    (edge : V → V → Prop) (source target : V) :
    (ReflTransGen edge source target ↔
      ReflTransGen (clockSerializedEdge edge)
        (clockSerializedSource source) (clockSerializedTarget target)) ∧
      (∀ vertex, ¬ TransGen (clockSerializedEdge edge) vertex vertex) ∧
      LayeredReachability.DirectedDegreeAtMost 2 (clockSerializedEdge edge) ∧
      (∀ old new, clockSerializedEdge edge old new ↔
        ∃! color, clockSerializedLayer edge color old new) ∧
      (∀ color old new, clockSerializedLayer edge color old new →
        clockSerializedEdge edge old new) ∧
      ∀ color, Relator.BiUnique (clockSerializedLayer edge color) :=
  ⟨reaches_iff_clockSerialized edge source target,
    clockSerialized_acyclic edge,
    clockSerialized_directedDegreeAtMostTwo edge,
    clockSerialized_edge_iff_existsUnique_layer edge,
    clockSerialized_layer_sub_edge edge,
    clockSerialized_layer_biUnique edge⟩

end ExplicitDegreeTwoReachability

end
