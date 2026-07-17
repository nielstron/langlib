module

public import Langlib.Automata.LinearBounded.BoundedDegree
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relator

@[expose]
public section

/-!
# Decomposing degree-two relations into partial bijections

Every relation with at most two successors and at most two predecessors is the union of four
relations that are both functional and cofunctional.  No finiteness assumption is made on the
ambient vertex type: only the individual predecessor and successor fibers are bounded.

The construction independently assigns a two-valued port to every outgoing and incoming fiber,
then colors an edge by its pair of ports.  The result is structural rather than algorithmic: the
ports are chosen classically.
-/

open Set

namespace PartialBijectionDecomposition

variable {V : Type*}

/-- A set of cardinality at most two admits a two-valued coloring that is injective on the set.
The ambient type itself need not be finite. -/
private theorem exists_finTwo_injOn (s : Set V) (hcard : s.encard ≤ 2) :
    ∃ color : V → Fin 2, Set.InjOn color s := by
  have hs : s.Finite := Set.finite_of_encard_le_coe hcard
  have hle : s.encard ≤ (Set.univ : Set (Fin 2)).encard := by
    simpa using hcard
  obtain ⟨color, _, hinjective⟩ := hs.exists_injOn_of_encard_le hle
  exact ⟨color, hinjective⟩

/-- Any directed relation with predecessor and successor fibers of extended cardinality at most
two is partitioned into four bi-unique relations.

The unique-existence clause says that every edge receives exactly one color.  Thus this is
strictly stronger than merely expressing the original relation as a union of four layers. -/
public theorem exists_four_biUnique_partition
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2) :
    ∃ layer : Fin 2 × Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target, layer color source target → edge source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  classical
  choose outPort houtPort using fun source =>
    exists_finTwo_injOn {target | edge source target} (hout source)
  choose inPort hinPort using fun target =>
    exists_finTwo_injOn {source | edge source target} (hin target)
  let layer : Fin 2 × Fin 2 → V → V → Prop :=
    fun color source target =>
      edge source target ∧
        outPort source target = color.1 ∧
        inPort target source = color.2
  refine ⟨layer, ?_, ?_, ?_⟩
  · intro source target
    constructor
    · intro hedge
      refine ⟨(outPort source target, inPort target source),
        ⟨hedge, rfl, rfl⟩, ?_⟩
      intro color hcolor
      apply Prod.ext
      · exact hcolor.2.1.symm
      · exact hcolor.2.2.symm
    · rintro ⟨color, hcolor, _⟩
      exact hcolor.1
  · intro color source target hcolor
    exact hcolor.1
  · intro color
    constructor
    · intro left right target hleft hright
      apply hinPort target hleft.1 hright.1
      exact hleft.2.2.trans hright.2.2.symm
    · intro source left right hleft hright
      apply houtPort source hleft.1 hright.1
      exact hleft.2.1.trans hright.2.1.symm

/-- Any directed relation with predecessor and successor fibers of extended cardinality at most
two is exactly the union of four bi-unique relations.

`layer (outPort, inPort)` contains the edges carrying that outgoing port at their source and that
incoming port at their target.  `Relator.BiUnique` says simultaneously that a layer has at most
one outgoing edge at every source and at most one incoming edge at every target. -/
public theorem exists_four_biUnique_decomposition
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2) :
    ∃ layer : Fin 2 × Fin 2 → V → V → Prop,
      (∀ source target, edge source target ↔ ∃ color, layer color source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  obtain ⟨layer, hpartition, hsub, hbiUnique⟩ :=
    exists_four_biUnique_partition edge hout hin
  refine ⟨layer, ?_, hbiUnique⟩
  · intro source target
    constructor
    · intro hedge
      exact ((hpartition source target).mp hedge).exists
    · rintro ⟨color, hcolor⟩
      exact hsub color source target hcolor

/-- Function equality form of `exists_four_biUnique_decomposition`. -/
public theorem exists_four_biUnique_decomposition_eq
    (edge : V → V → Prop)
    (hout : ∀ source, {target | edge source target}.encard ≤ 2)
    (hin : ∀ target, {source | edge source target}.encard ≤ 2) :
    ∃ layer : Fin 2 × Fin 2 → V → V → Prop,
      edge = (fun source target => ∃ color, layer color source target) ∧
        ∀ color, Relator.BiUnique (layer color) := by
  obtain ⟨layer, hcover, hunique⟩ :=
    exists_four_biUnique_decomposition edge hout hin
  exact ⟨layer, funext fun source => funext fun target => propext (hcover source target), hunique⟩

end PartialBijectionDecomposition

namespace LBA

variable {Γ Λ : Type*}

/-- At every fixed tape width, a degree-two LBA configuration relation is exactly the union of
four partial bijections.  The four layers may depend on the width; the number of layers does not.
-/
public theorem Machine.exists_four_biUnique_step_decomposition
    (M : Machine Γ Λ) (hdegree : M.ConfigurationDegreeAtMostTwo) (n : ℕ) :
    ∃ layer : Fin 2 × Fin 2 →
        DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop,
      (∀ source target,
        Step M source target ↔ ∃ color, layer color source target) ∧
        ∀ color, Relator.BiUnique (layer color) :=
  PartialBijectionDecomposition.exists_four_biUnique_decomposition
    (Step M) (hdegree.1 n) (hdegree.2 n)

/-- At every fixed tape width, the four partial-bijection layers can be chosen so that every
machine edge belongs to exactly one of them. -/
public theorem Machine.exists_four_biUnique_step_partition
    (M : Machine Γ Λ) (hdegree : M.ConfigurationDegreeAtMostTwo) (n : ℕ) :
    ∃ layer : Fin 2 × Fin 2 →
        DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop,
      (∀ source target,
        Step M source target ↔ ∃! color, layer color source target) ∧
        (∀ color source target,
          layer color source target → Step M source target) ∧
        ∀ color, Relator.BiUnique (layer color) :=
  PartialBijectionDecomposition.exists_four_biUnique_partition
    (Step M) (hdegree.1 n) (hdegree.2 n)

end LBA

end
