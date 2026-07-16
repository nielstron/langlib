module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ExposedSuccessorResult
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PrefixSupportComposition
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.MultipleArgumentReplacement

@[expose]
public section

/-!
# All exposed successors of one balancing segment

Normal form supplies one fixed shorter exposing row for every immediate
successor of the active root.  This file selects those rows as a dependent
finite family and records the structural prefix witnesses of their pivot
residuals.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One exposed-successor result for every concrete immediate child of the
active root, in the same order as the root's child list. -/
public structure BalancingSegment.ExposedSuccessorFamily
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {initialLeft initialRight : RegularTerm}
    (stem : List (Label Action)) (filler : RegularTerm)
    (children : List ℕ) where
  row : ∀ i : Fin children.length,
    BalancingSegment.ExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      segment stem filler children[i.val]

/-- Normal form selects the complete ordered family of shorter successor
rows. -/
public theorem BalancingSegment.exists_exposedSuccessorFamily
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hexposureBound : g.exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    {filler : RegularTerm} (hfiller : filler.Ground g.ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    {X : ℕ} {children : List ℕ}
    (hroot : active.rootApplication? = some (X, children)) :
    Nonempty (BalancingSegment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      segment stem filler children) := by
  classical
  have hrank : g.ranks[X]? = some children.length :=
    hactive.root_rank_arity hroot
  have hX : X < g.ranks.length :=
    (List.getElem?_eq_some_iff.mp hrank).1
  let symbol : Fin g.ranks.length := ⟨X, hX⟩
  have hsymbolRank : g.ranks.get symbol = children.length := by
    apply Option.some.inj
    exact (List.getElem?_eq_getElem hX).symm.trans hrank
  have hexists : ∀ i : Fin children.length,
      Nonempty (BalancingSegment.ExposedSuccessorResult
        (initialLeft := initialLeft) (initialRight := initialRight)
        segment stem filler children[i.val]) := by
    intro i
    let childPosition : Fin (g.ranks.get symbol) :=
      ⟨i.val, by
        rw [hsymbolRank]
        exact i.isLt⟩
    let position : g.SuccessorPosition := ⟨symbol, childPosition⟩
    apply segment.exists_exposedSuccessorResult hg hnormal
      hexposureBound hactive hpivot hfiller houter hequivalent position
    · simpa [position, symbol] using hroot
    · simpa [position, childPosition] using
        (List.getElem?_eq_getElem i.isLt)
  exact ⟨
    { row := fun i => Classical.choice (hexists i) }⟩

namespace BalancingSegment.ExposedSuccessorFamily

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {initialLeft initialRight : RegularTerm}
  {stem : List (Label Action)} {filler : RegularTerm}
  {children : List ℕ}

/-- Concrete pivot targets, ordered by active-root successor. -/
@[expose] public noncomputable def pivotTargets
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children) : List RegularTerm :=
  List.ofFn fun i => (family.row i).pivotTarget

/-- Symbolic pivot residual contexts, ordered by active-root successor. -/
@[expose] public noncomputable def pivotResiduals
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children) : List RegularTerm :=
  List.ofFn fun i => (family.row i).pivotResidual

@[simp] public theorem pivotTargets_length
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children) :
    family.pivotTargets.length = children.length := by
  simp [pivotTargets]

@[simp] public theorem pivotResiduals_length
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children) :
    family.pivotResiduals.length = children.length := by
  simp [pivotResiduals]

public theorem pivotTargets_getElem
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (i : Fin children.length) :
    family.pivotTargets[i.val] = (family.row i).pivotTarget := by
  simp [pivotTargets]

public theorem pivotResiduals_getElem
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (i : Fin children.length) :
    family.pivotResiduals[i.val] = (family.row i).pivotResidual := by
  simp [pivotResiduals]

/-- Every concrete replacement target is ground. -/
public theorem pivotTargets_ground
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed) (hpivot : pivot.Ground g.ranks) :
    ∀ target ∈ family.pivotTargets, target.Ground g.ranks := by
  intro target htarget
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp htarget
  let index : Fin children.length := ⟨i, by
    simpa [family.pivotTargets_length] using hi⟩
  have htargetEq : target = (family.row index).pivotTarget := by
    have hslot := family.pivotTargets_getElem index
    exact hget.symm.trans hslot
  rw [htargetEq]
  have hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.ground_of_run hpivot
    (by simpa [runActions?] using (family.row index).pivot_run)

/-- Each selected symbolic pivot residual has a reachable witness supported by
the pivot depth-prefix tails. -/
public theorem row_pivotResidual_hasPrefixWitness
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed) (hpivot : pivot.Ground g.ranks)
    (i : Fin children.length) :
    (family.row i).pivotResidual.HasPrefixWitness
      (pivot.depthPrefix bound).tails.length := by
  let decomposition := pivot.depthPrefix bound
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid pivot bound
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hpivot bound
  have hwitness :
      decomposition.head.toRegularTerm.HasPrefixWitness
        decomposition.tails.length :=
    FiniteHead.toRegularTerm_hasPrefixWitness hvalid
  have hwellFormed :
      decomposition.head.toRegularTerm.WellFormed g.ranks
        (decomposition.schemaArity g.ranks) :=
    decomposition.head_wellFormed_schemaArity hvalid hranked
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  exact hwitness.runActions hg hpadding hwellFormed
    (by simpa [decomposition] using (family.row i).pivot_symbolic_run)

/-- Every selected pivot residual is well formed at the common pivot-prefix
arity. -/
public theorem pivotResiduals_wellFormed
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children) :
    ∀ residual ∈ family.pivotResiduals,
      residual.WellFormed g.ranks
        ((pivot.depthPrefix bound).schemaArity g.ranks) := by
  intro residual hresidual
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hresidual
  let index : Fin children.length := ⟨i, by
    simpa [family.pivotResiduals_length] using hi⟩
  have hresidualEq : residual = (family.row index).pivotResidual := by
    exact hget.symm.trans (family.pivotResiduals_getElem index)
  rw [hresidualEq]
  exact (family.row index).pivot_supported.1

end BalancingSegment.ExposedSuccessorFamily

end EncodedFirstOrderGrammar

end DCFEquivalence
