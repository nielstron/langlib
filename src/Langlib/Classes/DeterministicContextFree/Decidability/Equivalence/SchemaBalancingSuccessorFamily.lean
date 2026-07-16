module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaExposedSuccessorResult

@[expose]
public section

/-!
# Fixed-argument successor families for balancing

For every immediate successor of the active root, normal form selects a
shorter certificate row.  All pivot residual schemas in this family are
expressed over one pre-existing argument tuple, which is the form needed by
the later pivot-path stair construction.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One fixed-argument exposed-successor result for every concrete immediate
child of the active root. -/
public structure BalancingSegment.SchemaExposedSuccessorFamily
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {initialLeft initialRight : RegularTerm}
    (stem : List (Label Action)) (children : List ℕ)
    (pivotSchema : RegularTerm) (arguments : List RegularTerm)
    (arity width : ℕ) where
  row : ∀ i : Fin children.length,
    BalancingSegment.SchemaExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      segment stem children[i.val] pivotSchema arguments arity width

/-- Normal form selects the complete ordered fixed-argument successor family. -/
public theorem BalancingSegment.exists_schemaExposedSuccessorFamily
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hexposureBound : g.exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    {pivotSchema : RegularTerm} {arguments : List RegularTerm}
    {arity width : ℕ}
    (hpivotSupported : RegularTerm.SupportedByPrefix g.ranks
      arity width pivotSchema)
    (hpivotWitness : pivotSchema.HasPrefixWitness width)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hpivotDepth : pivotSchema.ApplicationDepth bound)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hpivotInstance :
      (pivotSchema.instantiate arguments).UnfoldingEquivalent pivot)
    {X : ℕ} {children : List ℕ}
    (hroot : active.rootApplication? = some (X, children)) :
    Nonempty (segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) := by
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
      Nonempty (segment.SchemaExposedSuccessorResult
        (initialLeft := initialLeft) (initialRight := initialRight)
        stem children[i.val] pivotSchema arguments arity width) := by
    intro i
    let childPosition : Fin (g.ranks.get symbol) :=
      ⟨i.val, by rw [hsymbolRank]; exact i.isLt⟩
    let position : g.SuccessorPosition := ⟨symbol, childPosition⟩
    apply segment.exists_schemaExposedSuccessorResult hg hnormal
      hexposureBound hactive hpivot houter hequivalent
      hpivotSupported hpivotWitness hpadding hpivotDepth
      hargumentsLength hargumentsClosed hpivotInstance position
    · simpa [position, symbol] using hroot
    · change children[i.val]? = some children[i.val]
      exact List.getElem?_eq_getElem i.isLt
  exact ⟨
    { row := fun i => Classical.choice (hexists i) }⟩

namespace BalancingSegment.SchemaExposedSuccessorFamily

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {initialLeft initialRight : RegularTerm}
  {stem : List (Label Action)} {children : List ℕ}
  {pivotSchema : RegularTerm} {arguments : List RegularTerm}
  {arity width : ℕ}

/-- Concrete pivot targets ordered by active-root successor. -/
@[expose] public noncomputable def pivotTargets
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) : List RegularTerm :=
  List.ofFn fun i => (family.row i).pivotTarget

/-- Symbolic fixed-argument pivot residuals ordered by active-root successor. -/
@[expose] public noncomputable def pivotResiduals
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) : List RegularTerm :=
  List.ofFn fun i => (family.row i).pivotResidual

@[simp] public theorem pivotTargets_length
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) :
    family.pivotTargets.length = children.length := by
  simp [pivotTargets]

@[simp] public theorem pivotResiduals_length
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) :
    family.pivotResiduals.length = children.length := by
  simp [pivotResiduals]

public theorem pivotTargets_getElem
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (i : Fin children.length) :
    family.pivotTargets[i.val] = (family.row i).pivotTarget := by
  simp [pivotTargets]

public theorem pivotResiduals_getElem
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (i : Fin children.length) :
    family.pivotResiduals[i.val] = (family.row i).pivotResidual := by
  simp [pivotResiduals]

/-- Every concrete replacement target is ground. -/
public theorem pivotTargets_ground
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
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
  exact PreservesGroundSteps.ground_of_run
    (preservesGroundSteps_of_wellFormed hg) hpivot
      (by simpa [runActions?] using (family.row index).pivot_run)

/-- Every symbolic replacement context is well formed at the common arity. -/
public theorem pivotResiduals_wellFormed
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width) :
    ∀ residual ∈ family.pivotResiduals,
      residual.WellFormed g.ranks arity := by
  intro residual hresidual
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hresidual
  let index : Fin children.length := ⟨i, by
    simpa [family.pivotResiduals_length] using hi⟩
  have hresidualEq : residual = (family.row index).pivotResidual := by
    have hslot := family.pivotResiduals_getElem index
    exact hget.symm.trans hslot
  rw [hresidualEq]
  exact (family.row index).pivot_supported.1

/-- Each active successor position receives a pivot residual carrying the
common prefix witness. -/
public theorem pivotResiduals_hasPrefixWitness
    (family : segment.SchemaExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem children pivotSchema arguments arity width)
    (i : Fin children.length) :
    (family.row i).pivotResidual.HasPrefixWitness width :=
  (family.row i).pivot_hasPrefixWitness

end BalancingSegment.SchemaExposedSuccessorFamily

end EncodedFirstOrderGrammar

end DCFEquivalence
