module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedCoveragePairs
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedRepeatPigeonhole
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedBasis

@[expose]
public section

/-!
# Derived repetition from uniformly bounded fixed-argument coverages

With one fixed ground argument tuple, a uniform presentation bound leaves only
finitely many possible schema pairs.  Concrete pairs covered by those schemas
therefore lie in two fixed finite semantic covers, so an infinite increasing
sequence of such coverages yields a derived repeat.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Uniformly bounded witnessed coverages over one fixed argument tuple force
a certificate-derived repeat. -/
public theorem TracePath.hasDerivedRepeat_of_uniformBoundedWitnessedCoverages
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (bound width : ℕ) (arguments : List RegularTerm)
    (hcovered : ∀ n, Nonempty
      (BoundedWitnessedActiveSchemaCoverage g
        initialLeft initialRight bound width arguments
        (path.word (levels n)))) :
    path.HasDerivedRepeat := by
  classical
  let coverage : ∀ n, BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight bound width arguments
      (path.word (levels n)) :=
    fun n => Classical.choice (hcovered n)
  let pairs : ∀ n, path.DerivedPairAt (levels n) :=
    fun n => (coverage n).toDerivedPairAt rfl
  let leftCover : List RegularTerm :=
    (g.basisPairsUpTo bound).map fun schema =>
      schema.left.instantiate arguments
  let rightCover : List RegularTerm :=
    (g.basisPairsUpTo bound).map fun schema =>
      schema.right.instantiate arguments
  apply path.hasDerivedRepeat_of_finite_semantic_cover
    levels hlevels pairs leftCover rightCover
  · intro n
    let bounded := coverage n
    let active := bounded.witnessed.coverage
    have hschemaMem : active.schema ∈ g.basisPairsUpTo bound := by
      apply (g.mem_basisPairsUpTo_iff bound active.schema).mpr
      exact ⟨bounded.arity_le, bounded.left_size_le,
        bounded.right_size_le, active.schema_wellFormed⟩
    have hmatch :
        active.left.UnfoldingEquivalent
          (active.schema.left.instantiate active.arguments) :=
      (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
        active.left_matches
    have harguments : active.arguments = arguments :=
      bounded.arguments_eq
    rw [harguments] at hmatch
    refine ⟨active.schema.left.instantiate arguments, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨active.schema, hschemaMem, rfl⟩
    · exact hmatch
  · intro n
    let bounded := coverage n
    let active := bounded.witnessed.coverage
    have hschemaMem : active.schema ∈ g.basisPairsUpTo bound := by
      apply (g.mem_basisPairsUpTo_iff bound active.schema).mpr
      exact ⟨bounded.arity_le, bounded.left_size_le,
        bounded.right_size_le, active.schema_wellFormed⟩
    have hmatch :
        active.right.UnfoldingEquivalent
          (active.schema.right.instantiate active.arguments) :=
      (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
        active.right_matches
    have harguments : active.arguments = arguments :=
      bounded.arguments_eq
    rw [harguments] at hmatch
    refine ⟨active.schema.right.instantiate arguments, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨active.schema, hschemaMem, rfl⟩
    · exact hmatch

/-- A finite family of admissible argument tuples is enough: combining it
with the finite bounded schema enumeration still gives finite concrete
semantic covers. -/
public theorem TracePath.hasDerivedRepeat_of_uniformBoundedWitnessedCoverages_finiteArguments
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (bound width : ℕ)
    (arguments : ℕ → List RegularTerm)
    (argumentTuples : List (List RegularTerm))
    (harguments : ∀ n, arguments n ∈ argumentTuples)
    (hcovered : ∀ n, Nonempty
      (BoundedWitnessedActiveSchemaCoverage g
        initialLeft initialRight bound width (arguments n)
        (path.word (levels n)))) :
    path.HasDerivedRepeat := by
  classical
  let coverage : ∀ n, BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight bound width (arguments n)
      (path.word (levels n)) :=
    fun n => Classical.choice (hcovered n)
  let pairs : ∀ n, path.DerivedPairAt (levels n) :=
    fun n => (coverage n).toDerivedPairAt rfl
  let leftCover : List RegularTerm :=
    (g.basisPairsUpTo bound).flatMap fun schema =>
      argumentTuples.map fun tuple =>
        schema.left.instantiate tuple
  let rightCover : List RegularTerm :=
    (g.basisPairsUpTo bound).flatMap fun schema =>
      argumentTuples.map fun tuple =>
        schema.right.instantiate tuple
  apply path.hasDerivedRepeat_of_finite_semantic_cover
    levels hlevels pairs leftCover rightCover
  · intro n
    let bounded := coverage n
    let active := bounded.witnessed.coverage
    have hschemaMem : active.schema ∈ g.basisPairsUpTo bound := by
      apply (g.mem_basisPairsUpTo_iff bound active.schema).mpr
      exact ⟨bounded.arity_le, bounded.left_size_le,
        bounded.right_size_le, active.schema_wellFormed⟩
    have hmatch :
        active.left.UnfoldingEquivalent
          (active.schema.left.instantiate active.arguments) :=
      (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
        active.left_matches
    have hargumentEq : active.arguments = arguments n :=
      bounded.arguments_eq
    rw [hargumentEq] at hmatch
    refine ⟨active.schema.left.instantiate (arguments n), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨active.schema, hschemaMem,
        List.mem_map.mpr ⟨arguments n, harguments n, rfl⟩⟩
    · exact hmatch
  · intro n
    let bounded := coverage n
    let active := bounded.witnessed.coverage
    have hschemaMem : active.schema ∈ g.basisPairsUpTo bound := by
      apply (g.mem_basisPairsUpTo_iff bound active.schema).mpr
      exact ⟨bounded.arity_le, bounded.left_size_le,
        bounded.right_size_le, active.schema_wellFormed⟩
    have hmatch :
        active.right.UnfoldingEquivalent
          (active.schema.right.instantiate active.arguments) :=
      (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
        active.right_matches
    have hargumentEq : active.arguments = arguments n :=
      bounded.arguments_eq
    rw [hargumentEq] at hmatch
    refine ⟨active.schema.right.instantiate (arguments n), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨active.schema, hschemaMem,
        List.mem_map.mpr ⟨arguments n, harguments n, rfl⟩⟩
    · exact hmatch

/-- The same uniform fixed-argument coverage criterion directly yields the
bound-one open-sound branch. -/
public theorem TracePath.eventuallyBoundedOpenSound_of_uniformBoundedWitnessedCoverages
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (bound width : ℕ) (arguments : List RegularTerm)
    (hcovered : ∀ n, Nonempty
      (BoundedWitnessedActiveSchemaCoverage g
        initialLeft initialRight bound width arguments
        (path.word (levels n)))) :
    g.EventuallyBoundedOpenSound initialLeft initialRight 1 path := by
  apply path.eventuallyBoundedOpenSound_of_hasDerivedRepeat
  exact path.hasDerivedRepeat_of_uniformBoundedWitnessedCoverages
    levels hlevels bound width arguments hcovered

/-- The finite-argument-family variant also directly yields the bound-one
open-sound branch. -/
public theorem TracePath.eventuallyBoundedOpenSound_of_uniformBoundedWitnessedCoverages_finiteArguments
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (bound width : ℕ)
    (arguments : ℕ → List RegularTerm)
    (argumentTuples : List (List RegularTerm))
    (harguments : ∀ n, arguments n ∈ argumentTuples)
    (hcovered : ∀ n, Nonempty
      (BoundedWitnessedActiveSchemaCoverage g
        initialLeft initialRight bound width (arguments n)
        (path.word (levels n)))) :
    g.EventuallyBoundedOpenSound initialLeft initialRight 1 path := by
  apply path.eventuallyBoundedOpenSound_of_hasDerivedRepeat
  exact path.hasDerivedRepeat_of_uniformBoundedWitnessedCoverages_finiteArguments
    levels hlevels bound width arguments argumentTuples
      harguments hcovered

end EncodedFirstOrderGrammar

end DCFEquivalence
