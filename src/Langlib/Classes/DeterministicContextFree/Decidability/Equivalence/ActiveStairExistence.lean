module

public import Mathlib.Data.Fintype.Pigeonhole
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SubtermReplacement
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveStairBases

@[expose]
public section

/-!
# Constructing the initial active stair

This module formalizes the path argument of Jančar's
arXiv:1010.4760v4, Propositions 48--49.  The first local case is a repeated
residual pair: ordinary subterm replacement turns the later occurrence into
an instance of the fixed open-sound row `(x₀,x₀)`.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A common trace path repeats a residual pair at two distinct levels. -/
@[expose] public def TracePath.HasRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) : Prop :=
  ∃ i j, i < j ∧
    (path.left i).UnfoldingEquivalent (path.left j) ∧
    (path.right i).UnfoldingEquivalent (path.right j)

/-- If both residual streams are represented, up to equality of unfoldings,
by fixed finite lists, then the path repeats semantically. -/
public theorem TracePath.hasRepeat_of_finite_semantic_cover
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (leftCover rightCover : List RegularTerm)
    (hleft : ∀ n, ∃ representative ∈ leftCover,
      (path.left n).UnfoldingEquivalent representative)
    (hright : ∀ n, ∃ representative ∈ rightCover,
      (path.right n).UnfoldingEquivalent representative) :
    path.HasRepeat := by
  classical
  have hleftIndex : ∀ n, ∃ i : Fin leftCover.length,
      (path.left n).UnfoldingEquivalent leftCover[i] := by
    intro n
    obtain ⟨representative, hrepresentative, hequivalent⟩ := hleft n
    obtain ⟨i, hi, hget⟩ :=
      List.mem_iff_getElem.mp hrepresentative
    exact ⟨⟨i, hi⟩, by simpa [hget] using hequivalent⟩
  have hrightIndex : ∀ n, ∃ i : Fin rightCover.length,
      (path.right n).UnfoldingEquivalent rightCover[i] := by
    intro n
    obtain ⟨representative, hrepresentative, hequivalent⟩ := hright n
    obtain ⟨i, hi, hget⟩ :=
      List.mem_iff_getElem.mp hrepresentative
    exact ⟨⟨i, hi⟩, by simpa [hget] using hequivalent⟩
  choose leftIndex hleftEquivalent using hleftIndex
  choose rightIndex hrightEquivalent using hrightIndex
  letI : Fintype (Fin leftCover.length × Fin rightCover.length) :=
    Fintype.ofList
      ((List.finRange leftCover.length).flatMap fun i =>
        (List.finRange rightCover.length).map fun j => (i, j))
      (by
        rintro ⟨i, j⟩
        simp)
  letI : Finite (Fin leftCover.length × Fin rightCover.length) :=
    Fintype.finite
      (inferInstance :
        Fintype (Fin leftCover.length × Fin rightCover.length))
  obtain ⟨i, j, hij, hindices⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n => (leftIndex n, rightIndex n))
  have hleftIndexEq : leftIndex i = leftIndex j :=
    congrArg Prod.fst hindices
  have hrightIndexEq : rightIndex i = rightIndex j :=
    congrArg Prod.snd hindices
  have hleftRepeat :
      (path.left i).UnfoldingEquivalent (path.left j) := by
    exact (hleftEquivalent i).trans
      (hleftIndexEq ▸ (hleftEquivalent j).symm)
  have hrightRepeat :
      (path.right i).UnfoldingEquivalent (path.right j) := by
    exact (hrightEquivalent i).trans
      (hrightIndexEq ▸ (hrightEquivalent j).symm)
  by_cases hlt : i < j
  · exact ⟨i, j, hlt, hleftRepeat, hrightRepeat⟩
  · have hji : j < i := by omega
    exact ⟨j, i, hji, hleftRepeat.symm, hrightRepeat.symm⟩

/-- A repeated pair is discharged by the one-variable open-sound identity
schema, uniformly at presentation bound one. -/
public theorem TracePath.eventuallyBoundedOpenSound_of_hasRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hgroundSteps : g.PreservesGroundSteps)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hrepeat : path.HasRepeat) :
    g.EventuallyBoundedOpenSound initialLeft initialRight 1 path := by
  obtain ⟨i, j, hij, hleft, hright⟩ := hrepeat
  have houter := path.pair_derivable
    hgroundSteps hground hinitial j
  have hshorter :=
    path.pair_derivable hgroundSteps hground hinitial i
  have hresidualGround :=
    path.residual_ground hgroundSteps hground j
  unfold groundPairCode at hresidualGround
  rw [Bool.and_eq_true] at hresidualGround
  have hleftGround : (path.left j).Ground g.ranks :=
    (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hresidualGround.1
  have hrightGround : (path.right j).Ground g.ranks :=
    (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hresidualGround.2
  have hvariableWellFormed :
      (RegularTerm.variableTerm 0).WellFormed g.ranks 1 :=
    RegularTerm.variableTerm_wellFormed (by omega)
  have hleftInstance :
      ((RegularTerm.variableTerm 0).instantiate [path.left j])
        |>.UnfoldingEquivalent (path.left j) := by
    exact RegularTerm.instantiate_unfoldingEquivalent_argument
      (by simpa [RegularTerm.rootNode?] using
        RegularTerm.variableTerm_rootNode? 0)
      (by simp)
      (RegularTerm.referenceClosed_of_ground hleftGround)
  have hrightInstance :
      ((RegularTerm.variableTerm 0).instantiate [path.right j])
        |>.UnfoldingEquivalent (path.right j) := by
    exact RegularTerm.instantiate_unfoldingEquivalent_argument
      (by simpa [RegularTerm.rootNode?] using
        RegularTerm.variableTerm_rootNode? 0)
      (by simp)
      (RegularTerm.referenceClosed_of_ground hrightGround)
  obtain ⟨result, hresultDerivable, hresultMatch⟩ :=
    houter.subtermReplacement hshorter
      hvariableWellFormed hleftGround hrightGround
      (by simpa [path.word_length] using hij)
      hleftInstance.symm
      hleft
      hright
  let schema : BasisPair :=
    (1, RegularTerm.variableTerm 0, RegularTerm.variableTerm 0)
  have hschemaWellFormed :
      g.basisPairWellFormedCode schema = true := by
    unfold basisPairWellFormedCode
    rw [Bool.and_eq_true]
    exact ⟨hvariableWellFormed, hvariableWellFormed⟩
  have hopen : g.OpenSoundBasisPair schema := by
    exact ⟨hschemaWellFormed, g.traceEquivalent_refl _⟩
  have hargumentsGround :
      g.groundArgumentsCode [path.right j] = true := by
    unfold groundArgumentsCode
    simp [(RegularTerm.groundCode_eq_true_iff g.ranks _).mpr
      hrightGround]
  have hwordNonempty : path.word j ≠ [] := by
    intro hnil
    have hlength := path.word_length j
    rw [hnil] at hlength
    simp at hlength
    omega
  refine ⟨j, ⟨?_⟩⟩
  exact
    { left := result
      right := path.right j
      derivation := hresultDerivable
      schema := schema
      arguments := [path.right j]
      word_nonempty := hwordNonempty
      arity_le := by simp [schema, BasisPair.arity]
      left_size_le := by
        simp [schema, BasisPair.left, RegularTerm.variableTerm,
          RegularTerm.nodes]
      right_size_le := by
        simp [schema, BasisPair.right, RegularTerm.variableTerm,
          RegularTerm.nodes]
      open_sound := hopen
      argument_count := by simp [schema, BasisPair.arity]
      arguments_ground := hargumentsGround
      left_matches :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by simpa [schema, BasisPair.left] using hresultMatch)
      right_matches :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by
            simpa [schema, BasisPair.right] using
              hrightInstance.symm) }

end EncodedFirstOrderGrammar

end DCFEquivalence
