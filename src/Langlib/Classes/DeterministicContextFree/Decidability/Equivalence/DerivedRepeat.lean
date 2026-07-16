module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveStairExistence

@[expose]
public section

/-!
# Repetition of certificate-derived pairs

Jančar's repeat condition applies to any two pairs derived at distinct prefix
words, not only to the raw residual pair recorded by a `TracePath`.  Balancing
results live in precisely this larger certificate-derived space.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A ground pair derived at one accumulated word of a trace path. -/
public structure TracePath.DerivedPairAt
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (level : ℕ) where
  left : RegularTerm
  right : RegularTerm
  derivation :
    CertificateDerivable g initialLeft initialRight []
      (.pair (path.word level) left right)

/-- Two componentwise equal derived pairs occur at distinct prefix levels. -/
@[expose] public def TracePath.HasDerivedRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) : Prop :=
  ∃ earlierLevel laterLevel,
    ∃ earlier : path.DerivedPairAt earlierLevel,
      ∃ later : path.DerivedPairAt laterLevel,
        earlierLevel < laterLevel ∧
          earlier.left.UnfoldingEquivalent later.left ∧
          earlier.right.UnfoldingEquivalent later.right

/-- A repeated raw residual pair is a special case of a derived repeat. -/
public theorem TracePath.hasDerivedRepeat_of_hasRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hgroundSteps : g.PreservesGroundSteps)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hrepeat : path.HasRepeat) :
    path.HasDerivedRepeat := by
  obtain ⟨i, j, hij, hleft, hright⟩ := hrepeat
  let earlier : path.DerivedPairAt i :=
    { left := path.left i
      right := path.right i
      derivation :=
        path.pair_derivable hgroundSteps hground hinitial i }
  let later : path.DerivedPairAt j :=
    { left := path.left j
      right := path.right j
      derivation :=
        path.pair_derivable hgroundSteps hground hinitial j }
  exact ⟨i, j, earlier, later, hij, hleft, hright⟩

/-- A repeated certificate-derived pair is discharged by the one-variable
open-sound identity schema, uniformly at presentation bound one. -/
public theorem TracePath.eventuallyBoundedOpenSound_of_hasDerivedRepeat
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hrepeat : path.HasDerivedRepeat) :
    g.EventuallyBoundedOpenSound initialLeft initialRight 1 path := by
  obtain ⟨i, j, earlier, later, hij, hleft, hright⟩ := hrepeat
  have hlaterGround :=
    groundPairCode_of_pair_derivable later.derivation
  unfold groundPairCode at hlaterGround
  rw [Bool.and_eq_true] at hlaterGround
  have hleftGround : later.left.Ground g.ranks :=
    (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hlaterGround.1
  have hrightGround : later.right.Ground g.ranks :=
    (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hlaterGround.2
  have hvariableWellFormed :
      (RegularTerm.variableTerm 0).WellFormed g.ranks 1 :=
    RegularTerm.variableTerm_wellFormed (by omega)
  have hleftInstance :
      ((RegularTerm.variableTerm 0).instantiate [later.left])
        |>.UnfoldingEquivalent later.left := by
    exact RegularTerm.instantiate_unfoldingEquivalent_argument
      (by simpa [RegularTerm.rootNode?] using
        RegularTerm.variableTerm_rootNode? 0)
      (by simp)
      (RegularTerm.referenceClosed_of_ground hleftGround)
  have hrightInstance :
      ((RegularTerm.variableTerm 0).instantiate [later.right])
        |>.UnfoldingEquivalent later.right := by
    exact RegularTerm.instantiate_unfoldingEquivalent_argument
      (by simpa [RegularTerm.rootNode?] using
        RegularTerm.variableTerm_rootNode? 0)
      (by simp)
      (RegularTerm.referenceClosed_of_ground hrightGround)
  obtain ⟨result, hresultDerivable, hresultMatch⟩ :=
    later.derivation.subtermReplacement earlier.derivation
      hvariableWellFormed hleftGround hrightGround
      (by simpa [path.word_length] using hij)
      hleftInstance.symm hleft hright
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
      g.groundArgumentsCode [later.right] = true := by
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
      right := later.right
      derivation := hresultDerivable
      schema := schema
      arguments := [later.right]
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
