module

public import Langlib.Automata.LinearBounded.AlphabetTransport
public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedTwoMatching
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Endmarker-alphabet transport for the combined boundary shuttle

The combined shuttle initially has tape alphabet
`CombinedShuttleAlphabet (EndAlpha T Γ) Λ`, which is finite but is not syntactically an
`EndAlpha`.  This module gives an explicit equivalence with a canonical endmarker alphabet.

Plain endmarkers, blanks, input symbols, and old work symbols retain their canonical roles.
Every non-plain shuttle tag is instead represented by a disjoint constructor of a new work
alphabet.  Transport along the equivalence is exact on the complete raw configuration graph.
Run reflection and guarded source-language equivalence are proved separately in
`CombinedReflection` and `CombinedEndmarkerLanguage`.
-/

namespace LBA

variable {T Γ Λ : Type*}

/-- Work symbols needed to present the combined shuttle as a canonical endmarker LBA.

`sourceWork` embeds the old source work alphabet.  The remaining constructors are disjoint
encodings of the three protocol-tag families. -/
public inductive CombinedShuttleWorkAlphabet (T Γ Λ : Type*) where
  | sourceWork (symbol : Γ)
  | directionalDeparture (move : ShuttleMove (EndAlpha T Γ) Λ)
  | directionalNeighbour (move : ShuttleMove (EndAlpha T Γ) Λ)
      (symbol : EndAlpha T Γ)
  | stationarySaved (move : ShuttleMove (EndAlpha T Γ) Λ)
  deriving DecidableEq, Fintype

/-- Explicit bijection from the combined tape alphabet to a canonical endmarker alphabet.

The only symbols sent to the target endmarkers/input/blank constructors are their corresponding
plain source symbols.  In particular, no protocol tag can masquerade as canonical input. -/
@[expose]
public def combinedShuttleEndEquiv :
    CombinedShuttleAlphabet (EndAlpha T Γ) Λ ≃
      EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ) where
  toFun
    | .plain (Sum.inl none) => Sum.inl none
    | .plain (Sum.inl (some (Sum.inl terminal))) =>
        Sum.inl (some (Sum.inl terminal))
    | .plain (Sum.inl (some (Sum.inr work))) =>
        Sum.inl (some (Sum.inr (.sourceWork work)))
    | .plain (Sum.inr marker) => Sum.inr marker
    | .directionalDeparture move =>
        Sum.inl (some (Sum.inr (.directionalDeparture move)))
    | .directionalNeighbour move symbol =>
        Sum.inl (some (Sum.inr (.directionalNeighbour move symbol)))
    | .stationarySaved move =>
        Sum.inl (some (Sum.inr (.stationarySaved move)))
  invFun
    | Sum.inl none => .plain (Sum.inl none)
    | Sum.inl (some (Sum.inl terminal)) =>
        .plain (Sum.inl (some (Sum.inl terminal)))
    | Sum.inl (some (Sum.inr (.sourceWork work))) =>
        .plain (Sum.inl (some (Sum.inr work)))
    | Sum.inl (some (Sum.inr (.directionalDeparture move))) =>
        .directionalDeparture move
    | Sum.inl (some (Sum.inr (.directionalNeighbour move symbol))) =>
        .directionalNeighbour move symbol
    | Sum.inl (some (Sum.inr (.stationarySaved move))) =>
        .stationarySaved move
    | Sum.inr marker => .plain (Sum.inr marker)
  left_inv symbol := by
    cases symbol with
    | plain symbol =>
      rcases symbol with (symbol | marker)
      · rcases symbol with (_ | symbol)
        · rfl
        · rcases symbol with (terminal | work) <;> rfl
      · rfl
    | directionalDeparture move => rfl
    | directionalNeighbour move symbol => rfl
    | stationarySaved move => rfl
  right_inv symbol := by
    rcases symbol with (symbol | marker)
    · rcases symbol with (_ | symbol)
      · rfl
      · rcases symbol with (terminal | work)
        · rfl
        · cases work <;> rfl
    · rfl

@[simp]
public theorem combinedShuttleEndEquiv_plain_blank :
    combinedShuttleEndEquiv
        (.plain (Sum.inl none : EndAlpha T Γ)) =
      (Sum.inl none : EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ)) := rfl

@[simp]
public theorem combinedShuttleEndEquiv_plain_input (terminal : T) :
    combinedShuttleEndEquiv
        (.plain (Sum.inl (some (Sum.inl terminal)) : EndAlpha T Γ)) =
      (Sum.inl (some (Sum.inl terminal)) :
        EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ)) := rfl

@[simp]
public theorem combinedShuttleEndEquiv_plain_work (work : Γ) :
    combinedShuttleEndEquiv
        (.plain (Sum.inl (some (Sum.inr work)) : EndAlpha T Γ)) =
      (Sum.inl (some (Sum.inr (.sourceWork work))) :
        EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ)) := rfl

@[simp]
public theorem combinedShuttleEndEquiv_plain_marker (marker : Bool) :
    combinedShuttleEndEquiv
        (.plain (Sum.inr marker : EndAlpha T Γ)) =
      (Sum.inr marker : EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ)) := rfl

@[simp]
public theorem combinedShuttleEndEquiv_directionalDeparture
    (move : ShuttleMove (EndAlpha T Γ) Λ) :
    combinedShuttleEndEquiv (.directionalDeparture move) =
      (Sum.inl (some (Sum.inr (.directionalDeparture move))) :
        EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ)) := rfl

@[simp]
public theorem combinedShuttleEndEquiv_directionalNeighbour
    (move : ShuttleMove (EndAlpha T Γ) Λ) (symbol : EndAlpha T Γ) :
    combinedShuttleEndEquiv (.directionalNeighbour move symbol) =
      (Sum.inl (some (Sum.inr (.directionalNeighbour move symbol))) :
        EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ)) := rfl

@[simp]
public theorem combinedShuttleEndEquiv_stationarySaved
    (move : ShuttleMove (EndAlpha T Γ) Λ) :
    combinedShuttleEndEquiv (.stationarySaved move) =
      (Sum.inl (some (Sum.inr (.stationarySaved move))) :
        EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ)) := rfl

/-- The transported combined shuttle, now syntactically a canonical endmarker LBA. -/
@[expose]
public def Machine.combinedBoundaryShuttleEndmarker
    (M : Machine (EndAlpha T Γ) Λ) :
    Machine (EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ))
      (CombinedShuttleState (EndAlpha T Γ) Λ) :=
  M.combinedBoundaryShuttle.alphabetTransport combinedShuttleEndEquiv

/-- Renaming the plain combined image of a canonical input tape produces exactly the canonical
input tape for the new work alphabet. -/
public theorem alphabetEquivTape_combinedShuttleTape_loadEnd
    (input : List T) :
    alphabetEquivTape (combinedShuttleEndEquiv (T := T) (Γ := Γ) (Λ := Λ))
        (combinedShuttleTape (Λ := Λ) (loadEnd (Γ := Γ) input)) =
      loadEnd (Γ := CombinedShuttleWorkAlphabet T Γ Λ) input := by
  apply congrArg (fun contents =>
    (⟨contents, ⟨0, Nat.succ_pos _⟩⟩ :
      DLBA.BoundedTape (EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ))
        (input.length + 1)))
  funext index
  change combinedShuttleEndEquiv
      (.plain
        (if index.val = 0 then (leftMark : EndAlpha T Γ)
        else if h : index.val - 1 < input.length then
          Sum.inl (some (Sum.inl (input.get ⟨index.val - 1, h⟩)))
        else rightMark)) =
    (if index.val = 0 then
      (leftMark : EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ))
    else if h : index.val - 1 < input.length then
      Sum.inl (some (Sum.inl (input.get ⟨index.val - 1, h⟩)))
    else rightMark)
  split
  · simp_all
  · split
    · simp_all
    · simp_all

/-- The canonical initial configuration is exactly the rename of the natural plain/normal
combined-shuttle initial configuration. -/
public theorem alphabetEquivCfg_combinedShuttleCfg_initCfgEnd
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    alphabetEquivCfg (combinedShuttleEndEquiv (T := T) (Γ := Γ) (Λ := Λ))
        (combinedShuttleCfg (initCfgEnd M input)) =
      initCfgEnd M.combinedBoundaryShuttleEndmarker input := by
  change (⟨.normal M.initial,
    alphabetEquivTape combinedShuttleEndEquiv
      (combinedShuttleTape (loadEnd input))⟩ :
      DLBA.Cfg (EndAlpha T (CombinedShuttleWorkAlphabet T Γ Λ))
        (CombinedShuttleState (EndAlpha T Γ) Λ) (input.length + 1)) =
    ⟨.normal M.initial,
      loadEnd (Γ := CombinedShuttleWorkAlphabet T Γ Λ) input⟩
  rw [alphabetEquivTape_combinedShuttleTape_loadEnd]

/-- The language of the combined compiler from its natural plain/normal input presentation.
This is named separately because the untransported combined alphabet is not syntactically an
`EndAlpha`. -/
@[expose]
public noncomputable def Machine.combinedBoundaryShuttleLanguageEnd
    (M : Machine (EndAlpha T Γ) Λ) : Language T :=
  fun input => Accepts M.combinedBoundaryShuttle
    (combinedShuttleCfg (initCfgEnd M input))

/-- Alphabet transport preserves exactly the natural combined-shuttle input language. -/
public theorem Machine.languageEnd_combinedBoundaryShuttleEndmarker_eq
    (M : Machine (EndAlpha T Γ) Λ) :
    LanguageEnd M.combinedBoundaryShuttleEndmarker =
      M.combinedBoundaryShuttleLanguageEnd := by
  funext input
  change Accepts M.combinedBoundaryShuttleEndmarker
      (initCfgEnd M.combinedBoundaryShuttleEndmarker input) =
    Accepts M.combinedBoundaryShuttle
      (combinedShuttleCfg (initCfgEnd M input))
  rw [← alphabetEquivCfg_combinedShuttleCfg_initCfgEnd]
  exact propext (M.combinedBoundaryShuttle.accepts_alphabetTransport_iff
    combinedShuttleEndEquiv (combinedShuttleCfg (initCfgEnd M input)))

/-- The complete raw two-matching property is unchanged by the endmarker presentation. -/
public theorem Machine.combinedBoundaryShuttleEndmarker_hasTwoMatchingStepPartition_iff
    (M : Machine (EndAlpha T Γ) Λ) :
    M.combinedBoundaryShuttleEndmarker.HasTwoMatchingStepPartition ↔
      M.combinedBoundaryShuttle.HasTwoMatchingStepPartition :=
  M.combinedBoundaryShuttle.hasTwoMatchingStepPartition_alphabetTransport_iff
    combinedShuttleEndEquiv

/-- Consequently the combined shuttle's local hypotheses yield an exact two-matching machine
whose alphabet has the canonical endmarker shape required by `is_LBA`. -/
public theorem Machine.combinedBoundaryShuttleEndmarker_hasTwoMatchingStepPartition
    [Fintype T] [Fintype Γ] [Fintype Λ]
    [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine (EndAlpha T Γ) Λ)
    (hfunctional : M.Functional)
    (hdirectional : M.DirectionalTargetInjective)
    (hstationary : M.StationaryTargetWrittenInjective)
    (hkind : M.ShuttleTargetKindDisjoint) :
    M.combinedBoundaryShuttleEndmarker.HasTwoMatchingStepPartition :=
  (M.combinedBoundaryShuttleEndmarker_hasTwoMatchingStepPartition_iff).2
    (M.combinedBoundaryShuttle_hasTwoMatchingStepPartition
      hfunctional hdirectional hstationary hkind)

/-- Class-shaped conclusion of the transport: under the local shuttle hypotheses, the natural
combined-shuttle input language has a genuine canonical-endmarker exact-two-matching
presentation.  The separate guarded-language theorem in `CombinedEndmarkerLanguage` identifies
this language with the source language when its endmarker premise holds. -/
public theorem Machine.is_TwoMatchingLBA_combinedBoundaryShuttleLanguageEnd
    {T₀ Γ₀ Λ₀ : Type}
    [Fintype T₀] [Fintype Γ₀] [Fintype Λ₀]
    [DecidableEq T₀] [DecidableEq Γ₀] [DecidableEq Λ₀]
    (M : Machine (EndAlpha T₀ Γ₀) Λ₀)
    (hfunctional : M.Functional)
    (hdirectional : M.DirectionalTargetInjective)
    (hstationary : M.StationaryTargetWrittenInjective)
    (hkind : M.ShuttleTargetKindDisjoint) :
    is_TwoMatchingLBA M.combinedBoundaryShuttleLanguageEnd := by
  exact ⟨CombinedShuttleWorkAlphabet T₀ Γ₀ Λ₀,
    CombinedShuttleState (EndAlpha T₀ Γ₀) Λ₀,
    inferInstance, inferInstance, inferInstance, inferInstance,
    M.combinedBoundaryShuttleEndmarker,
    M.combinedBoundaryShuttleEndmarker_hasTwoMatchingStepPartition
      hfunctional hdirectional hstationary hkind,
    M.languageEnd_combinedBoundaryShuttleEndmarker_eq⟩

end LBA

end
