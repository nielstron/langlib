module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedReflection
public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedEndmarkerTransport
public import Langlib.Automata.LinearBounded.GraphWalking.EndmarkerNonclamping
import Mathlib.Tactic

@[expose]
public section

/-!
# Whole-language correctness of the combined shuttle on endmarked runs

The combined shuttle reflects every run from a plain/normal configuration,
without hypotheses.  Its forward simulation needs only that each directional
source step genuinely moves inside the bounded tape.  An endmarker-guarded
machine supplies exactly that fact on every run from `loadEnd`.

Consequently the combined compiler, and its alphabet-transported canonical
endmarker presentation, recognize exactly the source language for every
endmarker-guarded source machine.  No functionality, matching, finiteness, or
injectivity assumption is involved in this semantic theorem.
-/

namespace LBA

open Relation

variable {T Γ Λ : Type*}

/-- One guarded source step can be expanded by the combined shuttle and also
preserves the endpoint-marker invariant. -/
public theorem Machine.reaches_combinedBoundaryShuttle_of_step_of_endmarkersIntact
    (M : Machine (EndAlpha T Γ) Λ) (hguard : M.EndmarkerGuarded)
    {n : ℕ} {source target : DLBA.Cfg (EndAlpha T Γ) Λ n}
    (hintact : EndmarkersIntact source.tape)
    (hstep : Step M source target) :
    Reaches M.combinedBoundaryShuttle
        (combinedShuttleCfg source) (combinedShuttleCfg target) ∧
      EndmarkersIntact target.tape := by
  rcases hstep with
    ⟨targetState, written, direction, htransition, rfl⟩
  let move : ShuttleMove (EndAlpha T Γ) Λ :=
    { source := source.state
      old := source.tape.read
      target := targetState
      written := written
      direction := direction }
  have henabled : M.ShuttleEnabled move := by
    exact htransition
  have hnonclamping :=
    M.transitionNonclamping_of_endmarkersIntact
      hguard source.state source.tape hintact
      targetState written direction htransition
  have hphysical :
      move.direction = .stay ∨ movesInside source.tape move.direction := by
    cases direction with
    | stay => exact Or.inl rfl
    | left => exact Or.inr hnonclamping
    | right => exact Or.inr hnonclamping
  constructor
  · exact M.reaches_combinedBoundaryShuttle_of_move
      move source.tape henabled rfl hphysical
  · exact M.endmarkersIntact_of_step hguard hintact
      ⟨targetState, written, direction, htransition, rfl⟩

/-- Every finite guarded source run from an intact tape has a corresponding
combined-shuttle run between the exact plain/normal embeddings. -/
public theorem Machine.reaches_combinedBoundaryShuttle_of_reaches_of_endmarkersIntact
    (M : Machine (EndAlpha T Γ) Λ) (hguard : M.EndmarkerGuarded)
    {n : ℕ} {source target : DLBA.Cfg (EndAlpha T Γ) Λ n}
    (hintact : EndmarkersIntact source.tape)
    (hreach : Reaches M source target) :
    Reaches M.combinedBoundaryShuttle
        (combinedShuttleCfg source) (combinedShuttleCfg target) ∧
      EndmarkersIntact target.tape := by
  induction hreach with
  | refl => exact ⟨.refl, hintact⟩
  | tail hprefix hstep ih =>
      obtain ⟨hcompiled, hmiddleIntact⟩ := ih
      obtain ⟨hlast, htargetIntact⟩ :=
        M.reaches_combinedBoundaryShuttle_of_step_of_endmarkersIntact
          hguard hmiddleIntact hstep
      exact ⟨hcompiled.trans hlast, htargetIntact⟩

/-- On an intact source tape, guarded source acceptance is equivalent to
acceptance by the combined shuttle.  The backward implication is the
unconditional reflection theorem. -/
public theorem Machine.accepts_combinedBoundaryShuttle_iff_of_endmarkersIntact
    (M : Machine (EndAlpha T Γ) Λ) (hguard : M.EndmarkerGuarded)
    {n : ℕ} (source : DLBA.Cfg (EndAlpha T Γ) Λ n)
    (hintact : EndmarkersIntact source.tape) :
    Accepts M.combinedBoundaryShuttle (combinedShuttleCfg source) ↔
      Accepts M source := by
  constructor
  · exact M.accepts_of_accepts_combinedBoundaryShuttle source
  · rintro ⟨target, hreach, haccept⟩
    have hcompiled :=
      (M.reaches_combinedBoundaryShuttle_of_reaches_of_endmarkersIntact
        hguard hintact hreach).1
    exact ⟨combinedShuttleCfg target, hcompiled, haccept⟩

/-- The natural plain/normal input language of a guarded combined shuttle is
exactly the source endmarker language, including the empty word. -/
public theorem Machine.combinedBoundaryShuttleLanguageEnd_eq_languageEnd
    (M : Machine (EndAlpha T Γ) Λ) (hguard : M.EndmarkerGuarded) :
    M.combinedBoundaryShuttleLanguageEnd = LanguageEnd M := by
  funext input
  exact propext (M.accepts_combinedBoundaryShuttle_iff_of_endmarkersIntact
    hguard (initCfgEnd M input) (endmarkersIntact_loadEnd input))

/-- After the explicit alphabet equivalence, the compiled machine is a
canonical endmarker LBA recognizing exactly the guarded source language. -/
public theorem Machine.languageEnd_combinedBoundaryShuttleEndmarker_eq_source
    (M : Machine (EndAlpha T Γ) Λ) (hguard : M.EndmarkerGuarded) :
    LanguageEnd M.combinedBoundaryShuttleEndmarker = LanguageEnd M := by
  rw [M.languageEnd_combinedBoundaryShuttleEndmarker_eq,
    M.combinedBoundaryShuttleLanguageEnd_eq_languageEnd hguard]

/-- Class-shaped semantic conclusion.  Under the independent local matching
hypotheses, every guarded source language has a canonical exact-two-matching
presentation.  The hypotheses are deliberately stated on the source table;
this theorem does not assert that arbitrary deterministic machines satisfy
them. -/
public theorem Machine.is_TwoMatchingLBA_languageEnd_of_combinedBoundaryShuttle
    {T₀ Γ₀ Λ₀ : Type}
    [Fintype T₀] [Fintype Γ₀] [Fintype Λ₀]
    [DecidableEq T₀] [DecidableEq Γ₀] [DecidableEq Λ₀]
    (M : Machine (EndAlpha T₀ Γ₀) Λ₀)
    (hguard : M.EndmarkerGuarded)
    (hfunctional : M.Functional)
    (hdirectional : M.DirectionalTargetInjective)
    (hstationary : M.StationaryTargetWrittenInjective)
    (hkind : M.ShuttleTargetKindDisjoint) :
    is_TwoMatchingLBA (LanguageEnd M) := by
  rw [← M.combinedBoundaryShuttleLanguageEnd_eq_languageEnd hguard]
  exact M.is_TwoMatchingLBA_combinedBoundaryShuttleLanguageEnd
    hfunctional hdirectional hstationary hkind

end LBA

end
