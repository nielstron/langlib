module

public import Langlib.Automata.LinearBounded.MachineTwoMatchings.SequentialUnionInitialization
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.ClockedBranchUnion
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical language of the sequential pinned-branch scheduler

This file combines the canonical packing sweep with the restored-tape scheduler theorem.  The
main theorem is deliberately parameterized by the semantic finite pin cover; the exact
two-matching argument and the acyclic clock wrapper are separate corollaries.
-/

namespace LBA.MachineTwoMatchings

open Classical Relation

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]

omit [DecidableEq Λ] in
/-- Canonical initialization neither creates nor loses acceptance: because the sequential
machine is functional, every accepting path from the raw input is comparable with the unique
initialization path to the first restored rewind checkpoint. -/
public theorem accepts_sequentialUnion_init_iff_rewind_zero
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    Accepts (sequentialUnion M)
        (LBA.initCfgEnd (sequentialUnion M) input) ↔
      Accepts (sequentialUnion M)
        ⟨.rewind 0,
          packedTape (LBA.loadEnd (T := T) (Γ := Γ) input).contents
            (postInitializationTape (Γ := Γ) input)⟩ := by
  let checkpoint :
      DLBA.Cfg (BackupAlpha T Γ) (SequentialState T Γ Λ) (input.length + 1) :=
    ⟨.rewind 0,
      packedTape (LBA.loadEnd (T := T) (Γ := Γ) input).contents
        (postInitializationTape (Γ := Γ) input)⟩
  have hinit : Reaches (sequentialUnion M)
      (LBA.initCfgEnd (sequentialUnion M) input) checkpoint :=
    reaches_rewind_zero_init M input
  constructor
  · rintro ⟨acceptCfg, hacceptReach, hfinal⟩
    have hrightUnique : Relator.RightUnique
        (@Step _ _ (input.length + 1) (sequentialUnion M)) :=
      step_rightUnique_of_functional (n := input.length + 1)
        (sequentialUnion M) (sequentialUnion_functional M)
    rcases ReflTransGen.total_of_right_unique
        hrightUnique hinit hacceptReach with
      hcheckpointAccept | hacceptCheckpoint
    · exact ⟨acceptCfg, hcheckpointAccept, hfinal⟩
    · have heq : acceptCfg = checkpoint :=
        reaches_eq_of_sink (sequentialUnion M)
          (sequentialUnion_sink_of_accepting M acceptCfg hfinal)
          hacceptCheckpoint
      subst acceptCfg
      exact ⟨checkpoint, .refl, hfinal⟩
  · rintro ⟨acceptCfg, hacceptReach, hfinal⟩
    exact ⟨acceptCfg, hinit.trans hacceptReach, hfinal⟩

omit [DecidableEq Λ] in
/-- On a canonical endmarker input, the sequential scheduler recognizes exactly the finite
union of all pinned-first-move languages. -/
public theorem languageEnd_sequentialUnion_iff_exists_languageEnd_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    (input : List T) :
    LanguageEnd (sequentialUnion M) input ↔
      ∃ first : Move (EndAlpha T Γ) Λ,
        LanguageEnd (M.pinFirst first) input := by
  rw [show LanguageEnd (sequentialUnion M) input =
      Accepts (sequentialUnion M)
        (LBA.initCfgEnd (sequentialUnion M) input) by rfl]
  rw [accepts_sequentialUnion_init_iff_rewind_zero M input]
  have hscheduler :=
    accepts_sequentialUnion_rewind_zero_iff_exists_accepts_pinFirst
      M hacyclic (n := input.length + 1) (by omega)
        (LBA.loadEnd (T := T) (Γ := Γ) input).contents
        (postInitializationTape (Γ := Γ) input)
        (postInitializationTape_contents (Γ := Γ) input)
  simpa [LanguageEnd, LBA.initCfgEnd, Machine.pinFirstBootCfg] using hscheduler

omit [DecidableEq Λ] in
/-- Any globally acyclic endmarker machine whose language is the semantic union of its pinned
branches is recognized by its functional sequential scheduler. -/
public theorem languageEnd_sequentialUnion_eq_of_pinCover
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    (hunion : ∀ input : List T,
      LanguageEnd M input ↔
        ∃ first : Move (EndAlpha T Γ) Λ,
          LanguageEnd (M.pinFirst first) input) :
    LanguageEnd (sequentialUnion M) = LanguageEnd M := by
  funext input
  apply propext
  exact (languageEnd_sequentialUnion_iff_exists_languageEnd_pinFirst
    M hacyclic input).trans (hunion input).symm

omit [DecidableEq Λ] in
/-- Exact two-matching machines satisfy the semantic pin-cover premise directly. -/
public theorem languageEnd_sequentialUnion_eq_of_twoMatching
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    (hlayers : M.HasTwoMatchingStepPartition) :
    LanguageEnd (sequentialUnion M) = LanguageEnd M := by
  exact languageEnd_sequentialUnion_eq_of_pinCover M hacyclic
    (M.languageEnd_pinFirst_iff hlayers)

/-- Applying the sequential scheduler to the clocked branch-union wrapper removes the source
machine's acyclicity assumption.  Exact two-matching languages therefore have one functional
endmarker presentation with exactly the same canonical language. -/
public theorem languageEnd_sequentialUnion_clockedBranchUnion_eq
    (M : Machine (EndAlpha T Γ) Λ) (hlayers : M.HasTwoMatchingStepPartition) :
    LanguageEnd (sequentialUnion (ClockedBranchUnion.machine M)) =
      LanguageEnd M := by
  rw [languageEnd_sequentialUnion_eq_of_pinCover
    (ClockedBranchUnion.machine M)
    (ClockedBranchUnion.machine_configurationAcyclic M)
    (ClockedBranchUnion.languageEnd_machine_iff_exists_languageEnd_outerPinFirst M)]
  exact ClockedBranchUnion.languageEnd_machine_eq M hlayers

/-- The clocked sequential presentation is locally functional. -/
public theorem sequentialUnion_clockedBranchUnion_functional
    (M : Machine (EndAlpha T Γ) Λ) :
    (sequentialUnion (ClockedBranchUnion.machine M)).Functional :=
  sequentialUnion_functional (ClockedBranchUnion.machine M)

end LBA.MachineTwoMatchings

end
