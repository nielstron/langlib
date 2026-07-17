module

public import Langlib.Automata.LinearBounded.AcyclicClock.LanguageEquivalence

@[expose]
public section

/-!
# The first LBA problem on the exact compiler image

The concrete target machine is globally configuration-acyclic on every raw tape and recognizes
exactly the source language.  Consequently the first LBA problem is unchanged even if the target
is restricted to the literal image of this compiler.  The same remains true after applying the
simultaneous indegree/outdegree-two serializer.

These results are stronger restrictions than quantifying over every globally acyclic or
degree-two presentation: they quantify only over machines produced by the two fixed compiler
pipelines.  They are nevertheless reformulations, not determinization theorems.
-/

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- Global acyclicity together with the forward half of exact language preservation. -/
public theorem machine_acyclic_and_source_language_subset
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    (machine M).ConfigurationAcyclic ∧
      ∀ input, LBA.LanguageEnd M input →
        LBA.LanguageEnd (machine M) input :=
  ⟨(machine_acyclic_and_language_eq M).1, by
    intro input hinput
    rw [(machine_acyclic_and_language_eq M).2]
    exact hinput⟩

/-! ## Exact syntactic compiler images -/

/-- Every language produced by the concrete guarded clock compiler has a DLBA presentation.

The quantification is over source machines, but the language supplied to `is_DLBA` is literally
the language of `machine M`, rather than the extensionally equal source language. -/
public def EveryClockCompiledLanguageIsDLBA
    (T : Type) [Fintype T] [DecidableEq T] : Prop :=
  ∀ (Γ Λ : Type)
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine (SourceAlpha T Γ) Λ),
    is_DLBA (LBA.LanguageEnd (machine M))

/-- The full LBA-to-DLBA inclusion is already equivalent to determinizing the literal image of
the guarded globally acyclic clock compiler. -/
public theorem lba_subset_dlba_iff_clockCompiledLanguages
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) ⊆ DLBA) ↔
      EveryClockCompiledLanguageIsDLBA T := by
  constructor
  · intro hsubset Γ Λ hΓ hΛ hdecΓ hdecΛ M
    letI := hΓ
    letI := hΛ
    letI := hdecΓ
    letI := hdecΛ
    rw [languageEnd_machine_eq M]
    exact hsubset ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, rfl⟩
  · intro hcompiled L hL
    rcases hL with ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩
    letI := hΓ
    letI := hΛ
    letI := hdecΓ
    letI := hdecΛ
    have htarget := hcompiled Γ Λ M
    rw [languageEnd_machine_eq M, hM] at htarget
    exact htarget

/-- Equality of LBA and DLBA is equivalent to determinizing the exact guarded-clock compiler
image. -/
public theorem lba_eq_dlba_iff_clockCompiledLanguages
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      EveryClockCompiledLanguageIsDLBA T := by
  rw [Set.Subset.antisymm_iff]
  simp only [DLBA_subset_LBA, and_true]
  exact lba_subset_dlba_iff_clockCompiledLanguages

/-- Every language produced by first clock-compiling and then degree-serializing a source LBA has
a DLBA presentation.  Every target in this syntactic image is globally acyclic and has
configuration indegree and outdegree at most two. -/
public def EveryClockDegreeSerializedLanguageIsDLBA
    (T : Type) [Fintype T] [DecidableEq T] : Prop :=
  ∀ (Γ Λ : Type)
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine (SourceAlpha T Γ) Λ),
    is_DLBA (LBA.LanguageEnd (machine M).boundedDegree)

/-- The full inclusion problem is unchanged on the literal output of the guarded-clock compiler
followed by the fixed indegree/outdegree-two serializer. -/
public theorem lba_subset_dlba_iff_clockDegreeSerializedLanguages
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) ⊆ DLBA) ↔
      EveryClockDegreeSerializedLanguageIsDLBA T := by
  constructor
  · intro hsubset Γ Λ hΓ hΛ hdecΓ hdecΛ M
    letI := hΓ
    letI := hΛ
    letI := hdecΓ
    letI := hdecΛ
    rw [(machine M).languageEnd_boundedDegree_eq, languageEnd_machine_eq M]
    exact hsubset ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, rfl⟩
  · intro hcompiled L hL
    rcases hL with ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩
    letI := hΓ
    letI := hΛ
    letI := hdecΓ
    letI := hdecΛ
    have htarget := hcompiled Γ Λ M
    rw [(machine M).languageEnd_boundedDegree_eq,
      languageEnd_machine_eq M, hM] at htarget
    exact htarget

/-- Equality of LBA and DLBA is already equivalent to determinizing only the explicit globally
acyclic, degree-two compiler image. -/
public theorem lba_eq_dlba_iff_clockDegreeSerializedLanguages
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      EveryClockDegreeSerializedLanguageIsDLBA T := by
  rw [Set.Subset.antisymm_iff]
  simp only [DLBA_subset_LBA, and_true]
  exact lba_subset_dlba_iff_clockDegreeSerializedLanguages

end LBA.AcyclicClock

end
