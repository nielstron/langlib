module

public import Langlib.Automata.LinearBounded.AcyclicClock.InitializationSoundness
public import Langlib.Automata.LinearBounded.AcyclicClock.SimulationLift

@[expose]
public section

/-!
# Lifting checkpoint-path reflection to reverse language inclusion

`SimulationLift` isolates the semantic obligation `ReflectsCheckpointPaths`.
`InitializationSoundness` proves that every accepting computation from a raw canonical target
input passes through the exact canonical checkpoint.  Together they give reverse acceptance and
language inclusion.  Supplying both forward macro completeness and checkpoint reflection yields
language equality.
-/

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- Checkpoint-path reflection gives reverse acceptance on canonical target inputs. -/
public theorem accepts_of_accepts_machine_init
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hreflect : ReflectsCheckpointPaths M)
    (input : List T)
    (haccept :
      LBA.Accepts (machine M) (LBA.initCfgEnd (machine M) input)) :
    LBA.Accepts M (LBA.initCfgEnd M input) := by
  obtain ⟨target, hreach, htargetAccept⟩ := haccept
  have hready : target.state.IsReady := by
    obtain ⟨source, hsource, _⟩ :=
      (machine_accept_eq_true_iff M target.state).1 htargetAccept
    rw [hsource]
    trivial
  have hcanonical :
      LBA.Reaches (machine M)
        (canonicalCfg M (LBA.initCfgEnd M input)) target :=
    reaches_from_canonicalCfg_of_reaches_ready_init
      M input hreach hready
  exact accepts_of_accepts_machine_canonical M hreflect
    (LBA.initCfgEnd M input)
    ⟨target, hcanonical, htargetAccept⟩

/-- Checkpoint-path reflection gives reverse language inclusion for the operational compiler. -/
public theorem languageEnd_machine_subset
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hreflect : ReflectsCheckpointPaths M) :
    ∀ input, LBA.LanguageEnd (machine M) input →
      LBA.LanguageEnd M input := by
  intro input hinput
  exact accepts_of_accepts_machine_init M hreflect input hinput

/-- Forward macro completeness plus reverse checkpoint reflection prove exact compiler language
equality. -/
public theorem languageEnd_machine_eq_of_simulation
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    [Nonempty Λ]
    (hforward : SimulatesClockedSteps M)
    (hreverse : ReflectsCheckpointPaths M) :
    LBA.LanguageEnd (machine M) = LBA.LanguageEnd M := by
  apply funext
  intro input
  apply propext
  constructor
  · exact languageEnd_machine_subset M hreverse input
  · exact languageEnd_subset_machine M hforward input

end LBA.AcyclicClock

end
