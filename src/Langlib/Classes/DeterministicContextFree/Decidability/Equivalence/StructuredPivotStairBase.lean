module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotProgressStairBase

@[expose]
public section

/-!
# Structured pivot bounds yield witnessed stair bases

The public compatibility names in this file now use the operational maximal
rebase.  Semantic `ExposesBy` maximality is intentionally absent: cyclic
regular terms can expose arbitrary depths without consuming input.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Compatibility name for the operational uniform structured-pivot bound. -/
public abbrev HasUniformStructuredPivotRebaseBound
    (g : EncodedFirstOrderGrammar Action)
    (bound : ℕ) (actionBound : ℕ → ℕ) : Prop :=
  g.HasUniformStructuredPivotProgressRebaseBound bound actionBound

/-- The structured-pivot endpoint now delegates to the operational maximal
rebase theorem. -/
public theorem hasWitnessedRegularActiveStairBase_of_structuredPivotRebaseBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hbound : 0 < bound)
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (actionBound : ℕ → ℕ)
    (hm2 : g.HasUniformStructuredPivotRebaseBound bound actionBound) :
    g.HasWitnessedRegularActiveStairBase
      (g.fixedTailWidthBound bound) :=
  g.hasWitnessedRegularActiveStairBase_of_structuredPivotProgressRebaseBound
    hg hnormal hbound hexposureBound actionBound hm2

end EncodedFirstOrderGrammar

end DCFEquivalence
