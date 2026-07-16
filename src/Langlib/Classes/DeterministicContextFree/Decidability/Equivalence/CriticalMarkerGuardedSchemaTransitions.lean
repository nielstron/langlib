module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedFixedTailPresentation

@[expose]
public section

/-!
# Successive transitions of guarded critical-prefix schemas

Every residual in a guarded critical fixed-tail presentation is reflected
from the same marker-aware source schema.  Factoring two accumulated action
words therefore gives both the exact symbolic suffix run and the proper-prefix
no-variable invariant required by the one-step Proposition-49 recurrence.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace CriticalGuardedFixedTailPivotPresentation

/-- If the later accumulated action word extends the earlier one, the suffix
executes exactly between their guarded residual schemas. -/
public theorem symbolic_run_suffix
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ} {base filler : RegularTerm}
    {labels : ℕ → List (Label (Action ⊕ ℕ))}
    {pivots : ℕ → RegularTerm}
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    {first second : ℕ} {suffix : List (Action ⊕ ℕ)}
    (hactions :
      presentation.actions second =
        presentation.actions first ++ suffix) :
    (g.withCriticalMarkers count).runActions? suffix
        (presentation.schema first) =
      some (presentation.schema second) := by
  let extended := g.withCriticalMarkers count
  let source :=
    (g.criticalDepthPrefix presentation.depth base)
      |>.head.toRegularTerm
  have hfirst :
      extended.runActions? (presentation.actions first) source =
        some (presentation.schema first) :=
    (presentation.residual first).symbolic_run
  have hsecond :
      extended.runActions? (presentation.actions second) source =
        some (presentation.schema second) :=
    (presentation.residual second).symbolic_run
  rw [hactions] at hsecond
  unfold runActions? at hfirst hsecond ⊢
  rw [List.map_append, extended.run?_append, hfirst] at hsecond
  exact hsecond

/-- The same factorization transports the source critical-prefix
no-variable proof to every proper prefix of the suffix. -/
public theorem noVariableBefore_suffix
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ} {base filler : RegularTerm}
    {labels : ℕ → List (Label (Action ⊕ ℕ))}
    {pivots : ℕ → RegularTerm}
    (presentation : CriticalGuardedFixedTailPivotPresentation
      g count base filler labels pivots)
    {first second : ℕ} {suffix : List (Action ⊕ ℕ)}
    (hactions :
      presentation.actions second =
        presentation.actions first ++ suffix) :
    (g.withCriticalMarkers count).NoVariableBefore
      (presentation.schema first) suffix := by
  let extended := g.withCriticalMarkers count
  intro stem remainder hsuffix hremaining residual x
    hstemRun hvariable
  have hfirst :
      extended.runActions? (presentation.actions first)
          ((g.criticalDepthPrefix presentation.depth base)
            |>.head.toRegularTerm) =
        some (presentation.schema first) := by
    simpa [extended] using
      (presentation.residual first).symbolic_run
  have hcombinedRun :
      extended.runActions?
          (presentation.actions first ++ stem)
          ((g.criticalDepthPrefix presentation.depth base)
            |>.head.toRegularTerm) =
        some residual := by
    rw [runActions?, List.map_append, extended.run?_append]
    rw [← runActions?, hfirst]
    simpa [runActions?, extended] using hstemRun
  apply (presentation.residual second).noVariableBefore
    (presentation.actions first ++ stem) remainder
  · calc
      presentation.actions second =
          presentation.actions first ++ suffix := hactions
      _ = presentation.actions first ++
          (stem ++ remainder) := by rw [hsuffix]
      _ = (presentation.actions first ++ stem) ++
          remainder := by rw [List.append_assoc]
  · exact hremaining
  · exact hcombinedRun
  · exact hvariable

end CriticalGuardedFixedTailPivotPresentation

end EncodedFirstOrderGrammar

end DCFEquivalence
