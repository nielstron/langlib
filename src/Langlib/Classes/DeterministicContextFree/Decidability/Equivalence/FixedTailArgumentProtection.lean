module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OperationalFixedTailPresentation

@[expose]
public section

/-!
# Protecting the fixed tail tuple along retained pivot edges

The operational rebase rules out sinking from one fixed concrete base along
every retained prefix.  Consequently, after factoring the symbolic run at a
retained pivot, no prefix of the remaining edge can reach one of the fixed
tail variables.  The conclusion is inclusive: it also protects the endpoint
of the edge.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace FixedTailPivotPresentation

/-- If a later retained word factors through an earlier one, fixed-base
non-sinking along the later word keeps every symbolic prefix of the suffix
away from the common tail variables. -/
public theorem noVariableAlong_suffix_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (hdepth : 0 < presentation.depth)
    {first second : ℕ} {suffix : List Action}
    (hactions :
      presentation.actions second =
        presentation.actions first ++ suffix)
    (hnever :
      g.NeverSinksFromBase base
        (presentation.actions second)) :
    g.NoVariableAlong (presentation.schema first) suffix := by
  intro stem remainder hsuffix residual x hstemRun
  have hcombinedRun :
      g.runActions?
          (presentation.actions first ++ stem)
          (base.depthPrefix presentation.depth).head.toRegularTerm =
        some residual := by
    rw [runActions?, List.map_append, g.run?_append]
    rw [← runActions?, (presentation.residual first).symbolic_run]
    simpa [runActions?] using hstemRun
  have hneverPrefix :
      g.NeverSinksFromBase base
        (presentation.actions first ++ stem) := by
    intro sinkingStem sinkingRemainder hprefix hsinks
    apply hnever sinkingStem (sinkingRemainder ++ remainder)
    · calc
        presentation.actions second =
            presentation.actions first ++ suffix := hactions
        _ = presentation.actions first ++
            (stem ++ remainder) := by rw [hsuffix]
        _ = (presentation.actions first ++ stem) ++
            remainder := by rw [List.append_assoc]
        _ = (sinkingStem ++ sinkingRemainder) ++
            remainder := by rw [hprefix]
        _ = sinkingStem ++
            (sinkingRemainder ++ remainder) := by
              rw [List.append_assoc]
    · exact hsinks
  have happlicationDepth :
      residual.ApplicationDepth presentation.depth :=
    depthPrefix_residual_applicationDepth_of_neverSinksFromBase
      hg presentation.base_ground presentation.depth
      hcombinedRun hneverPrefix
  intro hvariable
  have hvariableRoot :
      residual.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hvariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  cases hdepthValue : presentation.depth with
  | zero => simp [hdepthValue] at hdepth
  | succ depth =>
      rw [hdepthValue] at happlicationDepth
      obtain ⟨Y, children, hroot, _hchildren⟩ :=
        happlicationDepth
      have happlicationRoot :
          residual.rootNode? = some (.inr (Y, children)) := by
        simpa [RegularTerm.rootNode?] using
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
      rw [hvariableRoot] at happlicationRoot
      simp at happlicationRoot

/-- Proper-prefix symbolic reflection is an immediate corollary of the
inclusive edge protection theorem. -/
public theorem noVariableBefore_suffix_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (hdepth : 0 < presentation.depth)
    {first second : ℕ} {suffix : List Action}
    (hactions :
      presentation.actions second =
        presentation.actions first ++ suffix)
    (hnever :
      g.NeverSinksFromBase base
        (presentation.actions second)) :
    g.NoVariableBefore (presentation.schema first) suffix :=
  (presentation.noVariableAlong_suffix_of_neverSinksFromBase
    hg hdepth hactions hnever).noVariableBefore

end FixedTailPivotPresentation

end EncodedFirstOrderGrammar

end DCFEquivalence
