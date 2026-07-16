module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DepthExposure
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.NoExposureIndependence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinkingCore

@[expose]
public section

/-!
# Balancing segments

This file formalizes Definition 42's side-independent core.  In a left
balancing segment `active` is the left term and `pivot` the right term; a right
segment is obtained by swapping them.  The active term follows a word of the
fixed exposure length without a syntactic root run reaching one of its formal
successors along a proper prefix.  Finite trace agreement forces the pivot to
follow the same word.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A balancing segment before choosing its left/right orientation. -/
public structure BalancingSegment
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ)
    (active pivot : RegularTerm) (word : List (Label Action)) where
  active_target : RegularTerm
  word_length : word.length = bound
  agreement : g.TraceApprox bound active pivot
  active_run : g.run? word active = some active_target
  no_early_root_sink : ∀ initialSegment suffix,
    word = initialSegment ++ suffix → suffix ≠ [] →
    ¬g.RootSinksBy active initialSegment

/-- A positive exposure bound makes every balancing segment nonempty. -/
public theorem BalancingSegment.word_ne_nil
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {word : List (Label Action)}
    (segment : BalancingSegment g bound active pivot word)
    (hbound : 0 < bound) : word ≠ [] := by
  intro hnil
  have hlength := segment.word_length
  rw [hnil] at hlength
  simp at hlength
  omega

/-- Finite agreement through the segment length forces the pivot to execute
the same word. -/
public theorem BalancingSegment.exists_pivot_target
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {word : List (Label Action)}
    (segment : BalancingSegment g bound active pivot word) :
    ∃ target, g.run? word pivot = some target := by
  have hactiveTrace : g.IsTrace active word := by
    unfold IsTrace
    rw [segment.active_run]
    rfl
  have hsame := (g.traceApprox_iff_sameTracesThrough
    bound active pivot).mp segment.agreement word (by
      rw [segment.word_length])
  have hpivotTrace : g.IsTrace pivot word := hsame.mp hactiveTrace
  exact g.isTrace_iff_exists_executes.mp hpivotTrace

/-- The pivot target selected from determinism. -/
noncomputable def BalancingSegment.pivotTarget
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {word : List (Label Action)}
    (segment : BalancingSegment g bound active pivot word) : RegularTerm :=
  Classical.choose segment.exists_pivot_target

public theorem BalancingSegment.pivot_run
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {word : List (Label Action)}
    (segment : BalancingSegment g bound active pivot word) :
    g.run? word pivot = some segment.pivotTarget :=
  Classical.choose_spec segment.exists_pivot_target

/-- Groundness is invariant under a finite run when it is invariant under one
step. -/
public theorem PreservesGroundSteps.ground_of_run
    {g : EncodedFirstOrderGrammar Action} (hsteps : g.PreservesGroundSteps)
    {source target : RegularTerm} {word : List (Label Action)}
    (hsource : source.Ground g.ranks)
    (hrun : g.run? word source = some target) :
    target.Ground g.ranks := by
  induction word generalizing source with
  | nil =>
      simp at hrun
      subst target
      exact hsource
  | cons label word ih =>
      simp only [run?_cons] at hrun
      cases hstep : g.step? label source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep, Option.bind_some] at hrun
          exact ih (hsteps hsource hstep) hrun

/-- Executing the same prefix from trace-equivalent terms leaves
trace-equivalent residuals. -/
public theorem TraceEquivalent.residual
    {g : EncodedFirstOrderGrammar Action}
    {left right left' right' : RegularTerm}
    {word : List (Label Action)}
    (hequivalent : g.TraceEquivalent left right)
    (hleft : g.run? word left = some left')
    (hright : g.run? word right = some right') :
    g.TraceEquivalent left' right' := by
  apply Set.ext
  intro suffix
  have hleftQuotient : g.IsTrace left' suffix ↔
      g.IsTrace left (word ++ suffix) := by
    unfold IsTrace
    rw [g.run?_append, hleft]
    rfl
  have hrightQuotient : g.IsTrace right' suffix ↔
      g.IsTrace right (word ++ suffix) := by
    unfold IsTrace
    rw [g.run?_append, hright]
    rfl
  have hinitial : g.IsTrace left (word ++ suffix) ↔
      g.IsTrace right (word ++ suffix) := by
    exact Set.ext_iff.mp hequivalent (word ++ suffix)
  exact hleftQuotient.trans (hinitial.trans hrightQuotient.symm)

/-- An equivalent balancing pair has equivalent direct residuals after the
segment word.  Later balancing replaces active-side subterms while preserving
this semantic invariant. -/
public theorem BalancingSegment.directResidual_traceEquivalent
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {word : List (Label Action)}
    (segment : BalancingSegment g bound active pivot word)
    (hequivalent : g.TraceEquivalent active pivot) :
    g.TraceEquivalent segment.active_target segment.pivotTarget :=
  hequivalent.residual segment.active_run segment.pivot_run

/-- An unexposable immediate successor is semantically inactive in a
balancing comparison.  Replacing only that successor preserves the finite
agreement between the active side and its pivot.  This is the formal reason
such successors need not be retained in the active tail tuple of a bal-result.
-/
public theorem BalancingSegment.agreement_after_unexposable_replacement
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {active pivot : RegularTerm}
    {word : List (Label Action)}
    (segment : BalancingSegment g bound active pivot word)
    (position : g.SuccessorPosition)
    (hno : ¬ ∃ exposingWord, g.ExposesSuccessor position exposingWord)
    {activeArguments replacementArguments : List RegularTerm}
    (hactive : active =
      (RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate activeArguments)
    (hlengths :
      activeArguments.length = g.ranks.get position.1 ∧
      replacementArguments.length = g.ranks.get position.1)
    (hactiveGround : ∀ argument ∈ activeArguments,
      argument.Ground g.ranks)
    (hreplacementGround : ∀ argument ∈ replacementArguments,
      argument.Ground g.ranks)
    (hsame : ∀ j, j ≠ position.2.val →
      activeArguments[j]? = replacementArguments[j]?) :
    g.TraceApprox bound
      ((RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate replacementArguments)
      pivot := by
  have hindependent :=
    traceEquivalent_symbolTemplate_instances_of_not_exposable_ground
      hg position hno hlengths hactiveGround hreplacementGround hsame
  have hreplacementActive : g.TraceEquivalent
      ((RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).instantiate replacementArguments)
      active := by
    rw [hactive]
    exact hindependent.symm
  exact ((g.traceEquivalent_iff_forall_traceApprox _ _).mp
    hreplacementActive bound).trans segment.agreement

end EncodedFirstOrderGrammar

end DCFEquivalence
