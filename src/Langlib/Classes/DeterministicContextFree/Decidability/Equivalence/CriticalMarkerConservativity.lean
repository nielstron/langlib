module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalWorstInstance
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ExposedEquations

@[expose]
public section

/-!
# Conservativity of critical-marker extensions on original terms

The fresh critical markers add observable actions only at the fresh marker
symbols.  Consequently, a term graph whose application nodes all use symbols
of the original grammar has no genuinely new transition.  For a well-formed
original grammar this invariant is preserved by every original transition, so
every successful run from such a term is the pointwise lift of a unique-shaped
original word.

This is the marker-stable semantic interface needed by the finite-basis
argument: an open schema carried through the marker extension can be returned
to the original grammar once it is known to use only original symbols.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Original labelled rewriting preserves the fact that every application node
uses an original ranked symbol. -/
public theorem step?_some_usesOriginalSymbols
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {label : Label Action} {source target : RegularTerm}
    (hsource : source.UsesOriginalSymbols g.ranks)
    (hstep : g.step? label source = some target) :
    target.UsesOriginalSymbols g.ranks := by
  cases label with
  | inl action =>
      change g.rootRewrite? action source = some target at hstep
      unfold rootRewrite? at hstep
      cases hroot : source.rootApplication? with
      | none => simp [hroot] at hstep
      | some application =>
          rcases application with ⟨X, children⟩
          simp only [hroot] at hstep
          obtain ⟨rhs, hrule, htarget⟩ :=
            Option.map_eq_some_iff.mp hstep
          subst target
          obtain ⟨rank, _hrank, hrhs⟩ :=
            selected_rhs_wellFormed hg hrule
          apply RegularTerm.usesOriginalSymbols_instantiate
            (RegularTerm.usesOriginalSymbols_of_wellFormed hrhs)
          intro argument hargument
          obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hargument
          exact RegularTerm.usesOriginalSymbols_withRoot hsource child
  | inr x =>
      unfold step? at hstep
      cases hroot : source.rootNode? with
      | none => simp [hroot] at hstep
      | some node =>
          cases node with
          | inr application => simp [hroot] at hstep
          | inl y =>
              by_cases hxy : x = y
              · simp [hroot, hxy] at hstep
                subst target
                exact hsource
              · simp [hroot, hxy] at hstep

/-- A fresh marker action is disabled at every term using only symbols from the
original rank table.  Variables are stuck for ordinary actions as usual. -/
public theorem withCriticalMarkers_step?_marker_none_of_originalSymbols
    (g : EncodedFirstOrderGrammar Action) (count marker : ℕ)
    {source : RegularTerm}
    (hsource : source.UsesOriginalSymbols g.ranks) :
    (g.withCriticalMarkers count).step? (.inl (.inr marker)) source = none := by
  change (g.withCriticalMarkers count).rootRewrite? (.inr marker) source = none
  unfold rootRewrite?
  cases hroot : source.rootApplication? with
  | none => rfl
  | some application =>
      rcases application with ⟨X, children⟩
      have hrootNode := RegularTerm.nodeAt?_root_of_rootApplication? hroot
      obtain ⟨rank, hrank, _hchildren⟩ :=
        hsource X children (List.mem_of_getElem? hrootNode)
      have hX : X < g.ranks.length :=
        (List.getElem?_eq_some_iff.mp hrank).1
      simp only [hroot]
      rw [withCriticalMarkers_ruleLookup_markerAction_originalSymbol
        g count marker X hX]
      rfl

/-- Every successful transition from an original-symbol term in the marker
extension is a lifted original transition. -/
public theorem withCriticalMarkers_step?_some_iff_original
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    {label : Label (Action ⊕ ℕ)} {source target : RegularTerm}
    (hsource : source.UsesOriginalSymbols g.ranks) :
    (g.withCriticalMarkers count).step? label source = some target ↔
      ∃ originalLabel : Label Action,
        label = liftCriticalLabel originalLabel ∧
          g.step? originalLabel source = some target := by
  constructor
  · intro hstep
    cases label with
    | inl action =>
        cases action with
        | inl originalAction =>
            refine ⟨.inl originalAction, rfl, ?_⟩
            exact (withCriticalMarkers_step?_lift g count
              (.inl originalAction) source).symm.trans hstep
        | inr marker =>
            rw [withCriticalMarkers_step?_marker_none_of_originalSymbols
              g count marker hsource] at hstep
            contradiction
    | inr x =>
        refine ⟨.inr x, rfl, ?_⟩
        simpa using hstep
  · rintro ⟨originalLabel, rfl, hstep⟩
    rw [withCriticalMarkers_step?_lift]
    exact hstep

/-- Successful runs from an original-symbol term are exactly lifted original
runs.  Well-formedness of the grammar is used only to preserve the symbol
invariant at intermediate residuals. -/
public theorem withCriticalMarkers_run?_some_iff_original
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count : ℕ) {word : List (Label (Action ⊕ ℕ))}
    {source target : RegularTerm}
    (hsource : source.UsesOriginalSymbols g.ranks) :
    (g.withCriticalMarkers count).run? word source = some target ↔
      ∃ originalWord : List (Label Action),
        word = originalWord.map liftCriticalLabel ∧
          g.run? originalWord source = some target := by
  constructor
  · intro hrun
    induction word generalizing source target with
    | nil =>
        simp only [run?_nil] at hrun
        have htarget : target = source := Option.some.inj hrun.symm
        subst target
        exact ⟨[], rfl, rfl⟩
    | cons label word ih =>
        rw [run?_cons] at hrun
        cases hstep : (g.withCriticalMarkers count).step? label source with
        | none => simp [hstep] at hrun
        | some next =>
            simp only [hstep, Option.bind_some] at hrun
            obtain ⟨originalLabel, hlabel, horiginalStep⟩ :=
              (withCriticalMarkers_step?_some_iff_original
                g count hsource).mp hstep
            have hnext := step?_some_usesOriginalSymbols hg hsource
              horiginalStep
            obtain ⟨originalWord, hword, horiginalRun⟩ :=
              ih hnext hrun
            refine ⟨originalLabel :: originalWord, ?_, ?_⟩
            · simp [hlabel, hword]
            · simp only [run?_cons, horiginalStep,
                Option.bind_some, horiginalRun]
  · rintro ⟨originalWord, rfl, hrun⟩
    simpa [withCriticalMarkers_run?_lift] using hrun

/-- Original trace equivalence is preserved by adding critical markers when
both compared terms use only symbols of the original grammar. -/
public theorem traceEquivalent_withCriticalMarkers_of_originalSymbols
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count : ℕ) {left right : RegularTerm}
    (hleft : left.UsesOriginalSymbols g.ranks)
    (hright : right.UsesOriginalSymbols g.ranks)
    (hequivalent : g.TraceEquivalent left right) :
    (g.withCriticalMarkers count).TraceEquivalent left right := by
  apply Set.ext
  intro word
  constructor
  · intro hleftTrace
    obtain ⟨leftTarget, hleftRun⟩ :=
      (g.withCriticalMarkers count).isTrace_iff_exists_executes.mp
        hleftTrace
    obtain ⟨originalWord, hword, hleftOriginalRun⟩ :=
      (withCriticalMarkers_run?_some_iff_original
        g hg count hleft).mp hleftRun
    have hleftOriginalTrace : g.IsTrace left originalWord :=
      g.isTrace_iff_exists_executes.mpr
        ⟨leftTarget, hleftOriginalRun⟩
    have hrightOriginalTrace : g.IsTrace right originalWord := by
      exact (Set.ext_iff.mp hequivalent originalWord).mp
        hleftOriginalTrace
    obtain ⟨rightTarget, hrightOriginalRun⟩ :=
      g.isTrace_iff_exists_executes.mp hrightOriginalTrace
    apply (g.withCriticalMarkers count).isTrace_iff_exists_executes.mpr
    refine ⟨rightTarget, ?_⟩
    rw [hword]
    change (g.withCriticalMarkers count).run?
      (originalWord.map liftCriticalLabel) right = some rightTarget
    rw [withCriticalMarkers_run?_lift]
    exact hrightOriginalRun
  · intro hrightTrace
    obtain ⟨rightTarget, hrightRun⟩ :=
      (g.withCriticalMarkers count).isTrace_iff_exists_executes.mp
        hrightTrace
    obtain ⟨originalWord, hword, hrightOriginalRun⟩ :=
      (withCriticalMarkers_run?_some_iff_original
        g hg count hright).mp hrightRun
    have hrightOriginalTrace : g.IsTrace right originalWord :=
      g.isTrace_iff_exists_executes.mpr
        ⟨rightTarget, hrightOriginalRun⟩
    have hleftOriginalTrace : g.IsTrace left originalWord := by
      exact (Set.ext_iff.mp hequivalent originalWord).mpr
        hrightOriginalTrace
    obtain ⟨leftTarget, hleftOriginalRun⟩ :=
      g.isTrace_iff_exists_executes.mp hleftOriginalTrace
    apply (g.withCriticalMarkers count).isTrace_iff_exists_executes.mpr
    refine ⟨leftTarget, ?_⟩
    rw [hword]
    change (g.withCriticalMarkers count).run?
      (originalWord.map liftCriticalLabel) left = some leftTarget
    rw [withCriticalMarkers_run?_lift]
    exact hleftOriginalRun

/-- On original-symbol terms, adding critical markers is semantically
conservative in both directions. -/
public theorem traceEquivalent_withCriticalMarkers_iff_originalSymbols
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count : ℕ) {left right : RegularTerm}
    (hleft : left.UsesOriginalSymbols g.ranks)
    (hright : right.UsesOriginalSymbols g.ranks) :
    (g.withCriticalMarkers count).TraceEquivalent left right ↔
      g.TraceEquivalent left right := by
  constructor
  · exact traceEquivalent_of_withCriticalMarkers g count
  · exact traceEquivalent_withCriticalMarkers_of_originalSymbols
      g hg count hleft hright

end EncodedFirstOrderGrammar

end DCFEquivalence
