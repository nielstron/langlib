module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FaithfulFiniteWindowSchemaRecurrence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinking

@[expose]
public section

/-!
# Finite-window schema recurrence without faithful arguments

The guarded fixed-tail presentation already records the exact open execution
between consecutive schemas.  In the bounded terminal branch we can therefore
use the actual next schema itself.  No cancellation through the common
argument tuple is needed: bounded ordinary execution directly supplies its
prefix witness and semantic-depth bound.

The complementary sinking branch is developed in `RootSinking`: a
root-syntactic sinking witness replays on the open schema and reaches one of
its literal immediate children.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Concrete finite-window premise retaining the root-syntactic witness.
At every position of one exact ground run, either the remaining suffix is
short or a bounded prefix root-sinks from the current concrete state. -/
@[expose] public def BoundedReachOrRootSinkAlong
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (actions : List Action)
    (window : ℕ) : Prop :=
  ∀ consumed remaining current,
    actions = consumed ++ remaining →
    g.runActions? consumed source = some current →
    remaining.length ≤ window ∨
      ∃ sinking rest,
        remaining = sinking ++ rest ∧
          sinking.length ≤ window ∧
          g.RootSinksBy current
            (sinking.map Sum.inl)

namespace BoundedReachOrRootSinkAlong

/-- Enlarging the window preserves the concrete root-sinking premise. -/
public theorem mono
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {actions : List Action}
    {small large : ℕ}
    (hwindow :
      g.BoundedReachOrRootSinkAlong source actions small)
    (hle : small ≤ large) :
    g.BoundedReachOrRootSinkAlong source actions large := by
  intro consumed remaining current hactions hrun
  rcases hwindow consumed remaining current hactions hrun with
    hshort | ⟨sinking, rest, hremaining, hlength, hsinks⟩
  · exact Or.inl (hshort.trans hle)
  · exact Or.inr ⟨sinking, rest, hremaining,
      hlength.trans hle, hsinks⟩

end BoundedReachOrRootSinkAlong

/-- A protected nonempty symbolic suffix cannot start at a schema variable.
For a prefix-witnessed well-formed schema its root is therefore an
application. -/
public theorem NoVariableBefore.exists_rootApplication
    {g : EncodedFirstOrderGrammar Action}
    {schema : RegularTerm} {width : ℕ} {word : List Action}
    (hwitness : schema.HasPrefixWitness width)
    (hnoVariable : g.NoVariableBefore schema word)
    (hword : word ≠ []) :
    ∃ rootSymbol children,
      schema.rootApplication? =
        some (rootSymbol, children) := by
  obtain ⟨support, hsupport⟩ := hwitness
  rcases hsupport.2 schema.root hsupport.1 with
    hvariable | happlication
  · obtain ⟨x, hrootNode, _hx⟩ := hvariable
    have hrootVariable :
        schema.rootNode? = some (.inl x) := by
      simpa [RegularTerm.rootNode?] using hrootNode
    exfalso
    exact hnoVariable [] word (by simp) hword schema x
      (by simp [runActions?])
      (unfoldingEquivalent_variableTerm_of_rootNode?
        hrootVariable)
  · obtain ⟨rootSymbol, children, hrootNode, _hchildren⟩ :=
      happlication
    exact ⟨rootSymbol, children, by
      simp [RegularTerm.rootApplication?,
        RegularTerm.rootNode?, hrootNode]⟩

/-- A root-sinking witness on a term semantically equal to one instance of an
open application can be replayed on the open schema itself.  Only the root
symbol and arity are transported; no equivalence cancellation through the
argument tuple is used. -/
public theorem RootSinksBy.of_schemaInstance
    {g : EncodedFirstOrderGrammar Action}
    {source schema : RegularTerm}
    {arguments : List RegularTerm}
    {word : List (Label Action)}
    {variableBound rootSymbol : ℕ}
    {children : List ℕ}
    (hschema :
      schema.WellFormed g.ranks variableBound)
    (hroot :
      schema.rootApplication? =
        some (rootSymbol, children))
    (hsource :
      source.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hsinks : g.RootSinksBy source word) :
    g.RootSinksBy schema word := by
  have hschemaClosed :
      schema.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschema
  have hinstanceRoot :
      (schema.instantiate arguments).rootApplication? =
        some (rootSymbol,
          children.map (schema.resolveRHSRef arguments)) :=
    RegularTerm.instantiate_rootApplication?
      hschemaClosed hroot
  have hinstanceSinks :
      g.RootSinksBy
        (schema.instantiate arguments) word :=
    hsinks.of_unfoldingEquivalent hsource
  exact hinstanceSinks.retarget hinstanceRoot hroot (by simp)

/-- A concrete root-sinking prefix aligned with an arbitrary schema instance
selects a literal immediate child of the open schema.  The exact action
factorization is retained for recursive continuation. -/
public theorem RootSinksBy.exists_schemaChild_of_instance
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width : ℕ}
    {arguments : List RegularTerm}
    {schema source : RegularTerm}
    {sinkingActions restActions : List Action}
    (hschema :
      schema.WellFormed g.ranks arity)
    (hwitness : schema.HasPrefixWitness width)
    (hsource :
      source.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hnoVariable :
      g.NoVariableBefore schema
        (sinkingActions ++ restActions))
    (hsinks :
      g.RootSinksBy source
        (sinkingActions.map Sum.inl)) :
    ∃ stemActions sinkRemainderActions target child,
      sinkingActions =
          stemActions ++ sinkRemainderActions ∧
        stemActions ≠ [] ∧
        schema.DescendantAt 1 child ∧
        g.runActions? stemActions schema = some target ∧
        target.UnfoldingEquivalent
          (schema.withRoot child) := by
  have hsinkingNonempty : sinkingActions ≠ [] := by
    intro hnil
    subst sinkingActions
    exact g.not_rootSinksBy_nil source (by simpa using hsinks)
  obtain ⟨rootSymbol, children, hroot⟩ :=
    hnoVariable.exists_rootApplication hwitness
      (List.append_ne_nil_of_left_ne_nil
        hsinkingNonempty restActions)
  have hschemaSinks :
      g.RootSinksBy schema
        (sinkingActions.map Sum.inl) :=
    hsinks.of_schemaInstance hschema hroot hsource
  obtain ⟨stemActions, labelRemainder, target, child,
      hword, hstemNonempty, hchild, hrun, htarget⟩ :=
    hschemaSinks.exists_schemaChild hg ⟨arity, hschema⟩
  obtain ⟨actualStem, sinkRemainderActions,
      hsinking, hstemMap, _hremainderMap⟩ :=
    List.map_eq_append_iff.mp hword
  have hactualStem : actualStem = stemActions :=
    (List.map_inj_right
      (fun _ _ h => Sum.inl.inj h :
        Function.Injective
          (Sum.inl : Action → Label Action))).mp hstemMap
  subst actualStem
  exact ⟨stemActions, sinkRemainderActions, target, child,
    hsinking, hstemNonempty, hchild, hrun, htarget⟩

/-- The exact open-schema finite-window premise.  At every position of one
symbolic run, either the remaining suffix is short or a bounded nonempty
prefix reaches a residual which denotes a literal immediate child of the
current schema.

Unlike `BoundedReachOrSinkAlong`, the sinking alternative is syntactic in the
open schema.  It is therefore stable under arbitrary substitutions and needs
no cancellation property for the argument tuple. -/
@[expose] public def BoundedReachOrSchemaSinkAlong
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (actions : List Action)
    (window : ℕ) : Prop :=
  ∀ consumed remaining current,
    actions = consumed ++ remaining →
    g.runActions? consumed source = some current →
    remaining.length ≤ window ∨
      ∃ sinking rest target child,
        remaining = sinking ++ rest ∧
          sinking.length ≤ window ∧
          sinking ≠ [] ∧
          current.DescendantAt 1 child ∧
          g.runActions? sinking current = some target ∧
          target.UnfoldingEquivalent
            (current.withRoot child)

namespace BoundedReachOrSchemaSinkAlong

/-- Enlarging the window preserves the open-schema reach-or-sink premise. -/
public theorem mono
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {actions : List Action}
    {small large : ℕ}
    (hwindow :
      g.BoundedReachOrSchemaSinkAlong source actions small)
    (hle : small ≤ large) :
    g.BoundedReachOrSchemaSinkAlong source actions large := by
  intro consumed remaining current hactions hrun
  rcases hwindow consumed remaining current hactions hrun with
    hshort | ⟨sinking, rest, target, child, hremaining,
      hlength, hnonempty, hchild, hsinkingRun, htarget⟩
  · exact Or.inl (hshort.trans hle)
  · exact Or.inr ⟨sinking, rest, target, child, hremaining,
      hlength.trans hle, hnonempty, hchild,
      hsinkingRun, htarget⟩

end BoundedReachOrSchemaSinkAlong

/-- A concrete root-sinking window on one arbitrary ground instance induces
the corresponding open-schema window on the exact symbolic run.  This is the
substitution-independent bridge from the structured `M₂` trajectory to the
faithfulness-free depth recurrence. -/
public theorem BoundedReachOrRootSinkAlong.toSchema
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width window : ℕ}
    {arguments : List RegularTerm}
    {schema source concreteTarget : RegularTerm}
    {actions : List Action}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hschema :
      schema.WellFormed g.ranks arity)
    (hwitness : schema.HasPrefixWitness width)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    (hsourceGround : source.Ground g.ranks)
    (hsource :
      source.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hconcreteRun :
      g.runActions? actions source =
        some concreteTarget)
    (hnoVariable :
      g.NoVariableBefore schema actions)
    (hwindow :
      g.BoundedReachOrRootSinkAlong
        source actions window) :
    g.BoundedReachOrSchemaSinkAlong
      schema actions window := by
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hschemaClosed :
      schema.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschema
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      hschemaClosed hargumentsClosed
  intro consumed remaining current hactions hcurrentRun
  have hconcretePrefix :
      ∃ concrete,
        g.runActions? consumed source = some concrete := by
    rw [hactions, runActions?, List.map_append,
      g.run?_append] at hconcreteRun
    cases hprefix :
        g.run? (consumed.map Sum.inl) source with
    | none =>
        simp [hprefix] at hconcreteRun
    | some concrete =>
        exact ⟨concrete, by
          simpa [runActions?] using hprefix⟩
  obtain ⟨concrete, hconcretePrefix⟩ :=
    hconcretePrefix
  rcases hwindow consumed remaining concrete
      hactions hconcretePrefix with
    hshort | ⟨sinking, rest, hremaining,
      hsinkingLength, hsinks⟩
  · exact Or.inl hshort
  · have hcurrentWellFormed :
        current.WellFormed g.ranks arity :=
      g.runActions?_preserves_wellFormed_padded
        hg hpadding consumed hschema hcurrentRun
    have hcurrentWitness :
        current.HasPrefixWitness width :=
      hwitness.runActions
        hg hpadding hschema hcurrentRun
    obtain ⟨instanceTarget, hinstanceRun,
        hcurrentInstance⟩ :=
      g.runActions?_instantiate hg consumed hschema
        hargumentsClosed hcurrentRun
    obtain ⟨transported, htransportedRun,
        htransportedInstance⟩ :=
      exists_runActions_of_unfoldingEquivalent
        hg hsource
        (RegularTerm.referenceClosed_of_ground
          hsourceGround)
        hinstanceClosed hinstanceRun
    have htransported :
        transported = concrete :=
      Option.some.inj
        (htransportedRun.symm.trans hconcretePrefix)
    subst transported
    have hconcreteCurrent :
        concrete.UnfoldingEquivalent
          (current.instantiate arguments) :=
      htransportedInstance.trans hcurrentInstance.symm
    have hnoCurrent :
        g.NoVariableBefore current remaining := by
      apply NoVariableBefore.of_run_prefix
        (hrun := hcurrentRun)
      rw [← hactions]
      exact hnoVariable
    have hnoSinking :
        g.NoVariableBefore current
          (sinking ++ rest) := by
      rw [← hremaining]
      exact hnoCurrent
    obtain ⟨stem, sinkRemainder, target, child,
        hsinking, hstemNonempty, hchild, hstemRun,
        htarget⟩ :=
      hsinks.exists_schemaChild_of_instance
        hg hcurrentWellFormed hcurrentWitness
        hconcreteCurrent hnoSinking
    refine Or.inr ⟨stem, sinkRemainder ++ rest,
      target, child, ?_, ?_, hstemNonempty,
      hchild, hstemRun, htarget⟩
    · calc
        remaining = sinking ++ rest := hremaining
        _ = (stem ++ sinkRemainder) ++ rest := by
          rw [← hsinking]
        _ = stem ++ (sinkRemainder ++ rest) := by
          rw [List.append_assoc]
    · have hstemLength : stem.length ≤ sinking.length := by
        rw [hsinking, List.length_append]
        omega
      exact hstemLength.trans hsinkingLength

/-- The bounded terminal branch of Proposition 49, using the exact symbolic
schema transition rather than reflecting the concrete endpoint through a
possibly non-faithful argument tuple. -/
public theorem
    exists_exactFiniteWindowSchemaSuccessor_of_boundedRun
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width sourceDepth window : ℕ}
    {arguments : List RegularTerm}
    {current actualNext : RegularTerm}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hcurrentWellFormed :
      current.WellFormed g.ranks arity)
    (hcurrentWitness : current.HasPrefixWitness width)
    (hcurrentDepth :
      current.UnfoldingDepthAtMost sourceDepth)
    (hactualWellFormed :
      actualNext.WellFormed g.ranks arity)
    {actions : List Action}
    (hactionsLength : actions.length ≤ window)
    (hrun :
      g.runActions? actions current = some actualNext) :
    Nonempty (FaithfulFiniteWindowSchemaSuccessor
      g arity width arguments actualNext
        (g.residualUnfoldingDepthBound window sourceDepth)) := by
  have hactualWitness :
      actualNext.HasPrefixWitness width :=
    hcurrentWitness.runActions
      hg hpadding hcurrentWellFormed hrun
  have hactualDepth :
      actualNext.UnfoldingDepthAtMost
        (g.residualUnfoldingDepthBound window sourceDepth) := by
    have hlocal :
        actualNext.UnfoldingDepthAtMost
          (g.residualUnfoldingDepthBound
            actions.length sourceDepth) :=
      g.runActions?_preserves_unfoldingDepthAtMost
        hg ⟨arity, hcurrentWellFormed⟩
        hcurrentDepth hrun
    intro depth index hdescendant
    exact (hlocal hdescendant).trans
      (g.residualUnfoldingDepthBound_mono_steps'
        hactionsLength)
  exact ⟨
    { schema := actualNext
      wellFormed := hactualWellFormed
      hasPrefixWitness := hactualWitness
      unfoldingDepthAtMost := hactualDepth
      instance_equivalent :=
        RegularTerm.unfoldingEquivalent_refl _
      equivalent_actual :=
        RegularTerm.unfoldingEquivalent_refl _ }⟩

/-- The open-schema recurrence from an arbitrary position of an exact
symbolic run.  Each schema-sinking branch consumes a nonempty prefix and
strictly decreases the semantic depth of the current finite schema. -/
public theorem
    exists_exactFiniteWindowSchemaSuccessor_from_position
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width sourceDepth window : ℕ}
    {arguments : List RegularTerm}
    {origin actualNext current : RegularTerm}
    {actions consumed remaining : List Action}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hactualWellFormed :
      actualNext.WellFormed g.ranks arity)
    (hcurrentWellFormed :
      current.WellFormed g.ranks arity)
    (hcurrentWitness : current.HasPrefixWitness width)
    (hcurrentDepth :
      current.UnfoldingDepthAtMost sourceDepth)
    (hwindow :
      g.BoundedReachOrSchemaSinkAlong origin actions window)
    (hactions :
      actions = consumed ++ remaining)
    (hprefixRun :
      g.runActions? consumed origin = some current)
    (hremainingRun :
      g.runActions? remaining current = some actualNext) :
    Nonempty (FaithfulFiniteWindowSchemaSuccessor
      g arity width arguments actualNext
        (g.residualUnfoldingDepthBound window sourceDepth)) := by
  induction sourceDepth generalizing
      current consumed remaining with
  | zero =>
      rcases hwindow consumed remaining current
          hactions hprefixRun with
        hshort | ⟨sinking, rest, target, child,
          hremaining, _hlength, _hnonempty, hchild,
          _hsinkingRun, _htarget⟩
      · exact
          exists_exactFiniteWindowSchemaSuccessor_of_boundedRun
            hg hpadding hcurrentWellFormed hcurrentWitness
            hcurrentDepth hactualWellFormed hshort
            hremainingRun
      · have himpossible : 1 ≤ 0 :=
          hcurrentDepth hchild
        omega
  | succ sourceDepth ih =>
      rcases hwindow consumed remaining current
          hactions hprefixRun with
        hshort | ⟨sinking, rest, target, child,
          hremaining, _hlength, _hnonempty, hchild,
          hsinkingRun, htarget⟩
      · exact
          exists_exactFiniteWindowSchemaSuccessor_of_boundedRun
            hg hpadding hcurrentWellFormed hcurrentWitness
            hcurrentDepth hactualWellFormed hshort
            hremainingRun
      · have htargetWellFormed :
            target.WellFormed g.ranks arity :=
          g.runActions?_preserves_wellFormed_padded
            hg hpadding sinking hcurrentWellFormed
            hsinkingRun
        have htargetWitness :
            target.HasPrefixWitness width :=
          hcurrentWitness.runActions
            hg hpadding hcurrentWellFormed hsinkingRun
        have hchildDepth :
            (current.withRoot child).UnfoldingDepthAtMost
              sourceDepth :=
          hcurrentDepth.withRoot_of_descendant hchild
        have htargetDepth :
            target.UnfoldingDepthAtMost sourceDepth :=
          htarget.symm.unfoldingDepthAtMost hchildDepth
        have hnextActions :
            actions =
              (consumed ++ sinking) ++ rest := by
          calc
            actions = consumed ++ remaining := hactions
            _ = consumed ++ (sinking ++ rest) := by
              rw [hremaining]
            _ = (consumed ++ sinking) ++ rest := by
              rw [List.append_assoc]
        have hnextPrefixRun :
            g.runActions? (consumed ++ sinking) origin =
              some target := by
          rw [runActions?, List.map_append, g.run?_append]
          rw [← runActions?, hprefixRun]
          simpa [runActions?] using hsinkingRun
        have hrestRun :
            g.runActions? rest target =
              some actualNext := by
          rw [hremaining, runActions?,
            List.map_append, g.run?_append] at hremainingRun
          rw [← runActions?, hsinkingRun] at hremainingRun
          simpa [runActions?] using hremainingRun
        have hsuccessor :
            Nonempty (FaithfulFiniteWindowSchemaSuccessor
              g arity width arguments actualNext
                (g.residualUnfoldingDepthBound
                  window sourceDepth)) :=
          ih htargetWellFormed htargetWitness htargetDepth
            hnextActions hnextPrefixRun hrestRun
        obtain ⟨successor⟩ := hsuccessor
        exact ⟨successor.mono
          (g.residualUnfoldingDepthBound_mono_initial'
            window (Nat.le_succ sourceDepth))⟩

/-- Starting at the beginning of an exact symbolic run gives the
faithfulness-free Proposition-49 finite-window successor bound. -/
public theorem exists_exactFiniteWindowSchemaSuccessor
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width sourceDepth window : ℕ}
    {arguments : List RegularTerm}
    {current actualNext : RegularTerm}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hcurrentWellFormed :
      current.WellFormed g.ranks arity)
    (hcurrentWitness : current.HasPrefixWitness width)
    (hcurrentDepth :
      current.UnfoldingDepthAtMost sourceDepth)
    (hactualWellFormed :
      actualNext.WellFormed g.ranks arity)
    {actions : List Action}
    (hrun :
      g.runActions? actions current = some actualNext)
    (hwindow :
      g.BoundedReachOrSchemaSinkAlong
        current actions window) :
    Nonempty (FaithfulFiniteWindowSchemaSuccessor
      g arity width arguments actualNext
        (g.residualUnfoldingDepthBound window sourceDepth)) := by
  apply exists_exactFiniteWindowSchemaSuccessor_from_position
    hg hpadding hactualWellFormed
    hcurrentWellFormed hcurrentWitness hcurrentDepth
    hwindow (consumed := []) (remaining := actions)
  · simp
  · simp [runActions?]
  · exact hrun

end EncodedFirstOrderGrammar

end DCFEquivalence
