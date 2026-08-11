module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FinitePrefixExecution

@[expose]
public section

/-!
# Symbolic reflection before a variable is exposed

Application-depth reflection handles runs shorter than a fixed finite prefix.
Balancing segments need the complementary invariant: a symbolic source can be
executed as long as no proper prefix reaches a variable root.  A variable
would be exactly the point where a concrete instance sinks into one of its
arguments.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- No proper prefix of `word` reaches a residual denoting a variable. -/
@[expose] public def NoVariableBefore
    (g : EncodedFirstOrderGrammar Action)
    (schema : RegularTerm) (word : List Action) : Prop :=
  ∀ stem suffix,
    word = stem ++ suffix →
    suffix ≠ [] →
    ∀ residual x,
      g.runActions? stem schema = some residual →
      ¬residual.UnfoldingEquivalent (RegularTerm.variableTerm x)

/-- A concrete instance run reflects to the open schema if no proper
symbolic prefix exposes a variable. -/
public theorem runActions?_reflects_instantiation_of_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema concrete : RegularTerm} {arguments : List RegularTerm}
    (word : List Action)
    (hschema : ∃ arity, schema.WellFormed g.ranks arity)
    (harguments : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hrun :
      g.runActions? word (schema.instantiate arguments) =
        some concrete)
    (hnoVariable : g.NoVariableBefore schema word) :
    ∃ residual,
      g.runActions? word schema = some residual ∧
      (residual.instantiate arguments).UnfoldingEquivalent concrete := by
  induction word generalizing schema concrete with
  | nil =>
      simp [runActions?] at hrun
      subst concrete
      exact ⟨schema, by simp [runActions?],
        RegularTerm.unfoldingEquivalent_refl _⟩
  | cons action word ih =>
      cases hconcreteStep :
          g.step? (.inl action) (schema.instantiate arguments) with
      | none =>
          simp [runActions?, hconcreteStep] at hrun
      | some concreteNext =>
          have htail :
              g.runActions? word concreteNext = some concrete := by
            simpa [runActions?, hconcreteStep] using hrun
          have hschemaWellFormed :=
            Classical.choose_spec hschema
          have hschemaClosed :=
            RegularTerm.referenceClosed_of_wellFormed hschemaWellFormed
          have hnotVariable :
              ∀ x, ¬schema.UnfoldingEquivalent
                (RegularTerm.variableTerm x) := by
            intro x hequivalent
            exact hnoVariable [] (action :: word)
              (by simp) (by simp) schema x
              (by simp [runActions?]) hequivalent
          have hdepthOne : schema.ApplicationDepth 1 := by
            cases hroot : schema.rootNode? with
            | none =>
                have hrootLt := hschemaClosed.1
                unfold RegularTerm.rootNode?
                  RegularTerm.nodeAt? at hroot
                rw [List.getElem?_eq_none_iff] at hroot
                omega
            | some node =>
                cases node with
                | inl x =>
                    exact (hnotVariable x
                      (unfoldingEquivalent_variableTerm_of_rootNode?
                        hroot)).elim
                | inr application =>
                    rcases application with ⟨X, children⟩
                    refine ⟨X, children, ?_, ?_⟩
                    · simp [RegularTerm.rootApplication?,
                        hroot]
                    · intro child hchild
                      trivial
          obtain ⟨next, hstep⟩ :=
            exists_stepAction_of_instantiate_step
              hschemaClosed hdepthOne hconcreteStep
          have hnextWellFormed :=
            stepAction_some_wellFormed hg hschema hstep
          have hsymbolicOne :
              g.runActions? [action] schema = some next := by
            simpa [runActions?] using hstep
          obtain ⟨concreteNext', hconcreteOne,
              hnextEquivalent⟩ :=
            g.runActions?_instantiate hg [action]
              hschemaWellFormed harguments hsymbolicOne
          have hconcreteNextEq : concreteNext' = concreteNext := by
            have hconcreteOne' :
                g.runActions? [action]
                    (schema.instantiate arguments) =
                  some concreteNext := by
              simpa [runActions?] using hconcreteStep
            exact Option.some.inj
              (hconcreteOne.symm.trans hconcreteOne')
          subst concreteNext'
          have hnextInstanceClosed :
              (next.instantiate arguments).ReferenceClosed :=
            RegularTerm.instantiate_referenceClosed
              (RegularTerm.referenceClosed_of_wellFormed
                (Classical.choose_spec hnextWellFormed))
              harguments
          have hconcreteNextClosed :
              concreteNext.ReferenceClosed :=
            step?_preserves_referenceClosed hg
              (RegularTerm.instantiate_referenceClosed
                hschemaClosed harguments)
              hconcreteStep
          have htailRelation :=
            g.runActions?_congr_unfoldingEquivalent hg word
              hnextInstanceClosed hconcreteNextClosed hnextEquivalent
          rw [htail] at htailRelation
          cases hnextRun :
              g.runActions? word (next.instantiate arguments) with
          | none =>
              rw [hnextRun] at htailRelation
              cases htailRelation
          | some nextConcrete =>
              rw [hnextRun] at htailRelation
              cases htailRelation with
              | some htargets =>
                  have hnoNext : g.NoVariableBefore next word := by
                    intro stem suffix hword hsuffix residual x
                      hstem hequivalent
                    apply hnoVariable (action :: stem) suffix
                    · simp [hword, List.cons_append]
                    · exact hsuffix
                    · simpa [runActions?, hstep] using hstem
                    · exact hequivalent
                  obtain ⟨residual, hsymbolicTail,
                      hresidualEquivalent⟩ :=
                    ih hnextWellFormed hnextRun hnoNext
                  exact ⟨residual, by
                    simpa [runActions?, hstep] using hsymbolicTail,
                    hresidualEquivalent.trans htargets⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
