module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.NonSinkingReflection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaSinkingDescent

@[expose]
public section

/-!
# Excluding premature schema-variable hits during sinking

`NoVariableBefore` is deliberately a proper-prefix invariant: it permits a
variable exactly at the endpoint of the protected word.  A positive sinking
step, however, selects a nonempty prefix of its available action word.  If
there is still protected input after that word, a root-variable alternative
would occur at a proper prefix and is impossible.  Consequently the first
sinking step must descend through an immediate application child.

The result retains the exact endpoints of both the concrete source run and
the canonical schema-instance run.  This is the form needed to re-enter a
window hypothesis after one recursive descent.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A sinking action prefix protected by `NoVariableBefore` cannot start at
a schema variable.  It therefore reaches an instance of an immediate schema
child.  Both deterministic runs and their semantic alignment are retained.

The extra `restActions` records why the beginning of `sinkingActions` is
still a proper prefix of the protected word.  The theorem remains valid when
it is empty, since sinking itself makes `sinkingActions` nonempty; in that
case only a variable at the *final endpoint* of the sinking word remains
outside the scope of the conclusion. -/
public theorem SinksBy.exists_schemaChild_of_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema canonical source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {support : List ℕ}
    {sinkingActions restActions : List Action}
    (hwitness : schema.PrefixWitness width support)
    (hschemaClosed : schema.ReferenceClosed)
    (hcanonicalGround : canonical.Ground g.ranks)
    (hsourceGround : source.Ground g.ranks)
    (hcanonicalSchema :
      canonical.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hsourceCanonical : source.UnfoldingEquivalent canonical)
    (hnoVariable :
      g.NoVariableBefore schema
        (sinkingActions ++ restActions))
    (hsinks :
      g.SinksBy source (sinkingActions.map Sum.inl)) :
    ∃ stemActions sinkRemainderActions
        sourceTarget canonicalTarget child,
      sinkingActions = stemActions ++ sinkRemainderActions ∧
        stemActions ≠ [] ∧
        schema.DescendantAt 1 child ∧
        g.runActions? stemActions source = some sourceTarget ∧
        g.runActions? stemActions canonical = some canonicalTarget ∧
        canonicalTarget.UnfoldingEquivalent sourceTarget ∧
        sourceTarget.UnfoldingEquivalent
          ((schema.withRoot child).instantiate arguments) ∧
        canonicalTarget.UnfoldingEquivalent
          ((schema.withRoot child).instantiate arguments) := by
  obtain ⟨stem, suffix, sourceTarget, hword, ⟨step⟩⟩ :=
    hsinks.exists_sinkingStep_prefix
  obtain ⟨stemActions, sinkRemainderActions,
      hsinkingActions, hstem, _hsuffix⟩ :=
    List.map_eq_append_iff.mp hword
  have hstemNonempty : stemActions ≠ [] := by
    intro hnil
    subst stemActions
    simp at hstem
    exact step.word_nonempty hstem
  rcases hwitness.2 schema.root hwitness.1 with
    hvariable | happlication
  · obtain ⟨x, hrootVariableNode, _hx⟩ := hvariable
    have hrootVariable :
        schema.rootNode? = some (.inl x) := by
      simpa [RegularTerm.rootNode?] using hrootVariableNode
    have hprotectedNonempty :
        sinkingActions ++ restActions ≠ [] := by
      rw [hsinkingActions]
      simp [hstemNonempty]
    exfalso
    exact hnoVariable [] (sinkingActions ++ restActions)
      (by simp) hprotectedNonempty schema x
      (by simp [runActions?])
      (unfoldingEquivalent_variableTerm_of_rootNode?
        hrootVariable)
  · obtain ⟨X, children, hrootNode, _hchildrenSupport⟩ :=
      happlication
    have hrootApplication :
        schema.rootApplication? = some (X, children) := by
      simp [RegularTerm.rootApplication?,
        RegularTerm.rootNode?, hrootNode]
    have hsourceInstance :
        source.UnfoldingEquivalent
          (schema.instantiate arguments) :=
      hsourceCanonical.trans hcanonicalSchema
    obtain ⟨instanceSubterm, hinstanceSubterm,
        hsubtermMatches⟩ :=
      hsourceInstance.exists_subtermAtDepth_one step.subterm_at
    obtain ⟨instanceIndex, hinstanceDescendant, rfl⟩ :=
      hinstanceSubterm
    cases hinstanceDescendant with
    | @child _ parent Y instanceChildren child
        hparent hinstanceNode hinstanceChild =>
        cases hparent
        have hinstanceRoot :=
          RegularTerm.instantiate_rootApplication?
            (arguments := arguments) hschemaClosed hrootApplication
        have hinstanceRootNode :=
          RegularTerm.nodeAt?_root_of_rootApplication? hinstanceRoot
        have happlications :
            (Y, instanceChildren) =
              (X, children.map
                (schema.resolveRHSRef arguments)) := by
          exact Sum.inr.inj
            (Option.some.inj
              (hinstanceNode.symm.trans hinstanceRootNode))
        have hinstanceChildren :
            instanceChildren =
              children.map
                (schema.resolveRHSRef arguments) :=
          congrArg Prod.snd happlications
        subst instanceChildren
        obtain ⟨schemaChild, hschemaChild, hresolved⟩ :=
          List.mem_map.mp hinstanceChild
        have hinstanceChildEq :
            (schema.instantiate arguments).withRoot instanceIndex =
              (schema.withRoot schemaChild).instantiate
                arguments := by
          rw [← hresolved]
          exact schema.instantiate_withRoot
            arguments schemaChild
        rw [hinstanceChildEq] at hsubtermMatches
        have hsourceTargetChild :
            sourceTarget.UnfoldingEquivalent
              ((schema.withRoot schemaChild).instantiate
                arguments) :=
          step.target_matches.trans hsubtermMatches
        obtain ⟨canonicalTarget, hcanonicalRun,
            hcanonicalTargetSource⟩ :=
          exists_run_of_unfoldingEquivalent hg
            hsourceCanonical.symm
            (RegularTerm.referenceClosed_of_ground
              hcanonicalGround)
            (RegularTerm.referenceClosed_of_ground
              hsourceGround)
            step.run
        have hfirst :
            schema.DescendantAt 1 schemaChild :=
          .child .root hrootNode hschemaChild
        refine ⟨stemActions, sinkRemainderActions,
          sourceTarget, canonicalTarget, schemaChild,
          hsinkingActions, hstemNonempty, hfirst, ?_, ?_,
          hcanonicalTargetSource, hsourceTargetChild,
          hcanonicalTargetSource.trans hsourceTargetChild⟩
        · simpa [runActions?, hstem] using step.run
        · simpa [runActions?, hstem] using hcanonicalRun

end EncodedFirstOrderGrammar

end DCFEquivalence
