module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinkingBoundary

@[expose]
public section

/-!
# Aligning one concrete sinking step with a schema child

The `M₂` growth argument does not charge a bounded residual-growth increment
when the short branch sinks.  Instead it discards the surrounding schema
context and continues from the selected immediate schema child.  This file
keeps the consumed concrete prefix aligned with that child.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A concrete sinking prefix from an instance either starts at a schema
variable, hence has already reached one of the active arguments, or reaches
an instance of an immediate schema child.  In the child branch the exact
consumed prefix and its canonical endpoint are retained for recursive
continuation. -/
public theorem SinksBy.exists_canonicalArgumentRootHit_or_schemaChild
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema canonical source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {support : List ℕ} {word : List (Label Action)}
    (hwitness : schema.PrefixWitness width support)
    (hschemaClosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    (hcanonicalGround : canonical.Ground g.ranks)
    (hsourceGround : source.Ground g.ranks)
    (hcanonicalSchema :
      canonical.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hsourceCanonical : source.UnfoldingEquivalent canonical)
    (hsinks : g.SinksBy source word) :
    (∃ x,
      schema.rootNode? = some (.inl x) ∧
        Nonempty (CanonicalArgumentHitBy
          g canonical arguments width word)) ∨
      ∃ stem suffix target child,
        word = stem ++ suffix ∧
          stem ≠ [] ∧
          schema.DescendantAt 1 child ∧
          g.run? stem canonical = some target ∧
          target.UnfoldingEquivalent
            ((schema.withRoot child).instantiate arguments) := by
  obtain ⟨stem, suffix, target, hword, ⟨step⟩⟩ :=
    hsinks.exists_sinkingStep_prefix
  rcases hwitness.2 schema.root hwitness.1 with
    hvariable | happlication
  · obtain ⟨x, hrootVariableNode, hx⟩ := hvariable
    have hxArguments : x < arguments.length :=
      hx.trans_le hwidth
    let argument := arguments[x]
    have hargument :
        arguments[x]? = some argument :=
      List.getElem?_eq_getElem hxArguments
    have hinstanceArgument :
        (schema.instantiate arguments).UnfoldingEquivalent
          argument := by
      exact RegularTerm.instantiate_unfoldingEquivalent_argument
        hrootVariableNode hargument
        (RegularTerm.referenceClosed_of_ground
          (hargumentsGround argument
            (List.mem_of_getElem? hargument)))
    have hrootVariable :
        schema.rootNode? = some (.inl x) := by
      simpa [RegularTerm.rootNode?] using hrootVariableNode
    exact Or.inl ⟨x, hrootVariable, ⟨
      { initialSegment := []
        remainder := word
        word_eq := by simp
        index := x
        index_lt := hx
        argument := argument
        argument_at := hargument
        target := canonical
        run := rfl
        target_matches :=
          hcanonicalSchema.trans hinstanceArgument }⟩⟩
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
        have htargetChild :
            target.UnfoldingEquivalent
              ((schema.withRoot schemaChild).instantiate
                arguments) :=
          step.target_matches.trans hsubtermMatches
        obtain ⟨canonicalNext, hcanonicalRun,
            hcanonicalNextTarget⟩ :=
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
        exact Or.inr ⟨stem, suffix, canonicalNext, schemaChild,
          hword, step.word_nonempty, hfirst, hcanonicalRun,
          hcanonicalNextTarget.trans htargetChild⟩

/-- Compatibility form which forgets the root-variable and strict-progress
facts retained by
`SinksBy.exists_canonicalArgumentRootHit_or_schemaChild`. -/
public theorem SinksBy.exists_canonicalArgumentHit_or_schemaChild
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema canonical source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {support : List ℕ} {word : List (Label Action)}
    (hwitness : schema.PrefixWitness width support)
    (hschemaClosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    (hcanonicalGround : canonical.Ground g.ranks)
    (hsourceGround : source.Ground g.ranks)
    (hcanonicalSchema :
      canonical.UnfoldingEquivalent
        (schema.instantiate arguments))
    (hsourceCanonical : source.UnfoldingEquivalent canonical)
    (hsinks : g.SinksBy source word) :
    Nonempty (CanonicalArgumentHitBy
      g canonical arguments width word) ∨
      ∃ stem suffix target child,
        word = stem ++ suffix ∧
          schema.DescendantAt 1 child ∧
          g.run? stem canonical = some target ∧
          target.UnfoldingEquivalent
            ((schema.withRoot child).instantiate arguments) := by
  rcases hsinks.exists_canonicalArgumentRootHit_or_schemaChild
      hg hwitness hschemaClosed hwidth hargumentsGround
      hcanonicalGround hsourceGround hcanonicalSchema
      hsourceCanonical with hargument | hchild
  · obtain ⟨_x, _hroot, hit⟩ := hargument
    exact Or.inl hit
  · obtain ⟨stem, suffix, target, child, hword, _hnonempty,
      hdescendant, hrun, hmatches⟩ := hchild
    exact Or.inr ⟨stem, suffix, target, child,
      hword, hdescendant, hrun, hmatches⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
