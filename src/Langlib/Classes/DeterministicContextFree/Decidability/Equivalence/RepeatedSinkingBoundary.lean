module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteUnfoldingDepth
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinking

@[expose]
public section

/-!
# Reflecting a repeated-sinking spine through a finite schema

Repeated sinking selects one concrete unfolding edge at a time.  When the
source is semantically an instance of a finite open schema, a spine longer
than the schema's whole unfolding depth must cross a schema variable.  This
file keeps the operational prefixes aligned while descending, so the crossing
is witnessed by an actual run of the canonical instance to the selected
argument.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- A prefix witness remains valid after changing the distinguished root to a
supported child. -/
public theorem PrefixWitness.withRoot
    {term : RegularTerm} {width : ℕ} {support : List ℕ}
    (hwitness : term.PrefixWitness width support)
    {child : ℕ} (hchild : child ∈ support) :
    (term.withRoot child).PrefixWitness width support := by
  refine ⟨hchild, ?_⟩
  intro i hi
  simpa [withRoot, nodeAt?, nodes] using hwitness.2 i hi

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A prefix of `word` executed by one canonical instance reaches one of its
active substitution arguments. -/
public structure CanonicalArgumentHitBy
    (g : EncodedFirstOrderGrammar Action)
    (canonical : RegularTerm) (arguments : List RegularTerm)
    (width : ℕ) (word : List (Label Action)) where
  initialSegment : List (Label Action)
  remainder : List (Label Action)
  word_eq : word = initialSegment ++ remainder
  index : ℕ
  index_lt : index < width
  argument : RegularTerm
  argument_at : arguments[index]? = some argument
  target : RegularTerm
  run : g.run? initialSegment canonical = some target
  target_matches : target.UnfoldingEquivalent argument

/-- Before using finiteness, repeated sinking either reaches an active
argument or reflects to a schema-side descendant of the same depth. -/
public theorem repeatedlySinksBy_argumentHit_or_schemaDescendant
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema canonical source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {support : List ℕ} {word : List (Label Action)} {depth : ℕ}
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
    (hsinks : g.RepeatedlySinksBy source word depth) :
    Nonempty (CanonicalArgumentHitBy
      g canonical arguments width word) ∨
      ∃ index, schema.DescendantAt depth index := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  induction depth generalizing schema canonical source support word with
  | zero =>
      exact Or.inr ⟨schema.root, .root⟩
  | succ depth ih =>
      obtain ⟨stem, suffix, target, hword, ⟨step⟩, hrest⟩ :=
        hsinks
      rcases hwitness.2 schema.root hwitness.1 with
        hvariable | happlication
      · obtain ⟨x, hrootVariable, hx⟩ := hvariable
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
            hrootVariable hargument
            (RegularTerm.referenceClosed_of_ground
              (hargumentsGround argument
                (List.mem_of_getElem? hargument)))
        exact Or.inl ⟨
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
              hcanonicalSchema.trans hinstanceArgument }⟩
      · obtain ⟨X, children, hrootNode, hchildrenSupport⟩ :=
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
            have hchildBound : schemaChild < schema.nodes.length :=
              hschemaClosed.2 schema.root X children hrootNode
                schemaChild hschemaChild
            have hchildClosed :
                (schema.withRoot schemaChild).ReferenceClosed :=
              RegularTerm.withRoot_referenceClosed
                hschemaClosed hchildBound
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
                    arguments) := by
              exact step.target_matches.trans hsubtermMatches
            obtain ⟨canonicalNext, hcanonicalRun,
                hcanonicalNextTarget⟩ :=
              exists_run_of_unfoldingEquivalent hg
                hsourceCanonical.symm
                (RegularTerm.referenceClosed_of_ground
                  hcanonicalGround)
                (RegularTerm.referenceClosed_of_ground
                  hsourceGround)
                step.run
            have htargetGround :
                target.Ground g.ranks :=
              hgroundSteps.ground_of_run hsourceGround step.run
            have hcanonicalNextGround :
                canonicalNext.Ground g.ranks :=
              hgroundSteps.ground_of_run
                hcanonicalGround hcanonicalRun
            have hchildWitness :
                (schema.withRoot schemaChild)
                  |>.PrefixWitness width support :=
              hwitness.withRoot
                (hchildrenSupport schemaChild hschemaChild)
            rcases ih
                hchildWitness hchildClosed
                hcanonicalNextGround htargetGround
                (hcanonicalNextTarget.trans htargetChild)
                hcanonicalNextTarget.symm hrest with
              hhit | hschemaPath
            · obtain ⟨hit⟩ := hhit
              exact Or.inl ⟨
                { initialSegment :=
                    stem ++ hit.initialSegment
                  remainder := hit.remainder
                  word_eq := by
                    calc
                      word = stem ++ suffix := hword
                      _ = stem ++
                          (hit.initialSegment ++
                            hit.remainder) :=
                        congrArg (fun tail =>
                          stem ++ tail) hit.word_eq
                      _ = (stem ++ hit.initialSegment) ++
                          hit.remainder :=
                        (List.append_assoc _ _ _).symm
                  index := hit.index
                  index_lt := hit.index_lt
                  argument := hit.argument
                  argument_at := hit.argument_at
                  target := hit.target
                  run := by
                    rw [g.run?_append, hcanonicalRun]
                    exact hit.run
                  target_matches := hit.target_matches }⟩
            · obtain ⟨finalIndex, hchildPath⟩ :=
                hschemaPath
              have hfirst :
                  schema.DescendantAt 1 schemaChild :=
                .child .root hrootNode hschemaChild
              have hfull :
                  schema.DescendantAt (depth + 1) finalIndex := by
                have := hfirst.trans hchildPath
                simpa [Nat.add_comm] using this
              exact Or.inr ⟨finalIndex, hfull⟩

/-- A repeated-sinking spine deeper than a semantic schema-depth bound cannot
remain entirely inside that schema. -/
public theorem exists_canonicalArgumentHit_of_repeatedlySinksBy_of_depthBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema canonical source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {word : List (Label Action)} {bound depth : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hbound : schema.UnfoldingDepthAtMost bound)
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
    (hdeep : bound < depth)
    (hsinks : g.RepeatedlySinksBy source word depth) :
    Nonempty (CanonicalArgumentHitBy
      g canonical arguments width word) := by
  obtain ⟨support, hsupport⟩ := hwitness
  rcases repeatedlySinksBy_argumentHit_or_schemaDescendant
      hg hsupport hschemaClosed hwidth hargumentsGround
      hcanonicalGround hsourceGround
      hcanonicalSchema hsourceCanonical hsinks with
    hhit | hschemaPath
  · exact hhit
  · obtain ⟨index, hdescendant⟩ := hschemaPath
    exact False.elim (by
      have hle := hbound hdescendant
      omega)

/-- A repeated-sinking spine longer than a finite schema cannot remain
entirely inside that schema. -/
public theorem exists_canonicalArgumentHit_of_repeatedlySinksBy
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema canonical source : RegularTerm}
    {arguments : List RegularTerm} {width : ℕ}
    {word : List (Label Action)} {depth : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hfinite : schema.UnfoldsFinite)
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
    (hdeep : schema.nodes.length < depth)
    (hsinks : g.RepeatedlySinksBy source word depth) :
    Nonempty (CanonicalArgumentHitBy
      g canonical arguments width word) := by
  exact g.exists_canonicalArgumentHit_of_repeatedlySinksBy_of_depthBound
    hg hwitness hfinite.unfoldingDepthAtMost_nodes hschemaClosed
    hwidth hargumentsGround hcanonicalGround hsourceGround
    hcanonicalSchema hsourceCanonical hdeep hsinks

end EncodedFirstOrderGrammar

end DCFEquivalence
