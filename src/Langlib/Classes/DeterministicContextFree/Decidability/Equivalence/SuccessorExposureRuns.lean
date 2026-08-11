module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingResultCore

@[expose]
public section

/-!
# Exposing immediate successors in ground instances

An exposing word for a formal successor of a ranked symbol reaches the
corresponding concrete child in every ground instance.  Finite trace agreement
then forces a balancing pivot to execute that same shorter word.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A formal successor-exposing word reaches the corresponding immediate
child of every ground instance of the symbol. -/
public theorem exists_runActions_to_child_of_exposesSuccessor
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (position : g.SuccessorPosition) {word : List Action}
    (hexposes : g.ExposesSuccessor position word)
    {term : RegularTerm} (hground : term.Ground g.ranks)
    {children : List ℕ} {child : ℕ}
    (hroot :
      term.rootApplication? = some (position.1.val, children))
    (hchild : children[position.2.val]? = some child) :
    ∃ target,
      g.runActions? word term = some target ∧
      target.UnfoldingEquivalent
        (term.withRoot child) := by
  obtain ⟨schemaTarget, hschemaRun, hschemaVariable⟩ := hexposes
  have hchildrenLength :
      children.length = g.ranks.get position.1 := by
    have hrank := hground.root_rank_arity hroot
    exact Option.some.inj (hrank.symm.trans (by simp))
  let arguments := children.map term.withRoot
  have hargumentsLength :
      arguments.length = g.ranks.get position.1 := by
    simp [arguments, hchildrenLength]
  have htermClosed :=
    RegularTerm.referenceClosed_of_ground hground
  have hchildrenBound :=
    RegularTerm.rootApplication_children_lt htermClosed hroot
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    obtain ⟨child, hchild, rfl⟩ :=
      List.mem_map.mp hargument
    exact RegularTerm.withRoot_referenceClosed htermClosed
      (hchildrenBound child hchild)
  have htemplateWellFormed :
      (RegularTerm.symbolTemplate position.1
        (g.ranks.get position.1)).WellFormed g.ranks
          (g.ranks.get position.1) := by
    apply RegularTerm.symbolTemplate_wellFormed
    simp
  obtain ⟨templateConcrete, htemplateConcreteRun,
      htargetInstance⟩ :=
    g.runActions?_instantiate hg word htemplateWellFormed
      hargumentsClosed hschemaRun
  have htemplateInstance :
      ((RegularTerm.symbolTemplate position.1
          (g.ranks.get position.1)).instantiate arguments)
        |>.UnfoldingEquivalent term := by
    simpa [arguments, hchildrenLength] using
      RegularTerm.symbolTemplate_instantiate_unfoldingEquivalent
        htermClosed hroot
  have htemplateInstanceClosed :
      ((RegularTerm.symbolTemplate position.1
          (g.ranks.get position.1)).instantiate arguments)
        |>.ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed
        htemplateWellFormed)
      hargumentsClosed
  obtain ⟨target, htargetRun, htargetTemplate⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      htemplateInstance.symm htermClosed
      htemplateInstanceClosed htemplateConcreteRun
  exact ⟨target, htargetRun, by
    have hargument :
        arguments[position.2]? =
          some (term.withRoot child) := by
      simp [arguments, hchild]
    have hschemaRoot :
        schemaTarget.rootNode? =
          some (.inl position.2) :=
      rootNode?_variable_of_unfoldingEquivalent
        hschemaVariable.symm
        (RegularTerm.variableTerm_rootNode? position.2)
    have hschemaNode :
        schemaTarget.nodeAt? schemaTarget.root =
          some (.inl position.2) := by
      simpa [RegularTerm.rootNode?] using hschemaRoot
    have hinstanceChild :=
      RegularTerm.instantiate_unfoldingEquivalent_argument
        hschemaNode hargument
        (RegularTerm.withRoot_referenceClosed htermClosed
          (hchildrenBound child
            (List.mem_of_getElem? hchild)))
    exact htargetTemplate.trans
      (htargetInstance.symm.trans hinstanceChild)⟩

/-- A shorter successor-exposing word runs both sides of a balancing segment,
reaching the concrete child on the active side. -/
public theorem BalancingSegment.exists_pivotTarget_for_exposedSuccessor
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {active pivot : RegularTerm}
    {segmentWord : List (Label Action)}
    (segment : BalancingSegment g bound active pivot segmentWord)
    (hactive : active.Ground g.ranks)
    (position : g.SuccessorPosition) {word : List Action}
    (hexposes : g.ExposesSuccessor position word)
    (hshort : word.length < bound)
    {children : List ℕ} {child : ℕ}
    (hroot :
      active.rootApplication? = some (position.1.val, children))
    (hchild : children[position.2.val]? = some child) :
    ∃ activeTarget pivotTarget,
      g.runActions? word active = some activeTarget ∧
      activeTarget.UnfoldingEquivalent (active.withRoot child) ∧
      g.runActions? word pivot = some pivotTarget := by
  obtain ⟨activeTarget, hactiveRun, hactiveChild⟩ :=
    exists_runActions_to_child_of_exposesSuccessor
      hg position hexposes hactive hroot hchild
  have hactiveTrace :
      g.IsTrace active (word.map Sum.inl) := by
    unfold IsTrace
    unfold runActions? at hactiveRun
    rw [hactiveRun]
    rfl
  have hsame :=
    (g.traceApprox_iff_sameTracesThrough
      bound active pivot).mp segment.agreement
      (word.map Sum.inl) (by
        simpa using Nat.le_of_lt hshort)
  have hpivotTrace : g.IsTrace pivot (word.map Sum.inl) :=
    hsame.mp hactiveTrace
  obtain ⟨pivotTarget, hpivotRun⟩ :=
    g.isTrace_iff_exists_executes.mp hpivotTrace
  exact ⟨activeTarget, pivotTarget, hactiveRun,
    hactiveChild, by simpa [runActions?] using hpivotRun⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
