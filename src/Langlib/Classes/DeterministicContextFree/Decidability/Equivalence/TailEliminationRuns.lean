module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveExposure
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.UnaryFixedPointUniqueness

@[expose]
public section

/-!
# Concrete certificate step for eliminating one active tail

This module packages the operational heart of width reduction.  A shorter
derived equation `focus = H(focus)` is used twice by the certificate limit
rule, replacing the selected argument in both components of a later pair.
The resulting concrete terms are related to the bounded same-arity schemas
obtained by parametrically tying `H`.
-/

namespace DCFEquivalence

namespace RegularTerm

private theorem list_sum_le_length_mul
    (values : List ℕ) (bound : ℕ)
    (hbound : ∀ value ∈ values, value ≤ bound) :
    values.sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.sum_cons, List.length_cons]
      have hhead := hbound value (by simp)
      have htail := ih (fun tail htail => hbound tail (by simp [htail]))
      rw [Nat.succ_mul]
      simpa [Nat.add_comm] using Nat.add_le_add htail hhead

/-- Substitute the same-arity tied solution of `replacement` into `outer`. -/
@[expose] public def tieInto
    (outer replacement : RegularTerm) (arity x : ℕ) : RegularTerm :=
  outer.instantiate (replacement.tieArguments arity x)

public theorem tieInto_wellFormed
    {ranks : List ℕ} {outer replacement : RegularTerm}
    {arity x : ℕ}
    (houter : outer.WellFormed ranks arity)
    (hreplacement : replacement.WellFormed ranks arity)
    (hx : x < arity) :
    (tieInto outer replacement arity x).WellFormed ranks arity := by
  have hresult := instantiate_wellFormed_max
    (arguments := replacement.tieArguments arity x)
    (variableBound := arity)
    (by simpa using houter)
    (tieArguments_wellFormed hreplacement hx)
  simpa [tieInto] using hresult

/-- Every component of a tying substitution is either a one-node identity
variable or the tied replacement graph itself. -/
public theorem tieArguments_nodeSize_le
    (replacement : RegularTerm) {arity x : ℕ}
    (hx : x < arity) :
    ∀ argument ∈ replacement.tieArguments arity x,
      argument.nodes.length ≤ replacement.nodes.length + 1 := by
  intro argument hargument
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hargument
  have hiArity : i < arity := by
    have hilength := (List.getElem?_eq_some_iff.mp hi).choose
    simpa using hilength
  by_cases hix : i = x
  · subst i
    rw [tieArguments_getElem?_eq hx] at hi
    cases Option.some.inj hi
    simp
  · have hslot := tieArguments_getElem?_ne
        (context := replacement) hiArity (fun hxi => hix hxi.symm)
    rw [hslot] at hi
    cases Option.some.inj hi
    simp

/-- Coarse uniform graph-size bound for a schema after tying in a
replacement. -/
public theorem tieInto_nodes_length_le
    (outer replacement : RegularTerm) {arity x : ℕ}
    (hx : x < arity) :
    (tieInto outer replacement arity x).nodes.length ≤
      outer.nodes.length + arity * (replacement.nodes.length + 1) := by
  rw [tieInto, instantiate_nodes_length]
  apply Nat.add_le_add_left
  have hsum := list_sum_le_length_mul
    ((replacement.tieArguments arity x).map
      fun argument => argument.nodes.length)
    (replacement.nodes.length + 1)
    (by
      intro size hsize
      obtain ⟨argument, hargument, rfl⟩ := List.mem_map.mp hsize
      exact tieArguments_nodeSize_le replacement hx argument hargument)
  simpa using hsum

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Output of one two-sided certificate tail replacement, including its
bounded parametric schema presentation. -/
public structure TailEliminatedPair
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (basis : List BasisPair) (word : List (Label Action))
    (leftSchema rightSchema replacement : RegularTerm)
    (arguments : List RegularTerm) (x : ℕ) where
  leftTarget : RegularTerm
  rightTarget : RegularTerm
  derivation : CertificateDerivable g initialLeft initialRight basis
    (.pair word leftTarget rightTarget)
  left_schema_wellFormed :
    (RegularTerm.tieInto leftSchema replacement arguments.length x)
      |>.WellFormed g.ranks arguments.length
  right_schema_wellFormed :
    (RegularTerm.tieInto rightSchema replacement arguments.length x)
      |>.WellFormed g.ranks arguments.length
  left_matches : leftTarget.UnfoldingEquivalent
    ((RegularTerm.tieInto leftSchema replacement arguments.length x)
      |>.instantiate arguments)
  right_matches : rightTarget.UnfoldingEquivalent
    ((RegularTerm.tieInto rightSchema replacement arguments.length x)
      |>.instantiate arguments)

/-- Apply the concrete limit rule on both sides and identify its result with
the corresponding parametric tied schemas. -/
public theorem exists_tailEliminatedPair
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word shorterWord : List (Label Action)}
    {left right shorterLeft shorterRight : RegularTerm}
    {leftSchema rightSchema replacement : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ}
    (houter : CertificateDerivable g initialLeft initialRight basis
      (.pair word left right))
    (hshorter : CertificateDerivable g initialLeft initialRight basis
      (.pair shorterWord shorterLeft shorterRight))
    (hleftSchema : leftSchema.WellFormed g.ranks arguments.length)
    (hrightSchema : rightSchema.WellFormed g.ranks arguments.length)
    (hreplacement : replacement.WellFormed g.ranks arguments.length)
    (hx : x < arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (hreplacementNonvariable :
      ¬replacement.UnfoldingEquivalent (RegularTerm.variableTerm x))
    (hlength : shorterWord.length < word.length)
    (hleftMatch : left.UnfoldingEquivalent
      (leftSchema.instantiate arguments))
    (hrightMatch : right.UnfoldingEquivalent
      (rightSchema.instantiate arguments))
    (hshorterLeft : shorterLeft.UnfoldingEquivalent arguments[x])
    (hshorterRight : shorterRight.UnfoldingEquivalent
      (replacement.instantiate arguments)) :
    Nonempty (TailEliminatedPair g initialLeft initialRight basis word
      leftSchema rightSchema replacement arguments x) := by
  let focus := arguments[x]
  let leftContext := RegularTerm.unarySpecialization
    leftSchema arguments x
  let rightContext := RegularTerm.unarySpecialization
    rightSchema arguments x
  let replacementContext := RegularTerm.unarySpecialization
    replacement arguments x
  let replacementLimit := replacementContext.unaryLimit
  let tiedInstance := (replacement.tieVariable x).instantiate arguments
  let leftTarget := leftContext.instantiate [replacementLimit]
  let rightTarget := rightContext.instantiate [replacementLimit]
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (harguments argument hargument)
  have hfocusGround : focus.Ground g.ranks := by
    exact harguments arguments[x] (List.getElem_mem hx)
  have hleftContext : leftContext.WellFormed g.ranks 1 :=
    RegularTerm.unarySpecialization_wellFormed hleftSchema harguments
  have hrightContext : rightContext.WellFormed g.ranks 1 :=
    RegularTerm.unarySpecialization_wellFormed hrightSchema harguments
  have hreplacementContext : replacementContext.WellFormed g.ranks 1 :=
    RegularTerm.unarySpecialization_wellFormed hreplacement harguments
  have hnontrivial : replacementContext.nontrivialUnaryCode = true :=
    RegularTerm.unarySpecialization_nontrivial_of_schema_not_variable
      hreplacement hx harguments hreplacementNonvariable
  have hlimitGround : replacementLimit.Ground g.ranks :=
    RegularTerm.unaryLimit_ground hreplacementContext hnontrivial
  have hleftTargetGround : leftTarget.Ground g.ranks :=
    RegularTerm.instantiate_singleton_ground hleftContext hlimitGround
  have hrightTargetGround : rightTarget.Ground g.ranks :=
    RegularTerm.instantiate_singleton_ground hrightContext hlimitGround
  have houterGround := groundPairCode_of_pair_derivable houter
  unfold groundPairCode at houterGround
  rw [Bool.and_eq_true] at houterGround
  have hrightGround : right.Ground g.ranks :=
    (RegularTerm.groundCode_eq_true_iff g.ranks right).mp houterGround.2
  have hfirstGround : g.groundPairCode leftTarget right = true := by
    unfold groundPairCode
    rw [Bool.and_eq_true]
    exact ⟨(RegularTerm.groundCode_eq_true_iff g.ranks leftTarget).mpr
        hleftTargetGround,
      (RegularTerm.groundCode_eq_true_iff g.ranks right).mpr hrightGround⟩
  have hsecondGround : g.groundPairCode rightTarget leftTarget = true := by
    unfold groundPairCode
    rw [Bool.and_eq_true]
    exact ⟨(RegularTerm.groundCode_eq_true_iff g.ranks rightTarget).mpr
        hrightTargetGround,
      (RegularTerm.groundCode_eq_true_iff g.ranks leftTarget).mpr
        hleftTargetGround⟩
  have hleftAtFocus : (leftContext.instantiate [focus]).UnfoldingEquivalent
      (leftSchema.instantiate arguments) := by
    simpa [leftContext, focus] using
      (RegularTerm.unarySpecialization_instantiate_unfoldingEquivalent
        hleftSchema hx harguments)
  have hrightAtFocus :
      (rightContext.instantiate [focus]).UnfoldingEquivalent
        (rightSchema.instantiate arguments) := by
    simpa [rightContext, focus] using
      (RegularTerm.unarySpecialization_instantiate_unfoldingEquivalent
        hrightSchema hx harguments)
  have hreplacementAtFocus :
      (replacementContext.instantiate [focus]).UnfoldingEquivalent
        (replacement.instantiate arguments) := by
    simpa [replacementContext, focus] using
      (RegularTerm.unarySpecialization_instantiate_unfoldingEquivalent
        hreplacement hx harguments)
  have hderivation : CertificateDerivable g initialLeft initialRight basis
      (.pair word leftTarget rightTarget) := by
    apply houter.limit_both hshorter
      (hleftContext := hleftContext)
      (hrightContext := hrightContext)
      (hreplacementContext := hreplacementContext)
      (hfocus := (RegularTerm.groundCode_eq_true_iff g.ranks focus).mpr
        hfocusGround)
      (hnontrivial := hnontrivial)
      (hlength := hlength)
      (hleftMatch := (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        (hleftMatch.trans hleftAtFocus.symm))
      (hrightMatch := (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        (hrightMatch.trans hrightAtFocus.symm))
      (hshorterLeft :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (by simpa [focus] using hshorterLeft))
      (hshorterRight :=
        (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
          (hshorterRight.trans hreplacementAtFocus.symm))
      (hleftGround := hfirstGround)
      (hrightGround := hsecondGround)
  have hbridge : replacementLimit.UnfoldingEquivalent tiedInstance := by
    simpa [replacementContext, replacementLimit, tiedInstance] using
      (RegularTerm.unarySpecialization_unaryLimit_unfoldingEquivalent_tiedInstance
        hreplacement hx harguments hreplacementNonvariable)
  have htiedClosed : tiedInstance.ReferenceClosed := by
    apply RegularTerm.instantiate_referenceClosed
    · exact RegularTerm.tieVariable_referenceClosed
        (RegularTerm.referenceClosed_of_wellFormed hreplacement) x
    · exact hargumentsClosed
  have hlimitClosed := RegularTerm.referenceClosed_of_ground hlimitGround
  have replacementCongruence
      (outer : RegularTerm)
      (houterSchema : outer.WellFormed g.ranks arguments.length) :
      (outer.instantiate
          (RegularTerm.replaceArgument arguments x replacementLimit))
        |>.UnfoldingEquivalent
        (outer.instantiate
          (RegularTerm.replaceArgument arguments x tiedInstance)) := by
    apply RegularTerm.instantiate_unfoldingEquivalent
      (RegularTerm.referenceClosed_of_wellFormed houterSchema)
      (RegularTerm.replaceArgument_forall₂ hx hbridge)
    · exact RegularTerm.replaceArgument_referenceClosed hx
        hargumentsClosed hlimitClosed
    · exact RegularTerm.replaceArgument_referenceClosed hx
        hargumentsClosed htiedClosed
  have hleftFill : leftTarget.UnfoldingEquivalent
      (leftSchema.instantiate
        (RegularTerm.replaceArgument arguments x replacementLimit)) := by
    simpa [leftTarget, leftContext, replacementLimit] using
      (RegularTerm.unarySpecialization_instantiate_focus
        hleftSchema hx harguments hlimitClosed)
  have hrightFill : rightTarget.UnfoldingEquivalent
      (rightSchema.instantiate
        (RegularTerm.replaceArgument arguments x replacementLimit)) := by
    simpa [rightTarget, rightContext, replacementLimit] using
      (RegularTerm.unarySpecialization_instantiate_focus
        hrightSchema hx harguments hlimitClosed)
  have hleftParametric := RegularTerm.instantiate_tieArguments_fixedInstance
    hleftSchema hreplacement hx hargumentsClosed
  have hrightParametric := RegularTerm.instantiate_tieArguments_fixedInstance
    hrightSchema hreplacement hx hargumentsClosed
  refine ⟨
    { leftTarget := leftTarget
      rightTarget := rightTarget
      derivation := hderivation
      left_schema_wellFormed := RegularTerm.tieInto_wellFormed
        hleftSchema hreplacement hx
      right_schema_wellFormed := RegularTerm.tieInto_wellFormed
        hrightSchema hreplacement hx
      left_matches := ?_
      right_matches := ?_ }⟩
  · exact hleftFill.trans
      ((replacementCongruence leftSchema hleftSchema).trans
        (by simpa [RegularTerm.tieInto] using hleftParametric.symm))
  · exact hrightFill.trans
      ((replacementCongruence rightSchema hrightSchema).trans
        (by simpa [RegularTerm.tieInto] using hrightParametric.symm))

end EncodedFirstOrderGrammar

end DCFEquivalence
