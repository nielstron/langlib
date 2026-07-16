module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GrammarNormalForm

@[expose]
public section

/-!
# Syntactic root-sinking witnesses

The semantic statement that a concrete residual happens to equal an
immediate subterm is not stable under changing the surrounding arguments.
`RootSinkingStep` instead retains an actual open run from the current root
symbol template to one of its formal parameters.  This lightweight module
contains only the witness and transport operations needed below balancing;
replay on arbitrary schemas is developed later in `RootSinking`.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One nonempty ordinary open run from `X(x₀,…,xₙ₋₁)` to the literal
parameter `xᵢ`. -/
public structure RootSinkingStep
    (g : EncodedFirstOrderGrammar Action)
    (rootSymbol rank : ℕ) (actions : List Action) where
  child : Fin rank
  target : RegularTerm
  actions_nonempty : actions ≠ []
  run :
    g.runActions? actions
      (RegularTerm.symbolTemplate rootSymbol rank) = some target
  target_root :
    target.rootNode? = some (.inl child.val)

/-- A word root-sinks from `source` when an ordinary prefix is induced by an
open root-sinking step for the actual root symbol of `source`. -/
@[expose] public def RootSinksBy
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action)) : Prop :=
  ∃ rootSymbol children actions suffix,
    source.rootApplication? = some (rootSymbol, children) ∧
      word = actions.map Sum.inl ++ suffix ∧
      Nonempty (RootSinkingStep
        g rootSymbol children.length actions)

/-- An open residual unfolding-equivalent to a variable has that variable at
its reachable root. -/
private theorem rootNode?_variable_of_equivalent_variable
    {left : RegularTerm} {x : ℕ}
    (hequivalent :
      left.UnfoldingEquivalent (RegularTerm.variableTerm x)) :
    left.rootNode? = some (.inl x) := by
  obtain ⟨relation, hroot, hbisimulation⟩ := hequivalent
  have hcompatible := hbisimulation left.root
    (RegularTerm.variableTerm x).root hroot
  unfold RegularTerm.NodeCompatible at hcompatible
  change RegularTerm.RawCompatible relation left.rootNode?
    (RegularTerm.variableTerm x).rootNode? at hcompatible
  rw [RegularTerm.variableTerm_rootNode?] at hcompatible
  cases hleft : left.rootNode? with
  | none =>
      rw [hleft] at hcompatible
      simp [RegularTerm.RawCompatible] at hcompatible
  | some node =>
      rw [hleft] at hcompatible
      cases node with
      | inr application =>
          simp [RegularTerm.RawCompatible] at hcompatible
      | inl y =>
          have hy : y = x := by
            simpa [RegularTerm.RawCompatible] using hcompatible
          subst y
          simpa using hleft

/-- Every ordinary successor-exposing witness is a syntactic root-sinking
step. -/
public theorem RootSinkingStep.of_exposesSuccessor
    {g : EncodedFirstOrderGrammar Action}
    (position : g.SuccessorPosition) {actions : List Action}
    (hactions : actions ≠ [])
    (hexposes : g.ExposesSuccessor position actions) :
    Nonempty (RootSinkingStep g position.1
      (g.ranks.get position.1) actions) := by
  obtain ⟨target, hrun, htarget⟩ := hexposes
  exact ⟨
    { child := position.2
      target := target
      actions_nonempty := hactions
      run := hrun
      target_root :=
        rootNode?_variable_of_equivalent_variable htarget }⟩

/-- Appending unused input preserves a syntactic root-sinking witness. -/
public theorem RootSinksBy.append
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    (hsinks : g.RootSinksBy source word)
    (suffix : List (Label Action)) :
    g.RootSinksBy source (word ++ suffix) := by
  obtain ⟨rootSymbol, children, actions, remainder,
      hroot, hword, hstep⟩ := hsinks
  exact ⟨rootSymbol, children, actions, remainder ++ suffix,
    hroot, by rw [hword, List.append_assoc], hstep⟩

/-- Root sinking always consumes a nonempty word prefix. -/
public theorem not_rootSinksBy_nil
    (g : EncodedFirstOrderGrammar Action) (source : RegularTerm) :
    ¬g.RootSinksBy source [] := by
  rintro ⟨_rootSymbol, _children, actions, suffix,
    _hroot, hword, ⟨step⟩⟩
  have hwordLength := congrArg List.length hword
  have hlength : actions.length = 0 := by
    simp only [List.length_nil, List.length_append, List.length_map]
      at hwordLength
    omega
  exact step.actions_nonempty
    (List.length_eq_zero_iff.mp hlength)

/-- The root-syntactic witness is independent of the concrete children. -/
public theorem RootSinksBy.retarget
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {word : List (Label Action)}
    {rootSymbol : ℕ} {sourceChildren targetChildren : List ℕ}
    (hsinks : g.RootSinksBy source word)
    (hsource :
      source.rootApplication? =
        some (rootSymbol, sourceChildren))
    (htarget :
      target.rootApplication? =
        some (rootSymbol, targetChildren))
    (hlength :
      targetChildren.length = sourceChildren.length) :
    g.RootSinksBy target word := by
  obtain ⟨witnessSymbol, witnessChildren, actions, suffix,
      hwitnessRoot, hword, hstep⟩ := hsinks
  have hwitness :
      (witnessSymbol, witnessChildren) =
        (rootSymbol, sourceChildren) :=
    Option.some.inj (hwitnessRoot.symm.trans hsource)
  have hsymbol : witnessSymbol = rootSymbol :=
    congrArg Prod.fst hwitness
  have hchildren : witnessChildren = sourceChildren :=
    congrArg Prod.snd hwitness
  subst witnessSymbol
  subst witnessChildren
  have hstep' :
      Nonempty (RootSinkingStep
        g rootSymbol targetChildren.length actions) := by
    simpa [hlength] using hstep
  exact ⟨rootSymbol, targetChildren, actions, suffix,
    htarget, hword, hstep'⟩

/-- Root sinking transports across unfolding equivalence because equivalent
application roots have the same symbol and the same number of children. -/
public theorem RootSinksBy.of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {word : List (Label Action)}
    (hsinks : g.RootSinksBy source word)
    (hequivalent : source.UnfoldingEquivalent target) :
    g.RootSinksBy target word := by
  have hsinks' := hsinks
  obtain ⟨rootSymbol, sourceChildren, _actions, _suffix,
      hsource, _hword, _hstep⟩ := hsinks
  obtain ⟨targetChildren, htarget, hchildren⟩ :=
    RegularTerm.rootApplication?_of_unfoldingEquivalent
      hequivalent hsource
  exact RootSinksBy.retarget hsinks' hsource htarget
    hchildren.length_eq.symm

end EncodedFirstOrderGrammar

end DCFEquivalence
