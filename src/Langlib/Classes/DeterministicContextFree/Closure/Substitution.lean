module

public import Langlib.Classes.DeterministicContextFree.Closure.Union
public import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Classes.Regular.Closure.Union
public import Langlib.Classes.Regular.Inclusion.DeterministicContextFree
public import Langlib.Utilities.ClosurePredicates

/-! # Deterministic Context-Free Languages Are Not Closed Under Substitution -/

private theorem DCF_singletons_bool : is_DCF ({[false], [true]} : Language Bool) := by
  apply is_DCF_of_is_RG
  apply is_RG_of_isRegular
  convert (Language.isRegular_singleton_word [false]).add'
    (Language.isRegular_singleton_word [true]) using 1

/-- The finite-alphabet substitution closure property for deterministic context-free languages. -/
public def DCFClosedUnderSubstitution : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] (L : Language α) (f : α → Language β),
    is_DCF L → (∀ a, is_DCF (f a)) → is_DCF (L.subst f)

/-- Deterministic context-free languages are not closed under substitution. -/
public theorem DCF_notClosedUnderSubstitution :
    ¬ DCFClosedUnderSubstitution := by
  intro hsubst
  apply DCF_notClosedUnderUnion
  intro L₁ L₂ h₁ h₂
  let f : Bool → Language (Fin 3) := fun b => if b then L₂ else L₁
  have h : is_DCF (({[false], [true]} : Language Bool).subst f) := by
    exact hsubst ({[false], [true]} : Language Bool) f DCF_singletons_bool
      (fun b => by
        cases b
        · simpa [f] using h₁
        · simpa [f] using h₂)
  simpa [f] using (Language.subst_singletons_eq_add (f := f) ▸ h)
