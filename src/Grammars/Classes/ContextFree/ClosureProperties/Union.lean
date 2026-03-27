import Grammars.Classes.ContextFree.ClosureProperties.Substitution

/-! # Context-Free Closure Under Union

This file derives closure under union from closure under substitution.

## Main declarations

- `CF_of_CF_u_CF`
-/

variable {T : Type}

/-- The class of context-free languages is closed under union. -/
theorem CF_of_CF_u_CF (L₁ : Language T) (L₂ : Language T) :
    is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ + L₂) := by
  classical
  rintro ⟨h₁, h₂⟩
  let f : Bool → Language T := fun b => if b then L₂ else L₁
  have hsubst : is_CF (({[false], [true]} : Language Bool).subst f) := by
    apply CF_of_subst_CF ({[false], [true]} : Language Bool) f
    · exact (is_CF_iff_isContextFree).mpr isContextFree_pair_bool
    · intro b
      cases b with
      | false => simpa [f]
      | true => simpa [f]
  simpa [f] using (Language.subst_singletons_eq_add (f := f) ▸ hsubst)
