import Grammars.Classes.ContextFree.ClosureProperties.Substitution

/-! # Context-Free Closure Under Kleene Star

This file derives closure under Kleene star from closure under substitution.

## Main declarations

- `CF_of_star_CF`
-/

variable {T : Type}

/-- The class of context-free languages is closed under Kleene star. -/
theorem CF_of_star_CF (L : Language T) :
    is_CF L → is_CF (KStar.kstar L) := by
  intro h
  rw [is_CF_iff_isContextFree]
  exact Language.IsContextFree.kstar ((is_CF_iff_isContextFree).mp h)
