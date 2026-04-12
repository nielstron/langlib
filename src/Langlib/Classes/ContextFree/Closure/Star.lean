import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.ContextFree.Definition
import Langlib.Utilities.ClosurePredicates

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

/-- The class of context-free languages is closed under Kleene star. -/
theorem CF_closedUnderKleeneStar : ClosedUnderKleeneStar (CF : Set (Language T)) :=
  CF_of_star_CF
