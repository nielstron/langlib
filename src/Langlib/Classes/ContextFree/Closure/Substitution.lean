import Langlib.Classes.ContextFree.Basics.Inclusion
import Langlib.Classes.ContextFree.Closure.Substitution.Core
import Langlib.Classes.ContextFree.Definition

/-! # Context-Free Closure Under Substitution

This file imports mathlib's proof that context-free languages are closed under substitution and
repackages it for this project's `is_CF` predicate.

## Main declarations

- `CF_of_subst_CF`
-/

variable {α β : Type}

/-- The class of context-free languages is closed under substitution. -/
theorem CF_of_subst_CF (L : Language α) (f : α → Language β) :
    is_CF L → (∀ a, is_CF (f a)) → is_CF (L.subst f) := by
  intro hL hf
  rw [is_CF_iff_isContextFree]
  exact Language.IsContextFree.subst L f
    ((is_CF_iff_isContextFree).mp hL)
    (fun a => (is_CF_iff_isContextFree).mp (hf a))
