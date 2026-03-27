import Grammars.Classes.ContextFree.Basics.Pumping
import Grammars.Classes.ContextFree.Basics.Elementary
import Grammars.Classes.ContextFree.ClosureProperties.Concatenation
import Grammars.Classes.ContextFree.ClosureProperties.Permutation
import Grammars.Utilities.ListUtils
import Grammars.Utilities.LanguageOperations

/-- The class of context-free languages isn't closed under intersection. -/
theorem nnyCF_of_CF_i_CF : ¬ (∀ T : Type, ∀ L₁ : Language T, ∀ L₂ : Language T,
    is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ ⊓ L₂)
) := by
  sorry
