import Grammars.Classes.ContextFree.ClosureProperties.Bijection

/-! # Context-Free Closure Under Permutations

This file specializes bijective terminal renaming to permutations of a fixed alphabet.

## Main declarations

- `CF_of_permute_CF`
-/

/-- A language is context-free iff its image under a permutation of terminals is context-free. -/
@[simp] theorem CF_of_permute_CF {T : Type} (π : Equiv.Perm T) (L : Language T) :
  is_CF (Language.permuteLang L π) ↔ is_CF L := by
  simp [Language.permuteLang]
