import Grammars.Classes.ContextFree.ClosureProperties.Bijection

open Grammars


/-- A language is context-free iff its image under a permutation of terminals is context-free. -/
@[simp] theorem CF_of_permute_CF {T : Type} (π : Equiv.Perm T) (L : Language T) :
  is_CF (permuteLang L π) ↔ is_CF L := by
  simp [permuteLang]
