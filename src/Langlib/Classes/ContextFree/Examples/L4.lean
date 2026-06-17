module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.L4
public import Langlib.Examples.AnBn
import Langlib.Classes.ContextFree.Examples.AnBn
import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Grammars.ContextFree.MathlibCFG
import Mathlib.Logic.Embedding.Basic
@[expose]
public section

/-! # `{0ⁿ1ⁿ2ᵐ3ᵐ}` is context-free

`L4` is context-free as a concatenation of two context-free factors `map f4 {aⁿbⁿ}` and
`map g4 {aⁿbⁿ}`. The generic lemma `map_anbn_is_CF` and the membership characterizations
`mem_map_anbn` / `eq_of_mem_map_anbn` for `map f {aⁿbⁿ}` are exposed because the
not-linear proof in `Langlib.Classes.Linear.Examples.L4` reuses them.
-/

open Language

variable {T : Type}

/-- `map f {aⁿbⁿ}` is context-free for any letter map `f`. -/
public theorem map_anbn_is_CF (f : Bool → T) : is_CF (Language.map f anbn) := by
  have hsubst : is_CF (anbn.subst (fun x => ({[f x]} : Language T))) := by
    apply CF_of_subst_CF anbn
    · exact anbn_is_CF
    · intro x
      rw [is_CF_iff_isContextFree]
      exact isContextFree_singleton [f x]
  simpa [Language.subst_singletons_eq_map] using hsubst

/-- `{0ⁿ1ⁿ2ᵐ3ᵐ}` is context-free. -/
public theorem L4_is_CF : is_CF L4 :=
  CF_of_CF_c_CF _ _ ⟨map_anbn_is_CF f4, map_anbn_is_CF g4⟩

/-- `(f false)ᵏ (f true)ᵏ ∈ map f {aⁿbⁿ}`. -/
public theorem mem_map_anbn (f : Bool → T) (k : ℕ) :
    List.replicate k (f false) ++ List.replicate k (f true) ∈ Language.map f anbn := by
  refine ⟨List.replicate k false ++ List.replicate k true, ⟨k, rfl⟩, ?_⟩
  simp [List.map_append, List.map_replicate]

/-- Membership in `map f {aⁿbⁿ}` is exactly `(f false)ᵏ (f true)ᵏ`. -/
public theorem eq_of_mem_map_anbn {f : Bool → T} {s : List T} (hs : s ∈ Language.map f anbn) :
    ∃ k, s = List.replicate k (f false) ++ List.replicate k (f true) := by
  obtain ⟨ws, ⟨k, rfl⟩, rfl⟩ := hs
  exact ⟨k, by simp [List.map_append, List.map_replicate]⟩

/-- The `Fin 4` witness, relabelled along an embedding, is context-free. -/
public theorem Lwit_is_CF (e : Fin 4 ↪ T) : is_CF (Language.map e L4) := by
  have hrw : Language.map e L4
      = Language.map (e ∘ f4) anbn * Language.map (e ∘ g4) anbn := by
    rw [L4, map_mul, Language.map_map, Language.map_map]
  rw [hrw]
  exact CF_of_CF_c_CF _ _ ⟨map_anbn_is_CF _, map_anbn_is_CF _⟩

end
