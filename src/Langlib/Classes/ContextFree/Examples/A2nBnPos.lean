import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Examples.A2nBn

/-! # The positive `{a^(2n)b^n}` language

This file defines `{a^(2n)b^n | n >= 1}` over `Bool`, with `false = a` and
`true = b`, and proves it is context-free.
-/

open Language

/-- The positive block language `{a^(2n)b^n | n >= 1}`, with `false = a` and `true = b`. -/
def quotientLeftBlock : Language Bool :=
  fun w => ∃ n : ℕ, w = List.replicate (2 * (n + 1)) false ++ List.replicate (n + 1) true

lemma quotientLeftBlock_eq_singletons_core :
    quotientLeftBlock = ({[false, false]} : Language Bool) * quotientLeftBlockCore * {[true]} := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    rw [Language.mem_mul]
    refine ⟨[false, false] ++
        (List.replicate (2 * n) false ++ List.replicate n true),
      ?_, [true], Set.mem_singleton _, ?_⟩
    · rw [Language.mem_mul]
      refine ⟨[false, false], Set.mem_singleton _, _,
        ⟨n, rfl⟩, ?_⟩
      simp
    · rw [show 2 * (n + 1) = 2 + 2 * n by omega]
      rw [show List.replicate (2 + 2 * n) false =
          [false, false] ++ List.replicate (2 * n) false by
        simp [List.replicate_add]]
      rw [List.replicate_succ']
      simp [List.append_assoc]
  · intro hw
    rw [Language.mem_mul] at hw
    rcases hw with ⟨u, hu, v, hv, rfl⟩
    rw [Language.mem_mul] at hu
    rcases hu with ⟨p, hp, q, ⟨n, hq⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hp hv
    subst hp
    subst hv
    refine ⟨n, ?_⟩
    rw [hq]
    rw [show 2 * (n + 1) = 2 + 2 * n by omega]
    simp [List.replicate_add, List.append_assoc]

lemma CF_quotientLeftBlock : is_CF quotientLeftBlock := by
  rw [quotientLeftBlock_eq_singletons_core]
  apply CF_of_CF_c_CF
  exact ⟨CF_of_CF_c_CF _ _ ⟨is_CF_singleton [false, false], CF_quotientLeftBlockCore⟩,
    is_CF_singleton [true]⟩
