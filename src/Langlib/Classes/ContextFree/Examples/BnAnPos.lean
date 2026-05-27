import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Examples.BnAn

/-! # The positive `{b^n a^n}` language

This file defines `{b^n a^n | n >= 1}` over `Bool`, with `false = a` and
`true = b`, and proves it is context-free.
-/

open Language

/-- The positive block language `{b^n a^n | n >= 1}`, with `false = a` and `true = b`. -/
def quotientRightBlock : Language Bool :=
  fun w => ∃ n : ℕ, w = List.replicate (n + 1) true ++ List.replicate (n + 1) false

lemma quotientRightBlock_eq_singletons_core :
    quotientRightBlock = ({[true]} : Language Bool) * quotientRightBlockCore * {[false]} := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    rw [Language.mem_mul]
    refine ⟨[true] ++ (List.replicate n true ++ List.replicate n false),
      ?_, [false], Set.mem_singleton _, ?_⟩
    · rw [Language.mem_mul]
      refine ⟨[true], Set.mem_singleton _, _,
        ⟨n, rfl⟩, ?_⟩
      simp
    · rw [List.replicate_succ, List.replicate_succ']
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
    rw [List.replicate_succ, List.replicate_succ']
    simp [List.append_assoc]

lemma CF_quotientRightBlock : is_CF quotientRightBlock := by
  rw [quotientRightBlock_eq_singletons_core]
  apply CF_of_CF_c_CF
  exact ⟨CF_of_CF_c_CF _ _ ⟨is_CF_singleton [true], CF_quotientRightBlockCore⟩,
    is_CF_singleton [false]⟩
