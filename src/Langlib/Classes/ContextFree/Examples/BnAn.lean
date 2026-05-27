import Langlib.Classes.ContextFree.Closure.Homomorphism
import Langlib.Classes.ContextFree.Examples.AnBn
import Mathlib

/-! # The `{b^n a^n}` language

This file defines `{b^n a^n | n in N}` over `Bool`, with `false = a` and
`true = b`, and proves it is context-free.
-/

open Language

/-- Multiplying singleton-word languages along a word gives the flattened homomorphic image. -/
private lemma mem_prod_singleton_words_iff {α β : Type} (h : α → List β) :
    ∀ w : List α, ∀ u : List β,
      u ∈ (w.map fun x => ({h x} : Language β)).prod ↔ u = w.flatMap h
  | [], u => by
      change u ∈ ({[]} : Language β) ↔ u = []
      rfl
  | x :: xs, u => by
      constructor
      · intro hu
        rw [show (List.map (fun x => ({h x} : Language β)) (x :: xs)).prod =
            ({h x} : Language β) * (List.map (fun x => ({h x} : Language β)) xs).prod
          by rfl] at hu
        rw [Language.mul_def] at hu
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        have hu₂' := (mem_prod_singleton_words_iff h xs u₂).1 hu₂
        have hu₁' : u₁ = h x := by simpa using hu₁
        simp [hu₁', hu₂']
      · intro hu
        subst hu
        rw [show (List.map (fun x => ({h x} : Language β)) (x :: xs)).prod =
            ({h x} : Language β) * (List.map (fun x => ({h x} : Language β)) xs).prod
          by rfl]
        rw [Language.mul_def]
        refine ⟨h x, Set.mem_singleton _, xs.flatMap h, ?_, rfl⟩
        exact (mem_prod_singleton_words_iff h xs _).2 rfl

/-- The core block language `{b^n a^n | n in N}`. -/
def quotientRightBlockCore : Language Bool :=
  fun w => ∃ n : ℕ, w = List.replicate n true ++ List.replicate n false

private lemma flatMap_right_hom_anbn (n : ℕ) :
    (List.replicate n false ++ List.replicate n true).flatMap
        (fun b => if b = true then [false] else [true]) =
      List.replicate n true ++ List.replicate n false := by
  simp [List.flatMap_append, List.flatMap_replicate]

lemma quotientRightBlockCore_eq_hom :
    quotientRightBlockCore =
      anbn.homomorphicImage (fun b => if b = true then [false] else [true]) := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨List.replicate n false ++ List.replicate n true, ⟨n, rfl⟩, ?_⟩
    exact
      (mem_prod_singleton_words_iff
        (fun b => if b = true then [false] else [true]) _ _).2
        (flatMap_right_hom_anbn n).symm
  · rintro ⟨src, ⟨n, hsrc⟩, hwprod⟩
    refine ⟨n, ?_⟩
    have hw :=
      (mem_prod_singleton_words_iff
        (fun b => if b = true then [false] else [true]) src w).1 hwprod
    rw [hw, hsrc, flatMap_right_hom_anbn]

lemma CF_quotientRightBlockCore : is_CF quotientRightBlockCore := by
  rw [quotientRightBlockCore_eq_hom]
  exact CF_closed_under_homomorphism anbn
    (fun b => if b = true then [false] else [true]) anbn_is_CF
