module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.AnBmCm
public import Langlib.Examples.AlphabetABC
public import Langlib.Classes.ContextFree.Examples.AnBnCm
import Langlib.Classes.ContextFree.Basics.Elementary
import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Closure.Permutation
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Langlib.Utilities.Tactics
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
@[expose]
public section

/-! # `{aⁿbᵐcᵐ}` is context-free

The language `lang_any_eq = {aⁿbᵐcᵐ | n,m ∈ ℕ}` is context-free, presented as the
concatenation of `{aⁿ}` with `{bᵐcᵐ}`. The latter factor is obtained from
`lang_aux_ab = {aⁿbⁿ}` (proved context-free in
`Langlib.Classes.ContextFree.Examples.AnBnCm`) by a letter permutation.
-/

private def lang_aux_a : Language (Fin 3) :=
fun w => ∃ n : ℕ, w = List.replicate n a_

private lemma CF_lang_aux_a : is_CF lang_aux_a := by
  apply is_CF_via_cfg_implies_is_CF
  refine ⟨cfg_symbol_star a_, ?_⟩
  unfold lang_aux_a
  apply language_of_cfg_symbol_star

private def lang_aux_bc : Language (Fin 3) :=
fun w => ∃ n : ℕ, w = List.replicate n b_ ++ List.replicate n c_

private def permut : Equiv.Perm (Fin 3) := Equiv.mk
  (fun x => ite (x = 2) 0 (x + 1))
  (fun x => ite (x = 0) 2 (x - 1))
  (by
    intro x
    fin_cases x <;> rfl)
  (by
    intro x
    fin_cases x <;> rfl)

private lemma CF_lang_aux_bc : is_CF lang_aux_bc := by
  have permuted : lang_aux_bc = Language.permuteLang lang_aux_ab permut := by
    have psb : permut.symm b_ = a_ := by decide
    have psc : permut.symm c_ = b_ := by decide
    have pa : permut a_ = b_ := by decide
    have pb : permut b_ = c_ := by decide
    ext1 w
    constructor
    · rintro ⟨n, hn⟩
      show List.map permut.symm w ∈ lang_aux_ab
      refine ⟨n, ?_⟩
      rw [hn, List.map_append, List.map_replicate, List.map_replicate, psb, psc]
    · intro h
      show _ ∈ lang_aux_bc
      obtain ⟨n, hn⟩ := h
      refine ⟨n, ?_⟩
      have := congr_arg (List.map permut) hn
      rw [List.map_map, List.map_append, List.map_replicate, List.map_replicate, pa, pb] at this
      simp only [Equiv.self_comp_symm, List.map_id] at this
      exact this
  rw [permuted]
  exact (CF_of_permute_CF permut lang_aux_ab).mpr CF_lang_aux_ab

public lemma CF_lang_any_eq : is_CF lang_any_eq := by
  have concatenated : lang_any_eq = lang_aux_a * lang_aux_bc := by
    ext1 w
    constructor
    · rintro ⟨n, m, hnm⟩
      rw [Language.mem_mul]
      exact ⟨_, ⟨n, rfl⟩, _, ⟨m, rfl⟩, by rw [← List.append_assoc]; exact hnm.symm⟩
    · intro hmem
      rw [Language.mem_mul] at hmem
      obtain ⟨u, ⟨n, hu⟩, v, ⟨m, hv⟩, h⟩ := hmem
      use n, m
      rw [List.append_assoc, ← h, ← hu, ← hv]
  rw [concatenated]
  apply CF_of_CF_c_CF
  exact And.intro CF_lang_aux_a CF_lang_aux_bc

end
