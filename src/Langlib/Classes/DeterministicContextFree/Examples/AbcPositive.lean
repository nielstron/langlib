module

public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Examples.AbcPositive
public import Langlib.Examples.AnBnCnPos
public import Langlib.Examples.AnBnCn
import Langlib.Classes.ContextFree.Examples.AnBnCnPos
import Langlib.Classes.DeterministicContextFree.Closure.Complement
import Langlib.Classes.DeterministicContextFree.Closure.IntersectionRegular
import Langlib.Classes.DeterministicContextFree.Examples.AnBmCm
import Langlib.Classes.DeterministicContextFree.Examples.AnBnCm
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
import Langlib.Classes.Regular.Closure.Concatenation
import Langlib.Classes.Regular.Closure.Star
@[expose]
public section

/-! # Membership facts for the positive `a b c` slice witnesses

`abcPositive` is regular; the positive-slice intersections `lang_eq_any_pos` /
`lang_any_eq_pos` (and the complement variants `lang_not_eq_any_pos` /
`lang_not_any_eq_pos`) are deterministic context-free; and the positive `{aⁿbⁿcⁿ}` witness
`lang_eq_eq_pos` is neither context-free nor deterministic context-free.

The bridge `lang_eq_eq_pos_eq_inter` identifies the explicit-replicate `lang_eq_eq_pos`
(from `Langlib.Examples.AnBnCnPos`) with the intersection `lang_eq_eq ⊓ abcPositive`,
so the deterministic non-closure proofs can reuse the shared definition.
-/

open PDA

/-- The explicit positive witness `lang_eq_eq_pos` equals `lang_eq_eq ⊓ abcPositive`. -/
public theorem lang_eq_eq_pos_eq_inter :
    lang_eq_eq_pos = lang_eq_eq ⊓ abcPositive := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨⟨n + 1, by simp only [a_, b_, c_]⟩, n, n, n, by simp only [a_, b_, c_]⟩
  · rintro ⟨⟨m, hm⟩, hpos⟩
    have hm_pos : m ≠ 0 := by
      rintro rfl
      rw [hm] at hpos
      obtain ⟨n', m', k', hp⟩ := hpos
      have hlen := congrArg List.length hp
      simp only [List.length_append, List.length_replicate] at hlen
      omega
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos
    exact ⟨p, by rw [hm]; simp only [a_, b_, c_]⟩

private abbrev letterPlus (a : Fin 3) : Language (Fin 3) :=
  ({[a]} : Language (Fin 3)) * KStar.kstar ({[a]} : Language (Fin 3))

private lemma letterPlus_regular (a : Fin 3) :
    (letterPlus a).IsRegular :=
  (Language.isRegular_singleton_word [a]).mul'
    ((Language.isRegular_singleton_word [a]).kstar')

private lemma letterPlus_mem_iff {a : Fin 3} {w : List (Fin 3)} :
    w ∈ letterPlus a ↔ ∃ n : ℕ, w = List.replicate (n + 1) a := by
  have flatten_singletons :
      ∀ blocks : List (List (Fin 3)),
        (∀ y ∈ blocks, y = [a]) → blocks.flatten = List.replicate blocks.length a := by
    intro blocks
    induction blocks with
    | nil =>
        intro _
        simp
    | cons block blocks ih =>
        intro hblocks
        have hblock : block = [a] := hblocks block (by simp)
        have htail : ∀ y ∈ blocks, y = [a] := by
          intro y hy
          exact hblocks y (by simp [hy])
        simp [hblock, ih htail, List.replicate_succ]
  rw [letterPlus, Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst u
    rw [Language.mem_kstar] at hv
    rcases hv with ⟨blocks, rfl, hblocks⟩
    have hblocks_eq : ∀ y ∈ blocks, y = [a] := by
      intro y hy
      exact Set.mem_singleton_iff.mp (hblocks y hy)
    exact ⟨blocks.length, by simp [flatten_singletons blocks hblocks_eq, List.replicate_succ]⟩
  · rintro ⟨n, rfl⟩
    refine ⟨[a], Set.mem_singleton _, List.replicate n a, ?_, ?_⟩
    · rw [Language.mem_kstar]
      refine ⟨List.replicate n [a], ?_, ?_⟩
      · have hrep : (List.replicate n [a]).flatten = List.replicate n a := by
          induction n with
          | zero => rfl
          | succ n ih => simp [List.replicate_succ, ih]
        exact hrep.symm
      · intro y hy
        rw [List.mem_replicate] at hy
        exact hy.2.symm ▸ Set.mem_singleton [a]
    · simp [List.replicate_succ]

/-- The slice `a⁺ b⁺ c⁺` is regular. -/
public theorem abcPositive_regular : abcPositive.IsRegular := by
  have hreg : (letterPlus a_ * letterPlus b_ * letterPlus c_).IsRegular :=
    ((letterPlus_regular a_).mul' (letterPlus_regular b_)).mul' (letterPlus_regular c_)
  convert hreg using 1
  ext w
  constructor
  · rintro ⟨n, m, k, rfl⟩
    rw [Language.mem_mul]
    refine ⟨List.replicate (n + 1) a_ ++ List.replicate (m + 1) b_, ?_,
      List.replicate (k + 1) c_, (letterPlus_mem_iff).2 ⟨k, rfl⟩, ?_⟩
    · rw [Language.mem_mul]
      exact ⟨List.replicate (n + 1) a_, (letterPlus_mem_iff).2 ⟨n, rfl⟩,
        List.replicate (m + 1) b_, (letterPlus_mem_iff).2 ⟨m, rfl⟩, rfl⟩
    · simp [List.append_assoc]
  · rw [Language.mem_mul]
    rintro ⟨u, hu, v, hv, rfl⟩
    rw [Language.mem_mul] at hu
    rcases hu with ⟨x, hx, y, hy, rfl⟩
    rcases (letterPlus_mem_iff).1 hx with ⟨n, rfl⟩
    rcases (letterPlus_mem_iff).1 hy with ⟨m, rfl⟩
    rcases (letterPlus_mem_iff).1 hv with ⟨k, rfl⟩
    exact ⟨n, m, k, by simp [List.append_assoc]⟩

public theorem DCF_lang_eq_any_pos : is_DCF lang_eq_any_pos :=
  DCF_inter_regular lang_eq_any abcPositive
    DCFLIntersection.DCF_lang_eq_any abcPositive_regular

public theorem DCF_lang_any_eq_pos : is_DCF lang_any_eq_pos :=
  DCF_inter_regular lang_any_eq abcPositive
    DCFLIntersection.DCF_lang_any_eq abcPositive_regular

public theorem DCF_lang_not_eq_any_pos : is_DCF lang_not_eq_any_pos :=
  DCF_inter_regular lang_eq_any_posᶜ abcPositive
    (DCF_closedUnderComplement lang_eq_any_pos DCF_lang_eq_any_pos)
    abcPositive_regular

public theorem DCF_lang_not_any_eq_pos : is_DCF lang_not_any_eq_pos :=
  DCF_inter_regular lang_any_eq_posᶜ abcPositive
    (DCF_closedUnderComplement lang_any_eq_pos DCF_lang_any_eq_pos)
    abcPositive_regular

public theorem notDCF_lang_eq_eq_pos : ¬ is_DCF lang_eq_eq_pos := by
  intro h
  exact notCF_lang_eq_eq_pos (is_CF_of_is_DCF h)

end
