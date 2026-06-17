module

public import Langlib.Classes.Linear.Inclusion.ContextFree
public import Langlib.Classes.Linear.Pumping.Pumping
public import Langlib.Classes.Linear.Basics.Map
public import Langlib.Examples.L4
public import Langlib.Classes.ContextFree.Examples.L4
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Embedding.Basic
@[expose]
public section

/-! # `{0ⁿ1ⁿ2ᵐ3ᵐ}` is not linear

The linear pumping lemma confines the pumped pieces to the two ends of the witness
`{0ⁿ1ⁿ2ᵐ3ᵐ}`, so pumping breaks one of the two independent `aⁿbⁿ` matchings
(`L4_not_is_Linear`). The relabelled version `Lwit_not_is_Linear` follows because
linearity reflects along injective terminal maps.
-/

open Language List

variable {T : Type}

/-- `{0ⁿ1ⁿ2ᵐ3ᵐ}` is not linear. -/
public theorem L4_not_is_Linear : ¬ is_Linear L4 := by
  intro hLin
  obtain ⟨p, hp⟩ := is_Linear.pumping hLin
  set w : List (Fin 4) :=
    List.replicate p 0 ++ List.replicate p 1 ++ List.replicate p 2 ++ List.replicate p 3 with hw
  -- the witness word is in the language
  have hwmem : w ∈ L4 := by
    have hsplit : w = (List.replicate p 0 ++ List.replicate p 1) ++
        (List.replicate p 2 ++ List.replicate p 3) := by rw [hw]; simp [List.append_assoc]
    rw [hsplit]
    exact Language.append_mem_mul (by simpa [f4] using mem_map_anbn f4 p)
      (by simpa [g4] using mem_map_anbn g4 p)
  have hwlen4 : w.length = 4 * p := by
    rw [hw]; simp only [List.length_append, List.length_replicate]; omega
  have hwlen : w.length ≥ p := by rw [hwlen4]; omega
  obtain ⟨u, v, x, y, z, hdecomp, hvy, hbound, hpump⟩ := hp w hwmem hwlen
  -- take/drop of `w`
  have htake : ∀ m, m ≤ p → w.take m = List.replicate m (0 : Fin 4) := by
    intro m hm
    have e1 : w = List.replicate p (0 : Fin 4) ++
        (List.replicate p 1 ++ List.replicate p 2 ++ List.replicate p 3) := by
      rw [hw]; simp [List.append_assoc]
    rw [e1, List.take_append_of_le_length (by simp only [List.length_replicate]; omega),
      List.take_replicate]
    congr 1; omega
  have hrev : w.reverse = List.replicate p (3 : Fin 4) ++
      (List.replicate p 2 ++ List.replicate p 1 ++ List.replicate p 0) := by
    rw [hw]; simp [List.reverse_append, List.append_assoc]
  have htakeRev : ∀ m, m ≤ p → w.reverse.take m = List.replicate m (3 : Fin 4) := by
    intro m hm
    rw [hrev, List.take_append_of_le_length (by simp only [List.length_replicate]; omega),
      List.take_replicate]
    congr 1; omega
  -- `v` lies in the first block, so it is all `0`
  have hbound' : (u ++ v).length ≤ p ∧ (y ++ z).length ≤ p := by
    simp only [List.length_append] at hbound ⊢; omega
  have hv0 : ∀ e ∈ v, e = (0 : Fin 4) := by
    have hpre : u ++ v <+: w := ⟨x ++ y ++ z, by rw [hdecomp]; simp [List.append_assoc]⟩
    have heq : u ++ v = List.replicate (u ++ v).length (0 : Fin 4) :=
      (List.prefix_iff_eq_take.1 hpre).trans (htake _ hbound'.1)
    intro e he
    exact List.eq_of_mem_replicate (heq ▸ List.mem_append_right u he)
  -- `y` lies in the last block, so it is all `3` (argue on the reversed word)
  have hy3 : ∀ e ∈ y, e = (3 : Fin 4) := by
    have hsuf : y ++ z <:+ w := ⟨u ++ v ++ x, by rw [hdecomp]; simp [List.append_assoc]⟩
    have hpre : (y ++ z).reverse <+: w.reverse := List.reverse_prefix.2 hsuf
    have hlen : (y ++ z).reverse.length ≤ p := by
      rw [List.length_reverse]; exact hbound'.2
    have heq : (y ++ z).reverse = List.replicate (y ++ z).reverse.length (3 : Fin 4) :=
      (List.prefix_iff_eq_take.1 hpre).trans (htakeRev _ hlen)
    intro e he
    have hmem : e ∈ (y ++ z).reverse := List.mem_reverse.2 (List.mem_append.2 (Or.inl he))
    exact List.eq_of_mem_replicate (heq ▸ hmem)
  -- the pumped-down word and its membership
  have huxz : u ++ x ++ z ∈ L4 := by
    have := hpump 0
    simpa [nTimes] using this
  obtain ⟨s, hs, t, ht, hst⟩ := Language.mem_mul.1 huxz
  obtain ⟨k, hsk⟩ := eq_of_mem_map_anbn hs
  obtain ⟨l, htl⟩ := eq_of_mem_map_anbn ht
  simp only [f4, Bool.false_eq_true, if_false, if_true] at hsk
  simp only [g4, Bool.false_eq_true, if_false, if_true] at htl
  -- counts of each symbol in the relevant pieces
  have hcw : ∀ c : Fin 4, List.count c w = p := by
    intro c; rw [hw]
    simp only [List.count_append, List.count_replicate]
    fin_cases c <;> simp
  have hrel : ∀ c : Fin 4,
      List.count c w = List.count c (u ++ x ++ z) + List.count c v + List.count c y := by
    intro c; rw [hdecomp]; simp only [List.count_append]; omega
  have hcuxz : ∀ c : Fin 4, List.count c (u ++ x ++ z) = List.count c s + List.count c t := by
    intro c; rw [← hst, List.count_append]
  have hcv1 : List.count (1 : Fin 4) v = 0 := by
    rw [List.count_eq_zero]; exact fun he => absurd (hv0 _ he) (by decide)
  have hcv2 : List.count (2 : Fin 4) v = 0 := by
    rw [List.count_eq_zero]; exact fun he => absurd (hv0 _ he) (by decide)
  have hcv3 : List.count (3 : Fin 4) v = 0 := by
    rw [List.count_eq_zero]; exact fun he => absurd (hv0 _ he) (by decide)
  have hcy0 : List.count (0 : Fin 4) y = 0 := by
    rw [List.count_eq_zero]; exact fun he => absurd (hy3 _ he) (by decide)
  have hcy1 : List.count (1 : Fin 4) y = 0 := by
    rw [List.count_eq_zero]; exact fun he => absurd (hy3 _ he) (by decide)
  have hcy2 : List.count (2 : Fin 4) y = 0 := by
    rw [List.count_eq_zero]; exact fun he => absurd (hy3 _ he) (by decide)
  have hcv0 : List.count (0 : Fin 4) v = v.length := by
    conv_lhs => rw [List.eq_replicate_length.2 hv0]
    simp
  have hcy3 : List.count (3 : Fin 4) y = y.length := by
    conv_lhs => rw [List.eq_replicate_length.2 hy3]
    simp
  -- combine: count 0 = count 1 forces |v| = 0, count 2 = count 3 forces |y| = 0
  have e0 := hrel 0; have e1 := hrel 1; have e2 := hrel 2; have e3 := hrel 3
  rw [hcw, hcuxz, hsk, htl] at e0 e1 e2 e3
  simp [List.count_append, List.count_replicate] at e0 e1 e2 e3
  have hvy' : v.length + y.length > 0 := by simpa [List.length_append] using hvy
  omega

/-- The relabelled witness is not linear: linearity would reflect back to `L4`. -/
public theorem Lwit_not_is_Linear (e : Fin 4 ↪ T) : ¬ is_Linear (Language.map e L4) :=
  fun h => L4_not_is_Linear (is_Linear_of_map_injective e.injective h)

end
