module

/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Linear.Inclusion.ContextFree
public import Langlib.Classes.Linear.Pumping.Pumping
import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.ContextFree.Closure.Homomorphism
import Langlib.Classes.ContextFree.Examples.AnBn
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Mathlib.Tactic.FinCases
public import Langlib.Examples.AnBn
@[expose]
public section



/-! # Linear ⊊ Context-Free

The language `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4` is context-free (a concatenation of two
copies of `aⁿbⁿ`) but not linear: the linear pumping lemma confines the pumped
pieces to the two ends, but pumping then breaks one of the two independent
matchings.

## Main results

- `L4_is_CF`            — `{0ⁿ1ⁿ2ᵐ3ᵐ}` is context-free.
- `L4_not_is_Linear`    — `{0ⁿ1ⁿ2ᵐ3ᵐ}` is not linear.
- `Linear_strict_subclass_CF` — `Linear ⊊ CF` over `Fin 4`.
-/

open Language List

/-- Inject `aⁿbⁿ`'s alphabet to `0`/`1`. -/
def f4 : Bool → Fin 4 := fun b => if b then 1 else 0
/-- Inject `aⁿbⁿ`'s alphabet to `2`/`3`. -/
def g4 : Bool → Fin 4 := fun b => if b then 3 else 2

theorem map_anbn_is_CF' (f : Bool → Fin 4) : is_CF (Language.map f anbn) := by
  have hsubst : is_CF (anbn.subst (fun x => ({[f x]} : Language (Fin 4)))) := by
    apply CF_of_subst_CF anbn
    · exact anbn_is_CF
    · intro x
      rw [is_CF_iff_isContextFree]
      exact isContextFree_singleton [f x]
  simpa [Language.subst_singletons_eq_map] using hsubst

/-- The witness language `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4`. -/
public def L4 : Language (Fin 4) := Language.map f4 anbn * Language.map g4 anbn

/-- `{0ⁿ1ⁿ2ᵐ3ᵐ}` is context-free. -/
public theorem L4_is_CF : is_CF L4 :=
  CF_of_CF_c_CF _ _ ⟨map_anbn_is_CF' f4, map_anbn_is_CF' g4⟩

/-- `0ᵏ1ᵏ ∈ map f4 aⁿbⁿ`. -/
theorem mem_map_anbn (f : Bool → Fin 4) (k : ℕ) :
    List.replicate k (f false) ++ List.replicate k (f true) ∈ Language.map f anbn := by
  refine ⟨List.replicate k false ++ List.replicate k true, ⟨k, rfl⟩, ?_⟩
  simp [List.map_append, List.map_replicate]

/-- If `s ∈ map f anbn` then `s = (f false)ᵏ (f true)ᵏ` for some `k`. -/
theorem eq_of_mem_map_anbn {f : Bool → Fin 4} {s : List (Fin 4)} (hs : s ∈ Language.map f anbn) :
    ∃ k, s = List.replicate k (f false) ++ List.replicate k (f true) := by
  obtain ⟨ws, ⟨k, rfl⟩, rfl⟩ := hs
  exact ⟨k, by simp [List.map_append, List.map_replicate]⟩

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

/-- Linear languages are a strict subclass of context-free languages over `Fin 4`. -/
public theorem Linear_strict_subclass_CF :
    (Linear : Set (Language (Fin 4))) ⊂ (CF : Set (Language (Fin 4))) := by
  refine ⟨Linear_subclass_CF, fun hsub => ?_⟩
  exact L4_not_is_Linear (hsub L4_is_CF)
