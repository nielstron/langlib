import Mathlib.Data.List.Basic
import Mathlib.Computability.ContextFreeGrammar

/-! # Pumping CFG Utilities

This file contains helper lemmas for repeated concatenation and derivation induction.

## Main declarations

- `nTimes_add`
- `nTimes_mul`
- `Derives.head_induction_on`
-/

variable {α : Type _}

def nTimes (l : List α) (n : ℕ) : List α :=
  (List.replicate n l).flatten

infixl:69 " ^+^ " => nTimes

variable {l : List α} {n : ℕ}

lemma nTimes_succ_l : l^+^n.succ = l ++ l^+^n := by
  simp [nTimes, List.replicate_succ]

lemma nTimes_succ_r : l^+^n.succ = l^+^n ++ l := by
  simp [nTimes, List.replicate_succ']

lemma nTimes_map {β : Type _} {f : α → β} : (l.map f)^+^n = (l^+^n).map f := by
  simp [nTimes]

-- not used anywhere, just for fun
lemma nTimes_add {m : ℕ} : l ^+^ (m + n) = l ^+^ m ++ l ^+^ n := by
  induction n with
  | zero => exact (l ^+^ m).append_nil.symm
  | succ _ ih => rw [Nat.add_succ, nTimes_succ_r, nTimes_succ_r, ih, List.append_assoc]

-- not used anywhere, just for fun
lemma nTimes_mul {m : ℕ} : l ^+^ m * n = l ^+^ m ^+^ n := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Nat.mul_succ, nTimes_add, ih, nTimes_succ_r]

namespace ContextFreeGrammar

universe uN uT

variable {T : Type uT} {g : ContextFreeGrammar T}

theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
    {u : List (Symbol T g.NT)} (huv : g.Derives u v)
    (refl : P v (Derives.refl v))
    (head : ∀ {u w} (huw : g.Produces u w) (hwv : g.Derives w v), P w hwv → P u (hwv.head huw)) :
    P u huv :=
  Relation.ReflTransGen.head_induction_on huv refl head

end ContextFreeGrammar
