module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

@[expose]
public section

/-!
# Fixed-width packing for linear-bounded tapes

This module packs a bounded number of logical symbols into each physical tape cell. It is
independent of any particular grammar or automaton and is used by Aho's row encoding.
-/

/-- A width-`W` block of optional logical symbols stored in one physical tape cell. -/
public abbrev PackedBlock (α : Type) (W : ℕ) : Type :=
  Fin W → Option α

public noncomputable instance PackedBlock.instFintype
    {α : Type} [Fintype α] (W : ℕ) :
    Fintype (PackedBlock α W) := by
  classical
  change Fintype (Fin W → Option α)
  infer_instance

public instance PackedBlock.instDecidableEq
    {α : Type} [DecidableEq α] (W : ℕ) :
    DecidableEq (PackedBlock α W) := by
  change DecidableEq (Fin W → Option α)
  infer_instance

/-- The `i`-th width-`W` block of a list, padded with `none` past the list end. -/
public def packedCell {α : Type} (W : ℕ) (xs : List α) (i : ℕ) : PackedBlock α W :=
  fun j => xs[i * W + j.1]?

/-- Pack a list into `n` width-`W` cells. Entries beyond `n * W` are ignored. -/
public def packedTape {α : Type} (W n : ℕ) (xs : List α) : Fin n → PackedBlock α W :=
  fun i => packedCell W xs i.1

public theorem packedTape_lookup {α : Type} {W n k : ℕ} (xs : List α)
    (hW : 0 < W) (hk : k < n * W) :
    packedTape W n xs
        ⟨k / W, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)⟩
        ⟨k % W, Nat.mod_lt k hW⟩ =
      xs[k]? := by
  simp [packedTape, packedCell]
  rw [Nat.mul_comm (k / W) W, Nat.div_add_mod]

/-- Packing is injective for lists that fit in the advertised physical capacity. -/
public theorem packedTape_ext_of_length_le {α : Type} {W n : ℕ} {xs ys : List α}
    (hW : 0 < W) (hxs : xs.length ≤ n * W) (hys : ys.length ≤ n * W)
    (hpack : packedTape W n xs = packedTape W n ys) :
    xs = ys := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < n * W
  · have hx := packedTape_lookup (W := W) (n := n) (k := k) xs hW hk
    have hy := packedTape_lookup (W := W) (n := n) (k := k) ys hW hk
    have hp :=
      congrFun
        (congrFun hpack
          ⟨k / W, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)⟩)
        ⟨k % W, Nat.mod_lt k hW⟩
    rw [hx, hy] at hp
    exact hp
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end
