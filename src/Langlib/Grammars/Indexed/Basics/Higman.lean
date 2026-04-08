import Mathlib

/-! # Higman's Lemma Application for Languages

This file states a consequence of Higman's lemma that is used in the proof of the
shrinking lemma for indexed languages.

## Main result

`higman_finite_antichain`: For any set `Y` of lists over a finite type, the set of
minimal elements of `Y` under the sublist relation is finite.

## References

* J. Sakarovitch and I. Simon, "Subwords", in M. Lothaire (ed.),
  *Combinatorics on Words*, 1983.
* R. H. Gilman, "A shrinking lemma for indexed languages",
  *Theoret. Comput. Sci.* 163 (1996), 277–281.
-/

open List

/-- The set of minimal elements of a set `Y` of lists, under the sublist relation.
An element `x ∈ Y` is minimal if no proper sublist of `x` belongs to `Y`. -/
def minimalElements (α : Type*) (Y : Set (List α)) : Set (List α) :=
  {x ∈ Y | ∀ y ∈ Y, y <+ x → y = x}

/-
**Higman's lemma consequence**: For any set `Y` of lists over a finite type,
the set of minimal elements under the sublist relation is finite.

This follows from Higman's lemma (`Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`)
which states that the sublist relation is a well-quasi-order on lists over a finite type.
In a well-quasi-order, every antichain (set of pairwise incomparable elements) is finite,
and the set of minimal elements is an antichain.
-/
theorem higman_finite_antichain (α : Type*) [Fintype α] (Y : Set (List α)) :
    Set.Finite (minimalElements α Y) := by
  by_contra! h;
  obtain ⟨l, hl⟩ : ∃ l : ℕ → List α, Set.InjOn l Set.univ ∧ ∀ n, l n ∈ minimalElements α Y := by
    have := h.natEmbedding;
    exact ⟨ _, fun n _ m _ hnm => by simpa using this.injective <| Subtype.ext hnm, fun n => this n |>.2 ⟩;
  -- By Higman's lemma, there exist indices $i < j$ such that $l_i$ is a sublist of $l_j$.
  obtain ⟨i, j, hij, h_sublist⟩ : ∃ i j, i < j ∧ l i <+ l j := by
    have h_higman : WellQuasiOrdered (fun x y : List α => x <+ y) := by
      have h_higman : WellQuasiOrdered (fun x y : List α => List.SublistForall₂ (fun x y => x = y) x y) := by
        have h_well_quasi_ordered : WellQuasiOrdered (fun x y : α => x = y) := by
          exact Finite.wellQuasiOrdered fun x y => x = y;
        have h_well_quasi_ordered : ∀ (s : Set α), Set.PartiallyWellOrderedOn s (fun x y : α => x = y) → Set.PartiallyWellOrderedOn {l : List α | ∀ x ∈ l, x ∈ s} (fun x y : List α => List.SublistForall₂ (fun x y => x = y) x y) := by
          exact fun s a => Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (fun x y => x = y) a;
        specialize h_well_quasi_ordered Set.univ;
        simp_all +decide [ Set.PartiallyWellOrderedOn ];
        convert h_well_quasi_ordered _;
        · constructor <;> intro h f;
          · exact h fun n => f n |>.1;
          · exact h ( fun n => ⟨ f n, fun x hx => Set.mem_univ x ⟩ );
        · intro f;
          aesop;
      convert h_higman using 1;
      ext x y; simp +decide [ List.sublistForall₂_iff ] ;
    exact Exists₂.imp (fun a b a_1 => a_1) (h_higman l);
  have := hl.2 j;
  exact absurd ( this.2 ( l i ) ( hl.2 i |>.1 ) h_sublist ) ( hl.1.ne ( Set.mem_univ _ ) ( Set.mem_univ _ ) hij.ne )

/-
For any set `Y` of lists over a finite type, any element of `Y` either is minimal
or has a minimal element as a sublist.
-/
theorem exists_minimal_sublist (α : Type*) [Fintype α] (Y : Set (List α))
    (y : List α) (hy : y ∈ Y) :
    ∃ x ∈ minimalElements α Y, x <+ y := by
  -- Use well-founded induction on the length of `y`.
  induction' n : y.length using Nat.strong_induction_on with n ih generalizing y;
  by_cases h_min : ∀ z ∈ Y, z <+ y → z = y;
  · exact ⟨ y, ⟨ hy, h_min ⟩, List.Sublist.refl _ ⟩;
  · -- Otherwise, there exists y' ∈ Y with y' <+ y and y' ≠ y, so y'.length < y.length.
    obtain ⟨y', hy', hy'_lt, hy'_ne⟩ : ∃ y' ∈ Y, y' <+ y ∧ y' ≠ y ∧ y'.length < y.length := by
      grind +qlia;
    exact Exists.elim ( ih _ ( by linarith ) _ hy' rfl ) fun x hx => ⟨ x, hx.1, hx.2.trans hy'_lt ⟩