import Mathlib

/-! # DropFromLastSep: Generic erase-prefix-through-last-separator
Generic definitions for `dropFromLastSep`.
-/
open Turing

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ]

/-- Drop everything up to and including the LAST occurrence of `sep`.
    If `sep ∉ l`, return `l` unchanged. -/
def dropFromLastSep (sep : Γ) : List Γ → List Γ
  | [] => []
  | c :: rest =>
    if sep ∈ rest then dropFromLastSep sep rest
    else if c = sep then rest
    else c :: rest

theorem dropFromLastSep_nil (sep : Γ) : dropFromLastSep sep ([] : List Γ) = [] :=
 by rfl

theorem dropFromLastSep_cons_mem (sep : Γ) (c : Γ) (rest : List Γ) (h : sep ∈ rest) :
    dropFromLastSep sep (c :: rest) = dropFromLastSep sep rest := by
  simp [dropFromLastSep, h]

theorem dropFromLastSep_cons_sep_not_mem (sep : Γ) (rest : List Γ) (h : sep ∉ rest) :
    dropFromLastSep sep (sep :: rest) = rest := by
  simp [dropFromLastSep, h]

theorem dropFromLastSep_cons_ne_not_mem (sep c : Γ) (rest : List Γ) (hc : c ≠ sep) (h : sep ∉ rest) :
    dropFromLastSep sep (c :: rest) = c :: rest := by
  simp [dropFromLastSep, h, hc]

/-- When `sep ∉ l`, `dropFromLastSep` is the identity. -/
theorem dropFromLastSep_not_mem (sep : Γ) (l : List Γ) (h : sep ∉ l) :
    dropFromLastSep sep l = l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.mem_cons, not_or] at h
    simp [dropFromLastSep, h.2, Ne.symm h.1]

/-- `dropFromLastSep` preserves non-defaultness. -/
theorem dropFromLastSep_ne_default (sep : Γ) (l : List Γ)
    (hl : ∀ g ∈ l, g ≠ default) :
    ∀ g ∈ dropFromLastSep sep l, g ≠ default := by
  induction l with
  | nil => simp [dropFromLastSep]
  | cons c rest ih =>
    simp only [dropFromLastSep]
    split_ifs with h1 h2
    · exact ih (fun g hg => hl g (List.mem_cons_of_mem _ hg))
    · exact fun g hg => hl g (List.mem_cons_of_mem _ hg)
    · exact hl
