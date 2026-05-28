module

public import Aesop.BuiltinRules
public import Mathlib.Computability.TuringMachine
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-! # Drop from the Last Separator

This file contains the list-level operation used by separator-erasing block
machines.

## Key results

- `dropFromLastSep`: drops everything through the final occurrence of `sep`.
- `dropFromLastSep_not_mem`: if `sep` is absent, the operation is the identity.
- `dropFromLastSep_ne_default`: non-default cells stay non-default.
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
