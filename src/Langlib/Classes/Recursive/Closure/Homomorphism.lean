module

public import Langlib.Classes.Recursive.Inclusion.StrictRecursivelyEnumerable
public import Langlib.Classes.RecursivelyEnumerable.Closure.Substitution
public import Langlib.Utilities.ClosurePredicates

/-!
# Recursive Homomorphism Counterexample Scaffold

This file isolates the standard bounded-halting source language whose erasing
homomorphic image is the unary halting language.
-/

open Language

/-- A two-letter bounded-halting language: `false^n true^k` is accepted exactly when
the unary program code of length `n` halts within bound `k`. -/
public def boundedHaltingSource : Language Bool :=
  fun w => ∃ n k : ℕ,
    w = List.replicate n false ++ List.replicate k true ∧
      haltingUnaryTest k (List.replicate n ()) = true

/-- Erase the bound marker and keep the unary program-code marker. -/
public def eraseBoundedHaltingSource : Bool → List Unit
  | false => [()]
  | true => []

private lemma unit_list_eq_replicate (w : List Unit) :
    w = List.replicate w.length () := by
  induction w with
  | nil => simp
  | cons u w ih =>
      cases u
      rw [ih]
      simp [List.replicate]

private lemma flatMap_eraseBoundedHaltingSource_false (n : ℕ) :
    (List.replicate n false).flatMap eraseBoundedHaltingSource =
      List.replicate n () := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate, eraseBoundedHaltingSource, ih]

private lemma flatMap_eraseBoundedHaltingSource_true (k : ℕ) :
    (List.replicate k true).flatMap eraseBoundedHaltingSource = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [List.replicate, eraseBoundedHaltingSource, ih]

private lemma flatMap_eraseBoundedHaltingSource_replicate (n k : ℕ) :
    (List.replicate n false ++ List.replicate k true).flatMap
        eraseBoundedHaltingSource =
      List.replicate n () := by
  rw [List.flatMap_append]
  rw [flatMap_eraseBoundedHaltingSource_false n]
  rw [flatMap_eraseBoundedHaltingSource_true k]
  rw [List.append_nil]

/-- The erasing homomorphic image of the bounded source is the unary halting language. -/
public theorem boundedHaltingSource_homomorphicImage :
    boundedHaltingSource.homomorphicImage eraseBoundedHaltingSource =
      haltingUnaryLanguage := by
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, hxw⟩ :=
      (Language.mem_homomorphicImage_iff_flatMap boundedHaltingSource
        eraseBoundedHaltingSource w).mp hw
    rcases hx with ⟨n, k, rfl, htest⟩
    have hw_eq : w = List.replicate n () := by
      rw [← hxw]
      exact flatMap_eraseBoundedHaltingSource_replicate n k
    exact (haltingUnaryLanguage_search w).mpr ⟨k, by rw [hw_eq]; exact htest⟩
  · intro hw
    obtain ⟨k, hk⟩ := (haltingUnaryLanguage_search w).mp hw
    refine (Language.mem_homomorphicImage_iff_flatMap boundedHaltingSource
      eraseBoundedHaltingSource w).mpr ?_
    refine ⟨List.replicate w.length false ++ List.replicate k true, ?_, ?_⟩
    · refine ⟨w.length, k, rfl, ?_⟩
      rw [← unit_list_eq_replicate w]
      exact hk
    · exact (flatMap_eraseBoundedHaltingSource_replicate w.length k).trans
        (unit_list_eq_replicate w).symm

/-- Once the bounded-halting source is known recursive, recursive languages cannot be
closed under homomorphism. -/
public theorem Recursive_notClosedUnderHomomorphism_of_boundedHaltingSource_recursive
    (hbounded : is_Recursive boundedHaltingSource) :
    ¬ ClosedUnderHomomorphism is_Recursive := by
  intro hclosed
  have himage : is_Recursive
      (boundedHaltingSource.homomorphicImage eraseBoundedHaltingSource) :=
    hclosed boundedHaltingSource eraseBoundedHaltingSource hbounded
  rw [boundedHaltingSource_homomorphicImage] at himage
  exact haltingUnaryLanguage_not_Recursive himage
