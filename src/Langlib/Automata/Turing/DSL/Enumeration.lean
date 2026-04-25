import Mathlib

/-! # Composable Enumerations

This file defines `Enum α`, a type of computable enumerations over a type `α`,
together with a library of combinators for building complex enumerations from
simple ones. This forms the "generator" half of the DSL.

## Design

An `Enum α` is simply a function `ℕ → Option α`. Semantically, it represents a
(possibly infinite) stream of elements: `enum 0, enum 1, enum 2, ...`, where
`none` means "no output at this index" (allowing sparse enumerations).

The key combinators are:
- `Enum.naturals` — enumerate all natural numbers
- `Enum.ofList` — enumerate elements of a finite list
- `Enum.ofEncodable` — enumerate all elements of an `Encodable` type
- `Enum.product` — enumerate all pairs (dovetailing)
- `Enum.bind` — monadic bind (flatMap with dovetailing)
- `Enum.map` — apply a function to each element
- `Enum.filterMap` — filter and transform

Each combinator preserves the property that every element in the range
eventually appears (surjectivity onto the range).

## Main definitions

- `Enum` — the type of enumerations
- `Enum.range` — the set of elements that appear in an enumeration
- `Enum.Surjective` — every element in the range appears
- Various combinators with range correctness theorems

## References

This is the "generator" layer of the DSL described in the module
`Langlib.Automata.Turing.DSL.SearchProc`.
-/

/-- An enumeration of elements of type `α`.

Semantically, `e : Enum α` represents a computable sequence
`e 0, e 1, e 2, ...` where each step either produces an element (`some a`)
or is a no-op (`none`). The **range** of `e` is `{a | ∃ n, e n = some a}`.

Note: an `Enum` may produce the same element multiple times; what matters is
that every element in the intended set appears at least once. -/
def Enum (α : Type*) := ℕ → Option α

namespace Enum

variable {α β γ : Type*}

/-- The range (set of produced elements) of an enumeration. -/
def range (e : Enum α) : Set α :=
  { a | ∃ n, e n = some a }

/-- An enumeration is **surjective** onto a set `S` if every element of `S`
    appears in the enumeration. -/
def SurjectiveOnto (e : Enum α) (S : Set α) : Prop :=
  S ⊆ e.range

/-- An enumeration is **exact** for a set `S` if its range equals `S`. -/
def Exact (e : Enum α) (S : Set α) : Prop :=
  e.range = S

theorem exact_iff_range_eq (e : Enum α) (S : Set α) :
    e.Exact S ↔ e.range = S := Iff.rfl

/-! ### Basic enumerations -/

/-- Enumerate all natural numbers: `0, 1, 2, ...` -/
def naturals : Enum ℕ := fun n => some n

theorem naturals_range : naturals.range = Set.univ := by
  ext n; simp [range, naturals]

/-- Enumerate elements of a finite list. -/
def ofList (l : List α) : Enum α := fun n => l[n]?

theorem ofList_range (l : List α) : (ofList l).range = { a | a ∈ l } := by
  ext a; simp [range, ofList, List.mem_iff_getElem?]

/-- Enumerate all elements of an `Encodable` type. -/
def ofEncodable [Encodable α] : Enum α := fun n => Encodable.decode n

theorem ofEncodable_range [Encodable α] : (ofEncodable (α := α)).range = Set.univ := by
  ext a; simp [range, ofEncodable]
  exact ⟨Encodable.encode a, Encodable.encodek a⟩

/-- The empty enumeration. -/
def empty : Enum α := fun _ => none

theorem empty_range : (empty : Enum α).range = ∅ := by
  ext a; simp [range, empty]

/-- Enumerate a single element. -/
def singleton (a : α) : Enum α := fun n => if n = 0 then some a else none

theorem singleton_range (a : α) : (singleton a).range = {a} := by
  ext x; simp [range, singleton]

/-! ### Combinators -/

/-- Apply a function to each enumerated element. -/
def map (f : α → β) (e : Enum α) : Enum β :=
  fun n => (e n).map f

theorem map_range (f : α → β) (e : Enum α) :
    (e.map f).range = f '' e.range := by
  ext b; simp only [range, map, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨n, h⟩
    cases he : e n with
    | none => simp [he, Option.map] at h
    | some a => exact ⟨a, ⟨n, he⟩, by simpa [he, Option.map] using h⟩
  · rintro ⟨a, ⟨n, hn⟩, rfl⟩
    exact ⟨n, by simp [hn, Option.map]⟩

/-- Filter and transform an enumeration. -/
def filterMap (f : α → Option β) (e : Enum α) : Enum β :=
  fun n => (e n).bind f

theorem filterMap_range (f : α → Option β) (e : Enum α) :
    (e.filterMap f).range = { b | ∃ a ∈ e.range, f a = some b } := by
  ext b; simp only [range, filterMap, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, h⟩
    cases he : e n with
    | none => simp [he, Option.bind] at h
    | some a => exact ⟨a, ⟨n, he⟩, by simpa [he, Option.bind] using h⟩
  · rintro ⟨a, ⟨n, hn⟩, hf⟩
    exact ⟨n, by simp [hn, Option.bind, hf]⟩

/-- Filter an enumeration by a predicate. -/
def filter (p : α → Bool) (e : Enum α) : Enum α :=
  fun n => (e n).bind (fun a => if p a then some a else none)

theorem filter_range (p : α → Bool) (e : Enum α) :
    (e.filter p).range = { a ∈ e.range | p a = true } := by
  ext a; simp only [range, filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, h⟩
    cases he : e n with
    | none => simp [he, Option.bind] at h
    | some a' =>
      simp [he, Option.bind] at h
      by_cases hp : p a' = true
      · simp [hp] at h; subst h; exact ⟨⟨n, he⟩, hp⟩
      · simp [Bool.eq_false_iff.mpr hp] at h
  · rintro ⟨⟨n, hn⟩, hp⟩
    exact ⟨n, by simp [hn, Option.bind, hp]⟩

/-! ### Pairing / Dovetailing

To enumerate all pairs `(a, b)` from two enumerations, we use the Cantor
pairing function to dovetail. -/

/-- Enumerate all pairs from two enumerations using dovetailing. -/
def product (e₁ : Enum α) (e₂ : Enum β) : Enum (α × β) :=
  fun n =>
    let (i, j) := Nat.unpair n
    match e₁ i, e₂ j with
    | some a, some b => some (a, b)
    | _, _ => none

theorem product_range (e₁ : Enum α) (e₂ : Enum β) :
    (e₁.product e₂).range = { p | p.1 ∈ e₁.range ∧ p.2 ∈ e₂.range } := by
  ext ⟨a, b⟩; simp only [range, product, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, h⟩
    cases he1 : e₁ (Nat.unpair n).1 with
    | none => simp [he1] at h
    | some a' =>
      cases he2 : e₂ (Nat.unpair n).2 with
      | none => simp [he1, he2] at h
      | some b' =>
        simp [he1, he2] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨⟨_, he1⟩, ⟨_, he2⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨Nat.pair i j, by simp [Nat.unpair_pair, hi, hj]⟩

/-- Monadic bind (flatMap) with dovetailing.
    For each element `a` from `e`, enumerate `f a`, interleaving all results. -/
def bind (e : Enum α) (f : α → Enum β) : Enum β :=
  fun n =>
    let (i, j) := Nat.unpair n
    match e i with
    | some a => f a j
    | none => none

theorem bind_range (e : Enum α) (f : α → Enum β) :
    (e.bind f).range = { b | ∃ a ∈ e.range, b ∈ (f a).range } := by
  ext b; simp only [range, bind, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, h⟩
    cases he : e (Nat.unpair n).1 with
    | none => simp [he] at h
    | some a => exact ⟨a, ⟨_, he⟩, ⟨_, by simpa [he] using h⟩⟩
  · rintro ⟨a, ⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨Nat.pair i j, by simp [Nat.unpair_pair, hi, hj]⟩

/-! ### Derived enumerations -/

/-- Enumerate all finite lists over an `Encodable` type. -/
def finLists [Encodable α] : Enum (List α) := ofEncodable

theorem finLists_range [Encodable α] : (finLists (α := α)).range = Set.univ :=
  ofEncodable_range

/-- Enumerate all pairs of natural numbers. -/
def natPairs : Enum (ℕ × ℕ) := product naturals naturals

theorem natPairs_range : natPairs.range = Set.univ := by
  ext ⟨a, b⟩
  simp only [natPairs, product_range, naturals_range]
  simp

end Enum
