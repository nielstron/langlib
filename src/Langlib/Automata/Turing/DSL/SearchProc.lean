import Mathlib
import Langlib.Automata.Turing.DSL.Enumeration
import Langlib.Automata.Turing.Definition

/-! # Search Procedures — The Core DSL

This file defines `SearchProc`, the central abstraction of the DSL.
A `SearchProc` captures the pattern:

> **"Enumerate candidates from a countable domain; test each one;
>    halt when a witness is found."**

This is the universal pattern for semi-decision procedures: to check
`w ∈ L`, we enumerate a domain of "proofs/witnesses" and test each one.
For grammars, the witnesses are derivation sequences; for other problems
they might be computation traces, certificates, etc.

## Architecture

```
  ┌─────────────┐     ┌──────────────┐     ┌──────────┐
  │  Enum α     │────▶│  test : α →  │────▶│  halt if │
  │  (generator)│     │  List T →    │     │  true    │
  │             │     │  Bool        │     │          │
  └─────────────┘     └──────────────┘     └──────────┘
```

The `SearchProc` bundles:
1. An `Enum α` (the generator / candidate enumerator)
2. A `test : α → List T → Bool` (the decidable test)

It **recognizes** the language `{ w | ∃ a ∈ enum.range, test a w = true }`.

## Composability

Search procedures compose via the `Enum` combinators:
- To search over pairs, use `Enum.product`
- To search over lists, use `Enum.finLists`
- To search with additional structure, use `Enum.bind`

The test function can be built from decidable predicates using standard
Boolean combinators.

## Compilation to TM0

The key theorem `SearchProc.toTM0` (in `Compile.lean`) states:
if the enumeration and test are "TM-computable" (formalized via
a computability predicate), then the search procedure compiles to
a TM0 machine satisfying `is_TM`.

## Main definitions

- `SearchProc` — a search procedure
- `SearchProc.accepts` — whether the procedure accepts a given word
- `SearchProc.language` — the language recognized
- `SearchProc.mk'` — convenient constructor from `Enum` + test
- Composition lemmas
-/

open Enum

/-- A **search procedure** over alphabet `T` with witness type `α`.

A search procedure recognizes a language by systematically enumerating
witnesses from a countable domain and testing each one against the input word.
It accepts `w` if and only if some witness passes the test.

This is the core abstraction of the DSL. Every semi-decision procedure
for a language can be expressed as a `SearchProc` (by Rice's theorem,
the converse also holds for r.e. languages). -/
structure SearchProc (T : Type*) where
  /-- The type of witnesses / certificates -/
  WitTy : Type*
  /-- Enumeration of all candidate witnesses -/
  enum : Enum WitTy
  /-- The test: given a witness and an input word, does the witness certify membership? -/
  test : WitTy → List T → Bool

namespace SearchProc

variable {T : Type*}

/-- A search procedure **accepts** word `w` if some enumerated witness
passes the test. -/
def accepts (sp : SearchProc T) (w : List T) : Prop :=
  ∃ a ∈ sp.enum.range, sp.test a w = true

/-- The **language** recognized by a search procedure: the set of all
accepted words. -/
def language (sp : SearchProc T) : Language T :=
  { w | sp.accepts w }

/-- A search procedure accepts `w` iff there exists `n : ℕ` such that
the `n`-th enumerated witness passes the test. -/
theorem accepts_iff (sp : SearchProc T) (w : List T) :
    sp.accepts w ↔ ∃ n, ∃ a, sp.enum n = some a ∧ sp.test a w = true := by
  simp [accepts, Enum.range]
  constructor
  · rintro ⟨a, ⟨n, hn⟩, ht⟩; exact ⟨n, a, hn, ht⟩
  · rintro ⟨n, a, hn, ht⟩; exact ⟨a, ⟨n, hn⟩, ht⟩

/-- Equivalent "step-based" view: the procedure accepts `w` iff
`sp.step w n = true` for some `n`, where `step` is the composed
enumerate-and-test function. -/
def step (sp : SearchProc T) (w : List T) (n : ℕ) : Bool :=
  match sp.enum n with
  | some a => sp.test a w
  | none => false

theorem accepts_iff_step (sp : SearchProc T) (w : List T) :
    sp.accepts w ↔ ∃ n, sp.step w n = true := by
  rw [accepts_iff]
  simp [step]
  constructor
  · rintro ⟨n, a, hn, ht⟩; exact ⟨n, by simp [hn, ht]⟩
  · rintro ⟨n, h⟩
    cases he : sp.enum n with
    | none => simp [he] at h
    | some a => exact ⟨n, a, he, by simpa [he] using h⟩

/-! ### Constructors -/

/-- Build a search procedure from an `Encodable` witness type and a test.
    Automatically uses the `Encodable` instance to enumerate all witnesses. -/
def ofEncodable [Encodable α] (test : α → List T → Bool) : SearchProc T where
  WitTy := α
  enum := Enum.ofEncodable
  test := test

theorem ofEncodable_language [Encodable α] (test : α → List T → Bool) :
    (ofEncodable test).language = { w | ∃ a : α, test a w = true } := by
  ext w; simp [language, accepts, Enum.range, ofEncodable, Enum.ofEncodable]
  constructor
  · rintro ⟨a, ⟨n, hn⟩, ht⟩; exact ⟨a, ht⟩
  · rintro ⟨a, ht⟩; exact ⟨a, ⟨Encodable.encode a, Encodable.encodek a⟩, ht⟩

/-- Build a search procedure that searches over all natural numbers. -/
def searchNat (test : ℕ → List T → Bool) : SearchProc T where
  WitTy := ℕ
  enum := Enum.naturals
  test := test

theorem searchNat_language (test : ℕ → List T → Bool) :
    (searchNat test).language = { w | ∃ n : ℕ, test n w = true } := by
  ext w; simp [language, accepts, Enum.range, searchNat, Enum.naturals]

/-! ### Composition -/

/-- Refine a search procedure with a stronger test. -/
def refine (sp : SearchProc T) (p : sp.WitTy → List T → Bool) : SearchProc T where
  WitTy := sp.WitTy
  enum := sp.enum
  test := fun a w => sp.test a w && p a w

theorem refine_language (sp : SearchProc T) (p : sp.WitTy → List T → Bool) :
    ∀ w, w ∈ (sp.refine p).language → w ∈ sp.language := by
  intro w hw
  simp only [language, accepts, refine] at hw ⊢
  obtain ⟨a, ha, ht⟩ := hw
  exact ⟨a, ha, by simp [Bool.and_eq_true] at ht; exact ht.1⟩

/-- Transform the witness type of a search procedure. -/
def mapWitness (sp : SearchProc T) (f : β → sp.WitTy) (enum_β : Enum β) :
    SearchProc T where
  WitTy := β
  enum := enum_β
  test := fun b w => sp.test (f b) w

/-- Existential search: search for a pair `(a, b)` where `a` comes from
one enumeration and `b` from another. -/
def existsPair {α β : Type*} (enumA : Enum α) (enumB : Enum β)
    (test : α → β → List T → Bool) : SearchProc T where
  WitTy := α × β
  enum := enumA.product enumB
  test := fun p w => test p.1 p.2 w

theorem existsPair_language {α β : Type*} (enumA : Enum α) (enumB : Enum β)
    (test : α → β → List T → Bool) :
    (existsPair enumA enumB test).language =
      { w | ∃ a ∈ enumA.range, ∃ b ∈ enumB.range, test a b w = true } := by
  ext w; simp [existsPair]; (
  simp +decide [SearchProc.language, SearchProc.accepts];
  simp +decide only [product_range, Set.mem_setOf_eq];
  grind)

end SearchProc