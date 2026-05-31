---
title: "Context-free languages are not closed under right quotient"
description: "A concrete Lean 4 construction proving context-free languages are not closed under right quotient by a context-free language — two explicit CF witnesses whose quotient encodes the powers of two."
parent: "Context-free"
nav_order: 7
---

# Context-free languages are not closed under right quotient

## Statement

The **right quotient** of `L` by `R` is `L / R = { w : ∃ v ∈ R, w·v ∈ L }`.

Context-free languages **are** closed under right quotient by a *regular* language, but
they are **not** closed under right quotient by an arbitrary context-free language.
Langlib proves the latter with an explicit, self-contained pair of context-free
witnesses.

## The two witness languages

Over the alphabet `{a, b}` (in the source, `a = false`, `b = true`):

- **Numerator** `N` — concatenations of blocks that have **twice as many `a`s as `b`s**:

  > `N = { a²ᵐ bᵐ : m ≥ 1 }*` &nbsp; (`quotientNumerator = (quotientLeftBlock)*`)

  e.g. `ε`, `a²b`, `a⁴b²`, `a²b·a²b`, `a⁴b²·a²b`, … — each block is `a²ᵐbᵐ`.

- **Denominator** `D` — concatenations of `bᵐaᵐ` blocks, followed by **one trailing `b`**:

  > `D = { bᵐ aᵐ : m ≥ 1 }* · b` &nbsp; (`quotientDenominator = (quotientRightBlock)* · {b}`)

  e.g. `b`, `b²a²·b`, `ba·b`, `b²a²·b³a³·b`, … — note the smallest element is just `b`.

Both are context-free — each is the Kleene star of a single-block context-free language
(and CFL is closed under star and concatenation): `CF_quotientNumerator`,
`CF_quotientDenominator`.

## Why the quotient is the powers of two

Intersect the quotient with the **regular** unary language `{a}*`. The key identity
(`quotient_slice_eq_unaryPow2`) is

> `(N / D) ∩ {a}*` = `unaryPow2` = `{ a^(2ᵏ) : k ≥ 1 }` = `{ a², a⁴, a⁸, a¹⁶, … }`.

Recall `aᵐ ∈ N / D` means *some* `v ∈ D` makes `aᵐ·v ∈ N`. Worked examples:

- **`a² ∈ N/D`**: take `v = b` (∈ D). Then `a²·v = a²b`, a single `N`-block (`m = 1`). ✓
- **`a⁴ ∈ N/D`**: take `v = b²a²·b` (∈ D). Then `a⁴·v = a⁴b² a²b = (a⁴b²)(a²b)`, two
  `N`-blocks. ✓
- **`a³ ∉ N/D`**: every `v ∈ D` starts with `b`, so `a³·v` begins `a³b…`; but an
  `N`-block needs an **even** number of `a`s before its `b`s, and `a³b` has three — no
  parse exists. ✗

The general mechanism: matching `aᵐ·v` against the `N`-blocks forces the `bᵐ` tail of
one block to be eaten by a denominator block `bᵐaᵐ`, whose `aᵐ` must then begin the
**next** numerator block `a²ᵐ'bᵐ'` — so `m = 2m'`. Walking this chain outward from the
single trailing `b` **doubles** the exponent at each step, so the only unary words that
survive are `a^(2ᵏ)`. That set is `unaryPow2`, which the
[pumping lemma](context-free-pumping-lemma.html) shows is **not** context-free
(`notCF_unaryPow2`).

## Putting it together

The non-closure then follows from a *positive* closure property used as a lever:

1. CFLs **are** closed under intersection with a regular language.
2. So if `N / D` were context-free, `(N / D) ∩ {a}*` would be context-free too.
3. But that intersection is `unaryPow2`, which is not — contradiction.

Hence CFLs are not closed under right quotient. The hard part — the bulk of the
~700-line file — is proving that the slice equals the powers of two *exactly*.

## In Lean

Closure result and counterexample, in `Classes/ContextFree/Closure/Quotient.lean`:

- [`CF_notClosedUnderRightQuotient`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Quotient.lean) — `is_CF` is not closed under right quotient.
- [`notCF_quotient`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Quotient.lean) — the specific quotient `N / D` is not context-free.
- [`quotient_slice_eq_unaryPow2`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Quotient.lean) — the identity `(N / D) ∩ {a}* = unaryPow2`.
- [`CF_closedUnderRightQuotientWithRegular`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Quotient.lean) — the contrasting *positive* result (quotient with a regular language is CF).

The witness languages (definitions in `Examples/`, context-freeness in `Classes/ContextFree/Examples/`):

- [`quotientNumerator`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Examples/A2nBnPosStar.lean) `= (quotientLeftBlock)*`, with [`quotientLeftBlock = { a²ᵐbᵐ : m ≥ 1 }`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Examples/A2nBnPos.lean) — context-free by [`CF_quotientNumerator`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/A2nBnPosStar.lean).
- [`quotientDenominator`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Examples/BnAnPosStarB.lean) `= (quotientRightBlock)* · {b}`, with [`quotientRightBlock = { bᵐaᵐ : m ≥ 1 }`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Examples/BnAnPos.lean) — context-free by [`CF_quotientDenominator`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/BnAnPosStarB.lean).
- [`unaryPow2 = { a^(2^(k+1)) }`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Examples/UnaryA2PowSucc.lean) / [`notCF_unaryPow2`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/UnaryA2PowSucc.lean).

## Keywords / also known as

context-free not closed under right quotient, CFL quotient counterexample, concrete
construction context-free quotient, powers of two not context-free, right quotient by
context-free language, CFL closure properties, Lean formal proof.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
