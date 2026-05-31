---
title: "Closure properties of deterministic context-free languages"
description: "Formal Lean 4 proofs of the closure properties of deterministic context-free languages: closed under complement, but not under union, intersection, concatenation, star, homomorphism, substitution, or quotient."
---

# Closure properties of deterministic context-free languages

## Statement

Deterministic context-free languages (DCFL) have an unusual closure profile that sets
them apart from the full context-free languages. They **are** closed under
**complement** (the [marquee result](dcfl-closed-under-complement.html)) and under
intersection/union with a *regular* language — but they are **not** closed under most
of the operations the context-free languages enjoy:

| Operation | DCFL | CFL |
|---|---|---|
| Complement | ✅ [yes](dcfl-closed-under-complement.html) | ❌ [no](cfl-not-closed-under-intersection.html) |
| Union | ❌ no | ✅ yes |
| Intersection | ❌ no | ❌ no |
| Concatenation | ❌ no | ✅ yes |
| Kleene star | ❌ no | ✅ yes |
| Homomorphism | ❌ no | ✅ yes |
| Substitution | ❌ no | ✅ [yes](cf-closed-under-substitution.html) |
| Right quotient | ❌ no | ✅ yes |
| ∩ / ∪ with regular | ✅ yes | ✅ yes |

The two hardest non-closure proofs — concatenation and homomorphism — are each
over a thousand lines.

## In Lean

Positive results (`Classes/DeterministicContextFree/Closure/`):

- [`DCF_closedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean) — closed under complement (see the [dedicated page](dcfl-closed-under-complement.html)).
- [`DCF_closedUnderIntersectionWithRegular`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/IntersectionRegular.lean) — closed under intersection with a regular language (and likewise union with a regular language, in `Closure/UnionRegular.lean`).

Non-closure results (same directory):

- [`DCF_notClosedUnderConcatenation`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Concatenation.lean) — **not** closed under concatenation (~1550-line proof).
- [`DCF_notClosedUnderHomomorphism`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Homomorphism.lean) / [`DCF_notClosedUnderEpsFreeHomomorphism`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Homomorphism.lean) — **not** closed under (ε-free) homomorphism (~1150-line proof).
- [`DCF_notClosedUnderUnion`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Union.lean) — not closed under union.
- [`DCF_notClosedUnderIntersection`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Intersection.lean) — not closed under intersection.
- [`DCF_notClosedUnderKleeneStar`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Star.lean) — not closed under Kleene star.
- [`DCF_notClosedUnderSubstitution`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Substitution.lean) — not closed under substitution.
- [`DCF_notClosedUnderRightQuotient`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Quotient.lean) — not closed under right quotient.

## Proof idea

Closure under **complement** comes from totalizing the DPDA so that it always halts
and then flipping accepting/non-accepting states (see
[DPDA totalization](dpda-totalization.html)). The **non-closures** exhibit explicit
witnesses: deterministic languages whose union/concatenation/image forces a
non-deterministic choice a single DPDA cannot make. Non-closure under **union** is the
seed — given that, non-closure under **intersection** is immediate from closure under
complement and De Morgan; concatenation, star, homomorphism, and substitution each
require their own witness languages and the (lengthy) verification that the result has
no deterministic pushdown recognizer.

## Keywords / also known as

deterministic context-free closure properties, DCFL closed under complement, DCFL not
closed under union, DPDA closure, deterministic context-free not closed under
concatenation, DCFL homomorphism, type-2 deterministic languages closure, Lean
formalization.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
