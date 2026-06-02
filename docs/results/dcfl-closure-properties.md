---
title: "Closure properties of deterministic context-free languages"
description: "Formal Lean 4 proofs of the closure properties of deterministic context-free languages: closed under complement, but not under union, intersection, concatenation, star, homomorphism, substitution, or quotient."
parent: "Deterministic context-free"
nav_order: 3
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

Closure under **complement** comes from totalizing the DPDA to a deciding
presentation and complementing its final states (see
[DPDA totalization](dpda-totalization.html)). The **non-closures** form a reduction
chain seeded by intersection, all anchored on the context-free pumping fact that
`lang_eq_eq = {aⁿbⁿcⁿ}` is not even context-free.

- **Intersection** is the seed (`DCF_notClosedUnderIntersection`): the CFL
  counterexample languages `lang_eq_any = {aⁿbⁿcᵐ}` and `lang_any_eq = {aᵐbⁿcⁿ}` are
  exhibited as deterministic context-free, and their intersection is `lang_eq_eq`,
  which is not context-free, hence not DCF.
- **Union** (`DCF_notClosedUnderUnion`) then follows from complement closure by De
  Morgan: `L₁ ∩ L₂ = (L₁ᶜ ∪ L₂ᶜ)ᶜ`, so union closure would force intersection
  closure.
- **Substitution** (`DCF_notClosedUnderSubstitution`) reduces directly to union:
  substituting the two singleton Boolean words by arbitrary DCFLs produces their
  union. **Concatenation** and **homomorphism** (`DCF_notClosedUnderConcatenation`,
  ~1550 lines; `DCF_notClosedUnderHomomorphism`, ~1150 lines) each likewise reduce a
  hypothetical closure to union closure — concatenation via a fresh marker plus an
  intersection and left quotient, homomorphism by erasing a prefix marker on a
  disjoint union — and **Kleene star** (`DCF_notClosedUnderKleeneStar`) uses the same
  union witnesses restricted to strictly positive `a⁺b⁺c⁺` blocks.
- **Right quotient** (`DCF_notClosedUnderRightQuotient`) is an independent reduction
  to the CFL right-quotient counterexample: both witness languages are DCF, but their
  quotient is the non-context-free language used in the CFL pumping argument.

## Keywords / also known as

deterministic context-free closure properties, DCFL closed under complement, DCFL not
closed under union, DPDA closure, deterministic context-free not closed under
concatenation, DCFL homomorphism, type-2 deterministic languages closure, Lean
formalization.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
