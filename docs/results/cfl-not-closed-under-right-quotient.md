---
title: "Context-free languages are not closed under right quotient"
description: "A concrete Lean 4 construction proving context-free languages are not closed under right quotient by a context-free language — two CF witnesses whose quotient encodes the powers of two."
---

# Context-free languages are not closed under right quotient

## Statement

The **right quotient** of `L` by `R` is `L / R = { w : ∃ v ∈ R, w·v ∈ L }`.

Context-free languages **are** closed under right quotient by a *regular* language, but
they are **not** closed under right quotient by an arbitrary context-free language.
Langlib proves the latter with an explicit, self-contained pair of context-free
witnesses — a concrete construction that is surprisingly hard to find written out
anywhere.

## The construction

Two context-free languages over the alphabet `{false, true}` are defined so that their
quotient, restricted to the unary slice `{false}*`, is exactly the **powers-of-two**
language:

> `(quotientNumerator / quotientDenominator) ∩ {false}*` = `unaryPow2` = `{ falseᵏ : k is a power of 2 }`.

- `quotientNumerator` and `quotientDenominator` are both context-free (blocks of
  `false`s separated by `true`s encode lists of natural numbers; the numerator uses a
  *doubling* relationship `a²ⁿ`/`bⁿ` and the denominator the matching `bⁿ`/`aⁿ`).
- Their right quotient relates these encoded numbers in a way that, once you keep only
  the purely-unary words, forces the surviving lengths to be **exactly the powers of
  two**.
- `unaryPow2` is **not** context-free (a textbook pumping-lemma language).

Now the punchline uses a *positive* closure property as a lever: context-free
languages **are** closed under intersection with a regular language. If the quotient
`quotientNumerator / quotientDenominator` were context-free, then intersecting it with
the regular language `{false}*` would stay context-free — but that intersection is
`unaryPow2`, which is not. Contradiction.

## In Lean

In `Classes/ContextFree/Closure/Quotient.lean`:

- [`CF_notClosedUnderRightQuotient`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Quotient.lean) — the class `is_CF` is not closed under right quotient.
- [`notCF_quotient`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Quotient.lean) — the specific quotient language is not context-free.
- [`quotient_slice_eq_unaryPow2`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Quotient.lean) — the key identity: the unary slice of the quotient is exactly `unaryPow2`.

The witnesses and the non-CF unary language, in `Classes/ContextFree/Examples/`:

- [`quotientNumerator`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/A2nBnPosStar.lean) ([`CF_quotientNumerator`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/A2nBnPosStar.lean)) and [`quotientDenominator`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/BnAnPosStarB.lean) ([`CF_quotientDenominator`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/BnAnPosStarB.lean)) — the two context-free witnesses.
- [`unaryPow2`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/UnaryA2PowSucc.lean) / [`notCF_unaryPow2`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/UnaryA2PowSucc.lean) — the powers-of-two unary language and its non-context-freeness.

For contrast, the **positive** result is in the same file:
[`CF_closedUnderRightQuotientWithRegular`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Quotient.lean) — closure under right quotient *with a regular language*.

## Proof idea

The reusable trick is to **slice with a regular language to expose a non-context-free
unary language**: pick CF numerator/denominator whose quotient, intersected with a
regular unary `{false}*`, lands exactly on a unary language known to be non-CF (here
`unaryPow2`). Closure of CFL under intersection-with-regular then turns "the quotient
is CF" into "`unaryPow2` is CF", which the pumping lemma refutes. The hard part — and
the bulk of the ~700-line file — is designing the two grammars and proving the slice
equals the powers of two exactly.

## Keywords / also known as

context-free not closed under right quotient, CFL quotient counterexample, concrete
construction context-free quotient, powers of two not context-free, right quotient by
context-free language, CFL closure properties, Lean formal proof.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
