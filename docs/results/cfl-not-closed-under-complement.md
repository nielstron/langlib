---
title: "Context-free languages are not closed under complement or intersection"
description: "A formal Lean 4 proof that the class of context-free languages is not closed under complement, and not under intersection."
---

# Context-free languages are not closed under complement (or intersection)

## Statement

The class of **context-free languages** (CFL) is **not** closed under
complementation: there is a context-free language whose complement is not
context-free. It is likewise not closed under intersection. (Contrast with the
*deterministic* context-free languages, which **are**
[closed under complement](dcfl-closed-under-complement.html).)

## In Lean

In `Classes/ContextFree/Closure/Complement.lean`:

- [`CF_notClosedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Complement.lean) — the class is not closed under complement.
- [`CF_notClosedUnderComplement_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Complement.lean) — over any alphabet with enough symbols.

Non-closure under intersection is in
[`Classes/ContextFree/Closure/Intersection.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Intersection.lean).

## Proof idea

CFLs *are* closed under union. If they were also closed under complement, De
Morgan's law would make them closed under intersection — but the intersection of two
context-free languages can fail to be context-free (the classic
`{aⁱbⁱcʲ} ∩ {aⁱbʲcʲ} = {aⁿbⁿcⁿ}` example, which is not context-free). The
contradiction shows CFLs are not closed under complement.

## Keywords / also known as

context-free languages not closed under complement, CFL complement not context-free,
context-free not closed under intersection, anbncn not context-free, De Morgan
context-free closure, type-2 languages closure properties.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
