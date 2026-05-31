---
title: "Context-free languages are not closed under intersection"
description: "A formal Lean 4 proof that context-free languages are not closed under intersection (via the pumping lemma), with non-closure under complement as a corollary."
---

# Context-free languages are not closed under intersection

## Statement

The class of **context-free languages** (CFL) is **not** closed under intersection:
there are two context-free languages whose intersection is not context-free. The
standard witness is

> `{aⁿbⁿcⁿ}` = `{aⁿbⁿcᵐ}` ∩ `{aᵐbⁿcⁿ}`,

where each of the two factors is context-free (only two of the three blocks are
constrained, which a single stack can check), but the intersection `{aⁿbⁿcⁿ}` is
**not** context-free — exactly the language ruled out by the
[pumping lemma for context-free languages](context-free-pumping-lemma.html).

Non-closure under **complement** then follows as a corollary: context-free languages
*are* closed under union, so if they were also closed under complement, De Morgan's
law would force closure under intersection — a contradiction.

## In Lean

Non-closure under intersection, in `Classes/ContextFree/Closure/Intersection.lean`:

- [`CF_notClosedUnderIntersection`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Intersection.lean) — the class is not closed under intersection.
- [`CF_notClosedUnderIntersection_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Intersection.lean) — over any alphabet with enough symbols.
- [`notCF_lang_eq_eq`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Intersection.lean) — the intersection witness language is not context-free (the pumping-lemma step).

Non-closure under complement (the corollary), in `Classes/ContextFree/Closure/Complement.lean`:

- [`CF_notClosedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Complement.lean) / [`CF_notClosedUnderComplement_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Complement.lean).

## Proof idea

The two factor languages are context-free (a pushdown automaton matches the one pair
of blocks that is constrained and ignores the third). Their intersection is
`{aⁿbⁿcⁿ}`, which the [pumping lemma](context-free-pumping-lemma.html) shows is not
context-free — see [`{aⁿbⁿcⁿ}` is not context-free](anbncn-not-context-free.html).
That gives non-closure under intersection directly. For complement: CFLs are closed
under union, and `A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ`, so closure under complement would imply the
just-refuted closure under intersection.

## Keywords / also known as

context-free not closed under intersection, CFL intersection not context-free,
anbncn not context-free, context-free not closed under complement, pumping lemma
context-free, De Morgan context-free closure, type-2 languages closure properties.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
