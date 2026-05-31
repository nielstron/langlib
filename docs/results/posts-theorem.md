---
title: "Post's theorem (RE ∩ co-RE = recursive)"
description: "A formal Lean 4 proof of Post's theorem: a language is recursive (decidable) iff both it and its complement are recursively enumerable."
---

# Post's theorem: RE ∩ co-RE = recursive

## Statement

A language `L` is **recursive** (decidable) if and only if both `L` and its
complement `Lᶜ` are **recursively enumerable** (semi-decidable). Equivalently,
`RE ∩ co-RE = Recursive`. Langlib formalizes the substantive direction: if `L` and
`Lᶜ` are both RE, then `L` is recursive.

## In Lean

In `Classes/Recursive/Basics/Post.lean`:

- [`is_Recursive_of_isRE_of_isRE_compl`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Basics/Post.lean) — recursive form: `is_RE L → is_RE Lᶜ → is_Recursive L`.
- [`computablePred_of_isRE_of_isRE_compl`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Basics/Post.lean) — computability form: yields an explicit `ComputablePred` decider.
- [`REPred_mem_of_is_RE`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Basics/Post.lean) — bridges the language-level RE predicate to a computability-theoretic `RePred`.

## Proof idea

Run the two semi-deciders for `L` and `Lᶜ` in parallel ("dovetailing"). For any
word, exactly one of them halts and accepts. The first to accept tells you the
verdict, so the combined procedure always halts — giving a total decider and hence
a `ComputablePred`.

## Keywords / also known as

Post's theorem, RE intersect co-RE equals recursive, decidable iff semidecidable
and co-semidecidable, recursive equals RE and co-RE, complementation theorem for
recursively enumerable sets, Emil Post theorem computability.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
