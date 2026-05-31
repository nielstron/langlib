---
title: "Recursive languages are closed under complement"
description: "A formal Lean 4 proof that the complement of a recursive (decidable) language is recursive."
parent: "Recursive"
nav_order: 2
---

# Recursive languages are closed under complement

## Statement

If a language `L` is **recursive** (decidable), then its complement `Lᶜ` is also
recursive. The class of recursive languages is closed under complementation. (This
is *not* true for recursively enumerable languages — see
[Recursive ⊊ RE](recursive-strict-subset-re.html).)

## In Lean

In `Classes/Recursive/Closure/Complement.lean`:

- [`is_Recursive_complement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Closure/Complement.lean) — `is_Recursive L → is_Recursive Lᶜ`.
- [`Recursive_closedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Closure/Complement.lean) — packaged `ClosedUnderComplement` instance.

## Proof idea

A decider for `L` always halts with a yes/no answer; negate that answer to obtain a
decider for `Lᶜ`. Flipping a total computable predicate stays computable, so `Lᶜ`
is recursive.

## Keywords / also known as

recursive languages closed under complement, decidable languages complement
decidable, complement of a recursive set is recursive, computable predicate
negation, recursive closure properties.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
