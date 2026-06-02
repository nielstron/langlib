---
title: "Complement"
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

- [`is_Recursive_complement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Closure/Complement.lean) — `is_Recursive L → is_Recursive Lᶜ`.
- [`Recursive_closedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Closure/Complement.lean) — packaged `ClosedUnderComplement` instance.

## Proof idea

`is_Recursive L` provides an always-halting `Turing.TM0` machine `M` together with a
Boolean state predicate `accept` deciding membership. `is_Recursive_complement` reuses
the *same* machine `M` — identical work alphabet, states, and halting behaviour — and
only negates the acceptance predicate to `fun q => !accept q`. Since the run on each
input is unchanged, the halting witness carries over and `w ∈ Lᶜ ↔ !accept q = true`
holds, discharged by `grind`. `Recursive_closedUnderComplement` packages this as the
`ClosedUnderComplement` instance.

## Keywords / also known as

recursive languages closed under complement, decidable languages complement
decidable, complement of a recursive set is recursive, computable predicate
negation, recursive closure properties.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
